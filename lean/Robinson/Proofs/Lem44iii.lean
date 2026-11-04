/-
Robinson/Proofs/Lem44iii.lean — proofs of lem_4_4_iii.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.NearP
import Robinson.NotFormalized
import Robinson.Proofs.NearP_A

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Taylor coefficients from a power-series expansion -/

/-- If `F(ξ) = ∑ aₙ ξⁿ` on a disc around `0`, then the Taylor coefficients of `F` at `0` are the `aₙ`. -/
private lemma l44_coeff_eq {F : ℂ → ℂ} {a : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hs : ∀ ξ ∈ ball (0 : ℂ) r, HasSum (fun n => a n * ξ ^ n) (F ξ)) (n : ℕ) : coeff F n = a n := by
  set t : NNReal := ⟨r / 2, by positivity⟩ with ht
  have htr : (t : ℝ) = r / 2 := rfl
  have hmem : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hrad : (t : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
    have h1 := (hs _ hmem).summable.tendsto_atTop_zero.norm
    simp only [norm_zero] at h1
    convert h1 using 2 with m
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < r / 2), htr]
  have hp : HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ a) 0 (t : ENNReal) := by
    refine ⟨hrad, ENNReal.coe_pos.mpr ?_, ?_⟩
    · rw [← NNReal.coe_pos, htr]
      positivity
    · intro y hy
      rw [Metric.eball_coe, mem_ball_zero_iff, htr] at hy
      simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
      exact hs y (mem_ball_zero_iff.mpr (by linarith))
  have hq := hp.hasFPowerSeriesAt.analyticAt.hasFPowerSeriesAt
  have heq := hq.eq_formalMultilinearSeries hp.hasFPowerSeriesAt
  have h2 := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ heq
  unfold coeff
  exact congrFun h2 n

/-! ### The series `∑_m d_m ξᵐ/(1 - qξ)^{m-s}` and its coefficients -/

/-- `ξᵐ/(1 - qξ)^{k+1} = ∑_i C(i+k, k) qⁱ ξ^{m+i}` for `|qξ| < 1`. -/
private lemma l44_kernel {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (k m : ℕ) {q x : 𝕜}
    (h : ‖q * x‖ < 1) :
    HasSum (fun i : ℕ => ((i + k).choose k : 𝕜) * q ^ i * x ^ (m + i)) (x ^ m / (1 - q * x) ^ (k + 1)) := by
  have h0 := (hasSum_choose_mul_geometric_of_norm_lt_one k h).mul_left (x ^ m)
  convert h0 using 1
  · funext i
    rw [mul_pow, pow_add]
    ring
  · rw [mul_one_div]

/-- The coefficient of `ξⁿ` in `ξᵐ/(1 - qξ)^{m-s}` (for `s < m ≤ n`). -/
private noncomputable def l44_kc (s : ℕ) (q : ℂ) (m n : ℕ) : ℂ :=
  ((n - m + (m - s - 1)).choose (m - s - 1) : ℂ) * q ^ (n - m)

/-- The coefficient of `ξⁿ` in `∑_m d_m ξᵐ/(1 - qξ)^{m-s}`. -/
private noncomputable def l44_gc (d : ℕ → ℂ) (s : ℕ) (q : ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (n + 1), d m * l44_kc s q m n

/-- The function `∑_m d_m ξᵐ/(1 - qξ)^{m-s}`. -/
private noncomputable def l44_gs (d : ℕ → ℂ) (s : ℕ) (q : ℂ) (ξ : ℂ) : ℂ :=
  ∑' m : ℕ, d m * ξ ^ m / (1 - q * ξ) ^ (m - s)

/-- The double family `d_m C(i+k_m, k_m) qⁱ ξ^{m+i}`, `k_m = m - s - 1`. -/
private noncomputable def l44_dbl (d : ℕ → ℂ) (s : ℕ) (q ξ : ℂ) (p : ℕ × ℕ) : ℂ :=
  d p.1 * ((p.2 + (p.1 - s - 1)).choose (p.1 - s - 1) : ℂ) * q ^ p.2 * ξ ^ (p.1 + p.2)

private lemma l44_dbl_fiber {d : ℕ → ℂ} {s : ℕ} (hd0 : ∀ m ≤ s, d m = 0) {q ξ : ℂ} (h : ‖q * ξ‖ < 1)
    (m : ℕ) : HasSum (fun i => l44_dbl d s q ξ (m, i)) (d m * ξ ^ m / (1 - q * ξ) ^ (m - s)) := by
  by_cases hm : m ≤ s
  · simp only [l44_dbl, hd0 m hm, zero_mul, zero_div]
    exact hasSum_zero
  · have hk : m - s = m - s - 1 + 1 := by omega
    have h0 := (l44_kernel (m - s - 1) m h).mul_left (d m)
    rw [hk]
    convert h0 using 1
    · funext i
      simp only [l44_dbl]
      ring
    · ring

private lemma l44_dbl_fiber_norm (d : ℕ → ℂ) (s : ℕ) {q ξ : ℂ} (h : ‖q‖ * ‖ξ‖ < 1) (m : ℕ) :
    HasSum (fun i => ‖l44_dbl d s q ξ (m, i)‖)
      (‖d m‖ * (‖ξ‖ ^ m / (1 - ‖q‖ * ‖ξ‖) ^ (m - s - 1 + 1))) := by
  have h' : ‖(‖q‖ * ‖ξ‖ : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact h
  have h0 := (l44_kernel (m - s - 1) m h').mul_left (‖d m‖)
  convert h0 using 1
  funext i
  simp only [l44_dbl, norm_mul, norm_pow, Complex.norm_natCast]
  ring

private lemma l44_summable_outer (d : ℕ → ℂ) (s : ℕ) {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hdb : ∀ m, ‖d m‖ ≤ M * ρ ^ m) {q ξ : ℂ} (h1 : ‖q‖ * ‖ξ‖ ≤ 1 / 2) (h2 : 2 * ρ * ‖ξ‖ ≤ 1 / 2) :
    Summable (fun m => ‖d m‖ * (‖ξ‖ ^ m / (1 - ‖q‖ * ‖ξ‖) ^ (m - s - 1 + 1))) := by
  have hρξ : 0 ≤ 2 * ρ * ‖ξ‖ := mul_nonneg (mul_nonneg (by norm_num) hρ) (norm_nonneg _)
  have hgeo : Summable (fun m : ℕ => 2 * M * (2 * ρ * ‖ξ‖) ^ m) :=
    (summable_geometric_of_lt_one hρξ (by linarith)).mul_left _
  have hpos' : 0 < 1 - ‖q‖ * ‖ξ‖ := by linarith
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _)
    (div_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg hpos'.le _))) (fun m => ?_) hgeo
  set a := ‖q‖ * ‖ξ‖ with ha
  have ha0 : 0 ≤ a := by positivity
  have hpos : 0 < 1 - a := hpos'
  have hk : m - s - 1 + 1 ≤ m + 1 := by omega
  have hinv : 1 / (1 - a) ^ (m - s - 1 + 1) ≤ 2 ^ (m + 1) := by
    rw [div_le_iff₀ (pow_pos hpos _)]
    calc (1 : ℝ) = 2 ^ (m - s - 1 + 1) * (1 / 2) ^ (m - s - 1 + 1) := by
          rw [← mul_pow]; norm_num
      _ ≤ 2 ^ (m + 1) * (1 - a) ^ (m - s - 1 + 1) := by
          apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hk)
            (pow_le_pow_left₀ (by norm_num) (by linarith) _) (by positivity) (by positivity)
  have hξ0 : 0 ≤ ‖ξ‖ ^ m := by positivity
  calc ‖d m‖ * (‖ξ‖ ^ m / (1 - a) ^ (m - s - 1 + 1))
      = ‖d m‖ * ‖ξ‖ ^ m * (1 / (1 - a) ^ (m - s - 1 + 1)) := by ring
    _ ≤ (M * ρ ^ m) * ‖ξ‖ ^ m * 2 ^ (m + 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hdb m) hξ0) hinv (by positivity)
          (mul_nonneg (mul_nonneg hM (pow_nonneg hρ _)) hξ0)
    _ = 2 * M * (2 * ρ * ‖ξ‖) ^ m := by rw [mul_pow, mul_pow, pow_succ]; ring

/-- The power series of `∑_m d_m ξᵐ/(1 - qξ)^{m-s}` for small `ξ`. -/
private lemma l44_gs_hasSum {d : ℕ → ℂ} {s : ℕ} {q : ℂ} {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hd0 : ∀ m ≤ s, d m = 0) (hdb : ∀ m, ‖d m‖ ≤ M * ρ ^ m) {ξ : ℂ} (h1 : ‖q‖ * ‖ξ‖ ≤ 1 / 2)
    (h2 : 2 * ρ * ‖ξ‖ ≤ 1 / 2) :
    HasSum (fun n => l44_gc d s q n * ξ ^ n) (l44_gs d s q ξ) := by
  have hqξ : ‖q * ξ‖ < 1 := by
    rw [norm_mul]
    linarith
  have hlt : ‖q‖ * ‖ξ‖ < 1 := by linarith
  have hgs : Summable (l44_dbl d s q ξ) := by
    refine Summable.of_norm ?_
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun m => (l44_dbl_fiber_norm d s hlt m).summable, ?_⟩
    simp only [(l44_dbl_fiber_norm d s hlt _).tsum_eq]
    exact l44_summable_outer d s hM hρ hdb h1 h2
  have hT := hgs.hasSum.prod_fiberwise (l44_dbl_fiber hd0 hqξ)
  have hval : l44_gs d s q ξ = ∑' p, l44_dbl d s q ξ p := hT.tsum_eq
  rw [hval]
  have hg2 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr hgs.hasSum
  have hg3 := hg2.sigma (fun n => hasSum_fintype _)
  convert hg3 using 1
  funext n
  refine Eq.trans ?_ (Finset.sum_coe_sort _ (l44_dbl d s q ξ)).symm
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, l44_gc, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  simp only [l44_dbl, l44_kc]
  rw [Nat.add_sub_cancel' hmn]
  ring

/-- The Taylor coefficients of a function equal to `∑_m d_m ξᵐ/(1 - qξ)^{m-s}` near `0`. -/
private lemma l44_coeff_gs {d : ℕ → ℂ} {s : ℕ} {q : ℂ} {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hd0 : ∀ m ≤ s, d m = 0) (hdb : ∀ m, ‖d m‖ ≤ M * ρ ^ m) {F : ℂ → ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hF : ∀ ξ ∈ ball (0 : ℂ) r₀, F ξ = l44_gs d s q ξ) (n : ℕ) : coeff F n = l44_gc d s q n := by
  set r := min r₀ (min (1 / (2 * (‖q‖ + 1))) (1 / (4 * (ρ + 1)))) with hr
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hrpos : 0 < r := lt_min hr₀ (lt_min (div_pos one_pos (by linarith)) (div_pos one_pos (by linarith)))
  refine l44_coeff_eq hrpos (fun ξ hξ => ?_) n
  rw [mem_ball_zero_iff] at hξ
  have hr1 : r ≤ r₀ := min_le_left _ _
  have hr2 : r ≤ 1 / (2 * (‖q‖ + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ 1 / (4 * (ρ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg _
  have h1 : ‖q‖ * ‖ξ‖ ≤ 1 / 2 := by
    have : ‖ξ‖ * (2 * (‖q‖ + 1)) ≤ 1 := by
      have := (lt_of_lt_of_le hξ hr2).le
      rwa [le_div_iff₀ (by linarith)] at this
    nlinarith
  have h2 : 2 * ρ * ‖ξ‖ ≤ 1 / 2 := by
    have : ‖ξ‖ * (4 * (ρ + 1)) ≤ 1 := by
      have := (lt_of_lt_of_le hξ hr3).le
      rwa [le_div_iff₀ (by linarith)] at this
    nlinarith
  rw [hF ξ (mem_ball_zero_iff.mpr (lt_of_lt_of_le hξ hr1))]
  exact l44_gs_hasSum hM hρ hd0 hdb h1 h2

/-- Termwise comparison of the coefficients `l44_gc`. -/
private lemma l44_gc_le (d : ℕ → ℂ) (D : ℕ → ℝ) (K : ℝ) (s : ℕ) (q : ℂ) (q' : ℝ)
    (hq : ‖q‖ ≤ q') (hd : ∀ m, ‖d m‖ ≤ K * D m) (n : ℕ) :
    ‖l44_gc d s q n‖ ≤ K * (l44_gc (fun m => (D m : ℂ)) s (q' : ℂ) n).re := by
  unfold l44_gc l44_kc
  rw [Complex.re_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  set C : ℕ := (n - m + (m - s - 1)).choose (m - s - 1)
  have hD : 0 ≤ K * D m := (norm_nonneg _).trans (hd m)
  have hre : ((D m : ℂ) * ((C : ℂ) * (q' : ℂ) ^ (n - m))).re = D m * (C * q' ^ (n - m)) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hre, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  calc ‖d m‖ * (C * ‖q‖ ^ (n - m)) ≤ (K * D m) * (C * q' ^ (n - m)) :=
        mul_le_mul (hd m) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq _) (Nat.cast_nonneg _))
          (by positivity) hD
    _ = K * (D m * (C * q' ^ (n - m))) := by ring

/-! ### `B₁` and `B₂` as series of the same shape -/

/-- `B₁ = ∑_{m ≥ 2} (3/5)(4/3)ᵐ xᵐ/(1 - ⅔x)^{m-1}`. -/
private noncomputable def l44_d1 (m : ℕ) : ℝ := if 2 ≤ m then 3 / 5 * (4 / 3) ^ m else 0

/-- The weights `e₄ = 1/3`, `e_m = 4/15` (`m ≥ 5`). -/
private noncomputable def l44_e (m : ℕ) : ℝ := if m = 4 then 1 / 3 else 4 / 15

/-- `B₂ = ∑_{m ≥ 4} e_m (4/3)ᵐ xᵐ/(1 - ⅔x)^{m-2}`. -/
private noncomputable def l44_d2 (m : ℕ) : ℝ := if 4 ≤ m then l44_e m * (4 / 3) ^ m else 0

private lemma l44_d1_nonneg (m : ℕ) : 0 ≤ l44_d1 m := by
  unfold l44_d1
  split_ifs <;> positivity

private lemma l44_d1_le (m : ℕ) : l44_d1 m ≤ (4 / 3) ^ m := by
  unfold l44_d1
  split_ifs
  · have : (0 : ℝ) ≤ (4 / 3) ^ m := by positivity
    linarith
  · positivity

private lemma l44_e_pos (m : ℕ) : 0 < l44_e m := by
  unfold l44_e
  split_ifs <;> norm_num

private lemma l44_e_le (m : ℕ) : l44_e m ≤ 1 := by
  unfold l44_e
  split_ifs <;> norm_num

private lemma l44_d2_nonneg (m : ℕ) : 0 ≤ l44_d2 m := by
  unfold l44_d2
  split_ifs
  · exact mul_nonneg (l44_e_pos m).le (by positivity)
  · exact le_refl 0

private lemma l44_d2_le (m : ℕ) : l44_d2 m ≤ (4 / 3) ^ m := by
  unfold l44_d2
  split_ifs
  · have : (0 : ℝ) ≤ (4 / 3) ^ m := by positivity
    nlinarith [l44_e_le m]
  · positivity

private lemma l44_real_norm_le {D : ℕ → ℝ} (h0 : ∀ m, 0 ≤ D m) (h1 : ∀ m, D m ≤ (4 / 3) ^ m) (m : ℕ) :
    ‖(D m : ℂ)‖ ≤ 1 * (4 / 3) ^ m := by
  rw [Complex.norm_real, Real.norm_of_nonneg (h0 m), one_mul]
  exact h1 m

/-- Elementary facts for `|x| < 1/4`. -/
private lemma l44_small {x : ℂ} (hx : ‖x‖ < 1 / 4) :
    (1 - 2 / 3 * x) ≠ 0 ∧ (1 - 2 * x) ≠ 0 ∧ ‖4 / 3 * x / (1 - 2 / 3 * x)‖ < 1 := by
  have h23 : ‖(2 / 3 : ℂ)‖ = 2 / 3 := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
  have h43 : ‖(4 / 3 : ℂ)‖ = 4 / 3 := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
  have h1 : ‖(2 / 3 : ℂ) * x‖ < 1 / 6 := by
    rw [norm_mul, h23]
    linarith
  have hP : 5 / 6 < ‖1 - 2 / 3 * x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (2 / 3 * x)
    rw [norm_one] at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [h, norm_zero] at hP
    linarith
  · intro h
    have hx2 : x = 1 / 2 := by linear_combination -h / 2
    rw [hx2, norm_div, norm_one, Complex.norm_ofNat] at hx
    linarith
  · rw [norm_div, div_lt_one (by linarith), norm_mul, h43]
    linarith

private lemma l44_alg1 {x P Q : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    16 / 15 * x ^ 2 / P * (P / Q) = 16 / 15 * (x ^ 2 / Q) := by
  field_simp

private lemma l44_alg2 {x P Q : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    4 / 15 * (4 / 3) ^ 5 * x ^ 5 / P ^ 3 * (P / Q) =
      256 / 243 * (x ^ 4 / P ^ 2) + 4096 / 3645 * (x ^ 5 / (P ^ 2 * Q)) - 1 / 3 * (4 / 3) ^ 4 * x ^ 4 / P ^ 2 := by
  field_simp
  ring

private lemma l44_alg3 {x P : ℂ} (i : ℕ) :
    3 / 5 * (4 / 3) ^ (i + 2) * x ^ (i + 2) / P ^ (i + 1) = 16 / 15 * x ^ 2 / P * (4 / 3 * x / P) ^ i := by
  rw [div_pow (4 / 3 * x) P i, mul_pow (4 / 3 : ℂ) x i, pow_add (4 / 3 : ℂ) i 2, pow_add x i 2, pow_succ P i]
  generalize (4 / 3 : ℂ) ^ i = A
  generalize x ^ i = X
  generalize P ^ i = R
  ring

private lemma l44_alg4 {x P : ℂ} (i : ℕ) :
    4 / 15 * (4 / 3) ^ (i + 5) * x ^ (i + 5) / P ^ (i + 3) =
      4 / 15 * (4 / 3) ^ 5 * x ^ 5 / P ^ 3 * (4 / 3 * x / P) ^ i := by
  rw [div_pow (4 / 3 * x) P i, mul_pow (4 / 3 : ℂ) x i, pow_add (4 / 3 : ℂ) i 5, pow_add x i 5, pow_add P i 3]
  generalize (4 / 3 : ℂ) ^ i = A
  generalize x ^ i = X
  generalize P ^ i = R
  ring

private lemma l44_w1 {x : ℂ} (hP : (1 - 2 / 3 * x) ≠ 0) :
    (1 : ℂ) - 4 / 3 * x / (1 - 2 / 3 * x) = (1 - 2 * x) / (1 - 2 / 3 * x) := by
  rw [eq_div_iff hP, sub_mul, div_mul_cancel₀ _ hP]
  ring

private lemma l44_B1c_eq {x : ℂ} (hx : ‖x‖ < 1 / 4) :
    B1c x = l44_gs (fun m => (l44_d1 m : ℂ)) 1 ((2 / 3 : ℝ) : ℂ) x := by
  obtain ⟨hP, h2x, hw⟩ := l44_small hx
  have hval : 16 / 15 * x ^ 2 / (1 - 2 / 3 * x) * (1 - 4 / 3 * x / (1 - 2 / 3 * x))⁻¹ = B1c x := by
    rw [l44_w1 hP, inv_div, B1c]
    exact l44_alg1 hP h2x
  have hG := (hasSum_geometric_of_norm_lt_one hw).mul_left (16 / 15 * x ^ 2 / (1 - 2 / 3 * x))
  rw [hval] at hG
  have hS : HasSum (fun m => (l44_d1 m : ℂ) * x ^ m / (1 - ((2 / 3 : ℝ) : ℂ) * x) ^ (m - 1)) (B1c x) := by
    rw [← hasSum_nat_add_iff' 2]
    have h0 : ∑ i ∈ Finset.range 2, (l44_d1 i : ℂ) * x ^ i / (1 - ((2 / 3 : ℝ) : ℂ) * x) ^ (i - 1) = 0 := by
      simp [Finset.sum_range_succ, l44_d1]
    rw [h0, sub_zero]
    convert hG using 1
    funext i
    simp only [l44_d1, show 2 ≤ i + 2 from by omega, ite_true, show i + 2 - 1 = i + 1 from by omega]
    push_cast
    exact l44_alg3 i
  exact hS.tsum_eq.symm

private lemma l44_B2c_eq {x : ℂ} (hx : ‖x‖ < 1 / 4) :
    B2c x = l44_gs (fun m => (l44_d2 m : ℂ)) 2 ((2 / 3 : ℝ) : ℂ) x := by
  obtain ⟨hP, h2x, hw⟩ := l44_small hx
  have hval : 4 / 15 * (4 / 3) ^ 5 * x ^ 5 / (1 - 2 / 3 * x) ^ 3 * (1 - 4 / 3 * x / (1 - 2 / 3 * x))⁻¹ =
      B2c x - 1 / 3 * (4 / 3) ^ 4 * x ^ 4 / (1 - 2 / 3 * x) ^ 2 := by
    rw [l44_w1 hP, inv_div, B2c]
    exact l44_alg2 hP h2x
  have hG := (hasSum_geometric_of_norm_lt_one hw).mul_left
    (4 / 15 * (4 / 3) ^ 5 * x ^ 5 / (1 - 2 / 3 * x) ^ 3)
  rw [hval] at hG
  have hS : HasSum (fun m => (l44_d2 m : ℂ) * x ^ m / (1 - ((2 / 3 : ℝ) : ℂ) * x) ^ (m - 2)) (B2c x) := by
    rw [← hasSum_nat_add_iff' 5]
    have h0 : ∑ i ∈ Finset.range 5, (l44_d2 i : ℂ) * x ^ i / (1 - ((2 / 3 : ℝ) : ℂ) * x) ^ (i - 2) =
        1 / 3 * (4 / 3) ^ 4 * x ^ 4 / (1 - 2 / 3 * x) ^ 2 := by
      simp [Finset.sum_range_succ, l44_d2, l44_e]
    rw [h0]
    convert hG using 1
    funext i
    simp only [l44_d2, l44_e, show 4 ≤ i + 5 from by omega, ite_true, show i + 5 ≠ 4 from by omega, ite_false,
      show i + 5 - 2 = i + 3 from by omega]
    push_cast
    exact l44_alg4 i
  exact hS.tsum_eq.symm

/-! ### `B` and `B²` as series of the same shape -/

/-- `d_m = b_{2m-1}/vᵐ` for `m ≥ 2`, with `b_{2m-1} = coeff φ m`. -/
private noncomputable def l44_dB (τ : ℝ) (φ : ℂ → ℂ) (m : ℕ) : ℂ :=
  if 2 ≤ m then coeff φ m / (vτ τ : ℂ) ^ m else 0

private lemma l44_dB_small (τ : ℝ) (φ : ℂ → ℂ) {m : ℕ} (hm : m < 2) : l44_dB τ φ m = 0 := by
  simp [l44_dB, show ¬ 2 ≤ m by omega]

/-- `B(ξ) = ∑_{m ≥ 2} d_m ξᵐ/(1 + βξ)^{m-1}`. -/
private lemma l44_Bser_eq {τ : ℝ} (hv : vτ τ ≠ 0) (φ : ℂ → ℂ) (ξ : ℂ) :
    Bser τ φ ξ = l44_gs (l44_dB τ φ) 1 (-(βτ τ : ℂ)) ξ := by
  unfold Bser l44_gs
  congr 1
  funext m
  by_cases hm : 2 ≤ m
  · simp only [hm, ite_true, l44_dB]
    have hv' : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast hv
    have hrel : (vτ τ : ℂ) + (τ : ℂ) * ξ = (vτ τ : ℂ) * (1 - -(βτ τ : ℂ) * ξ) := by
      simp only [βτ]
      push_cast
      field_simp
      ring
    rw [hrel, mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
    ring
  · simp [hm, l44_dB]

/-- A Cauchy square of a sequence vanishing below `2` vanishes below `4`. -/
private lemma l44_cmul_small {d : ℕ → ℂ} (hd : ∀ k < 2, d k = 0) {n : ℕ} (hn : n < 4) : cmul d d n = 0 := by
  unfold cmul
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  by_cases hk2 : k < 2
  · rw [hd k hk2, zero_mul]
  · rw [hd (n - k) (by omega), mul_zero]

/-- `B(ξ)² = ∑_{m ≥ 4} C_m ξᵐ/(1 + βξ)^{m-2}` with `C = d * d` (Cauchy square), for `|ξ| < 1/8`. -/
private lemma l44_Bsq_eq {τ : ℝ} (hv : vτ τ ≠ 0) (hβ0 : 0 ≤ βτ τ) (hβ : βτ τ ≤ 2 / 3) {φ : ℂ → ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hdB : ∀ m, ‖l44_dB τ φ m‖ ≤ K * (4 / 3) ^ m) {ξ : ℂ} (hξ : ‖ξ‖ < 1 / 8) :
    Bser τ φ ξ ^ 2 = l44_gs (cmul (l44_dB τ φ) (l44_dB τ φ)) 2 (-(βτ τ : ℂ)) ξ := by
  have hβξ : ‖-(βτ τ : ℂ) * ξ‖ ≤ 1 / 12 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hβ0]
    nlinarith [norm_nonneg ξ]
  have hPn : 11 / 12 ≤ ‖1 - -(βτ τ : ℂ) * ξ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(βτ τ : ℂ) * ξ)
    rw [norm_one] at this
    linarith
  have hP0 : (1 - -(βτ τ : ℂ) * ξ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hPn
    linarith
  set P : ℂ := 1 - -(βτ τ : ℂ) * ξ with hP
  set d := l44_dB τ φ with hd
  have hwn : ‖ξ / P‖ ≤ 1 / 4 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith
  have hterm : ∀ m, d m * ξ ^ m / P ^ (m - 1) = P * (d m * (ξ / P) ^ m) := by
    intro m
    rcases m with _ | k
    · simp [hd, l44_dB_small τ φ (by norm_num : 0 < 2)]
    · simp only [Nat.add_sub_cancel, div_pow, pow_succ]
      field_simp
  have hsumm : Summable (fun m => ‖d m * (ξ / P) ^ m‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)).mul_left K)
    rw [norm_mul, norm_pow]
    calc ‖d m‖ * ‖ξ / P‖ ^ m ≤ (K * (4 / 3) ^ m) * (1 / 4) ^ m :=
          mul_le_mul (hdB m) (pow_le_pow_left₀ (norm_nonneg _) hwn _) (by positivity)
            (mul_nonneg hK (by positivity))
      _ = K * (1 / 3) ^ m := by rw [mul_assoc, ← mul_pow]; norm_num
  have hB : Bser τ φ ξ = P * ∑' m, d m * (ξ / P) ^ m := by
    rw [l44_Bser_eq hv, l44_gs, ← tsum_mul_left]
    exact tsum_congr hterm
  rw [hB, mul_pow, sq (∑' m, d m * (ξ / P) ^ m),
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hsumm hsumm, ← tsum_mul_left]
  unfold l44_gs
  refine tsum_congr fun n => ?_
  rw [← hP]
  have hc : ∑ k ∈ Finset.range (n + 1), d k * (ξ / P) ^ k * (d (n - k) * (ξ / P) ^ (n - k)) =
      cmul d d n * (ξ / P) ^ n := by
    unfold cmul
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show (ξ / P) ^ n = (ξ / P) ^ k * (ξ / P) ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
    ring
  rw [hc]
  rcases lt_or_ge n 2 with hn | hn
  · rw [l44_cmul_small (fun k hk => l44_dB_small τ φ hk) (by omega : n < 4)]
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel, div_pow, pow_add]
    field_simp

/-! ### The area theorem for `G_τ`, for `9/20 ≤ τ ≤ 1/2` -/

/-- `A_j = (2j - 1)|b_{2j-1}|²` for `j ≥ 2`. -/
private noncomputable def l44_A (φ : ℂ → ℂ) (j : ℕ) : ℝ :=
  if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0

private lemma l44_A_nonneg (φ : ℂ → ℂ) (j : ℕ) : 0 ≤ l44_A φ j := by
  unfold l44_A
  split_ifs with hj
  · have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    exact mul_nonneg (by linarith) (by positivity)
  · exact le_refl 0

private lemma l44_fT_mem_S {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) :
    InS (fT f τ) := by
  have hτ : -(τ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  exact sec3_koebe_transform_mem_S_proved f hf _ hτ

/-- Re-indexing the area sum: `∑_n n |b_n|²` over the Laurent coefficients of `G_τ` is `|c|² + ∑_{j ≥ 2} (2j - 1)
|coeff φ j|²`. -/
private lemma l44_area_reindex {c : ℂ} {φ : ℂ → ℂ} {S : ℝ}
    (hS : HasSum (fun n : ℕ => (n : ℝ) * ‖Glaurent c φ n‖ ^ 2) S) :
    HasSum (fun j : ℕ => if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) (S - ‖c‖ ^ 2) := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b hab => by simp at hab; omega
  have hodd : HasSum ((fun n : ℕ => (n : ℝ) * ‖Glaurent c φ n‖ ^ 2) ∘ (fun m : ℕ => 2 * m + 1)) S := by
    rw [hinj.hasSum_iff]
    · exact hS
    · intro n hn
      have hev : n % 2 = 0 := by
        by_contra hne
        exact hn ⟨n / 2, by simp only; omega⟩
      have h1 : n ≠ 1 := by omega
      have h2 : ¬ n % 2 = 1 := by omega
      simp [Glaurent, h1, h2]
  have h1 := (hasSum_nat_add_iff' 1).mpr hodd
  rw [← hasSum_nat_add_iff' 2]
  convert h1 using 1
  · funext m
    have ha : 2 * (m + 1) + 1 ≠ 1 := by omega
    have hb : (2 * (m + 1) + 1) % 2 = 1 := by omega
    have hc' : (2 * (m + 1) + 1 + 1) / 2 = m + 2 := by omega
    have hd : 2 ≤ m + 2 := by omega
    simp only [Function.comp, Glaurent, ha, hb, hc', hd, ↓reduceIte]
    push_cast
    ring
  · simp [Finset.sum_range_succ, Glaurent]

/-- The area theorem for `G_τ` (also at `τ = 1/2`): `∑_{j ≥ 2} (2j - 1)|b_{2j-1}|² ≤ η`. -/
private lemma l44_area (hArea : FactArea) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) :
    Summable (l44_A φ) ∧ ∑' j, l44_A φ j ≤ etadef (cOf f τ) := by
  have hg := l44_fT_mem_S hf h1 h2
  obtain ⟨hsum, hle⟩ := hArea (Gtau φ) (Glaurent (cOf f τ) φ) (gtau_differentiableOn hφ.1)
    (gtau_injOn hg hφ) (fun ζ hζ => gtau_hasSum hg hφ hζ)
  have ht : HasSum (l44_A φ) (∑' n : ℕ, (n : ℝ) * ‖Glaurent (cOf f τ) φ n‖ ^ 2 - ‖cOf f τ‖ ^ 2) :=
    l44_area_reindex hsum.hasSum
  rw [ht.tsum_eq]
  refine ⟨ht.summable, ?_⟩
  simp only [etadef]
  linarith

/-! ### The coefficient bounds from the area theorem -/

/-- `|b_{2j-1}| ≤ (3/5)√η` for `j ≥ 2` (from `3|b_{2j-1}|² ≤ η`, `1/3 ≤ 9/25`). -/
private lemma l44_b_le {φ : ℂ → ℂ} {η : ℝ} (hs : Summable (l44_A φ)) (hle : ∑' j, l44_A φ j ≤ η) {j : ℕ}
    (hj : 2 ≤ j) : ‖coeff φ j‖ ≤ 3 / 5 * Real.sqrt η := by
  have h1 : l44_A φ j ≤ η := (hs.le_tsum j (fun k _ => l44_A_nonneg φ k)).trans hle
  have hη : 0 ≤ η := (tsum_nonneg (l44_A_nonneg φ)).trans hle
  simp only [l44_A, hj, ite_true] at h1
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hsq : ‖coeff φ j‖ ^ 2 ≤ (3 / 5 * Real.sqrt η) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hη]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (j : ℝ) - 4) (sq_nonneg ‖coeff φ j‖)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- `|d_m| ≤ √η (3/5)(4/3)ᵐ`. -/
private lemma l44_dB_le {τ : ℝ} (hv : 3 / 4 ≤ vτ τ) {φ : ℂ → ℂ} {η : ℝ}
    (hb : ∀ j, 2 ≤ j → ‖coeff φ j‖ ≤ 3 / 5 * Real.sqrt η) (m : ℕ) :
    ‖l44_dB τ φ m‖ ≤ Real.sqrt η * l44_d1 m := by
  unfold l44_dB l44_d1
  split_ifs with hm
  · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      div_le_iff₀ (pow_pos (by linarith) _)]
    have h1 : 1 ≤ (4 / 3 * vτ τ) ^ m := one_le_pow₀ (by linarith)
    calc ‖coeff φ m‖ ≤ 3 / 5 * Real.sqrt η := hb m hm
      _ ≤ 3 / 5 * Real.sqrt η * (4 / 3 * vτ τ) ^ m := le_mul_of_one_le_right (by positivity) h1
      _ = Real.sqrt η * (3 / 5 * (4 / 3) ^ m) * vτ τ ^ m := by rw [mul_pow]; ring
  · simp

/-- `XY ≤ (c/2)(aX² + bY²)` when `c²ab ≥ 1`. -/
private lemma l44_amgm {X Y a b c : ℝ} (ha : 0 < a) (hc : 0 < c) (h : 1 ≤ c ^ 2 * a * b) :
    X * Y ≤ c / 2 * (a * X ^ 2 + b * Y ^ 2) := by
  have hca : 0 < c * a := mul_pos hc ha
  have key : c * a * (c * a * X ^ 2 + c * b * Y ^ 2 - 2 * X * Y) =
      (c * a * X - Y) ^ 2 + (c ^ 2 * a * b - 1) * Y ^ 2 := by ring
  have hnn : 0 ≤ c * a * (c * a * X ^ 2 + c * b * Y ^ 2 - 2 * X * Y) := by
    rw [key]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
  have := (mul_nonneg_iff_of_pos_left hca).mp hnn
  nlinarith

/-- `e_m² (2k - 1)(2l - 1) ≥ 1` for `k, l ≥ 2`, `k + l = m`. -/
private lemma l44_weight {m k : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ m - k) (hkm : k ≤ m) :
    1 ≤ l44_e m ^ 2 * (2 * (k : ℝ) - 1) * (2 * ((m - k : ℕ) : ℝ) - 1) := by
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : (2 : ℝ) ≤ ((m - k : ℕ) : ℝ) := by exact_mod_cast hl
  by_cases h4 : m = 4
  · have hk2 : k = 2 := by omega
    have hl2 : m - k = 2 := by omega
    rw [hl2, hk2]
    simp [l44_e, h4]
    norm_num
  · have h5 : 5 ≤ m := by omega
    have hKL : (k : ℝ) + ((m - k : ℕ) : ℝ) = m := by
      rw [Nat.cast_sub hkm]
      ring
    have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast h5
    simp only [l44_e, h4, ite_false]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 2) (by linarith : (0 : ℝ) ≤ ((m - k : ℕ) : ℝ) - 2)]

/-- One term of the Cauchy square: `|d_k d_{m-k}| ≤ (4/3)ᵐ (e_m/2)(A_k + A_{m-k})`. -/
private lemma l44_cmul_term {τ : ℝ} (hv : 3 / 4 ≤ vτ τ) (φ : ℂ → ℂ) {m k : ℕ} (hkm : k ≤ m) :
    ‖l44_dB τ φ k * l44_dB τ φ (m - k)‖ ≤
      (4 / 3) ^ m * (l44_e m / 2) * (l44_A φ k + l44_A φ (m - k)) := by
  have hA0 := l44_A_nonneg φ k
  have hA1 := l44_A_nonneg φ (m - k)
  have he := l44_e_pos m
  have hRHS : 0 ≤ (4 / 3) ^ m * (l44_e m / 2) * (l44_A φ k + l44_A φ (m - k)) := by positivity
  by_cases hk2 : 2 ≤ k
  · by_cases hl2 : 2 ≤ m - k
    · have hvpos : 0 < vτ τ := by linarith
      simp only [l44_dB, hk2, hl2, ite_true, l44_A]
      rw [norm_mul, norm_div, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hvpos.le]
      have hvm : 1 / vτ τ ^ m ≤ (4 / 3) ^ m := by
        rw [div_le_iff₀ (pow_pos hvpos _), ← mul_pow]
        exact one_le_pow₀ (by linarith)
      have hprod : ‖coeff φ k‖ / vτ τ ^ k * (‖coeff φ (m - k)‖ / vτ τ ^ (m - k)) =
          ‖coeff φ k‖ * ‖coeff φ (m - k)‖ * (1 / vτ τ ^ m) := by
        rw [show vτ τ ^ m = vτ τ ^ k * vτ τ ^ (m - k) by rw [← pow_add, Nat.add_sub_cancel' hkm]]
        field_simp
      rw [hprod]
      have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hamgm := l44_amgm (X := ‖coeff φ k‖) (Y := ‖coeff φ (m - k)‖) (by linarith : 0 < 2 * (k : ℝ) - 1) he
        (l44_weight hk2 hl2 hkm)
      calc ‖coeff φ k‖ * ‖coeff φ (m - k)‖ * (1 / vτ τ ^ m)
          ≤ ‖coeff φ k‖ * ‖coeff φ (m - k)‖ * (4 / 3) ^ m :=
            mul_le_mul_of_nonneg_left hvm (by positivity)
        _ ≤ l44_e m / 2 * ((2 * (k : ℝ) - 1) * ‖coeff φ k‖ ^ 2 +
              (2 * ((m - k : ℕ) : ℝ) - 1) * ‖coeff φ (m - k)‖ ^ 2) * (4 / 3) ^ m :=
            mul_le_mul_of_nonneg_right hamgm (by positivity)
        _ = _ := by ring
    · simp only [l44_dB, hl2, ite_false, mul_zero, norm_zero]
      exact hRHS
  · simp only [l44_dB, hk2, ite_false, zero_mul, norm_zero]
    exact hRHS

/-- `|C_m| ≤ η e_m (4/3)ᵐ` for the Cauchy square `C = d * d`, by the area theorem. -/
private lemma l44_cmul_le {τ : ℝ} (hv : 3 / 4 ≤ vτ τ) {φ : ℂ → ℂ} {η : ℝ} (hs : Summable (l44_A φ))
    (hle : ∑' j, l44_A φ j ≤ η) (m : ℕ) :
    ‖cmul (l44_dB τ φ) (l44_dB τ φ) m‖ ≤ η * l44_d2 m := by
  have hη : 0 ≤ η := (tsum_nonneg (l44_A_nonneg φ)).trans hle
  by_cases hm : m < 4
  · rw [l44_cmul_small (fun k hk => l44_dB_small τ φ hk) hm, norm_zero]
    exact mul_nonneg hη (l44_d2_nonneg m)
  · have hm : 4 ≤ m := by omega
    have hd2 : l44_d2 m = l44_e m * (4 / 3) ^ m := by simp [l44_d2, hm]
    have hrefl : ∑ k ∈ Finset.range (m + 1), l44_A φ (m - k) = ∑ k ∈ Finset.range (m + 1), l44_A φ k := by
      have := Finset.sum_range_reflect (l44_A φ) (m + 1)
      simp only [Nat.add_sub_cancel] at this
      exact this
    have hpart : ∑ k ∈ Finset.range (m + 1), l44_A φ k ≤ η :=
      (hs.sum_le_tsum _ (fun k _ => l44_A_nonneg φ k)).trans hle
    have he := l44_e_pos m
    calc ‖cmul (l44_dB τ φ) (l44_dB τ φ) m‖
        ≤ ∑ k ∈ Finset.range (m + 1), ‖l44_dB τ φ k * l44_dB τ φ (m - k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (m + 1), (4 / 3) ^ m * (l44_e m / 2) * (l44_A φ k + l44_A φ (m - k)) :=
          Finset.sum_le_sum fun k hk => l44_cmul_term hv φ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      _ = (4 / 3) ^ m * (l44_e m / 2) * (2 * ∑ k ∈ Finset.range (m + 1), l44_A φ k) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hrefl, two_mul]
      _ ≤ (4 / 3) ^ m * (l44_e m / 2) * (2 * η) := by gcongr
      _ = η * l44_d2 m := by rw [hd2]; ring

/-! ### Lemma 4.4(iii) -/

private lemma l44_v_ge {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 3 / 4 ≤ vτ τ := by
  simp only [vτ]
  nlinarith

private lemma l44_beta {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 0 ≤ βτ τ ∧ βτ τ ≤ 2 / 3 := by
  have hv := l44_v_ge h1 h2
  refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
  rw [βτ, div_le_iff₀ (by linarith)]
  simp only [vτ]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - τ) (by linarith : (0 : ℝ) ≤ τ + 2)]

/-- Lemma 4.4(iii) (sec_04_near.tex:176-179): `B ≪ √η B₁` and `B² ≪ η B₂` (coefficients in `ξ`). -/
theorem lem_4_4_iii_proved (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    Majorizes (coeff (Bser τ φ)) (fun n => Real.sqrt (etadef (cOf f τ)) * (coeff B1c n).re) ∧
      Majorizes (coeff (fun ξ => Bser τ φ ξ ^ 2)) (fun n => etadef (cOf f τ) * (coeff B2c n).re) := by
  obtain ⟨hs, hle⟩ := l44_area hArea hf h1 h2 hφ
  have hη : 0 ≤ etadef (cOf f τ) := (tsum_nonneg (l44_A_nonneg φ)).trans hle
  have hv := l44_v_ge h1 h2
  have hv0 : vτ τ ≠ 0 := by linarith
  obtain ⟨hβ0, hβ⟩ := l44_beta h1 h2
  have hdB : ∀ m, ‖l44_dB τ φ m‖ ≤ Real.sqrt (etadef (cOf f τ)) * l44_d1 m :=
    l44_dB_le hv (fun j hj => l44_b_le hs hle hj)
  have hdB' : ∀ m, ‖l44_dB τ φ m‖ ≤ Real.sqrt (etadef (cOf f τ)) * (4 / 3) ^ m := fun m =>
    (hdB m).trans (mul_le_mul_of_nonneg_left (l44_d1_le m) (Real.sqrt_nonneg _))
  have hC : ∀ m, ‖cmul (l44_dB τ φ) (l44_dB τ φ) m‖ ≤ etadef (cOf f τ) * l44_d2 m := l44_cmul_le hv hs hle
  have hC' : ∀ m, ‖cmul (l44_dB τ φ) (l44_dB τ φ) m‖ ≤ etadef (cOf f τ) * (4 / 3) ^ m := fun m =>
    (hC m).trans (mul_le_mul_of_nonneg_left (l44_d2_le m) hη)
  have hqβ : ‖-(βτ τ : ℂ)‖ ≤ 2 / 3 := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hβ0]
    exact hβ
  have hcB : ∀ n, coeff (Bser τ φ) n = l44_gc (l44_dB τ φ) 1 (-(βτ τ : ℂ)) n :=
    l44_coeff_gs (Real.sqrt_nonneg _) (by norm_num) (fun m hm => l44_dB_small τ φ (by omega)) hdB' one_pos
      (fun ξ _ => l44_Bser_eq hv0 φ ξ)
  have hcB1 : ∀ n, coeff B1c n = l44_gc (fun m => (l44_d1 m : ℂ)) 1 ((2 / 3 : ℝ) : ℂ) n :=
    l44_coeff_gs zero_le_one (by norm_num) (fun m hm => by simp [l44_d1, show ¬ 2 ≤ m by omega])
      (l44_real_norm_le l44_d1_nonneg l44_d1_le) (by norm_num : (0 : ℝ) < 1 / 4)
      (fun ξ hξ => l44_B1c_eq (mem_ball_zero_iff.mp hξ))
  have hcB2 : ∀ n, coeff (fun ξ => Bser τ φ ξ ^ 2) n =
      l44_gc (cmul (l44_dB τ φ) (l44_dB τ φ)) 2 (-(βτ τ : ℂ)) n :=
    l44_coeff_gs hη (by norm_num) (fun m hm => l44_cmul_small (fun k hk => l44_dB_small τ φ hk) (by omega))
      hC' (by norm_num : (0 : ℝ) < 1 / 8)
      (fun ξ hξ => l44_Bsq_eq hv0 hβ0 hβ (Real.sqrt_nonneg _) hdB' (mem_ball_zero_iff.mp hξ))
  have hcB2' : ∀ n, coeff B2c n = l44_gc (fun m => (l44_d2 m : ℂ)) 2 ((2 / 3 : ℝ) : ℂ) n :=
    l44_coeff_gs zero_le_one (by norm_num) (fun m hm => by simp [l44_d2, show ¬ 4 ≤ m by omega])
      (l44_real_norm_le l44_d2_nonneg l44_d2_le) (by norm_num : (0 : ℝ) < 1 / 4)
      (fun ξ hξ => l44_B2c_eq (mem_ball_zero_iff.mp hξ))
  refine ⟨fun n => ?_, fun n => ?_⟩
  · show ‖coeff (Bser τ φ) n‖ ≤ Real.sqrt (etadef (cOf f τ)) * (coeff B1c n).re
    rw [hcB n, hcB1 n]
    exact l44_gc_le _ _ _ 1 _ _ hqβ hdB n
  · show ‖coeff (fun ξ => Bser τ φ ξ ^ 2) n‖ ≤ etadef (cOf f τ) * (coeff B2c n).re
    rw [hcB2 n, hcB2' n]
    exact l44_gc_le _ _ _ 2 _ _ hqβ hC n

end Robinson.Proofs
