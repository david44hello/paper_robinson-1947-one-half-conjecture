/-
Robinson/Proofs/NearP_C.lean — the tail bound of the first variation (Lemma 4.5(ii)).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Proofs.NearP_A
import Robinson.Proofs.Majorants

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Products of binomial series -/

/-- The coefficients of `(1 - a x)^{-(k+1)}`. -/
noncomputable def binCo {R : Type*} [Semiring R] (k : ℕ) (a : R) (n : ℕ) : R := ((n + k).choose k : R) * a ^ n

lemma summable_norm_binC (k : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n => ‖((n + k).choose k : ℂ) * w ^ n‖) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k (r := ‖w‖) (by rwa [norm_norm])).summable
  refine h.congr (fun n => ?_)
  rw [norm_mul, norm_pow, Complex.norm_natCast]

lemma summable_norm_binR (k : ℕ) {w : ℝ} (hw : ‖w‖ < 1) :
    Summable (fun n => ‖((n + k).choose k : ℝ) * w ^ n‖) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k (r := ‖w‖) (by rwa [norm_norm])).summable
  refine h.congr (fun n => ?_)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg (Nat.cast_nonneg _)]

lemma binCo_term {R : Type*} [CommRing R] (m n k : ℕ) (hk : k ≤ n) (α γ z : R) :
    ((k + m).choose m : R) * (α * z) ^ k * (((n - k + 2).choose 2 : R) * (γ * z) ^ (n - k)) =
      binCo m α k * binCo 2 γ (n - k) * z ^ n := by
  have hz : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  simp only [binCo]
  rw [hz, mul_pow, mul_pow]
  ring

/-- `(1 - αz)^{-(m+1)} (1 - γz)^{-3}` as a power series in `z` (complex). -/
lemma hasSum_binCo_mulC (m : ℕ) {α γ z : ℂ} (hα : ‖α * z‖ < 1) (hγ : ‖γ * z‖ < 1) :
    HasSum (fun n => cmul (binCo m α) (binCo 2 γ) n * z ^ n)
      (1 / (1 - α * z) ^ (m + 1) * (1 / (1 - γ * z) ^ (2 + 1))) := by
  have hf := hasSum_choose_mul_geometric_of_norm_lt_one m hα
  have hg := hasSum_choose_mul_geometric_of_norm_lt_one 2 hγ
  have h := hasSum_sum_range_mul_of_summable_norm (summable_norm_binC m hα) (summable_norm_binC 2 hγ)
  rw [hf.tsum_eq, hg.tsum_eq] at h
  refine h.congr_fun (fun n => ?_)
  simp only [cmul, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k hk =>
    (binCo_term m n k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) α γ z).symm)

/-- `(1 - αz)^{-(m+1)} (1 - γz)^{-3}` as a power series in `z` (real). -/
lemma hasSum_binCo_mulR (m : ℕ) {α γ z : ℝ} (hα : ‖α * z‖ < 1) (hγ : ‖γ * z‖ < 1) :
    HasSum (fun n => cmul (binCo m α) (binCo 2 γ) n * z ^ n)
      (1 / (1 - α * z) ^ (m + 1) * (1 / (1 - γ * z) ^ (2 + 1))) := by
  have hf := hasSum_choose_mul_geometric_of_norm_lt_one m hα
  have hg := hasSum_choose_mul_geometric_of_norm_lt_one 2 hγ
  have h := hasSum_sum_range_mul_of_summable_norm (summable_norm_binR m hα) (summable_norm_binR 2 hγ)
  rw [hf.tsum_eq, hg.tsum_eq] at h
  refine h.congr_fun (fun n => ?_)
  simp only [cmul, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k hk =>
    (binCo_term m n k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) α γ z).symm)

/-- Multiplying a power series by `C z^p` shifts its coefficients by `p`. -/
lemma hasSum_shift {𝕜 : Type*} [RCLike 𝕜] {a : ℕ → 𝕜} {z S : 𝕜} (h : HasSum (fun n => a n * z ^ n) S)
    (C : 𝕜) (p : ℕ) :
    HasSum (fun n => (if p ≤ n then C * a (n - p) else 0) * z ^ n) (C * z ^ p * S) := by
  refine (hasSum_nat_add_iff' p).mp ?_
  have hz : ∑ i ∈ Finset.range p, (if p ≤ i then C * a (i - p) else 0) * z ^ i = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      have hi' : ¬ (p ≤ i) := by simp only [Finset.mem_range] at hi; omega
      rw [if_neg hi', zero_mul])
  rw [hz, sub_zero]
  convert h.mul_left (C * z ^ p) using 1
  funext n
  have hn : p ≤ n + p := by omega
  rw [if_pos hn, Nat.add_sub_cancel, pow_add]
  ring

/-- A power series that sums to `g` on a disc gives the coefficients `coeff g n`. -/
lemma coeff_eq_of_hasSum {g : ℂ → ℂ} {a : ℕ → ℂ} {r : NNReal} (hr : 0 < r)
    (hs : Summable (fun n => ‖a n‖ * (r : ℝ) ^ n))
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => a n * z ^ n) (g z)) (n : ℕ) : coeff g n = a n := by
  have hp : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ a) 0 (r : ENNReal) := by
    refine ⟨?_, ENNReal.coe_pos.mpr hr, ?_⟩
    · refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
      simpa only [FormalMultilinearSeries.ofScalars_norm] using hs
    · intro y hy
      rw [Metric.eball_coe, mem_ball_zero_iff] at hy
      simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
      exact h y hy
  have hp' := hp.hasFPowerSeriesAt
  have heq := hp'.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hp'
  have h2 := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ heq
  unfold coeff
  exact congrFun h2 n

lemma binCo_nonneg {k : ℕ} {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ binCo k a n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha n)

lemma cmul_nonneg {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) : 0 ≤ cmul a b n :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (ha k) (hb (n - k)))

/-- `‖b‖ ≤ b⁺` gives `binCo k b ≪ binCo k b⁺`. -/
lemma binCo_maj {k : ℕ} {b : ℂ} {bp : ℝ} (hb : ‖b‖ ≤ bp) : Majorizes (binCo k b) (binCo k bp) := by
  intro n
  unfold binCo
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb n) (Nat.cast_nonneg _)

/-- If `Z ≥ 0` and `∑ Zₙ sⁿ` converges, then `∑ (n+1) Zₙ yⁿ` converges for `0 ≤ y < s`. -/
lemma summable_succ_mul {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {s y : ℝ} (hy : 0 ≤ y) (hys : y < s)
    (hs : Summable (fun n : ℕ => Z n * s ^ n)) : Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * y ^ n) := by
  have hs0 : 0 < s := lt_of_le_of_lt hy hys
  have hq0 : 0 ≤ y / s := div_nonneg hy hs0.le
  have hq1 : y / s < 1 := (div_lt_one hs0).mpr hys
  have hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) * (y / s) ^ n) := by
    have := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 (r := y / s)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)).summable
    refine this.congr (fun n => ?_)
    simp [Nat.choose_one_right]
  obtain ⟨C, hC⟩ : ∃ C, ∀ n : ℕ, ((n : ℝ) + 1) * (y / s) ^ n ≤ C :=
    ⟨_, fun n => hgeo.le_tsum n (fun m _ => by positivity)⟩
  refine Summable.of_nonneg_of_le (fun n => by have := hZ n; positivity) (fun n => ?_) (hs.mul_left C)
  have hyn : y ^ n = s ^ n * (y / s) ^ n := by
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero n hs0.ne')]
  rw [hyn]
  have h1 := hC n
  have h2 := mul_nonneg (hZ n) (pow_nonneg hs0.le n)
  nlinarith

/-! ### The terms of `𝔥` and `𝔴` -/

/-- The terms of `hCoef Z x`. -/
noncomputable def hTerm (Z : ℕ → ℝ) (x : ℝ) (i : ℕ) : ℝ := if 1 ≤ i then Z (2 * i + 1) * x ^ (2 * i) else 0

/-- The terms of `wCoef Z x`. -/
noncomputable def wTerm (Z : ℕ → ℝ) (x : ℝ) (i : ℕ) : ℝ :=
  if 1 ≤ i then ((2 * (i : ℝ) + 10 / 3) * Z (2 * i + 1) + ((i : ℝ) + 1) * Z (2 * i + 2)) * x ^ (2 * i - 2) else 0

private lemma inj_odd' : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b h => by
  simp only at h
  omega

private lemma inj_even2' : Function.Injective (fun m : ℕ => 2 * m + 2) := fun a b h => by
  simp only at h
  omega

lemma summable_hTerm {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {y : ℝ} (hy : 0 < y)
    (hZs : Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * y ^ n)) : Summable (hTerm Z y) := by
  have hc := (hZs.comp_injective inj_odd').mul_left y⁻¹
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hc
  · unfold hTerm
    split_ifs
    · exact mul_nonneg (hZ _) (pow_nonneg hy.le _)
    · exact le_rfl
  · simp only [Function.comp_apply]
    unfold hTerm
    have e : y⁻¹ * ((((2 * j + 1 : ℕ) : ℝ) + 1) * Z (2 * j + 1) * y ^ (2 * j + 1)) =
        (2 * (j : ℝ) + 2) * (Z (2 * j + 1) * y ^ (2 * j)) := by
      push_cast
      rw [pow_succ]
      field_simp
      ring
    have hA0 : 0 ≤ Z (2 * j + 1) * y ^ (2 * j) := mul_nonneg (hZ _) (pow_nonneg hy.le _)
    refine le_trans ?_ (le_of_eq e.symm)
    split_ifs
    · nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    · positivity

lemma summable_wTerm {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {y : ℝ} (hy : 0 < y)
    (hZs : Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * y ^ n)) : Summable (wTerm Z y) := by
  have hc := ((hZs.comp_injective inj_odd').mul_left (10 / 3 * (y ^ 3)⁻¹)).add
    ((hZs.comp_injective inj_even2').mul_left (y ^ 4)⁻¹)
  have hy3 : 0 ≤ (y ^ 3)⁻¹ := by positivity
  have hy4 : 0 ≤ (y ^ 4)⁻¹ := by positivity
  have ht0 : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * Z n * y ^ n := fun n =>
    mul_nonneg (mul_nonneg (by positivity) (hZ n)) (pow_nonneg hy.le n)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hc
  · unfold wTerm
    split_ifs
    · exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) (hZ _)) (mul_nonneg (by positivity) (hZ _)))
        (pow_nonneg hy.le _)
    · exact le_rfl
  · simp only [Function.comp_apply]
    unfold wTerm
    split_ifs with hj
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hA0 : 0 ≤ Z (2 * (k + 1) + 1) * y ^ (2 * k) := mul_nonneg (hZ _) (pow_nonneg hy.le _)
      have hB0 : 0 ≤ Z (2 * (k + 1) + 2) * y ^ (2 * k) := mul_nonneg (hZ _) (pow_nonneg hy.le _)
      have e : 10 / 3 * (y ^ 3)⁻¹ * ((((2 * (k + 1) + 1 : ℕ) : ℝ) + 1) * Z (2 * (k + 1) + 1) *
            y ^ (2 * (k + 1) + 1)) +
          (y ^ 4)⁻¹ * ((((2 * (k + 1) + 2 : ℕ) : ℝ) + 1) * Z (2 * (k + 1) + 2) * y ^ (2 * (k + 1) + 2)) =
          10 / 3 * ((2 * (k : ℝ) + 4) * (Z (2 * (k + 1) + 1) * y ^ (2 * k))) +
            (2 * (k : ℝ) + 5) * (Z (2 * (k + 1) + 2) * y ^ (2 * k)) := by
        push_cast
        field_simp
        ring
      refine le_trans ?_ (le_of_eq e.symm)
      rw [show 2 * (k + 1) - 2 = 2 * k by omega]
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hA0, mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hB0]
    · exact add_nonneg (mul_nonneg (by positivity) (ht0 _)) (mul_nonneg hy4 (ht0 _))

lemma hTerm_sum (S : Finset ℕ) (f : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (x : ℝ) (i : ℕ) :
    hTerm (fun n => ∑ j ∈ S, f j * Z j n) x i = ∑ j ∈ S, f j * hTerm (Z j) x i := by
  by_cases hi : 1 ≤ i
  · simp only [hTerm, if_pos hi]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  · simp only [hTerm, if_neg hi, mul_zero, Finset.sum_const_zero]

lemma wTerm_sum (S : Finset ℕ) (f : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (x : ℝ) (i : ℕ) :
    wTerm (fun n => ∑ j ∈ S, f j * Z j n) x i = ∑ j ∈ S, f j * wTerm (Z j) x i := by
  by_cases hi : 1 ≤ i
  · simp only [wTerm, if_pos hi]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  · simp only [wTerm, if_neg hi, mul_zero, Finset.sum_const_zero]

lemma hTerm_mono {Z Z' : ℕ → ℝ} (h : ∀ n, Z n ≤ Z' n) {x : ℝ} (hx : 0 ≤ x) (i : ℕ) :
    hTerm Z x i ≤ hTerm Z' x i := by
  unfold hTerm
  split_ifs
  · exact mul_le_mul_of_nonneg_right (h _) (pow_nonneg hx _)
  · exact le_rfl

lemma wTerm_mono {Z Z' : ℕ → ℝ} (h : ∀ n, Z n ≤ Z' n) {x : ℝ} (hx : 0 ≤ x) (i : ℕ) :
    wTerm Z x i ≤ wTerm Z' x i := by
  unfold wTerm
  split_ifs
  · exact mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left (h _) (by positivity))
      (mul_le_mul_of_nonneg_left (h _) (by positivity))) (pow_nonneg hx _)
  · exact le_rfl

lemma hTerm_mono_x {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {x x' : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x') (i : ℕ) :
    hTerm Z x i ≤ hTerm Z x' i := by
  unfold hTerm
  split_ifs
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxx _) (hZ _)
  · exact le_rfl

lemma wTerm_mono_x {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {x x' : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x') (i : ℕ) :
    wTerm Z x i ≤ wTerm Z x' i := by
  unfold wTerm
  split_ifs
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxx _)
      (add_nonneg (mul_nonneg (by positivity) (hZ _)) (mul_nonneg (by positivity) (hZ _)))
  · exact le_rfl

/-! ### The majorants `Z^{(j)}` of `Π_j` and their sum `Z₆` -/

/-- The weight `10/33` on `j ≥ 6` (`1/√(2j-1) ≤ 10/33`). -/
noncomputable def cw6 (j : ℕ) : ℝ := if 6 ≤ j then 10 / 33 else 0

lemma cw6_nonneg (j : ℕ) : 0 ≤ cw6 j := by
  unfold cw6
  split_ifs <;> norm_num

/-- The coefficients of `Z^{(j)}(x) = 2(4/3)^j x^{j+1} (1 - ⅔x)^{-(j-2)} (1 - ν⁺x)^{-3}`. -/
noncomputable def zJ (νp : ℝ) (j n : ℕ) : ℝ :=
  if j + 1 ≤ n then 2 * (4 / 3 : ℝ) ^ j * cmul (binCo (j - 3) (2 / 3 : ℝ)) (binCo 2 νp) (n - (j + 1)) else 0

/-- `Z^{(j)}` as a function. -/
noncomputable def zJf (νp : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  2 * (4 / 3 : ℝ) ^ j * t ^ (j + 1) * (1 / (1 - 2 / 3 * t) ^ (j - 3 + 1) * (1 / (1 - νp * t) ^ (2 + 1)))

/-- The coefficients of `Z₆ = (10/33) ∑_{j ≥ 6} Z^{(j)}` (a finite sum for each `n`). -/
noncomputable def z6 (νp : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, cw6 j * zJ νp j n

lemma zJ_nonneg {νp : ℝ} (hν0 : 0 ≤ νp) (j n : ℕ) : 0 ≤ zJ νp j n := by
  unfold zJ
  split_ifs
  · exact mul_nonneg (by positivity)
      (cmul_nonneg (binCo_nonneg (by norm_num)) (binCo_nonneg hν0) _)
  · exact le_rfl

lemma z6_nonneg {νp : ℝ} (hν0 : 0 ≤ νp) (n : ℕ) : 0 ≤ z6 νp n :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (cw6_nonneg j) (zJ_nonneg hν0 j n))

lemma z6_one (νp : ℝ) : z6 νp 1 = 0 := by
  simp [z6, cw6]

lemma z6_two (νp : ℝ) : z6 νp 2 = 0 := by
  simp [z6, cw6, Finset.sum_range_succ]

lemma zJ_hasSum {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (j : ℕ) (t : ℝ) (ht : |t| < 1 / 2) :
    HasSum (fun n => zJ νp j n * t ^ n) (zJf νp j t) := by
  have hα : ‖(2 / 3 : ℝ) * t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    linarith
  have hγ : ‖νp * t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hν0]
    nlinarith [abs_nonneg t]
  exact hasSum_shift (hasSum_binCo_mulR (j - 3) hα hγ) (2 * (4 / 3 : ℝ) ^ j) (j + 1)

/-- `∑_{j ≥ 6} (10/33) Z^{(j)}(t) = Z₆(t)` (a geometric series in `j`). -/
lemma zJ_geom {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (t : ℝ) (ht : |t| < 1 / 4) :
    HasSum (fun j => cw6 j * zJf νp j t) (Z6Of νp t) := by
  have hta := le_abs_self t
  have htb := neg_abs_le t
  have hA : 0 < 1 - 2 / 3 * t := by linarith
  have hB : 0 < 1 - 2 * t := by linarith
  have hC : 0 < 1 - νp * t := by nlinarith [abs_nonneg t]
  have hρ : |4 / 3 * t / (1 - 2 / 3 * t)| < 1 := by
    rw [abs_div, abs_of_pos hA, div_lt_one hA, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    linarith
  refine (hasSum_nat_add_iff' 6).mp ?_
  have h0 : ∑ i ∈ Finset.range 6, cw6 i * zJf νp i t = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [cw6, show ¬ (6 ≤ i) by omega])
  rw [h0, sub_zero]
  have hg := (hasSum_geometric_of_abs_lt_one hρ).mul_left
    (10 / 33 * (2 * (4 / 3 : ℝ) ^ 6 * t ^ 7 * (1 / (1 - 2 / 3 * t) ^ 4 * (1 / (1 - νp * t) ^ 3))))
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hC' := hC.ne'
  have hval : 10 / 33 * (2 * (4 / 3 : ℝ) ^ 6 * t ^ 7 * (1 / (1 - 2 / 3 * t) ^ 4 * (1 / (1 - νp * t) ^ 3))) *
      (1 - 4 / 3 * t / (1 - 2 / 3 * t))⁻¹ = Z6Of νp t := by
    have h1r : 1 - 4 / 3 * t / (1 - 2 / 3 * t) = (1 - 2 * t) / (1 - 2 / 3 * t) := by
      rw [eq_div_iff hA', sub_mul, div_mul_cancel₀ _ hA', one_mul]
      ring
    rw [h1r, inv_div]
    unfold Z6Of
    generalize 1 - 2 / 3 * t = A at hA' ⊢
    generalize 1 - 2 * t = B at hB' ⊢
    generalize 1 - νp * t = C at hC' ⊢
    field_simp
    ring
  rw [← hval]
  convert hg using 1
  funext j
  simp only [cw6, zJf, if_pos (show 6 ≤ j + 6 by omega), show j + 6 - 3 + 1 = j + 4 by omega]
  rw [div_pow (4 / 3 * t) (1 - 2 / 3 * t) j, mul_pow (4 / 3 : ℝ) t j]
  generalize 1 - 2 / 3 * t = A at hA' ⊢
  generalize 1 - νp * t = C at hC' ⊢
  ring

lemma fiber_hasSum {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (j : ℕ) (t : ℝ) (ht : |t| < 1 / 2) :
    HasSum (fun n => cw6 j * (zJ νp j n * t ^ n)) (cw6 j * zJf νp j t) :=
  (zJ_hasSum hν0 hν2 j t ht).mul_left (cw6 j)

/-- `Z₆(x) = ∑ z6ₙ xⁿ` for `|x| < 1/4`: the double series over `(j, n)` converges absolutely. -/
lemma z6_hasSum {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (x : ℝ) (hx : |x| < 1 / 4) :
    HasSum (fun n => z6 νp n * x ^ n) (Z6Of νp x) := by
  have hx2 : |x| < 1 / 2 := by linarith
  have hax : |(|x|)| < 1 / 4 := by rwa [abs_abs]
  have hax2 : |(|x|)| < 1 / 2 := by rw [abs_abs]; linarith
  have hG0 : ∀ p : ℕ × ℕ, 0 ≤ cw6 p.1 * (zJ νp p.1 p.2 * |x| ^ p.2) := fun p =>
    mul_nonneg (cw6_nonneg _) (mul_nonneg (zJ_nonneg hν0 _ _) (pow_nonneg (abs_nonneg x) _))
  have hG : Summable (fun p : ℕ × ℕ => cw6 p.1 * (zJ νp p.1 p.2 * |x| ^ p.2)) := by
    refine (summable_prod_of_nonneg (fun p => hG0 p)).mpr
      ⟨fun j => (fiber_hasSum hν0 hν2 j |x| hax2).summable, ?_⟩
    exact (zJ_geom hν0 hν2 |x| hax).summable.congr
      (fun j => ((fiber_hasSum hν0 hν2 j |x| hax2).tsum_eq).symm)
  have hF : Summable (fun p : ℕ × ℕ => cw6 p.1 * (zJ νp p.1 p.2 * x ^ p.2)) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => le_of_eq ?_) hG)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg (cw6_nonneg _),
      abs_of_nonneg (zJ_nonneg hν0 _ _)]
  have htot := (zJ_geom hν0 hν2 x hx).unique
    (hF.hasSum.prod_fiberwise (fun j => fiber_hasSum hν0 hν2 j x hx2))
  have hsw := ((Equiv.prodComm ℕ ℕ).hasSum_iff).mpr hF.hasSum
  rw [htot]
  refine hsw.prod_fiberwise (fun n => ?_)
  show HasSum (fun j => cw6 j * (zJ νp j n * x ^ n)) _
  have h : HasSum (fun j => cw6 j * (zJ νp j n * x ^ n)) (∑ j ∈ Finset.range n, cw6 j * (zJ νp j n * x ^ n)) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj
      simp only [zJ, if_neg (show ¬ (j + 1 ≤ n) by omega), zero_mul, mul_zero])
  convert h using 1
  simp only [z6, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- For a finite set `S`, `∑_{j ∈ S} cw6 j Z^{(j)}_n ≤ z6ₙ`. -/
lemma zsum_le {νp : ℝ} (hν0 : 0 ≤ νp) (S : Finset ℕ) (n : ℕ) :
    ∑ j ∈ S, cw6 j * zJ νp j n ≤ z6 νp n := by
  calc ∑ j ∈ S, cw6 j * zJ νp j n = ∑ j ∈ S.filter (· < n), cw6 j * zJ νp j n := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        split_ifs with h
        · rfl
        · rw [show zJ νp j n = 0 from if_neg (show ¬ (j + 1 ≤ n) by omega), mul_zero]
    _ ≤ z6 νp n := Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
        (fun j _ _ => mul_nonneg (cw6_nonneg j) (zJ_nonneg hν0 j n))

/-! ### The coefficients of `Π_j` -/

/-- The coefficients of `Π_j` (`j ≥ 3`). -/
noncomputable def pJ (τ : ℝ) (c : ℂ) (j n : ℕ) : ℂ :=
  if j + 1 ≤ n then -2 / (vτ τ : ℂ) ^ j * cmul (binCo (j - 3) (-(βτ τ : ℂ))) (binCo 2 (nuτ τ c)) (n - (j + 1))
  else 0

lemma PiJ_hasSum {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) {j : ℕ} (hj : 3 ≤ j)
    {ξ : ℂ} (hξ : ‖ξ‖ < 1 / 2) : HasSum (fun n => pJ τ c j n * ξ ^ n) (PiJ τ c j ξ) := by
  obtain ⟨hb0, hb1⟩ := beta_bounds h1 h2
  have hnu := nu_bound h1 h2 hc
  have hα : ‖-(βτ τ : ℂ) * ξ‖ < 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
    nlinarith [norm_nonneg ξ]
  have hγ : ‖nuτ τ c * ξ‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg ξ, norm_nonneg (nuτ τ c)]
  have h := hasSum_shift (hasSum_binCo_mulC (j - 3) hα hγ) (-2 / (vτ τ : ℂ) ^ j) (j + 1)
  have hz : ((2 : ℤ) - (j : ℤ)) = -(((j - 3 + 1 : ℕ)) : ℤ) := by omega
  have e : PiJ τ c j ξ = -2 / (vτ τ : ℂ) ^ j * ξ ^ (j + 1) *
      (1 / (1 - -(βτ τ : ℂ) * ξ) ^ (j - 3 + 1) * (1 / (1 - nuτ τ c * ξ) ^ (2 + 1))) := by
    simp only [PiJ]
    rw [hz, zpow_neg, zpow_natCast, show (1 : ℂ) - -(βτ τ : ℂ) * ξ = 1 + (βτ τ : ℂ) * ξ by ring]
    generalize (1 + (βτ τ : ℂ) * ξ) ^ (j - 3 + 1) = X
    generalize 1 - nuτ τ c * ξ = Y
    generalize (vτ τ : ℂ) ^ j = V
    ring
  rw [e]
  exact h

lemma pJ_maj {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} {νp : ℝ} (hν : ‖nuτ τ c‖ ≤ νp) (j n : ℕ) :
    ‖pJ τ c j n‖ ≤ zJ νp j n := by
  obtain ⟨hb0, hb1⟩ := beta_bounds h1 h2
  have hv := vτ_ge h1 h2
  unfold pJ zJ
  split_ifs with hn
  · rw [norm_mul]
    have hβ : ‖-(βτ τ : ℂ)‖ ≤ 2 / 3 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
      exact hb1
    have hcm := (sec4_majorant_rules_proved.2.1 _ _ _ _ (binCo_maj (k := j - 3) hβ)
      (binCo_maj (k := 2) hν)).2 (n - (j + 1))
    have hC : ‖(-2 / (vτ τ : ℂ) ^ j)‖ ≤ 2 * (4 / 3 : ℝ) ^ j := by
      rw [norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < vτ τ by linarith),
        show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (pow_pos (by linarith) j), mul_assoc, ← mul_pow]
      nlinarith [one_le_pow₀ (n := j) (show (1 : ℝ) ≤ 4 / 3 * vτ τ by linarith)]
    exact mul_le_mul hC hcm (norm_nonneg _) (by positivity)
  · simp

lemma coeff_PiJ {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) {j : ℕ} (hj : 3 ≤ j)
    (n : ℕ) : coeff (PiJ τ c j) n = pJ τ c j n := by
  have hnu := nu_bound h1 h2 hc
  have h14 : ((1 / 4 : NNReal) : ℝ) = 1 / 4 := by norm_num
  refine coeff_eq_of_hasSum (r := 1 / 4) (by positivity) ?_
    (fun z hz => PiJ_hasSum h1 h2 hc hj (by rw [h14] at hz; linarith)) n
  rw [h14]
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (pJ_maj h1 h2 hnu j n) (by positivity))
    (zJ_hasSum (νp := 2) (by norm_num) le_rfl j (1 / 4) (by norm_num)).summable

/-! ### Lemma 4.5(ii) -/

lemma yτ_pos {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : 0 < yτ τ := by
  unfold yτ
  exact Real.sqrt_pos.mpr (by simp only [ysq]; nlinarith)

lemma PihatLow_pos (νp : ℝ) : 0 < PihatLowOf νp := by
  unfold PihatLowOf
  have hm : min (20 / 9) (νp ^ 2 + 4 / 3 * νp) ≤ 20 / 9 := min_le_left _ _
  have hy0' : y0 ^ 2 = 289 / 6400 := by norm_num [y0]
  apply div_pos
  · rw [hy0']
    linarith
  · positivity

lemma y0_pos : 0 < y0 := by norm_num [y0]

lemma zJ_succ_y0 {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (j : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * zJ νp j n * y0 ^ n) :=
  summable_succ_mul (zJ_nonneg hν0 j) y0_pos.le (by norm_num [y0])
    (zJ_hasSum hν0 hν2 j (1 / 4) (by norm_num)).summable

lemma z6_succ_y0 {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * z6 νp n * y0 ^ n) :=
  summable_succ_mul (z6_nonneg hν0) y0_pos.le (by norm_num [y0])
    (z6_hasSum hν0 hν2 (6 / 25) (by norm_num)).summable

lemma sum_cw6_hCoef_le {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (S : Finset ℕ) :
    ∑ j ∈ S, cw6 j * hCoef (zJ νp j) y0 ≤ hCoef (z6 νp) y0 := by
  have hS : HasSum (fun i => ∑ j ∈ S, cw6 j * hTerm (zJ νp j) y0 i) (∑ j ∈ S, cw6 j * hCoef (zJ νp j) y0) :=
    hasSum_sum (fun j _ => ((summable_hTerm (zJ_nonneg hν0 j) y0_pos (zJ_succ_y0 hν0 hν2 j)).hasSum).mul_left
      (cw6 j))
  refine hasSum_le (fun i => ?_) hS (summable_hTerm (z6_nonneg hν0) y0_pos (z6_succ_y0 hν0 hν2)).hasSum
  rw [← hTerm_sum S cw6 (zJ νp) y0 i]
  exact hTerm_mono (fun n => zsum_le hν0 S n) y0_pos.le i

lemma sum_cw6_wCoef_le {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (S : Finset ℕ) :
    ∑ j ∈ S, cw6 j * wCoef (zJ νp j) y0 ≤ wCoef (z6 νp) y0 := by
  have hS : HasSum (fun i => ∑ j ∈ S, cw6 j * wTerm (zJ νp j) y0 i) (∑ j ∈ S, cw6 j * wCoef (zJ νp j) y0) :=
    hasSum_sum (fun j _ => ((summable_wTerm (zJ_nonneg hν0 j) y0_pos (zJ_succ_y0 hν0 hν2 j)).hasSum).mul_left
      (cw6 j))
  refine hasSum_le (fun i => ?_) hS (summable_wTerm (z6_nonneg hν0) y0_pos (z6_succ_y0 hν0 hν2)).hasSum
  rw [← wTerm_sum S cw6 (zJ νp) y0 i]
  exact wTerm_mono (fun n => zsum_le hν0 S n) y0_pos.le i

lemma N6_eq {νp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) :
    N6Of νp = (wCoef (z6 νp) y0 + TPlusOf νp * hCoef (z6 νp) y0) / PihatLowOf νp := by
  obtain ⟨hlink, -, -⟩ := sec4_hw_coeff_proved (z6 νp) (z6_nonneg hν0) (z6_one νp) (z6_two νp) (Z6Of νp)
    (1 / 4) (by norm_num) (fun x hx => z6_hasSum hν0 hν2 x hx)
  obtain ⟨hH, hW⟩ := hlink y0 y0_pos (by norm_num [y0])
  rw [← hH, ← hW]
  rfl

/-- `|T_j| ≤ (𝔴[Z^{(j)}](y₀) + T⁺ 𝔥[Z^{(j)}](y₀)) / Π̂₋` for `j ≥ 6`. -/
lemma TJ_bound {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (hy0 : yτ τ ≤ y0) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {νp : ℝ} (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) {j : ℕ} (hj : 6 ≤ j) :
    ‖TJ τ c j‖ ≤ (wCoef (zJ νp j) y0 + TPlusOf νp * hCoef (zJ νp j) y0) / PihatLowOf νp := by
  have hν0 : 0 ≤ νp := (norm_nonneg _).trans hν
  have hy := yτ_pos h1 h2
  obtain ⟨hTp, hPl⟩ := lem_4_4_iv_proved τ h1 h2.le hy hy0 c hc νp hν hνp
  have hT0 : 0 ≤ TPlusOf νp := (norm_nonneg _).trans hTp
  have hcoef : ∀ n, coeff (PiJ τ c j) n = pJ τ c j n := coeff_PiJ h1 h2 hc (by omega)
  have hmaj : Majorizes (coeff (PiJ τ c j)) (zJ νp j) := fun n => by
    rw [hcoef]
    exact pJ_maj h1 h2 hν j n
  have hdp : ∀ n, n ≤ 2 → coeff (PiJ τ c j) n = 0 := fun n hn => by
    rw [hcoef]
    simp only [pJ]
    rw [if_neg (show ¬ (j + 1 ≤ n) by omega)]
  have hZ0 := zJ_nonneg hν0 j
  have hs4 := (zJ_hasSum hν0 hνp j (1 / 4) (by norm_num)).summable
  have hy1 : yτ τ < 1 / 4 := lt_of_le_of_lt hy0 (by norm_num [y0])
  have hZs := summable_succ_mul hZ0 hy.le hy1 hs4
  have hZs0 := zJ_succ_y0 hν0 hνp j
  obtain ⟨hP, hU⟩ := lem_4_4_i_proved τ h1 h2.le (yτ τ) hy hy0 c hc _ _ hdp hmaj hZs
  have hHm : hCoef (zJ νp j) (yτ τ) ≤ hCoef (zJ νp j) y0 :=
    hasSum_le (fun i => hTerm_mono_x hZ0 hy.le hy0 i) (summable_hTerm hZ0 hy hZs).hasSum
      (summable_hTerm hZ0 y0_pos hZs0).hasSum
  have hWm : wCoef (zJ νp j) (yτ τ) ≤ wCoef (zJ νp j) y0 :=
    hasSum_le (fun i => wTerm_mono_x hZ0 hy.le hy0 i) (summable_wTerm hZ0 hy hZs).hasSum
      (summable_wTerm hZ0 y0_pos hZs0).hasSum
  have hcl := sec4_Tj_closed_proved τ h1 h2 c hc j (by omega)
  have hxi : xiτ τ = I * ((yτ τ : ℝ) : ℂ) := rfl
  rw [hxi] at hcl
  rw [← hcl, norm_div]
  have hnum : ‖UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiJ τ c j)) (I * ((yτ τ : ℝ) : ℂ)) -
      That τ c * PiOddSer (coeff (PiJ τ c j)) (I * ((yτ τ : ℝ) : ℂ))‖ ≤
      wCoef (zJ νp j) y0 + TPlusOf νp * hCoef (zJ νp j) y0 := by
    calc _ ≤ ‖UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiJ τ c j)) (I * ((yτ τ : ℝ) : ℂ))‖ +
          ‖That τ c‖ * ‖PiOddSer (coeff (PiJ τ c j)) (I * ((yτ τ : ℝ) : ℂ))‖ := by
          rw [← norm_mul]
          exact norm_sub_le _ _
      _ ≤ _ := add_le_add (hU.trans hWm) (mul_le_mul hTp (hP.trans hHm) (norm_nonneg _) hT0)
  exact div_le_div₀ ((norm_nonneg _).trans hnum) hnum (PihatLow_pos νp) hPl

/-- The terms `|T_j|/√(2j-1)` for `j ≥ 6`. -/
noncomputable def tailT (τ : ℝ) (c : ℂ) (j : ℕ) : ℝ := if 6 ≤ j then ‖TJ τ c j‖ / Real.sqrt (2 * (j : ℝ) - 1) else 0

lemma tailT_nonneg (τ : ℝ) (c : ℂ) (j : ℕ) : 0 ≤ tailT τ c j := by
  unfold tailT
  split_ifs
  · exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  · exact le_rfl

lemma tailT_le {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (hy0 : yτ τ ≤ y0) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {νp : ℝ} (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) (j : ℕ) :
    tailT τ c j ≤ cw6 j * ((wCoef (zJ νp j) y0 + TPlusOf νp * hCoef (zJ νp j) y0) / PihatLowOf νp) := by
  unfold tailT cw6
  split_ifs with hj
  · have hb := TJ_bound h1 h2 hy0 hc hν hνp hj
    have hj6 : (6 : ℝ) ≤ j := by exact_mod_cast hj
    have hsq : 33 / 10 ≤ Real.sqrt (2 * (j : ℝ) - 1) := by
      have h := Real.sqrt_le_sqrt (show (33 / 10 : ℝ) ^ 2 ≤ 2 * (j : ℝ) - 1 by nlinarith)
      rwa [Real.sqrt_sq (show (0 : ℝ) ≤ 33 / 10 by norm_num)] at h
    calc ‖TJ τ c j‖ / Real.sqrt (2 * (j : ℝ) - 1) ≤ ‖TJ τ c j‖ / (33 / 10) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hsq
      _ = 10 / 33 * ‖TJ τ c j‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)
  · simp

lemma tailT_sq (τ : ℝ) (c : ℂ) (j : ℕ) :
    (if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) = tailT τ c j ^ 2 := by
  unfold tailT
  split_ifs with hj
  · have hj6 : (6 : ℝ) ≤ j := by exact_mod_cast hj
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (j : ℝ) - 1 by linarith)]
  · simp

theorem lem_4_5_ii_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (hy0 : yτ τ ≤ y0) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) :
    Summable (fun j : ℕ => if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) ∧
      Real.sqrt (∑' j : ℕ, if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) ≤ N6Of νp := by
  have hν0 : 0 ≤ νp := (norm_nonneg _).trans hν
  have hy := yτ_pos h1 h2
  obtain ⟨hTp, -⟩ := lem_4_4_iv_proved τ h1 h2.le hy hy0 c hc νp hν hνp
  have hT0 : 0 ≤ TPlusOf νp := (norm_nonneg _).trans hTp
  have hPL := PihatLow_pos νp
  have ha0 : ∀ j, 0 ≤ tailT τ c j := tailT_nonneg τ c
  have hpart : ∀ S : Finset ℕ, ∑ j ∈ S, tailT τ c j ≤ N6Of νp := by
    intro S
    calc ∑ j ∈ S, tailT τ c j ≤
          ∑ j ∈ S, cw6 j * ((wCoef (zJ νp j) y0 + TPlusOf νp * hCoef (zJ νp j) y0) / PihatLowOf νp) :=
          Finset.sum_le_sum (fun j _ => tailT_le h1 h2 hy0 hc hν hνp j)
      _ = (∑ j ∈ S, cw6 j * wCoef (zJ νp j) y0 + TPlusOf νp * ∑ j ∈ S, cw6 j * hCoef (zJ νp j) y0) /
            PihatLowOf νp := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ (wCoef (z6 νp) y0 + TPlusOf νp * hCoef (z6 νp) y0) / PihatLowOf νp :=
          (div_le_div_iff_of_pos_right hPL).mpr (add_le_add (sum_cw6_wCoef_le hν0 hνp S)
            (mul_le_mul_of_nonneg_left (sum_cw6_hCoef_le hν0 hνp S) hT0))
      _ = N6Of νp := (N6_eq hν0 hνp).symm
  have hsum : Summable (tailT τ c) := summable_of_sum_le (fun j => ha0 j) hpart
  have hA : ∑' j, tailT τ c j ≤ N6Of νp := Real.tsum_le_of_sum_le (fun j => ha0 j) hpart
  have hA0 : 0 ≤ ∑' j, tailT τ c j := tsum_nonneg ha0
  have hle : ∀ j, tailT τ c j ^ 2 ≤ (∑' i, tailT τ c i) * tailT τ c j := fun j => by
    have := hsum.le_tsum j (fun i _ => ha0 i)
    nlinarith [ha0 j]
  have hs2 : Summable (fun j => tailT τ c j ^ 2) :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) hle (hsum.mul_left _)
  have hfun : (fun j : ℕ => if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) =
      fun j => tailT τ c j ^ 2 := funext (tailT_sq τ c)
  rw [hfun]
  refine ⟨hs2, ?_⟩
  have hT2 : ∑' j, tailT τ c j ^ 2 ≤ (∑' j, tailT τ c j) ^ 2 := by
    rw [pow_two]
    exact hasSum_le hle hs2.hasSum (hsum.hasSum.mul_left (∑' i, tailT τ c i))
  calc Real.sqrt (∑' j, tailT τ c j ^ 2) ≤ Real.sqrt ((∑' j, tailT τ c j) ^ 2) := Real.sqrt_le_sqrt hT2
    _ = ∑' j, tailT τ c j := Real.sqrt_sq hA0
    _ ≤ N6Of νp := hA

end Robinson.Proofs
