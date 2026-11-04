/-
Robinson/Proofs/Lem44ii.lean — proofs of lem_4_4_ii.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Proofs.NearP_A

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The numbers `v`, `β`, `v + τξ` for `9/20 ≤ τ ≤ 1/2` (the endpoint `τ = 1/2` included) -/

private lemma l44_v_ge {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 3 / 4 ≤ vτ τ := by
  simp only [vτ]; nlinarith

private lemma l44_v_pos {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 0 < vτ τ := by
  have := l44_v_ge h1 h2; linarith

private lemma l44_v_ne {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : (vτ τ : ℂ) ≠ 0 := by
  have := l44_v_pos h1 h2
  exact_mod_cast this.ne'

private lemma l44_beta {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 0 < βτ τ ∧ βτ τ ≤ 2 / 3 := by
  have hv := l44_v_ge h1 h2
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  rw [βτ, div_le_iff₀ (by linarith)]
  linarith

private lemma l44_neg_tau_mem {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : -(τ : ℂ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

private lemma l44_norm_v_add_ge {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) : 5 / 8 ≤ ‖(vτ τ : ℂ) + (τ : ℂ) * ξ‖ := by
  have hv := l44_v_ge h1 h2
  rw [mem_ball_zero_iff] at hξ
  have hnv : ‖(vτ τ : ℂ)‖ = vτ τ := by rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnt : ‖(τ : ℂ) * ξ‖ = τ * ‖ξ‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have htri := norm_sub_norm_le (vτ τ : ℂ) (-((τ : ℂ) * ξ))
  rw [norm_neg, sub_neg_eq_add, hnv, hnt] at htri
  nlinarith [norm_nonneg ξ]

private lemma l44_v_add_ne {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) : (vτ τ : ℂ) + (τ : ℂ) * ξ ≠ 0 := by
  intro h0
  have := l44_norm_v_add_ge h1 h2 hξ
  rw [h0, norm_zero] at this
  linarith

private lemma l44_w_mem_ball {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) : wmap τ ξ ∈ ball (0 : ℂ) 1 := by
  have hn := l44_norm_v_add_ge h1 h2 hξ
  have hξ' := mem_ball_zero_iff.mp hξ
  rw [wmap, mem_ball_zero_iff, norm_div, div_lt_one (by linarith)]
  linarith

/-- The automorphism identity `(u - τ)/(1 - τu) = -τ + ξ` at `u = ξ/(v + τξ)`. -/
private lemma l44_mobius {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) - (τ : ℂ)) / (1 - (τ : ℂ) * (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) =
      -(τ : ℂ) + ξ := by
  have hden := l44_v_add_ne h1 h2 hξ
  have hV0 := l44_v_ne h1 h2
  have hV : (vτ τ : ℂ) = 1 - (τ : ℂ) ^ 2 := by simp [vτ]
  have e1 : ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) - (τ : ℂ) =
      (vτ τ : ℂ) * (ξ - τ) / ((vτ τ : ℂ) + (τ : ℂ) * ξ) := by
    rw [eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden, hV]
    ring
  have e2 : 1 - (τ : ℂ) * (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ)) = (vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * ξ) := by
    rw [eq_div_iff hden, sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hden]
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hden, mul_div_cancel_left₀ _ hV0]
  ring

/-- `Π(ξ) = v f_{-τ}(ξ/(v + τξ))` on `|ξ| < 1/4`. -/
private lemma l44_PiF_eq_fT {f : ℂ → ℂ} {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    PiF f τ ξ = (vτ τ : ℂ) * fT f τ (wmap τ ξ) := by
  have hV0 := l44_v_ne h1 h2
  have harg : (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) + -(τ : ℂ)) /
      (1 + (starRingEnd ℂ) (-(τ : ℂ)) * (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) = -(τ : ℂ) + ξ := by
    rw [map_neg, Complex.conj_ofReal, ← sub_eq_add_neg, neg_mul, ← sub_eq_add_neg]
    exact l44_mobius h1 h2 hξ
  have hnorm : ((1 - ‖-(τ : ℂ)‖ ^ 2 : ℝ) : ℂ) = (vτ τ : ℂ) := by
    rw [norm_neg, norm_real, Real.norm_eq_abs, sq_abs]
    rfl
  simp only [PiF, fT, koebeTransform, wmap]
  rw [harg, hnorm, ← mul_div_assoc, mul_div_mul_left _ _ hV0]

private lemma l44_fT_mem_S {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) :
    InS (fT f τ) :=
  sec3_koebe_transform_mem_S_proved f hf _ (l44_neg_tau_mem h1 h2)

/-- `π₁ = 1`. -/
private lemma l44_PiF_coeff_one {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) :
    coeff (PiF f τ) 1 = 1 := by
  have hτ := l44_neg_tau_mem h1 h2
  have hb : -(τ : ℂ) + 0 ∈ ball (0 : ℂ) 1 := by rw [add_zero]; exact hτ
  rw [coeff_one_eq, (hasDerivAt_PiF hf hb).deriv, add_zero]
  exact div_self (sec3_deriv_ne_zero_proved f hf _ hτ)

/-- For `g ∈ 𝒮`: `|a_l| ≤ l` for every `l` (`a₀ = 0`, `a₁ = 1`, de Branges for `l ≥ 2`). -/
private lemma l44_coeff_bound (hDB : FactDeBranges) {g : ℂ → ℂ} (hg : InS g) (l : ℕ) :
    ‖coeff g l‖ ≤ l := by
  rcases Nat.lt_or_ge l 2 with hl | hl
  · interval_cases l
    · rw [coeff_zero_eq, hg.map_zero]; simp
    · rw [coeff_one_eq, hg.deriv_zero]; simp
  · exact hDB g hg l hl

/-! ### The double series

`v w^l = v (ξ/v)^l (1 + βξ)^{-l} = v (ξ/v)^l ∑_k C(k+l-1, l-1) (-βξ)^k`; summing over `l` with the weights
`a_l` and collecting the terms of total degree `n = l + k` gives the Taylor coefficients of `Π`. -/

/-- The binomial weight `C(k + l - 1, l - 1)` of `x^k` in `(1 - x)^{-l}` (`l ≥ 1`). -/
private def bw (l k : ℕ) : ℕ := (k + (l - 1)).choose (l - 1)

/-- `∑_k A X^l C(k+l-1, l-1) r^k = A (X/(1 - r))^l`, where `A = 0` if `l = 0`. -/
private lemma l44_inner_hasSum {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (A X r : 𝕜) (hr : ‖r‖ < 1)
    (l : ℕ) (hA : l = 0 → A = 0) :
    HasSum (fun k : ℕ => A * X ^ l * ((bw l k : ℕ) : 𝕜) * r ^ k) (A * (X / (1 - r)) ^ l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp [hA rfl]
  · have h := (hasSum_choose_mul_geometric_of_norm_lt_one (l - 1) hr).mul_left (A * X ^ l)
    rw [Nat.sub_add_cancel hl] at h
    convert h using 1
    · funext k; simp only [bw]; ring
    · rw [div_pow]; ring

/-- An absolutely summable double series, summed first along the rows, regrouped by total degree. -/
private lemma l44_regroup {F : ℕ × ℕ → ℂ} {G : ℕ → ℂ} {S : ℂ} (hF : Summable F)
    (hin : ∀ l, HasSum (fun k => F (l, k)) (G l)) (hout : HasSum G S) :
    HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p) S := by
  have hS : ∑' p, F p = S := (hF.hasSum.prod_fiberwise hin).unique hout
  have h1 : HasSum F S := hS ▸ hF.hasSum
  have h2 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr h1
  refine h2.sigma fun n => ?_
  have h3 := hasSum_fintype (fun c : Finset.HasAntidiagonal.antidiagonal n => F c)
  rw [Finset.sum_coe_sort] at h3
  exact h3

/-- The coefficient `π_n = ∑_{l+k=n} a_l v (1/v)^l C(k+l-1, l-1) (-β)^k`, `a_l` the coefficients of `g`. -/
private noncomputable def cPi (g : ℂ → ℂ) (τ : ℝ) (n : ℕ) : ℂ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
    coeff g p.1 * (vτ τ : ℂ) * (1 / (vτ τ : ℂ)) ^ p.1 * ((bw p.1 p.2 : ℕ) : ℂ) * (-(βτ τ : ℂ)) ^ p.2

/-- `Π(ξ) = ∑ π_n ξ^n` on `|ξ| < 1/4`. -/
private lemma l44_PiF_hasSum (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    HasSum (fun n => cPi (fT f τ) τ n * ξ ^ n) (PiF f τ ξ) := by
  set g := fT f τ with hg_def
  have hg : InS g := l44_fT_mem_S hf h1 h2
  have hv := l44_v_ge h1 h2
  have hv0 : 0 < vτ τ := by linarith
  have hV : (vτ τ : ℂ) ≠ 0 := l44_v_ne h1 h2
  obtain ⟨hβ0, hβ1⟩ := l44_beta h1 h2
  have hξn : ‖ξ‖ < 1 / 4 := mem_ball_zero_iff.mp hξ
  have hbx : βτ τ * ‖ξ‖ ≤ 1 / 6 := by nlinarith [norm_nonneg ξ]
  have hr : ‖-((βτ τ : ℂ) * ξ)‖ < 1 := by
    rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hβ0]; linarith
  set F : ℕ × ℕ → ℂ := fun p => coeff g p.1 * (vτ τ : ℂ) * (ξ / (vτ τ : ℂ)) ^ p.1 *
    ((bw p.1 p.2 : ℕ) : ℂ) * (-((βτ τ : ℂ) * ξ)) ^ p.2 with hF
  -- the rows
  have hden := l44_v_add_ne h1 h2 hξ
  have hwe : ξ / (vτ τ : ℂ) / (1 - -((βτ τ : ℂ) * ξ)) = wmap τ ξ := by
    have h1b : (1 : ℂ) - -((βτ τ : ℂ) * ξ) = ((vτ τ : ℂ) + (τ : ℂ) * ξ) / (vτ τ : ℂ) := by
      simp only [βτ]; push_cast; field_simp; ring
    rw [h1b, wmap, div_div_div_cancel_right₀ hV]
  have hin : ∀ l, HasSum (fun k => F (l, k)) (coeff g l * (vτ τ : ℂ) * (wmap τ ξ) ^ l) := by
    intro l
    rw [← hwe]
    have hA : l = 0 → coeff g l * (vτ τ : ℂ) = 0 := fun hl => by
      subst hl; rw [coeff_zero_eq, hg.map_zero, zero_mul]
    have h := l44_inner_hasSum (𝕜 := ℂ) (coeff g l * (vτ τ : ℂ)) (ξ / (vτ τ : ℂ)) (-((βτ τ : ℂ) * ξ)) hr l hA
    simp only [hF]
    exact h
  -- the sum of the rows
  have hw : wmap τ ξ ∈ ball (0 : ℂ) 1 := l44_w_mem_ball h1 h2 hξ
  have hout : HasSum (fun l => coeff g l * (vτ τ : ℂ) * (wmap τ ξ) ^ l) (PiF f τ ξ) := by
    rw [l44_PiF_eq_fT h1 h2 hξ]
    have := (hasSum_coeff hg.differentiableOn hw).mul_left (vτ τ : ℂ)
    convert this using 1
    funext l; ring
  -- absolute summability
  set B : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) * vτ τ * (‖ξ‖ / vτ τ) ^ p.1 * ((bw p.1 p.2 : ℕ) : ℝ) *
    (βτ τ * ‖ξ‖) ^ p.2 with hB
  have hB0 : 0 ≤ B := fun p => by simp only [hB, Pi.zero_apply]; positivity
  have hFB : ∀ p, ‖F p‖ ≤ B p := by
    intro p
    have hnorm : ‖F p‖ = ‖coeff g p.1‖ * vτ τ * (‖ξ‖ / vτ τ) ^ p.1 * ((bw p.1 p.2 : ℕ) : ℝ) *
        (βτ τ * ‖ξ‖) ^ p.2 := by
      simp only [hF, norm_mul, norm_pow, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hv0, abs_of_pos hβ0, Complex.norm_natCast]
    rw [hnorm]
    have := l44_coeff_bound hDB hg p.1
    simp only [hB]
    gcongr
  have hrr : ‖βτ τ * ‖ξ‖‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]; linarith
  have hinB : ∀ l, HasSum (fun k => B (l, k)) ((l : ℝ) * vτ τ * (‖ξ‖ / vτ τ / (1 - βτ τ * ‖ξ‖)) ^ l) :=
    fun l => l44_inner_hasSum ((l : ℝ) * vτ τ) (‖ξ‖ / vτ τ) _ hrr l (fun hl => by subst hl; simp)
  have hρ : ‖‖ξ‖ / vτ τ / (1 - βτ τ * ‖ξ‖)‖ < 1 := by
    have hpos : 0 < 1 - βτ τ * ‖ξ‖ := by linarith
    rw [Real.norm_of_nonneg (by positivity), div_lt_one hpos, div_lt_iff₀ hv0]
    nlinarith [norm_nonneg ξ]
  have hBs : Summable B := by
    refine (summable_prod_of_nonneg hB0).mpr ⟨fun l => (hinB l).summable, ?_⟩
    have hfun : (fun l => ∑' k, B (l, k)) =
        fun l : ℕ => vτ τ * ((l : ℝ) ^ 1 * (‖ξ‖ / vτ τ / (1 - βτ τ * ‖ξ‖)) ^ l) := by
      funext l; rw [(hinB l).tsum_eq]; ring
    rw [hfun]
    exact (summable_pow_mul_geometric_of_norm_lt_one 1 hρ).mul_left _
  have hsum : Summable F := Summable.of_norm_bounded hBs hFB
  -- regroup by total degree
  have hreg := l44_regroup hsum hin hout
  convert hreg using 1
  funext n
  rw [cPi, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp]
  simp only [hF]
  ring

/-- `Π` has the power series `∑ π_n ξ^n` at `0`. -/
private lemma l44_series (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) :
    HasFPowerSeriesOnBall (PiF f τ) (FormalMultilinearSeries.ofScalars ℂ (cPi (fT f τ) τ)) 0
      ((1 / 8 : NNReal) : ENNReal) := by
  have h18 : ((1 / 8 : NNReal) : ℝ) = 1 / 8 := by norm_num
  refine ⟨?_, ENNReal.coe_pos.mpr (by norm_num), ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    have hx : ((1 / 8 : ℝ) : ℂ) ∈ ball (0 : ℂ) (1 / 4) := by
      rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs]; norm_num
    have hs := (l44_PiF_hasSum hDB hf h1 h2 hx).summable.tendsto_atTop_zero.norm
    rw [norm_zero] at hs
    refine hs.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, h18, norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  · intro z hz
    rw [Metric.eball_coe, mem_ball_zero_iff, h18] at hz
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
    exact l44_PiF_hasSum hDB hf h1 h2 (mem_ball_zero_iff.mpr (by linarith))

/-- The Taylor coefficients of `Π` are the `π_n` of the double series. -/
private lemma l44_coeff_eq (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) (n : ℕ) : coeff (PiF f τ) n = cPi (fT f τ) τ n := by
  have hp := (l44_series hDB hf h1 h2).hasFPowerSeriesAt
  have hq := hp.analyticAt.hasFPowerSeriesAt
  have heq := hq.eq_formalMultilinearSeries hp
  have h2' := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ heq
  unfold coeff
  exact congrFun h2' n

/-! ### The bound `|π_n| ≤ (2/3)(n + 1/2) 2^{n-1}`

Termwise, `|a_l| v^{1-l} β^k ≤ l (4/3)^{l-1} (2/3)^k` (`v ≥ 3/4`, `β ≤ 2/3`): the value at `τ = 1/2`. -/

/-- The majorant coefficient `∑_{l+k=n} l (3/4)(4/3)^l C(k+l-1, l-1) (2/3)^k`. -/
private noncomputable def gam (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (p.1 : ℝ) * (3 / 4) * (4 / 3) ^ p.1 * ((bw p.1 p.2 : ℕ) : ℝ) * (2 / 3) ^ p.2

private lemma l44_term_le (hDB : FactDeBranges) {g : ℂ → ℂ} (hg : InS g) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) (l k : ℕ) :
    ‖coeff g l * (vτ τ : ℂ) * (1 / (vτ τ : ℂ)) ^ l * ((bw l k : ℕ) : ℂ) * (-(βτ τ : ℂ)) ^ k‖ ≤
      (l : ℝ) * (3 / 4) * (4 / 3) ^ l * ((bw l k : ℕ) : ℝ) * (2 / 3) ^ k := by
  have hv := l44_v_ge h1 h2
  have hv0 : 0 < vτ τ := by linarith
  obtain ⟨hβ0, hβ1⟩ := l44_beta h1 h2
  have hnorm : ‖coeff g l * (vτ τ : ℂ) * (1 / (vτ τ : ℂ)) ^ l * ((bw l k : ℕ) : ℂ) * (-(βτ τ : ℂ)) ^ k‖ =
      ‖coeff g l‖ * (vτ τ * (1 / vτ τ) ^ l) * ((bw l k : ℕ) : ℝ) * βτ τ ^ k := by
    simp only [norm_mul, norm_pow, norm_div, norm_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hv0, abs_of_pos hβ0, Complex.norm_natCast]
    ring
  rw [hnorm]
  rcases l with _ | j
  · have h0 : ‖coeff g 0‖ = 0 := by rw [coeff_zero_eq, hg.map_zero, norm_zero]
    rw [h0]; simp
  · have hc := l44_coeff_bound hDB hg (j + 1)
    have hvj : vτ τ * (1 / vτ τ) ^ (j + 1) ≤ 3 / 4 * (4 / 3) ^ (j + 1) := by
      have e1 : vτ τ * (1 / vτ τ) ^ (j + 1) = (1 / vτ τ) ^ j := by
        rw [pow_succ, mul_comm, mul_assoc, one_div_mul_cancel hv0.ne', mul_one]
      have h43 : 1 / vτ τ ≤ 4 / 3 := by rw [div_le_iff₀ hv0]; linarith
      rw [e1]
      calc (1 / vτ τ) ^ j ≤ (4 / 3) ^ j := pow_le_pow_left₀ (by positivity) h43 j
        _ = 3 / 4 * (4 / 3) ^ (j + 1) := by ring
    have hβk : βτ τ ^ k ≤ (2 / 3) ^ k := pow_le_pow_left₀ hβ0.le hβ1 k
    calc ‖coeff g (j + 1)‖ * (vτ τ * (1 / vτ τ) ^ (j + 1)) * ((bw (j + 1) k : ℕ) : ℝ) * βτ τ ^ k
        ≤ ((j + 1 : ℕ) : ℝ) * (3 / 4 * (4 / 3) ^ (j + 1)) * ((bw (j + 1) k : ℕ) : ℝ) * (2 / 3) ^ k := by
          gcongr
      _ = _ := by ring

private lemma l44_cPi_le (hDB : FactDeBranges) {g : ℂ → ℂ} (hg : InS g) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) (n : ℕ) : ‖cPi g τ n‖ ≤ gam n :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => l44_term_le hDB hg h1 h2 p.1 p.2)

/-- The binomial theorem over the antidiagonal. -/
private lemma l44_binom (n : ℕ) (x y : ℝ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose p.1 : ℝ) * x ^ p.1 * y ^ p.2 = (x + y) ^ n := by
  rw [(Commute.all x y).add_pow']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [nsmul_eq_mul]; ring

/-- `∑_{l+k=N+1} l C(N+1, l) x^l y^k = (N+1) x (x+y)^N`. -/
private lemma l44_binom_d (N : ℕ) (x y : ℝ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (N + 1), (p.1 : ℝ) * ((N + 1).choose p.1 : ℝ) * x ^ p.1 * y ^ p.2 =
      ((N : ℝ) + 1) * x * (x + y) ^ N := by
  rw [Finset.Nat.sum_antidiagonal_succ, ← l44_binom N x y, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hc : ((N + 1).choose (p.1 + 1) : ℝ) * ((p.1 : ℝ) + 1) = ((N : ℝ) + 1) * (N.choose p.1 : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq N p.1).symm
  push_cast
  linear_combination (x ^ (p.1 + 1) * y ^ p.2) * hc

/-- `γ_{n+1} = 2^n (1 + 2n/3)`. -/
private lemma l44_gam_succ (n : ℕ) : gam (n + 1) = 2 ^ n * (1 + 2 / 3 * (n : ℝ)) := by
  have hsum : gam (n + 1) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((p.1 : ℝ) + 1) * (n.choose p.1 : ℝ) * (4 / 3) ^ p.1 * (2 / 3) ^ p.2 := by
    rw [gam, Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hb : bw (p.1 + 1) p.2 = n.choose p.1 := by
      simp only [bw, Nat.add_sub_cancel]
      rw [add_comm, hp]
    rw [hb]; push_cast; ring
  rw [hsum]
  rcases n with _ | N
  · simp
  · have hsplit : ∀ p : ℕ × ℕ, ((p.1 : ℝ) + 1) * ((N + 1).choose p.1 : ℝ) * (4 / 3) ^ p.1 * (2 / 3) ^ p.2 =
        (p.1 : ℝ) * ((N + 1).choose p.1 : ℝ) * (4 / 3) ^ p.1 * (2 / 3) ^ p.2 +
          ((N + 1).choose p.1 : ℝ) * (4 / 3) ^ p.1 * (2 / 3) ^ p.2 := fun p => by ring
    simp only [hsplit, Finset.sum_add_distrib, l44_binom_d, l44_binom]
    norm_num
    ring

/-- `γ_{2m+1} = 4^m (1 + 4m/3)`. -/
private lemma l44_gam_odd (m : ℕ) : gam (2 * m + 1) = 4 ^ m * (1 + 4 / 3 * (m : ℝ)) := by
  rw [l44_gam_succ, pow_mul]
  push_cast
  ring

/-! ### Row: lem_4_4_ii -/

/-- Lemma 4.4(ii) (sec_04_near.tex:175): for every `f ∈ 𝒮`, `|Π_o(iy) - 1| ≤ ε(y)`. -/
theorem lem_4_4_ii_proved (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) (y : ℝ) (hy : 0 < y) (hy0 : y ≤ y0) :
    ‖PiOddSer (coeff (PiF f τ)) (I * (y : ℂ)) - 1‖ ≤ epsOf y := by
  set q : ℝ := 4 * y ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by simp only [y0] at hy0; nlinarith
  set d : ℕ → ℂ := fun m => coeff (PiF f τ) (2 * m + 1) * (I * (y : ℂ)) ^ (2 * m) with hd
  set e : ℕ → ℝ := fun m => (1 + 4 / 3 * (m : ℝ)) * q ^ m with he
  have hde : ∀ m, ‖d m‖ ≤ e m := by
    intro m
    simp only [hd, he]
    rw [norm_mul, norm_pow, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs, abs_of_pos hy,
      l44_coeff_eq hDB hf h1 h2]
    have hb := (l44_cPi_le hDB (l44_fT_mem_S hf h1 h2) h1 h2 (2 * m + 1)).trans_eq (l44_gam_odd m)
    calc ‖cPi (fT f τ) τ (2 * m + 1)‖ * y ^ (2 * m) ≤ 4 ^ m * (1 + 4 / 3 * (m : ℝ)) * y ^ (2 * m) := by
          gcongr
      _ = (1 + 4 / 3 * (m : ℝ)) * q ^ m := by rw [hq, mul_pow, pow_mul]; ring
  have heS : HasSum e (1 / (1 - q) + 4 / 3 * (q / (1 - q) ^ 2)) := by
    have hg1 := hasSum_geometric_of_lt_one hq0 hq1
    have hg2 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := q)
      (by rw [Real.norm_of_nonneg hq0]; exact hq1)
    convert hg1.add (hg2.mul_left (4 / 3)) using 1
    · funext m; simp only [he]; ring
    · rw [one_div]
  have hdS : Summable d := Summable.of_norm_bounded heS.summable hde
  have hd0 : d 0 = 1 := by
    simp only [hd, mul_zero, zero_add, pow_zero, mul_one]
    exact l44_PiF_coeff_one hf h1 h2
  have hd1 : HasSum (fun m => d (m + 1)) (PiOddSer (coeff (PiF f τ)) (I * (y : ℂ)) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hdS.hasSum
    rw [Finset.sum_range_one, hd0] at h
    exact h
  have he1 : HasSum (fun m => e (m + 1)) (1 / (1 - q) + 4 / 3 * (q / (1 - q) ^ 2) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr heS
    rw [Finset.sum_range_one] at h
    convert h using 2
    simp only [he]; simp
  calc _ ≤ 1 / (1 - q) + 4 / 3 * (q / (1 - q) ^ 2) - 1 := hd1.norm_le_of_bounded he1 fun m => hde (m + 1)
    _ = epsOf y := by
      have hne : 1 - q ≠ 0 := by linarith
      have hne' : 1 - 4 * y ^ 2 ≠ 0 := by rw [← hq]; exact hne
      simp only [epsOf]
      rw [hq]
      field_simp
      ring

end Robinson.Proofs
