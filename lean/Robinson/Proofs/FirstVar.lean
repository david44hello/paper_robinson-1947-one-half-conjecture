/-
Robinson/Proofs/FirstVar.lean — proofs of sec4_first_variation.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Proofs.NearP_B

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The function `B` on `|ξ| < 1/4`

From `L = 1 - νξ + B = (1 + βξ) φ(u(ξ))`, `u(ξ) = ξ/(v + τξ)`: `B(ξ) = (1 + βξ) φ(u(ξ)) - 1 + νξ`. So `B` is
holomorphic on `|ξ| < 1/4`, `B(0) = 0`, `B'(0) = β - c/v + ν = 0`, and `B` is bounded there (`|u| ≤ 2/5`). -/

private lemma fv_Bser_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    Bser τ φ w = (1 + (βτ τ : ℂ) * w) * φ (wmap τ w) - 1 + nuτ τ (cOf f τ) * w := by
  have h := Lfun_eq hf h1 h2 hφ hw
  simp only [Lfun] at h
  linear_combination h

private lemma fv_b0 {g φ : ℂ → ℂ} (hφ : IsSqrtQuot g φ) : coeff φ 0 = 1 := by
  rw [coeff_zero_eq, hφ.2.1]

private lemma fv_b1 {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) : coeff φ 1 = -cOf f τ :=
  sqrtQuot_coeff_one (fT_mem_S hf h1 h2) hφ

private lemma fv_hasDerivAt_Bf {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) 1)) (ν : ℂ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    HasDerivAt (fun x => (1 + (βτ τ : ℂ) * x) * φ (wmap τ x) - 1 + ν * x)
      ((βτ τ : ℂ) * φ (wmap τ w) +
        (1 + (βτ τ : ℂ) * w) * (deriv φ (wmap τ w) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) + ν) w := by
  have hsb : wmap τ w ∈ ball (0 : ℂ) 1 := w_mem_ball h1 h2 hw
  have hφa : HasDerivAt φ (deriv φ (wmap τ w)) (wmap τ w) :=
    (hφd.differentiableAt (isOpen_ball.mem_nhds hsb)).hasDerivAt
  have hc : HasDerivAt (fun x => φ (wmap τ x))
      (deriv φ (wmap τ w) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) w :=
    hφa.comp w (hasDerivAt_wmap h1 h2 hw)
  have hl : HasDerivAt (fun x : ℂ => 1 + (βτ τ : ℂ) * x) (βτ τ : ℂ) w :=
    (((hasDerivAt_id' w).const_mul (βτ τ : ℂ)).const_add 1).congr_deriv (by ring)
  exact (((hl.mul hc).sub_const 1).add ((hasDerivAt_id' w).const_mul ν)).congr_deriv (by ring)

private lemma fv_hasDerivAt_Bser {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    HasDerivAt (Bser τ φ) ((βτ τ : ℂ) * φ (wmap τ w) +
        (1 + (βτ τ : ℂ) * w) * (deriv φ (wmap τ w) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) +
          nuτ τ (cOf f τ)) w := by
  have hev : Bser τ φ =ᶠ[𝓝 w] fun x => (1 + (βτ τ : ℂ) * x) * φ (wmap τ x) - 1 + nuτ τ (cOf f τ) * x :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) (fun x hx => fv_Bser_eq hf h1 h2 hφ hx)
  exact (fv_hasDerivAt_Bf h1 h2 hφ.1 _ hw).congr_of_eventuallyEq hev

private lemma fv_Bser_zero {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) : Bser τ φ 0 = 0 := by
  rw [fv_Bser_eq hf h1 h2 hφ (mem_ball_self (by norm_num)), wmap_zero, hφ.2.1]
  ring

private lemma fv_deriv_Bser_zero {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) : deriv (Bser τ φ) 0 = 0 := by
  rw [(fv_hasDerivAt_Bser hf h1 h2 hφ (mem_ball_self (by norm_num))).deriv, wmap_zero, hφ.2.1,
    ← coeff_one_eq, fv_b1 hf h1 h2 hφ]
  have hV0 := vτ_ne_zero h1 h2
  simp only [βτ, nuτ, mul_zero, add_zero, mul_one, one_mul]
  push_cast
  generalize (vτ τ : ℂ) = V at hV0 ⊢
  field_simp
  ring

private lemma fv_Bser_bound (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) :
    ∃ M : ℝ, 0 < M ∧ ∀ w ∈ ball (0 : ℂ) (1 / 4), ‖Bser τ φ w‖ ≤ M := by
  have hcont : ContinuousOn φ (closedBall (0 : ℂ) (2 / 5)) :=
    hφ.1.continuousOn.mono (closedBall_subset_ball (by norm_num))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (2 / 5)).exists_bound_of_continuousOn hcont
  have hν := nu_bound h1 h2 (cOf_norm_le hDB hf h1 h2)
  obtain ⟨hb0, hb1⟩ := beta_bounds h1 h2
  refine ⟨2 * max C 0 + 2, by positivity, fun w hw => ?_⟩
  have hw' := mem_ball_zero_iff.mp hw
  have hs : wmap τ w ∈ closedBall (0 : ℂ) (2 / 5) := by
    rw [mem_closedBall_zero_iff]
    have hn := norm_v_add_ge h1 h2 hw
    simp only [wmap]
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith
  have hφs : ‖φ (wmap τ w)‖ ≤ max C 0 := (hC _ hs).trans (le_max_left _ _)
  have hβw : ‖1 + (βτ τ : ℂ) * w‖ ≤ 2 := by
    calc ‖1 + (βτ τ : ℂ) * w‖ ≤ ‖(1 : ℂ)‖ + ‖(βτ τ : ℂ) * w‖ := norm_add_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb0]
        nlinarith [norm_nonneg w]
  have hνw : ‖nuτ τ (cOf f τ) * w‖ ≤ 1 / 2 := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg (nuτ τ (cOf f τ))]
  have hprod : ‖(1 + (βτ τ : ℂ) * w) * φ (wmap τ w)‖ ≤ 2 * max C 0 := by
    rw [norm_mul]
    exact mul_le_mul hβw hφs (norm_nonneg _) (by norm_num)
  rw [fv_Bser_eq hf h1 h2 hφ hw]
  calc ‖(1 + (βτ τ : ℂ) * w) * φ (wmap τ w) - 1 + nuτ τ (cOf f τ) * w‖
      ≤ ‖(1 + (βτ τ : ℂ) * w) * φ (wmap τ w)‖ + ‖(1 : ℂ)‖ + ‖nuτ τ (cOf f τ) * w‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 2 * max C 0 + 2 := by
        rw [norm_one]
        linarith

/-! ### The function `N/(1 - νξ + λB)²` for small `λ` -/

/-- Its derivative in `ξ`, written out. -/
private noncomputable def fvD (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (lam w : ℂ) : ℂ :=
  ((1 + 2 * (βτ τ : ℂ) * w) * (1 - nuτ τ c * w + lam * Bser τ φ w) -
    2 * Nfun τ w * (-nuτ τ c + lam * deriv (Bser τ φ) w)) / (1 - nuτ τ c * w + lam * Bser τ φ w) ^ 3

/-- `Δ(λ) = Π_λ(iy) - Π_λ(-iy)`. -/
private noncomputable def fvΔ (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (lam : ℂ) : ℂ :=
  PiLam τ c φ lam (xiτ τ) - PiLam τ c φ lam (-xiτ τ)

/-- The explicit value of `T` for `Π_λ`: `(N_λ - kΔ_λ)/(ξ²Δ_λ)` at `ξ = iy`, `k = 1 - 2τ(β + 2ν)`. -/
private noncomputable def fvF (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (lam : ℂ) : ℂ :=
  ((-(τ : ℂ) + xiτ τ) * fvD τ c φ lam (xiτ τ) + ((τ : ℂ) + xiτ τ) * fvD τ c φ lam (-xiτ τ) -
      (1 - 2 * (τ : ℂ) * ((βτ τ : ℂ) + 2 * nuτ τ c)) * fvΔ τ c φ lam) / (xiτ τ ^ 2 * fvΔ τ c φ lam)

private lemma fv_E_ne {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) {φ : ℂ → ℂ} {M : ℝ}
    (hM0 : 0 < M) (hM : ∀ w ∈ ball (0 : ℂ) (1 / 4), ‖Bser τ φ w‖ ≤ M) {lam : ℂ}
    (hlam : lam ∈ ball (0 : ℂ) (1 / (4 * M))) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    1 - nuτ τ c * w + lam * Bser τ φ w ≠ 0 := by
  have hν := nu_bound h1 h2 hc
  have hw' := mem_ball_zero_iff.mp hw
  have hl' := mem_ball_zero_iff.mp hlam
  have hlM : ‖lam‖ * M < 1 / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hl'
    linarith
  have h3 : ‖lam * Bser τ φ w‖ < 1 / 4 := by
    rw [norm_mul]
    calc ‖lam‖ * ‖Bser τ φ w‖ ≤ ‖lam‖ * M := mul_le_mul_of_nonneg_left (hM w hw) (norm_nonneg _)
      _ < 1 / 4 := hlM
  have h4 : ‖nuτ τ c * w‖ < 1 / 2 := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg (nuτ τ c)]
  intro h0
  have h5 : (1 : ℂ) = nuτ τ c * w - lam * Bser τ φ w := by linear_combination h0
  have h6 := norm_sub_le (nuτ τ c * w) (lam * Bser τ φ w)
  rw [← h5, norm_one] at h6
  linarith

private lemma fv_hasDerivAt_N (τ : ℝ) (w : ℂ) : HasDerivAt (Nfun τ) (1 + 2 * (βτ τ : ℂ) * w) w :=
  ((hasDerivAt_id' w).mul (((hasDerivAt_id' w).const_mul (βτ τ : ℂ)).const_add 1)).congr_deriv (by ring)

private lemma fv_hasDerivAt_E (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (lam : ℂ) {w B' : ℂ}
    (hB : HasDerivAt (Bser τ φ) B' w) :
    HasDerivAt (fun x => 1 - nuτ τ c * x + lam * Bser τ φ x) (-nuτ τ c + lam * B') w :=
  ((((hasDerivAt_id' w).const_mul (nuτ τ c)).const_sub 1).add (hB.const_mul lam)).congr_deriv (by ring)

private lemma fv_hasDerivAt_PiLam_xi (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (lam : ℂ) {w : ℂ}
    (hB : HasDerivAt (Bser τ φ) (deriv (Bser τ φ) w) w) (hE : 1 - nuτ τ c * w + lam * Bser τ φ w ≠ 0) :
    HasDerivAt (PiLam τ c φ lam) (fvD τ c φ lam w) w := by
  refine ((fv_hasDerivAt_N τ w).div ((fv_hasDerivAt_E τ c φ lam hB).pow 2) (pow_ne_zero 2 hE)).congr_deriv ?_
  simp only [fvD, Pi.pow_apply]
  generalize 1 - nuτ τ c * w + lam * Bser τ φ w = E at hE ⊢
  norm_num
  field_simp

/-- For small `λ`: `coeff 1 = 1` and `coeff 2 = β + 2ν` (because `B(0) = B'(0) = 0`). -/
private lemma fv_PiLam_coeffs (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (lam : ℂ)
    (hBd : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (Bser τ φ) (deriv (Bser τ φ) w) w)
    (hB0 : Bser τ φ 0 = 0) (hB'0 : deriv (Bser τ φ) 0 = 0)
    (hE : ∀ w ∈ ball (0 : ℂ) (1 / 4), 1 - nuτ τ c * w + lam * Bser τ φ w ≠ 0) :
    coeff (PiLam τ c φ lam) 1 = 1 ∧ coeff (PiLam τ c φ lam) 2 = (βτ τ : ℂ) + 2 * nuτ τ c := by
  have hl : ∀ w : ℂ, HasDerivAt (fun x : ℂ => 1 + (βτ τ : ℂ) * x) (βτ τ : ℂ) w := fun w =>
    (((hasDerivAt_id' w).const_mul (βτ τ : ℂ)).const_add 1).congr_deriv (by ring)
  have hH : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt
      (fun x => (1 + (βτ τ : ℂ) * x) / (1 - nuτ τ c * x + lam * Bser τ φ x) ^ 2)
      (((βτ τ : ℂ) * (1 - nuτ τ c * w + lam * Bser τ φ w) ^ 2 -
        (1 + (βτ τ : ℂ) * w) * (↑2 * (1 - nuτ τ c * w + lam * Bser τ φ w) ^ (2 - 1) *
          (-nuτ τ c + lam * deriv (Bser τ φ) w))) / ((1 - nuτ τ c * w + lam * Bser τ φ w) ^ 2) ^ 2) w :=
    fun w hw => (hl w).div ((fv_hasDerivAt_E τ c φ lam (hBd w hw)).pow 2) (pow_ne_zero 2 (hE w hw))
  have hHd : DifferentiableOn ℂ (fun x => (1 + (βτ τ : ℂ) * x) / (1 - nuτ τ c * x + lam * Bser τ φ x) ^ 2)
      (ball (0 : ℂ) (1 / 4)) := fun w hw => (hH w hw).differentiableAt.differentiableWithinAt
  obtain ⟨-, e1, e2⟩ := coeff_of_mul_id (g := PiLam τ c φ lam) (by norm_num : (0 : ℝ) < 1 / 4) hHd
    (fun ξ _ => by simp only [PiLam, Nfun]; ring)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 4) := mem_ball_self (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [e1]
    simp [hB0]
  · rw [e2, (hH 0 h0).deriv, hB0, hB'0]
    norm_num

/-- `T` from the values and derivatives at `±iy` of a function `g` with `coeff g 1 = 1`, `coeff g 2 = P₂`. -/
private lemma fv_Tser_eq {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g (ball (0 : ℂ) (1 / 4))) {P2 : ℂ} (hc1 : coeff g 1 = 1) (hc2 : coeff g 2 = P2) :
    Tser τ (coeff g) =
      ((-(τ : ℂ) + xiτ τ) * deriv g (xiτ τ) + ((τ : ℂ) + xiτ τ) * deriv g (-xiτ τ) -
          (1 - 2 * (τ : ℂ) * P2) * (g (xiτ τ) - g (-xiτ τ))) / (xiτ τ ^ 2 * (g (xiτ τ) - g (-xiτ τ))) := by
  obtain ⟨hξ0, hξ, -⟩ := xi_facts h1 h2
  have hNI := numerator_identity hd τ P2 (by rw [hc1, hc2, mul_one]) hξ hξ0
  have hO := (PiOddSer_eq hd hξ hξ0).2
  simp only [Tser, UpsSer]
  rw [hc2, hO]
  generalize (-(τ : ℂ) + xiτ τ) * deriv g (xiτ τ) + ((τ : ℂ) + xiτ τ) * deriv g (-xiτ τ) = Nn at hNI ⊢
  generalize g (xiτ τ) - g (-xiτ τ) = Δ at hNI ⊢
  generalize UpsLin τ P2 (coeff g) (xiτ τ) = U at hNI ⊢
  rw [hNI]
  by_cases hΔ0 : Δ = 0
  · simp [hΔ0]
  · field_simp

private lemma fv_Tser_PiLam {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} {φ : ℂ → ℂ} {lam : ℂ}
    (hBd : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (Bser τ φ) (deriv (Bser τ φ) w) w)
    (hB0 : Bser τ φ 0 = 0) (hB'0 : deriv (Bser τ φ) 0 = 0)
    (hE : ∀ w ∈ ball (0 : ℂ) (1 / 4), 1 - nuτ τ c * w + lam * Bser τ φ w ≠ 0) :
    Tser τ (coeff (PiLam τ c φ lam)) = fvF τ c φ lam := by
  have hd : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (PiLam τ c φ lam) (fvD τ c φ lam w) w :=
    fun w hw => fv_hasDerivAt_PiLam_xi τ c φ lam (hBd w hw) (hE w hw)
  have hdiff : DifferentiableOn ℂ (PiLam τ c φ lam) (ball (0 : ℂ) (1 / 4)) :=
    fun w hw => (hd w hw).differentiableAt.differentiableWithinAt
  obtain ⟨e1, e2⟩ := fv_PiLam_coeffs τ c φ lam hBd hB0 hB'0 hE
  obtain ⟨-, hξ, -⟩ := xi_facts h1 h2
  rw [fv_Tser_eq h1 h2 hdiff e1 e2, (hd _ hξ).deriv, (hd _ (neg_mem_ball_zero hξ)).deriv]
  rfl

/-- The `λ`-derivative at `0` of the written-out `ξ`-derivative. -/
private lemma fv_hasDerivAt_D (N N' a B B' ν : ℂ) (ha : a ≠ 0) :
    HasDerivAt (fun lam : ℂ => (N' * (a + lam * B) - 2 * N * (-ν + lam * B')) / (a + lam * B) ^ 3)
      (-2 * (N' * B + N * B') / a ^ 3 - 6 * ν * N * B / a ^ 4) 0 := by
  have hE : HasDerivAt (fun lam : ℂ => a + lam * B) B 0 :=
    (((hasDerivAt_id' (0 : ℂ)).mul_const B).const_add a).congr_deriv (by ring)
  have hE' : HasDerivAt (fun lam : ℂ => -ν + lam * B') B' 0 :=
    (((hasDerivAt_id' (0 : ℂ)).mul_const B').const_add (-ν)).congr_deriv (by ring)
  have hn : HasDerivAt (fun lam : ℂ => N' * (a + lam * B) - 2 * N * (-ν + lam * B')) (N' * B - 2 * N * B') 0 :=
    (hE.const_mul N').sub (hE'.const_mul (2 * N))
  have hne : (a + 0 * B) ^ 3 ≠ 0 := by
    rw [zero_mul, add_zero]
    exact pow_ne_zero 3 ha
  refine (hn.div (hE.pow 3) hne).congr_deriv ?_
  simp only [zero_mul, add_zero, Pi.pow_apply]
  norm_num
  field_simp
  ring

/-! ### `Π_j = G · u^j` and the series of `Π̇`, `Π̇'` -/

/-- `G(ξ) = -2ξ(1 + βξ)²/(1 - νξ)³`. -/
private noncomputable def fvG (τ : ℝ) (c : ℂ) (w : ℂ) : ℂ :=
  -2 * w * (1 + (βτ τ : ℂ) * w) ^ 2 / (1 - nuτ τ c * w) ^ 3

private lemma fv_differentiableAt_G {τ : ℝ} (c : ℂ) {w : ℂ} (ha : 1 - nuτ τ c * w ≠ 0) :
    DifferentiableAt ℂ (fvG τ c) w := by
  have hn : DifferentiableAt ℂ (fun x : ℂ => -2 * x * (1 + (βτ τ : ℂ) * x) ^ 2) w := by fun_prop
  have hd : DifferentiableAt ℂ (fun x : ℂ => (1 - nuτ τ c * x) ^ 3) w := by fun_prop
  exact hn.div hd (pow_ne_zero 3 ha)

private lemma fv_PiJ_eq {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (j : ℕ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) (1 / 4)) : PiJ τ c j w = fvG τ c w * wmap τ w ^ j := by
  have hb := one_add_beta_ne h1 h2 (quarter_sub_half hw)
  have hV0 := vτ_ne_zero h1 h2
  have hVβ : (vτ τ : ℂ) + (τ : ℂ) * w = (vτ τ : ℂ) * (1 + (βτ τ : ℂ) * w) := by
    rw [one_add_beta h1 h2 w, mul_div_cancel₀ _ hV0]
  have hz : (1 + (βτ τ : ℂ) * w) ^ ((2 : ℤ) - (j : ℤ)) =
      (1 + (βτ τ : ℂ) * w) ^ 2 / (1 + (βτ τ : ℂ) * w) ^ j := by
    rw [zpow_sub₀ hb, zpow_natCast]
    norm_cast
  simp only [PiJ, fvG, wmap, hz, hVβ, div_pow, mul_pow]
  generalize 1 - nuτ τ c * w = m
  generalize 1 + (βτ τ : ℂ) * w = bb at hb ⊢
  ring

private lemma fv_deriv_PiJ {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) (j : ℕ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    deriv (PiJ τ c j) w = deriv (fvG τ c) w * wmap τ w ^ j +
      fvG τ c w * ((j : ℂ) * wmap τ w ^ (j - 1) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) := by
  have ha := one_sub_nu_ne h1 h2 hc (quarter_sub_half hw)
  have hev : PiJ τ c j =ᶠ[𝓝 w] fun x => fvG τ c x * wmap τ x ^ j :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) (fun x hx => fv_PiJ_eq h1 h2 c j hx)
  have h := (fv_differentiableAt_G c ha).hasDerivAt.mul ((hasDerivAt_wmap h1 h2 hw).pow j)
  rw [hev.deriv_eq]
  exact h.deriv

/-- `∑_{j ≥ 2} b_j u^j = φ(u) - b₀ - b₁u`. -/
private lemma fv_hasSum_tail {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) 1)) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) 1) :
    HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * u ^ j else 0) (φ u - coeff φ 0 - coeff φ 1 * u) := by
  have h := (hasSum_nat_add_iff' 2).mpr (hasSum_coeff hφd hu)
  rw [← hasSum_nat_add_iff' 2]
  convert h using 1
  · funext m
    simp only [show 2 ≤ m + 2 by omega, ↓reduceIte]
  · simp [Finset.sum_range_succ]
    try ring

/-- `∑_{j ≥ 2} j b_j u^{j-1} = φ'(u) - b₁`. -/
private lemma fv_hasSum_tail_deriv {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) 1)) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) 1) :
    HasSum (fun j : ℕ => if 2 ≤ j then (j : ℂ) * coeff φ j * u ^ (j - 1) else 0) (deriv φ u - coeff φ 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_coeff (hφd.deriv isOpen_ball) hu)
  rw [← hasSum_nat_add_iff' 2]
  convert h using 1
  · funext m
    simp only [show 2 ≤ m + 2 by omega, ↓reduceIte, coeff_deriv, show m + 2 - 1 = m + 1 by omega,
      show m + 1 + 1 = m + 2 by omega]
    push_cast
    ring
  · simp [Finset.sum_range_succ, coeff_deriv]

/-- `Π̇ = -2NB/(1 - νξ)³ = G · (φ(u) - 1 + cu)`. -/
private lemma fv_Pd_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    -2 * Nfun τ w * Bser τ φ w / (1 - nuτ τ (cOf f τ) * w) ^ 3 =
      fvG τ (cOf f τ) w * (φ (wmap τ w) - 1 + cOf f τ * wmap τ w) := by
  have hV0 := vτ_ne_zero h1 h2
  have hden := v_add_ne_zero h1 h2 hw
  have hbs : (1 + (βτ τ : ℂ) * w) * wmap τ w = w / (vτ τ : ℂ) := by
    rw [one_add_beta h1 h2 w, wmap, div_mul_div_comm, mul_comm ((vτ τ : ℂ) + (τ : ℂ) * w) w,
      mul_div_mul_right _ _ hden]
  have hνβ : nuτ τ (cOf f τ) + (βτ τ : ℂ) = cOf f τ / (vτ τ : ℂ) := by
    simp only [nuτ, βτ]
    push_cast
    ring
  have hcore : Nfun τ w * Bser τ φ w =
      w * (1 + (βτ τ : ℂ) * w) ^ 2 * (φ (wmap τ w) - 1 + cOf f τ * wmap τ w) := by
    rw [fv_Bser_eq hf h1 h2 hφ hw]
    simp only [Nfun]
    linear_combination (-(w * (1 + (βτ τ : ℂ) * w) * cOf f τ)) * hbs +
      (w * (1 + (βτ τ : ℂ) * w) * w) * hνβ
  simp only [fvG]
  rw [mul_assoc (-2 : ℂ), hcore]
  ring

/-- `∑_{j ≥ 2} b_j Π_j(ξ) = Π̇(ξ)` as a convergent series. -/
private lemma fv_hasSum_PiJ {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * PiJ τ (cOf f τ) j w else 0)
      (-2 * Nfun τ w * Bser τ φ w / (1 - nuτ τ (cOf f τ) * w) ^ 3) := by
  have hsb : wmap τ w ∈ ball (0 : ℂ) 1 := w_mem_ball h1 h2 hw
  have hsum := (fv_hasSum_tail hφ.1 hsb).mul_left (fvG τ (cOf f τ) w)
  rw [fv_Pd_eq hf h1 h2 hφ hw]
  convert hsum using 1
  · funext j
    split_ifs
    · rw [fv_PiJ_eq h1 h2 _ j hw]
      ring
    · ring
  · rw [fv_b0 hφ, fv_b1 hf h1 h2 hφ]
    ring

/-- The `ξ`-derivative of `Π̇ = -2NB/(1 - νξ)³`, written out. -/
private lemma fv_hasDerivAt_Pd (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) {w B' : ℂ} (hB : HasDerivAt (Bser τ φ) B' w)
    (ha : 1 - nuτ τ c * w ≠ 0) :
    HasDerivAt (fun x => -2 * Nfun τ x * Bser τ φ x / (1 - nuτ τ c * x) ^ 3)
      (-2 * ((1 + 2 * (βτ τ : ℂ) * w) * Bser τ φ w + Nfun τ w * B') / (1 - nuτ τ c * w) ^ 3 -
        6 * nuτ τ c * Nfun τ w * Bser τ φ w / (1 - nuτ τ c * w) ^ 4) w := by
  have ha' : HasDerivAt (fun x => 1 - nuτ τ c * x) (-nuτ τ c) w :=
    (((hasDerivAt_id' w).const_mul (nuτ τ c)).const_sub 1).congr_deriv (by ring)
  refine ((((fv_hasDerivAt_N τ w).const_mul (-2)).mul hB).div (ha'.pow 3) (pow_ne_zero 3 ha)).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  generalize 1 - nuτ τ c * w = a at ha ⊢
  norm_num
  field_simp
  ring

/-- `∑_{j ≥ 2} b_j Π_j'(ξ) = Π̇'(ξ)` as a convergent series. -/
private lemma fv_hasSum_dPiJ (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * deriv (PiJ τ (cOf f τ) j) w else 0)
      (-2 * ((1 + 2 * (βτ τ : ℂ) * w) * Bser τ φ w + Nfun τ w * deriv (Bser τ φ) w) /
          (1 - nuτ τ (cOf f τ) * w) ^ 3 -
        6 * nuτ τ (cOf f τ) * Nfun τ w * Bser τ φ w / (1 - nuτ τ (cOf f τ) * w) ^ 4) := by
  have hc := cOf_norm_le hDB hf h1 h2
  have ha := one_sub_nu_ne h1 h2 hc (quarter_sub_half hw)
  have hsb : wmap τ w ∈ ball (0 : ℂ) 1 := w_mem_ball h1 h2 hw
  have hs := hasDerivAt_wmap h1 h2 hw
  have hG := (fv_differentiableAt_G (τ := τ) (cOf f τ) ha).hasDerivAt
  have hφa : HasDerivAt φ (deriv φ (wmap τ w)) (wmap τ w) :=
    (hφ.1.differentiableAt (isOpen_ball.mem_nhds hsb)).hasDerivAt
  have hev : (fun x => -2 * Nfun τ x * Bser τ φ x / (1 - nuτ τ (cOf f τ) * x) ^ 3) =ᶠ[𝓝 w]
      fun x => fvG τ (cOf f τ) x * (φ (wmap τ x) - 1 + cOf f τ * wmap τ x) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) (fun x hx => fv_Pd_eq hf h1 h2 hφ hx)
  have hS : HasDerivAt (fun x => φ (wmap τ x) - 1 + cOf f τ * wmap τ x)
      (deriv φ (wmap τ w) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2) +
        cOf f τ * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) w :=
    ((hφa.comp w hs).sub_const 1).add (hs.const_mul (cOf f τ))
  have hA := (hG.mul hS).congr_of_eventuallyEq hev
  have hB := fv_hasDerivAt_Pd τ (cOf f τ) φ
    (fv_hasDerivAt_Bser hf h1 h2 hφ hw).differentiableAt.hasDerivAt ha
  have huniq := hA.unique hB
  have hsum := ((fv_hasSum_tail hφ.1 hsb).mul_left (deriv (fvG τ (cOf f τ)) w)).add
    ((fv_hasSum_tail_deriv hφ.1 hsb).mul_left
      (fvG τ (cOf f τ) w * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)))
  rw [← huniq]
  convert hsum using 1
  · funext j
    split_ifs with hj
    · rw [fv_deriv_PiJ h1 h2 hc j hw]
      ring
    · ring
  · rw [fv_b0 hφ, fv_b1 hf h1 h2 hφ]
    ring

/-! ### The final algebra and the derivative of `T` at `λ = 0` -/

/-- `Ṫ = ∑ b_j T_j` from the four convergent series `∑ b_j Π_j(±iy)`, `∑ b_j Π_j'(±iy)`. -/
private lemma fv_Tdot_eq {τ : ℝ} {c : ℂ} {φ : ℂ → ℂ} {P1 P2 d1 d2 : ℂ}
    (hS1 : HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * PiJ τ c j (xiτ τ) else 0) d1)
    (hS2 : HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * PiJ τ c j (-xiτ τ) else 0) d2)
    (hS3 : HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * deriv (PiJ τ c j) (xiτ τ) else 0) P1)
    (hS4 : HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * deriv (PiJ τ c j) (-xiτ τ) else 0) P2) :
    Tdot τ c φ = -1 / (ysq τ : ℂ) * (((-(τ : ℂ) + xiτ τ) * P1 + ((τ : ℂ) + xiτ τ) * P2 -
      (Qhat τ c - 1) * (d1 - d2)) / (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ))) := by
  have hsum := ((((hS3.mul_left (-(τ : ℂ) + xiτ τ)).add (hS4.mul_left ((τ : ℂ) + xiτ τ))).sub
    ((hS1.sub hS2).mul_left (Qhat τ c - 1))).div_const
      (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ))).mul_left (-1 / (ysq τ : ℂ))
  have hT : HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * TJ τ c j else 0)
      (-1 / (ysq τ : ℂ) * (((-(τ : ℂ) + xiτ τ) * P1 + ((τ : ℂ) + xiτ τ) * P2 -
        (Qhat τ c - 1) * (d1 - d2)) / (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ)))) := by
    convert hsum using 1
    funext j
    simp only [TJ]
    split_ifs <;> ring
  exact hT.tsum_eq

private lemma fv_algebra {t ξ k Dh Dh' y2 P1 P2 d1 d2 H1 H2 H1' H2' : ℂ} (hξ : ξ ≠ 0) (hDh : Dh ≠ 0)
    (hy : y2 = -ξ ^ 2) (e1 : H1' = H1) (e2 : H2' = H2) (e3 : Dh' = Dh) :
    (((-t + ξ) * P1 + (t + ξ) * P2 - k * (d1 - d2)) * (ξ ^ 2 * Dh) -
        ((-t + ξ) * H1 + (t + ξ) * H2 - k * Dh) * (ξ ^ 2 * (d1 - d2))) / (ξ ^ 2 * Dh) ^ 2 =
      -1 / y2 * (((-t + ξ) * P1 + (t + ξ) * P2 -
        (1 + ((-t + ξ) * H1' + (t + ξ) * H2') / Dh' - 1) * (d1 - d2)) / Dh') := by
  subst hy e1 e2 e3
  field_simp
  ring

private lemma fv_partB (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) :
    HasDerivAt (fun lam : ℂ => Tser τ (coeff (PiLam τ (cOf f τ) φ lam))) (Tdot τ (cOf f τ) φ) 0 := by
  have hc := cOf_norm_le hDB hf h1 h2
  obtain ⟨hξ0, hξ, hsq⟩ := xi_facts h1 h2
  have hξm := neg_mem_ball_zero hξ
  have hBd : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (Bser τ φ) (deriv (Bser τ φ) w) w :=
    fun w hw => (fv_hasDerivAt_Bser hf h1 h2 hφ hw).differentiableAt.hasDerivAt
  have hB0 := fv_Bser_zero hf h1 h2 hφ
  have hB'0 := fv_deriv_Bser_zero hf h1 h2 hφ
  obtain ⟨M, hM0, hM⟩ := fv_Bser_bound hDB hf h1 h2 hφ
  have hδ : (0 : ℝ) < 1 / (4 * M) := by positivity
  have hE : ∀ lam ∈ ball (0 : ℂ) (1 / (4 * M)), ∀ w ∈ ball (0 : ℂ) (1 / 4),
      1 - nuτ τ (cOf f τ) * w + lam * Bser τ φ w ≠ 0 :=
    fun lam hlam w hw => fv_E_ne h1 h2 hc hM0 hM hlam hw
  -- `T(λ)` is the explicit quotient `fvF` near `λ = 0`
  have hev : (fun lam : ℂ => Tser τ (coeff (PiLam τ (cOf f τ) φ lam))) =ᶠ[𝓝 0] fvF τ (cOf f τ) φ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with lam hlam
    exact fv_Tser_PiLam h1 h2 hBd hB0 hB'0 (hE lam hlam)
  -- the comparison function at `λ = 0`
  have haP := one_sub_nu_ne h1 h2 hc (quarter_sub_half hξ)
  have haM := one_sub_nu_ne h1 h2 hc (quarter_sub_half hξm)
  have hPO : PihatO τ (cOf f τ) ≠ 0 := by
    obtain ⟨-, -, -, -, -, R, hR1, -, -, -, hden⟩ := sec4_hat_bounds_proved τ h1 h2.le
    have hc' : cOf f τ ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
    obtain ⟨hQd, -⟩ := hden _ hc'
    simp only [PihatO]
    exact div_ne_zero (right_ne_zero_of_mul hQd) (pow_ne_zero 2 (left_ne_zero_of_mul hQd))
  have hDh : PiLam τ (cOf f τ) φ 0 (xiτ τ) - PiLam τ (cOf f τ) φ 0 (-xiτ τ) =
      Pihat τ (cOf f τ) (xiτ τ) - Pihat τ (cOf f τ) (-xiτ τ) := by
    rw [PiLam_zero, PiLam_zero]
  have hDh0 : PiLam τ (cOf f τ) φ 0 (xiτ τ) - PiLam τ (cOf f τ) φ 0 (-xiτ τ) ≠ 0 := by
    rw [hDh, Pihat_sub_eq h1 h2 hc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hξ0) hPO
  have hPL0 : PiLam τ (cOf f τ) φ 0 = Pihat τ (cOf f τ) := funext (PiLam_zero τ (cOf f τ) φ)
  have h0δ : (0 : ℂ) ∈ ball (0 : ℂ) (1 / (4 * M)) := mem_ball_self hδ
  have hH1 : deriv (Pihat τ (cOf f τ)) (xiτ τ) = fvD τ (cOf f τ) φ 0 (xiτ τ) := by
    rw [← hPL0]
    exact (fv_hasDerivAt_PiLam_xi τ (cOf f τ) φ 0 (hBd _ hξ) (hE 0 h0δ _ hξ)).deriv
  have hH2 : deriv (Pihat τ (cOf f τ)) (-xiτ τ) = fvD τ (cOf f τ) φ 0 (-xiτ τ) := by
    rw [← hPL0]
    exact (fv_hasDerivAt_PiLam_xi τ (cOf f τ) φ 0 (hBd _ hξm) (hE 0 h0δ _ hξm)).deriv
  -- the derivative of `fvF` at `0`
  have hDP := fv_hasDerivAt_D (Nfun τ (xiτ τ)) (1 + 2 * (βτ τ : ℂ) * xiτ τ) (1 - nuτ τ (cOf f τ) * xiτ τ)
    (Bser τ φ (xiτ τ)) (deriv (Bser τ φ) (xiτ τ)) (nuτ τ (cOf f τ)) haP
  have hDM := fv_hasDerivAt_D (Nfun τ (-xiτ τ)) (1 + 2 * (βτ τ : ℂ) * -xiτ τ) (1 - nuτ τ (cOf f τ) * -xiτ τ)
    (Bser τ φ (-xiτ τ)) (deriv (Bser τ φ) (-xiτ τ)) (nuτ τ (cOf f τ)) haM
  have hΔ := (hasDerivAt_PiLam_lam τ (cOf f τ) φ haP).sub (hasDerivAt_PiLam_lam τ (cOf f τ) φ haM)
  have hΔ0 : xiτ τ ^ 2 * (PiLam τ (cOf f τ) φ 0 (xiτ τ) - PiLam τ (cOf f τ) φ 0 (-xiτ τ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hξ0) hDh0
  have hF : HasDerivAt (fvF τ (cOf f τ) φ) _ 0 :=
    (((hDP.const_mul (-(τ : ℂ) + xiτ τ)).add (hDM.const_mul ((τ : ℂ) + xiτ τ))).sub
      (hΔ.const_mul (1 - 2 * (τ : ℂ) * ((βτ τ : ℂ) + 2 * nuτ τ (cOf f τ))))).div
      (hΔ.const_mul (xiτ τ ^ 2)) hΔ0
  -- `Ṫ = ∑ b_j T_j` through the four series at `±iy`
  have hTd := fv_Tdot_eq (fv_hasSum_PiJ hf h1 h2 hφ hξ) (fv_hasSum_PiJ hf h1 h2 hφ hξm)
    (fv_hasSum_dPiJ hDB hf h1 h2 hφ hξ) (fv_hasSum_dPiJ hDB hf h1 h2 hφ hξm)
  have hy : (ysq τ : ℂ) = -xiτ τ ^ 2 := by rw [hsq]; ring
  refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hTd, ← Pihat_Q_series h1 h2 hc]
  exact fv_algebra hξ0 hDh0 hy hH1 hH2 hDh.symm

theorem sec4_first_variation_proved (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    (∀ ξ ∈ ball (0 : ℂ) (1 / 4), PiLam τ (cOf f τ) φ 1 ξ = PiF f τ ξ ∧ PiLam τ (cOf f τ) φ 0 ξ = Pihat τ (cOf f τ) ξ ∧
      HasDerivAt (fun lam : ℂ => PiLam τ (cOf f τ) φ lam ξ)
        (-2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ (cOf f τ) * ξ) ^ 3) 0 ∧
      -2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ (cOf f τ) * ξ) ^ 3 =
        ∑' j : ℕ, if 2 ≤ j then coeff φ j * PiJ τ (cOf f τ) j ξ else 0) ∧
      HasDerivAt (fun lam : ℂ => Tser τ (coeff (PiLam τ (cOf f τ) φ lam))) (Tdot τ (cOf f τ) φ) 0 := by
  have hc := cOf_norm_le hDB hf h1 h2
  refine ⟨fun ξ hξ => ⟨PiLam_one hf h1 h2 hφ hξ, PiLam_zero τ _ φ ξ,
    hasDerivAt_PiLam_lam τ _ φ (one_sub_nu_ne h1 h2 hc (quarter_sub_half hξ)),
    Pidot_series hDB hf h1 h2 φ hξ⟩, fv_partB hDB hf h1 h2 hφ⟩

end Robinson.Proofs
