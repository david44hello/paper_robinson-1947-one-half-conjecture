/-
Robinson/Proofs/NearP_B.lean — the first variation of Section 4 (sec4_first_variation).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Proofs.NearP_A

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Pointwise facts on `|ξ| < 1/4` -/

lemma one_add_beta_ne {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 2)) :
    1 + (βτ τ : ℂ) * ξ ≠ 0 := by
  obtain ⟨hb0, hb1⟩ := beta_bounds h1 h2
  have hξ' := mem_ball_zero_iff.mp hξ
  intro h0
  have h1' : (βτ τ : ℂ) * ξ = -1 := by linear_combination h0
  have := congrArg norm h1'
  rw [norm_mul, norm_neg, norm_one, norm_real, Real.norm_eq_abs, abs_of_pos hb0] at this
  nlinarith [norm_nonneg ξ]

lemma quarter_sub_half {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) : ξ ∈ ball (0 : ℂ) (1 / 2) :=
  ball_subset_ball (by norm_num) hξ

/-- `φ` has no zero on the disc. -/
lemma sqrtQuot_ne_zero {g φ : ℂ → ℂ} (hφ : IsSqrtQuot g φ) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) : φ u ≠ 0 := by
  by_cases hu0 : u = 0
  · subst hu0
    rw [hφ.2.1]
    exact one_ne_zero
  · intro h0
    have h := hφ.2.2 u hu
    rw [h0, zero_pow two_ne_zero, mul_zero] at h
    exact hu0 h.symm

lemma Lfun_ne_zero {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) : Lfun τ (cOf f τ) φ ξ ≠ 0 := by
  rw [Lfun_eq hf h1 h2 hφ hξ]
  exact mul_ne_zero (one_add_beta_ne h1 h2 (quarter_sub_half hξ)) (sqrtQuot_ne_zero hφ (w_mem_ball h1 h2 hξ))

lemma PiLam_one {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    PiLam τ (cOf f τ) φ 1 ξ = PiF f τ ξ := by
  have hL := Lfun_ne_zero hf h1 h2 hφ hξ
  have hPL := (sec4_Pi_formula_proved f hf τ h1 h2 φ hφ).2.2.1 ξ hξ
  have hrw : 1 - nuτ τ (cOf f τ) * ξ + 1 * Bser τ φ ξ = Lfun τ (cOf f τ) φ ξ := by
    simp only [Lfun, one_mul]
  simp only [PiLam]
  rw [hrw, ← hPL, mul_div_cancel_right₀ _ (pow_ne_zero 2 hL)]

lemma PiLam_zero (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (ξ : ℂ) : PiLam τ c φ 0 ξ = Pihat τ c ξ := by
  simp [PiLam, Pihat, Nfun]

lemma hasDerivAt_PiLam_lam (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) {ξ : ℂ} (ha : 1 - nuτ τ c * ξ ≠ 0) :
    HasDerivAt (fun lam : ℂ => PiLam τ c φ lam ξ)
      (-2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ c * ξ) ^ 3) 0 := by
  have hd : HasDerivAt (fun lam : ℂ => (1 - nuτ τ c * ξ + lam * Bser τ φ ξ) ^ 2)
      (2 * (1 - nuτ τ c * ξ + 0 * Bser τ φ ξ) * Bser τ φ ξ) 0 := by
    have h := (((hasDerivAt_id' (0 : ℂ)).mul_const (Bser τ φ ξ)).const_add (1 - nuτ τ c * ξ)).pow 2
    convert h using 1
    norm_num
  have hne : (1 - nuτ τ c * ξ + 0 * Bser τ φ ξ) ^ 2 ≠ 0 := by
    rw [zero_mul, add_zero]
    exact pow_ne_zero 2 ha
  have h := (hasDerivAt_const (0 : ℂ) (Nfun τ ξ)).div hd hne
  convert h using 1 <;> first | rfl | (simp only [zero_mul, add_zero]; field_simp; ring)

/-- `Π̇ = -2NB/(1 - νξ)³ = ∑_{j ≥ 2} b_{2j-1} Π_j(ξ)`. -/
lemma Pidot_series {f : ℂ → ℂ} (hDB : FactDeBranges) (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    -2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ (cOf f τ) * ξ) ^ 3 =
      ∑' j : ℕ, if 2 ≤ j then coeff φ j * PiJ τ (cOf f τ) j ξ else 0 := by
  have hc := cOf_norm_le hDB hf h1 h2
  have ha := one_sub_nu_ne h1 h2 hc (quarter_sub_half hξ)
  have hb := one_add_beta_ne h1 h2 (quarter_sub_half hξ)
  have hden := v_add_ne_zero h1 h2 hξ
  have hV0 := vτ_ne_zero h1 h2
  simp only [Bser]
  rw [mul_div_right_comm, ← tsum_mul_left]
  congr 1
  funext j
  split_ifs with hj
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hz : (1 + (βτ τ : ℂ) * ξ) ^ ((2 : ℤ) - ((k + 2 : ℕ) : ℤ)) = ((1 + (βτ τ : ℂ) * ξ) ^ k)⁻¹ := by
      rw [show (2 : ℤ) - ((k + 2 : ℕ) : ℤ) = -(k : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hVβ : (vτ τ : ℂ) + (τ : ℂ) * ξ = (vτ τ : ℂ) * (1 + (βτ τ : ℂ) * ξ) := by
      rw [one_add_beta h1 h2 ξ, mul_div_cancel₀ _ hV0]
    simp only [PiJ, Nfun, hz, show k + 2 - 1 = k + 1 by omega]
    rw [hVβ, mul_pow]
    generalize hm : 1 - nuτ τ (cOf f τ) * ξ = m at ha ⊢
    generalize hbb : 1 + (βτ τ : ℂ) * ξ = bb at hb ⊢
    field_simp
    ring
  · rw [mul_zero]

end Robinson.Proofs
