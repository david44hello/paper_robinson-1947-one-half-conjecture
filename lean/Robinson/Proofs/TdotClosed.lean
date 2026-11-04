/-
Robinson/Proofs/TdotClosed.lean — proofs of Tdot_closed (a sub-lemma of Lemma 4.6: the closed form
Ṫ·Π̂_o = Υ[Π̇] - T̂·Π̇_o at ξ₀ = iy, with Π̇ = -2NB/(1 - νξ)³ the first variation).
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

private lemma td_Bser_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    Bser τ φ w = (1 + (βτ τ : ℂ) * w) * φ (wmap τ w) - 1 + nuτ τ (cOf f τ) * w := by
  have h := Lfun_eq hf h1 h2 hφ hw
  simp only [Lfun] at h
  linear_combination h

private lemma td_b0 {g φ : ℂ → ℂ} (hφ : IsSqrtQuot g φ) : coeff φ 0 = 1 := by
  rw [coeff_zero_eq, hφ.2.1]

private lemma td_b1 {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) : coeff φ 1 = -cOf f τ :=
  sqrtQuot_coeff_one (fT_mem_S hf h1 h2) hφ

private lemma td_hasDerivAt_Bf {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
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

private lemma td_hasDerivAt_Bser {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    HasDerivAt (Bser τ φ) ((βτ τ : ℂ) * φ (wmap τ w) +
        (1 + (βτ τ : ℂ) * w) * (deriv φ (wmap τ w) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) +
          nuτ τ (cOf f τ)) w := by
  have hev : Bser τ φ =ᶠ[𝓝 w] fun x => (1 + (βτ τ : ℂ) * x) * φ (wmap τ x) - 1 + nuτ τ (cOf f τ) * x :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) (fun x hx => td_Bser_eq hf h1 h2 hφ hx)
  exact (td_hasDerivAt_Bf h1 h2 hφ.1 _ hw).congr_of_eventuallyEq hev

private lemma td_Bser_zero {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) : Bser τ φ 0 = 0 := by
  rw [td_Bser_eq hf h1 h2 hφ (mem_ball_self (by norm_num)), wmap_zero, hφ.2.1]
  ring

private lemma td_deriv_Bser_zero {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) : deriv (Bser τ φ) 0 = 0 := by
  rw [(td_hasDerivAt_Bser hf h1 h2 hφ (mem_ball_self (by norm_num))).deriv, wmap_zero, hφ.2.1,
    ← coeff_one_eq, td_b1 hf h1 h2 hφ]
  have hV0 := vτ_ne_zero h1 h2
  simp only [βτ, nuτ, mul_zero, add_zero, mul_one, one_mul]
  push_cast
  generalize (vτ τ : ℂ) = V at hV0 ⊢
  field_simp
  ring

private lemma td_hasDerivAt_N (τ : ℝ) (w : ℂ) : HasDerivAt (Nfun τ) (1 + 2 * (βτ τ : ℂ) * w) w :=
  ((hasDerivAt_id' w).mul (((hasDerivAt_id' w).const_mul (βτ τ : ℂ)).const_add 1)).congr_deriv (by ring)

/-! ### `Π_j = G · u^j` and the series of `Π̇`, `Π̇'` -/

/-- `G(ξ) = -2ξ(1 + βξ)²/(1 - νξ)³`. -/
private noncomputable def tdG (τ : ℝ) (c : ℂ) (w : ℂ) : ℂ :=
  -2 * w * (1 + (βτ τ : ℂ) * w) ^ 2 / (1 - nuτ τ c * w) ^ 3

private lemma td_differentiableAt_G {τ : ℝ} (c : ℂ) {w : ℂ} (ha : 1 - nuτ τ c * w ≠ 0) :
    DifferentiableAt ℂ (tdG τ c) w := by
  have hn : DifferentiableAt ℂ (fun x : ℂ => -2 * x * (1 + (βτ τ : ℂ) * x) ^ 2) w := by fun_prop
  have hd : DifferentiableAt ℂ (fun x : ℂ => (1 - nuτ τ c * x) ^ 3) w := by fun_prop
  exact hn.div hd (pow_ne_zero 3 ha)

private lemma td_PiJ_eq {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (j : ℕ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) (1 / 4)) : PiJ τ c j w = tdG τ c w * wmap τ w ^ j := by
  have hb := one_add_beta_ne h1 h2 (quarter_sub_half hw)
  have hV0 := vτ_ne_zero h1 h2
  have hVβ : (vτ τ : ℂ) + (τ : ℂ) * w = (vτ τ : ℂ) * (1 + (βτ τ : ℂ) * w) := by
    rw [one_add_beta h1 h2 w, mul_div_cancel₀ _ hV0]
  have hz : (1 + (βτ τ : ℂ) * w) ^ ((2 : ℤ) - (j : ℤ)) =
      (1 + (βτ τ : ℂ) * w) ^ 2 / (1 + (βτ τ : ℂ) * w) ^ j := by
    rw [zpow_sub₀ hb, zpow_natCast]
    norm_cast
  simp only [PiJ, tdG, wmap, hz, hVβ, div_pow, mul_pow]
  generalize 1 - nuτ τ c * w = m
  generalize 1 + (βτ τ : ℂ) * w = bb at hb ⊢
  ring

private lemma td_deriv_PiJ {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) (j : ℕ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    deriv (PiJ τ c j) w = deriv (tdG τ c) w * wmap τ w ^ j +
      tdG τ c w * ((j : ℂ) * wmap τ w ^ (j - 1) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) := by
  have ha := one_sub_nu_ne h1 h2 hc (quarter_sub_half hw)
  have hev : PiJ τ c j =ᶠ[𝓝 w] fun x => tdG τ c x * wmap τ x ^ j :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) (fun x hx => td_PiJ_eq h1 h2 c j hx)
  have h := (td_differentiableAt_G c ha).hasDerivAt.mul ((hasDerivAt_wmap h1 h2 hw).pow j)
  rw [hev.deriv_eq]
  exact h.deriv

/-- `∑_{j ≥ 2} b_j u^j = φ(u) - b₀ - b₁u`. -/
private lemma td_hasSum_tail {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) 1)) {u : ℂ}
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
private lemma td_hasSum_tail_deriv {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) 1)) {u : ℂ}
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
private lemma td_Pd_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    -2 * Nfun τ w * Bser τ φ w / (1 - nuτ τ (cOf f τ) * w) ^ 3 =
      tdG τ (cOf f τ) w * (φ (wmap τ w) - 1 + cOf f τ * wmap τ w) := by
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
    rw [td_Bser_eq hf h1 h2 hφ hw]
    simp only [Nfun]
    linear_combination (-(w * (1 + (βτ τ : ℂ) * w) * cOf f τ)) * hbs +
      (w * (1 + (βτ τ : ℂ) * w) * w) * hνβ
  simp only [tdG]
  rw [mul_assoc (-2 : ℂ), hcore]
  ring

/-- `∑_{j ≥ 2} b_j Π_j(ξ) = Π̇(ξ)` as a convergent series. -/
private lemma td_hasSum_PiJ {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * PiJ τ (cOf f τ) j w else 0)
      (-2 * Nfun τ w * Bser τ φ w / (1 - nuτ τ (cOf f τ) * w) ^ 3) := by
  have hsb : wmap τ w ∈ ball (0 : ℂ) 1 := w_mem_ball h1 h2 hw
  have hsum := (td_hasSum_tail hφ.1 hsb).mul_left (tdG τ (cOf f τ) w)
  rw [td_Pd_eq hf h1 h2 hφ hw]
  convert hsum using 1
  · funext j
    split_ifs
    · rw [td_PiJ_eq h1 h2 _ j hw]
      ring
    · ring
  · rw [td_b0 hφ, td_b1 hf h1 h2 hφ]
    ring

/-- The `ξ`-derivative of `Π̇ = -2NB/(1 - νξ)³`, written out. -/
private lemma td_hasDerivAt_Pd (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) {w B' : ℂ} (hB : HasDerivAt (Bser τ φ) B' w)
    (ha : 1 - nuτ τ c * w ≠ 0) :
    HasDerivAt (fun x => -2 * Nfun τ x * Bser τ φ x / (1 - nuτ τ c * x) ^ 3)
      (-2 * ((1 + 2 * (βτ τ : ℂ) * w) * Bser τ φ w + Nfun τ w * B') / (1 - nuτ τ c * w) ^ 3 -
        6 * nuτ τ c * Nfun τ w * Bser τ φ w / (1 - nuτ τ c * w) ^ 4) w := by
  have ha' : HasDerivAt (fun x => 1 - nuτ τ c * x) (-nuτ τ c) w :=
    (((hasDerivAt_id' w).const_mul (nuτ τ c)).const_sub 1).congr_deriv (by ring)
  refine ((((td_hasDerivAt_N τ w).const_mul (-2)).mul hB).div (ha'.pow 3) (pow_ne_zero 3 ha)).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  generalize 1 - nuτ τ c * w = a at ha ⊢
  norm_num
  field_simp
  ring

/-- `∑_{j ≥ 2} b_j Π_j'(ξ) = Π̇'(ξ)` as a convergent series. -/
private lemma td_hasSum_dPiJ (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) (1 / 4)) :
    HasSum (fun j : ℕ => if 2 ≤ j then coeff φ j * deriv (PiJ τ (cOf f τ) j) w else 0)
      (-2 * ((1 + 2 * (βτ τ : ℂ) * w) * Bser τ φ w + Nfun τ w * deriv (Bser τ φ) w) /
          (1 - nuτ τ (cOf f τ) * w) ^ 3 -
        6 * nuτ τ (cOf f τ) * Nfun τ w * Bser τ φ w / (1 - nuτ τ (cOf f τ) * w) ^ 4) := by
  have hc := cOf_norm_le hDB hf h1 h2
  have ha := one_sub_nu_ne h1 h2 hc (quarter_sub_half hw)
  have hsb : wmap τ w ∈ ball (0 : ℂ) 1 := w_mem_ball h1 h2 hw
  have hs := hasDerivAt_wmap h1 h2 hw
  have hG := (td_differentiableAt_G (τ := τ) (cOf f τ) ha).hasDerivAt
  have hφa : HasDerivAt φ (deriv φ (wmap τ w)) (wmap τ w) :=
    (hφ.1.differentiableAt (isOpen_ball.mem_nhds hsb)).hasDerivAt
  have hev : (fun x => -2 * Nfun τ x * Bser τ φ x / (1 - nuτ τ (cOf f τ) * x) ^ 3) =ᶠ[𝓝 w]
      fun x => tdG τ (cOf f τ) x * (φ (wmap τ x) - 1 + cOf f τ * wmap τ x) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) (fun x hx => td_Pd_eq hf h1 h2 hφ hx)
  have hS : HasDerivAt (fun x => φ (wmap τ x) - 1 + cOf f τ * wmap τ x)
      (deriv φ (wmap τ w) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2) +
        cOf f τ * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)) w :=
    ((hφa.comp w hs).sub_const 1).add (hs.const_mul (cOf f τ))
  have hA := (hG.mul hS).congr_of_eventuallyEq hev
  have hB := td_hasDerivAt_Pd τ (cOf f τ) φ
    (td_hasDerivAt_Bser hf h1 h2 hφ hw).differentiableAt.hasDerivAt ha
  have huniq := hA.unique hB
  have hsum := ((td_hasSum_tail hφ.1 hsb).mul_left (deriv (tdG τ (cOf f τ)) w)).add
    ((td_hasSum_tail_deriv hφ.1 hsb).mul_left
      (tdG τ (cOf f τ) w * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * w) ^ 2)))
  rw [← huniq]
  convert hsum using 1
  · funext j
    split_ifs with hj
    · rw [td_deriv_PiJ h1 h2 hc j hw]
      ring
    · ring
  · rw [td_b0 hφ, td_b1 hf h1 h2 hφ]
    ring

/-- `Ṫ = ∑ b_j T_j` from the four convergent series `∑ b_j Π_j(±iy)`, `∑ b_j Π_j'(±iy)`. -/
private lemma td_Tdot_eq {τ : ℝ} {c : ℂ} {φ : ℂ → ℂ} {P1 P2 d1 d2 : ℂ}
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


/-! ### The coefficients `coeff Π̇ 1 = coeff Π̇ 2 = 0`

`Π̇(ξ) = -2N(ξ)B(ξ)/(1 - νξ)³ = ξ · K(ξ)B(ξ)` with `K(ξ) = -2(1 + βξ)/(1 - νξ)³`. Since `B(0) = B'(0) = 0`, the
function `H = K B` has `H(0) = 0` and `H'(0) = K'(0)B(0) + K(0)B'(0) = 0`. -/

/-- The first variation `Π̇(ξ) = -2N(ξ)B(ξ)/(1 - νξ)³` as a function. -/
private noncomputable def tdPd (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  -2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ c * ξ) ^ 3

/-- `K(ξ) = -2(1 + βξ)/(1 - νξ)³`. -/
private noncomputable def tdK (τ : ℝ) (c : ℂ) (ξ : ℂ) : ℂ :=
  -2 * (1 + (βτ τ : ℂ) * ξ) / (1 - nuτ τ c * ξ) ^ 3

private lemma td_differentiableAt_K {τ : ℝ} (c : ℂ) {w : ℂ} (ha : 1 - nuτ τ c * w ≠ 0) :
    DifferentiableAt ℂ (tdK τ c) w := by
  have hn : DifferentiableAt ℂ (fun x : ℂ => -2 * (1 + (βτ τ : ℂ) * x)) w := by fun_prop
  have hd : DifferentiableAt ℂ (fun x : ℂ => (1 - nuτ τ c * x) ^ 3) w := by fun_prop
  exact hn.div hd (pow_ne_zero 3 ha)

private lemma td_Pd_coeffs (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) {φ : ℂ → ℂ} (hφ : IsSqrtQuot (fT f τ) φ) :
    coeff (tdPd τ (cOf f τ) φ) 1 = 0 ∧ coeff (tdPd τ (cOf f τ) φ) 2 = 0 := by
  have hc := cOf_norm_le hDB hf h1 h2
  have hBd : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (Bser τ φ) (deriv (Bser τ φ) w) w :=
    fun w hw => (td_hasDerivAt_Bser hf h1 h2 hφ hw).differentiableAt.hasDerivAt
  have hKd : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (tdK τ (cOf f τ)) (deriv (tdK τ (cOf f τ)) w) w :=
    fun w hw => (td_differentiableAt_K (cOf f τ) (one_sub_nu_ne h1 h2 hc (quarter_sub_half hw))).hasDerivAt
  have hH : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (fun x => tdK τ (cOf f τ) x * Bser τ φ x)
      (deriv (tdK τ (cOf f τ)) w * Bser τ φ w + tdK τ (cOf f τ) w * deriv (Bser τ φ) w) w :=
    fun w hw => (hKd w hw).mul (hBd w hw)
  have hHd : DifferentiableOn ℂ (fun x => tdK τ (cOf f τ) x * Bser τ φ x) (ball (0 : ℂ) (1 / 4)) :=
    fun w hw => (hH w hw).differentiableAt.differentiableWithinAt
  obtain ⟨-, e1, e2⟩ := coeff_of_mul_id (g := tdPd τ (cOf f τ) φ) (by norm_num : (0 : ℝ) < 1 / 4) hHd
    (fun ξ _ => by simp only [tdPd, tdK, Nfun]; ring)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 4) := mem_ball_self (by norm_num)
  have hB0 := td_Bser_zero hf h1 h2 hφ
  have hB'0 := td_deriv_Bser_zero hf h1 h2 hφ
  refine ⟨?_, ?_⟩
  · rw [e1, hB0, mul_zero]
  · rw [e2, (hH 0 h0).deriv, hB0, hB'0, mul_zero, mul_zero, add_zero]

/-! ### The closed form for a function with `coeff g 1 = coeff g 2 = 0`

For `g` holomorphic on `|ξ| < 1/4` with `coeff g 1 = coeff g 2 = 0`, the expression of `T_j` with `Π_j` replaced by
`g`, multiplied by `Π̂_o(iy)`, equals `Υ[g](iy) - T̂ Π_o[g](iy)`, where `Υ` is formed with `π̂₂ = (2c - τ)/v`. This is
the computation of Lemma 4.5(i) for a general `g`: the numerator identity, `g(ξ) - g(-ξ) = 2ξ Π_o[g](ξ)`,
`Π̂(ξ) - Π̂(-ξ) = 2ξ Π̂_o`, `Q̂ = D - y² T̂` and `D = 2 - 2τπ̂₂`. -/

private lemma td_closed_generic {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g (ball (0 : ℂ) (1 / 4))) (e1 : coeff g 1 = 0) (e2 : coeff g 2 = 0) :
    -1 / (ysq τ : ℂ) * (((-(τ : ℂ) + xiτ τ) * deriv g (xiτ τ) + ((τ : ℂ) + xiτ τ) * deriv g (-xiτ τ) -
        (Qhat τ c - 1) * (g (xiτ τ) - g (-xiτ τ))) / (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ))) * PihatO τ c =
      UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (coeff g) (xiτ τ) - That τ c * PiOddSer (coeff g) (xiτ τ) := by
  obtain ⟨hξ0, hξ, hsq⟩ := xi_facts h1 h2
  have hNI := numerator_identity hd τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (by rw [e1, e2, mul_zero]) hξ hξ0
  have hO := (PiOddSer_eq hd hξ hξ0).2
  obtain ⟨-, -, -, -, -, R, hR1, -, -, -, hden⟩ := sec4_hat_bounds_proved τ h1 h2.le
  have hc' : c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  obtain ⟨hQd, -⟩ := hden c hc'
  have hB : 1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ) ≠ 0 := right_ne_zero_of_mul hQd
  have hA : 1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 := left_ne_zero_of_mul hQd
  have hPO : PihatO τ c ≠ 0 := by
    simp only [PihatO]
    exact div_ne_zero hB (pow_ne_zero 2 hA)
  have hN : (-(τ : ℂ) + xiτ τ) * deriv g (xiτ τ) + ((τ : ℂ) + xiτ τ) * deriv g (-xiτ τ) =
      (1 - 2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ))) * (g (xiτ τ) - g (-xiτ τ)) +
        2 * xiτ τ ^ 3 * UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (coeff g) (xiτ τ) := by
    rw [← hNI]
    ring
  have hΔ : g (xiτ τ) - g (-xiτ τ) = 2 * xiτ τ * PiOddSer (coeff g) (xiτ τ) := by
    rw [hO]
    field_simp
  rw [hN, hΔ, Pihat_sub_eq h1 h2 hc, ← Qhat_eq h1 h2 hc, Dτ_eq_p2 h1 h2 c]
  have hy : (ysq τ : ℂ) = -xiτ τ ^ 2 := by rw [hsq]; ring
  rw [hy]
  field_simp
  ring

/-! ### The closed form of `Ṫ` -/

/-- `Ṫ · Π̂_o = Υ[Π̇] - T̂ · Π̇_o` at `ξ₀ = iy`, where `Π̇ = -2NB/(1 - νξ)³` is the first variation and `Υ` is
formed with `π̂₂ = (2c - τ)/v`. -/
theorem Tdot_closed (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    Tdot τ (cOf f τ) φ * PihatO τ (cOf f τ) =
      UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ))
          (coeff (fun ξ => -2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ (cOf f τ) * ξ) ^ 3)) (xiτ τ) -
        That τ (cOf f τ) *
          PiOddSer (coeff (fun ξ => -2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ (cOf f τ) * ξ) ^ 3)) (xiτ τ) := by
  have hc := cOf_norm_le hDB hf h1 h2
  obtain ⟨-, hξ, -⟩ := xi_facts h1 h2
  have hξm := neg_mem_ball_zero hξ
  have hPdd : ∀ w ∈ ball (0 : ℂ) (1 / 4), HasDerivAt (tdPd τ (cOf f τ) φ)
      (-2 * ((1 + 2 * (βτ τ : ℂ) * w) * Bser τ φ w + Nfun τ w * deriv (Bser τ φ) w) /
          (1 - nuτ τ (cOf f τ) * w) ^ 3 -
        6 * nuτ τ (cOf f τ) * Nfun τ w * Bser τ φ w / (1 - nuτ τ (cOf f τ) * w) ^ 4) w :=
    fun w hw => td_hasDerivAt_Pd τ (cOf f τ) φ
      (td_hasDerivAt_Bser hf h1 h2 hφ hw).differentiableAt.hasDerivAt
      (one_sub_nu_ne h1 h2 hc (quarter_sub_half hw))
  have hdiff : DifferentiableOn ℂ (tdPd τ (cOf f τ) φ) (ball (0 : ℂ) (1 / 4)) :=
    fun w hw => (hPdd w hw).differentiableAt.differentiableWithinAt
  obtain ⟨e1, e2⟩ := td_Pd_coeffs hDB hf h1 h2 hφ
  have hG := td_closed_generic h1 h2 hc hdiff e1 e2
  rw [(hPdd _ hξ).deriv, (hPdd _ hξm).deriv] at hG
  have hTd := td_Tdot_eq (td_hasSum_PiJ hf h1 h2 hφ hξ) (td_hasSum_PiJ hf h1 h2 hφ hξm)
    (td_hasSum_dPiJ hDB hf h1 h2 hφ hξ) (td_hasSum_dPiJ hDB hf h1 h2 hφ hξm)
  rw [hTd]
  exact hG

end Robinson.Proofs
