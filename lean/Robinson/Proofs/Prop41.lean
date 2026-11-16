/-
Robinson/Proofs/Prop41.lean — proofs of prop_4_1 from its layer rows (prop_4_1_hzero_from,
prop_4_1_hcell_from, prop_4_1_proved_from).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Near
import Robinson.Defs.NearP
import Robinson.NotFormalized
import Robinson.ComputerChecked
import Robinson.Proofs.Koebe
import Robinson.Proofs.Sec3Local
import Robinson.Proofs.Sec4Hat
import Robinson.Proofs.Sec4Elem

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Elementary facts for `9/20 ≤ τ < 1/2` -/

private lemma p41_ysq_pos {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : 0 < ysq τ := by
  unfold ysq; nlinarith

private lemma p41_mem_of_normSq {w : ℂ} (h : normSq w < 1) : w ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg w]

/-- The two points `-τ ± iy` lie on the circle `|z| = 1/2`, so in the disc. -/
private lemma p41_pts_mem (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    -(τ : ℂ) + xiτ τ ∈ ball (0 : ℂ) 1 ∧ -(τ : ℂ) - xiτ τ ∈ ball (0 : ℂ) 1 := by
  have hy : yτ τ * yτ τ = 1 / 4 - τ ^ 2 := by
    unfold yτ; rw [Real.mul_self_sqrt (p41_ysq_pos h1 h2).le]; rfl
  constructor <;> apply p41_mem_of_normSq <;> simp [xiτ, normSq_apply] <;> nlinarith

/-- `Q_f = Q_g` at two points of the disc when `f = g` on the disc. -/
private lemma p41_Q_congr {f g : ℂ → ℂ} (hfg : Set.EqOn f g (ball (0 : ℂ) 1)) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) : Q f z w = Q g z w := by
  have hdz : deriv f z = deriv g z :=
    (hfg.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).deriv_eq
  have hdw : deriv f w = deriv g w :=
    (hfg.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw)).deriv_eq
  unfold Q
  rw [hfg hz, hfg hw, hdz, hdw]

/-! ### The case `e = 0`: `f_{-τ} = k` forces `f = k` on the disc

With `σ(z) = (z + τ)/(1 + τz)`, the inverse of `u ↦ (u - τ)/(1 - τu)`, the relation `f_{-τ} = k` reads
`f(z) = f(-τ) + K k(σ(z))` with `K = (1 - τ²) f'(-τ)`, and `k(σ(z)) = k(τ) + ((1 + τ)/(1 - τ))² k(z)`. The
normalization `f(0) = 0`, `f'(0) = 1` then gives `f = k`. -/

private lemma p41_den_ne {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    1 + (τ : ℂ) * z ≠ 0 := by
  intro h
  have h' : (τ : ℂ) * z = -1 := by linear_combination h
  have hn := congrArg norm h'
  rw [norm_mul, norm_neg, norm_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0] at hn
  rw [mem_ball_zero_iff] at hz
  nlinarith [norm_nonneg z, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ) (norm_nonneg z)]

/-- `σ` maps the disc into the disc: `|1 + τz|² - |z + τ|² = (1 - τ²)(1 - |z|²)`. -/
private lemma p41_sigma_mem {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (z + (τ : ℂ)) / (1 + (τ : ℂ) * z) ∈ ball (0 : ℂ) 1 := by
  have hden := p41_den_ne hτ0 hτ1 hz
  rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm]
  have hid : normSq (1 + (τ : ℂ) * z) - normSq (z + (τ : ℂ)) = (1 - τ ^ 2) * (1 - normSq z) := by
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, one_re, one_im]
    ring
  have hz2 : normSq z < 1 := by
    rw [mem_ball_zero_iff] at hz
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hpos : 0 < (1 - τ ^ 2) * (1 - normSq z) := mul_pos (by nlinarith) (by linarith)
  linarith

/-- `(σ(z) - τ)/(1 - τ σ(z)) = z`, written as the argument of `f` in the Koebe transform at `-τ`. -/
private lemma p41_inv {τ : ℝ} (hτc : (1 : ℂ) - (τ : ℂ) ^ 2 ≠ 0) {z : ℂ} (hden : 1 + (τ : ℂ) * z ≠ 0) :
    ((z + (τ : ℂ)) / (1 + (τ : ℂ) * z) + -(τ : ℂ)) /
        (1 + conj (-(τ : ℂ)) * ((z + (τ : ℂ)) / (1 + (τ : ℂ) * z))) = z := by
  have hc : conj (-(τ : ℂ)) = -(τ : ℂ) := by rw [map_neg, Complex.conj_ofReal]
  have hden' : 1 + z * (τ : ℂ) ≠ 0 := by rwa [mul_comm]
  rw [hc]
  have e1 : (z + (τ : ℂ)) / (1 + (τ : ℂ) * z) + -(τ : ℂ) = z * (1 - (τ : ℂ) ^ 2) / (1 + (τ : ℂ) * z) := by
    field_simp; ring
  have e2 : 1 + -(τ : ℂ) * ((z + (τ : ℂ)) / (1 + (τ : ℂ) * z)) = (1 - (τ : ℂ) ^ 2) / (1 + (τ : ℂ) * z) := by
    field_simp; ring
  rw [e1, e2]
  field_simp

/-- `k(σ(z)) = k(τ) + ((1 + τ)/(1 - τ))² k(z)`. -/
private lemma p41_koebe_sigma {τ : ℝ} (hτ : (1 : ℂ) - (τ : ℂ) ≠ 0) {z : ℂ} (hz : (1 : ℂ) - z ≠ 0)
    (hden : 1 + (τ : ℂ) * z ≠ 0) :
    koebe ((z + (τ : ℂ)) / (1 + (τ : ℂ) * z)) =
      koebe (τ : ℂ) + (1 + (τ : ℂ)) ^ 2 / (1 - (τ : ℂ)) ^ 2 * koebe z := by
  have hden' : 1 + z * (τ : ℂ) ≠ 0 := by rwa [mul_comm]
  have hw : 1 - (z + (τ : ℂ)) / (1 + (τ : ℂ) * z) = (1 - (τ : ℂ)) * (1 - z) / (1 + (τ : ℂ) * z) := by
    field_simp; ring
  unfold koebe
  rw [hw]
  field_simp
  ring

/-- If `f ∈ 𝒮` and `f(z) = A + K(B + C k(z))` on the disc, then `f = k` on the disc. -/
private lemma p41_eqOn_of_rep (f : ℂ → ℂ) (hf : InS f) (A K B C : ℂ)
    (hrep : ∀ z ∈ ball (0 : ℂ) 1, f z = A + K * (B + C * koebe z)) :
    Set.EqOn f koebe (ball (0 : ℂ) 1) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hk0 : koebe 0 = 0 := by simp [koebe]
  have hA : A + K * B = 0 := by
    have h := hrep 0 h0
    rw [hf.map_zero, hk0] at h
    linear_combination -h
  have hrep' : ∀ z ∈ ball (0 : ℂ) 1, f z = (K * C) * koebe z := by
    intro z hz
    rw [hrep z hz]
    linear_combination hA
  have hev : f =ᶠ[𝓝 0] fun z => (K * C) * koebe z :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0) hrep'
  have hd : deriv f 0 = K * C := by
    rw [hev.deriv_eq, deriv_const_mul _ (hasDerivAt_koebe (by norm_num)).differentiableAt,
      deriv_koebe (by norm_num)]
    norm_num
  have hKC : K * C = 1 := by rw [← hd, hf.deriv_zero]
  intro z hz
  rw [hrep' z hz, hKC, one_mul]

/-- `f_{-τ} = k` on the disc implies `f = k` on the disc. -/
private lemma p41_f_eq_koebe (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (hk : Set.EqOn (fT f τ) koebe (ball (0 : ℂ) 1)) : Set.EqOn f koebe (ball (0 : ℂ) 1) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith
  have hτ1 : τ < 1 := by linarith
  have hτball : -(τ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    exact hτ1
  have hK : (((1 - ‖-(τ : ℂ)‖ ^ 2 : ℝ)) : ℂ) * deriv f (-(τ : ℂ)) ≠ 0 := by
    refine mul_ne_zero ?_ (sec3_deriv_ne_zero_proved f hf _ hτball)
    rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    exact Complex.ofReal_ne_zero.mpr (by nlinarith : (0 : ℝ) < 1 - τ ^ 2).ne'
  have hτc : (1 : ℂ) - (τ : ℂ) ^ 2 ≠ 0 := by
    have h := Complex.ofReal_ne_zero.mpr (by nlinarith : (0 : ℝ) < 1 - τ ^ 2).ne'
    push_cast at h
    exact h
  have hτc1 : (1 : ℂ) - (τ : ℂ) ≠ 0 := by
    have h := Complex.ofReal_ne_zero.mpr (by linarith : (0 : ℝ) < 1 - τ).ne'
    push_cast at h
    exact h
  refine p41_eqOn_of_rep f hf (f (-(τ : ℂ))) ((((1 - ‖-(τ : ℂ)‖ ^ 2 : ℝ)) : ℂ) * deriv f (-(τ : ℂ)))
    (koebe (τ : ℂ)) ((1 + (τ : ℂ)) ^ 2 / (1 - (τ : ℂ)) ^ 2) ?_
  intro z hz
  have hden := p41_den_ne hτ0 hτ1 hz
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz' : z = 1 := by linear_combination -h
    rw [mem_ball_zero_iff, hz', norm_one] at hz
    exact lt_irrefl _ hz
  have h := hk (p41_sigma_mem hτ0 hτ1 hz)
  simp only [fT, koebeTransform] at h
  rw [p41_inv hτc hden, p41_koebe_sigma hτc1 hz1 hden, div_eq_iff hK] at h
  linear_combination h

/-! ### (A) The hypothesis `hzero` of `prop_4_1_from_layer` -/

set_option linter.unusedVariables false in
/-- sec_04_near.tex:337 (proof of Proposition 4.1): "If `ϰ = 0`, then `f_{-τ} = k`, so
`Q_f(-τ + iy, -τ - iy) = Q_k`" (eq:Qk). Assumes the rows `sec4_e_zero` and `sec4_Gtau`. -/
theorem prop_4_1_hzero_from
    (h_e_zero : ∀ (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
      (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (he : edef (cOf f τ) = 0),
      cOf f τ = 1 ∧ etadef (cOf f τ) = 0 ∧ (∀ j : ℕ, 2 ≤ j → coeff φ j = 0) ∧
        Set.EqOn (fT f τ) koebe (ball (0 : ℂ) 1))
    (h_Gtau : ∀ (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2),
      ∃ φ : ℂ → ℂ, IsSqrtQuot (fT f τ) φ ∧
        (∀ ψ : ℂ → ℂ, IsSqrtQuot (fT f τ) ψ → Set.EqOn ψ φ (ball (0 : ℂ) 1)) ∧
        coeff φ 1 = -cOf f τ ∧
        (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ ζ ^ 2 * fT f τ ((ζ ^ 2)⁻¹) = 1) ∧
        DifferentiableOn ℂ (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
        (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ (-ζ) = -Gtau φ ζ) ∧
        Set.InjOn (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
        ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℕ => Glaurent (cOf f τ) φ n * (ζ ^ n)⁻¹) (Gtau φ ζ - ζ))
    (hArea : FactArea) :
    ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → edef (cOf f τ) = 0 →
      Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) = (Qk τ : ℂ) := by
  intro f hf τ h1 h2 he
  obtain ⟨φ, hφ, -⟩ := h_Gtau f hf τ h1 h2
  obtain ⟨-, -, -, hk⟩ := h_e_zero hArea f hf τ h1 h2 φ hφ he
  obtain ⟨hz, hw⟩ := p41_pts_mem τ h1 h2
  rw [p41_Q_congr (p41_f_eq_koebe f hf τ h1 h2 hk) hz hw,
    show xiτ τ = (yτ τ : ℂ) * I from mul_comm _ _]
  exact (eq_Qk_proved τ h1 h2).2.2.2

/-! ### (B) The hypothesis `hcell` of `prop_4_1_from_layer` -/

/-- `|c| ≤ 1` for `9/20 ≤ τ < 1/2` (de Branges for `n = 2`, applied to `f_{-τ} ∈ 𝒮`). -/
private lemma p41_c_le (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) : ‖cOf f τ‖ ≤ 1 := by
  have hτ : -(τ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hA := hDB (fT f τ) (sec3_koebe_transform_mem_S_proved f hf _ hτ) 2 le_rfl
  norm_num at hA
  unfold cOf
  rw [norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n]
  linarith

/-- `ε(y₀) < 1`. -/
private lemma p41_epsY0_lt : epsY0 < 1 := by
  unfold epsY0 epsOf y0
  norm_num

/-- `Π₋ = max(1 - ε, ...) > 0` for every pair of caps. -/
private lemma p41_PiLowOf_pos (νp ηp : ℝ) : 0 < PiLowOf νp ηp :=
  lt_of_lt_of_le (by linarith [p41_epsY0_lt]) (le_max_left _ _)

set_option linter.unusedVariables false in
/-- sec_04_near.tex:338-342 (proof of Proposition 4.1, first display): for `e > 0` and `ρ = η/e` in the cell
`[i/256, (i+1)/256]`, `Re Q_f ≥ Re Q̂ - y²|Ṫ| - y²|T - T̂ - Ṫ| ≥ (16/27)y² + e m(ρ) - y²√(η(M + 130e)) - y²ηΛ`,
with the caps of the cell (valid by `sec4_caps_valid`). Assumes the rows `sec4_majorant_split`, `lem_4_3`,
`lem_4_5_iii`, `lem_4_6` and `sec4_Gtau`. -/
theorem prop_4_1_hcell_from
    (h_split : ∀ (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
      (h2 : τ < 1 / 2) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ),
      (Qhat τ (cOf f τ)).re - ysq τ * ‖Tdot τ (cOf f τ) φ‖ -
          ysq τ * ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
        (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re)
    (h_lem43 : ∀ (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1),
      Qk τ + edef c * mρ (etadef c / edef c) ≤ (Qhat τ c).re ∧
        16 / 27 * ysq τ + edef c * mρ (etadef c / edef c) ≤ Qk τ + edef c * mρ (etadef c / edef c))
    (h_lem45iii : ∀ (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
      (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (νp : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp)
      (hνp : νp ≤ 2),
      ‖Tdot τ (cOf f τ) φ‖ ≤
        Real.sqrt (etadef (cOf f τ)) * Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)))
    (h_lem46 : ∀ (hDB : FactDeBranges) (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
      (h2 : τ ≤ 1 / 2) (hy : 0 < yτ τ) (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ)
      (νp ηp np : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp) (hνp : νp ≤ 2) (hη : etadef (cOf f τ) ≤ ηp) (hηp : ηp ≤ 1)
      (hn : Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)) ≤ np),
      PiLowOf νp ηp ≤ ‖PiOddSer (coeff (PiF f τ)) (xiτ τ)‖ ∧
        (0 < PiLowOf νp ηp →
          ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
            etadef (cOf f τ) * LamOf νp ηp np))
    (h_Gtau : ∀ (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2),
      ∃ φ : ℂ → ℂ, IsSqrtQuot (fT f τ) φ ∧
        (∀ ψ : ℂ → ℂ, IsSqrtQuot (fT f τ) ψ → Set.EqOn ψ φ (ball (0 : ℂ) 1)) ∧
        coeff φ 1 = -cOf f τ ∧
        (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ ζ ^ 2 * fT f τ ((ζ ^ 2)⁻¹) = 1) ∧
        DifferentiableOn ℂ (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
        (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ (-ζ) = -Gtau φ ζ) ∧
        Set.InjOn (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
        ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℕ => Glaurent (cOf f τ) φ n * (ζ ^ n)⁻¹) (Gtau φ ζ - ζ))
    (hDB : FactDeBranges) (hArea : FactArea) :
    ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → yτ τ ≤ y0 → 0 < edef (cOf f τ) →
      ∀ i : ℕ, i ≤ 255 → (i : ℝ) / 256 ≤ etadef (cOf f τ) / edef (cOf f τ) →
        etadef (cOf f τ) / edef (cOf f τ) ≤ ((i : ℝ) + 1) / 256 →
        16 / 27 * ysq τ + edef (cOf f τ) * mρ (etadef (cOf f τ) / edef (cOf f τ)) -
            ysq τ * Real.sqrt (etadef (cOf f τ) * (Mcap ((i : ℝ) / 256) + 130 * edef (cOf f τ))) -
            ysq τ * etadef (cOf f τ) * Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ≤
          (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re := by
  intro f hf τ h1 h2 hy0 he i hi hlo hhi
  obtain ⟨φ, hφ, -⟩ := h_Gtau f hf τ h1 h2
  have hc : ‖cOf f τ‖ ≤ 1 := p41_c_le hDB f hf τ h1 h2
  have hc1 : cOf f τ ≠ 1 := by
    intro h
    rw [h] at he
    simp [edef] at he
  have hη0 : 0 ≤ etadef (cOf f τ) := by
    unfold etadef
    nlinarith [norm_nonneg (cOf f τ)]
  have hY : 0 ≤ ysq τ := (p41_ysq_pos h1 h2).le
  have hy : 0 < yτ τ := Real.sqrt_pos.mpr (p41_ysq_pos h1 h2)
  obtain ⟨hν, hν2, hη, hη1, -, hn⟩ := sec4_caps_valid_proved τ h1 h2.le (cOf f τ) hc hc1 i hi hlo hhi
  -- the cap `M` of the cell is `20 + N₆(ν⁺)²` with `ν⁺ = ν⁺(i/256)`
  have hM : Mcap ((i : ℝ) / 256) = 20 + N6Of (nuPlus ((i : ℝ) / 256)) ^ 2 := rfl
  have h43 := h_lem43 τ h1 h2 (cOf f τ) hc hc1
  have h45 := h_lem45iii hArea f hf τ h1 h2 hy0 φ hφ _ hν hν2
  rw [← hM, ← Real.sqrt_mul hη0] at h45
  have hn' : Real.sqrt (20 + N6Of (nuPlus ((i : ℝ) / 256)) ^ 2 + 130 * edef (cOf f τ)) ≤
      nPlus ((i : ℝ) / 256) := by
    rw [← hM]; exact hn
  have h46 := (h_lem46 hDB hArea f hf τ h1 h2.le hy hy0 φ hφ _ _ _ hν hν2 hη hη1 hn').2
    (p41_PiLowOf_pos _ _)
  have hA : ysq τ * ‖Tdot τ (cOf f τ) φ‖ ≤
      ysq τ * Real.sqrt (etadef (cOf f τ) * (Mcap ((i : ℝ) / 256) + 130 * edef (cOf f τ))) :=
    mul_le_mul_of_nonneg_left h45 hY
  have hB : ysq τ * ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
      ysq τ * etadef (cOf f τ) * Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h46 hY
  have hsplit := h_split hDB f hf τ h1 h2 φ hφ
  linarith [h43.1, h43.2]

/-! ### (C) Proposition 4.1 -/

set_option linter.unusedVariables false in
/-- Proposition 4.1 (sec_04_near.tex:24-29), from `prop_4_1_from_layer` and the layer rows used by (A) and (B).
Assumes the rows `prop_4_1_from_layer`, `sec4_e_zero`, `sec4_Gtau`, `sec4_majorant_split`, `lem_4_3`, `lem_4_5_iii`
and `lem_4_6`; then the binders and the conclusion of the row `prop_4_1`. -/
theorem prop_4_1_proved_from
    (h_from_layer : ∀ (hDB : FactDeBranges) (h48 : Check_4_8)
      (hzero : ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → edef (cOf f τ) = 0 →
        Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) = (Qk τ : ℂ))
      (hcell : ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → yτ τ ≤ y0 → 0 < edef (cOf f τ) →
        ∀ i : ℕ, i ≤ 255 → (i : ℝ) / 256 ≤ etadef (cOf f τ) / edef (cOf f τ) →
          etadef (cOf f τ) / edef (cOf f τ) ≤ ((i : ℝ) + 1) / 256 →
          16 / 27 * ysq τ + edef (cOf f τ) * mρ (etadef (cOf f τ) / edef (cOf f τ)) -
              ysq τ * Real.sqrt (etadef (cOf f τ) * (Mcap ((i : ℝ) / 256) + 130 * edef (cOf f τ))) -
              ysq τ * etadef (cOf f τ) * Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ≤
            (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re),
      ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
        Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (h_e_zero : ∀ (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
      (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (he : edef (cOf f τ) = 0),
      cOf f τ = 1 ∧ etadef (cOf f τ) = 0 ∧ (∀ j : ℕ, 2 ≤ j → coeff φ j = 0) ∧
        Set.EqOn (fT f τ) koebe (ball (0 : ℂ) 1))
    (h_Gtau : ∀ (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2),
      ∃ φ : ℂ → ℂ, IsSqrtQuot (fT f τ) φ ∧
        (∀ ψ : ℂ → ℂ, IsSqrtQuot (fT f τ) ψ → Set.EqOn ψ φ (ball (0 : ℂ) 1)) ∧
        coeff φ 1 = -cOf f τ ∧
        (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ ζ ^ 2 * fT f τ ((ζ ^ 2)⁻¹) = 1) ∧
        DifferentiableOn ℂ (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
        (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ (-ζ) = -Gtau φ ζ) ∧
        Set.InjOn (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
        ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℕ => Glaurent (cOf f τ) φ n * (ζ ^ n)⁻¹) (Gtau φ ζ - ζ))
    (h_split : ∀ (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
      (h2 : τ < 1 / 2) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ),
      (Qhat τ (cOf f τ)).re - ysq τ * ‖Tdot τ (cOf f τ) φ‖ -
          ysq τ * ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
        (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re)
    (h_lem43 : ∀ (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1),
      Qk τ + edef c * mρ (etadef c / edef c) ≤ (Qhat τ c).re ∧
        16 / 27 * ysq τ + edef c * mρ (etadef c / edef c) ≤ Qk τ + edef c * mρ (etadef c / edef c))
    (h_lem45iii : ∀ (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
      (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (νp : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp)
      (hνp : νp ≤ 2),
      ‖Tdot τ (cOf f τ) φ‖ ≤
        Real.sqrt (etadef (cOf f τ)) * Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)))
    (h_lem46 : ∀ (hDB : FactDeBranges) (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
      (h2 : τ ≤ 1 / 2) (hy : 0 < yτ τ) (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ)
      (νp ηp np : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp) (hνp : νp ≤ 2) (hη : etadef (cOf f τ) ≤ ηp) (hηp : ηp ≤ 1)
      (hn : Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)) ≤ np),
      PiLowOf νp ηp ≤ ‖PiOddSer (coeff (PiF f τ)) (xiτ τ)‖ ∧
        (0 < PiLowOf νp ηp →
          ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
            etadef (cOf f τ) * LamOf νp ηp np))
    (hDB : FactDeBranges) (hArea : FactArea) (h48 : Check_4_8) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
    Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re :=
  h_from_layer hDB h48 (prop_4_1_hzero_from h_e_zero h_Gtau hArea)
    (prop_4_1_hcell_from h_split h_lem43 h_lem45iii h_lem46 h_Gtau hDB hArea)

end Robinson.Proofs
