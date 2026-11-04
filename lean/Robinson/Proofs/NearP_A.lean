/-
Robinson/Proofs/NearP_A.lean — proofs of the power-series layer of Section 4 (first part).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.NearP
import Robinson.NotFormalized
import Robinson.Proofs.Sec3Local
import Robinson.Proofs.Sec4Hat
import Robinson.Proofs.Sec4Elem
import Robinson.ComputerChecked

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### A holomorphic logarithm and square root on the unit disc

A holomorphic `h` with no zero on the disc has a holomorphic logarithm: a primitive `F` of `h'/h` with
`F(0) = log h(0)`; then `h · exp(-F)` has derivative `0` on the (connected) disc, so it is constant `1`. -/

private lemma ball_one_mem_nhds_zero : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos

private lemma zero_mem_ball_one : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos

/-- A holomorphic function without zeros on the unit disc has a holomorphic logarithm there, with value
`log h(0)` at `0`. -/
lemma exists_log_on_ball {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h (ball (0 : ℂ) 1))
    (hne : ∀ u ∈ ball (0 : ℂ) 1, h u ≠ 0) :
    ∃ F : ℂ → ℂ, F 0 = Complex.log (h 0) ∧ (∀ u ∈ ball (0 : ℂ) 1, HasDerivAt F (deriv h u / h u) u) ∧
      ∀ u ∈ ball (0 : ℂ) 1, exp (F u) = h u := by
  have hk : DifferentiableOn ℂ (fun u => deriv h u / h u) (ball (0 : ℂ) 1) :=
    (hd.deriv isOpen_ball).div hd hne
  obtain ⟨F, hF0, hF⟩ := hk.isExactOn_ball.with_val_at 0 (Complex.log (h 0))
  refine ⟨F, hF0, hF, ?_⟩
  -- `E(u) = h(u) exp(-F(u))` has derivative zero on the disc
  have hE : ∀ u ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun w => h w * exp (-F w)) 0 u := by
    intro u hu
    have hhu : HasDerivAt h (deriv h u) u :=
      (hd.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
    have hexp : HasDerivAt (fun w => exp (-F w)) (exp (-F u) * (-(deriv h u / h u))) u :=
      ((hF u hu).neg).cexp
    have := hhu.mul hexp
    convert this using 1
    field_simp [hne u hu]
    ring
  have hEd : DifferentiableOn ℂ (fun w => h w * exp (-F w)) (ball (0 : ℂ) 1) :=
    fun u hu => (hE u hu).differentiableAt.differentiableWithinAt
  have hEz : Set.EqOn (deriv (fun w => h w * exp (-F w))) 0 (ball (0 : ℂ) 1) :=
    fun u hu => (hE u hu).deriv
  intro u hu
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected hEd hEz hu
    zero_mem_ball_one
  have h0 : h 0 * exp (-F 0) = 1 := by
    rw [hF0, Complex.exp_neg, Complex.exp_log (hne 0 zero_mem_ball_one)]
    exact mul_inv_cancel₀ (hne 0 zero_mem_ball_one)
  rw [h0, Complex.exp_neg] at hconst
  have hexpne : exp (F u) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hconst
  exact hconst.symm

/-- For `g ∈ 𝒮`, the quotient `g(u)/u` (the value `g'(0) = 1` at `0`) is `dslope g 0`; it is holomorphic and has no
zero on the disc. -/
lemma dslope_facts {g : ℂ → ℂ} (hg : InS g) :
    DifferentiableOn ℂ (dslope g 0) (ball (0 : ℂ) 1) ∧ (∀ u ∈ ball (0 : ℂ) 1, dslope g 0 u ≠ 0) ∧
      dslope g 0 0 = 1 ∧ ∀ u : ℂ, u * dslope g 0 u = g u := by
  refine ⟨(differentiableOn_dslope ball_one_mem_nhds_zero).mpr hg.differentiableOn, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      rw [dslope_same, hg.deriv_zero]
      exact one_ne_zero
    · rw [dslope_of_ne _ hu0, slope_def_field, hg.map_zero, sub_zero, sub_zero]
      have hgu : g u ≠ 0 := by
        intro h0
        exact hu0 (hg.injOn hu zero_mem_ball_one (by rw [h0, hg.map_zero]))
      exact div_ne_zero hgu hu0
  · rw [dslope_same, hg.deriv_zero]
  · intro u
    have := sub_smul_dslope g 0 u
    rw [sub_zero, hg.map_zero, sub_zero, smul_eq_mul] at this
    exact this

/-- For `g ∈ 𝒮` and `u ≠ 0` in the disc, `g(u) ≠ 0`. -/
lemma InS_apply_ne_zero {g : ℂ → ℂ} (hg : InS g) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) (hu0 : u ≠ 0) :
    g u ≠ 0 := by
  intro h0
  exact hu0 (hg.injOn hu zero_mem_ball_one (by rw [h0, hg.map_zero]))

/-- The square root of `u/g(u)` exists for `g ∈ 𝒮`: `φ = exp(-F/2)` with `exp F = g(u)/u`, `F(0) = 0`. -/
lemma exists_sqrtQuot {g : ℂ → ℂ} (hg : InS g) :
    ∃ φ : ℂ → ℂ, IsSqrtQuot g φ ∧ deriv φ 0 = -(deriv (dslope g 0) 0) / 2 := by
  obtain ⟨hhd, hhne, hh0, hgu⟩ := dslope_facts hg
  obtain ⟨F, hF0, hFd, hFexp⟩ := exists_log_on_ball hhd hhne
  rw [hh0, Complex.log_one] at hF0
  have hφd : ∀ u ∈ ball (0 : ℂ) 1, HasDerivAt (fun w => exp (-(F w / 2)))
      (exp (-(F u / 2)) * (-(deriv (dslope g 0) u / dslope g 0 u / 2))) u :=
    fun u hu => (((hFd u hu).div_const 2).neg).cexp
  refine ⟨fun w => exp (-(F w / 2)), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun u hu => (hφd u hu).differentiableAt.differentiableWithinAt
  · simp [hF0]
  · intro u hu
    have hsq : exp (-(F u / 2)) ^ 2 = (dslope g 0 u)⁻¹ := by
      rw [← Complex.exp_nat_mul, ← hFexp u hu, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [hsq, ← hgu u, mul_assoc, mul_inv_cancel₀ (hhne u hu), mul_one]
  · rw [(hφd 0 zero_mem_ball_one).deriv, hF0, hh0]
    simp only [zero_div, neg_zero, Complex.exp_zero, one_mul, div_one]
    ring

/-- Two square roots of `u/g(u)` with value `1` at `0` agree on the disc. -/
lemma sqrtQuot_unique {g φ ψ : ℂ → ℂ} (hg : InS g) (hφ : IsSqrtQuot g φ) (hψ : IsSqrtQuot g ψ) :
    Set.EqOn ψ φ (ball (0 : ℂ) 1) := by
  have hsq : ∀ u ∈ ball (0 : ℂ) 1, ψ u ^ 2 = φ u ^ 2 := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      rw [hφ.2.1, hψ.2.1]
    · have hgu := InS_apply_ne_zero hg hu hu0
      have h1 := hφ.2.2 u hu
      have h2 := hψ.2.2 u hu
      exact mul_left_cancel₀ hgu (h2.trans h1.symm)
  have hcont : ContinuousAt (fun u => ψ u + φ u) 0 :=
    ((hψ.1.differentiableAt ball_one_mem_nhds_zero).continuousAt).add
      ((hφ.1.differentiableAt ball_one_mem_nhds_zero).continuousAt)
  have hne : ∀ᶠ u in 𝓝 (0 : ℂ), ψ u + φ u ≠ 0 := by
    apply hcont.eventually_ne
    rw [hφ.2.1, hψ.2.1]
    norm_num
  have hev : ψ =ᶠ[𝓝 (0 : ℂ)] φ := by
    filter_upwards [hne, ball_one_mem_nhds_zero] with u hu hub
    have h := hsq u hub
    have : (ψ u - φ u) * (ψ u + φ u) = 0 := by ring_nf; rw [h]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hu)
  exact (hψ.1.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hφ.1.analyticOnNhd isOpen_ball) (convex_ball (0 : ℂ) 1).isPreconnected zero_mem_ball_one hev

/-! ### Taylor coefficients -/

/-- `coeff g 0 = g 0`. -/
lemma coeff_zero_eq (g : ℂ → ℂ) : coeff g 0 = g 0 := by
  simp [coeff]

/-- `coeff g 1 = g'(0)`. -/
lemma coeff_one_eq (g : ℂ → ℂ) : coeff g 1 = deriv g 0 := by
  simp [coeff]

/-- `coeff g 2 = g''(0)/2`. -/
lemma coeff_two_eq (g : ℂ → ℂ) : coeff g 2 = deriv (deriv g) 0 / 2 := by
  simp only [coeff, iteratedDeriv_succ]
  norm_num [Nat.factorial]

/-- A function holomorphic on `ball 0 r` is the sum of its Taylor series there, in the form `∑ coeff g n uⁿ`. -/
lemma hasSum_coeff {g : ℂ → ℂ} {r : ℝ} (hd : DifferentiableOn ℂ g (ball (0 : ℂ) r)) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) r) : HasSum (fun n : ℕ => coeff g n * u ^ n) (g u) := by
  convert Complex.hasSum_taylorSeries_on_ball hd hu using 1
  funext n
  simp only [coeff, sub_zero, smul_eq_mul]
  ring

/-- For `g` holomorphic on the disc with `g 0 = 0`: the second Taylor coefficient of `g` is the first derivative at
`0` of `g(u)/u`. -/
lemma coeff_two_eq_deriv_dslope {g : ℂ → ℂ} (hd : DifferentiableOn ℂ g (ball (0 : ℂ) 1)) (hg0 : g 0 = 0) :
    coeff g 2 = deriv (dslope g 0) 0 := by
  set h := dslope g 0 with hh
  have hhd : DifferentiableOn ℂ h (ball (0 : ℂ) 1) := (differentiableOn_dslope ball_one_mem_nhds_zero).mpr hd
  have hgu : ∀ u : ℂ, g u = u * h u := by
    intro u
    have := sub_smul_dslope g 0 u
    rw [sub_zero, hg0, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hgfun : g = fun u => u * h u := funext hgu
  have hdg : ∀ u ∈ ball (0 : ℂ) 1, deriv g u = h u + u * deriv h u := by
    intro u hu
    have hhu : HasDerivAt h (deriv h u) u := (hhd.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
    rw [hgfun]
    have := (hasDerivAt_id u).mul hhu
    simp only [id, one_mul] at this
    exact this.deriv
  have hev : deriv g =ᶠ[𝓝 (0 : ℂ)] fun u => h u + u * deriv h u :=
    Filter.eventually_of_mem ball_one_mem_nhds_zero hdg
  have hh'd : DifferentiableAt ℂ (deriv h) 0 :=
    ((hhd.analyticOnNhd isOpen_ball) 0 zero_mem_ball_one).deriv.differentiableAt
  have hh0 : HasDerivAt h (deriv h 0) 0 := (hhd.differentiableAt ball_one_mem_nhds_zero).hasDerivAt
  have hsum : HasDerivAt (fun u => h u + u * deriv h u) (deriv h 0 + (1 * deriv h 0 + 0 * deriv (deriv h) 0)) 0 :=
    hh0.add ((hasDerivAt_id' 0).mul hh'd.hasDerivAt)
  rw [coeff_two_eq, hev.deriv_eq, hsum.deriv]
  ring

/-! ### The square root `φ` and the function `G_τ` -/

/-- For every square root `φ` of `u/g(u)`: `coeff φ 1 = -(coeff g 2)/2`. -/
lemma sqrtQuot_coeff_one {g φ : ℂ → ℂ} (hg : InS g) (hφ : IsSqrtQuot g φ) : coeff φ 1 = -(coeff g 2 / 2) := by
  obtain ⟨φ₀, hφ₀, hd₀⟩ := exists_sqrtQuot hg
  have hev : φ =ᶠ[𝓝 (0 : ℂ)] φ₀ := Filter.eventually_of_mem ball_one_mem_nhds_zero (sqrtQuot_unique hg hφ₀ hφ)
  rw [coeff_one_eq, hev.deriv_eq, hd₀, coeff_two_eq_deriv_dslope hg.differentiableOn hg.map_zero]
  ring

/-- `|ζ| > 1` gives `(ζ²)⁻¹` in the unit disc. -/
lemma inv_sq_mem_ball {ζ : ℂ} (hζ : 1 < ‖ζ‖) : (ζ ^ 2)⁻¹ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_inv, norm_pow]
  have h1 : 1 < ‖ζ‖ ^ 2 := by nlinarith
  exact inv_lt_one_of_one_lt₀ h1

lemma ne_zero_of_one_lt_norm {ζ : ℂ} (hζ : 1 < ‖ζ‖) : ζ ≠ 0 := by
  rintro rfl
  simp at hζ
  linarith

/-- `G_τ(ζ)² g(ζ⁻²) = 1` for `|ζ| > 1`. -/
lemma gtau_sq_mul {g φ : ℂ → ℂ} (hφ : IsSqrtQuot g φ) {ζ : ℂ} (hζ : 1 < ‖ζ‖) :
    Gtau φ ζ ^ 2 * g ((ζ ^ 2)⁻¹) = 1 := by
  have h := hφ.2.2 _ (inv_sq_mem_ball hζ)
  have hζ0 := ne_zero_of_one_lt_norm hζ
  simp only [Gtau]
  calc (ζ * φ (ζ ^ 2)⁻¹) ^ 2 * g (ζ ^ 2)⁻¹ = ζ ^ 2 * (g (ζ ^ 2)⁻¹ * φ (ζ ^ 2)⁻¹ ^ 2) := by ring
    _ = 1 := by rw [h]; field_simp

lemma gtau_differentiableOn {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) 1)) :
    DifferentiableOn ℂ (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} := by
  have hinv : DifferentiableOn ℂ (fun ζ : ℂ => (ζ ^ 2)⁻¹) {ζ : ℂ | 1 < ‖ζ‖} :=
    (differentiableOn_pow 2).inv (fun ζ hζ => pow_ne_zero 2 (ne_zero_of_one_lt_norm hζ))
  exact differentiableOn_id.mul (hφd.comp hinv (fun ζ hζ => inv_sq_mem_ball hζ))

lemma gtau_odd (φ : ℂ → ℂ) (ζ : ℂ) : Gtau φ (-ζ) = -Gtau φ ζ := by
  simp [Gtau]

lemma gtau_injOn {g φ : ℂ → ℂ} (hg : InS g) (hφ : IsSqrtQuot g φ) :
    Set.InjOn (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} := by
  intro ζ₁ h₁ ζ₂ h₂ heq
  have hs₁ := gtau_sq_mul hφ h₁
  have hs₂ := gtau_sq_mul hφ h₂
  rw [heq] at hs₁
  have hG : Gtau φ ζ₂ ^ 2 ≠ 0 := left_ne_zero_of_mul_eq_one hs₂
  have hgeq : g ((ζ₁ ^ 2)⁻¹) = g ((ζ₂ ^ 2)⁻¹) := mul_left_cancel₀ hG (hs₁.trans hs₂.symm)
  have hu := hg.injOn (inv_sq_mem_ball h₁) (inv_sq_mem_ball h₂) hgeq
  have hsq : ζ₁ ^ 2 = ζ₂ ^ 2 := inv_injective hu
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · exfalso
    have hz : Gtau φ ζ₂ = 0 := by
      have h' : Gtau φ ζ₁ = -Gtau φ ζ₂ := by rw [h, gtau_odd]
      rw [h'] at heq
      linear_combination -heq / 2
    rw [hz] at hs₂
    simp at hs₂

/-- The Laurent expansion `G_τ(ζ) - ζ = ∑_n Glaurent n ζ^{-n}` for `|ζ| > 1`. -/
lemma gtau_hasSum {g φ : ℂ → ℂ} (hg : InS g) (hφ : IsSqrtQuot g φ) {ζ : ℂ} (hζ : 1 < ‖ζ‖) :
    HasSum (fun n : ℕ => Glaurent (coeff g 2 / 2) φ n * (ζ ^ n)⁻¹) (Gtau φ ζ - ζ) := by
  set u := (ζ ^ 2)⁻¹ with hu
  have hζ0 := ne_zero_of_one_lt_norm hζ
  have hT := hasSum_coeff hφ.1 (inv_sq_mem_ball hζ)
  have hT1 : HasSum (fun n : ℕ => coeff φ (n + 1) * u ^ (n + 1)) (φ u - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hT
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, coeff_zero_eq, hφ.2.1] at this
    exact this
  have hT2 : HasSum (fun n : ℕ => ζ * (coeff φ (n + 1) * u ^ (n + 1))) (Gtau φ ζ - ζ) := by
    have := hT1.mul_left ζ
    convert this using 1
    simp only [Gtau, u]
    ring
  have hc1 := sqrtQuot_coeff_one hg hφ
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b hab => by simp at hab; omega
  rw [← hinj.hasSum_iff]
  · convert hT2 using 1
    funext m
    simp only [Function.comp, Glaurent]
    have hpow : ζ * u ^ (m + 1) = (ζ ^ (2 * m + 1))⁻¹ := by
      rw [hu, inv_pow, ← pow_mul]
      field_simp
      ring
    have hcoef : (if 2 * m + 1 = 1 then -(coeff g 2 / 2) else
        if (2 * m + 1) % 2 = 1 then coeff φ ((2 * m + 1 + 1) / 2) else 0) = coeff φ (m + 1) := by
      by_cases hm : m = 0
      · subst hm
        simp [hc1]
      · have h1 : 2 * m + 1 ≠ 1 := by omega
        have h2 : (2 * m + 1) % 2 = 1 := by omega
        have h3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
        simp only [h1, h2, h3, ↓reduceIte]
    rw [hcoef, ← hpow]
    ring
  · intro n hn
    have hev : n % 2 = 0 := by
      by_contra hne
      exact hn ⟨n / 2, by simp only; omega⟩
    have h1 : n ≠ 1 := by omega
    have h2 : ¬ n % 2 = 1 := by omega
    simp [Glaurent, h1, h2]

/-! ### Row: sec4_Gtau -/

lemma fT_mem_S {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : InS (fT f τ) := by
  have hτ : -(τ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  exact sec3_koebe_transform_mem_S_proved f hf _ hτ

theorem sec4_Gtau_proved (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    ∃ φ : ℂ → ℂ, IsSqrtQuot (fT f τ) φ ∧
      (∀ ψ : ℂ → ℂ, IsSqrtQuot (fT f τ) ψ → Set.EqOn ψ φ (ball (0 : ℂ) 1)) ∧
      coeff φ 1 = -cOf f τ ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ ζ ^ 2 * fT f τ ((ζ ^ 2)⁻¹) = 1) ∧
      DifferentiableOn ℂ (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ (-ζ) = -Gtau φ ζ) ∧
      Set.InjOn (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
      ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℕ => Glaurent (cOf f τ) φ n * (ζ ^ n)⁻¹) (Gtau φ ζ - ζ) := by
  have hg := fT_mem_S hf h1 h2
  obtain ⟨φ, hφ, -⟩ := exists_sqrtQuot hg
  exact ⟨φ, hφ, fun ψ hψ => sqrtQuot_unique hg hφ hψ, sqrtQuot_coeff_one hg hφ,
    fun ζ hζ => gtau_sq_mul hφ hζ, gtau_differentiableOn hφ.1, fun ζ _ => gtau_odd φ ζ, gtau_injOn hg hφ,
    fun ζ hζ => gtau_hasSum hg hφ hζ⟩

/-! ### Rows: sec4_area, sec4_e_zero (the area theorem for `G_τ`) -/

/-- Re-indexing the area sum: `∑_n n |b_n|²` over the Laurent coefficients of `G_τ` is `|c|² + ∑_{j ≥ 2} (2j - 1)
|coeff φ j|²`. -/
private lemma area_reindex {c : ℂ} {φ : ℂ → ℂ} {S : ℝ}
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

theorem sec4_area_proved (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    Summable (fun j : ℕ => if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) ∧
      ‖cOf f τ‖ ^ 2 + ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) ≤ 1 ∧
      ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) ≤ etadef (cOf f τ) := by
  have hg := fT_mem_S hf h1 h2
  obtain ⟨hsum, hle⟩ := hArea (Gtau φ) (Glaurent (cOf f τ) φ) (gtau_differentiableOn hφ.1) (gtau_injOn hg hφ)
    (fun ζ hζ => gtau_hasSum hg hφ hζ)
  have ht := area_reindex hsum.hasSum
  rw [ht.tsum_eq]
  refine ⟨ht.summable, by linarith, ?_⟩
  simp only [etadef]
  linarith

theorem sec4_e_zero_proved (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (he : edef (cOf f τ) = 0) :
    cOf f τ = 1 ∧ etadef (cOf f τ) = 0 ∧ (∀ j : ℕ, 2 ≤ j → coeff φ j = 0) ∧
      Set.EqOn (fT f τ) koebe (ball (0 : ℂ) 1) := by
  obtain ⟨hsum, hle, -⟩ := sec4_area_proved hArea f hf τ h1 h2 φ hφ
  have hnn : ∀ j : ℕ, 0 ≤ (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) := by
    intro j
    split_ifs with hj
    · have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      exact mul_nonneg (by linarith) (by positivity)
    · exact le_refl 0
  have htn : 0 ≤ ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) := tsum_nonneg hnn
  have hre : (cOf f τ).re = 1 := by simp only [edef] at he; linarith
  have hc1 : cOf f τ = 1 := by
    have hns : ‖cOf f τ‖ ^ 2 = (cOf f τ).re ^ 2 + (cOf f τ).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hre] at hns
    have him2 : (cOf f τ).im ^ 2 = 0 := by nlinarith [sq_nonneg (cOf f τ).im]
    have him : (cOf f τ).im = 0 := (pow_eq_zero_iff two_ne_zero).mp him2
    exact Complex.ext (by simp [hre]) (by simp [him])
  have hη : etadef (cOf f τ) = 0 := by simp [etadef, hc1]
  have hzero : ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) = 0 := by
    rw [hc1, norm_one, one_pow] at hle
    linarith
  have hfun := (hasSum_zero_iff_of_nonneg hnn).mp (hzero ▸ hsum.hasSum)
  have hbj : ∀ j : ℕ, 2 ≤ j → coeff φ j = 0 := by
    intro j hj
    have hj0 := congrFun hfun j
    simp only [hj, ↓reduceIte, Pi.zero_apply] at hj0
    have h2j : (0 : ℝ) < 2 * (j : ℝ) - 1 := by
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hsq : ‖coeff φ j‖ ^ 2 = 0 := (mul_eq_zero.mp hj0).resolve_left h2j.ne'
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  refine ⟨hc1, hη, hbj, ?_⟩
  intro u hu
  have hc1' : coeff φ 1 = -1 := by
    rw [sqrtQuot_coeff_one (fT_mem_S hf h1 h2) hφ]
    show -(cOf f τ) = -1
    rw [hc1]
  have hφu : φ u = 1 - u := by
    have hfin : HasSum (fun n : ℕ => coeff φ n * u ^ n) (∑ n ∈ Finset.range 2, coeff φ n * u ^ n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by
        have : 2 ≤ n := by simp at hn; omega
        rw [hbj n this, zero_mul])
    rw [(hasSum_coeff hφ.1 hu).unique hfin]
    simp [Finset.sum_range_succ, coeff_zero_eq, hφ.2.1, hc1']
    try ring
  have h := hφ.2.2 u hu
  rw [hφu] at h
  have h1u : (1 - u) ≠ 0 := by
    intro h0
    have hu1 : u = 1 := by linear_combination -h0
    rw [hu1, mem_ball_zero_iff, norm_one] at hu
    exact lt_irrefl _ hu
  simp only [koebe]
  rw [eq_div_iff (pow_ne_zero 2 h1u)]
  exact h

/-! ### The numbers `v`, `v + τξ` for `9/20 ≤ τ < 1/2`, `|ξ| < 1/4` -/

lemma vτ_ge {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : 3 / 4 < vτ τ := by
  simp only [vτ]; nlinarith

lemma vτ_ne_zero {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : (vτ τ : ℂ) ≠ 0 := by
  have := vτ_ge h1 h2
  exact_mod_cast (by linarith : vτ τ ≠ 0)

lemma norm_v_add_ge {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    5 / 8 ≤ ‖(vτ τ : ℂ) + (τ : ℂ) * ξ‖ := by
  have hv := vτ_ge h1 h2
  rw [mem_ball_zero_iff] at hξ
  have hnv : ‖(vτ τ : ℂ)‖ = vτ τ := by rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnt : ‖(τ : ℂ) * ξ‖ = τ * ‖ξ‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have htri := norm_sub_norm_le (vτ τ : ℂ) (-((τ : ℂ) * ξ))
  rw [norm_neg, sub_neg_eq_add, hnv, hnt] at htri
  nlinarith [norm_nonneg ξ]

lemma v_add_ne_zero {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    (vτ τ : ℂ) + (τ : ℂ) * ξ ≠ 0 := by
  intro h0
  have := norm_v_add_ge h1 h2 hξ
  rw [h0, norm_zero] at this
  linarith

lemma w_mem_ball {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) ∈ ball (0 : ℂ) 1 := by
  have hn := norm_v_add_ge h1 h2 hξ
  have hξ' := mem_ball_zero_iff.mp hξ
  rw [mem_ball_zero_iff, norm_div, div_lt_one (by linarith)]
  linarith

lemma ball_quarter_sub {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    -(τ : ℂ) + ξ ∈ ball (0 : ℂ) 1 := by
  have hξ' := mem_ball_zero_iff.mp hξ
  rw [mem_ball_zero_iff]
  calc ‖-(τ : ℂ) + ξ‖ ≤ ‖-(τ : ℂ)‖ + ‖ξ‖ := norm_add_le _ _
    _ < 1 := by
      rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith

/-! ### Row: sec4_Pi_formula -/

/-- The automorphism identity `(u - τ)/(1 - τu) = -τ + ξ` at `u = ξ/(v + τξ)`. -/
lemma mobius_w {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) - (τ : ℂ)) / (1 - (τ : ℂ) * (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) =
      -(τ : ℂ) + ξ := by
  have hden := v_add_ne_zero h1 h2 hξ
  have hV0 := vτ_ne_zero h1 h2
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

lemma PiF_eq_fT {f : ℂ → ℂ} {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    PiF f τ ξ = (vτ τ : ℂ) * fT f τ (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ)) := by
  have hV0 := vτ_ne_zero h1 h2
  have harg : (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) + -(τ : ℂ)) /
      (1 + (starRingEnd ℂ) (-(τ : ℂ)) * (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) = -(τ : ℂ) + ξ := by
    rw [map_neg, Complex.conj_ofReal, ← sub_eq_add_neg, neg_mul, ← sub_eq_add_neg]
    exact mobius_w h1 h2 hξ
  have hnorm : ((1 - ‖-(τ : ℂ)‖ ^ 2 : ℝ) : ℂ) = (vτ τ : ℂ) := by
    rw [norm_neg, norm_real, Real.norm_eq_abs, sq_abs]
    rfl
  simp only [PiF, fT, koebeTransform]
  rw [harg, hnorm, ← mul_div_assoc, mul_div_mul_left _ _ hV0]

/-- `1 + βξ = (v + τξ)/v`. -/
lemma one_add_beta {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (ξ : ℂ) :
    1 + (βτ τ : ℂ) * ξ = ((vτ τ : ℂ) + (τ : ℂ) * ξ) / (vτ τ : ℂ) := by
  have hV0 := vτ_ne_zero h1 h2
  simp only [βτ]
  push_cast
  field_simp

/-- The map `u(ξ) = ξ/(v + τξ)`. -/
noncomputable def wmap (τ : ℝ) (ξ : ℂ) : ℂ := ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ)

lemma wmap_zero (τ : ℝ) : wmap τ 0 = 0 := by simp [wmap]

lemma hasDerivAt_wmap {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    HasDerivAt (wmap τ) ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ 2) ξ := by
  have hden := v_add_ne_zero h1 h2 hξ
  have h := (hasDerivAt_id' ξ).div (((hasDerivAt_id' ξ).const_mul (τ : ℂ)).const_add (vτ τ : ℂ)) hden
  convert h using 1 <;> first | rfl | ring

/-- `L(ξ) = (1 + βξ) φ(u(ξ))` on `|ξ| < 1/4`. -/
lemma Lfun_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    Lfun τ (cOf f τ) φ ξ = (1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ) := by
  have hden := v_add_ne_zero h1 h2 hξ
  have hV0 := vτ_ne_zero h1 h2
  have hc1 := sqrtQuot_coeff_one (fT_mem_S hf h1 h2) hφ
  have hT : HasSum (fun i : ℕ => (1 + (βτ τ : ℂ) * ξ) * (coeff φ i * wmap τ ξ ^ i))
      ((1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ)) :=
    (hasSum_coeff hφ.1 (w_mem_ball h1 h2 hξ)).mul_left (1 + (βτ τ : ℂ) * ξ)
  -- the terms `j ≥ 2` of `(1 + βξ) φ(u)` are the terms of `B`
  have hterm : ∀ k : ℕ, (1 + (βτ τ : ℂ) * ξ) * (coeff φ (k + 1) * wmap τ ξ ^ (k + 1)) =
      coeff φ (k + 1) * ξ ^ (k + 1) / ((vτ τ : ℂ) * ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ k) := by
    intro k
    rw [one_add_beta h1 h2 ξ]
    simp only [wmap, div_pow]
    field_simp
    ring
  have hB : HasSum (fun j : ℕ => if 2 ≤ j then
        coeff φ j * ξ ^ j / ((vτ τ : ℂ) * ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ (j - 1)) else 0)
      ((1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ) -
        (1 + (βτ τ : ℂ) * ξ) * (coeff φ 0 * wmap τ ξ ^ 0 + coeff φ 1 * wmap τ ξ ^ 1)) := by
    have h2' := (hasSum_nat_add_iff' 2).mpr hT
    rw [← hasSum_nat_add_iff' 2]
    convert h2' using 1
    · funext m
      simp only [show 2 ≤ m + 2 by omega, ↓reduceIte]
      exact (hterm (m + 1)).symm
    · simp [Finset.sum_range_succ]
      try ring
  have hBser : Bser τ φ ξ = (1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ) -
      (1 + (βτ τ : ℂ) * ξ) * (coeff φ 0 * wmap τ ξ ^ 0 + coeff φ 1 * wmap τ ξ ^ 1) := hB.tsum_eq
  rw [Lfun, hBser, coeff_zero_eq, hφ.2.1, hc1, one_add_beta h1 h2 ξ]
  simp only [nuτ, cOf, wmap, pow_zero, pow_one, mul_one]
  field_simp
  ring

/-- The coefficient `π₁ = 1` and the derivative of `Π`. -/
lemma hasDerivAt_PiF {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} {ξ : ℂ} (hξ : -(τ : ℂ) + ξ ∈ ball (0 : ℂ) 1) :
    HasDerivAt (PiF f τ) (deriv f (-(τ : ℂ) + ξ) / deriv f (-(τ : ℂ))) ξ := by
  have hfd : HasDerivAt f (deriv f (-(τ : ℂ) + ξ)) (-(τ : ℂ) + ξ) :=
    (hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hξ)).hasDerivAt
  have hc : HasDerivAt (fun x : ℂ => -(τ : ℂ) + x) 1 ξ := (hasDerivAt_id' ξ).const_add _
  have h := ((hfd.comp ξ hc).sub_const (f (-(τ : ℂ)))).div_const (deriv f (-(τ : ℂ)))
  convert h using 1 <;> first | rfl | simp

lemma neg_tau_mem_ball {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : -(τ : ℂ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

lemma PiF_coeff_one {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    coeff (PiF f τ) 1 = 1 := by
  have hb : -(τ : ℂ) + 0 ∈ ball (0 : ℂ) 1 := by rw [add_zero]; exact neg_tau_mem_ball h1 h2
  rw [coeff_one_eq, (hasDerivAt_PiF hf hb).deriv, add_zero]
  exact div_self (sec3_deriv_ne_zero_proved f hf _ (neg_tau_mem_ball h1 h2))

/-- `Π(ξ) = v f_{-τ}(u(ξ))` has derivative `v f_{-τ}'(u(ξ)) u'(ξ)`. -/
lemma hasDerivAt_Vfw {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    HasDerivAt (fun x => (vτ τ : ℂ) * fT f τ (wmap τ x))
      ((vτ τ : ℂ) * (deriv (fT f τ) (wmap τ ξ) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ 2))) ξ := by
  have hT := fT_mem_S hf h1 h2
  have hfd : HasDerivAt (fT f τ) (deriv (fT f τ) (wmap τ ξ)) (wmap τ ξ) :=
    (hT.differentiableOn.differentiableAt (isOpen_ball.mem_nhds (w_mem_ball h1 h2 hξ))).hasDerivAt
  exact (hfd.comp ξ (hasDerivAt_wmap h1 h2 hξ)).const_mul _

/-- `π₂ = (2c - τ)/v`, from `Π(ξ) = v f_{-τ}(u(ξ))`: `Π''(0) = v (f_{-τ}''(0) u'(0)² + f_{-τ}'(0) u''(0))`. -/
lemma PiF_coeff_two {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    coeff (PiF f τ) 2 = (2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ) := by
  have hT := fT_mem_S hf h1 h2
  have hV0 := vτ_ne_zero h1 h2
  have hq : ball (0 : ℂ) (1 / 4) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 (by norm_num)
  have hq0 : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 4) := mem_ball_self (by norm_num)
  have hev : PiF f τ =ᶠ[𝓝 (0 : ℂ)] fun x => (vτ τ : ℂ) * fT f τ (wmap τ x) :=
    Filter.eventually_of_mem hq (fun ξ hξ => PiF_eq_fT h1 h2 hξ)
  have hev2 : deriv (fun x => (vτ τ : ℂ) * fT f τ (wmap τ x)) =ᶠ[𝓝 (0 : ℂ)]
      fun ξ => (vτ τ : ℂ) * (deriv (fT f τ) (wmap τ ξ) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ 2)) :=
    Filter.eventually_of_mem hq (fun ξ hξ => (hasDerivAt_Vfw hf h1 h2 hξ).deriv)
  have hA : HasDerivAt (deriv (fT f τ)) (deriv (deriv (fT f τ)) 0) (wmap τ 0) := by
    rw [wmap_zero]
    exact ((hT.differentiableOn.analyticOnNhd isOpen_ball) 0 zero_mem_ball_one).deriv.differentiableAt.hasDerivAt
  have hAw := hA.comp (0 : ℂ) (hasDerivAt_wmap h1 h2 hq0)
  have hden0 : (vτ τ : ℂ) + (τ : ℂ) * 0 ≠ 0 := v_add_ne_zero h1 h2 hq0
  have hp : HasDerivAt (fun ξ : ℂ => ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ 2)
      (2 * ((vτ τ : ℂ) + (τ : ℂ) * 0) * (τ : ℂ)) 0 := by
    have h := (((hasDerivAt_id' (0 : ℂ)).const_mul (τ : ℂ)).const_add (vτ τ : ℂ)).pow 2
    convert h using 1
    push_cast
    ring
  have hR := (hasDerivAt_const (0 : ℂ) (vτ τ : ℂ)).div hp (pow_ne_zero 2 hden0)
  have hD : HasDerivAt
      (fun ξ => (vτ τ : ℂ) * (deriv (fT f τ) (wmap τ ξ) * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ 2)))
      ((vτ τ : ℂ) * (deriv (deriv (fT f τ)) 0 * ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * 0) ^ 2) *
          ((vτ τ : ℂ) / ((vτ τ : ℂ) + (τ : ℂ) * 0) ^ 2) +
        deriv (fT f τ) (wmap τ 0) *
          ((0 * ((vτ τ : ℂ) + (τ : ℂ) * 0) ^ 2 - (vτ τ : ℂ) * (2 * ((vτ τ : ℂ) + (τ : ℂ) * 0) * (τ : ℂ))) /
            (((vτ τ : ℂ) + (τ : ℂ) * 0) ^ 2) ^ 2))) 0 :=
    (hAw.mul hR).const_mul (vτ τ : ℂ)
  rw [coeff_two_eq, hev.deriv.deriv_eq, hev2.deriv_eq, hD.deriv, wmap_zero, hT.deriv_zero]
  simp only [cOf, coeff_two_eq, mul_zero, add_zero]
  field_simp
  ring

theorem sec4_Pi_formula_proved (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    (∀ ξ ∈ ball (0 : ℂ) (1 / 4),
      (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) - (τ : ℂ)) / (1 - (τ : ℂ) * (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) = -(τ : ℂ) + ξ) ∧
      (∀ ξ ∈ ball (0 : ℂ) (1 / 4), PiF f τ ξ = (vτ τ : ℂ) * fT f τ (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) ∧
      (∀ ξ ∈ ball (0 : ℂ) (1 / 4), PiF f τ ξ * Lfun τ (cOf f τ) φ ξ ^ 2 = Nfun τ ξ) ∧
      coeff (PiF f τ) 1 = 1 ∧ coeff (PiF f τ) 2 = (2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ) := by
  refine ⟨fun ξ hξ => mobius_w h1 h2 hξ, fun ξ hξ => PiF_eq_fT h1 h2 hξ, ?_, PiF_coeff_one hf h1 h2,
    PiF_coeff_two hf h1 h2⟩
  intro ξ hξ
  have hden := v_add_ne_zero h1 h2 hξ
  have hV0 := vτ_ne_zero h1 h2
  have hsq : fT f τ (wmap τ ξ) * φ (wmap τ ξ) ^ 2 = wmap τ ξ := hφ.2.2 _ (w_mem_ball h1 h2 hξ)
  have hPi : PiF f τ ξ = (vτ τ : ℂ) * fT f τ (wmap τ ξ) := PiF_eq_fT h1 h2 hξ
  rw [hPi, Lfun_eq hf h1 h2 hφ hξ]
  simp only [Nfun]
  have hre : (vτ τ : ℂ) * fT f τ (wmap τ ξ) * ((1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ)) ^ 2 =
      (vτ τ : ℂ) * (1 + (βτ τ : ℂ) * ξ) ^ 2 * (fT f τ (wmap τ ξ) * φ (wmap τ ξ) ^ 2) := by ring
  rw [hre, hsq, one_add_beta h1 h2 ξ]
  simp only [wmap]
  field_simp

/-! ### Odd and even parts of a power series, and the identity behind Lemma 4.2

For `g` holomorphic on `ball 0 R` with coefficients `p_n = coeff g n`, at `ξ` with `±ξ` in the ball:
`(g(ξ) - g(-ξ))/2 = ∑ p_{2m+1} ξ^{2m+1}`; the derivative has coefficients `(n+1) p_{n+1}`, so
`(g'(ξ) + g'(-ξ))/2 = ∑ (2m+1) p_{2m+1} ξ^{2m}` and `(g'(ξ) - g'(-ξ))/2 = ∑ (2m+2) p_{2m+2} ξ^{2m+1}`.
Collecting terms gives the numerator identity: if `P₂ p₁ = p₂`, then
`(-τ + ξ) g'(ξ) + (τ + ξ) g'(-ξ) - (1 - 2τP₂)(g(ξ) - g(-ξ)) = 2ξ³ Υ(ξ)`, with `Υ` formed with `P₂`. -/

lemma neg_mem_ball_zero {R : ℝ} {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) R) : -ξ ∈ ball (0 : ℂ) R := by
  rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]

private lemma odd_injective : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b hab => by
  simp at hab; omega

private lemma even_injective : Function.Injective (fun m : ℕ => 2 * m) := fun a b hab => by
  simp at hab; omega

/-- The odd part of a power series sum. -/
lemma hasSum_odd_part {p : ℕ → ℂ} {ξ a b : ℂ} (ha : HasSum (fun n => p n * ξ ^ n) a)
    (hb : HasSum (fun n => p n * (-ξ) ^ n) b) :
    HasSum (fun m : ℕ => p (2 * m + 1) * ξ ^ (2 * m + 1)) ((a - b) / 2) := by
  have hs := (ha.sub hb).div_const 2
  have hf : ∀ n ∉ Set.range (fun m : ℕ => 2 * m + 1),
      (fun n => (p n * ξ ^ n - p n * (-ξ) ^ n) / 2) n = 0 := by
    intro n hn
    have hev : Even n := by
      rcases Nat.even_or_odd n with h | ⟨k, hk⟩
      · exact h
      · exact absurd ⟨k, hk.symm⟩ hn
    simp only [hev.neg_pow, sub_self, zero_div]
  have hs2 := (odd_injective.hasSum_iff hf).mpr hs
  convert hs2 using 1
  funext m
  simp only [Function.comp, Odd.neg_pow ⟨m, rfl⟩]
  ring

/-- The even part of a power series sum. -/
lemma hasSum_even_part {p : ℕ → ℂ} {ξ a b : ℂ} (ha : HasSum (fun n => p n * ξ ^ n) a)
    (hb : HasSum (fun n => p n * (-ξ) ^ n) b) :
    HasSum (fun m : ℕ => p (2 * m) * ξ ^ (2 * m)) ((a + b) / 2) := by
  have hs := (ha.add hb).div_const 2
  have hf : ∀ n ∉ Set.range (fun m : ℕ => 2 * m),
      (fun n => (p n * ξ ^ n + p n * (-ξ) ^ n) / 2) n = 0 := by
    intro n hn
    have hod : Odd n := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | h
      · exact absurd ⟨k, by show 2 * k = n; omega⟩ hn
      · exact h
    simp only [hod.neg_pow]
    ring
  have hs2 := (even_injective.hasSum_iff hf).mpr hs
  convert hs2 using 1
  funext m
  simp only [Function.comp, (even_two_mul m).neg_pow]
  ring

/-- The coefficients of the derivative: `coeff g' n = (n + 1) coeff g (n + 1)`. -/
lemma coeff_deriv (g : ℂ → ℂ) (n : ℕ) : coeff (deriv g) n = ((n : ℂ) + 1) * coeff g (n + 1) := by
  simp only [coeff, ← iteratedDeriv_succ']
  have hn : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- `Π_o(ξ) = (g(ξ) - g(-ξ))/(2ξ)`. -/
lemma PiOddSer_eq {g : ℂ → ℂ} {R : ℝ} (hd : DifferentiableOn ℂ g (ball (0 : ℂ) R)) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) R) (hξ0 : ξ ≠ 0) :
    HasSum (fun m : ℕ => coeff g (2 * m + 1) * ξ ^ (2 * m)) ((g ξ - g (-ξ)) / (2 * ξ)) ∧
      PiOddSer (coeff g) ξ = (g ξ - g (-ξ)) / (2 * ξ) := by
  have h := (hasSum_odd_part (hasSum_coeff hd hξ) (hasSum_coeff hd (neg_mem_ball_zero hξ))).div_const ξ
  have h' : HasSum (fun m : ℕ => coeff g (2 * m + 1) * ξ ^ (2 * m)) ((g ξ - g (-ξ)) / (2 * ξ)) := by
    convert h using 1
    · funext m
      rw [pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hξ0]
    · rw [div_div]
  exact ⟨h', h'.tsum_eq⟩

/-- The numerator identity of Lemma 4.2 (see the section comment). -/
lemma numerator_identity {g : ℂ → ℂ} {R : ℝ} (hd : DifferentiableOn ℂ g (ball (0 : ℂ) R)) (τ : ℝ) (P2 : ℂ)
    (h0 : P2 * coeff g 1 = coeff g 2) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) R) (hξ0 : ξ ≠ 0) :
    (-(τ : ℂ) + ξ) * deriv g ξ + ((τ : ℂ) + ξ) * deriv g (-ξ) - (1 - 2 * (τ : ℂ) * P2) * (g ξ - g (-ξ)) =
      2 * ξ ^ 3 * UpsLin τ P2 (coeff g) ξ := by
  have hξ' := neg_mem_ball_zero hξ
  have hdd : DifferentiableOn ℂ (deriv g) (ball (0 : ℂ) R) := hd.deriv isOpen_ball
  have hO := hasSum_odd_part (hasSum_coeff hd hξ) (hasSum_coeff hd hξ')
  have hA := hasSum_even_part (hasSum_coeff hdd hξ) (hasSum_coeff hdd hξ')
  have hB := hasSum_odd_part (hasSum_coeff hdd hξ) (hasSum_coeff hdd hξ')
  set cc : ℕ → ℂ := fun m => ((2 * (m : ℂ) + 2 * (τ : ℂ) * P2) * coeff g (2 * m + 1) -
    2 * (τ : ℂ) * ((m : ℂ) + 1) * coeff g (2 * m + 2)) with hcc
  have hX : HasSum (fun m : ℕ => 2 * ξ ^ (2 * m + 1) * cc m)
      ((-(τ : ℂ) + ξ) * deriv g ξ + ((τ : ℂ) + ξ) * deriv g (-ξ) - (1 - 2 * (τ : ℂ) * P2) * (g ξ - g (-ξ))) := by
    have h := ((hA.mul_left (2 * ξ)).sub (hB.mul_left (2 * (τ : ℂ)))).sub
      (hO.mul_left (2 * (1 - 2 * (τ : ℂ) * P2)))
    convert h using 1
    · funext m
      simp only [hcc, coeff_deriv, show 2 * m + 1 + 1 = 2 * m + 2 by omega]
      push_cast
      ring
    · ring
  have hc0 : cc 0 = 0 := by
    simp only [hcc, Nat.cast_zero, mul_zero, zero_add]
    linear_combination 2 * (τ : ℂ) * h0
  have hU : HasSum (fun j : ℕ => if 1 ≤ j then
      ((2 * (j : ℂ) + 2 * (τ : ℂ) * P2) * coeff g (2 * j + 1) - 2 * (τ : ℂ) * ((j : ℂ) + 1) * coeff g (2 * j + 2)) *
        ξ ^ (2 * j - 2) else 0)
      (((-(τ : ℂ) + ξ) * deriv g ξ + ((τ : ℂ) + ξ) * deriv g (-ξ) -
        (1 - 2 * (τ : ℂ) * P2) * (g ξ - g (-ξ))) / (2 * ξ ^ 3)) := by
    convert hX.div_const (2 * ξ ^ 3) using 1
    funext m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [show ¬ ((1 : ℕ) ≤ 0) by omega, ↓reduceIte]
      rw [hc0]
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [show 1 ≤ k + 1 by omega, ↓reduceIte, show 2 * (k + 1) - 2 = 2 * k by omega]
      simp only [hcc]
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega]
      field_simp
      ring
  rw [show UpsLin τ P2 (coeff g) ξ = _ from hU.tsum_eq]
  field_simp

/-! ### Rows: lem_4_2, sec4_D_diagonal -/

lemma PiF_differentiableOn {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    DifferentiableOn ℂ (PiF f τ) (ball (0 : ℂ) (1 / 4)) :=
  fun _ hξ => (hasDerivAt_PiF hf (ball_quarter_sub h1 h2 hξ)).differentiableAt.differentiableWithinAt

lemma deriv_f_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    deriv f (-(τ : ℂ) + ξ) = deriv f (-(τ : ℂ)) * deriv (PiF f τ) ξ := by
  have hF1 := sec3_deriv_ne_zero_proved f hf _ (neg_tau_mem_ball h1 h2)
  rw [(hasDerivAt_PiF hf (ball_quarter_sub h1 h2 hξ)).deriv]
  field_simp

lemma PiF_sub_ne_zero {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) (hξ0 : ξ ≠ 0) : PiF f τ ξ - PiF f τ (-ξ) ≠ 0 := by
  have hF1 := sec3_deriv_ne_zero_proved f hf _ (neg_tau_mem_ball h1 h2)
  have hb1 := ball_quarter_sub h1 h2 hξ
  have hb2 := ball_quarter_sub h1 h2 (neg_mem_ball_zero hξ)
  intro h0
  simp only [PiF] at h0
  rw [div_sub_div_same, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · have := hf.injOn hb1 hb2 (by linear_combination h0)
    apply hξ0
    linear_combination this / 2
  · exact hF1 h0

/-- `Q_f(-τ + ξ, -τ - ξ)` through `Π`. -/
lemma Q_eq_Pi {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    Q f (-(τ : ℂ) + ξ) (-(τ : ℂ) - ξ) =
      1 + ((-(τ : ℂ) + ξ) * deriv (PiF f τ) ξ + ((τ : ℂ) + ξ) * deriv (PiF f τ) (-ξ)) /
        (PiF f τ ξ - PiF f τ (-ξ)) := by
  have hm : -(τ : ℂ) - ξ = -(τ : ℂ) + -ξ := by ring
  have e1 := deriv_f_eq hf h1 h2 hξ
  have e2 := deriv_f_eq hf h1 h2 (neg_mem_ball_zero hξ)
  have hΔ : PiF f τ ξ - PiF f τ (-ξ) = (f (-(τ : ℂ) + ξ) - f (-(τ : ℂ) + -ξ)) / deriv f (-(τ : ℂ)) := by
    simp only [PiF]
    ring
  simp only [Q]
  rw [hm, e1, e2, hΔ, div_div_eq_mul_div]
  congr 2
  ring

/-- `D = 2 - 2τπ₂`. -/
lemma D_eq_two_sub {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    Dτ τ (cOf f τ) = 2 - 2 * (τ : ℂ) * coeff (PiF f τ) 2 := by
  have hV' : (1 - (τ : ℂ) ^ 2) ≠ 0 := by
    have := vτ_ne_zero h1 h2
    simpa [vτ] using this
  rw [PiF_coeff_two hf h1 h2]
  simp only [Dτ, vτ]
  push_cast
  field_simp
  ring

/-- `y = √(¼ - τ²)` lies in `(0, 1/4)`, and `(iy)² = -y²`. -/
lemma xi_facts {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    xiτ τ ≠ 0 ∧ xiτ τ ∈ ball (0 : ℂ) (1 / 4) ∧ xiτ τ ^ 2 = -(ysq τ : ℂ) := by
  have hys : 0 < ysq τ := by simp only [ysq]; nlinarith
  have hys' : ysq τ < 1 / 16 := by simp only [ysq]; nlinarith
  have hy : 0 < yτ τ := Real.sqrt_pos.mpr hys
  have hy4 : yτ τ < 1 / 4 := (Real.sqrt_lt' (by norm_num)).mpr (by linarith)
  have hsq : yτ τ ^ 2 = ysq τ := Real.sq_sqrt hys.le
  have hn : ‖xiτ τ‖ = yτ τ := by
    simp only [xiτ]
    rw [norm_mul, Complex.norm_I, one_mul, norm_real, Real.norm_eq_abs, abs_of_pos hy]
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have := congrArg norm h0
    rw [hn, norm_zero] at this
    linarith
  · rw [mem_ball_zero_iff, hn]
    exact hy4
  · simp only [xiτ]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hsq]
    ring

theorem lem_4_2_proved (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    (∀ ξ : ℂ, ξ ≠ 0 → ξ ∈ ball (0 : ℂ) (1 / 4) →
      PiOddSer (coeff (PiF f τ)) ξ = (PiF f τ ξ - PiF f τ (-ξ)) / (2 * ξ) ∧
        Q f (-(τ : ℂ) + ξ) (-(τ : ℂ) - ξ) =
          Dτ τ (cOf f τ) + ξ ^ 2 * UpsSer τ (coeff (PiF f τ)) ξ / PiOddSer (coeff (PiF f τ)) ξ) ∧
      Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) = Dτ τ (cOf f τ) - (ysq τ : ℂ) * Tser τ (coeff (PiF f τ)) := by
  have hd := PiF_differentiableOn hf h1 h2
  have hp1 := PiF_coeff_one hf h1 h2
  have hD := D_eq_two_sub hf h1 h2
  have main : ∀ ξ : ℂ, ξ ≠ 0 → ξ ∈ ball (0 : ℂ) (1 / 4) →
      PiOddSer (coeff (PiF f τ)) ξ = (PiF f τ ξ - PiF f τ (-ξ)) / (2 * ξ) ∧
        Q f (-(τ : ℂ) + ξ) (-(τ : ℂ) - ξ) =
          Dτ τ (cOf f τ) + ξ ^ 2 * UpsSer τ (coeff (PiF f τ)) ξ / PiOddSer (coeff (PiF f τ)) ξ := by
    intro ξ hξ0 hξ
    have hO := (PiOddSer_eq hd hξ hξ0).2
    refine ⟨hO, ?_⟩
    have hΔ := PiF_sub_ne_zero hf h1 h2 hξ hξ0
    have hNI := numerator_identity hd τ (coeff (PiF f τ) 2) (by rw [hp1, mul_one]) hξ hξ0
    have hN : (-(τ : ℂ) + ξ) * deriv (PiF f τ) ξ + ((τ : ℂ) + ξ) * deriv (PiF f τ) (-ξ) =
        (1 - 2 * (τ : ℂ) * coeff (PiF f τ) 2) * (PiF f τ ξ - PiF f τ (-ξ)) +
          2 * ξ ^ 3 * UpsLin τ (coeff (PiF f τ) 2) (coeff (PiF f τ)) ξ := by
      rw [← hNI]
      ring
    rw [Q_eq_Pi hf h1 h2 hξ, hO, hD]
    simp only [UpsSer]
    rw [hN]
    field_simp
    ring
  refine ⟨main, ?_⟩
  obtain ⟨hξ0, hξ, hsq⟩ := xi_facts h1 h2
  rw [(main _ hξ0 hξ).2, hsq]
  simp only [Tser]
  ring

/-- `π₂ = f''(-τ)/(2 f'(-τ))`. -/
lemma PiF_coeff_two_direct {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    coeff (PiF f τ) 2 = deriv (deriv f) (-(τ : ℂ)) / (2 * deriv f (-(τ : ℂ))) := by
  have hq : ball (0 : ℂ) (1 / 4) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 (by norm_num)
  have hev : deriv (PiF f τ) =ᶠ[𝓝 (0 : ℂ)] fun ξ => deriv f (-(τ : ℂ) + ξ) / deriv f (-(τ : ℂ)) :=
    Filter.eventually_of_mem hq (fun ξ hξ => (hasDerivAt_PiF hf (ball_quarter_sub h1 h2 hξ)).deriv)
  have hτb := neg_tau_mem_ball h1 h2
  have hf'a : HasDerivAt (deriv f) (deriv (deriv f) (-(τ : ℂ) + 0)) (-(τ : ℂ) + 0) := by
    rw [add_zero]
    exact ((hf.differentiableOn.analyticOnNhd isOpen_ball) _ hτb).deriv.differentiableAt.hasDerivAt
  have hc : HasDerivAt (fun x : ℂ => -(τ : ℂ) + x) 1 0 := (hasDerivAt_id' 0).const_add _
  have h' : HasDerivAt (fun ξ => deriv f (-(τ : ℂ) + ξ) / deriv f (-(τ : ℂ)))
      (deriv (deriv f) (-(τ : ℂ) + 0) * 1 / deriv f (-(τ : ℂ))) 0 :=
    (hf'a.comp (0 : ℂ) hc).div_const (deriv f (-(τ : ℂ)))
  rw [coeff_two_eq, hev.deriv_eq, h'.deriv, add_zero, mul_one, div_div, mul_comm (deriv f (-(τ : ℂ))) 2]

theorem sec4_D_diagonal_proved (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    Dτ τ (cOf f τ) = 2 + -(τ : ℂ) * deriv (deriv f) (-(τ : ℂ)) / deriv f (-(τ : ℂ)) ∧
      Dτ τ (cOf f τ) = 2 - 2 * (τ : ℂ) * coeff (PiF f τ) 2 ∧
      Tendsto (fun w => Q f (-(τ : ℂ)) w) (𝓝[≠] (-(τ : ℂ))) (𝓝 (Dτ τ (cOf f τ))) := by
  have hD := D_eq_two_sub hf h1 h2
  have hF1 := sec3_deriv_ne_zero_proved f hf _ (neg_tau_mem_ball h1 h2)
  have hD1 : Dτ τ (cOf f τ) = 2 + -(τ : ℂ) * deriv (deriv f) (-(τ : ℂ)) / deriv f (-(τ : ℂ)) := by
    rw [hD, PiF_coeff_two_direct hf h1 h2]
    field_simp
    ring
  refine ⟨hD1, hD, ?_⟩
  have hτb := neg_tau_mem_ball h1 h2
  have hfa : HasDerivAt f (deriv f (-(τ : ℂ))) (-(τ : ℂ)) :=
    (hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hτb)).hasDerivAt
  have hf'a : HasDerivAt (deriv f) (deriv (deriv f) (-(τ : ℂ))) (-(τ : ℂ)) :=
    ((hf.differentiableOn.analyticOnNhd isOpen_ball) _ hτb).deriv.differentiableAt.hasDerivAt
  have hha : HasDerivAt (fun w => w * deriv f w)
      (1 * deriv f (-(τ : ℂ)) + -(τ : ℂ) * deriv (deriv f) (-(τ : ℂ))) (-(τ : ℂ)) :=
    (hasDerivAt_id' _).mul hf'a
  have hlim := ((hasDerivAt_iff_tendsto_slope.mp hha).div (hasDerivAt_iff_tendsto_slope.mp hfa) hF1).const_add 1
  have hval : 1 + (1 * deriv f (-(τ : ℂ)) + -(τ : ℂ) * deriv (deriv f) (-(τ : ℂ))) / deriv f (-(τ : ℂ)) =
      Dτ τ (cOf f τ) := by
    rw [hD1]
    field_simp
    ring
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : w - -(τ : ℂ) ≠ 0 := sub_ne_zero.mpr hw
  simp only [Pi.div_apply, Q, slope_def_field]
  rw [div_div_div_cancel_right₀ hw', ← neg_div_neg_eq]
  congr 2 <;> ring

/-! ### Coefficients of `g(ξ) = ξ H(ξ)` -/

/-- For `g = ξ H(ξ)` near `0`: `coeff g 0 = 0`, `coeff g 1 = H(0)`, `coeff g 2 = H'(0)`. -/
lemma coeff_of_mul_id {g H : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hH : DifferentiableOn ℂ H (ball (0 : ℂ) r))
    (hg : ∀ ξ ∈ ball (0 : ℂ) r, g ξ = ξ * H ξ) :
    coeff g 0 = 0 ∧ coeff g 1 = H 0 ∧ coeff g 2 = deriv H 0 := by
  have hb : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hr
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hev : g =ᶠ[𝓝 (0 : ℂ)] fun ξ => ξ * H ξ := Filter.eventually_of_mem hb hg
  have hHd : ∀ ξ ∈ ball (0 : ℂ) r, HasDerivAt H (deriv H ξ) ξ :=
    fun ξ hξ => (hH.differentiableAt (isOpen_ball.mem_nhds hξ)).hasDerivAt
  have hd1 : ∀ ξ ∈ ball (0 : ℂ) r, HasDerivAt (fun ξ => ξ * H ξ) (1 * H ξ + ξ * deriv H ξ) ξ :=
    fun ξ hξ => (hasDerivAt_id' ξ).mul (hHd ξ hξ)
  have hev2 : deriv g =ᶠ[𝓝 (0 : ℂ)] fun ξ => 1 * H ξ + ξ * deriv H ξ :=
    hev.deriv.trans (Filter.eventually_of_mem hb (fun ξ hξ => (hd1 ξ hξ).deriv))
  have hH'd : HasDerivAt (deriv H) (deriv (deriv H) 0) 0 :=
    ((hH.analyticOnNhd isOpen_ball) 0 h0).deriv.differentiableAt.hasDerivAt
  have hd2 : HasDerivAt (fun ξ => 1 * H ξ + ξ * deriv H ξ)
      (1 * deriv H 0 + (1 * deriv H 0 + 0 * deriv (deriv H) 0)) 0 :=
    ((hHd 0 h0).const_mul 1).add ((hasDerivAt_id' 0).mul hH'd)
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_zero_eq, hg 0 h0, zero_mul]
  · rw [coeff_one_eq, hev.deriv_eq, (hd1 0 h0).deriv]
    ring
  · rw [coeff_two_eq, hev2.deriv_eq, hd2.deriv]
    ring

/-! ### The comparison function `Π̂ = N/(1 - νξ)²` and the functions `Π_j` -/

lemma beta_bounds {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : 0 < βτ τ ∧ βτ τ ≤ 2 / 3 := by
  have hv := vτ_ge h1 h2
  have hv1 : vτ τ ≤ 1 := by simp only [vτ]; nlinarith
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  rw [βτ, div_le_iff₀ (by linarith)]
  linarith

/-- On `|ξ| < 1/(2 + |ν|)`: `1 - νξ ≠ 0` and `1 + βξ ≠ 0`. -/
lemma small_ball_facts {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / (2 + ‖nuτ τ c‖))) :
    1 - nuτ τ c * ξ ≠ 0 ∧ 1 + (βτ τ : ℂ) * ξ ≠ 0 := by
  have hξ' := mem_ball_zero_iff.mp hξ
  have hpos : 0 < 2 + ‖nuτ τ c‖ := by positivity
  have hνξ : ‖nuτ τ c‖ * ‖ξ‖ < 1 := by
    rw [lt_div_iff₀ hpos] at hξ'
    nlinarith [norm_nonneg ξ, norm_nonneg (nuτ τ c)]
  have hξ2 : ‖ξ‖ < 1 / 2 := by
    calc ‖ξ‖ < 1 / (2 + ‖nuτ τ c‖) := hξ'
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith [norm_nonneg (nuτ τ c)])
  obtain ⟨hb0, hb1⟩ := beta_bounds h1 h2
  constructor
  · intro h0
    have h1' : nuτ τ c * ξ = 1 := by linear_combination -h0
    have := congrArg norm h1'
    rw [norm_mul, norm_one] at this
    linarith
  · intro h0
    have h1' : (βτ τ : ℂ) * ξ = -1 := by linear_combination h0
    have := congrArg norm h1'
    rw [norm_mul, norm_neg, norm_one, norm_real, Real.norm_eq_abs, abs_of_pos hb0] at this
    nlinarith [norm_nonneg ξ]

/-- `Π̂(ξ) = ξ H(ξ)` with `H = (1 + βξ)/(1 - νξ)²`: its coefficients `π̂₀ = 0`, `π̂₁ = 1`, `π̂₂ = β + 2ν`. -/
lemma Pihat_low_coeffs {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) :
    coeff (Pihat τ c) 0 = 0 ∧ coeff (Pihat τ c) 1 = 1 ∧
      coeff (Pihat τ c) 2 = (2 * c - (τ : ℂ)) / (vτ τ : ℂ) := by
  set r : ℝ := 1 / (2 + ‖nuτ τ c‖) with hr
  have hr0 : 0 < r := by positivity
  have hV0 := vτ_ne_zero h1 h2
  have hHd : ∀ ξ ∈ ball (0 : ℂ) r, HasDerivAt (fun x : ℂ => (1 + (βτ τ : ℂ) * x) / (1 - nuτ τ c * x) ^ 2)
      (((βτ τ : ℂ) * (1 - nuτ τ c * ξ) ^ 2 -
        (1 + (βτ τ : ℂ) * ξ) * (2 * (1 - nuτ τ c * ξ) * -nuτ τ c)) / ((1 - nuτ τ c * ξ) ^ 2) ^ 2) ξ := by
    intro ξ hξ
    have hne := (small_ball_facts h1 h2 c hξ).1
    have hN : HasDerivAt (fun x : ℂ => 1 + (βτ τ : ℂ) * x) (βτ τ : ℂ) ξ := by
      simpa using ((hasDerivAt_id' ξ).const_mul (βτ τ : ℂ)).const_add 1
    have hD : HasDerivAt (fun x : ℂ => (1 - nuτ τ c * x) ^ 2) (2 * (1 - nuτ τ c * ξ) * -nuτ τ c) ξ := by
      have h := (((hasDerivAt_id' ξ).const_mul (nuτ τ c)).const_sub 1).pow 2
      convert h using 1
      simp only [Nat.cast_ofNat, pow_one, mul_one]
      ring
    have h := hN.div hD (pow_ne_zero 2 hne)
    convert h using 1
  have hHdiff : DifferentiableOn ℂ (fun x : ℂ => (1 + (βτ τ : ℂ) * x) / (1 - nuτ τ c * x) ^ 2) (ball (0 : ℂ) r) :=
    fun ξ hξ => (hHd ξ hξ).differentiableAt.differentiableWithinAt
  obtain ⟨e0, e1, e2⟩ := coeff_of_mul_id (g := Pihat τ c) hr0 hHdiff (fun ξ _ => by simp only [Pihat]; ring)
  refine ⟨e0, ?_, ?_⟩
  · rw [e1]; simp
  · rw [e2, (hHd 0 (mem_ball_self hr0)).deriv]
    simp only [mul_zero, sub_zero, add_zero, one_pow, mul_one, one_mul, div_one]
    simp only [nuτ, βτ]
    push_cast
    field_simp
    ring

/-- `Π_j(ξ) = ξ · ξʲ K(ξ)`: for `j ≥ 2` its coefficients of order `0, 1, 2` vanish. -/
lemma PiJ_low_coeffs {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) {j : ℕ} (hj : 2 ≤ j) :
    coeff (PiJ τ c j) 0 = 0 ∧ coeff (PiJ τ c j) 1 = 0 ∧ coeff (PiJ τ c j) 2 = 0 := by
  set r : ℝ := 1 / (2 + ‖nuτ τ c‖) with hr
  have hr0 : 0 < r := by positivity
  set K : ℂ → ℂ := fun x => -2 * (1 + (βτ τ : ℂ) * x) ^ ((2 : ℤ) - j) / ((vτ τ : ℂ) ^ j * (1 - nuτ τ c * x) ^ 3)
    with hK
  have hV0 := vτ_ne_zero h1 h2
  have hKd : DifferentiableOn ℂ K (ball (0 : ℂ) r) := by
    intro ξ hξ
    obtain ⟨hne1, hne2⟩ := small_ball_facts h1 h2 c hξ
    have hz : DifferentiableAt ℂ (fun x : ℂ => (1 + (βτ τ : ℂ) * x) ^ ((2 : ℤ) - j)) ξ :=
      ((differentiableAt_id.const_mul _).const_add _).zpow (Or.inl hne2)
    have hden : DifferentiableAt ℂ (fun x : ℂ => (vτ τ : ℂ) ^ j * (1 - nuτ τ c * x) ^ 3) ξ :=
      (differentiableAt_const _).mul (((differentiableAt_id.const_mul _).const_sub _).pow 3)
    exact ((hz.const_mul (-2)).div hden (mul_ne_zero (pow_ne_zero _ hV0) (pow_ne_zero _ hne1))).differentiableWithinAt
  have hHd : DifferentiableOn ℂ (fun x : ℂ => x ^ j * K x) (ball (0 : ℂ) r) :=
    (differentiableOn_pow j).mul hKd
  obtain ⟨e0, e1, e2⟩ := coeff_of_mul_id (g := PiJ τ c j) hr0 hHd (fun ξ _ => by
    simp only [PiJ, hK]
    rw [pow_succ]
    ring)
  refine ⟨e0, ?_, ?_⟩
  · rw [e1]
    simp [zero_pow (by omega : j ≠ 0)]
  · rw [e2]
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr0
    have hKa : HasDerivAt K (deriv K 0) 0 := (hKd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have h : HasDerivAt (fun x : ℂ => x ^ j * K x) (↑j * 0 ^ (j - 1) * K 0 + 0 ^ j * deriv K 0) 0 :=
      (hasDerivAt_pow j (0 : ℂ)).mul hKa
    rw [h.deriv]
    simp [zero_pow (by omega : j - 1 ≠ 0), zero_pow (by omega : j ≠ 0)]

/-- `Π̂` is holomorphic on `|ξ| < 1/2` for `|c| ≤ 1`, with derivative `((1 + 2βξ)(1 - νξ) + 2νξ(1 + βξ))/(1 - νξ)³`. -/
lemma nu_bound {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) : ‖nuτ τ c‖ ≤ 2 := by
  obtain ⟨-, hb, h12, -⟩ := sec4_hat_bounds_proved τ h1 h2.le
  exact (hb c hc).1.trans h12

lemma one_sub_nu_ne {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) {ξ : ℂ}
    (hξ : ξ ∈ ball (0 : ℂ) (1 / 2)) : 1 - nuτ τ c * ξ ≠ 0 := by
  have hν := nu_bound h1 h2 hc
  have hξ' := mem_ball_zero_iff.mp hξ
  intro h0
  have h1' : nuτ τ c * ξ = 1 := by linear_combination -h0
  have := congrArg norm h1'
  rw [norm_mul, norm_one] at this
  nlinarith [norm_nonneg (nuτ τ c), norm_nonneg ξ]

lemma hasDerivAt_Pihat {τ : ℝ} (c : ℂ) {ξ : ℂ} (hne : 1 - nuτ τ c * ξ ≠ 0) :
    HasDerivAt (Pihat τ c) (((1 + 2 * (βτ τ : ℂ) * ξ) * (1 - nuτ τ c * ξ) +
      2 * nuτ τ c * ξ * (1 + (βτ τ : ℂ) * ξ)) / (1 - nuτ τ c * ξ) ^ 3) ξ := by
  have hN : HasDerivAt (fun x : ℂ => x * (1 + (βτ τ : ℂ) * x)) (1 * (1 + (βτ τ : ℂ) * ξ) + ξ * (βτ τ : ℂ)) ξ := by
    have h := (hasDerivAt_id' ξ).mul (((hasDerivAt_id' ξ).const_mul (βτ τ : ℂ)).const_add 1)
    convert h using 1
    ring
  have hD : HasDerivAt (fun x : ℂ => (1 - nuτ τ c * x) ^ 2) (2 * (1 - nuτ τ c * ξ) * -nuτ τ c) ξ := by
    have h := (((hasDerivAt_id' ξ).const_mul (nuτ τ c)).const_sub 1).pow 2
    convert h using 1
    simp only [Nat.cast_ofNat, pow_one, mul_one]
    ring
  have h := hN.div hD (pow_ne_zero 2 hne)
  convert h using 1 <;> first | rfl | (field_simp; ring)

lemma Pihat_differentiableOn {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    DifferentiableOn ℂ (Pihat τ c) (ball (0 : ℂ) (1 / 2)) :=
  fun _ hξ => (hasDerivAt_Pihat c (one_sub_nu_ne h1 h2 hc hξ)).differentiableAt.differentiableWithinAt

lemma xi_mem_half {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : xiτ τ ∈ ball (0 : ℂ) (1 / 2) := by
  have h := (xi_facts h1 h2).2.1
  rw [mem_ball_zero_iff] at h ⊢
  linarith

/-- `Π̂(ξ) - Π̂(-ξ) = 2ξ Π̂_o(iy)` at `ξ = iy` (the closed form of (sec4:hat)). -/
lemma Pihat_sub_eq {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ) = 2 * xiτ τ * PihatO τ c := by
  obtain ⟨hξ0, hξ, hsq⟩ := xi_facts h1 h2
  have hm1 := one_sub_nu_ne h1 h2 hc (xi_mem_half h1 h2)
  have hm2 := one_sub_nu_ne h1 h2 hc (neg_mem_ball_zero (xi_mem_half h1 h2))
  obtain ⟨-, -, -, -, -, R, hR1, -, -, -, hden⟩ := sec4_hat_bounds_proved τ h1 h2.le
  have hc' : c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  have hA : 1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 := left_ne_zero_of_mul (hden c hc').1
  simp only [PihatO, Pihat]
  rw [div_sub_div _ _ (pow_ne_zero 2 hm1) (pow_ne_zero 2 hm2), mul_div_assoc',
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hm1) (pow_ne_zero 2 hm2)) (pow_ne_zero 2 hA)]
  have hy : (ysq τ : ℂ) = -xiτ τ ^ 2 := by rw [hsq]; ring
  rw [hy]
  ring

/-- `D = 2 - 2τ(β + 2ν)`. -/
lemma Dτ_eq_beta_nu {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) :
    Dτ τ c = 2 - 2 * (τ : ℂ) * ((βτ τ : ℂ) + 2 * nuτ τ c) := by
  have hV0 := vτ_ne_zero h1 h2
  have hV' : (1 - (τ : ℂ) ^ 2) ≠ 0 := by simpa [vτ] using hV0
  simp only [Dτ, nuτ, βτ, vτ]
  push_cast
  field_simp
  ring

/-- `D = 2 - 2τπ̂₂` with `π̂₂ = (2c - τ)/v`. -/
lemma Dτ_eq_p2 {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) :
    Dτ τ c = 2 - 2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) := by
  have hV0 := vτ_ne_zero h1 h2
  have hV' : (1 - (τ : ℂ) ^ 2) ≠ 0 := by simpa [vτ] using hV0
  simp only [Dτ, vτ]
  push_cast
  field_simp
  ring

/-- `Q̂ = D - y² T̂` (the closed forms of (sec4:hat)). -/
lemma Qhat_eq {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Dτ τ c - (ysq τ : ℂ) * That τ c = Qhat τ c := by
  obtain ⟨-, -, -, -, -, R, hR1, -, -, -, hden⟩ := sec4_hat_bounds_proved τ h1 h2.le
  have hc' : c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  obtain ⟨hQd, hTd⟩ := hden c hc'
  have hV0 := vτ_ne_zero h1 h2
  have hV' : (1 - (τ : ℂ) ^ 2) ≠ 0 := by simpa [vτ] using hV0
  simp only [That, Qhat]
  rw [Dτ_eq_beta_nu h1 h2 c]
  generalize hTD : 1 - 2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) -
    (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ) ^ 2 = TD at hTd ⊢
  generalize hQD : (1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) *
    (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)) = QD at hQd ⊢
  rw [eq_div_iff hQd]
  field_simp
  subst hTD hQD
  simp only [βτ, vτ]
  push_cast
  field_simp
  ring

/-- `Q̂ = 1 + ((-τ + ξ)Π̂'(ξ) + (τ + ξ)Π̂'(-ξ))/(Π̂(ξ) - Π̂(-ξ))` at `ξ = iy`: the formula for `Q` applied to `Π̂`. -/
lemma Pihat_Q_series {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    1 + ((-(τ : ℂ) + xiτ τ) * deriv (Pihat τ c) (xiτ τ) + ((τ : ℂ) + xiτ τ) * deriv (Pihat τ c) (-xiτ τ)) /
      (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ)) = Qhat τ c := by
  obtain ⟨hξ0, hξ, hsq⟩ := xi_facts h1 h2
  have hxh := xi_mem_half h1 h2
  have hm1 := one_sub_nu_ne h1 h2 hc hxh
  have hm2 := one_sub_nu_ne h1 h2 hc (neg_mem_ball_zero hxh)
  obtain ⟨-, -, -, -, -, R, hR1, -, -, -, hden⟩ := sec4_hat_bounds_proved τ h1 h2.le
  have hc' : c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  obtain ⟨hQd, -⟩ := hden c hc'
  have hA : 1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 := left_ne_zero_of_mul hQd
  have hB : 1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ) ≠ 0 := right_ne_zero_of_mul hQd
  rw [(hasDerivAt_Pihat c hm1).deriv, (hasDerivAt_Pihat c hm2).deriv, Pihat_sub_eq h1 h2 hc]
  simp only [PihatO, Qhat]
  rw [Dτ_eq_beta_nu h1 h2 c]
  generalize nuτ τ c = ν at *
  generalize (βτ τ : ℂ) = β at *
  generalize (ysq τ : ℂ) = y2 at *
  generalize xiτ τ = ξ at *
  generalize (τ : ℂ) = t at *
  generalize hAd : 1 + ν ^ 2 * y2 = A at *
  generalize hBd : 1 - ν * (ν + 2 * β) * y2 = B at *
  generalize hm1d : 1 - ν * ξ = m1 at *
  generalize hm2d : 1 - ν * -ξ = m2 at *
  field_simp
  subst hAd hBd hm1d hm2d
  have hy2 : y2 = -ξ ^ 2 := by linear_combination hsq
  subst hy2
  ring

/-- `T̂ = (D - Q̂)/y²` from the numerator identity, the `Q`-formula for `Π̂` and `Q̂ = D - y²T̂` (pure algebra). -/
private lemma T_from_Q {U Nh Δ Qh Th PO D p2 y2 ξ t : ℂ} (hξ : ξ ≠ 0) (hPO : PO ≠ 0) (hy2 : y2 ≠ 0)
    (hsq : ξ ^ 2 = -y2) (hΔ : Δ = 2 * ξ * PO) (hNI : Nh - (1 - 2 * t * p2) * Δ = 2 * ξ ^ 3 * U)
    (hQs : 1 + Nh / Δ = Qh) (hQeq : D - y2 * Th = Qh) (hDp : D = 2 - 2 * t * p2) : U / PO = Th := by
  subst hΔ hDp
  have hΔ0 : 2 * ξ * PO ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hξ) hPO
  have hN : Nh = (Qh - 1) * (2 * ξ * PO) := by
    rw [← hQs, add_sub_cancel_left, div_mul_cancel₀ _ hΔ0]
  rw [hN] at hNI
  have h3 : ξ ^ 2 * U = PO * (Qh - 2 + 2 * t * p2) :=
    mul_left_cancel₀ (mul_ne_zero two_ne_zero hξ) (by linear_combination -hNI)
  rw [div_eq_iff hPO]
  exact mul_left_cancel₀ hy2 (by linear_combination U * hsq - h3 + PO * hQeq)

theorem sec4_hat_closed_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    coeff (Pihat τ c) 1 = 1 ∧ coeff (Pihat τ c) 2 = (2 * c - (τ : ℂ)) / (vτ τ : ℂ) ∧
      PiOddSer (coeff (Pihat τ c)) (xiτ τ) = PihatO τ c ∧
      Tser τ (coeff (Pihat τ c)) = That τ c ∧
      Dτ τ c - (ysq τ : ℂ) * That τ c = Qhat τ c := by
  obtain ⟨-, hp1, hp2⟩ := Pihat_low_coeffs h1 h2 c
  obtain ⟨hξ0, hξ, hsq⟩ := xi_facts h1 h2
  have hd := Pihat_differentiableOn h1 h2 hc
  have hxh := xi_mem_half h1 h2
  have hO : PiOddSer (coeff (Pihat τ c)) (xiτ τ) = PihatO τ c := by
    rw [(PiOddSer_eq hd hxh hξ0).2, Pihat_sub_eq h1 h2 hc]
    field_simp
  refine ⟨hp1, hp2, hO, ?_, Qhat_eq h1 h2 hc⟩
  obtain ⟨-, -, -, -, -, R, hR1, -, -, -, hden⟩ := sec4_hat_bounds_proved τ h1 h2.le
  have hc' : c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  obtain ⟨hQd, -⟩ := hden c hc'
  have hB : 1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ) ≠ 0 := right_ne_zero_of_mul hQd
  have hA : 1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 := left_ne_zero_of_mul hQd
  have hPO : PihatO τ c ≠ 0 := by
    simp only [PihatO]
    exact div_ne_zero hB (pow_ne_zero 2 hA)
  have hys : (ysq τ : ℂ) ≠ 0 := by
    intro h0
    rw [h0, neg_zero] at hsq
    exact hξ0 ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have hNI := numerator_identity hd τ (coeff (Pihat τ c) 2) (by rw [hp1, mul_one]) hxh hξ0
  rw [hp2] at hNI
  simp only [Tser, UpsSer]
  rw [hO, hp2]
  exact T_from_Q hξ0 hPO hys hsq (Pihat_sub_eq h1 h2 hc) hNI (Pihat_Q_series h1 h2 hc) (Qhat_eq h1 h2 hc)
    (Dτ_eq_p2 h1 h2 c)

/-! ### Rows: sec4_low_coeffs, sec4_diff, sec4_majorant_split, sec4_Tj_closed -/

theorem sec4_low_coeffs_proved (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    (∀ n : ℕ, n ≤ 2 → coeff (PiF f τ) n = coeff (Pihat τ (cOf f τ)) n) ∧
      ∀ c : ℂ, ∀ j : ℕ, 2 ≤ j → ∀ n : ℕ, n ≤ 2 → coeff (PiJ τ c j) n = 0 := by
  refine ⟨fun n hn => ?_, fun c j hj n hn => ?_⟩
  · obtain ⟨e0, e1, e2⟩ := Pihat_low_coeffs h1 h2 (cOf f τ)
    interval_cases n
    · rw [e0, coeff_zero_eq]
      simp [PiF]
    · rw [e1, PiF_coeff_one hf h1 h2]
    · rw [e2, PiF_coeff_two hf h1 h2]
  · obtain ⟨e0, e1, e2⟩ := PiJ_low_coeffs h1 h2 c hj
    interval_cases n
    · exact e0
    · exact e1
    · exact e2

/-- `|c| ≤ 1` from de Branges' theorem for `n = 2`. -/
lemma cOf_norm_le (hDB : FactDeBranges) {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    ‖cOf f τ‖ ≤ 1 := by
  have h := hDB (fT f τ) (fT_mem_S hf h1 h2) 2 le_rfl
  rw [cOf, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_one (by norm_num)]
  exact_mod_cast h

theorem sec4_diff_proved (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) :
    Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) - Qhat τ (cOf f τ) =
      -(ysq τ : ℂ) * (Tser τ (coeff (PiF f τ)) - That τ (cOf f τ)) := by
  rw [(lem_4_2_proved f hf τ h1 h2).2, ← Qhat_eq h1 h2 (cOf_norm_le hDB hf h1 h2)]
  ring

theorem sec4_majorant_split_proved (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    (Qhat τ (cOf f τ)).re - ysq τ * ‖Tdot τ (cOf f τ) φ‖ -
        ysq τ * ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
      (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re := by
  have hd := sec4_diff_proved hDB f hf τ h1 h2
  have hys : 0 ≤ ysq τ := by simp only [ysq]; nlinarith
  have hQ : Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) = Qhat τ (cOf f τ) -
      (ysq τ : ℂ) * Tdot τ (cOf f τ) φ -
        (ysq τ : ℂ) * (Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ) := by
    linear_combination hd
  rw [hQ, Complex.sub_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have e1 := Complex.re_le_norm (Tdot τ (cOf f τ) φ)
  have e2 := Complex.re_le_norm (Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ)
  nlinarith [mul_le_mul_of_nonneg_left e1 hys, mul_le_mul_of_nonneg_left e2 hys]

lemma PiJ_differentiableOn {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) (j : ℕ) :
    DifferentiableOn ℂ (PiJ τ c j) (ball (0 : ℂ) (1 / 2)) := by
  intro ξ hξ
  have hne1 := one_sub_nu_ne h1 h2 hc hξ
  have hne2 : 1 + (βτ τ : ℂ) * ξ ≠ 0 := by
    obtain ⟨hb0, hb1⟩ := beta_bounds h1 h2
    have hξ' := mem_ball_zero_iff.mp hξ
    intro h0
    have h1' : (βτ τ : ℂ) * ξ = -1 := by linear_combination h0
    have := congrArg norm h1'
    rw [norm_mul, norm_neg, norm_one, norm_real, Real.norm_eq_abs, abs_of_pos hb0] at this
    nlinarith [norm_nonneg ξ]
  have hV0 := vτ_ne_zero h1 h2
  have hz : DifferentiableAt ℂ (fun x : ℂ => (1 + (βτ τ : ℂ) * x) ^ ((2 : ℤ) - j)) ξ :=
    ((differentiableAt_id.const_mul _).const_add _).zpow (Or.inl hne2)
  have hnum : DifferentiableAt ℂ (fun x : ℂ => -2 * x ^ (j + 1) * (1 + (βτ τ : ℂ) * x) ^ ((2 : ℤ) - j)) ξ :=
    ((differentiableAt_pow (j + 1)).const_mul (-2)).mul hz
  have hden : DifferentiableAt ℂ (fun x : ℂ => (vτ τ : ℂ) ^ j * (1 - nuτ τ c * x) ^ 3) ξ :=
    (differentiableAt_const _).mul (((differentiableAt_id.const_mul _).const_sub _).pow 3)
  exact (hnum.div hden (mul_ne_zero (pow_ne_zero _ hV0) (pow_ne_zero _ hne1))).differentiableWithinAt

theorem sec4_Tj_closed_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (j : ℕ)
    (hj : 2 ≤ j) :
    (UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiJ τ c j)) (xiτ τ) -
        That τ c * PiOddSer (coeff (PiJ τ c j)) (xiτ τ)) / PihatO τ c = TJ τ c j := by
  obtain ⟨hξ0, hξ, hsq⟩ := xi_facts h1 h2
  have hxh := xi_mem_half h1 h2
  have hd := PiJ_differentiableOn h1 h2 hc j
  obtain ⟨-, e1, e2⟩ := PiJ_low_coeffs h1 h2 c hj
  have hNI := numerator_identity hd τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (by rw [e1, e2, mul_zero]) hxh hξ0
  have hO := (PiOddSer_eq hd hxh hξ0).2
  obtain ⟨-, -, -, -, -, R, hR1, -, -, -, hden⟩ := sec4_hat_bounds_proved τ h1 h2.le
  have hc' : c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  obtain ⟨hQd, -⟩ := hden c hc'
  have hB : 1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ) ≠ 0 := right_ne_zero_of_mul hQd
  have hA : 1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 := left_ne_zero_of_mul hQd
  have hPO : PihatO τ c ≠ 0 := by
    simp only [PihatO]
    exact div_ne_zero hB (pow_ne_zero 2 hA)
  have hys : (ysq τ : ℂ) ≠ 0 := by
    intro h0
    rw [h0, neg_zero] at hsq
    exact hξ0 (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  have hV0 := vτ_ne_zero h1 h2
  have hD : Dτ τ c = 2 - 2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) := by
    have hV' : (1 - (τ : ℂ) ^ 2) ≠ 0 := by simpa [vτ] using hV0
    simp only [Dτ, vτ]
    push_cast
    field_simp
    ring
  have hN : (-(τ : ℂ) + xiτ τ) * deriv (PiJ τ c j) (xiτ τ) + ((τ : ℂ) + xiτ τ) * deriv (PiJ τ c j) (-xiτ τ) =
      (1 - 2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ))) * (PiJ τ c j (xiτ τ) - PiJ τ c j (-xiτ τ)) +
        2 * xiτ τ ^ 3 * UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiJ τ c j)) (xiτ τ) := by
    rw [← hNI]
    ring
  have hΔ : PiJ τ c j (xiτ τ) - PiJ τ c j (-xiτ τ) = 2 * xiτ τ * PiOddSer (coeff (PiJ τ c j)) (xiτ τ) := by
    rw [hO]
    field_simp
  simp only [TJ]
  rw [hN, hΔ, Pihat_sub_eq h1 h2 hc, ← Qhat_eq h1 h2 hc, hD]
  have hy : (ysq τ : ℂ) = -xiτ τ ^ 2 := by rw [hsq]; ring
  rw [hy]
  field_simp
  ring

/-! ### Row: lem_4_5_iii, from Lemma 4.5 (i), (ii) and the area bound

`|Ṫ| = |∑_{j ≥ 2} b_{2j-1} T_j| ≤ (∑ (2j - 1)|b_{2j-1}|²)^{1/2} (∑ |T_j|²/(2j - 1))^{1/2} ≤ √η √(M + 130e)`, by the
weighted Cauchy–Schwarz inequality in the form `xy ≤ (s x² + y²/s)/2` with the best `s`. -/

private lemma amgm {s x y : ℝ} (hs : 0 < s) : x * y ≤ (s * x ^ 2 + y ^ 2 / s) / 2 := by
  have h : 0 ≤ (s * x - y) ^ 2 / s := div_nonneg (sq_nonneg _) hs.le
  have e : (s * x - y) ^ 2 / s = s * x ^ 2 + y ^ 2 / s - 2 * (x * y) := by
    field_simp
    ring
  linarith

/-- The term bound: `|b T| ≤ (s (2j-1)|b|² + |T|²/((2j-1) s))/2`. -/
private lemma term_bound {s : ℝ} (hs : 0 < s) (b T : ℂ) (j : ℕ) :
    ‖(if 2 ≤ j then b * T else 0)‖ ≤
      (s * (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖b‖ ^ 2 else 0) +
        (if 2 ≤ j then ‖T‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) / s) / 2 := by
  split_ifs with hj
  · have hW : (0 : ℝ) < 2 * (j : ℝ) - 1 := by
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have h := amgm (mul_pos hs hW) (x := ‖b‖) (y := ‖T‖)
    rw [norm_mul]
    calc ‖b‖ * ‖T‖ ≤ (s * (2 * (j : ℝ) - 1) * ‖b‖ ^ 2 + ‖T‖ ^ 2 / (s * (2 * (j : ℝ) - 1))) / 2 := h
      _ = _ := by field_simp
  · simp

theorem lem_4_5_iii_proved_from
    (hI : ∀ (τ : ℝ), 9 / 20 ≤ τ → τ < 1 / 2 → ∀ (c : ℂ), ‖c‖ ≤ 1 →
      ∑ j ∈ Finset.Icc 2 5, ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) ≤ 20 + 130 * edef c)
    (hII : ∀ (τ : ℝ), 9 / 20 ≤ τ → τ < 1 / 2 → yτ τ ≤ y0 → ∀ (c : ℂ), ‖c‖ ≤ 1 → ∀ (νp : ℝ),
      ‖nuτ τ c‖ ≤ νp → νp ≤ 2 →
      Summable (fun j : ℕ => if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) ∧
        Real.sqrt (∑' j : ℕ, if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) ≤ N6Of νp)
    (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (νp : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp)
    (hνp : νp ≤ 2) :
    ‖Tdot τ (cOf f τ) φ‖ ≤
      Real.sqrt (etadef (cOf f τ)) * Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)) := by
  obtain ⟨hsA, hA1, hAη⟩ := sec4_area_proved hArea f hf τ h1 h2 φ hφ
  -- the two weight sequences
  have hw0 : ∀ j : ℕ, 0 ≤ (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) := by
    intro j
    split_ifs with hj
    · have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      exact mul_nonneg (by linarith) (by positivity)
    · exact le_refl 0
  have hA0 : 0 ≤ ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) := tsum_nonneg hw0
  have hc : ‖cOf f τ‖ ≤ 1 := by nlinarith [norm_nonneg (cOf f τ)]
  have he0 : 0 ≤ edef (cOf f τ) := by
    have := Complex.re_le_norm (cOf f τ)
    simp only [edef]
    linarith
  obtain ⟨hs6, hN6⟩ := hII τ h1 h2 hy0 _ hc νp hν hνp
  have h5 := hI τ h1 h2 _ hc
  have hsplit : (fun j : ℕ => if 2 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) =
      fun j => (if j ∈ Finset.Icc 2 5 then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) + (if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) := by
    funext j
    by_cases hb : 6 ≤ j
    · have ha : 2 ≤ j := by omega
      have hc5 : j ∉ Finset.Icc 2 5 := by simp only [Finset.mem_Icc]; omega
      simp [ha, hb, hc5]
    · by_cases ha : 2 ≤ j
      · have hc5 : j ∈ Finset.Icc 2 5 := by simp only [Finset.mem_Icc]; omega
        simp [ha, hb, hc5]
      · have hc5 : j ∉ Finset.Icc 2 5 := by simp only [Finset.mem_Icc]; omega
        simp [ha, hb, hc5]
  have h5s : HasSum (fun j : ℕ => if j ∈ Finset.Icc 2 5 then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) (∑ j ∈ Finset.Icc 2 5, (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1))) := by
    have h : HasSum (fun j : ℕ => if j ∈ Finset.Icc 2 5 then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0)
        (∑ j ∈ Finset.Icc 2 5, (if j ∈ Finset.Icc 2 5 then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by simp [hj])
    convert h using 1
    exact Finset.sum_congr rfl (fun j hj => by simp [hj])
  have hT : HasSum (fun j : ℕ => if 2 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0)
      (∑ j ∈ Finset.Icc 2 5, (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) + ∑' j : ℕ, if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) := by
    rw [hsplit]
    exact h5s.add hs6.hasSum
  have hS6 : (∑' j : ℕ, if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) ≤ N6Of νp ^ 2 := by
    have hnn : 0 ≤ ∑' j : ℕ, (if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) := by
      apply tsum_nonneg
      intro j
      split_ifs with hj
      · have : (6 : ℝ) ≤ j := by exact_mod_cast hj
        exact div_nonneg (sq_nonneg _) (by linarith)
      · exact le_refl 0
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hN6 2
    rwa [Real.sq_sqrt hnn] at this
  set Mp : ℝ := 20 + N6Of νp ^ 2 + 130 * edef (cOf f τ) with hMp
  have hTM : ∑ j ∈ Finset.Icc 2 5, (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) + ∑' j : ℕ, (if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) ≤ Mp := by
    simp only [hMp]
    linarith
  have hMp0 : 0 < Mp := by simp only [hMp]; nlinarith [sq_nonneg (N6Of νp)]
  -- the bound for every `s > 0`
  have hbound : ∀ s : ℝ, 0 < s → ‖Tdot τ (cOf f τ) φ‖ ≤ (s * etadef (cOf f τ) + Mp / s) / 2 := by
    intro s hs
    have hg : HasSum (fun j : ℕ => (s * (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) +
        (if 2 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) / s) / 2)
        ((s * ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) +
          (∑ j ∈ Finset.Icc 2 5, (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) + ∑' j : ℕ, if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) / s) / 2) :=
      ((hsA.hasSum.mul_left s).add (hT.div_const s)).div_const 2
    have hle : ∀ j : ℕ, ‖(if 2 ≤ j then coeff φ j * TJ τ (cOf f τ) j else 0)‖ ≤
        (s * (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) + (if 2 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) / s) / 2 :=
      fun j => term_bound hs _ _ j
    have hns : Summable (fun j : ℕ => ‖(if 2 ≤ j then coeff φ j * TJ τ (cOf f τ) j else 0)‖) :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle hg.summable
    calc ‖Tdot τ (cOf f τ) φ‖ ≤ ∑' j : ℕ, ‖(if 2 ≤ j then coeff φ j * TJ τ (cOf f τ) j else 0)‖ :=
          norm_tsum_le_tsum_norm hns
      _ ≤ (s * ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) +
          (∑ j ∈ Finset.Icc 2 5, (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) + ∑' j : ℕ, if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) / s) / 2 :=
          hasSum_le hle hns.hasSum hg
      _ ≤ (s * etadef (cOf f τ) + Mp / s) / 2 := by
          have h1' : s * ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) ≤
              s * etadef (cOf f τ) := mul_le_mul_of_nonneg_left hAη hs.le
          have h2' : (∑ j ∈ Finset.Icc 2 5, (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) + ∑' j : ℕ, if 6 ≤ j then (‖TJ τ (cOf f τ) j‖ ^ 2 / (2 * (j : ℝ) - 1)) else 0) / s ≤ Mp / s :=
            div_le_div_of_nonneg_right hTM hs.le
          linarith
  have hη0 : 0 ≤ etadef (cOf f τ) := le_trans hA0 hAη
  rcases hη0.lt_or_eq with hη | hη
  · -- `s = √M/√η`
    set a := Real.sqrt (etadef (cOf f τ)) with ha
    set b := Real.sqrt Mp with hb
    have ha0 : 0 < a := Real.sqrt_pos.mpr hη
    have hb0 : 0 < b := Real.sqrt_pos.mpr hMp0
    have ha1 : a ≠ 0 := ha0.ne'
    have hb1 : b ≠ 0 := hb0.ne'
    have h := hbound (b / a) (div_pos hb0 ha0)
    have hη' : etadef (cOf f τ) = a ^ 2 := (Real.sq_sqrt hη.le).symm
    have hM' : Mp = b ^ 2 := (Real.sq_sqrt hMp0.le).symm
    calc ‖Tdot τ (cOf f τ) φ‖ ≤ (b / a * etadef (cOf f τ) + Mp / (b / a)) / 2 := h
      _ = a * b := by
        rw [hη', hM']
        field_simp
        ring
  · -- `η = 0`: then every `b_{2j-1}` vanishes and `Ṫ = 0`
    have hA : ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) = 0 := by
      linarith
    have hfun := (hasSum_zero_iff_of_nonneg hw0).mp (hA ▸ hsA.hasSum)
    have hz : ∀ j : ℕ, (if 2 ≤ j then coeff φ j * TJ τ (cOf f τ) j else 0) = 0 := by
      intro j
      split_ifs with hj
      · have hj0 := congrFun hfun j
        simp only [hj, ↓reduceIte, Pi.zero_apply] at hj0
        have h2j : (0 : ℝ) < 2 * (j : ℝ) - 1 := by
          have : (2 : ℝ) ≤ j := by exact_mod_cast hj
          linarith
        have hsq : ‖coeff φ j‖ ^ 2 = 0 := (mul_eq_zero.mp hj0).resolve_left h2j.ne'
        rw [norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq), zero_mul]
      · rfl
    have hT0 : Tdot τ (cOf f τ) φ = 0 := by
      simp only [Tdot]
      rw [show (fun j : ℕ => if 2 ≤ j then coeff φ j * TJ τ (cOf f τ) j else 0) = fun _ => 0 from funext hz]
      exact tsum_zero
    rw [hT0, norm_zero]
    positivity

/-! ### Row: prop_4_1_from_layer, given `Λ ≥ 0` on every cell

The proof of Proposition 4.1 (sec_04_near.tex:336-346): for `e > 0` take the cell with `ρ₋ ≤ ρ ≤ ρ₊`; with
`η = ρe`, `y ≤ y₀`, `m` increasing and `Λ ≥ 0`,
`Re Q_f - y²/20 ≥ y² (293/540 + δe - √(ρ₊e(M + 130e))) > 0` by the two inequalities of Lemma 4.8. -/

/-- The cell algebra. -/
private lemma cell_algebra {y2 e ρ η ρm ρp M Λ R : ℝ} (hy2 : 0 < y2) (hy2' : y2 ≤ y0 ^ 2) (he : 0 < e)
    (hρm : ρm ≤ ρ) (hρp : ρ ≤ ρp) (hρ0 : 0 ≤ ρm) (hM : 0 ≤ M) (hΛ : 0 ≤ Λ) (hη : η = ρ * e)
    (hA : 0 < 293 / 540 + (1 / y0 ^ 2 * (22 / 25 + 21 / 100 * ρm) - ρp * Λ) * e)
    (hA2 : 0 < (293 / 540 + (1 / y0 ^ 2 * (22 / 25 + 21 / 100 * ρm) - ρp * Λ) * e) ^ 2 -
      ρp * e * (M + 130 * e))
    (hR : 16 / 27 * y2 + e * (22 / 25 + 21 / 100 * ρ) - y2 * Real.sqrt (η * (M + 130 * e)) - y2 * η * Λ ≤ R) :
    y2 / 20 ≤ R := by
  subst hη
  have hy0 : (0 : ℝ) < y0 ^ 2 := by unfold y0; norm_num
  have hρp0 : 0 ≤ ρp := by linarith
  have hMe : 0 ≤ M + 130 * e := by linarith
  have hX : 0 ≤ ρp * e * (M + 130 * e) := mul_nonneg (mul_nonneg hρp0 he.le) hMe
  have hsq : Real.sqrt (ρp * e * (M + 130 * e)) <
      293 / 540 + (1 / y0 ^ 2 * (22 / 25 + 21 / 100 * ρm) - ρp * Λ) * e :=
    (Real.sqrt_lt' hA).mpr (by linarith)
  have hs1 : Real.sqrt (ρ * e * (M + 130 * e)) ≤ Real.sqrt (ρp * e * (M + 130 * e)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρp he.le) hMe)
  have h1 : y2 * (1 / y0 ^ 2) ≤ 1 := by rw [mul_one_div, div_le_one hy0]; exact hy2'
  have h2 : 0 ≤ 22 / 25 + 21 / 100 * ρm := by linarith
  have h3 : y2 * (1 / y0 ^ 2) * ((22 / 25 + 21 / 100 * ρm) * e) ≤ 1 * ((22 / 25 + 21 / 100 * ρm) * e) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg h2 he.le)
  have h4 : (22 / 25 + 21 / 100 * ρm) * e ≤ (22 / 25 + 21 / 100 * ρ) * e :=
    mul_le_mul_of_nonneg_right (by linarith) he.le
  have hl : y2 * (ρ * e) * Λ ≤ y2 * (ρp * e) * Λ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρp he.le) hy2.le) hΛ
  have hyA : y2 * (293 / 540 + (1 / y0 ^ 2 * (22 / 25 + 21 / 100 * ρm) - ρp * Λ) * e) =
      293 / 540 * y2 + y2 * (1 / y0 ^ 2) * ((22 / 25 + 21 / 100 * ρm) * e) - y2 * (ρp * e) * Λ := by ring
  have e1 := mul_le_mul_of_nonneg_left hs1 hy2.le
  have e2 := mul_lt_mul_of_pos_left hsq hy2
  nlinarith

theorem prop_4_1_from_layer_proved_from
    (hΛ : ∀ i : ℕ, i ≤ 255 → 0 ≤ Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256))
    (hDB : FactDeBranges) (h48 : Check_4_8)
    (hzero : ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → edef (cOf f τ) = 0 →
      Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) = (Qk τ : ℂ))
    (hcell : ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → yτ τ ≤ y0 → 0 < edef (cOf f τ) →
      ∀ i : ℕ, i ≤ 255 → (i : ℝ) / 256 ≤ etadef (cOf f τ) / edef (cOf f τ) →
        etadef (cOf f τ) / edef (cOf f τ) ≤ ((i : ℝ) + 1) / 256 →
        16 / 27 * ysq τ + edef (cOf f τ) * mρ (etadef (cOf f τ) / edef (cOf f τ)) -
            ysq τ * Real.sqrt (etadef (cOf f τ) * (Mcap ((i : ℝ) / 256) + 130 * edef (cOf f τ))) -
            ysq τ * etadef (cOf f τ) * Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ≤
          (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re := by
  rw [sec4_goal_equiv_proved]
  intro f hf
  -- the goal (sec4:goal) at every admissible `τ`
  have main : ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → yτ τ ≤ y0 →
      ysq τ / 20 ≤ (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re := by
    intro τ h1 h2 hyτ0
    have hc := cOf_norm_le hDB hf h1 h2
    have hys : 0 < ysq τ := by simp only [ysq]; nlinarith
    have he0 : 0 ≤ edef (cOf f τ) := by
      have := Complex.re_le_norm (cOf f τ)
      simp only [edef]
      linarith
    rcases he0.lt_or_eq with he | he
    · have hc1 : cOf f τ ≠ 1 := by
        rintro h
        simp [h, edef] at he
      obtain ⟨-, hρ0, hρ1, -, -⟩ := sec4_rho_facts_proved _ hc hc1
      have hρlt : etadef (cOf f τ) / edef (cOf f τ) < 1 := by linarith
      have h256 : 0 ≤ 256 * (etadef (cOf f τ) / edef (cOf f τ)) := mul_nonneg (by norm_num) hρ0
      have hi255 : Nat.floor (256 * (etadef (cOf f τ) / edef (cOf f τ))) ≤ 255 := by
        have : Nat.floor (256 * (etadef (cOf f τ) / edef (cOf f τ))) < 256 :=
          (Nat.floor_lt h256).mpr (by push_cast; linarith)
        omega
      have hlo : ((Nat.floor (256 * (etadef (cOf f τ) / edef (cOf f τ))) : ℕ) : ℝ) / 256 ≤
          etadef (cOf f τ) / edef (cOf f τ) := by
        have := Nat.floor_le h256
        rw [div_le_iff₀ (by norm_num)]
        linarith
      have hhi : etadef (cOf f τ) / edef (cOf f τ) ≤
          (((Nat.floor (256 * (etadef (cOf f τ) / edef (cOf f τ))) : ℕ) : ℝ) + 1) / 256 := by
        have := Nat.lt_floor_add_one (256 * (etadef (cOf f τ) / edef (cOf f τ)))
        rw [le_div_iff₀ (by norm_num)]
        linarith
      have hR := hcell f hf τ h1 h2 hyτ0 he _ hi255 hlo hhi
      obtain ⟨-, -, -, -, heP, -⟩ := sec4_caps_valid_proved τ h1 h2.le _ hc hc1 _ hi255 hlo hhi
      obtain ⟨-, -, hchk⟩ := h48 _ hi255
      obtain ⟨hA, hA2⟩ := hchk _ he.le heP
      simp only [dcap] at hA hA2
      simp only [mρ] at hR
      have hy2' : ysq τ ≤ y0 ^ 2 := by
        have h : yτ τ ^ 2 ≤ y0 ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hyτ0 2
        unfold yτ at h
        rwa [Real.sq_sqrt hys.le] at h
      have hη : etadef (cOf f τ) = etadef (cOf f τ) / edef (cOf f τ) * edef (cOf f τ) :=
        (div_mul_cancel₀ _ he.ne').symm
      have hM : 0 ≤ Mcap ((Nat.floor (256 * (etadef (cOf f τ) / edef (cOf f τ))) : ℕ) / 256 : ℝ) := by
        simp only [Mcap]
        positivity
      exact cell_algebra hys hy2' he hlo hhi (by positivity) hM (hΛ _ hi255) hη hA hA2 hR
    · have hQ := hzero f hf τ h1 h2 he.symm
      obtain ⟨-, -, hk, -⟩ := eq_Qk_proved τ h1 h2
      rw [hQ, Complex.ofReal_re]
      linarith
  intro y hy hy0
  obtain ⟨-, -, hτ1, hτ2, -, -, -⟩ := sec4_tau_bounds_proved y hy hy0
  have hy0' : y ≤ 17 / 80 := by simpa [y0] using hy0
  have hnn : 0 ≤ 1 / 4 - y ^ 2 := by nlinarith
  have hysq : ysq (Real.sqrt (1 / 4 - y ^ 2)) = y ^ 2 := by
    simp only [ysq]
    rw [Real.sq_sqrt hnn]
    ring
  have hyτ : yτ (Real.sqrt (1 / 4 - y ^ 2)) = y := by
    simp only [yτ]
    rw [hysq, Real.sqrt_sq hy.le]
  have hxi : xiτ (Real.sqrt (1 / 4 - y ^ 2)) = (y : ℂ) * I := by
    simp only [xiτ, hyτ]
    ring
  have key := main (Real.sqrt (1 / 4 - y ^ 2)) hτ1.le hτ2 (by rw [hyτ]; exact hy0)
  rw [hxi, hysq] at key
  exact key

end Robinson.Proofs
