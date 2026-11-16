/-
Robinson/Proofs/Sec4Elem.lean — proofs of sec4_midpoint, sec4_goal_equiv, sec4_tau_bounds,
sec4_eta_le, sec4_rho_facts, sec4_model_mem_S, lem_4_7, sec4_caps_valid.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Near
import Robinson.Proofs.Sec2Basic
import Robinson.Proofs.Normalize

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The rotation by `π` and the point `z_θ` -/

/-- `g(z) = f_π(z) = -f(-z)` (the rotation of Lemma 2.3 with `φ = π`; the paper calls it `g`). -/
private lemma rotate_pi_apply (f : ℂ → ℂ) (z : ℂ) : rotate Real.pi f z = -f (-z) := by
  unfold rotate
  rw [Complex.exp_neg_pi_mul_I, Complex.exp_pi_mul_I]
  simp

private lemma rotate_pi_eq (f : ℂ → ℂ) : rotate Real.pi f = fun z => -f (-z) := funext (rotate_pi_apply f)

/-- `Q_g(z, w) = Q_f(-z, -w)` for all `z, w`: `g'(z) = f'(-z)`. -/
private lemma Q_rotate_pi (f : ℂ → ℂ) (z w : ℂ) : Q (rotate Real.pi f) z w = Q f (-z) (-w) := by
  have hd : ∀ x : ℂ, deriv (rotate Real.pi f) x = deriv f (-x) := by
    intro x
    rw [rotate_pi_eq, deriv.fun_neg, deriv_comp_neg, neg_neg]
  unfold Q
  rw [hd z, hd w, rotate_pi_apply, rotate_pi_apply]
  have h1 : -z * deriv f (-z) - -w * deriv f (-w) = -(z * deriv f (-z) - w * deriv f (-w)) := by ring
  have h2 : f (-z) - f (-w) = -(-f (-z) - -f (-w)) := by ring
  rw [h1, h2, neg_div_neg_eq]

/-- `z_θ = ½ cos(θ/2) + i ½ sin(θ/2)`. -/
private lemma zθ_eq (θ : ℝ) :
    zθ θ = ((Real.cos (θ / 2) / 2 : ℝ) : ℂ) + ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I := by
  unfold zθ
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

private lemma conj_zθ_eq (θ : ℝ) :
    conj (zθ θ) = ((Real.cos (θ / 2) / 2 : ℝ) : ℂ) - ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I := by
  rw [zθ_eq, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- For `0 < θ ≤ π`: `θ ≤ θ₀ ⇔ ½ sin(θ/2) ≤ y₀`, as `sin` increases on `[-π/2, π/2]`. -/
private lemma le_θ₀_iff {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : θ ≤ θ₀ ↔ Real.sin (θ / 2) / 2 ≤ y0 := by
  have hmem : θ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have key := Real.le_arcsin_iff_sin_le hmem (y := 17 / 40) ⟨by norm_num, by norm_num⟩
  unfold θ₀ y0
  constructor
  · intro h
    have := key.mp (by linarith)
    linarith
  · intro h
    have := key.mpr (by linarith)
    linarith

private lemma θ₀_le_pi : θ₀ ≤ Real.pi := by
  unfold θ₀
  linarith [Real.arcsin_le_pi_div_two (17 / 40)]

/-- With `τ = ½ cos(θ/2)` and `y = ½ sin(θ/2)`: `Q_f(z_θ, z̄_θ) = Q_g(-τ + iy, -τ - iy)`. -/
private lemma Q_zθ_rot (f : ℂ → ℂ) (θ τ y : ℝ) (hc : Real.cos (θ / 2) / 2 = τ) (hs : Real.sin (θ / 2) / 2 = y) :
    Q f (zθ θ) (conj (zθ θ)) = Q (rotate Real.pi f) (-(τ : ℂ) + (y : ℂ) * I) (-(τ : ℂ) - (y : ℂ) * I) := by
  rw [Q_rotate_pi, sec2_Q_symm_proved f (zθ θ), conj_zθ_eq, zθ_eq, hc, hs]
  exact congrArg₂ (Q f) (by ring) (by ring)

/-- With `τ = ½ cos(θ/2)` and `y = ½ sin(θ/2)`: `Q_g(z_θ, z̄_θ) = Q_f(-τ + iy, -τ - iy)`. -/
private lemma Q_rot_zθ (f : ℂ → ℂ) (θ τ y : ℝ) (hc : Real.cos (θ / 2) / 2 = τ) (hs : Real.sin (θ / 2) / 2 = y) :
    Q (rotate Real.pi f) (zθ θ) (conj (zθ θ)) = Q f (-(τ : ℂ) + (y : ℂ) * I) (-(τ : ℂ) - (y : ℂ) * I) := by
  rw [Q_rotate_pi, sec2_Q_symm_proved f (-(zθ θ)), conj_zθ_eq, zθ_eq, hc, hs]
  exact congrArg₂ (Q f) (by ring) (by ring)

/-- For `0 < y ≤ y₀` the angle `θ = 2 arcsin(2y)` has `0 < θ ≤ θ₀`, `½ sin(θ/2) = y`, `½ cos(θ/2) = √(¼ - y²)`. -/
private lemma angle_of_y {y : ℝ} (hy : 0 < y) (hy0 : y ≤ y0) :
    0 < 2 * Real.arcsin (2 * y) ∧ 2 * Real.arcsin (2 * y) ≤ θ₀ ∧
      Real.cos (2 * Real.arcsin (2 * y) / 2) / 2 = Real.sqrt (1 / 4 - y ^ 2) ∧
      Real.sin (2 * Real.arcsin (2 * y) / 2) / 2 = y := by
  unfold y0 at hy0
  have hhalf : 2 * Real.arcsin (2 * y) / 2 = Real.arcsin (2 * y) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Real.arcsin_pos.mpr (by linarith : (0 : ℝ) < 2 * y)
    linarith
  · unfold θ₀
    have := Real.arcsin_le_arcsin (by linarith : 2 * y ≤ 17 / 40)
    linarith
  · rw [hhalf, Real.cos_arcsin, show 1 - (2 * y) ^ 2 = 2 ^ 2 * (1 / 4 - y ^ 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  · rw [hhalf, Real.sin_arcsin (by linarith) (by linarith)]
    ring

/-- For `0 < θ ≤ π`: `√(¼ - (½ sin(θ/2))²) = ½ cos(θ/2)`. -/
private lemma sqrt_eq_half_cos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    Real.sqrt (1 / 4 - (Real.sin (θ / 2) / 2) ^ 2) = Real.cos (θ / 2) / 2 := by
  have hcos : 0 ≤ Real.cos (θ / 2) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have := Real.sin_sq_add_cos_sq (θ / 2)
  rw [show 1 / 4 - (Real.sin (θ / 2) / 2) ^ 2 = (Real.cos (θ / 2) / 2) ^ 2 by linear_combination (-1 / 4) * this,
    Real.sqrt_sq (by linarith)]

/-! ### `sec4_midpoint` and `sec4_goal_equiv` -/

set_option linter.unusedVariables false in
theorem sec4_midpoint_proved (f : ℂ → ℂ) (hf : InS f) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    zθ θ = ((Real.cos (θ / 2) / 2 : ℝ) : ℂ) + ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I ∧
      (Real.cos (θ / 2) / 2) ^ 2 + (Real.sin (θ / 2) / 2) ^ 2 = 1 / 4 ∧
      (∀ z : ℂ, rotate Real.pi f z = -f (-z)) ∧
      Q f (zθ θ) (conj (zθ θ)) =
        Q (rotate Real.pi f) (-((Real.cos (θ / 2) / 2 : ℝ) : ℂ) - ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I)
          (-((Real.cos (θ / 2) / 2 : ℝ) : ℂ) + ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I) ∧
      Real.sin (θ / 2) ^ 2 / 80 = (Real.sin (θ / 2) / 2) ^ 2 / 20 ∧ (θ ≤ θ₀ ↔ Real.sin (θ / 2) / 2 ≤ y0) := by
  refine ⟨zθ_eq θ, ?_, rotate_pi_apply f, ?_, by ring, le_θ₀_iff h0 hπ⟩
  · have := Real.cos_sq_add_sin_sq (θ / 2)
    linear_combination this / 4
  · rw [Q_rotate_pi, conj_zθ_eq, zθ_eq]
    exact congrArg₂ (Q f) (by ring) (by ring)

theorem sec4_goal_equiv_proved :
    (∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
        Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re) ↔
      ∀ f : ℂ → ℂ, InS f → ∀ y : ℝ, 0 < y → y ≤ y0 →
        y ^ 2 / 20 ≤ (Q f (-((Real.sqrt (1 / 4 - y ^ 2) : ℝ) : ℂ) + (y : ℂ) * I)
          (-((Real.sqrt (1 / 4 - y ^ 2) : ℝ) : ℂ) - (y : ℂ) * I)).re := by
  constructor
  · intro H f hf y hy hy0
    obtain ⟨hθ0, hθ1, hc, hs⟩ := angle_of_y hy hy0
    have h := H (rotate Real.pi f) (lem_2_3_rot_proved f hf Real.pi).1 _ hθ0 hθ1
    rw [Q_rot_zθ f _ _ _ hc hs] at h
    have hs2 : Real.sin (2 * Real.arcsin (2 * y) / 2) = 2 * y := by linarith
    have e : (2 * y) ^ 2 / 80 = y ^ 2 / 20 := by ring
    rw [hs2, e] at h
    exact h
  · intro H f hf θ hθ0 hθ1
    have hπ : θ ≤ Real.pi := le_trans hθ1 θ₀_le_pi
    have hy : 0 < Real.sin (θ / 2) / 2 := by
      have := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ / 2) (by linarith [Real.pi_pos])
      linarith
    have hy0 : Real.sin (θ / 2) / 2 ≤ y0 := (le_θ₀_iff hθ0 hπ).mp hθ1
    have h := H (rotate Real.pi f) (lem_2_3_rot_proved f hf Real.pi).1 _ hy hy0
    rw [sqrt_eq_half_cos hθ0 hπ, ← Q_zθ_rot f θ _ _ rfl rfl] at h
    have e : (Real.sin (θ / 2) / 2) ^ 2 / 20 = Real.sin (θ / 2) ^ 2 / 80 := by ring
    rw [e] at h
    exact h

/-! ### `sec4_tau_bounds` -/

theorem sec4_tau_bounds_proved (y : ℝ) (hy : 0 < y) (hy0 : y ≤ y0) :
    1311 / 6400 ≤ Real.sqrt (1 / 4 - y ^ 2) ^ 2 ∧ (9 / 20 : ℝ) ^ 2 < 1311 / 6400 ∧
      9 / 20 < Real.sqrt (1 / 4 - y ^ 2) ∧ Real.sqrt (1 / 4 - y ^ 2) < 1 / 2 ∧
      3 / 4 ≤ vτ (Real.sqrt (1 / 4 - y ^ 2)) ∧ vτ (Real.sqrt (1 / 4 - y ^ 2)) ≤ 1 ∧
      βτ (Real.sqrt (1 / 4 - y ^ 2)) ≤ 2 / 3 := by
  unfold y0 at hy0
  have hy2 : y ^ 2 ≤ 289 / 6400 := by nlinarith
  have hy2' : 0 < y ^ 2 := by positivity
  have hnn : 0 ≤ 1 / 4 - y ^ 2 := by linarith
  have hsq : Real.sqrt (1 / 4 - y ^ 2) ^ 2 = 1 / 4 - y ^ 2 := Real.sq_sqrt hnn
  have hlo : 9 / 20 < Real.sqrt (1 / 4 - y ^ 2) := (Real.lt_sqrt (by norm_num)).mpr (by linarith)
  have hhi : Real.sqrt (1 / 4 - y ^ 2) < 1 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by linarith)
  have hv : vτ (Real.sqrt (1 / 4 - y ^ 2)) = 3 / 4 + y ^ 2 := by
    unfold vτ
    rw [hsq]
    ring
  refine ⟨by linarith, by norm_num, hlo, hhi, by rw [hv]; linarith, by rw [hv]; linarith, ?_⟩
  unfold βτ
  rw [hv, div_le_iff₀ (by positivity)]
  linarith

/-! ### `sec4_eta_le` and `sec4_rho_facts` -/

private lemma norm_sq_eq_re_im (c : ℂ) : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem sec4_eta_le_proved (c : ℂ) (hc : ‖c‖ ≤ 1) :
    etadef c ≤ edef c - edef c ^ 2 / 4 ∧ (edef c = 0 → c = 1 ∧ etadef c = 0) := by
  have hn := norm_sq_eq_re_im c
  have hn1 : ‖c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg c]
  unfold etadef edef
  refine ⟨by nlinarith [sq_nonneg c.im], fun he => ?_⟩
  have hre : c.re = 1 := by linarith
  have him2 : c.im ^ 2 ≤ 0 := by nlinarith
  have him : c.im = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm him2 (sq_nonneg _))
  have hc1 : c = 1 := Complex.ext (by rw [hre, Complex.one_re]) (by rw [him, Complex.one_im])
  refine ⟨hc1, ?_⟩
  rw [hc1]
  simp

private lemma edef_pos (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1) : 0 < edef c := by
  have hre : c.re ≤ 1 := le_trans (Complex.re_le_norm c) hc
  have hne : edef c ≠ 0 := fun h => hc1 ((sec4_eta_le_proved c hc).2 h).1
  exact lt_of_le_of_ne (by unfold edef; linarith) (Ne.symm hne)

theorem sec4_rho_facts_proved (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1) :
    0 < edef c ∧ 0 ≤ etadef c / edef c ∧ etadef c / edef c ≤ 1 - edef c / 4 ∧
      edef c ≤ 4 * (1 - etadef c / edef c) ∧ ‖c - ((etadef c / edef c : ℝ) : ℂ)‖ = 1 - etadef c / edef c := by
  have he := edef_pos c hc hc1
  have hη0 : 0 ≤ etadef c := by unfold etadef; nlinarith [norm_nonneg c]
  have hle := (sec4_eta_le_proved c hc).1
  have hρle : etadef c / edef c ≤ 1 - edef c / 4 := by
    rw [div_le_iff₀ he]
    nlinarith
  refine ⟨he, div_nonneg hη0 he.le, hρle, by linarith, ?_⟩
  set ρ := etadef c / edef c with hρ
  have hηρ : ρ * edef c = etadef c := div_mul_cancel₀ _ he.ne'
  have h1ρ : 0 ≤ 1 - ρ := by linarith
  have hn := norm_sq_eq_re_im c
  have hsq : ‖c - (ρ : ℂ)‖ ^ 2 = (1 - ρ) ^ 2 := by
    rw [norm_sq_eq_re_im]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    unfold etadef edef at hηρ
    linear_combination hηρ - hn
  exact (sq_eq_sq₀ (norm_nonneg _) h1ρ).mp hsq

/-! ### `sec4_model_mem_S`: the comparison function `u/(1 - cu)²` -/

/-- `|c| ≤ 1` and `|u| < 1` keep `1 - cu ≠ 0`. -/
private lemma one_sub_mul_ne_zero {c u : ℂ} (hc : ‖c‖ ≤ 1) (hu : ‖u‖ < 1) : 1 - c * u ≠ 0 := by
  intro h
  have h1 : c * u = 1 := by linear_combination -h
  have h2 : ‖c * u‖ < 1 := by
    rw [norm_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg u)]
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- The derivative of `u/(1 - cu)²` is `(1 + cu)/(1 - cu)³` where `1 - cu ≠ 0`. -/
private lemma hasDerivAt_model (c u : ℂ) (hu : 1 - c * u ≠ 0) :
    HasDerivAt (fun u => u / (1 - c * u) ^ 2) ((1 + c * u) / (1 - c * u) ^ 3) u := by
  have hden : HasDerivAt (fun x : ℂ => (1 - c * x) ^ 2) ((2 : ℕ) * (1 - c * u) ^ (2 - 1) * (0 - c * 1)) u :=
    ((hasDerivAt_const u (1 : ℂ)).sub ((hasDerivAt_id u).const_mul c)).pow 2
  have hq : HasDerivAt (fun x : ℂ => x / (1 - c * x) ^ 2)
      ((1 * (1 - c * u) ^ 2 - u * ((2 : ℕ) * (1 - c * u) ^ (2 - 1) * (0 - c * 1))) / ((1 - c * u) ^ 2) ^ 2) u :=
    (hasDerivAt_id u).div hden (pow_ne_zero 2 hu)
  refine hq.congr_deriv ?_
  push_cast
  field_simp
  ring

/-- The derivative of `(1 + cu)/(1 - cu)³` at `0` is `4c`. -/
private lemma hasDerivAt_model_deriv_zero (c : ℂ) :
    HasDerivAt (fun u => (1 + c * u) / (1 - c * u) ^ 3) (4 * c) 0 := by
  have hnum : HasDerivAt (fun x : ℂ => 1 + c * x) (0 + c * 1) 0 :=
    (hasDerivAt_const 0 (1 : ℂ)).add ((hasDerivAt_id 0).const_mul c)
  have hden : HasDerivAt (fun x : ℂ => (1 - c * x) ^ 3) ((3 : ℕ) * (1 - c * 0) ^ (3 - 1) * (0 - c * 1)) 0 :=
    ((hasDerivAt_const 0 (1 : ℂ)).sub ((hasDerivAt_id 0).const_mul c)).pow 3
  have hq := hnum.div hden (by simp)
  convert hq using 1
  norm_num
  ring

private lemma deriv_model_eventually (c : ℂ) :
    deriv (fun u => u / (1 - c * u) ^ 2) =ᶠ[𝓝 0] fun u => (1 + c * u) / (1 - c * u) ^ 3 := by
  have hcont : ContinuousAt (fun u : ℂ => 1 - c * u) 0 := by fun_prop
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), 1 - c * u ≠ 0 := hcont.eventually_ne (by simp)
  exact hev.mono fun u hu => (hasDerivAt_model c u hu).deriv

private lemma coeff_model_two (c : ℂ) : coeff (fun u => u / (1 - c * u) ^ 2) 2 = 2 * c := by
  unfold coeff
  rw [iteratedDeriv_succ, iteratedDeriv_one, (deriv_model_eventually c).deriv_eq,
    (hasDerivAt_model_deriv_zero c).deriv]
  norm_num [Nat.factorial]
  ring

private lemma model_injOn {c : ℂ} (hc : ‖c‖ ≤ 1) : Set.InjOn (fun u => u / (1 - c * u) ^ 2) (ball (0 : ℂ) 1) := by
  intro u hu w hw h
  have hu' := mem_ball_zero_iff.mp hu
  have hw' := mem_ball_zero_iff.mp hw
  have hu1 := one_sub_mul_ne_zero hc hu'
  have hw1 := one_sub_mul_ne_zero hc hw'
  simp only at h
  rw [div_eq_div_iff (pow_ne_zero 2 hu1) (pow_ne_zero 2 hw1)] at h
  have hfac : (u - w) * (1 - c ^ 2 * u * w) = 0 := by linear_combination h
  have hne : 1 - c ^ 2 * u * w ≠ 0 := by
    intro h0
    have h1 : c ^ 2 * u * w = 1 := by linear_combination -h0
    have hc2 : ‖c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg c]
    have huw : ‖u‖ * ‖w‖ < 1 := by
      nlinarith [norm_nonneg u, norm_nonneg w, mul_le_mul_of_nonneg_right hu'.le (norm_nonneg w)]
    have hlt : ‖c ^ 2 * u * w‖ < 1 := by
      rw [norm_mul, norm_mul, norm_pow]
      have hpos : 0 ≤ ‖u‖ * ‖w‖ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hc2 hpos]
    rw [h1, norm_one] at hlt
    exact lt_irrefl _ hlt
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hne)

private lemma model_inS (c : ℂ) (hc : ‖c‖ ≤ 1) : InS (fun u => u / (1 - c * u) ^ 2) where
  differentiableOn := fun u hu =>
    (hasDerivAt_model c u (one_sub_mul_ne_zero hc (mem_ball_zero_iff.mp hu))).differentiableAt.differentiableWithinAt
  injOn := model_injOn hc
  map_zero := by simp
  deriv_zero := by
    rw [(hasDerivAt_model c 0 (by simp)).deriv]
    simp

theorem sec4_model_mem_S_proved (c : ℂ) (hc : ‖c‖ ≤ 1) :
    InS (fun u => u / (1 - c * u) ^ 2) ∧ (c ≠ 0 → ∀ u : ℂ, u / (1 - c * u) ^ 2 = koebe (c * u) / c) ∧
      coeff (fun u => u / (1 - c * u) ^ 2) 2 = 2 * c ∧ (c = 1 → (fun u => u / (1 - c * u) ^ 2) = koebe) := by
  refine ⟨model_inS c hc, fun hc0 u => ?_, coeff_model_two c, fun h1 => ?_⟩
  · unfold koebe
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hc0]
  · subst h1
    funext u
    simp [koebe]

/-! ### Lemma 4.7 and the caps of the cells -/

/-- From `|c - ρ| = 1 - ρ` with `ρ₋ ≤ ρ < 1`: `|ν| ≤ max(20/29, 2 - (8/3)ρ₋)` for `9/20 ≤ τ ≤ ½`. -/
private lemma nu_bound_aux {τ ρ ρm : ℝ} {c : ℂ} (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hρm : ρm ≤ ρ) (hρ1 : ρ < 1)
    (hdist : ‖c - (ρ : ℂ)‖ = 1 - ρ) : ‖nuτ τ c‖ ≤ max (20 / 29) (2 - 8 / 3 * ρm) := by
  have hv : 0 < vτ τ := by unfold vτ; nlinarith
  have hnorm : ‖nuτ τ c‖ = ‖c - (τ : ℂ)‖ / vτ τ := by
    unfold nuτ
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  have htri : ‖c - (τ : ℂ)‖ ≤ (1 - ρ) + |ρ - τ| := by
    calc ‖c - (τ : ℂ)‖ = ‖(c - (ρ : ℂ)) + ((ρ - τ : ℝ) : ℂ)‖ := by
          congr 1
          push_cast
          ring
      _ ≤ ‖c - (ρ : ℂ)‖ + ‖((ρ - τ : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = (1 - ρ) + |ρ - τ| := by rw [hdist, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, div_le_iff₀ hv]
  rcases le_total τ ρ with h | h
  · rw [abs_of_nonneg (by linarith)] at htri
    calc ‖c - (τ : ℂ)‖ ≤ 1 - τ := by linarith
      _ ≤ 20 / 29 * vτ τ := by
          unfold vτ
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ) (by linarith : (0 : ℝ) ≤ 20 * τ - 9)]
      _ ≤ max (20 / 29) (2 - 8 / 3 * ρm) * vτ τ := by
          gcongr
          exact le_max_left _ _
  · rw [abs_of_nonpos (by linarith)] at htri
    have hA : 0 ≤ (1 + τ) - 2 / 3 * ρm * (1 + 2 * τ) := by nlinarith
    calc ‖c - (τ : ℂ)‖ ≤ 1 + τ - 2 * ρm := by linarith
      _ ≤ (2 - 8 / 3 * ρm) * vτ τ := by
          unfold vτ
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * τ) hA]
      _ ≤ max (20 / 29) (2 - 8 / 3 * ρm) * vτ τ := by
          gcongr
          exact le_max_right _ _

theorem lem_4_7_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (he : 0 < edef c)
    (ρm : ℝ) (hρ : ρm ≤ etadef c / edef c) :
    ‖nuτ τ c‖ ≤ max (20 / 29) (2 - 8 / 3 * ρm) ∧
      etadef c ≤ 4 * (etadef c / edef c) * (1 - etadef c / edef c) := by
  have hc1 : c ≠ 1 := by
    rintro rfl
    simp [edef] at he
  obtain ⟨-, hρ0, hρle, heρ, hdist⟩ := sec4_rho_facts_proved c hc hc1
  have hηρ : etadef c / edef c * edef c = etadef c := div_mul_cancel₀ _ he.ne'
  refine ⟨nu_bound_aux h1 h2 hρ (by linarith) hdist, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left heρ hρ0]

set_option linter.unusedVariables false in
theorem sec4_caps_valid_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (hc1 : c ≠ 1) (i : ℕ)
    (hi : i ≤ 255) (hlo : (i : ℝ) / 256 ≤ etadef c / edef c) (hhi : etadef c / edef c ≤ ((i : ℝ) + 1) / 256) :
    ‖nuτ τ c‖ ≤ nuPlus ((i : ℝ) / 256) ∧ nuPlus ((i : ℝ) / 256) ≤ 2 ∧
      etadef c ≤ etaPlus ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ∧
      etaPlus ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ≤ 1 ∧ edef c ≤ ePlus ((i : ℝ) / 256) ∧
      Real.sqrt (Mcap ((i : ℝ) / 256) + 130 * edef c) ≤ nPlus ((i : ℝ) / 256) := by
  have he := edef_pos c hc hc1
  obtain ⟨-, -, -, heρ, -⟩ := sec4_rho_facts_proved c hc hc1
  obtain ⟨hnu, hη⟩ := lem_4_7_proved τ h1 h2 c hc he _ hlo
  have hi0 : (0 : ℝ) ≤ (i : ℝ) / 256 := by positivity
  have hePlus : edef c ≤ ePlus ((i : ℝ) / 256) := by
    unfold ePlus
    linarith
  refine ⟨hnu, ?_, ?_, min_le_left _ _, hePlus, ?_⟩
  · unfold nuPlus
    exact max_le (by norm_num) (by linarith)
  · unfold etaPlus
    apply le_min
    · unfold etadef
      nlinarith [norm_nonneg c]
    · have hbdd : BddAbove ((fun ρ : ℝ => ρ * (1 - ρ)) '' Set.Icc ((i : ℝ) / 256) (((i : ℝ) + 1) / 256)) := by
        refine ⟨1 / 4, ?_⟩
        rintro _ ⟨r, -, rfl⟩
        nlinarith [sq_nonneg (r - 1 / 2)]
      have hsup : etadef c / edef c * (1 - etadef c / edef c) ≤
          sSup ((fun ρ : ℝ => ρ * (1 - ρ)) '' Set.Icc ((i : ℝ) / 256) (((i : ℝ) + 1) / 256)) :=
        le_csSup hbdd ⟨_, ⟨hlo, hhi⟩, rfl⟩
      nlinarith
  · unfold nPlus
    exact Real.sqrt_le_sqrt (by linarith)

end Robinson.Proofs
