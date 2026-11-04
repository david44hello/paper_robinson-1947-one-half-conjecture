/-
Robinson/Proofs/Sec3Local.lean — proofs of sec3_deriv_ne_zero, sec3_koebe_transform_mem_S,
sec3_kernel_nonvanishing, sec3_p_ne_zero, sec4_c_bounds.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Grunsky
import Robinson.Defs.Near
import Robinson.NotFormalized

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### An injective holomorphic function has a nonvanishing derivative

Suppose `f` is holomorphic and injective on an open set `U`, `a ∈ U` and `f'(a) = 0`. Then `f(z) - f(a)` is not
identically zero near `a`, so `f(z) - f(a) = (z - a)ⁿ g(z)` near `a` with `g` analytic, `g(a) ≠ 0`, and `n ≥ 2`
because `f'(a) = 0`. With `h` an analytic `n`-th root of `g` near `a`, `φ(z) = (z - a) h(z)` satisfies
`f(z) - f(a) = φ(z)ⁿ`; `φ` is not constant near `a`, so by the open mapping theorem its image of every small
neighbourhood of `a` contains a disc `|w| < ε`. The two values `w₁ = ε/2` and `w₂ = ω ε/2`, `ω = e^{2πi/n} ≠ 1`, are
taken at two distinct points where `f` takes the same value `f(a) + w₁ⁿ`. -/

/-- An injective function on an open set `U ∋ a` is not equal to `f(a)` on a whole neighbourhood of `a`. -/
private lemma not_eventually_sub_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hinj : Set.InjOn f U) {a : ℂ}
    (ha : a ∈ U) : ¬ ∀ᶠ z in 𝓝 a, f z - f a = 0 := by
  intro h
  have h2 : ∀ᶠ z in 𝓝[≠] a, (f z - f a = 0 ∧ z ∈ U) ∧ z ∈ ({a}ᶜ : Set ℂ) :=
    ((h.and (hU.mem_nhds ha)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨z, ⟨hz, hzU⟩, hne⟩ := h2.exists
  exact hne (hinj hzU ha (sub_eq_zero.mp hz))

/-- If `f(z) - f(a) = (z - a)ⁿ g(z)` near `a` with `g(a) ≠ 0` and `f'(a) = 0`, then `n ≥ 2`. -/
private lemma two_le_of_deriv_eq_zero {f g : ℂ → ℂ} {a : ℂ} {n : ℕ} (hfa : DifferentiableAt ℂ f a)
    (hga : AnalyticAt ℂ g a) (hg0 : g a ≠ 0) (hd : deriv f a = 0)
    (heq : ∀ᶠ z in 𝓝 a, f z - f a = (z - a) ^ n • g z) : 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exfalso
    interval_cases n
    · have h0 := heq.self_of_nhds
      simp only [sub_self, pow_zero, one_smul] at h0
      exact hg0 h0.symm
    · have hmul : HasDerivAt (fun z => (z - a) * g z) (1 * g a + (a - a) * deriv g a) a :=
        ((hasDerivAt_id' a).sub_const a).mul hga.differentiableAt.hasDerivAt
      have heq' : (fun z => f z - f a) =ᶠ[𝓝 a] fun z => (z - a) * g z := by
        filter_upwards [heq] with z hz
        simpa only [pow_one, smul_eq_mul] using hz
      have h1 : HasDerivAt (fun z => f z - f a) (1 * g a + (a - a) * deriv g a) a :=
        hmul.congr_of_eventuallyEq heq'
      have h2 : HasDerivAt (fun z => f z - f a) (deriv f a) a := hfa.hasDerivAt.sub_const (f a)
      have h3 := h1.unique h2
      rw [hd, sub_self, zero_mul, add_zero, one_mul] at h3
      exact hg0 h3
  · exact hn

/-- A function analytic at `a` with `g(a) ≠ 0` has an `n`-th root analytic at `a` (`n ≠ 0`):
`h(z) = g(a)^{1/n} (g(z)/g(a))^{1/n}`, principal powers; `g(z)/g(a)` is near `1`, off the cut. -/
private lemma exists_analytic_root {g : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : n ≠ 0) (hga : AnalyticAt ℂ g a)
    (hg0 : g a ≠ 0) : ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ ∀ z, h z ^ n = g z := by
  refine ⟨fun z => g a ^ ((n : ℂ)⁻¹) * (g z / g a) ^ ((n : ℂ)⁻¹), ?_, ?_⟩
  · have hslit : g a / g a ∈ slitPlane := by
      rw [div_self hg0]
      exact one_mem_slitPlane
    exact analyticAt_const.mul ((hga.div analyticAt_const hg0).cpow analyticAt_const hslit)
  · intro z
    rw [mul_pow, cpow_nat_inv_pow _ hn, cpow_nat_inv_pow _ hn]
    field_simp

/-- For `n ≥ 2` and `ε > 0` there are two distinct points `w₁ ≠ w₂` of the disc `|w| < ε` with `w₁ⁿ = w₂ⁿ`. -/
private lemma exists_ne_pow_eq {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ w₁ w₂ : ℂ, w₁ ∈ ball (0 : ℂ) ε ∧ w₂ ∈ ball (0 : ℂ) ε ∧ w₁ ≠ w₂ ∧ w₁ ^ n = w₂ ^ n := by
  have hn0 : n ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp n hn0
  set ω := exp (2 * Real.pi * I / n) with hω
  have hω1 : ‖ω‖ = 1 := hprim.norm'_eq_one hn0
  have hωne : ω ≠ 1 := hprim.ne_one (by omega)
  have hw : (((ε / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, ofReal_eq_zero]
    positivity
  have hnorm : ‖(((ε / 2 : ℝ)) : ℂ)‖ < ε := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  refine ⟨((ε / 2 : ℝ) : ℂ), ((ε / 2 : ℝ) : ℂ) * ω, ?_, ?_, ?_, ?_⟩
  · rwa [mem_ball_zero_iff]
  · rwa [mem_ball_zero_iff, norm_mul, hω1, mul_one]
  · intro h
    apply hωne
    have h' : ((ε / 2 : ℝ) : ℂ) * ω = ((ε / 2 : ℝ) : ℂ) * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ hw h'
  · rw [mul_pow, hprim.pow_eq_one, mul_one]

/-- An injective holomorphic function on an open set has a nonvanishing derivative there. -/
private lemma deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : Set.InjOn f U) {a : ℂ} (ha : a ∈ U) : deriv f a ≠ 0 := by
  intro hd
  have hfa : AnalyticAt ℂ f a := hf.analyticAt (hU.mem_nhds ha)
  have hne := not_eventually_sub_eq_zero hU hinj ha
  obtain ⟨n, g, hga, hg0, heq⟩ :=
    (hfa.sub analyticAt_const).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have heq' : ∀ᶠ z in 𝓝 a, f z - f a = (z - a) ^ n • g z := heq
  have hn2 : 2 ≤ n := two_le_of_deriv_eq_zero hfa.differentiableAt hga hg0 hd heq'
  obtain ⟨h, hha, hpow⟩ := exists_analytic_root (by omega : n ≠ 0) hga hg0
  set φ : ℂ → ℂ := fun z => (z - a) * h z with hφ
  have hφa : AnalyticAt ℂ φ a := ((analyticAt_id).sub analyticAt_const).mul hha
  have hφ0 : φ a = 0 := by simp [hφ]
  have hFφ : ∀ᶠ z in 𝓝 a, z ∈ U ∧ f z - f a = φ z ^ n := by
    filter_upwards [heq', hU.mem_nhds ha] with z hz hzU
    refine ⟨hzU, ?_⟩
    rw [hz, smul_eq_mul, hφ, mul_pow, hpow]
  rcases hφa.eventually_constant_or_nhds_le_map_nhds with hc | hopen
  · apply hne
    filter_upwards [hc, hFφ] with z hz hzF
    rw [hzF.2, hz, hφ0, zero_pow (by omega)]
  · have himg : φ '' {z | z ∈ U ∧ f z - f a = φ z ^ n} ∈ 𝓝 (φ a) := hopen (image_mem_map hFφ)
    rw [hφ0, Metric.mem_nhds_iff] at himg
    obtain ⟨ε, hε, hball⟩ := himg
    obtain ⟨w₁, w₂, hw₁, hw₂, hw, hpw⟩ := exists_ne_pow_eq hn2 hε
    obtain ⟨z₁, ⟨hz₁U, hz₁⟩, hφz₁⟩ := hball hw₁
    obtain ⟨z₂, ⟨hz₂U, hz₂⟩, hφz₂⟩ := hball hw₂
    have hfeq : f z₁ = f z₂ := by
      have h12 : f z₁ - f a = f z₂ - f a := by rw [hz₁, hz₂, hφz₁, hφz₂, hpw]
      exact sub_left_inj.mp h12
    apply hw
    rw [← hφz₁, ← hφz₂, hinj hz₁U hz₂U hfeq]

/-! ### Section 3 rows -/

/-- sec_03_tools.tex:13: `f'(a) ≠ 0` for `f ∈ 𝒮` and `a ∈ 𝔻`. -/
theorem sec3_deriv_ne_zero_proved (f : ℂ → ℂ) (hf : InS f) (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    deriv f a ≠ 0 :=
  deriv_ne_zero_of_injOn isOpen_ball hf.differentiableOn hf.injOn ha

/-! ### The disc automorphism `T(u) = (u + a)/(1 + ā u)` -/

/-- `|1 + ā u|² - |u + a|² = (1 - |a|²)(1 - |u|²)`. -/
private lemma normSq_mobius_identity (a u : ℂ) :
    normSq (1 + conj a * u) - normSq (u + a) = (1 - normSq a) * (1 - normSq u) := by
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

/-- `|z|² < 1` on the open unit disc. -/
private lemma normSq_lt_one {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : normSq z < 1 := by
  rw [mem_ball_zero_iff] at hz
  rw [normSq_eq_norm_sq]
  nlinarith [norm_nonneg z]

/-- `(1 - |a|²)(1 - |u|²) > 0` on the disc. -/
private lemma mobius_factor_pos {a u : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hu : u ∈ ball (0 : ℂ) 1) :
    0 < (1 - normSq a) * (1 - normSq u) := by
  have h1 := normSq_lt_one ha
  have h2 := normSq_lt_one hu
  apply mul_pos <;> linarith

/-- `1 + ā u ≠ 0` for `a, u` in the disc. -/
private lemma mobius_den_ne_zero {a u : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hu : u ∈ ball (0 : ℂ) 1) :
    1 + conj a * u ≠ 0 := by
  intro h
  have hid := normSq_mobius_identity a u
  rw [h, map_zero] at hid
  have := mobius_factor_pos ha hu
  nlinarith [normSq_nonneg (u + a)]

/-- `T` maps the disc into the disc. -/
private lemma mobius_mem_ball {a u : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hu : u ∈ ball (0 : ℂ) 1) :
    (u + a) / (1 + conj a * u) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.mpr (mobius_den_ne_zero ha hu))]
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm]
  have hid := normSq_mobius_identity a u
  have := mobius_factor_pos ha hu
  linarith

/-- `1 - a ā = 1 - |a|²`, as a complex number. -/
private lemma one_sub_mul_conj (a : ℂ) : 1 - a * conj a = (((1 - ‖a‖ ^ 2 : ℝ)) : ℂ) := by
  rw [mul_conj']
  push_cast
  ring

/-- `1 - |a|² ≠ 0` on the disc. -/
private lemma one_sub_norm_sq_ne_zero {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) : (((1 - ‖a‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
  rw [Ne, ofReal_eq_zero]
  rw [mem_ball_zero_iff] at ha
  nlinarith [norm_nonneg a]

/-- `T` is injective on the disc. -/
private lemma mobius_injOn {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    Set.InjOn (fun u => (u + a) / (1 + conj a * u)) (ball (0 : ℂ) 1) := by
  intro u hu v hv huv
  simp only at huv
  rw [div_eq_div_iff (mobius_den_ne_zero ha hu) (mobius_den_ne_zero ha hv)] at huv
  have key : (u - v) * (1 - a * conj a) = 0 := by linear_combination huv
  rw [one_sub_mul_conj] at key
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (one_sub_norm_sq_ne_zero ha))

/-- `T` is differentiable on the disc. -/
private lemma mobius_differentiableOn {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (fun u => (u + a) / (1 + conj a * u)) (ball (0 : ℂ) 1) := by
  intro u hu
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_id.add_const a).div
    ((differentiableAt_const (1 : ℂ)).add ((differentiableAt_const (conj a)).mul differentiableAt_id))
    (mobius_den_ne_zero ha hu)

/-- `T(0) = a` and `T'(0) = 1 - |a|²`. -/
private lemma mobius_hasDerivAt_zero (a : ℂ) :
    HasDerivAt (fun u => (u + a) / (1 + conj a * u)) (1 - a * conj a) 0 := by
  have hc : HasDerivAt (fun u : ℂ => u + a) 1 0 := (hasDerivAt_id' 0).add_const a
  have hd : HasDerivAt (fun u : ℂ => 1 + conj a * u) (conj a) 0 := by
    have := ((hasDerivAt_id' (0 : ℂ)).const_mul (conj a)).const_add 1
    simpa only [mul_one] using this
  have h := hc.div hd (by simp)
  convert h using 1
  simp

/-- sec_03_tools.tex:9-13: the Koebe transform `f_a` of `f ∈ 𝒮` belongs to `𝒮`. -/
theorem sec3_koebe_transform_mem_S_proved (f : ℂ → ℂ) (hf : InS f) (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    InS (koebeTransform f a) := by
  have hfa : deriv f a ≠ 0 := sec3_deriv_ne_zero_proved f hf a ha
  have hD : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * deriv f a ≠ 0 := mul_ne_zero (one_sub_norm_sq_ne_zero ha) hfa
  have hT0 : (0 + a) / (1 + conj a * 0) = a := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hf.differentiableOn.comp (mobius_differentiableOn ha)
      (fun u hu => mobius_mem_ball ha hu)).sub_const (f a)).div_const _
  · intro u hu v hv huv
    simp only [koebeTransform] at huv
    rw [div_left_inj' hD, sub_left_inj] at huv
    exact mobius_injOn ha hu hv (hf.injOn (mobius_mem_ball ha hu) (mobius_mem_ball ha hv) huv)
  · simp [koebeTransform]
  · have hfd : HasDerivAt f (deriv f a) ((0 + a) / (1 + conj a * 0)) := by
      rw [hT0]
      exact (hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
    have h := ((hfd.comp (0 : ℂ) (mobius_hasDerivAt_zero a)).sub_const (f a)).div_const
      (((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * deriv f a)
    have hval : deriv f a * (1 - a * conj a) / (((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * deriv f a) = 1 := by
      rw [one_sub_mul_conj, mul_comm (deriv f a)]
      exact div_self hD
    rw [hval] at h
    exact h.deriv

/-- sec_03_tools.tex:24: the difference quotient of `g ∈ 𝒮` (by `g'` on the diagonal) and `g(s)/s` (by `g'(0) = 1`
at `0`) have no zero in the disc. -/
theorem sec3_kernel_nonvanishing_proved (g : ℂ → ℂ) (hg : InS g) :
    (∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      (if s = t then deriv g s else (g s - g t) / (s - t)) ≠ 0) ∧ deriv g 0 = 1 ∧
      ∀ s : ℂ, s ∈ ball (0 : ℂ) 1 → (if s = 0 then deriv g 0 else g s / s) ≠ 0 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  refine ⟨?_, hg.deriv_zero, ?_⟩
  · intro s t hs ht
    split_ifs with hst
    · exact sec3_deriv_ne_zero_proved g hg s hs
    · refine div_ne_zero (fun h => hst (hg.injOn hs ht (sub_eq_zero.mp h))) (sub_ne_zero.mpr hst)
  · intro s hs
    split_ifs with hs0
    · rw [hg.deriv_zero]
      exact one_ne_zero
    · refine div_ne_zero (fun h => hs0 (hg.injOn hs h0 ?_)) hs0
      rw [h, hg.map_zero]

/-! ### `p(z) = z f'(z)/f(z)` -/

/-- `f(z) = z q(z)` with `q` holomorphic on the disc and `q(0) = f'(0) = 1` (`q` is the slope of `f` at `0`). -/
private lemma exists_factor_z {f : ℂ → ℂ} (hf : InS f) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball (0 : ℂ) 1) ∧ q 0 = 1 ∧ ∀ z, f z = z * q z := by
  refine ⟨dslope f 0, ?_, ?_, ?_⟩
  · exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hf.differentiableOn
  · rw [dslope_same, hf.deriv_zero]
  · intro z
    have h := sub_smul_dslope f 0 z
    rw [sub_zero, smul_eq_mul, hf.map_zero, sub_zero] at h
    exact h.symm

/-- The factor `q` of `f = z q` has no zero in the disc. -/
private lemma factor_ne_zero {f q : ℂ → ℂ} (hf : InS f) (hq0 : q 0 = 1) (hfq : ∀ z, f z = z * q z) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) : q z ≠ 0 := by
  by_cases hz0 : z = 0
  · rw [hz0, hq0]
    exact one_ne_zero
  · intro h
    apply hz0
    apply hf.injOn hz (by simp : (0 : ℂ) ∈ ball (0 : ℂ) 1)
    rw [hfq z, h, mul_zero, hf.map_zero]

/-- `f'(z) = q(z) + z q'(z)` for `f = z q`. -/
private lemma deriv_factor {f q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (ball (0 : ℂ) 1)) (hfq : ∀ z, f z = z * q z)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv f z = q z + z * deriv q z := by
  have hfeq : f = fun x => x * q x := funext hfq
  have h : HasDerivAt (fun x => x * q x) (1 * q z + z * deriv q z) z :=
    (hasDerivAt_id' z).mul (hq.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  rw [hfeq, h.deriv, one_mul]

/-- On the disc, `p(z) = 1 + z q'(z)/q(z)` (also at `z = 0`, where both sides are `1`). -/
private lemma pfun_eq {f q : ℂ → ℂ} (hf : InS f) (hq : DifferentiableOn ℂ q (ball (0 : ℂ) 1)) (hq0 : q 0 = 1)
    (hfq : ∀ z, f z = z * q z) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    pfun f z = 1 + z * deriv q z / q z := by
  have hqz := factor_ne_zero hf hq0 hfq hz
  by_cases hz0 : z = 0
  · simp [pfun, hz0]
  · simp only [pfun, hz0, ↓reduceIte]
    rw [deriv_factor hq hfq hz, hfq z]
    field_simp

/-- sec_03_tools.tex:49-51: `p` is holomorphic on `𝔻`, has no zero there, and `p(0) = 1`. -/
theorem sec3_p_ne_zero_proved (f : ℂ → ℂ) (hf : InS f) :
    DifferentiableOn ℂ (pfun f) (ball (0 : ℂ) 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, pfun f z ≠ 0) ∧ pfun f 0 = 1 := by
  obtain ⟨q, hq, hq0, hfq⟩ := exists_factor_z hf
  refine ⟨?_, ?_, by simp [pfun]⟩
  · have hrhs : DifferentiableOn ℂ (fun z => 1 + z * deriv q z / q z) (ball (0 : ℂ) 1) :=
      (differentiableOn_const 1).add ((differentiableOn_id.mul (hq.deriv isOpen_ball)).div hq
        (fun z hz => factor_ne_zero hf hq0 hfq hz))
    exact hrhs.congr (fun z hz => pfun_eq hf hq hq0 hfq hz)
  · intro z hz
    by_cases hz0 : z = 0
    · simp [pfun, hz0]
    · simp only [pfun, hz0, ↓reduceIte]
      have hfz : f z ≠ 0 := by
        intro h
        apply hz0
        apply hf.injOn hz (by simp : (0 : ℂ) ∈ ball (0 : ℂ) 1)
        rw [h, hf.map_zero]
      exact div_ne_zero (mul_ne_zero hz0 (sec3_deriv_ne_zero_proved f hf z hz)) hfz

/-! ### Section 4: the bounds on `c` -/

/-- `|c| ≤ 1` gives `e = 2(1 - Re c) ∈ [0, 4]` and `η = 1 - |c|² ∈ [0, 1]`. -/
private lemma e_eta_bounds {c : ℂ} (hc : ‖c‖ ≤ 1) :
    0 ≤ edef c ∧ edef c ≤ 4 ∧ 0 ≤ etadef c ∧ etadef c ≤ 1 := by
  have hre : |c.re| ≤ 1 := (abs_re_le_norm c).trans hc
  have hre' := abs_le.mp hre
  have hn := norm_nonneg c
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [edef, etadef] <;> nlinarith [hre'.1, hre'.2]

/-- sec_04_near.tex:53-60: for `f ∈ 𝒮` and `9/20 < τ < ½`, `f_{-τ} ∈ 𝒮`, `|A| ≤ 2` (de Branges, `n = 2`),
`|c| ≤ 1`, `e ∈ [0, 4]`, `η ∈ [0, 1]`. -/
theorem sec4_c_bounds_proved (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 < τ)
    (h2 : τ < 1 / 2) :
    InS (koebeTransform f (-(τ : ℂ))) ∧ ‖coeff (koebeTransform f (-(τ : ℂ))) 2‖ ≤ 2 ∧
      ‖coeff (koebeTransform f (-(τ : ℂ))) 2 / 2‖ ≤ 1 ∧
      0 ≤ edef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ∧ edef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ≤ 4 ∧
      0 ≤ etadef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ∧
      etadef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ≤ 1 := by
  have hτ : -(τ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hS := sec3_koebe_transform_mem_S_proved f hf _ hτ
  have hA : ‖coeff (koebeTransform f (-(τ : ℂ))) 2‖ ≤ 2 := by
    have := hDB _ hS 2 le_rfl
    simpa using this
  have hc : ‖coeff (koebeTransform f (-(τ : ℂ))) 2 / 2‖ ≤ 1 := by
    rw [norm_div]
    have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2n]
    linarith
  obtain ⟨he0, he4, hη0, hη1⟩ := e_eta_bounds hc
  exact ⟨hS, hA, hc, he0, he4, hη0, hη1⟩

end Robinson.Proofs
