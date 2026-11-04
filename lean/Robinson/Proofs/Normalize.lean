/-
Robinson/Proofs/Normalize.lean — proofs of lem_2_3_rot and lem_2_3_dil.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Basic

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Common facts -/

/-- A function of the class `𝒮` has a derivative at every point of the open unit disc. -/
private lemma hasDerivAt_of_mem_ball {f : ℂ → ℂ} (hf : InS f) {p : ℂ} (hp : p ∈ ball (0 : ℂ) 1) :
    HasDerivAt f (deriv f p) p :=
  (hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hp)).hasDerivAt

/-- The linear map `x ↦ b x` has derivative `b`. -/
private lemma hasDerivAt_const_mul_id (b z : ℂ) : HasDerivAt (fun x : ℂ => b * x) b z := by
  have h := (hasDerivAt_id' z).const_mul b
  rwa [mul_one] at h

/-- The origin lies in the open unit disc. -/
private lemma zero_mem_ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
  simp

/-- `x / (c⁻¹ y) = c x / y` for all complex numbers (also when `c = 0` or `y = 0`). -/
private lemma div_inv_mul_eq (x y c : ℂ) : x / (c⁻¹ * y) = c * x / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- `x / (y / s) = s x / y` for all complex numbers (also when `s = 0` or `y = 0`). -/
private lemma div_div_eq_mul_div' (x y s : ℂ) : x / (y / s) = s * x / y := by
  rw [div_div_eq_mul_div]
  ring

/-! ### The rotation `f_φ(z) = e^{-iφ} f(e^{iφ} z)` -/

/-- `|e^{iφ} z| = |z|`, so `e^{iφ} z` lies in the disc when `z` does. -/
private lemma rot_mem_ball (φ : ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    exp ((φ : ℂ) * I) * z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hz ⊢
  rwa [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `f_φ'(z) = e^{-iφ} f'(e^{iφ} z) e^{iφ} = f'(e^{iφ} z)` for `z` in the disc. -/
private lemma rotate_hasDerivAt {f : ℂ → ℂ} (hf : InS f) (φ : ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasDerivAt (rotate φ f) (deriv f (exp ((φ : ℂ) * I) * z)) z := by
  have h := ((hasDerivAt_of_mem_ball hf (rot_mem_ball φ hz)).comp z
    (hasDerivAt_const_mul_id (exp ((φ : ℂ) * I)) z)).const_mul (exp (-((φ : ℂ) * I)))
  have hc : exp (-((φ : ℂ) * I)) * (deriv f (exp ((φ : ℂ) * I) * z) * exp ((φ : ℂ) * I))
      = deriv f (exp ((φ : ℂ) * I) * z) := by
    rw [Complex.exp_neg, mul_comm (deriv f _), ← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _),
      one_mul]
  rw [hc] at h
  exact h

/-- The rotation of a function of the class `𝒮` belongs to `𝒮`. -/
private lemma rotate_inS {f : ℂ → ℂ} (hf : InS f) (φ : ℝ) : InS (rotate φ f) where
  differentiableOn := fun _ hz => (rotate_hasDerivAt hf φ hz).differentiableAt.differentiableWithinAt
  injOn := by
    intro z hz w hw hzw
    simp only [rotate] at hzw
    have h1 : f (exp ((φ : ℂ) * I) * z) = f (exp ((φ : ℂ) * I) * w) :=
      mul_left_cancel₀ (Complex.exp_ne_zero _) hzw
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) (hf.injOn (rot_mem_ball φ hz) (rot_mem_ball φ hw) h1)
  map_zero := by
    simp only [rotate, mul_zero, hf.map_zero]
  deriv_zero := by
    rw [(rotate_hasDerivAt hf φ zero_mem_ball).deriv, mul_zero, hf.deriv_zero]

/-- The factor `e^{-iφ}` cancels in `Q`: `Q_{f_φ}(z, w) = Q_f(e^{iφ} z, e^{iφ} w)`. -/
private lemma rotate_Q {f : ℂ → ℂ} (hf : InS f) (φ : ℝ) {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (hw : w ∈ ball (0 : ℂ) 1) :
    Q (rotate φ f) z w = Q f (exp ((φ : ℂ) * I) * z) (exp ((φ : ℂ) * I) * w) := by
  simp only [Q]
  rw [(rotate_hasDerivAt hf φ hz).deriv, (rotate_hasDerivAt hf φ hw).deriv]
  simp only [rotate]
  rw [Complex.exp_neg, ← mul_sub, div_inv_mul_eq]
  ring

/-! ### The dilation `F(u) = f(2ru) / (2r)` -/

/-- For `0 < r ≤ ½` and `|u| < 1`: `|2ru| < 1`. -/
private lemma dil_mem_ball {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) :
    2 * (r : ℂ) * u ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hu ⊢
  have h2r : ‖2 * (r : ℂ)‖ = 2 * r := by
    have : (2 * (r : ℂ)) = ((2 * r : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_of_nonneg (by linarith)]
  rw [norm_mul, h2r]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * r) (norm_nonneg u)]

/-- `2r ≠ 0` for `r > 0`. -/
private lemma two_r_ne_zero {r : ℝ} (hr : 0 < r) : (2 * (r : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (by exact_mod_cast hr.ne')

/-- `F'(u) = f'(2ru) (2r) / (2r) = f'(2ru)` for `u` in the disc. -/
private lemma dilate_hasDerivAt {f : ℂ → ℂ} (hf : InS f) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) 1) : HasDerivAt (dilate r f) (deriv f (2 * (r : ℂ) * u)) u := by
  have h := ((hasDerivAt_of_mem_ball hf (dil_mem_ball hr hr' hu)).comp u
    (hasDerivAt_const_mul_id (2 * (r : ℂ)) u)).div_const (2 * (r : ℂ))
  have hc : deriv f (2 * (r : ℂ) * u) * (2 * (r : ℂ)) / (2 * (r : ℂ)) = deriv f (2 * (r : ℂ) * u) :=
    mul_div_cancel_right₀ _ (two_r_ne_zero hr)
  rw [hc] at h
  exact h

/-- The dilation of a function of the class `𝒮` by `0 < r ≤ ½` belongs to `𝒮`. -/
private lemma dilate_inS {f : ℂ → ℂ} (hf : InS f) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) :
    InS (dilate r f) where
  differentiableOn := fun _ hu =>
    (dilate_hasDerivAt hf hr hr' hu).differentiableAt.differentiableWithinAt
  injOn := by
    intro z hz w hw hzw
    simp only [dilate] at hzw
    have h1 : f (2 * (r : ℂ) * z) = f (2 * (r : ℂ) * w) :=
      (div_left_inj' (two_r_ne_zero hr)).mp hzw
    exact mul_left_cancel₀ (two_r_ne_zero hr) (hf.injOn (dil_mem_ball hr hr' hz) (dil_mem_ball hr hr' hw) h1)
  map_zero := by
    simp only [dilate, mul_zero, hf.map_zero, zero_div]
  deriv_zero := by
    rw [(dilate_hasDerivAt hf hr hr' zero_mem_ball).deriv, mul_zero, hf.deriv_zero]

/-- The factor `1/(2r)` cancels in `Q`: `Q_F(z, w) = Q_f(2rz, 2rw)`. -/
private lemma dilate_Q {f : ℂ → ℂ} (hf : InS f) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    Q (dilate r f) z w = Q f (2 * (r : ℂ) * z) (2 * (r : ℂ) * w) := by
  simp only [Q]
  rw [(dilate_hasDerivAt hf hr hr' hz).deriv, (dilate_hasDerivAt hf hr hr' hw).deriv]
  simp only [dilate]
  rw [← sub_div, div_div_eq_mul_div']
  ring

/-! ### Lemma 2.3 -/

/-- Lemma 2.3, rotation: for `f ∈ 𝒮` and real `φ`, `f_φ ∈ 𝒮` and `Q_{f_φ}(z, w) = Q_f(e^{iφ} z, e^{iφ} w)`
for all `z, w` in the open unit disc. -/
theorem lem_2_3_rot_proved (f : ℂ → ℂ) (hf : InS f) (φ : ℝ) :
    InS (rotate φ f) ∧ ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
      Q (rotate φ f) z w = Q f (exp ((φ : ℂ) * I) * z) (exp ((φ : ℂ) * I) * w) :=
  ⟨rotate_inS hf φ, fun _ _ hz hw => rotate_Q hf φ hz hw⟩

/-- Lemma 2.3, dilation: for `f ∈ 𝒮` and `0 < r ≤ ½`, `F(u) = f(2ru)/(2r)` belongs to `𝒮` and
`Q_F(z, w) = Q_f(2rz, 2rw)` for all `z, w` in the open unit disc. -/
theorem lem_2_3_dil_proved (f : ℂ → ℂ) (hf : InS f) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1 / 2) :
    InS (dilate r f) ∧ ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
      Q (dilate r f) z w = Q f (2 * (r : ℂ) * z) (2 * (r : ℂ) * w) :=
  ⟨dilate_inS hf hr hr', fun _ _ hz hw => dilate_Q hf hr hr' hz hw⟩

end Robinson.Proofs
