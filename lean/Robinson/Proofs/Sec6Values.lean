/-
Robinson/Proofs/Sec6Values.lean — proofs of sec6_ZO_re_im, sec6_b_values, sec6_A0B0_closed,
sec6_value_180, sec6_A0_printed.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Matrix2
import Robinson.Defs.Far
import Robinson.Proofs.Arith

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## Angles: `θ ∈ [135°, 180°]` lies in `[0, π]` -/

private lemma theta_range {θ : ℝ} (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) : 0 ≤ θ ∧ θ ≤ Real.pi := by
  unfold deg at h1 h2
  have := Real.pi_pos
  constructor <;> linarith

/-! ## `Z_o = artanh z_θ` in closed form -/

/-- `z_θ = ½ (cos(θ/2) + i sin(θ/2))`. -/
private lemma zθ_eq_mk (θ : ℝ) : zθ θ = ⟨Real.cos (θ / 2) / 2, Real.sin (θ / 2) / 2⟩ := by
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  apply Complex.ext
  · rw [zθ, hhalf, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    dsimp only
    ring
  · rw [zθ, hhalf, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    dsimp only
    ring

/-- For `c² + s² = 1` and `z = (c + is)/2`: `(1 + z)/(1 - z) = (3 + 4is)/(5 - 4c)`. -/
private lemma w_eq (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (1 + (⟨c / 2, s / 2⟩ : ℂ)) / (1 - ⟨c / 2, s / 2⟩) = ⟨3 / (5 - 4 * c), 4 * s / (5 - 4 * c)⟩ := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  have h5 : (5 - 4 * c) ≠ 0 := (by linarith : (0 : ℝ) < 5 - 4 * c).ne'
  have hne : (1 - (⟨c / 2, s / 2⟩ : ℂ)) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  rw [div_eq_iff hne]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.add_re]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div, eq_div_iff h5]
    linear_combination (-2) * hcs
  · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.add_im]
    field_simp
    ring

/-- For `Re x > 0`: `arg x = arctan (Im x / Re x)`. -/
private lemma arg_eq_arctan_of_re_pos {x : ℂ} (hx : 0 < x.re) : Complex.arg x = Real.arctan (x.im / x.re) := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  rw [abs_lt] at h
  rw [← Complex.tan_arg, Real.arctan_tan h.1 h.2]

/-- The real and imaginary parts of `½ log ((3 + 4is)/(5 - 4c))` for `c, s ≥ 0`, `c² + s² = 1`. -/
private lemma half_log_w (c s : ℝ) (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((1 / 2 : ℂ) * log ⟨3 / (5 - 4 * c), 4 * s / (5 - 4 * c)⟩).re = uo c ∧
      ((1 / 2 : ℂ) * log ⟨3 / (5 - 4 * c), 4 * s / (5 - 4 * c)⟩).im = vo c := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  have h5 : (0 : ℝ) < 5 - 4 * c := by linarith
  have hs_eq : s = Real.sqrt (1 - c ^ 2) := by
    rw [← Real.sqrt_sq hs0]
    congr 1
    linarith
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.log_re, Complex.log_im]
  constructor
  · have hn2 : ‖(⟨3 / (5 - 4 * c), 4 * s / (5 - 4 * c)⟩ : ℂ)‖ ^ 2 = (1 + 4 * c / 5) / (1 - 4 * c / 5) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp only
      rw [div_mul_div_comm, div_mul_div_comm, ← add_div,
        div_eq_div_iff (mul_pos h5 h5).ne' (by linarith : (0 : ℝ) < 1 - 4 * c / 5).ne']
      linear_combination (16 / 5 * (5 - 4 * c)) * hcs
    have hlog : Real.log ‖(⟨3 / (5 - 4 * c), 4 * s / (5 - 4 * c)⟩ : ℂ)‖ =
        1 / 2 * Real.log ((1 + 4 * c / 5) / (1 - 4 * c / 5)) := by
      rw [← hn2, Real.log_pow]
      push_cast
      ring
    rw [hlog, uo, Real.artanh_eq_half_log ⟨by linarith, by linarith⟩]
  · have hq : (4 * s / (5 - 4 * c)) / (3 / (5 - 4 * c)) = 4 / 3 * s := by
      rw [div_div_div_cancel_right₀ h5.ne']
      ring
    have harg : Complex.arg (⟨3 / (5 - 4 * c), 4 * s / (5 - 4 * c)⟩ : ℂ) = Real.arctan (4 / 3 * s) := by
      rw [arg_eq_arctan_of_re_pos (by dsimp only; exact div_pos (by norm_num) h5)]
      dsimp only
      rw [hq]
    rw [harg, vo, ← hs_eq]

theorem sec6_ZO_re_im_proved (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (Zo θ).re = uo (Real.cos (θ / 2)) ∧ (Zo θ).im = vo (Real.cos (θ / 2)) := by
  have hc0 : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hcs : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hZo : Zo θ = (1 / 2 : ℂ) *
      log ⟨3 / (5 - 4 * Real.cos (θ / 2)), 4 * Real.sin (θ / 2) / (5 - 4 * Real.cos (θ / 2))⟩ := by
    rw [Zo, cartanh, zθ_eq_mk, w_eq _ _ hcs]
  rw [hZo]
  exact half_log_w _ _ hc0 hs0 hcs

/-! ## Lemma 6.4's parametrization: `e^{-iε}`, `z²`, `A_R`, `B_R` -/

/-- The real and imaginary parts of `e^{-iε} = 1 - 2c² - 2ic√(1 - c²)`. -/
private lemma emeps_re_im (c : ℝ) :
    (emeps c).re = 1 - 2 * c ^ 2 ∧ (emeps c).im = -(2 * (c * Real.sqrt (1 - c ^ 2))) := by
  constructor
  · simp [emeps]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  · simp [emeps]
    rw [← Complex.ofReal_pow, Complex.ofReal_im]

/-- `e^{-iε} = e^{-i(π - θ)} = 1 - 2c² - 2ic√(1 - c²)` for `c = cos(θ/2)`, `θ ∈ [0, π]`. -/
private lemma emeps_eq (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    emeps (Real.cos (θ / 2)) = exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) := by
  have hs : Real.sin (θ / 2) = Real.sqrt (1 - Real.cos (θ / 2) ^ 2) :=
    Real.sin_eq_sqrt_one_sub_cos_sq (by linarith) (by linarith)
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    congr 1
    ring
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]
    congr 1
    ring
  have harg : -(((Real.pi - θ : ℝ) : ℂ) * I) = ((θ - Real.pi : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [harg]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_sub_pi, hcos, (emeps_re_im _).1]
    ring
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_sub_pi, hsin, hs, (emeps_re_im _).2]
    ring

/-- `z_θ² = ¼ e^{iθ} = -x e^{-i(π - θ)}` with `x = ¼`. -/
private lemma zθ_sq_eq (θ : ℝ) : zθ θ ^ 2 = -(xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) := by
  have e1 : exp (((θ / 2 : ℝ) : ℂ) * I) ^ 2 = exp ((θ : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e2 : exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) = -exp ((θ : ℂ) * I) := by
    rw [show -(((Real.pi - θ : ℝ) : ℂ) * I) = (θ : ℂ) * I - (Real.pi : ℂ) * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]
  rw [zθ, mul_pow, e1, e2, xfar]
  push_cast
  ring

/-- `-(1/4)/(1 + e/4)² = -4/(4 + e)²` (both sides are `0` when `4 + e = 0`). -/
private lemma quarter_form (e : ℂ) : -(1 / 4 : ℂ) / (1 + 1 / 4 * e) ^ 2 = -4 / (4 + e) ^ 2 := by
  have h : (1 + 1 / 4 * e) ^ 2 = (4 + e) ^ 2 / 16 := by ring
  rw [h, div_div_eq_mul_div]
  ring

/-- `A_R = Re(-4/(4 + e^{-iε})²)`, for every `c` (Lean's `A0` is `Re(-x/(1 + x e^{-iε})²)` with `x = ¼`). -/
theorem sec6_A0_printed_proved (c : ℝ) : A0 c = (-4 / (4 + emeps c) ^ 2).re := by
  have h := quarter_form (emeps c)
  unfold A0 xfar
  congr 1
  push_cast
  linear_combination h

theorem sec6_A0B0_closed_proved (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    emeps (Real.cos (θ / 2)) = exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) ∧
      zθ θ ^ 2 = -(xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) ∧
      A0 (Real.cos (θ / 2)) = (exp (((Real.pi - θ : ℝ) : ℂ) * I) * (zθ θ ^ 2 / (1 - zθ θ ^ 2) ^ 2)).re ∧
      B0 (Real.cos (θ / 2)) = (exp (((Real.pi - θ : ℝ) : ℂ) * I) * (-log (1 - zθ θ ^ 2))).re := by
  obtain ⟨h0, hπ⟩ := theta_range h1 h2
  have hE := emeps_eq θ h0 hπ
  have hz := zθ_sq_eq θ
  refine ⟨hE, hz, ?_, ?_⟩
  · rw [A0, hE, hz]
    congr 1
    have hinv : exp (((Real.pi - θ : ℝ) : ℂ) * I) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) = 1 := by
      rw [← Complex.exp_add]
      simp
    have h1' : (1 : ℂ) - -(xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) =
        1 + (xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) := by ring
    rw [h1']
    calc -(xfar : ℂ) / (1 + (xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I))) ^ 2
        = (exp (((Real.pi - θ : ℝ) : ℂ) * I) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I))) *
            (-(xfar : ℂ) / (1 + (xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I))) ^ 2) := by
          rw [hinv, one_mul]
      _ = exp (((Real.pi - θ : ℝ) : ℂ) * I) * (-(xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) /
            (1 + (xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I))) ^ 2) := by ring
  · rw [B0, hE, hz]
    congr 1
    have h1' : (1 : ℂ) - -(xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) =
        1 + (xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) := by ring
    rw [h1', Complex.exp_neg (((Real.pi - θ : ℝ) : ℂ) * I), inv_inv]
    ring

/-! ## The value of Lemma 6.4's function at `θ = 180°` (`c = 0`) -/

private lemma emeps_zero : emeps 0 = 1 := by
  simp [emeps]

private lemma A0_zero : A0 0 = -4 / 25 := by
  rw [A0, emeps_zero, xfar]
  have h : (-((1 / 4 : ℝ) : ℂ) / (1 + ((1 / 4 : ℝ) : ℂ) * 1) ^ 2) = ((-4 / 25 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [h, Complex.ofReal_re]

private lemma B0_zero : B0 0 = -Real.log (5 / 4) := by
  rw [B0, emeps_zero, xfar]
  have h : (1 : ℂ) + ((1 / 4 : ℝ) : ℂ) * 1 = ((5 / 4 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [h, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  simp

/-- `R(0) = √((64/225) log(16/15)) + √((136/225) log(5/3))`. -/
private lemma Rbound_zero :
    Rbound 0 = Real.sqrt (64 / 225 * Real.log (16 / 15)) + Real.sqrt (136 / 225 * Real.log (5 / 3)) := by
  have hp : U0 + A0 0 = 64 / 225 := by
    rw [A0_zero, U0]
    norm_num
  have hm : U0 - A0 0 = 136 / 225 := by
    rw [A0_zero, U0]
    norm_num
  have lp : V0 + B0 0 = Real.log (16 / 15) := by
    rw [B0_zero, V0, ← sub_eq_add_neg,
      ← Real.log_div (x := 4 / 3) (y := 5 / 4) (by norm_num) (by norm_num)]
    norm_num
  have lm : V0 - B0 0 = Real.log (5 / 3) := by
    rw [B0_zero, V0, sub_neg_eq_add, ← Real.log_mul (x := 4 / 3) (y := 5 / 4) (by norm_num) (by norm_num)]
    norm_num
  rw [Rbound, hp, hm, lp, lm]

/-- `0.0645385 < log(16/15) < 0.0645386`, from `log(16/15) = -log(1 - 1/16)` and six terms of the series. -/
private lemma log_16_15_bounds :
    (645385 / 10 ^ 7 : ℝ) < Real.log (16 / 15) ∧ Real.log (16 / 15) < 645386 / 10 ^ 7 := by
  have hx : |(1 / 16 : ℝ)| = 1 / 16 := abs_of_pos (by norm_num)
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 16) (by rw [hx]; norm_num) 6
  have e : Real.log (1 - 1 / 16) = -Real.log (16 / 15) := by
    rw [show (1 : ℝ) - 1 / 16 = (16 / 15)⁻¹ by norm_num, Real.log_inv]
  rw [e, hx, abs_le] at h
  generalize Real.log (16 / 15) = y at h ⊢
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

/-- `0.5108255 < log(5/3) < 0.5108258`, from `log(5/3) = log 2 + log(1 - 1/6)`. -/
private lemma log_5_3_bounds :
    (5108255 / 10 ^ 7 : ℝ) < Real.log (5 / 3) ∧ Real.log (5 / 3) < 5108258 / 10 ^ 7 := by
  have hx : |(1 / 6 : ℝ)| = 1 / 6 := abs_of_pos (by norm_num)
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 6) (by rw [hx]; norm_num) 10
  have e : Real.log (5 / 3) = Real.log 2 + Real.log (1 - 1 / 6) := by
    rw [← Real.log_mul (x := 2) (y := 1 - 1 / 6) (by norm_num) (by norm_num)]
    norm_num
  rw [hx, abs_le] at h
  rw [e]
  generalize Real.log (1 - 1 / 6) = y at h ⊢
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  norm_num at l2 l2'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

theorem sec6_value_180_proved : 0.69115 < Rbound 0 ∧ Rbound 0 < 0.69125 := by
  rw [Rbound_zero]
  obtain ⟨l1, u1⟩ := log_16_15_bounds
  obtain ⟨l2, u2⟩ := log_5_3_bounds
  have a1 : (135490 / 10 ^ 6 : ℝ) < Real.sqrt (64 / 225 * Real.log (16 / 15)) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
    linarith
  have a2 : (555666 / 10 ^ 6 : ℝ) < Real.sqrt (136 / 225 * Real.log (5 / 3)) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
    linarith
  have b1 : Real.sqrt (64 / 225 * Real.log (16 / 15)) < 13550 / 10 ^ 5 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
    linarith
  have b2 : Real.sqrt (136 / 225 * Real.log (5 / 3)) < 55570 / 10 ^ 5 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
    linarith
  constructor
  · rw [show (0.69115 : ℝ) = 13823 / 20000 by norm_num]
    linarith
  · rw [show (0.69125 : ℝ) = 553 / 800 by norm_num]
    linarith

/-! ## The numbers `b₁, b₂, b₃` of Lemma 6.2 -/

/-- `log 3 > 1.097`, from `log 3 = log 2 - log(1 - 1/3)`. -/
private lemma log_three_gt : (1097 / 1000 : ℝ) < Real.log 3 := by
  have hx : |(1 / 3 : ℝ)| = 1 / 3 := abs_of_pos (by norm_num)
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 3) (by rw [hx]; norm_num) 8
  have e : Real.log 3 = Real.log 2 - Real.log (1 - 1 / 3) := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, Real.log_div (x := 2) (y := 3) (by norm_num) (by norm_num)]
    ring
  rw [hx, abs_le] at h
  rw [e]
  generalize Real.log (1 - 1 / 3) = y at h ⊢
  have l2 := Real.log_two_gt_d9
  norm_num at l2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith [h.1, h.2]

/-- `arctan(4/3) < 1`, because `tan 1 = sin 1 / cos 1 > (5/6) / (53/96) > 4/3`. -/
private lemma arctan_four_thirds_lt_one : Real.arctan (4 / 3) < 1 := by
  have hc := Real.cos_bound (x := 1) (by norm_num)
  have hs := Real.sin_gt_sub_cube (x := 1) (by norm_num)
  have hcpos := Real.cos_one_pos
  obtain ⟨_, hc2⟩ := abs_le.mp hc
  norm_num at hc2 hs
  have htan : (4 / 3 : ℝ) < Real.tan 1 := by
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcpos]
    linarith
  have hpi := Real.pi_gt_three
  calc Real.arctan (4 / 3) < Real.arctan (Real.tan 1) := Real.arctan_strictMono htan
    _ = 1 := Real.arctan_tan (by linarith) (by linarith)

/-- For `0 ≤ c < 383/1000`: `0 ≤ 2u_o(c) = artanh(4c/5) < 9/20` (via `log y ≤ y - 1`). -/
private lemma two_uo_bounds (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 383 / 1000) :
    0 ≤ 2 * uo c ∧ 2 * uo c < 9 / 20 := by
  have hx0 : 0 ≤ 4 * c / 5 := by positivity
  have hx1 : 4 * c / 5 < 1 := by linarith
  have h2u : 2 * uo c = Real.artanh (4 * c / 5) := by
    rw [uo]
    ring
  rw [h2u]
  refine ⟨Real.artanh_nonneg hx0, ?_⟩
  rw [Real.artanh_eq_half_log ⟨by linarith, hx1.le⟩]
  have hd : (0 : ℝ) < 1 - 4 * c / 5 := by linarith
  have hpos : 0 < (1 + 4 * c / 5) / (1 - 4 * c / 5) := div_pos (by linarith) hd
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hq : (1 + 4 * c / 5) / (1 - 4 * c / 5) - 1 < 9 / 10 := by
    rw [div_sub_one hd.ne', div_lt_iff₀ hd]
    linarith
  linarith

/-- `0 ≤ 2v_o(c) = arctan((4/3)√(1 - c²)) < 1`. -/
private lemma two_vo_bounds (c : ℝ) : 0 ≤ 2 * vo c ∧ 2 * vo c < 1 := by
  have h2v : 2 * vo c = Real.arctan (4 / 3 * Real.sqrt (1 - c ^ 2)) := by
    rw [vo]
    ring
  have hs0 : 0 ≤ Real.sqrt (1 - c ^ 2) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (1 - c ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg c])
  rw [h2v]
  refine ⟨Real.arctan_nonneg.mpr (by positivity), ?_⟩
  calc Real.arctan (4 / 3 * Real.sqrt (1 - c ^ 2)) ≤ Real.arctan (4 / 3) :=
        Real.arctan_strictMono.monotone (by nlinarith)
    _ < 1 := arctan_four_thirds_lt_one

/-- The algebra behind Lemma 6.2's numbers: with `L = 2A`, `r cos φ = u`, `r sin φ = v`, `4u² + 4v² < L²` and
`d = 4√(((A + r)/2)((A - r)/2))`, one has `d² = L² - 4u² - 4v²` and the stated identities. -/
private lemma b_core (L A r φ u v d : ℝ) (hLA : L = 2 * A) (hL0 : 0 < L)
    (hrc : r * Real.cos φ = u) (hrs : r * Real.sin φ = v) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hlt : 4 * u ^ 2 + 4 * v ^ 2 < L ^ 2)
    (hd : d = 4 * Real.sqrt ((A + r) / 2 * ((A - r) / 2))) :
    0 < Real.sqrt (L ^ 2 - 4 * u ^ 2) ∧
      Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2) = Real.sqrt (L ^ 2 - 4 * u ^ 2) ∧
      (L ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / Real.sqrt (L ^ 2 - 4 * u ^ 2) =
        4 * u * v / Real.sqrt (L ^ 2 - 4 * u ^ 2) ∧
      L * d / Real.sqrt (L ^ 2 - 4 * u ^ 2) =
        L * Real.sqrt (L ^ 2 - 4 * u ^ 2 - 4 * v ^ 2) / Real.sqrt (L ^ 2 - 4 * u ^ 2) ∧
      0 ≤ 4 * u * v / Real.sqrt (L ^ 2 - 4 * u ^ 2) ∧
      0 ≤ L * Real.sqrt (L ^ 2 - 4 * u ^ 2 - 4 * v ^ 2) / Real.sqrt (L ^ 2 - 4 * u ^ 2) ∧
      Real.sqrt (L ^ 2 - 4 * u ^ 2) ≤ L := by
  have hsc := Real.sin_sq_add_cos_sq φ
  have hr2 : r ^ 2 = u ^ 2 + v ^ 2 := by
    rw [← hrc, ← hrs]
    linear_combination (-r ^ 2) * hsc
  have hX : (A + r) / 2 * ((A - r) / 2) = (L ^ 2 - 4 * u ^ 2 - 4 * v ^ 2) / 16 := by
    rw [hLA]
    linear_combination (-1 / 4) * hr2
  have hXnn : 0 ≤ (A + r) / 2 * ((A - r) / 2) := by
    rw [hX]
    linarith
  have hd0 : 0 ≤ d := by
    rw [hd]
    positivity
  have hd2 : d ^ 2 = L ^ 2 - 4 * u ^ 2 - 4 * v ^ 2 := by
    rw [hd, mul_pow, Real.sq_sqrt hXnn, hX]
    ring
  have hd' : d = Real.sqrt (L ^ 2 - 4 * u ^ 2 - 4 * v ^ 2) := by
    rw [← hd2, Real.sqrt_sq hd0]
  have hb : 0 < Real.sqrt (L ^ 2 - 4 * u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg v])
  refine ⟨hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · congr 1
    rw [hd2, ← hrc, ← hrs]
    linear_combination (L ^ 2 - 4 * r ^ 2 * Real.cos φ ^ 2) * hsc
  · congr 1
    rw [hd2, ← hrc, ← hrs]
    linear_combination (4 * r ^ 2 * Real.sin φ * Real.cos φ) * hsc
  · rw [hd']
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu0) hv0) hb.le
  · exact div_nonneg (mul_nonneg hL0.le (Real.sqrt_nonneg _)) hb.le
  · calc Real.sqrt (L ^ 2 - 4 * u ^ 2) ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
      _ = L := Real.sqrt_sq hL0.le

theorem sec6_b_values_proved (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    let φ := Complex.arg (Zo θ)
    let d := 4 * Real.sqrt ((Ao + ‖Zo θ‖) / 2 * ((Ao - ‖Zo θ‖) / 2))
    let c := Real.cos (θ / 2)
    0 < b1 c ∧ Real.sqrt (Llog3 ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2) = b1 c ∧
      (Llog3 ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / b1 c = b2 c ∧ Llog3 * d / b1 c = b3 c ∧
      0 ≤ b2 c ∧ 0 ≤ b3 c ∧ b1 c ≤ Llog3 ∧ Llog3 < Real.pi / 2 := by
  intro φ d c
  obtain ⟨h0, hπ⟩ := theta_range h1 h2
  obtain ⟨hre, him⟩ := sec6_ZO_re_im_proved θ h0 hπ
  obtain ⟨hAo, hL, hLpi⟩ := sec6_L_log3_proved
  obtain ⟨hc0, hcs, hs383⟩ := sec6_c_bound_proved θ h1 h2
  have hL3 := log_three_gt
  have hLA : Llog3 = 2 * Ao := by rw [hL, hAo]
  have hL0 : 0 < Llog3 := by rw [hL]; linarith
  have hu := two_uo_bounds c hc0 (by linarith)
  have hv := two_vo_bounds c
  have hlt : 4 * uo c ^ 2 + 4 * vo c ^ 2 < Llog3 ^ 2 := by
    rw [hL]
    nlinarith [mul_self_lt_mul_self hu.1 hu.2, mul_self_lt_mul_self hv.1 hv.2,
      mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1097 / 1000) hL3]
  have hrc : ‖Zo θ‖ * Real.cos φ = uo c := (Complex.norm_mul_cos_arg _).trans hre
  have hrs : ‖Zo θ‖ * Real.sin φ = vo c := (Complex.norm_mul_sin_arg _).trans him
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ :=
    b_core Llog3 Ao ‖Zo θ‖ φ (uo c) (vo c) d hLA hL0 hrc hrs (by linarith [hu.1]) (by linarith [hv.1]) hlt rfl
  exact ⟨k1, k2, k3, k4, k5, k6, k7, hLpi⟩

end Robinson.Proofs
