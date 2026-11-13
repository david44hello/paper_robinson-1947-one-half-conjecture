/-
Robinson/Proofs/Sec6PhiD.lean — the reasons for `b₁ ≤ L` in Section 6 (sec6_phi_d_range): `z_θ` in the closed
first quadrant, `0 ≤ φ ≤ π/2`, and `d ≤ 2(σ₊ + σ₋) = L`.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Proofs.Sec6Values

namespace Robinson.Proofs

open Robinson Complex

/-- `z_θ = ½ e^{iθ/2} = ½ cos(θ/2) + i ½ sin(θ/2)`. -/
lemma phiD_zθ_re_im (θ : ℝ) : (zθ θ).re = 1 / 2 * Real.cos (θ / 2) ∧ (zθ θ).im = 1 / 2 * Real.sin (θ / 2) := by
  have hz : zθ θ = ((1 / 2 * Real.cos (θ / 2) : ℝ) : ℂ) + ((1 / 2 * Real.sin (θ / 2) : ℝ) : ℂ) * I := by
    rw [zθ, Complex.exp_mul_I]
    push_cast
    ring
  rw [hz]
  constructor <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;>
    ring

/-- For `θ ∈ [135°, 180°]`: `Re Z_o = u_o(c) ≥ 0` and `Im Z_o = v_o(c) ≥ 0`, `c = cos(θ/2) ≥ 0`. -/
lemma phiD_Zo_nonneg (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) : 0 ≤ (Zo θ).re ∧ 0 ≤ (Zo θ).im := by
  have hθ0 : 0 ≤ θ := by unfold deg at h1; linarith [Real.pi_pos]
  have hθπ : θ ≤ Real.pi := by unfold deg at h2; linarith
  obtain ⟨hc0, -, -⟩ := sec6_c_bound_proved θ h1 h2
  obtain ⟨hre, him⟩ := sec6_ZO_re_im_proved θ hθ0 hθπ
  rw [hre, him, uo, vo]
  constructor
  · have := Real.artanh_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.cos (θ / 2) / 5)
    linarith
  · have := Real.arctan_nonneg.mpr (by positivity : (0 : ℝ) ≤ 4 / 3 * Real.sqrt (1 - Real.cos (θ / 2) ^ 2))
    linarith

/-- AM-GM: `4√(σ₊σ₋) ≤ 2(σ₊ + σ₋)` when `σ₊ + σ₋ ≥ 0`. -/
lemma phiD_amgm (a b : ℝ) (hab : 0 ≤ a + b) : 4 * Real.sqrt (a * b) ≤ 2 * (a + b) := by
  have h := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)] : a * b ≤ ((a + b) / 2) ^ 2)
  rw [Real.sqrt_sq (by linarith)] at h
  linarith

/-- sec6_phi_d_range: for `θ ∈ [135°, 180°]`, `z_θ` lies in the closed first quadrant, `φ = arg Z_o ∈ [0, π/2]`,
and with `σ± = (A_o ± |Z_o|)/2`, `d = 4√(σ₊σ₋)`: `d ≤ 2(σ₊ + σ₋) = L`. -/
theorem sec6_phi_d_range_proved (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    let φ := Complex.arg (Zo θ)
    let σp := (Ao + ‖Zo θ‖) / 2
    let σm := (Ao - ‖Zo θ‖) / 2
    let d := 4 * Real.sqrt (σp * σm)
    0 ≤ (zθ θ).re ∧ 0 ≤ (zθ θ).im ∧ 0 ≤ φ ∧ φ ≤ Real.pi / 2 ∧
      d ≤ 2 * (σp + σm) ∧ 2 * (σp + σm) = Llog3 := by
  show 0 ≤ (zθ θ).re ∧ 0 ≤ (zθ θ).im ∧ 0 ≤ Complex.arg (Zo θ) ∧ Complex.arg (Zo θ) ≤ Real.pi / 2 ∧
      4 * Real.sqrt ((Ao + ‖Zo θ‖) / 2 * ((Ao - ‖Zo θ‖) / 2)) ≤ 2 * ((Ao + ‖Zo θ‖) / 2 + (Ao - ‖Zo θ‖) / 2) ∧
      2 * ((Ao + ‖Zo θ‖) / 2 + (Ao - ‖Zo θ‖) / 2) = Llog3
  have hθ0 : 0 ≤ θ := by unfold deg at h1; linarith [Real.pi_pos]
  have hθπ : θ ≤ Real.pi := by unfold deg at h2; linarith
  obtain ⟨hzre, hzim⟩ := phiD_zθ_re_im θ
  obtain ⟨hre, him⟩ := phiD_Zo_nonneg θ h1 h2
  obtain ⟨hAo, hL, -⟩ := sec6_L_log3_proved
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcos : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
  have hsin : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsum : (Ao + ‖Zo θ‖) / 2 + (Ao - ‖Zo θ‖) / 2 = Ao := by ring
  refine ⟨by rw [hzre]; positivity, by rw [hzim]; positivity, Complex.arg_nonneg_iff.mpr him,
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre), phiD_amgm _ _ (by rw [hsum]; linarith), ?_⟩
  rw [hsum, hL]
  linarith

end Robinson.Proofs
