/-
Robinson/Proofs/SigmaPos.lean — proofs of sec6_sigma_pos.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Matrix2
import Robinson.Defs.Grunsky
import Robinson.Proofs.Arith
import Robinson.Proofs.OddRootGram

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## The points `z_θ` and `s_θ` -/

private lemma sp_im_zθ (θ : ℝ) : (zθ θ).im = Real.sin (θ / 2) / 2 := by
  unfold zθ
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp
  ring

/-- `Im z_θ > 0` for `0 < θ ≤ π`. -/
private lemma sp_im_zθ_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < (zθ θ).im := by
  rw [sp_im_zθ]
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

/-- `‖s_θ‖² = 1/2`. -/
private lemma sp_norm_sθ_sq (θ : ℝ) : ‖sθ θ‖ ^ 2 = 1 / 2 := by
  unfold sθ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `s_θ² = z_θ`. -/
private lemma sp_sθ_sq (θ : ℝ) : sθ θ ^ 2 = zθ θ := by
  have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  unfold sθ zθ
  rw [mul_pow, h2, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `A_o = artanh(1/2) > 0`, since `2 A_o = log 3`. -/
private lemma sp_Ao_pos : 0 < Ao := by
  have h := sec6_L_log3_proved.1
  have : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

/-! ## The phase rotation -/

/-- `e^{iε/2}`. -/
private noncomputable def sp_ph (ε : ℝ) : ℂ := exp (((ε / 2 : ℝ) : ℂ) * I)

private lemma sp_norm_ph (ε : ℝ) : ‖sp_ph ε‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma sp_ph_sq (ε : ℝ) : sp_ph ε ^ 2 = exp ((ε : ℂ) * I) := by
  rw [sp_ph, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma sp_im_sq_eq (c : ℂ) : c.im ^ 2 = (‖c‖ ^ 2 - (c ^ 2).re) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sq c, Complex.mul_re]; ring

/-- `‖Im(e^{iε/2} u)‖² = (‖u‖² - Re(e^{iε} uᵀu))/2`. -/
private lemma sp_phase_hasSum_im (ε : ℝ) {u : ℕ → ℂ} {N : ℝ} {S : ℂ}
    (hN : HasSum (fun n => ‖u n‖ ^ 2) N) (hS : HasSum (fun n => u n ^ 2) S) :
    HasSum (fun n => (sp_ph ε * u n).im ^ 2) ((N - (exp ((ε : ℂ) * I) * S).re) / 2) := by
  have h1 : ∀ n, ‖sp_ph ε * u n‖ ^ 2 = ‖u n‖ ^ 2 := by intro n; rw [norm_mul, sp_norm_ph, one_mul]
  have h2 : ∀ n, (sp_ph ε * u n) ^ 2 = exp ((ε : ℂ) * I) * u n ^ 2 := by intro n; rw [mul_pow, sp_ph_sq]
  have hS' := Complex.hasSum_re (hS.mul_left (exp ((ε : ℂ) * I)))
  have e : (fun n => (sp_ph ε * u n).im ^ 2) =
      fun n => (‖u n‖ ^ 2 - (exp ((ε : ℂ) * I) * u n ^ 2).re) / 2 := by
    funext n; rw [sp_im_sq_eq, h1, h2]
  rw [e]; exact (hN.sub hS').div_const 2

/-- `e^{-iφ} Z_o = |Z_o|`, `φ = arg Z_o`. -/
private lemma sp_rot_Zo (θ : ℝ) : exp ((((-phiFar θ) : ℝ) : ℂ) * I) * Zo θ = ((‖Zo θ‖ : ℝ) : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (Zo θ)]
  rw [phiFar, mul_left_comm, ← Complex.exp_add]
  push_cast
  rw [neg_mul, neg_add_cancel, exp_zero, mul_one]

/-- With `r + iq = e^{-iφ/2} a(s)`: `‖q‖² = σ₋`. -/
private lemma sp_q_sum {θ : ℝ} {u : ℕ → ℂ} (hN : HasSum (fun n => ‖u n‖ ^ 2) Ao)
    (hS : HasSum (fun n => u n ^ 2) (Zo θ)) :
    HasSum (fun n => (sp_ph (-phiFar θ) * u n).im ^ 2) (sigM θ) := by
  have h := sp_phase_hasSum_im (-phiFar θ) hN hS
  rw [sp_rot_Zo, Complex.ofReal_re] at h
  exact h

/-! ## Positivity of `σ₊` and `σ₋` -/

private lemma sp_sigP_pos (θ : ℝ) : 0 < sigP θ := by
  unfold sigP; have := sp_Ao_pos; have := norm_nonneg (Zo θ); linarith

/-- `σ₋ > 0`: otherwise `e^{-iφ/2} s` and `e^{-iφ/2} s³` would both be real, and `z = s²` would be real. -/
private lemma sp_sigM_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < sigM θ := by
  obtain ⟨hN, hS, -, -⟩ := eq_gram_proved (sθ θ) (sp_norm_sθ_sq θ)
  rw [sp_sθ_sq] at hS
  have hq := sp_q_sum hN hS
  by_contra hneg
  rw [not_lt] at hneg
  set w := sp_ph (-phiFar θ)
  have hq0 : ∀ n, (w * aOdd (sθ θ) n).im = 0 := by
    intro n
    have := le_hasSum hq n (fun j _ => sq_nonneg _)
    nlinarith [sq_nonneg (w * aOdd (sθ θ) n).im]
  have ha1 : aOdd (sθ θ) 1 = sθ θ := by simp [aOdd]
  have ha3 : aOdd (sθ θ) 3 = sθ θ ^ 3 / (Real.sqrt 3 : ℂ) := by simp [aOdd]
  have hq1 := hq0 1
  have hq3 := hq0 3
  rw [ha1] at hq1
  rw [ha3, ← mul_div_assoc, Complex.div_ofReal_im] at hq3
  have hs3 : (w * sθ θ ^ 3).im = 0 := by
    have hsq : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    rcases div_eq_zero_iff.1 hq3 with h | h
    · exact h
    · linarith
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hs0 : sθ θ ≠ 0 := by
    intro h; have := sp_norm_sθ_sq θ; rw [h, norm_zero] at this; norm_num at this
  have hA : w * sθ θ = (((w * sθ θ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hq1])
  have hB : w * sθ θ ^ 3 = (((w * sθ θ ^ 3).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hs3])
  have hz : zθ θ = (w * sθ θ ^ 3) / (w * sθ θ) := by
    rw [← sp_sθ_sq]; field_simp
  have him : (zθ θ).im = 0 := by
    rw [hz, hB, hA, ← Complex.ofReal_div, Complex.ofReal_im]
  linarith [sp_im_zθ_pos h0 hπ]

/-! ## Row -/

theorem sec6_sigma_pos_proved : ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < sigM θ ∧ 0 < sigP θ :=
  fun _ h0 hπ => ⟨sp_sigM_pos h0 hπ, sp_sigP_pos _⟩

end Robinson.Proofs
