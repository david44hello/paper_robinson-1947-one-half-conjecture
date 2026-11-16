/-
Robinson/Proofs/Arith.lean — proofs of sec7_P_minors, tab3_totals, sec6_margin_arith,
sec6_cover_bound_arith, sec6_L_log3, sec6_c_bound.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Matrix2
import Robinson.Defs.Far

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## Pure arithmetic rows -/

theorem tab3_totals_proved :
    36762 + 42121 + 43457 + 63128 + 63302 + 8986 + 8128 + 7562 + 13517 + 12519 + 12024 = 311506 := by
  norm_num

theorem sec6_margin_arith_proved : (277 / 400 : ℝ) - 173 / 250 = 1 / 2000 := by
  norm_num

theorem sec6_cover_bound_arith_proved :
    (3459999249 : ℝ) / (5 * 10 ^ 9) < 173 / 250 ∧
      (0.69199984 : ℝ) < 3459999249 / (5 * 10 ^ 9) ∧ (3459999249 : ℝ) / (5 * 10 ^ 9) < 0.69199985 ∧
      (173 / 250 : ℝ) = 0.692 := by
  norm_num

/-! ## `L = 2 A_o = log 3 < π/2` -/

/-- `artanh (1/2) = ½ log 3`. -/
private lemma artanh_half : Real.artanh (1 / 2) = 1 / 2 * Real.log 3 := by
  rw [Real.artanh_eq_half_log (by constructor <;> norm_num)]
  norm_num

/-- `log 3 < 3/2`, because `exp (3/2) = (exp (1/2))³ ≥ (3/2)³ > 3`. -/
private lemma log_three_lt : Real.log 3 < 3 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
  have h2 : Real.exp (3 / 2) = Real.exp (1 / 2) ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : (3 / 2 : ℝ) ^ 3 ≤ Real.exp (1 / 2) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  rw [h2]
  norm_num at h3
  linarith

theorem sec6_L_log3_proved : 2 * Ao = Real.log 3 ∧ Llog3 = Real.log 3 ∧ Llog3 < Real.pi / 2 := by
  refine ⟨?_, rfl, ?_⟩
  · rw [Ao, artanh_half]; ring
  · have hpi := Real.pi_gt_d2
    have := log_three_lt
    rw [Llog3]
    linarith

/-! ## `0 ≤ cos(θ/2) ≤ sin(π/8) < 383/1000` for `θ ∈ [135°, 180°]` -/

/-- `sin(π/8) = √(2 - √2)/2 < 383/1000`. -/
private lemma sin_pi_div_eight_lt : Real.sin (Real.pi / 8) < 383 / 1000 := by
  rw [Real.sin_pi_div_eight]
  have hs2 : (1413244 / 1000000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h : Real.sqrt (2 - Real.sqrt 2) < 766 / 1000 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  linarith

theorem sec6_c_bound_proved (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    0 ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ Real.sin (Real.pi / 8) ∧ Real.sin (Real.pi / 8) < 383 / 1000 := by
  unfold deg at h1 h2
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, sin_pi_div_eight_lt⟩
  · apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
  · rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith

/-! ## The matrix `P`: its leading principal minors and positive definiteness -/

/-- The quadratic form of `P` written as `Σ D_j y_j²` with `y = Lᵀ x` (an `LDLᵀ` factorisation of `P`). -/
private noncomputable def qLDL (a b c d : ℝ) : ℝ :=
  8473 / 5000 * (a + 3451 / 16946 * b + (-496 / 8473) * c + 2537 / 16946 * d) ^ 2 +
    499588663 / 169460000 * (b + 17929168 / 499588663 * c + (-10585355 / 499588663) * d) ^ 2 +
    1317395036843 / 4995886630000 * (c + (-86463516320 / 1317395036843) * d) ^ 2 +
    125044355055249 / 2634790073686000 * d ^ 2

private lemma qLDL_pos (a b c d : ℝ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) : 0 < qLDL a b c d := by
  unfold qLDL
  set y0 := a + 3451 / 16946 * b + (-496 / 8473) * c + 2537 / 16946 * d with hy0
  set y1 := b + 17929168 / 499588663 * c + (-10585355 / 499588663) * d with hy1
  set y2 := c + (-86463516320 / 1317395036843) * d with hy2
  have hy : y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0 ∨ d ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e0, e1, e2, e3⟩ := hcon
    have hc : c = 0 := by rw [hy2, e3] at e2; linarith
    have hb : b = 0 := by rw [hy1, e3, hc] at e1; linarith
    have ha : a = 0 := by rw [hy0, e3, hc, hb] at e0; linarith
    rcases h with h | h | h | h <;> contradiction
  have s0 := sq_nonneg y0
  have s1 := sq_nonneg y1
  have s2 := sq_nonneg y2
  have s3 := sq_nonneg d
  rcases hy with h | h | h | h
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; linarith
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; linarith
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; linarith
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; linarith

private lemma Pmat_quadForm (x : Fin 4 → ℝ) :
    star x ⬝ᵥ (Pmat *ᵥ x) = qLDL (x 0) (x 1) (x 2) (x 3) := by
  simp [Pmat, qLDL, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

private lemma Pmat_isHermitian : Pmat.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pmat, Matrix.conjTranspose_apply]

theorem Pmat_posDef : Pmat.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos Pmat_isHermitian fun x hx => ?_
  rw [Pmat_quadForm]
  apply qLDL_pos
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp [hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2]

private lemma Pmat_minor1 :
    (Pmat.submatrix (Fin.castLE (by norm_num : 1 ≤ 4)) (Fin.castLE (by norm_num : 1 ≤ 4))).det = 8473 / 5000 := by
  rw [Matrix.det_fin_one]
  simp [Pmat]
  norm_num

private lemma Pmat_minor2 :
    (Pmat.submatrix (Fin.castLE (by norm_num : 2 ≤ 4)) (Fin.castLE (by norm_num : 2 ≤ 4))).det =
      499588663 / 10 ^ 8 := by
  rw [Matrix.det_fin_two]
  simp [Pmat]
  norm_num

private lemma Pmat_minor3 :
    (Pmat.submatrix (Fin.castLE (by norm_num : 3 ≤ 4)) (Fin.castLE (by norm_num : 3 ≤ 4))).det =
      1317395036843 / 10 ^ 12 := by
  rw [Matrix.det_fin_three]
  simp [Pmat]
  norm_num

private lemma Pmat_det : Pmat.det = 125044355055249 / (2 * 10 ^ 15) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Pmat, Fin.succAbove]
  norm_num

theorem sec7_P_minors_proved :
    (Pmat.submatrix (Fin.castLE (by norm_num : 1 ≤ 4)) (Fin.castLE (by norm_num : 1 ≤ 4))).det = 8473 / 5000 ∧
      (Pmat.submatrix (Fin.castLE (by norm_num : 2 ≤ 4)) (Fin.castLE (by norm_num : 2 ≤ 4))).det =
        499588663 / 10 ^ 8 ∧
      (Pmat.submatrix (Fin.castLE (by norm_num : 3 ≤ 4)) (Fin.castLE (by norm_num : 3 ≤ 4))).det =
        1317395036843 / 10 ^ 12 ∧
      Pmat.det = 125044355055249 / (2 * 10 ^ 15) ∧ Pmat.PosDef :=
  ⟨Pmat_minor1, Pmat_minor2, Pmat_minor3, Pmat_det, Pmat_posDef⟩

end Robinson.Proofs
