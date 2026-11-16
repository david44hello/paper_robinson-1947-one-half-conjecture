/-
Robinson/Proofs/Chart.lean — proofs of lem_5_3 and lem_5_4.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Matrix2

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Elementary facts about `e^{ix}` -/

/-- `conj e^{ix} = e^{-ix}` for real `x`. -/
private lemma conj_exp_mul_I (x : ℝ) : conj (exp ((x : ℂ) * I)) = exp (-((x : ℂ) * I)) := by
  rw [← exp_conj]
  congr 1
  simp

/-- `conj e^{-ix} = e^{ix}` for real `x`. -/
private lemma conj_exp_neg_mul_I (x : ℝ) : conj (exp (-((x : ℂ) * I))) = exp ((x : ℂ) * I) := by
  rw [← exp_conj]
  congr 1
  simp

/-- `e^{z} e^{-z} = 1`. -/
private lemma exp_mul_exp_neg' (z : ℂ) : exp z * exp (-z) = 1 := by
  rw [← exp_add, add_neg_cancel, exp_zero]

/-- `e^{i(π - x)} = -e^{-ix}`. -/
private lemma exp_pi_sub_mul_I (x : ℝ) :
    exp (((Real.pi - x : ℝ) : ℂ) * I) = -exp (-((x : ℂ) * I)) := by
  rw [show ((Real.pi - x : ℝ) : ℂ) * I = (Real.pi : ℂ) * I + -((x : ℂ) * I) by push_cast; ring, exp_add,
    exp_pi_mul_I]
  ring

/-- `e^{-i(π - x)} = -e^{ix}`. -/
private lemma exp_neg_pi_sub_mul_I (x : ℝ) :
    exp (-(((Real.pi - x : ℝ) : ℂ) * I)) = -exp ((x : ℂ) * I) := by
  rw [show -(((Real.pi - x : ℝ) : ℂ) * I) = (x : ℂ) * I + -((Real.pi : ℂ) * I) by push_cast; ring, exp_add,
    exp_neg, exp_pi_mul_I]
  simp

/-- `e^{i(x - 2π)} = e^{ix}`. -/
private lemma exp_sub_two_pi_mul_I (x : ℝ) :
    exp (((x - 2 * Real.pi : ℝ) : ℂ) * I) = exp ((x : ℂ) * I) := by
  rw [show ((x - 2 * Real.pi : ℝ) : ℂ) * I = (x : ℂ) * I - 2 * (Real.pi : ℂ) * I by push_cast; ring, exp_sub,
    exp_two_pi_mul_I, div_one]

/-! ### Entries of the chart -/

private lemma chart_00 (α ψ ω : ℝ) :
    chart α ψ ω 0 0 = exp ((ψ : ℂ) * I) * (exp ((ω : ℂ) * I) * (Real.cos α : ℂ)) := rfl

private lemma chart_01 (α ψ ω : ℝ) :
    chart α ψ ω 0 1 = exp ((ψ : ℂ) * I) * (I * (Real.sin α : ℂ)) := rfl

private lemma chart_10 (α ψ ω : ℝ) :
    chart α ψ ω 1 0 = exp ((ψ : ℂ) * I) * (I * (Real.sin α : ℂ)) := rfl

private lemma chart_11 (α ψ ω : ℝ) :
    chart α ψ ω 1 1 = exp ((ψ : ℂ) * I) * (exp (-((ω : ℂ) * I)) * (Real.cos α : ℂ)) := rfl

/-- Two 2x2 matrices with the same four entries are equal. -/
private lemma mat2_ext {M N : Matrix (Fin 2) (Fin 2) ℂ} (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- The chart depends on `ψ` and `ω` only through `e^{iψ}` and `e^{iω}`. -/
private lemma chart_congr (α ψ ω ψ' ω' : ℝ) (hψ : exp ((ψ : ℂ) * I) = exp ((ψ' : ℂ) * I))
    (hω : exp ((ω : ℂ) * I) = exp ((ω' : ℂ) * I)) : chart α ψ ω = chart α ψ' ω' := by
  have hω' : exp (-((ω : ℂ) * I)) = exp (-((ω' : ℂ) * I)) := by rw [exp_neg, exp_neg, hω]
  apply mat2_ext
  · rw [chart_00, chart_00, hψ, hω]
  · rw [chart_01, chart_01, hψ]
  · rw [chart_10, chart_10, hψ]
  · rw [chart_11, chart_11, hψ, hω']

/-! ### Lemma 5.3 (ii): the chart is symmetric and unitary -/

private lemma chart_symm (α ψ ω : ℝ) : (chart α ψ ω)ᵀ = chart α ψ ω := by
  apply mat2_ext
  · rfl
  · rw [Matrix.transpose_apply, chart_10, chart_01]
  · rw [Matrix.transpose_apply, chart_10, chart_01]
  · rfl

private lemma chart_unitary (α ψ ω : ℝ) : chart α ψ ω * (chart α ψ ω)ᴴ = 1 := by
  have hu := exp_mul_exp_neg' ((ψ : ℂ) * I)
  have hv := exp_mul_exp_neg' ((ω : ℂ) * I)
  have hcs : (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq α
  apply mat2_ext <;>
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, chart_00, chart_01, chart_10,
    chart_11, Complex.star_def, map_mul, conj_ofReal, conj_I, conj_exp_mul_I, conj_exp_neg_mul_I,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  · linear_combination
      (exp ((ω : ℂ) * I) * exp (-((ω : ℂ) * I)) * (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2) * hu +
        (Real.cos α : ℂ) ^ 2 * hv + hcs -
        exp ((ψ : ℂ) * I) * exp (-((ψ : ℂ) * I)) * (Real.sin α : ℂ) ^ 2 * I_sq
  · ring
  · ring
  · linear_combination
      (exp ((ω : ℂ) * I) * exp (-((ω : ℂ) * I)) * (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2) * hu +
        (Real.cos α : ℂ) ^ 2 * hv + hcs -
        exp ((ψ : ℂ) * I) * exp (-((ψ : ℂ) * I)) * (Real.sin α : ℂ) ^ 2 * I_sq

private lemma chart_symmUnitary (α ψ ω : ℝ) : IsSymmUnitary (chart α ψ ω) :=
  ⟨chart_symm α ψ ω, chart_unitary α ψ ω⟩

/-! ### Lemma 5.3 (iii): conjugation of the chart -/

private lemma mconj_chart (α ψ ω : ℝ) :
    mconj (chart α ψ ω) = chart α (Real.pi - ψ) (Real.pi - ω) := by
  apply mat2_ext <;>
  simp only [mconj, Matrix.map_apply, chart_00, chart_01, chart_10, chart_11, map_mul, conj_ofReal, conj_I,
    conj_exp_mul_I, conj_exp_neg_mul_I, exp_pi_sub_mul_I, exp_neg_pi_sub_mul_I] <;>
  ring

/-! ### Lemma 5.3 (i): every symmetric unitary matrix is a chart value -/

/-- The entries `a = M₀₀`, `b = M₀₁ = M₁₀`, `d = M₁₁` of a symmetric unitary matrix satisfy
`|a|² + |b|² = 1`, `a b̄ + b d̄ = 0`, `|b|² + |d|² = 1`. -/
private lemma symmUnitary_rels {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsSymmUnitary M) :
    M 1 0 = M 0 1 ∧ M 0 0 * conj (M 0 0) + M 0 1 * conj (M 0 1) = 1 ∧
      M 0 0 * conj (M 0 1) + M 0 1 * conj (M 1 1) = 0 ∧
      M 0 1 * conj (M 0 1) + M 1 1 * conj (M 1 1) = 1 := by
  obtain ⟨hT, hU⟩ := hM
  have hs : M 1 0 = M 0 1 := by
    have h := congrFun (congrFun hT 0) 1
    rwa [Matrix.transpose_apply] at h
  have e00 := congrFun (congrFun hU 0) 0
  have e01 := congrFun (congrFun hU 0) 1
  have e11 := congrFun (congrFun hU 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), hs] at e00 e01 e11
  exact ⟨hs, e00, e01, e11⟩

/-- Recovering `d` from `a`, `b` and the orthogonality relation `a b̄ + b d̄ = 0` when `b ≠ 0`. -/
private lemma d_eq_aux (a b d u e v w : ℂ) (ra rb : ℝ) (ha : a = u * (v * ra)) (hb : b = u * (I * rb))
    (hb0 : b ≠ 0) (hcu : conj u = e) (hcv : conj v = w) (hue : e * u = 1)
    (hrel : a * conj b + b * conj d = 0) : d = u * (w * ra) := by
  have h2 : conj a * b + conj b * d = 0 := by
    have h := congrArg conj hrel
    simpa using h
  have hca : conj a = e * (w * ra) := by rw [ha]; simp [hcu, hcv]
  have hcb : conj b = e * (-I * rb) := by rw [hb]; simp [hcu]
  have hrb : I * (rb : ℂ) ≠ 0 := by
    intro h0
    apply hb0
    rw [hb, h0, mul_zero]
  rw [hca, hcb, hb] at h2
  have h3 : (I * (rb : ℂ)) * (d - u * (w * ra)) = 0 := by
    linear_combination (-u) * h2 + (I * rb * u * w * ra - I * rb * d) * hue
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h hrb
  · exact sub_eq_zero.1 h

/-- Lemma 5.3 (i) on the entries. -/
private lemma chart_of_entries (a b d : ℂ) (e00 : a * conj a + b * conj b = 1)
    (e01 : a * conj b + b * conj d = 0) (e11 : b * conj b + d * conj d = 1) :
    ∃ α ψ ω : ℝ, 0 ≤ α ∧ α ≤ Real.pi / 2 ∧ -Real.pi ≤ ψ ∧ ψ ≤ Real.pi ∧ -Real.pi ≤ ω ∧ ω ≤ Real.pi ∧
      a = exp ((ψ : ℂ) * I) * (exp ((ω : ℂ) * I) * (Real.cos α : ℂ)) ∧
      b = exp ((ψ : ℂ) * I) * (I * (Real.sin α : ℂ)) ∧
      d = exp ((ψ : ℂ) * I) * (exp (-((ω : ℂ) * I)) * (Real.cos α : ℂ)) := by
  have hn1 : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    rw [mul_conj', mul_conj'] at e00
    exact_mod_cast e00
  have hn2 : ‖b‖ ^ 2 + ‖d‖ ^ 2 = 1 := by
    rw [mul_conj', mul_conj'] at e11
    exact_mod_cast e11
  have had : ‖d‖ = ‖a‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  have ha1 : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
  have hcos : Real.cos (Real.arccos ‖a‖) = ‖a‖ := Real.cos_arccos (by linarith [norm_nonneg a]) ha1
  have hsin : Real.sin (Real.arccos ‖a‖) = ‖b‖ := by
    rw [Real.sin_arccos, show 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg b)
  have hα0 : 0 ≤ Real.arccos ‖a‖ := Real.arccos_nonneg _
  have hα1 : Real.arccos ‖a‖ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 (norm_nonneg a)
  by_cases hb : b = 0
  · refine ⟨Real.arccos ‖a‖, (arg a + arg d) / 2, (arg a - arg d) / 2, hα0, hα1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [neg_pi_lt_arg a, neg_pi_lt_arg d]
    · linarith [arg_le_pi a, arg_le_pi d]
    · linarith [neg_pi_lt_arg a, arg_le_pi d]
    · linarith [arg_le_pi a, neg_pi_lt_arg d]
    · rw [hcos, ← mul_assoc, ← exp_add,
        show (((arg a + arg d) / 2 : ℝ) : ℂ) * I + (((arg a - arg d) / 2 : ℝ) : ℂ) * I = (arg a : ℂ) * I by
          push_cast; ring]
      linear_combination (-1 : ℂ) * norm_mul_exp_arg_mul_I a
    · rw [hsin, hb]
      simp
    · rw [hcos, ← had, ← mul_assoc, ← exp_add,
        show (((arg a + arg d) / 2 : ℝ) : ℂ) * I + -((((arg a - arg d) / 2 : ℝ) : ℂ) * I) = (arg d : ℂ) * I by
          push_cast; ring]
      linear_combination (-1 : ℂ) * norm_mul_exp_arg_mul_I d
  · set ψ : ℝ := arg (-I * b) with hψ
    set ω : ℝ := arg (a * exp (-((ψ : ℂ) * I))) with hω
    have hu : (‖b‖ : ℂ) * exp ((ψ : ℂ) * I) = -I * b := by
      have h := norm_mul_exp_arg_mul_I (-I * b)
      rwa [norm_mul, norm_neg, norm_I, one_mul] at h
    have hue : exp (-((ψ : ℂ) * I)) * exp ((ψ : ℂ) * I) = 1 := by
      rw [mul_comm]
      exact exp_mul_exp_neg' _
    have hne : ‖exp (-((ψ : ℂ) * I))‖ = 1 := by
      rw [← neg_mul, ← ofReal_neg, norm_exp_ofReal_mul_I]
    have hv : (‖a‖ : ℂ) * exp ((ω : ℂ) * I) = a * exp (-((ψ : ℂ) * I)) := by
      have h := norm_mul_exp_arg_mul_I (a * exp (-((ψ : ℂ) * I)))
      rwa [norm_mul, hne, mul_one] at h
    have hbeq : b = exp ((ψ : ℂ) * I) * (I * (‖b‖ : ℂ)) := by
      linear_combination -I * hu + b * I_sq
    have haeq : a = exp ((ψ : ℂ) * I) * (exp ((ω : ℂ) * I) * (‖a‖ : ℂ)) := by
      linear_combination -(exp ((ψ : ℂ) * I)) * hv - a * hue
    have hdeq : d = exp ((ψ : ℂ) * I) * (exp (-((ω : ℂ) * I)) * (‖a‖ : ℂ)) :=
      d_eq_aux a b d _ _ _ _ ‖a‖ ‖b‖ haeq hbeq hb (conj_exp_mul_I ψ) (conj_exp_mul_I ω) hue e01
    refine ⟨Real.arccos ‖a‖, ψ, ω, hα0, hα1, (neg_pi_lt_arg _).le, arg_le_pi _, (neg_pi_lt_arg _).le,
      arg_le_pi _, ?_, ?_, ?_⟩
    · rw [hcos]; exact haeq
    · rw [hsin]; exact hbeq
    · rw [hcos]; exact hdeq

/-- Lemma 5.3 (i). -/
private lemma chart_surj (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : IsSymmUnitary M) :
    ∃ α ψ ω : ℝ, 0 ≤ α ∧ α ≤ Real.pi / 2 ∧ -Real.pi ≤ ψ ∧ ψ ≤ Real.pi ∧ -Real.pi ≤ ω ∧ ω ≤ Real.pi ∧
      M = chart α ψ ω := by
  obtain ⟨hs, e00, e01, e11⟩ := symmUnitary_rels hM
  obtain ⟨α, ψ, ω, h1, h2, h3, h4, h5, h6, ha, hb, hd⟩ := chart_of_entries (M 0 0) (M 0 1) (M 1 1) e00 e01 e11
  refine ⟨α, ψ, ω, h1, h2, h3, h4, h5, h6, ?_⟩
  apply mat2_ext
  · rw [chart_00]; exact ha
  · rw [chart_01]; exact hb
  · rw [chart_10, hs]; exact hb
  · rw [chart_11]; exact hd

theorem lem_5_3_proved :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ, IsSymmUnitary M → ∃ α ψ ω : ℝ, 0 ≤ α ∧ α ≤ Real.pi / 2 ∧
      -Real.pi ≤ ψ ∧ ψ ≤ Real.pi ∧ -Real.pi ≤ ω ∧ ω ≤ Real.pi ∧ M = chart α ψ ω) ∧
      (∀ α ψ ω : ℝ, IsSymmUnitary (chart α ψ ω)) ∧
      ∀ α ψ ω : ℝ, mconj (chart α ψ ω) = chart α (Real.pi - ψ) (Real.pi - ω) :=
  ⟨chart_surj, chart_symmUnitary, mconj_chart⟩

/-! ### Lemma 5.4 -/

/-- A unitary matrix has operator norm at most `1`, so a symmetric unitary matrix lies in the ball `𝓑`. -/
private lemma inBall_of_symmUnitary {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsSymmUnitary M) : InBall M := by
  refine ⟨hM.1, ?_⟩
  have hU : M ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact hM.2)
  have hU' := Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) hU
  have h := CStarRing.norm_mem_unitary_mul
    (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) hU'
  rw [mul_one] at h
  unfold opNorm
  rw [h, ContinuousLinearMap.one_def]
  exact ContinuousLinearMap.norm_id_le

/-- An angle of `[0, 2π]` is congruent modulo `2π` to an angle of `[-π, π]`. -/
private lemma reduce_omega (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 2 * Real.pi) :
    ∃ y' : ℝ, -Real.pi ≤ y' ∧ y' ≤ Real.pi ∧ exp ((y' : ℂ) * I) = exp ((y : ℂ) * I) := by
  by_cases hy : y ≤ Real.pi
  · exact ⟨y, by linarith [Real.pi_pos], hy, rfl⟩
  · exact ⟨y - 2 * Real.pi, by linarith, by linarith [Real.pi_pos], exp_sub_two_pi_mul_I y⟩

theorem lem_5_4_proved (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (hΦ : ∀ M, InBall M → Φ (mconj M) = conj (Φ M)) :
    {x : ℝ | ∃ M : Matrix (Fin 2) (Fin 2) ℂ, IsSymmUnitary M ∧ x = (Φ M).re} =
      {x : ℝ | ∃ α ψ ω : ℝ, InX α ψ ω ∧ x = (Φ (chart α ψ ω)).re} := by
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨α, ψ, ω, hα0, hα1, hψ0, hψ1, hω0, hω1, rfl⟩ := chart_surj M hM
    by_cases hψ : -(Real.pi / 2) ≤ ψ ∧ ψ ≤ Real.pi / 2
    · exact ⟨α, ψ, ω, ⟨hα0, hα1, hψ.1, hψ.2, hω0, hω1⟩, rfl⟩
    · have hre : (Φ (chart α ψ ω)).re = (Φ (chart α (Real.pi - ψ) (Real.pi - ω))).re := by
        rw [← mconj_chart, hΦ _ (inBall_of_symmUnitary (chart_symmUnitary α ψ ω)), conj_re]
      rw [hre]
      obtain ⟨ω', hω'0, hω'1, hω'e⟩ := reduce_omega (Real.pi - ω) (by linarith) (by linarith)
      have hψ' : ∃ ψ' : ℝ, -(Real.pi / 2) ≤ ψ' ∧ ψ' ≤ Real.pi / 2 ∧
          exp ((ψ' : ℂ) * I) = exp (((Real.pi - ψ : ℝ) : ℂ) * I) := by
        by_cases hpos : Real.pi / 2 < ψ
        · exact ⟨Real.pi - ψ, by linarith, by linarith, rfl⟩
        · have hneg : ψ < -(Real.pi / 2) := by
            by_contra hc
            exact hψ ⟨by linarith, by linarith⟩
          exact ⟨(Real.pi - ψ) - 2 * Real.pi, by linarith, by linarith, exp_sub_two_pi_mul_I _⟩
      obtain ⟨ψ', hψ'0, hψ'1, hψ'e⟩ := hψ'
      refine ⟨α, ψ', ω', ⟨hα0, hα1, hψ'0, hψ'1, hω'0, hω'1⟩, ?_⟩
      rw [chart_congr α ψ' ω' (Real.pi - ψ) (Real.pi - ω) hψ'e hω'e]
  · rintro ⟨α, ψ, ω, -, rfl⟩
    exact ⟨chart α ψ ω, chart_symmUnitary α ψ ω, rfl⟩

end Robinson.Proofs
