/-
Robinson/Proofs/Sec4Hat.lean — proofs of sec4_hat_bounds, eq_Qk, sec4_no_constant, lem_4_4_iv.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Near
import Robinson.Proofs.Koebe
import Robinson.Proofs.Normalize

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Elementary bounds for `9/20 ≤ τ ≤ 1/2` -/

section bounds

variable {τ : ℝ}

private lemma v_ge (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 3 / 4 ≤ vτ τ := by
  unfold vτ; nlinarith

private lemma v_pos (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 0 < vτ τ := by
  linarith [v_ge h1 h2]

private lemma v_ne (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : (vτ τ : ℂ) ≠ 0 := by
  exact_mod_cast (v_pos h1 h2).ne'

private lemma beta_nonneg (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 0 ≤ βτ τ :=
  div_nonneg (by linarith) (v_pos h1 h2).le

private lemma beta_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : βτ τ ≤ 2 / 3 := by
  unfold βτ
  rw [div_le_iff₀ (v_pos h1 h2)]
  linarith [v_ge h1 h2]

private lemma ysq_nonneg (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 0 ≤ ysq τ := by
  unfold ysq; nlinarith

private lemma ysq_le (h1 : 9 / 20 ≤ τ) (_h2 : τ ≤ 1 / 2) : ysq τ ≤ 19 / 400 := by
  unfold ysq; nlinarith

private lemma norm_ysq (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : ‖(ysq τ : ℂ)‖ = ysq τ :=
  Complex.norm_of_nonneg (ysq_nonneg h1 h2)

/-- `ν + 2β = (c + τ)/v`. -/
private lemma nu_add_two_beta (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) :
    nuτ τ c + 2 * (βτ τ : ℂ) = (c + τ) / (vτ τ : ℂ) := by
  have hv := v_ne h1 h2
  unfold nuτ βτ
  push_cast
  field_simp
  ring

/-- `ν(ν + 2β) = (c² - τ²)/v²`. -/
private lemma nu_mul_identity (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) :
    nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) = (c ^ 2 - (τ : ℂ) ^ 2) / (vτ τ : ℂ) ^ 2 := by
  have hv := v_ne h1 h2
  rw [nu_add_two_beta h1 h2 c]
  unfold nuτ
  field_simp
  ring

private lemma norm_nu_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) :
    ‖nuτ τ c‖ ≤ (‖c‖ + τ) / vτ τ := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith
  unfold nuτ
  rw [norm_div, Complex.norm_of_nonneg (v_pos h1 h2).le]
  refine div_le_div_of_nonneg_right ?_ (v_pos h1 h2).le
  calc ‖c - (τ : ℂ)‖ ≤ ‖c‖ + ‖(τ : ℂ)‖ := norm_sub_le _ _
    _ = ‖c‖ + τ := by rw [Complex.norm_of_nonneg hτ0]

private lemma norm_nu_add_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) :
    ‖nuτ τ c + 2 * (βτ τ : ℂ)‖ ≤ (‖c‖ + τ) / vτ τ := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith
  rw [nu_add_two_beta h1 h2 c, norm_div, Complex.norm_of_nonneg (v_pos h1 h2).le]
  refine div_le_div_of_nonneg_right ?_ (v_pos h1 h2).le
  calc ‖c + (τ : ℂ)‖ ≤ ‖c‖ + ‖(τ : ℂ)‖ := norm_add_le _ _
    _ = ‖c‖ + τ := by rw [Complex.norm_of_nonneg hτ0]

private lemma norm_nu_small (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {c : ℂ} (hc : ‖c‖ < 101 / 100) :
    ‖nuτ τ c‖ ≤ 21 / 10 := by
  refine (norm_nu_le h1 h2 c).trans ?_
  rw [div_le_iff₀ (v_pos h1 h2)]
  linarith [v_ge h1 h2]

private lemma norm_nu_add_small (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {c : ℂ} (hc : ‖c‖ < 101 / 100) :
    ‖nuτ τ c + 2 * (βτ τ : ℂ)‖ ≤ 21 / 10 := by
  refine (norm_nu_add_le h1 h2 c).trans ?_
  rw [div_le_iff₀ (v_pos h1 h2)]
  linarith [v_ge h1 h2]

/-- `|ν(ν + 2β)| ≤ (1 + τ²)/v²` for `|c| ≤ 1`. -/
private lemma norm_nu_mul_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    ‖nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ))‖ ≤ (1 + τ ^ 2) / vτ τ ^ 2 := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith
  rw [nu_mul_identity h1 h2 c, norm_div, norm_pow, Complex.norm_of_nonneg (v_pos h1 h2).le]
  refine div_le_div_of_nonneg_right ?_ (pow_pos (v_pos h1 h2) 2).le
  calc ‖c ^ 2 - (τ : ℂ) ^ 2‖ ≤ ‖c ^ 2‖ + ‖(τ : ℂ) ^ 2‖ := norm_sub_le _ _
    _ = ‖c‖ ^ 2 + τ ^ 2 := by rw [norm_pow, norm_pow, Complex.norm_of_nonneg hτ0]
    _ ≤ 1 + τ ^ 2 := by
      have : ‖c‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg c) hc
      linarith

private lemma bound_twenty_ninths (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : (1 + τ ^ 2) / vτ τ ^ 2 ≤ 20 / 9 := by
  rw [div_le_iff₀ (pow_pos (v_pos h1 h2) 2)]
  unfold vτ
  have ha : 0 ≤ 1 - 4 * τ ^ 2 := by nlinarith
  have hb : 0 ≤ 11 - 5 * τ ^ 2 := by nlinarith
  nlinarith [mul_nonneg ha hb]

private lemma one_add_ne_zero_of_norm_lt {X : ℂ} (h : ‖X‖ < 1) : 1 + X ≠ 0 := by
  intro h0
  have hX : X = -1 := by linear_combination h0
  rw [hX, norm_neg, norm_one] at h
  exact lt_irrefl _ h

private lemma one_sub_ne_zero_of_norm_lt {X : ℂ} (h : ‖X‖ < 1) : 1 - X ≠ 0 := by
  intro h0
  have hX : X = 1 := by linear_combination (-1 : ℂ) * h0
  rw [hX, norm_one] at h
  exact lt_irrefl _ h

/-- The three denominators of (sec4:hat) do not vanish for `|c| < 101/100`. -/
private lemma den_ne (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {c : ℂ} (hc : ‖c‖ < 101 / 100) :
    1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 ∧
      1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ) ≠ 0 ∧
      1 - 2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) -
        (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ) ^ 2 ≠ 0 := by
  have hn := norm_nu_small h1 h2 hc
  have hm := norm_nu_add_small h1 h2 hc
  have hn0 := norm_nonneg (nuτ τ c)
  have hm0 := norm_nonneg (nuτ τ c + 2 * (βτ τ : ℂ))
  have hY0 := ysq_nonneg h1 h2
  have hY := ysq_le h1 h2
  have hb0 := beta_nonneg h1 h2
  have hb := beta_le h1 h2
  have hnY := norm_ysq h1 h2
  have hnb : ‖(βτ τ : ℂ)‖ = βτ τ := Complex.norm_of_nonneg hb0
  have hn2 : ‖nuτ τ c‖ ^ 2 ≤ (21 / 10) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  refine ⟨?_, ?_, ?_⟩
  · apply one_add_ne_zero_of_norm_lt
    rw [norm_mul, norm_pow, hnY]
    have := mul_le_mul hn2 hY hY0 (by norm_num)
    linarith
  · apply one_sub_ne_zero_of_norm_lt
    rw [norm_mul, norm_mul, hnY]
    have h3 := mul_le_mul hn hm hm0 (by norm_num)
    have := mul_le_mul h3 hY hY0 (by norm_num)
    linarith
  · have hrw : 1 - 2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) -
        (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ) ^ 2 =
        1 - (2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) +
          nuτ τ c ^ 3 * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ) ^ 2) := by ring
    rw [hrw]
    apply one_sub_ne_zero_of_norm_lt
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hnY, hnb,
      Complex.norm_ofNat]
    have e1 := mul_le_mul hb hn hn0 (by norm_num)
    have e2 := mul_le_mul e1 hY hY0 (by norm_num)
    have e3 : ‖nuτ τ c‖ ^ 3 ≤ (21 / 10) ^ 3 := pow_le_pow_left₀ hn0 hn 3
    have e4 := mul_le_mul e3 hm hm0 (by norm_num)
    have e5 : ysq τ ^ 2 ≤ (19 / 400) ^ 2 := pow_le_pow_left₀ hY0 hY 2
    have e6 := mul_le_mul e4 e5 (sq_nonneg _) (by norm_num)
    linarith

end bounds

/-! ### Unfolding the hat quantities -/

private lemma Qhat_eq (τ : ℝ) : Qhat τ = fun c =>
    (Dτ τ c - (ysq τ : ℂ) * (6 * nuτ τ c ^ 2 + 8 * (βτ τ : ℂ) * nuτ τ c - 4 * τ * nuτ τ c ^ 3 -
      6 * τ * (βτ τ : ℂ) * nuτ τ c ^ 2)) /
    ((1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) * (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ))) := rfl

private lemma That_eq (τ : ℝ) : That τ = fun c =>
    (-4 * τ * nuτ τ c ^ 3 + (6 + 2 * τ ^ 2 / (vτ τ : ℂ)) * nuτ τ c ^ 2 + 4 * τ / (vτ τ : ℂ) ^ 2 * nuτ τ c -
      Dτ τ c * (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ)) /
    (1 - 2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) -
      (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ) ^ 2) := rfl

private lemma PihatO_eq (τ : ℝ) : PihatO τ = fun c =>
    (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)) / (1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) ^ 2 := rfl

private lemma nu_differentiable (τ : ℝ) : Differentiable ℂ (nuτ τ) := by
  have h : nuτ τ = fun c => (c - (τ : ℂ)) / (vτ τ : ℂ) := rfl
  rw [h]
  fun_prop

private lemma D_differentiable (τ : ℝ) : Differentiable ℂ (Dτ τ) := by
  have h : Dτ τ = fun c => 2 * (1 - 2 * τ * c) / (vτ τ : ℂ) := rfl
  rw [h]
  fun_prop

/-! ### Row `sec4_hat_bounds` -/

theorem sec4_hat_bounds_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) :
    (∀ c : ℂ, nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) = (c ^ 2 - (τ : ℂ) ^ 2) / (vτ τ : ℂ) ^ 2) ∧
      (∀ c : ℂ, ‖c‖ ≤ 1 →
        ‖nuτ τ c‖ ≤ 1 / (1 - τ) ∧ ‖nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ))‖ ≤ (1 + τ ^ 2) / vτ τ ^ 2) ∧
      1 / (1 - τ) ≤ 2 ∧ (1 + τ ^ 2) / vτ τ ^ 2 ≤ 20 / 9 ∧ ysq τ ≤ 19 / 400 ∧
      ∃ R : ℝ, 1 < R ∧ DifferentiableOn ℂ (Qhat τ) (ball (0 : ℂ) R) ∧
        DifferentiableOn ℂ (That τ) (ball (0 : ℂ) R) ∧ DifferentiableOn ℂ (PihatO τ) (ball (0 : ℂ) R) ∧
        ∀ c ∈ ball (0 : ℂ) R,
          (1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) * (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)) ≠ 0 ∧
          1 - 2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) -
            (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ) ^ 2 ≠ 0 := by
  have hball : ∀ c ∈ ball (0 : ℂ) (101 / 100), ‖c‖ < 101 / 100 := by
    intro c hc
    rwa [mem_ball, dist_zero_right] at hc
  have hν := nu_differentiable τ
  have hD := D_differentiable τ
  refine ⟨nu_mul_identity h1 h2, ?_, ?_, bound_twenty_ninths h1 h2, ysq_le h1 h2, 101 / 100, by norm_num,
    ?_, ?_, ?_, ?_⟩
  · intro c hc
    refine ⟨?_, norm_nu_mul_le h1 h2 hc⟩
    refine (norm_nu_le h1 h2 c).trans ?_
    have h1t : 0 < 1 - τ := by linarith
    rw [div_le_div_iff₀ (v_pos h1 h2) h1t]
    unfold vτ
    nlinarith [mul_nonneg (sub_nonneg.2 hc) h1t.le]
  · rw [div_le_iff₀ (by linarith)]
    linarith
  · rw [Qhat_eq]
    refine DifferentiableOn.div (Differentiable.differentiableOn (by fun_prop))
      (Differentiable.differentiableOn (by fun_prop)) ?_
    intro c hc
    have hd := den_ne h1 h2 (hball c hc)
    exact mul_ne_zero hd.1 hd.2.1
  · rw [That_eq]
    refine DifferentiableOn.div (Differentiable.differentiableOn (by fun_prop))
      (Differentiable.differentiableOn (by fun_prop)) ?_
    intro c hc
    exact (den_ne h1 h2 (hball c hc)).2.2
  · rw [PihatO_eq]
    refine DifferentiableOn.div (Differentiable.differentiableOn (by fun_prop))
      (Differentiable.differentiableOn (by fun_prop)) ?_
    intro c hc
    exact pow_ne_zero 2 (den_ne h1 h2 (hball c hc)).1
  · intro c hc
    have hd := den_ne h1 h2 (hball c hc)
    exact ⟨mul_ne_zero hd.1 hd.2.1, hd.2.2⟩

/-! ### The Koebe quotient in closed form -/

/-- `k(z) - k(w) = (z - w)(1 - zw)/((1 - z)²(1 - w)²)`. -/
private lemma koebe_sub (z w : ℂ) (hz : 1 - z ≠ 0) (hw : 1 - w ≠ 0) :
    koebe z - koebe w = (z - w) * (1 - z * w) / ((1 - z) ^ 2 * (1 - w) ^ 2) := by
  unfold koebe
  field_simp
  ring

/-- `Q_k(z, w) = 1 + (sp + s + p² - 6p + 1)/((1 - s + p)(1 - p))` with `s = z + w`, `p = zw`. -/
private lemma Q_koebe_formula (z w : ℂ) (hz : z ≠ 1) (hw : w ≠ 1) (hzw : z ≠ w) (hp : 1 - z * w ≠ 0) :
    Q koebe z w = 1 + ((z + w) * (z * w) + (z + w) + (z * w) ^ 2 - 6 * (z * w) + 1) /
      ((1 - z) * (1 - w) * (1 - z * w)) := by
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h3 : z - w ≠ 0 := sub_ne_zero.mpr hzw
  unfold Q
  rw [koebe_sub z w h1 h2, deriv_koebe hz, deriv_koebe hw]
  field_simp
  ring

/-- For a pair with `z + w = -2t` and `zw = 1/4`, `Q_k(z, w) = (½ - t)/(¾(5/4 + 2t))`. -/
private lemma Q_koebe_pair (z w : ℂ) (t : ℝ) (hz : z ≠ 1) (hw : w ≠ 1) (hzw : z ≠ w)
    (hs : z + w = -2 * (t : ℂ)) (hp : z * w = 1 / 4) (ht : 0 ≤ t) :
    Q koebe z w = (((1 / 2 - t) / ((3 / 4) * (5 / 4 + 2 * t)) : ℝ) : ℂ) := by
  have hp1 : 1 - z * w ≠ 0 := by rw [hp]; norm_num
  rw [Q_koebe_formula z w hz hw hzw hp1, show (1 - z) * (1 - w) = 1 - (z + w) + z * w by ring, hs, hp]
  have hBr : ((3 : ℝ) / 4 * (5 / 4 + 2 * t)) ≠ 0 := (mul_pos (by norm_num) (by linarith)).ne'
  have hB : ((3 : ℂ) / 4 * (5 / 4 + 2 * (t : ℂ))) ≠ 0 := by
    have e : ((3 : ℂ) / 4 * (5 / 4 + 2 * (t : ℂ))) = (((3 : ℝ) / 4 * (5 / 4 + 2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]
    exact Complex.ofReal_ne_zero.mpr hBr
  have hden : (1 - -2 * (t : ℂ) + 1 / 4) * (1 - 1 / 4) = 3 / 4 * (5 / 4 + 2 * (t : ℂ)) := by ring
  rw [hden]
  push_cast
  rw [eq_div_iff hB, add_mul, div_mul_cancel₀ _ hB]
  ring

/-! ### Row `eq_Qk` -/

private lemma Qhat_one (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : Qhat τ 1 = (Qk τ : ℂ) := by
  have hd := den_ne h1 h2.le (c := 1) (by norm_num)
  rw [Qhat_eq]
  show _ / _ = _
  rw [div_eq_iff (mul_ne_zero hd.1 hd.2.1)]
  have hv : (1 - (τ : ℂ) ^ 2) ≠ 0 := by
    have := v_ne h1 h2.le
    unfold vτ at this
    exact_mod_cast this
  have hB : ((3 : ℂ) / 4 * (5 / 4 + 2 * (τ : ℂ))) ≠ 0 := by
    have hBr : ((3 : ℝ) / 4 * (5 / 4 + 2 * τ)) ≠ 0 := (mul_pos (by norm_num) (by linarith)).ne'
    have e : ((3 : ℂ) / 4 * (5 / 4 + 2 * (τ : ℂ))) = (((3 : ℝ) / 4 * (5 / 4 + 2 * τ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]
    exact Complex.ofReal_ne_zero.mpr hBr
  have hQk : ((Qk τ : ℝ) : ℂ) = (1 / 2 - (τ : ℂ)) / (3 / 4 * (5 / 4 + 2 * (τ : ℂ))) := by
    unfold Qk; push_cast; try ring
  rw [hQk, div_mul_eq_mul_div, eq_div_iff hB]
  simp only [nuτ, Dτ, βτ, vτ, ysq]
  push_cast
  field_simp
  ring

private lemma ysq_pos (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : 0 < ysq τ := by
  unfold ysq; nlinarith

theorem eq_Qk_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    Qhat τ 1 = (Qk τ : ℂ) ∧ Qk τ = ysq τ / ((1 / 2 + τ) * (3 / 4) * (5 / 4 + 2 * τ)) ∧ 16 / 27 * ysq τ ≤ Qk τ ∧
      Q koebe (-(τ : ℂ) + (yτ τ : ℂ) * I) (-(τ : ℂ) - (yτ τ : ℂ) * I) = (Qk τ : ℂ) := by
  have hQk : Qk τ = ysq τ / ((1 / 2 + τ) * (3 / 4) * (5 / 4 + 2 * τ)) := by
    have ha : (1 / 2 + τ) ≠ 0 := (by linarith : (0 : ℝ) < 1 / 2 + τ).ne'
    have hb : (5 / 4 + 2 * τ) ≠ 0 := (by linarith : (0 : ℝ) < 5 / 4 + 2 * τ).ne'
    unfold Qk ysq
    field_simp
    ring
  refine ⟨Qhat_one τ h1 h2, hQk, ?_, ?_⟩
  · have hpos : 0 < (1 / 2 + τ) * (3 / 4) * (5 / 4 + 2 * τ) :=
      mul_pos (mul_pos (by linarith) (by norm_num)) (by linarith)
    rw [hQk, le_div_iff₀ hpos]
    have hY := (ysq_pos τ h1 h2).le
    have hprod : (1 / 2 + τ) * (3 / 4) * (5 / 4 + 2 * τ) ≤ 27 / 16 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - τ) (by linarith : (0 : ℝ) ≤ 13 / 4 + 2 * τ)]
    nlinarith [mul_le_mul_of_nonneg_left hprod hY]
  · set y := yτ τ with hy_def
    have hYpos := ysq_pos τ h1 h2
    have hy : 0 < y := Real.sqrt_pos.mpr hYpos
    have hy2 : (y : ℂ) ^ 2 = 1 / 4 - (τ : ℂ) ^ 2 := by
      have : y ^ 2 = 1 / 4 - τ ^ 2 := by
        rw [hy_def]
        unfold yτ
        rw [Real.sq_sqrt hYpos.le]
        rfl
      have h := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at h
      exact h
    have hz : -(τ : ℂ) + (y : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hw : -(τ : ℂ) - (y : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hzw : -(τ : ℂ) + (y : ℂ) * I ≠ -(τ : ℂ) - (y : ℂ) * I := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hs : (-(τ : ℂ) + (y : ℂ) * I) + (-(τ : ℂ) - (y : ℂ) * I) = -2 * (τ : ℂ) := by ring
    have hp : (-(τ : ℂ) + (y : ℂ) * I) * (-(τ : ℂ) - (y : ℂ) * I) = 1 / 4 := by
      linear_combination hy2 - (y : ℂ) ^ 2 * I_sq
    rw [Q_koebe_pair _ _ τ hz hw hzw hs hp (by linarith)]
    rfl

/-! ### Row `lem_4_4_iv` -/

section caps

variable {τ : ℝ}

private lemma norm_ofReal_mul (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ = |r| * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

private lemma norm_D_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) : ‖Dτ τ c‖ ≤ 16 / 3 := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith
  unfold Dτ
  rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg (v_pos h1 h2).le,
    div_le_iff₀ (v_pos h1 h2)]
  have h : ‖1 - 2 * (τ : ℂ) * c‖ ≤ 2 := by
    calc ‖1 - 2 * (τ : ℂ) * c‖ ≤ ‖(1 : ℂ)‖ + ‖2 * (τ : ℂ) * c‖ := norm_sub_le _ _
      _ = 1 + 2 * τ * ‖c‖ := by
        rw [norm_one, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg hτ0]
      _ ≤ 2 := by nlinarith [norm_nonneg c]
  linarith [v_ge h1 h2]

/-- `|ν⁴ + 2βν³| ≤ (ν⁺)⁴ + (4/3)(ν⁺)³`. -/
private lemma norm_quartic_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {c : ℂ} {νp : ℝ} (hν : ‖nuτ τ c‖ ≤ νp) :
    ‖nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3‖ ≤ calVOf νp := by
  have hn0 := norm_nonneg (nuτ τ c)
  have hb0 := beta_nonneg h1 h2
  have hb := beta_le h1 h2
  have h4 : ‖nuτ τ c‖ ^ 4 ≤ νp ^ 4 := pow_le_pow_left₀ hn0 hν 4
  have h3 : ‖nuτ τ c‖ ^ 3 ≤ νp ^ 3 := pow_le_pow_left₀ hn0 hν 3
  have hb2 : 2 * βτ τ ≤ 4 / 3 := by linarith
  have h3' := mul_le_mul hb2 h3 (pow_nonneg hn0 3) (by norm_num)
  unfold calVOf
  calc ‖nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3‖
      ≤ ‖nuτ τ c ^ 4‖ + ‖2 * (βτ τ : ℂ) * nuτ τ c ^ 3‖ := norm_add_le _ _
    _ = ‖nuτ τ c‖ ^ 4 + 2 * βτ τ * ‖nuτ τ c‖ ^ 3 := by
      rw [norm_pow, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_of_nonneg hb0]
    _ ≤ νp ^ 4 + 4 / 3 * νp ^ 3 := by linarith

private lemma calV_le {νp : ℝ} (h0 : 0 ≤ νp) (h2 : νp ≤ 2) : calVOf νp ≤ 80 / 3 := by
  unfold calVOf
  have h4 : νp ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h2 4
  have h3 : νp ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h2 3
  linarith

private lemma calV_nonneg {νp : ℝ} (h0 : 0 ≤ νp) : 0 ≤ calVOf νp := by
  unfold calVOf
  exact add_nonneg (pow_nonneg h0 4) (mul_nonneg (by norm_num) (pow_nonneg h0 3))

private lemma ysq_le_y0 (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) : ysq τ ≤ y0 ^ 2 := by
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy0 2
  rwa [Real.sq_sqrt (ysq_nonneg h1 h2)] at h

private lemma y0_sq : y0 ^ 2 = 289 / 6400 := by unfold y0; norm_num

/-- The numerator of `T̂` is at most the numerator of `T⁺` (for any `ν`, `d` with the stated bounds). -/
private lemma That_num_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) {ν d : ℂ} {νp : ℝ}
    (hν : ‖ν‖ ≤ νp) (hd : ‖d‖ ≤ 16 / 3) (hQ : ‖ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3‖ ≤ calVOf νp) :
    ‖-4 * τ * ν ^ 3 + (6 + 2 * τ ^ 2 / (vτ τ : ℂ)) * ν ^ 2 + 4 * τ / (vτ τ : ℂ) ^ 2 * ν -
      d * (ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ)‖ ≤
      2 * νp ^ 3 + 20 / 3 * νp ^ 2 + 32 / 9 * νp + 16 / 3 * calVOf νp * y0 ^ 2 := by
  have hv := v_pos h1 h2
  have hvge := v_ge h1 h2
  have hn0 := norm_nonneg ν
  have hp0 : 0 ≤ νp := hn0.trans hν
  have hY0 := ysq_nonneg h1 h2
  have hY := ysq_le_y0 h1 h2 hy0
  have hV0 := calV_nonneg hp0
  have ea : (-4 * (τ : ℂ)) = ((-4 * τ : ℝ) : ℂ) := by push_cast; ring
  have eb : (6 + 2 * (τ : ℂ) ^ 2 / (vτ τ : ℂ)) = ((6 + 2 * τ ^ 2 / vτ τ : ℝ) : ℂ) := by push_cast; ring
  have ec : (4 * (τ : ℂ) / (vτ τ : ℂ) ^ 2) = ((4 * τ / vτ τ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have ha : |(-4 * τ : ℝ)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hb0 : 0 ≤ 6 + 2 * τ ^ 2 / vτ τ := add_nonneg (by norm_num) (div_nonneg (by positivity) hv.le)
  have hb : 6 + 2 * τ ^ 2 / vτ τ ≤ 20 / 3 := by
    have : 2 * τ ^ 2 / vτ τ ≤ 2 / 3 := by
      rw [div_le_iff₀ hv]; unfold vτ; nlinarith
    linarith
  have hc0 : 0 ≤ 4 * τ / vτ τ ^ 2 := div_nonneg (by linarith) (pow_nonneg hv.le 2)
  have hcb : 4 * τ / vτ τ ^ 2 ≤ 32 / 9 := by
    rw [div_le_iff₀ (pow_pos hv 2)]
    nlinarith
  have hcb' : |(4 * τ / vτ τ ^ 2 : ℝ)| ≤ 32 / 9 := by rwa [abs_of_nonneg hc0]
  have hb' : |(6 + 2 * τ ^ 2 / vτ τ : ℝ)| ≤ 20 / 3 := by rwa [abs_of_nonneg hb0]
  rw [ea, eb, ec]
  have t1 : ‖((-4 * τ : ℝ) : ℂ) * ν ^ 3‖ ≤ 2 * νp ^ 3 := by
    rw [norm_ofReal_mul, norm_pow]
    exact mul_le_mul ha (pow_le_pow_left₀ hn0 hν 3) (pow_nonneg hn0 3) (by norm_num)
  have t2 : ‖((6 + 2 * τ ^ 2 / vτ τ : ℝ) : ℂ) * ν ^ 2‖ ≤ 20 / 3 * νp ^ 2 := by
    rw [norm_ofReal_mul, norm_pow]
    exact mul_le_mul hb' (pow_le_pow_left₀ hn0 hν 2) (pow_nonneg hn0 2) (by norm_num)
  have t3 : ‖((4 * τ / vτ τ ^ 2 : ℝ) : ℂ) * ν‖ ≤ 32 / 9 * νp := by
    rw [norm_ofReal_mul]
    exact mul_le_mul hcb' hν hn0 (by norm_num)
  have t4 : ‖d * (ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ)‖ ≤ 16 / 3 * calVOf νp * y0 ^ 2 := by
    rw [norm_mul, norm_mul, norm_ysq h1 h2]
    have u1 := mul_le_mul hd hQ (norm_nonneg _) (by norm_num)
    exact mul_le_mul u1 hY hY0 (mul_nonneg (by norm_num) hV0)
  have hab := norm_add_le (((-4 * τ : ℝ) : ℂ) * ν ^ 3) (((6 + 2 * τ ^ 2 / vτ τ : ℝ) : ℂ) * ν ^ 2)
  have habc := norm_add_le (((-4 * τ : ℝ) : ℂ) * ν ^ 3 + ((6 + 2 * τ ^ 2 / vτ τ : ℝ) : ℂ) * ν ^ 2)
    (((4 * τ / vτ τ ^ 2 : ℝ) : ℂ) * ν)
  have hsub := norm_sub_le (((-4 * τ : ℝ) : ℂ) * ν ^ 3 + ((6 + 2 * τ ^ 2 / vτ τ : ℝ) : ℂ) * ν ^ 2 +
    ((4 * τ / vτ τ ^ 2 : ℝ) : ℂ) * ν) (d * (ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ))
  linarith

/-- The denominator of `T̂` is at least the denominator of `T⁺` (for any `ν` with the stated bounds). -/
private lemma That_den_ge (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) {ν : ℂ} {νp : ℝ}
    (hν : ‖ν‖ ≤ νp) (hQ : ‖ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3‖ ≤ calVOf νp) :
    1 - 4 / 3 * νp * y0 ^ 2 - calVOf νp * y0 ^ 4 ≤
      ‖1 - 2 * (βτ τ : ℂ) * ν * (ysq τ : ℂ) - (ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ) ^ 2‖ := by
  have hn0 := norm_nonneg ν
  have hp0 : 0 ≤ νp := hn0.trans hν
  have hY0 := ysq_nonneg h1 h2
  have hY := ysq_le_y0 h1 h2 hy0
  have hb0 := beta_nonneg h1 h2
  have hb := beta_le h1 h2
  have hV0 := calV_nonneg hp0
  have hrw : 1 - 2 * (βτ τ : ℂ) * ν * (ysq τ : ℂ) - (ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ) ^ 2 =
      1 - (2 * (βτ τ : ℂ) * ν * (ysq τ : ℂ) + (ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ) ^ 2) := by ring
  rw [hrw]
  have hsub := norm_sub_norm_le (1 : ℂ)
    (2 * (βτ τ : ℂ) * ν * (ysq τ : ℂ) + (ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ) ^ 2)
  rw [norm_one] at hsub
  have hadd := norm_add_le (2 * (βτ τ : ℂ) * ν * (ysq τ : ℂ))
    ((ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ) ^ 2)
  have e1 : ‖2 * (βτ τ : ℂ) * ν * (ysq τ : ℂ)‖ ≤ 4 / 3 * νp * y0 ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg hb0, norm_ysq h1 h2]
    have hb2 : 2 * βτ τ ≤ 4 / 3 := by linarith
    have u1 := mul_le_mul hb2 hν hn0 (by norm_num)
    have u2 := mul_le_mul u1 hY hY0 (by linarith)
    linarith
  have e2 : ‖(ν ^ 4 + 2 * (βτ τ : ℂ) * ν ^ 3) * (ysq τ : ℂ) ^ 2‖ ≤ calVOf νp * y0 ^ 4 := by
    rw [norm_mul, norm_pow, norm_ysq h1 h2]
    have hY2 : ysq τ ^ 2 ≤ y0 ^ 4 := by
      calc ysq τ ^ 2 ≤ (y0 ^ 2) ^ 2 := pow_le_pow_left₀ hY0 hY 2
        _ = y0 ^ 4 := by ring
    exact mul_le_mul hQ hY2 (sq_nonneg _) hV0
  linarith

private lemma TPlus_den_pos {νp : ℝ} (h0 : 0 ≤ νp) (h2 : νp ≤ 2) :
    0 < 1 - 4 / 3 * νp * y0 ^ 2 - calVOf νp * y0 ^ 4 := by
  have hV := calV_le h0 h2
  have hV0 := calV_nonneg h0
  have hy4 : y0 ^ 4 = (289 / 6400) ^ 2 := by rw [show y0 ^ 4 = (y0 ^ 2) ^ 2 by ring, y0_sq]
  rw [y0_sq, hy4]
  nlinarith

private lemma That_le (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {νp : ℝ} (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) : ‖That τ c‖ ≤ TPlusOf νp := by
  have hp0 : 0 ≤ νp := (norm_nonneg _).trans hν
  have hL := TPlus_den_pos hp0 hνp
  have hQ := norm_quartic_le h1 h2 hν
  have hnum := That_num_le h1 h2 hy0 hν (norm_D_le h1 h2 hc) hQ
  have hden := That_den_ge h1 h2 hy0 hν hQ
  rw [That_eq]
  show ‖_ / _‖ ≤ _
  rw [norm_div]
  unfold TPlusOf
  exact div_le_div₀ ((norm_nonneg _).trans hnum) hnum hL hden

/-- `|Π̂_o(iy)|` from below, for any `ν` with the stated bounds. -/
private lemma PihatO_ge_aux (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) {ν : ℂ} {νp : ℝ}
    (hν : ‖ν‖ ≤ νp) (hprod : ‖ν * (ν + 2 * (βτ τ : ℂ))‖ ≤ min (20 / 9) (νp ^ 2 + 4 / 3 * νp))
    (hne : 1 + ν ^ 2 * (ysq τ : ℂ) ≠ 0) :
    (1 - min (20 / 9) (νp ^ 2 + 4 / 3 * νp) * y0 ^ 2) / (1 + νp ^ 2 * y0 ^ 2) ^ 2 ≤
      ‖1 - ν * (ν + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)‖ / ‖1 + ν ^ 2 * (ysq τ : ℂ)‖ ^ 2 := by
  have hn0 := norm_nonneg ν
  have hp0 : 0 ≤ νp := hn0.trans hν
  have hY0 := ysq_nonneg h1 h2
  have hY := ysq_le_y0 h1 h2 hy0
  have hnY := norm_ysq h1 h2
  have hm0 : 0 ≤ min (20 / 9) (νp ^ 2 + 4 / 3 * νp) :=
    le_min (by norm_num) (add_nonneg (sq_nonneg _) (by linarith))
  have hm1 : min (20 / 9) (νp ^ 2 + 4 / 3 * νp) ≤ 20 / 9 := min_le_left _ _
  have hnum : 1 - min (20 / 9) (νp ^ 2 + 4 / 3 * νp) * y0 ^ 2 ≤
      ‖1 - ν * (ν + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)‖ := by
    have hsub := norm_sub_norm_le (1 : ℂ) (ν * (ν + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ))
    rw [norm_one, norm_mul, hnY] at hsub
    have := mul_le_mul hprod hY hY0 hm0
    linarith
  have hnum0 : 0 ≤ 1 - min (20 / 9) (νp ^ 2 + 4 / 3 * νp) * y0 ^ 2 := by
    rw [y0_sq]; nlinarith
  have hden1 : ‖1 + ν ^ 2 * (ysq τ : ℂ)‖ ≤ 1 + νp ^ 2 * y0 ^ 2 := by
    calc ‖1 + ν ^ 2 * (ysq τ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖ν ^ 2 * (ysq τ : ℂ)‖ := norm_add_le _ _
      _ = 1 + ‖ν‖ ^ 2 * ysq τ := by rw [norm_one, norm_mul, norm_pow, hnY]
      _ ≤ 1 + νp ^ 2 * y0 ^ 2 := by
        have := mul_le_mul (pow_le_pow_left₀ hn0 hν 2) hY hY0 (sq_nonneg _)
        linarith
  have hden_pos : 0 < ‖1 + ν ^ 2 * (ysq τ : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  have hden : ‖1 + ν ^ 2 * (ysq τ : ℂ)‖ ^ 2 ≤ (1 + νp ^ 2 * y0 ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hden1 2
  exact div_le_div₀ (hnum0.trans hnum) hnum hden_pos hden

/-- `|ν(ν + 2β)| ≤ min(20/9, (ν⁺)² + (4/3)ν⁺)` for `|c| ≤ 1`, `|ν| ≤ ν⁺`. -/
private lemma norm_nu_mul_le_min (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) {c : ℂ} (hc : ‖c‖ ≤ 1) {νp : ℝ}
    (hν : ‖nuτ τ c‖ ≤ νp) :
    ‖nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ))‖ ≤ min (20 / 9) (νp ^ 2 + 4 / 3 * νp) := by
  have hp0 : 0 ≤ νp := (norm_nonneg _).trans hν
  have hb0 := beta_nonneg h1 h2
  have hb := beta_le h1 h2
  apply le_min
  · exact (norm_nu_mul_le h1 h2 hc).trans (bound_twenty_ninths h1 h2)
  · rw [norm_mul]
    have hadd : ‖nuτ τ c + 2 * (βτ τ : ℂ)‖ ≤ νp + 4 / 3 := by
      calc ‖nuτ τ c + 2 * (βτ τ : ℂ)‖ ≤ ‖nuτ τ c‖ + ‖2 * (βτ τ : ℂ)‖ := norm_add_le _ _
        _ = ‖nuτ τ c‖ + 2 * βτ τ := by rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg hb0]
        _ ≤ νp + 4 / 3 := by linarith
    have := mul_le_mul hν hadd (norm_nonneg _) hp0
    linarith

private lemma PihatO_ge (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {νp : ℝ} (hν : ‖nuτ τ c‖ ≤ νp) : PihatLowOf νp ≤ ‖PihatO τ c‖ := by
  have hne : 1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 := (den_ne h1 h2 (c := c) (by linarith)).1
  have key := PihatO_ge_aux h1 h2 hy0 hν (norm_nu_mul_le_min h1 h2 hc hν) hne
  rw [PihatO_eq]
  show _ ≤ ‖_ / _‖
  rw [norm_div, norm_pow]
  unfold PihatLowOf
  exact key

end caps

theorem lem_4_4_iv_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy : 0 < yτ τ) (hy0 : yτ τ ≤ y0) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) :
    ‖That τ c‖ ≤ TPlusOf νp ∧ PihatLowOf νp ≤ ‖PihatO τ c‖ :=
  ⟨That_le h1 h2 hy0 hc hν hνp, PihatO_ge h1 h2 hy0 hc hν⟩

/-! ### Row `sec4_no_constant` -/

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

private lemma θ₀_pos : 0 < θ₀ := by
  unfold θ₀
  have : 0 < Real.arcsin (17 / 40) := Real.arcsin_pos.mpr (by norm_num)
  linarith

private lemma θ₀_le_pi : θ₀ ≤ Real.pi := by
  unfold θ₀
  linarith [Real.arcsin_le_pi_div_two (17 / 40)]

/-- For `0 < θ ≤ θ₀`, the quotient of `k_π` at `(z_θ, z̄_θ)` is `(½ - τ)/(¾(5/4 + 2τ))` with `τ = ½cos(θ/2)`. -/
private lemma Q_rot_koebe (θ : ℝ) (h0 : 0 < θ) (hθ : θ ≤ θ₀) :
    Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ)) =
      (((1 / 2 - Real.cos (θ / 2) / 2) / ((3 / 4) * (5 / 4 + 2 * (Real.cos (θ / 2) / 2))) : ℝ) : ℂ) := by
  set τ := Real.cos (θ / 2) / 2 with hτ
  set y := Real.sin (θ / 2) / 2 with hy_def
  have hpi := θ₀_le_pi
  have hcos : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
  have hsin : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  have hτ1 : τ ≤ 1 / 2 := by rw [hτ]; linarith [Real.cos_le_one (θ / 2)]
  have hy : 0 < y := by rw [hy_def]; linarith
  have hpyth : y ^ 2 + τ ^ 2 = 1 / 4 := by
    rw [hy_def, hτ]
    have := Real.sin_sq_add_cos_sq (θ / 2)
    linear_combination this / 4
  have hpythC : (y : ℂ) ^ 2 + (τ : ℂ) ^ 2 = 1 / 4 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hpyth
    push_cast at h
    exact h
  have hz : zθ θ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]
    unfold zθ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, norm_div, norm_one, Complex.norm_ofNat]
    norm_num
  have hw : conj (zθ θ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, Complex.norm_conj]
    rwa [mem_ball, dist_zero_right] at hz
  rw [(lem_2_3_rot_proved koebe koebe_mem_S_proved Real.pi).2 _ _ hz hw, Complex.exp_pi_mul_I,
    conj_zθ_eq, zθ_eq]
  rw [← hτ, ← hy_def]
  have hz1 : -1 * ((τ : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hw1 : -1 * ((τ : ℂ) - (y : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hzw : -1 * ((τ : ℂ) + (y : ℂ) * I) ≠ -1 * ((τ : ℂ) - (y : ℂ) * I) := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hs : -1 * ((τ : ℂ) + (y : ℂ) * I) + -1 * ((τ : ℂ) - (y : ℂ) * I) = -2 * (τ : ℂ) := by ring
  have hp : -1 * ((τ : ℂ) + (y : ℂ) * I) * (-1 * ((τ : ℂ) - (y : ℂ) * I)) = 1 / 4 := by
    linear_combination hpythC - (y : ℂ) ^ 2 * I_sq
  exact Q_koebe_pair _ _ τ hz1 hw1 hzw hs hp hτ0

/-- Two-sided bound `(4/27) sin²(θ/2) ≤ Re Q ≤ sin²(θ/2)` for `k_π` and `0 < θ ≤ θ₀`. -/
private lemma Q_rot_koebe_bounds (θ : ℝ) (h0 : 0 < θ) (hθ : θ ≤ θ₀) :
    4 / 27 * Real.sin (θ / 2) ^ 2 ≤ (Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))).re ∧
      (Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))).re ≤ 1 * Real.sin (θ / 2) ^ 2 := by
  rw [Q_rot_koebe θ h0 hθ, Complex.ofReal_re]
  have hpi := θ₀_le_pi
  have hcos : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
  have hc1 := Real.cos_le_one (θ / 2)
  have hpyth := Real.sin_sq_add_cos_sq (θ / 2)
  set C := Real.cos (θ / 2) with hC
  set S := Real.sin (θ / 2) with hS
  have hS2 : S ^ 2 = (1 - C) * (1 + C) := by linear_combination hpyth
  have hden : 0 < 3 / 4 * (5 / 4 + 2 * (C / 2)) := mul_pos (by norm_num) (by linarith)
  constructor
  · rw [le_div_iff₀ hden, hS2]
    have hu : 0 ≤ 1 - C := by linarith
    nlinarith [mul_nonneg (mul_nonneg hu hu) (by linarith : (0 : ℝ) ≤ 13 / 4 + C)]
  · rw [div_le_iff₀ hden, hS2]
    have hu : 0 ≤ 1 - C := by linarith
    nlinarith [mul_nonneg hu hcos, mul_nonneg (mul_nonneg hu hcos) hcos]

theorem sec4_no_constant_proved :
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      C₁ * Real.sin (θ / 2) ^ 2 ≤ (Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))).re ∧
        (Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))).re ≤ C₂ * Real.sin (θ / 2) ^ 2) ∧
      ∀ κ : ℝ, 0 < κ → ∃ f : ℂ → ℂ, InS f ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ θ₀ ∧ (Q f (zθ θ) (conj (zθ θ))).re < κ := by
  refine ⟨⟨4 / 27, 1, by norm_num, Q_rot_koebe_bounds⟩, ?_⟩
  intro κ hκ
  refine ⟨rotate Real.pi koebe, (lem_2_3_rot_proved koebe koebe_mem_S_proved Real.pi).1, ?_⟩
  set θ := min θ₀ (min 1 κ) with hθ_def
  have hθ0 : 0 < θ := lt_min θ₀_pos (lt_min one_pos hκ)
  have hθ1 : θ ≤ θ₀ := min_le_left _ _
  have hθ2 : θ ≤ min 1 κ := min_le_right _ _
  have hθκ : θ ≤ κ := hθ2.trans (min_le_right _ _)
  have hθone : θ ≤ 1 := hθ2.trans (min_le_left _ _)
  refine ⟨θ, hθ0, hθ1, ?_⟩
  have hub := (Q_rot_koebe_bounds θ hθ0 hθ1).2
  have hs0 : 0 ≤ Real.sin (θ / 2) := by
    have hpi := θ₀_le_pi
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsle : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le (by linarith)
  have hsq : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := pow_le_pow_left₀ hs0 hsle 2
  have : (θ / 2) ^ 2 < κ := by nlinarith
  linarith

end Robinson.Proofs
