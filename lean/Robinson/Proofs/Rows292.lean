/-
Robinson/Proofs/Rows292.lean — proofs of three rows added for the late-edit rule (1): the closed form and value
of sin(π/8), the weight bounds of the majorants, and the two forms of the denominator 𝒬(c) with 4 - 7τ².
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Near

namespace Robinson.Proofs

open Robinson Complex

/-- `sin(π/8) = √(2 - √2)/2`, and `0.38268 < sin(π/8) < 0.38269`. -/
theorem sec6_sin_pi_8_proved :
    Real.sin (Real.pi / 8) = Real.sqrt (2 - Real.sqrt 2) / 2 ∧
      (38268 / 100000 : ℝ) < Real.sin (Real.pi / 8) ∧ Real.sin (Real.pi / 8) < 38269 / 100000 := by
  rw [Real.sin_pi_div_eight]
  have hs2l : (1414213 / 1000000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2u : Real.sqrt 2 < 1414214 / 1000000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hlo : (76536 / 100000 : ℝ) < Real.sqrt (2 - Real.sqrt 2) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have hhi : Real.sqrt (2 - Real.sqrt 2) < 76538 / 100000 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  exact ⟨rfl, by linarith, by linarith⟩

/-- `|π₂| ≤ 10/3` for `π₂ = (2c - τ)/v`, and the two weight bounds `|2j + 2τπ₂| ≤ 2j + 10/3`, `|2τ(j + 1)| ≤ j + 1`. -/
theorem sec4_weight_bounds_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖(2 * c - (τ : ℂ)) / (vτ τ : ℂ)‖ ≤ 10 / 3 ∧
      ∀ j : ℕ, ‖2 * (j : ℂ) + 2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ))‖ ≤ 2 * j + 10 / 3 ∧
        ‖2 * (τ : ℂ) * ((j : ℂ) + 1)‖ ≤ (j : ℝ) + 1 := by
  have hv : 0 < vτ τ := by
    unfold vτ
    nlinarith
  have hτ : ‖(τ : ℂ)‖ = τ := Complex.norm_of_nonneg (by linarith)
  have hp2 : ‖(2 * c - (τ : ℂ)) / (vτ τ : ℂ)‖ ≤ 10 / 3 := by
    rw [norm_div, Complex.norm_of_nonneg hv.le, div_le_iff₀ hv]
    have hn : ‖2 * c - (τ : ℂ)‖ ≤ 2 + τ := by
      calc ‖2 * c - (τ : ℂ)‖ ≤ ‖2 * c‖ + ‖(τ : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 + τ := by
            rw [norm_mul, hτ]
            norm_num
            linarith
    unfold vτ
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0 : ℝ) ≤ 5 * τ + 4)]
  refine ⟨hp2, fun j => ⟨?_, ?_⟩⟩
  · calc ‖2 * (j : ℂ) + 2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ))‖
          ≤ ‖2 * (j : ℂ)‖ + ‖2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ))‖ := norm_add_le _ _
      _ = 2 * j + 2 * τ * ‖(2 * c - (τ : ℂ)) / (vτ τ : ℂ)‖ := by
          rw [norm_mul, norm_mul, norm_mul, hτ, Complex.norm_natCast]
          norm_num
      _ ≤ 2 * j + 10 / 3 := by nlinarith [norm_nonneg ((2 * c - (τ : ℂ)) / (vτ τ : ℂ))]
  · rw [norm_mul, norm_mul, hτ, show (j : ℂ) + 1 = ((j + 1 : ℕ) : ℂ) from (Nat.cast_succ j).symm,
      Complex.norm_natCast]
    push_cast
    norm_num
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- `v⁴(1 + ν²y²)(1 - ν(ν + 2β)y²) = (v² + (c - τ)²y²)(v² - (c² - τ²)y²)` (the two forms of `𝒬(c)`), and
`4 - 7τ² = 4v²(1 + β²y²) ≥ 9/4` for `τ ≤ ½`. -/
theorem sec4_Qcal_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) :
    (vτ τ : ℂ) ^ 4 * ((1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) *
        (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ))) =
      ((vτ τ : ℂ) ^ 2 + (c - τ) ^ 2 * (ysq τ : ℂ)) * ((vτ τ : ℂ) ^ 2 - (c ^ 2 - (τ : ℂ) ^ 2) * (ysq τ : ℂ)) ∧
    4 - 7 * τ ^ 2 = 4 * vτ τ ^ 2 * (1 + βτ τ ^ 2 * ysq τ) ∧ (9 / 4 : ℝ) ≤ 4 - 7 * τ ^ 2 := by
  have hv : 0 < vτ τ := by
    unfold vτ
    nlinarith
  have hv' : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨?_, ?_, by nlinarith⟩
  · simp only [nuτ, βτ]
    push_cast
    field_simp
    ring
  · simp only [βτ, ysq]
    field_simp
    unfold vτ
    ring

end Robinson.Proofs
