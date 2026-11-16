/-
Robinson/Proofs/Sec2Basic.lean — proofs of sec2_f_ne, sec2_Q_symm, lem_2_1, intro_gamma_deriv,
intro_factor_two, intro_gamma_coeff.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-- A function of the class `𝒮` takes distinct values at distinct points of the disc (injectivity). -/
theorem sec2_f_ne_proved (f : ℂ → ℂ) (hf : InS f) (z w : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1)
    (hzw : z ≠ w) : f z ≠ f w :=
  fun h => hzw (hf.injOn hz hw h)

/-- `Q_f` is symmetric: swapping `z` and `w` negates both numerator and denominator. -/
theorem sec2_Q_symm_proved (f : ℂ → ℂ) (z w : ℂ) : Q f z w = Q f w z := by
  unfold Q
  rw [← neg_sub (z * deriv f z), ← neg_sub (f z), neg_div_neg_eq]

/-- The identity `Γ f(z) - Γ f(w) = ½ (f(z) - f(w)) Q_f(z, w)`, valid whenever `f(z) ≠ f(w)`. -/
private theorem gam_sub_eq (f : ℂ → ℂ) (z w : ℂ) (hne : f z - f w ≠ 0) :
    Gam f z - Gam f w = (1 / 2 : ℂ) * (f z - f w) * Q f z w := by
  unfold Gam Q
  field_simp
  ring

theorem lem_2_1_proved (f : ℂ → ℂ) (hf : InS f) (z w : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1)
    (hzw : z ≠ w) :
    Gam f z - Gam f w = (1 / 2 : ℂ) * (f z - f w) * Q f z w ∧ (Gam f z = Gam f w ↔ Q f z w = 0) := by
  have hne : f z - f w ≠ 0 := sub_ne_zero.mpr (sec2_f_ne_proved f hf z w hz hw hzw)
  have hid := gam_sub_eq f z w hne
  have hc : (1 / 2 : ℂ) * (f z - f w) ≠ 0 := mul_ne_zero (by norm_num) hne
  refine ⟨hid, ?_⟩
  rw [← sub_eq_zero, hid]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hc
    · exact h1
  · intro h
    rw [h, mul_zero]

/-- Product rule: `(z f(z))' = f(z) + z f'(z) = 2 Γ f(z)`. -/
theorem intro_gamma_deriv_proved (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z) :
    Gam f z = (1 / 2 : ℂ) * deriv (fun x => x * f x) z := by
  have h : deriv (fun x => x * f x) z = 1 * f z + z * deriv f z :=
    ((hasDerivAt_id' z).mul hf.hasDerivAt).deriv
  rw [h]
  unfold Gam
  ring

/-- Multiplying by the nonzero constant `2` does not affect injectivity. -/
theorem intro_factor_two_proved (f : ℂ → ℂ) (U : Set ℂ) :
    Set.InjOn (fun z => 2 * Gam f z) U ↔ Set.InjOn (Gam f) U := by
  constructor
  · intro h x hx y hy hxy
    exact h hx hy (show 2 * Gam f x = 2 * Gam f y by rw [hxy])
  · intro h x hx y hy hxy
    exact h hx hy (mul_left_cancel₀ two_ne_zero hxy)

/-- On the open unit disc, where `f` is analytic, the `n`-th derivative of `Γ f` is
`((n + 1) f^{(n)}(z) + z f^{(n+1)}(z)) / 2` (Leibniz rule for `z f'(z)`, by induction on `n`). -/
private theorem iterate_deriv_gam (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ball 0 1)) (n : ℕ) :
    ∀ z ∈ ball (0 : ℂ) 1,
      deriv^[n] (Gam f) z = (((n : ℂ) + 1) * deriv^[n] f z + z * deriv^[n + 1] f z) / 2 := by
  induction n with
  | zero =>
    intro z _
    simp [Gam]
  | succ n ih =>
    intro z hz
    have hev : deriv^[n] (Gam f) =ᶠ[𝓝 z]
        fun y => (((n : ℂ) + 1) * deriv^[n] f y + y * deriv^[n + 1] f y) / 2 :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) ih
    have h1 : HasDerivAt (deriv^[n] f) (deriv^[n + 1] f z) z := by
      rw [Function.iterate_succ_apply' deriv n f]
      exact ((hf.iterated_deriv n) z hz).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (deriv^[n + 1] f) (deriv^[n + 1 + 1] f z) z := by
      rw [Function.iterate_succ_apply' deriv (n + 1) f]
      exact ((hf.iterated_deriv (n + 1)) z hz).differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun y => (((n : ℂ) + 1) * deriv^[n] f y + y * deriv^[n + 1] f y) / 2)
        ((((n : ℂ) + 1) * deriv^[n + 1] f z + (1 * deriv^[n + 1] f z + z * deriv^[n + 1 + 1] f z)) / 2) z :=
      ((h1.const_mul ((n : ℂ) + 1)).add ((hasDerivAt_id' z).mul h2)).div_const 2
    rw [Function.iterate_succ_apply' deriv n (Gam f), hev.deriv_eq, h3.deriv]
    push_cast
    ring

theorem intro_gamma_coeff_proved (f : ℂ → ℂ) (hf : InS f) (n : ℕ) :
    coeff (Gam f) n = ((n : ℂ) + 1) / 2 * coeff f n := by
  have han : AnalyticOnNhd ℂ f (ball 0 1) := hf.differentiableOn.analyticOnNhd isOpen_ball
  have h := iterate_deriv_gam f han n 0 (mem_ball_self one_pos)
  unfold coeff
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, h, zero_mul, add_zero]
  ring

end Robinson.Proofs
