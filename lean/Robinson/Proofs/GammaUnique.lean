/-
Robinson/Proofs/GammaUnique.lean — the one root of `γ = T sin γ` in `(0, π)` (sec6_gamma_unique).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Far

namespace Robinson.Proofs

open Robinson

/-- `T = 211/200 > 0`. -/
lemma gammaU_T_pos : 0 < Tfar := by norm_num [Tfar]

/-- `γ ↦ γ - T sin γ` is strictly convex on `[0, π]`: it is a line minus `T > 0` times `sin`, and `sin` is
strictly concave on `[0, π]`. -/
lemma gammaU_strictConvexOn :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) Real.pi) (fun γ : ℝ => γ - Tfar * Real.sin γ) := by
  refine ⟨convex_Icc 0 Real.pi, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hs := strictConcaveOn_sin_Icc.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hs ⊢
  have key := mul_lt_mul_of_pos_left hs gammaU_T_pos
  linarith

/-- A root of `γ = T sin γ` in `(1/4, π)`: `1/4 - T sin(1/4) < 0` (as `sin(1/4) > 1/4 - (1/4)³/6`) and
`π - T sin π = π > 0`; the intermediate value theorem. -/
lemma gammaU_exists : ∃ γ ∈ Set.Ioo (1 / 4 : ℝ) Real.pi, γ - Tfar * Real.sin γ = 0 := by
  have hcont : ContinuousOn (fun γ : ℝ => γ - Tfar * Real.sin γ) (Set.Icc (1 / 4) Real.pi) :=
    (continuous_id.sub (continuous_const.mul Real.continuous_sin)).continuousOn
  have hle : (1 / 4 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hlow : (1 / 4 : ℝ) - Tfar * Real.sin (1 / 4) < 0 := by
    have hs := Real.sin_gt_sub_cube (x := 1 / 4) (by norm_num)
    norm_num [Tfar] at hs ⊢
    linarith
  have hhigh : (0 : ℝ) < Real.pi - Tfar * Real.sin Real.pi := by
    rw [Real.sin_pi, mul_zero, sub_zero]
    exact Real.pi_pos
  obtain ⟨γ, hγ, hγ0⟩ := intermediate_value_Ioo hle hcont
    (show (0 : ℝ) ∈ Set.Ioo ((1 / 4 : ℝ) - Tfar * Real.sin (1 / 4)) (Real.pi - Tfar * Real.sin Real.pi) from
      ⟨hlow, hhigh⟩)
  exact ⟨γ, hγ, hγ0⟩

/-- Two roots `0 < a < b < π` of `γ = T sin γ` cannot exist: `a` lies strictly between `0` and `b`, where the
strictly convex function `γ - T sin γ` vanishes, so it would be negative at `a`. -/
lemma gammaU_two_roots {a b : ℝ} (ha : a ∈ Set.Ioo 0 Real.pi) (hb : b ∈ Set.Ioo 0 Real.pi) (hab : a < b)
    (hfa : a = Tfar * Real.sin a) (hfb : b = Tfar * Real.sin b) : False := by
  have hb0 : 0 < b := hb.1
  have h0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
  have hbI : b ∈ Set.Icc 0 Real.pi := Set.Ioo_subset_Icc_self hb
  have ht1 : 0 < 1 - a / b := by rw [sub_pos, div_lt_one hb0]; exact hab
  have ht2 : 0 < a / b := div_pos ha.1 hb0
  have key := gammaU_strictConvexOn.2 h0 hbI (ne_of_lt hb0) ht1 ht2 (by ring)
  have hpt : (1 - a / b) * 0 + a / b * b = a := by rw [mul_zero, zero_add, div_mul_cancel₀ a hb0.ne']
  simp only [smul_eq_mul] at key
  rw [hpt, Real.sin_zero, mul_zero, sub_zero] at key
  have ea : a - Tfar * Real.sin a = 0 := by linarith
  have eb : b - Tfar * Real.sin b = 0 := by linarith
  rw [ea, eb] at key
  linarith

/-- sec6_gamma_unique: `γ - T sin γ` is strictly convex on `[0, π]`, vanishes at `0`, and `γ = T sin γ` has exactly
one solution in `(0, π)`. -/
theorem sec6_gamma_unique_proved :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) Real.pi) (fun γ : ℝ => γ - Tfar * Real.sin γ) ∧
    (0 : ℝ) - Tfar * Real.sin 0 = 0 ∧
    ∃! γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) Real.pi ∧ γ = Tfar * Real.sin γ := by
  refine ⟨gammaU_strictConvexOn, by rw [Real.sin_zero, mul_zero, sub_zero], ?_⟩
  obtain ⟨γ, hγ, hγ0⟩ := gammaU_exists
  have hγI : γ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [hγ.1], hγ.2⟩
  refine ⟨γ, ⟨hγI, by linarith⟩, ?_⟩
  rintro y ⟨hy, hyeq⟩
  rcases lt_trichotomy y γ with h | h | h
  · exact (gammaU_two_roots hy hγI h hyeq (by linarith)).elim
  · exact h
  · exact (gammaU_two_roots hγI hy h (by linarith) hyeq).elim

end Robinson.Proofs
