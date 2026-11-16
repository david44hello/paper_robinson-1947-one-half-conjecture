/-
Robinson/Proofs/Assembly.lean — proofs of thm_1_2, rem_8_2 (conditional on the three ranges).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Proofs.Sec2Basic
import Robinson.Proofs.Normalize
import Robinson.Proofs.Connector
import Robinson.Proofs.Sec2Rest

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The points `z_θ` and `\overline{z_θ}` -/

private lemma asm_zθ_mem_ball (θ : ℝ) : zθ θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  unfold zθ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, norm_one, Complex.norm_ofNat]
  norm_num

private lemma asm_conj_zθ_mem_ball (θ : ℝ) : conj (zθ θ) ∈ ball (0 : ℂ) 1 := by
  have h := asm_zθ_mem_ball θ
  rw [mem_ball_zero_iff] at h ⊢
  rwa [Complex.norm_conj]

/-- `\overline{z_θ} = ½ e^{-iθ/2}`. -/
private lemma asm_conj_zθ (θ : ℝ) : conj (zθ θ) = (1 / 2 : ℂ) * exp (((-(θ / 2) : ℝ) : ℂ) * I) := by
  unfold zθ
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
    Complex.conj_ofNat]
  congr 2
  push_cast
  ring

/-- `½ e^{iα} · e^{iβ} = ½ e^{i(α + β)}`. -/
private lemma asm_half_exp_mul (α β : ℝ) :
    (1 / 2 : ℂ) * exp ((α : ℂ) * I) * exp ((β : ℂ) * I) = (1 / 2 : ℂ) * exp (((α + β : ℝ) : ℂ) * I) := by
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- By Lemma 2.3 (rotation): `Q_{g_φ}(z_θ, \overline{z_θ}) = Q_g(½ e^{iφ} e^{iθ/2}, ½ e^{iφ} e^{-iθ/2})`. -/
private lemma asm_Q_rotate_zθ {g : ℂ → ℂ} (hg : InS g) (φ θ : ℝ) :
    Q (rotate φ g) (zθ θ) (conj (zθ θ)) =
      Q g ((1 / 2 : ℂ) * exp ((φ : ℂ) * I) * exp (((θ / 2 : ℝ) : ℂ) * I))
        ((1 / 2 : ℂ) * exp ((φ : ℂ) * I) * exp (((-(θ / 2) : ℝ) : ℂ) * I)) := by
  rw [(lem_2_3_rot_proved g hg φ).2 _ _ (asm_zθ_mem_ball θ) (asm_conj_zθ_mem_ball θ), asm_conj_zθ]
  unfold zθ
  congr 1 <;> ring

/-! ### Reduction of a pair at angular distance `θ` to the pair `(z_θ, \overline{z_θ})` -/

/-- A point of modulus `½` is `½ e^{iα}` for some real `α`. -/
private lemma asm_exists_half_exp {z : ℂ} (hz : ‖z‖ = 1 / 2) :
    ∃ α : ℝ, z = (1 / 2 : ℂ) * exp ((α : ℂ) * I) := by
  refine ⟨arg z, ?_⟩
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [hz]
  push_cast
  ring

/-- On the circle `|z| = ½`: if `w = z e^{±iθ}`, then `Q_g(z, w) = Q_{g_φ}(z_θ, \overline{z_θ})` for some real `φ`
(Lemma 2.3, rotation, and the symmetry of `Q`). -/
private lemma asm_half_reduce {g : ℂ → ℂ} (hg : InS g) {z w : ℂ} (hz : ‖z‖ = 1 / 2) {θ : ℝ}
    (hzw : w = z * exp ((θ : ℂ) * I) ∨ w = z * exp (-((θ : ℂ) * I))) :
    ∃ φ : ℝ, Q g z w = Q (rotate φ g) (zθ θ) (conj (zθ θ)) := by
  obtain ⟨α, rfl⟩ := asm_exists_half_exp hz
  rcases hzw with rfl | rfl
  · refine ⟨α + θ / 2, ?_⟩
    rw [asm_Q_rotate_zθ hg, sec2_Q_symm_proved g ((1 / 2 : ℂ) * exp ((α : ℂ) * I))]
    simp only [asm_half_exp_mul]
    rw [show α + θ / 2 + θ / 2 = α + θ by ring, show α + θ / 2 + -(θ / 2) = α by ring]
  · refine ⟨α - θ / 2, ?_⟩
    have hneg : -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [hneg, asm_Q_rotate_zθ hg]
    simp only [asm_half_exp_mul]
    rw [show α - θ / 2 + θ / 2 = α by ring, show α - θ / 2 + -(θ / 2) = α + -θ by ring]

/-- Dilation (Lemma 2.3): for `0 < r ≤ ½` and `|z| = |w| = r`, the points `z/(2r)`, `w/(2r)` lie on `|u| = ½` and
`Q_f(z, w) = Q_F(z/(2r), w/(2r))` with `F(u) = f(2ru)/(2r)` in `𝒮`. -/
private lemma asm_dil_reduce {f : ℂ → ℂ} (hf : InS f) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) {z w : ℂ}
    (hz : ‖z‖ = r) (hw : ‖w‖ = r) :
    ‖z / (2 * (r : ℂ))‖ = 1 / 2 ∧ ‖w / (2 * (r : ℂ))‖ = 1 / 2 ∧
      Q f z w = Q (dilate r f) (z / (2 * (r : ℂ))) (w / (2 * (r : ℂ))) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2r : (2 * (r : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hr0
  have hn2r : ‖(2 * (r : ℂ))‖ = 2 * r := by
    have h2 : (2 * (r : ℂ)) = ((2 * r : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.norm_of_nonneg (by linarith)]
  have hz' : ‖z / (2 * (r : ℂ))‖ = 1 / 2 := by
    rw [norm_div, hz, hn2r]; field_simp
  have hw' : ‖w / (2 * (r : ℂ))‖ = 1 / 2 := by
    rw [norm_div, hw, hn2r]; field_simp
  have hzb : z / (2 * (r : ℂ)) ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hz']; norm_num
  have hwb : w / (2 * (r : ℂ)) ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hw']; norm_num
  have hQ := (lem_2_3_dil_proved f hf r hr hr').2 _ _ hzb hwb
  have hcz : 2 * (r : ℂ) * (z / (2 * (r : ℂ))) = z := by field_simp
  have hcw : 2 * (r : ℂ) * (w / (2 * (r : ℂ))) = w := by field_simp
  rw [hcz, hcw] at hQ
  exact ⟨hz', hw', hQ.symm⟩

/-- For `f ∈ 𝒮`, `0 < r ≤ ½`, `|z| = r` and `w = z e^{±iθ}`: `Q_f(z, w) = Q_g(z_θ, \overline{z_θ})` for some
`g ∈ 𝒮` (a dilation followed by a rotation of `f`). -/
private lemma asm_reduce {f : ℂ → ℂ} (hf : InS f) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) {z w : ℂ}
    (hz : ‖z‖ = r) (hw : ‖w‖ = r) {θ : ℝ}
    (hzw : w = z * exp ((θ : ℂ) * I) ∨ w = z * exp (-((θ : ℂ) * I))) :
    ∃ g : ℂ → ℂ, InS g ∧ Q f z w = Q g (zθ θ) (conj (zθ θ)) := by
  obtain ⟨hz', -, hQ⟩ := asm_dil_reduce hf hr hr' hz hw
  have hF := (lem_2_3_dil_proved f hf r hr hr').1
  have hzw' : w / (2 * (r : ℂ)) = z / (2 * (r : ℂ)) * exp ((θ : ℂ) * I) ∨
      w / (2 * (r : ℂ)) = z / (2 * (r : ℂ)) * exp (-((θ : ℂ) * I)) := by
    rcases hzw with rfl | rfl
    · exact Or.inl (div_mul_eq_mul_div _ _ _).symm
    · exact Or.inr (div_mul_eq_mul_div _ _ _).symm
  obtain ⟨φ, hφ⟩ := asm_half_reduce hF hz' hzw'
  exact ⟨rotate φ (dilate r f), (lem_2_3_rot_proved _ hF φ).1, hQ.trans hφ⟩

/-! ### Theorem 1.2: positivity on pairs of distinct points of a circle `|z| = r ≤ ½` -/

/-- Under the hypothesis `Re Q_g(z_θ, \overline{z_θ}) > 0` for all `g ∈ 𝒮`, `0 < θ ≤ π`: `Re Q_f(z, w) > 0` for
distinct `z, w` on the circle `|z| = ½` (normal form of the pair and Lemma 2.3, rotation). -/
private lemma asm_re_Q_pos_half
    (h : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    {f : ℂ → ℂ} (hf : InS f) {z w : ℂ} (hz : ‖z‖ = 1 / 2) (hw : ‖w‖ = 1 / 2) (hzw : z ≠ w) :
    0 < (Q f z w).re := by
  obtain ⟨φ, θ, hθ0, hθπ, -, hQ⟩ := sec2_pair_normal_form_proved z w hz hw hzw
  rw [hQ f hf]
  exact h _ (lem_2_3_rot_proved f hf φ).1 θ hθ0 hθπ

/-- Under the same hypothesis: `Re Q_f(z, w) > 0` for distinct `z, w` with `|z| = |w| = r ≤ ½` (dilation). -/
private lemma asm_re_Q_pos
    (h : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    {f : ℂ → ℂ} (hf : InS f) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) {z w : ℂ} (hz : ‖z‖ = r)
    (hw : ‖w‖ = r) (hzw : z ≠ w) : 0 < (Q f z w).re := by
  obtain ⟨hz', hw', hQ⟩ := asm_dil_reduce hf hr hr' hz hw
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2r : (2 * (r : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hr0
  have hzw' : z / (2 * (r : ℂ)) ≠ w / (2 * (r : ℂ)) := fun he => hzw ((div_left_inj' h2r).mp he)
  rw [hQ]
  exact asm_re_Q_pos_half h (lem_2_3_dil_proved f hf r hr hr').1 hz' hw' hzw'

/-- The three ranges `(0, θ₀]`, `[50.3°, 135°]`, `[135°, 180°]` cover `(0, π]` (Lemma 8.1), and on each the
hypothesis gives `Re Q_f(z_θ, \overline{z_θ}) > 0` (on the first, `sin²(θ/2)/80 > 0` since `0 < θ/2 < π`). -/
private lemma asm_re_Q_pos_all
    (hnear : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hmiddle : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    (hfar : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re := by
  intro f hf θ hθ0 hθπ
  rcases sec8_cover_proved.2 θ hθ0 hθπ with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
  · have hs : 0 < Real.sin (θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hle := hnear f hf θ hθ0 h1
    have hpos : 0 < Real.sin (θ / 2) ^ 2 / 80 := div_pos (pow_pos hs 2) (by norm_num)
    linarith
  · exact hmiddle f hf θ h2a h2b
  · have hlt := hfar f hf θ h3a h3b
    linarith

theorem thm_1_2_from
    (hnear : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hmiddle : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    (hfar : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 → 1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re) :
    ∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r → z ≠ w →
    0 < (Q f z w).re :=
  fun _ hf _ hr hr' _ _ hz hw hzw => asm_re_Q_pos (asm_re_Q_pos_all hnear hmiddle hfar) hf hr hr' hz hw hzw

/-! ### Remark 8.2: the quantitative bounds -/

theorem rem_8_2_from
    (hnear : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hfar : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 → 1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re) :
    ∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r →
    ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → (w = z * exp ((θ : ℂ) * I) ∨ w = z * exp (-((θ : ℂ) * I))) →
      (θ ≤ θ₀ → Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f z w).re) ∧ (deg 135 ≤ θ → 1 / 2000 < (Q f z w).re) := by
  intro f hf r hr hr' z w hz hw θ hθ0 hθπ hzw
  obtain ⟨g, hg, hQ⟩ := asm_reduce hf hr hr' hz hw hzw
  rw [hQ]
  refine ⟨fun h1 => hnear g hg θ hθ0 h1, fun h3 => hfar g hg θ h3 ?_⟩
  rw [sec8_cover_proved.1]
  exact hθπ

end Robinson.Proofs
