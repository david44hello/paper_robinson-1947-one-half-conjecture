/-
Robinson/Proofs/Koebe.lean — proofs of koebe_mem_S, prop_2_5, intro_koebe_critical_on_circle.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Basic

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Derivatives of `k(z) = z/(1-z)²` and of `z/(1-z)³` away from `z = 1` -/

private lemma one_sub_ne_zero {z : ℂ} (hz : z ≠ 1) : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)

/-- A point of the open unit disc is not `1`. -/
private lemma ne_one_of_mem_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : z ≠ 1 := by
  rintro rfl
  simp at hz

/-- `k'(z) = (1 + z)/(1 - z)³` for `z ≠ 1`. -/
lemma hasDerivAt_koebe {z : ℂ} (hz : z ≠ 1) : HasDerivAt koebe ((1 + z) / (1 - z) ^ 3) z := by
  have h1 := one_sub_ne_zero hz
  have hden : HasDerivAt (fun x : ℂ => (1 - x) ^ 2) ((2 : ℕ) * (1 - z) ^ (2 - 1) * (0 - 1)) z :=
    ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).pow 2
  have hq := (hasDerivAt_id z).div hden (pow_ne_zero 2 h1)
  have hk : koebe = fun x : ℂ => id x / (1 - x) ^ 2 := rfl
  rw [hk]
  convert hq using 1
  simp only [id]
  field_simp
  ring

lemma deriv_koebe {z : ℂ} (hz : z ≠ 1) : deriv koebe z = (1 + z) / (1 - z) ^ 3 :=
  (hasDerivAt_koebe hz).deriv

/-- `Γk(z) = z/(1-z)³` for `z ≠ 1`. -/
lemma Gam_koebe_eq {z : ℂ} (hz : z ≠ 1) : Gam koebe z = z / (1 - z) ^ 3 := by
  have h1 := one_sub_ne_zero hz
  unfold Gam
  rw [deriv_koebe hz]
  unfold koebe
  field_simp
  ring

/-- `(z/(1-z)³)' = (1 + 2z)/(1 - z)⁴` for `z ≠ 1`. -/
private lemma hasDerivAt_G {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun x : ℂ => x / (1 - x) ^ 3) ((1 + 2 * z) / (1 - z) ^ 4) z := by
  have h1 := one_sub_ne_zero hz
  have hden : HasDerivAt (fun x : ℂ => (1 - x) ^ 3) ((3 : ℕ) * (1 - z) ^ (3 - 1) * (0 - 1)) z :=
    ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).pow 3
  have hq := (hasDerivAt_id z).div hden (pow_ne_zero 3 h1)
  have hG : (fun x : ℂ => x / (1 - x) ^ 3) = fun x : ℂ => id x / (1 - x) ^ 3 := rfl
  rw [hG]
  convert hq using 1
  simp only [id]
  field_simp
  ring

/-- `(Γk)'(z) = (1 + 2z)/(1 - z)⁴` for `z ≠ 1`: near `z`, `Γk` agrees with `x/(1-x)³`. -/
lemma hasDerivAt_Gam_koebe {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (Gam koebe) ((1 + 2 * z) / (1 - z) ^ 4) z := by
  have heq : Gam koebe =ᶠ[𝓝 z] fun x : ℂ => x / (1 - x) ^ 3 :=
    (eventually_ne_nhds hz).mono fun x hx => Gam_koebe_eq hx
  exact (hasDerivAt_G hz).congr_of_eventuallyEq heq

lemma deriv_Gam_koebe {z : ℂ} (hz : z ≠ 1) : deriv (Gam koebe) z = (1 + 2 * z) / (1 - z) ^ 4 :=
  (hasDerivAt_Gam_koebe hz).deriv

lemma deriv_Gam_koebe_neg_half : deriv (Gam koebe) (-1 / 2) = 0 := by
  rw [deriv_Gam_koebe (by norm_num)]
  norm_num

/-! ### `k` is injective on the unit disc -/

/-- `k(z) = k(w)` with `z, w ∈ 𝔻` forces `z = w`, since `z(1-w)² - w(1-z)² = (z - w)(1 - zw)` and `|zw| < 1`. -/
lemma koebe_injOn : Set.InjOn koebe (ball (0 : ℂ) 1) := by
  intro z hz w hw h
  have hz1 := one_sub_ne_zero (ne_one_of_mem_ball hz)
  have hw1 := one_sub_ne_zero (ne_one_of_mem_ball hw)
  rw [mem_ball_zero_iff] at hz hw
  unfold koebe at h
  rw [div_eq_div_iff (pow_ne_zero 2 hz1) (pow_ne_zero 2 hw1)] at h
  have hfac : (z - w) * (1 - z * w) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have hzw : z * w = 1 := (sub_eq_zero.mp h0).symm
    have hn : ‖z‖ * ‖w‖ = 1 := by rw [← norm_mul, hzw, norm_one]
    nlinarith [norm_nonneg z, norm_nonneg w]

/-! ### `Γk` is not injective on `|z| < r` for `r > ½`: an explicit pair -/

/-- If `z w = P`, `z + w = S` and `1 - 3P + PS = 0`, then `z(1-w)³ = w(1-z)³`, because
`z(1-w)³ - w(1-z)³ = (z - w)(1 - 3zw + zw(z + w))`. -/
private lemma cubic_identity (z w P S : ℂ) (hprod : z * w = P) (hsum : z + w = S)
    (hkey : 1 - 3 * P + P * S = 0) : z * (1 - w) ^ 3 = w * (1 - z) ^ 3 := by
  linear_combination (z - w) * hkey + (z - w) * (z + w - 3) * hprod + (z - w) * P * hsum

/-- For `r > ½` there are `z ≠ w` with `|z|, |w| < r` and `Γk(z) = Γk(w)`: take `P` with `¼ < P < min(r², ⅓)`,
`a = (3 - 1/P)/2`, `b = √(P - a²)` and the conjugate pair `z = a + ib`, `w = a - ib`. Then `zw = P`, `z + w = 2a`,
`1 - 3P + 2aP = 0`, and `P - a² = (4P - 1)(P - 1)²/(4P²) > 0`. -/
lemma Gam_koebe_not_injOn {r : ℝ} (hr : 1 / 2 < r) : ¬ Set.InjOn (Gam koebe) (ball (0 : ℂ) r) := by
  have hr2 : (1 / 4 : ℝ) < min (r ^ 2) (1 / 3) := lt_min (by nlinarith) (by norm_num)
  obtain ⟨P, hP1, hP2⟩ := exists_between hr2
  have hPr : P < r ^ 2 := lt_of_lt_of_le hP2 (min_le_left _ _)
  have hP3 : P < 1 / 3 := lt_of_lt_of_le hP2 (min_le_right _ _)
  have hP0 : 0 < P := by linarith
  set a : ℝ := (3 - 1 / P) / 2 with ha
  have hpos : 0 < P - a ^ 2 := by
    have h4 : 4 * P ^ 2 * (P - a ^ 2) = (4 * P - 1) * (P - 1) ^ 2 := by
      rw [ha]; field_simp; ring
    have hrhs : 0 < (4 * P - 1) * (P - 1) ^ 2 :=
      mul_pos (by linarith) (by nlinarith)
    have hP2pos : 0 < 4 * P ^ 2 := by positivity
    rw [← h4] at hrhs
    exact pos_of_mul_pos_right hrhs hP2pos.le
  set b : ℝ := Real.sqrt (P - a ^ 2) with hb
  have hbpos : 0 < b := Real.sqrt_pos.mpr hpos
  have hbb : b * b = P - a ^ 2 := Real.mul_self_sqrt hpos.le
  set z : ℂ := ⟨a, b⟩ with hz
  have hnormSq : normSq z = P := by rw [hz, normSq_mk, hbb]; ring
  have hnorm : ‖z‖ < r := by
    have hsq : ‖z‖ ^ 2 < r ^ 2 := by rw [Complex.sq_norm, hnormSq]; exact hPr
    nlinarith [norm_nonneg z]
  have hzim : z.im ≠ 0 := by rw [hz]; exact hbpos.ne'
  have hz1 : z ≠ 1 := fun h => hzim (by rw [h, one_im])
  have hw1 : conj z ≠ 1 := fun h => hzim (by rw [← conj_conj z, h, map_one, one_im])
  have hzw : z ≠ conj z := fun h => hzim (conj_eq_iff_im.mp h.symm)
  have hkey : (1 : ℂ) - 3 * (P : ℂ) + (P : ℂ) * ((2 * z.re : ℝ) : ℂ) = 0 := by
    have hreal : (1 : ℝ) - 3 * P + P * (2 * a) = 0 := by rw [ha]; field_simp; ring
    rw [hz]
    exact_mod_cast hreal
  have hid := cubic_identity z (conj z) (P : ℂ) ((2 * z.re : ℝ) : ℂ)
    (by rw [mul_conj, hnormSq]) (add_conj z) hkey
  intro hinj
  apply hzw
  apply hinj
  · rw [mem_ball_zero_iff]; exact hnorm
  · rw [mem_ball_zero_iff, norm_conj]; exact hnorm
  · rw [Gam_koebe_eq hz1, Gam_koebe_eq hw1,
      div_eq_div_iff (pow_ne_zero 3 (one_sub_ne_zero hz1)) (pow_ne_zero 3 (one_sub_ne_zero hw1))]
    exact hid

/-! ### The rows -/

theorem koebe_mem_S_proved : InS koebe where
  differentiableOn := fun _ hz =>
    (hasDerivAt_koebe (ne_one_of_mem_ball hz)).differentiableAt.differentiableWithinAt
  injOn := koebe_injOn
  map_zero := by simp [koebe]
  deriv_zero := by
    rw [deriv_koebe (by norm_num)]
    norm_num

theorem prop_2_5_proved :
    (∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → Gam koebe z = z / (1 - z) ^ 3) ∧
      (∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → deriv (Gam koebe) z = (1 + 2 * z) / (1 - z) ^ 4) ∧
      deriv (Gam koebe) (-1 / 2) = 0 ∧
      ∀ r : ℝ, 1 / 2 < r → ¬ Set.InjOn (Gam koebe) (ball (0 : ℂ) r) :=
  ⟨fun _ hz => Gam_koebe_eq (ne_one_of_mem_ball hz),
    fun _ hz => deriv_Gam_koebe (ne_one_of_mem_ball hz),
    deriv_Gam_koebe_neg_half,
    fun _ hr => Gam_koebe_not_injOn hr⟩

theorem intro_koebe_critical_on_circle_proved :
    ‖(-1 / 2 : ℂ)‖ = 1 / 2 ∧ deriv (Gam koebe) (-1 / 2) = 0 := by
  refine ⟨?_, deriv_Gam_koebe_neg_half⟩
  rw [norm_div, norm_neg, norm_one, Complex.norm_ofNat]

end Robinson.Proofs
