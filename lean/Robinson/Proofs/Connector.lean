/-
Robinson/Proofs/Connector.lean — proofs of lem_8_1, intro_theta0_approx, sec8_cover.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Taylor bounds for `sin` on `[0, ∞)`

Each bound follows from the previous one: if `f 0 = 0` and `f' ≥ 0` on `[0, ∞)`, then `f ≥ 0` there. -/

/-- If `f 0 = 0` and `f' ≥ 0` on `[0, ∞)`, then `f x ≥ 0` for `x ≥ 0`. -/
private lemma nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hd : ∀ t, 0 ≤ t → 0 ≤ f' t) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hdiff : Differentiable ℝ f := fun t => (hf t).differentiableAt
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn hdiff.differentiableOn
    intro t ht
    rw [interior_Ici] at ht
    rw [(hf t).deriv]
    exact hd t (le_of_lt ht)
  have := hmono (Set.mem_Ici.2 le_rfl) hx hx
  rw [h0] at this
  exact this

/-- `cos t ≤ 1 - t²/2 + t⁴/24` for `t ≥ 0`. -/
private lemma cos_le_taylor4 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have key : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x :=
    nonneg_of_hasDerivAt (f := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s)
      (f' := fun s => -s + s ^ 3 / 6 + Real.sin s)
      (fun t => ((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)).congr_deriv
        (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := Real.sin_ge_sub_cube ht
        linarith)
      hx
  linarith

/-- `sin t ≤ t - t³/6 + t⁵/120` for `t ≥ 0`. -/
private lemma sin_le_taylor5 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have key : 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x :=
    nonneg_of_hasDerivAt (f := fun s => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s)
      (f' := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s)
      (fun t => ((((hasDerivAt_id' (x := t)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)).congr_deriv
        (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := cos_le_taylor4 ht
        linarith)
      hx
  linarith

/-- `cos t ≥ 1 - t²/2 + t⁴/24 - t⁶/720` for `t ≥ 0`. -/
private lemma taylor6_le_cos {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have key : 0 ≤ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) :=
    nonneg_of_hasDerivAt
      (f := fun s => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
      (f' := fun s => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s)
      (fun t => ((Real.hasDerivAt_cos t).sub ((((hasDerivAt_const t (1 : ℝ)).sub
        ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub
        ((hasDerivAt_pow 6 t).div_const 720))).congr_deriv (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := sin_le_taylor5 ht
        linarith)
      hx
  linarith

/-- `sin t ≥ t - t³/6 + t⁵/120 - t⁷/5040` for `t ≥ 0`. -/
private lemma taylor7_le_sin {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have key : 0 ≤ Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) :=
    nonneg_of_hasDerivAt
      (f := fun s => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040))
      (f' := fun s => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
      (fun t => ((Real.hasDerivAt_sin t).sub ((((hasDerivAt_id' (x := t)).sub
        ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub
        ((hasDerivAt_pow 7 t).div_const 5040))).congr_deriv (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := taylor6_le_cos ht
        linarith)
      hx
  linarith

/-! ### Numerical bounds for `sin` from bounds on its argument -/

/-- An upper bound for `sin x` from `0 ≤ l ≤ x ≤ u`. -/
private lemma sin_lt_of_bounds {x l u c : ℝ} (hl : 0 ≤ l) (hlx : l ≤ x) (hxu : x ≤ u)
    (hc : u - l ^ 3 / 6 + u ^ 5 / 120 < c) : Real.sin x < c := by
  have hx : 0 ≤ x := hl.trans hlx
  have h1 := sin_le_taylor5 hx
  have h3 : l ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hl hlx 3
  have h5 : x ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ hx hxu 5
  linarith

/-- A lower bound for `sin x` from `0 ≤ l ≤ x ≤ u`. -/
private lemma lt_sin_of_bounds {x l u c : ℝ} (hl : 0 ≤ l) (hlx : l ≤ x) (hxu : x ≤ u)
    (hc : c < l - u ^ 3 / 6 + l ^ 5 / 120 - u ^ 7 / 5040) : c < Real.sin x := by
  have hx : 0 ≤ x := hl.trans hlx
  have h1 := taylor7_le_sin hx
  have h3 : x ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hx hxu 3
  have h5 : l ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ hl hlx 5
  have h7 : x ^ 7 ≤ u ^ 7 := pow_le_pow_left₀ hx hxu 7
  linarith

/-- `sin (a π) < 17/40` from `π`'s six-digit bounds, when `0 ≤ a` and the check on rationals holds. -/
private lemma sin_mul_pi_lt {a : ℝ} (ha : 0 ≤ a)
    (hc : a * 3.141593 - (a * 3.141592) ^ 3 / 6 + (a * 3.141593) ^ 5 / 120 < 17 / 40) :
    Real.sin (a * Real.pi) < 17 / 40 := by
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  exact sin_lt_of_bounds (mul_nonneg ha (by norm_num)) (by nlinarith) (by nlinarith) hc

/-- `17/40 < sin (a π)` from `π`'s six-digit bounds, when `0 ≤ a` and the check on rationals holds. -/
private lemma lt_sin_mul_pi {a : ℝ} (ha : 0 ≤ a)
    (hc : 17 / 40 < a * 3.141592 - (a * 3.141593) ^ 3 / 6 + (a * 3.141592) ^ 5 / 120
      - (a * 3.141593) ^ 7 / 5040) :
    17 / 40 < Real.sin (a * Real.pi) := by
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  exact lt_sin_of_bounds (mul_nonneg ha (by norm_num)) (by nlinarith) (by nlinarith) hc

/-! ### From `sin` to `θ₀ = 2 arcsin (17/40)` -/

/-- If `0 ≤ a ≤ 180` and `sin (a° / 2) < 17/40`, then `a° < θ₀`. -/
private lemma deg_lt_theta0 {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 180)
    (hs : Real.sin (a / 360 * Real.pi) < 17 / 40) : deg a < θ₀ := by
  have hpi := Real.pi_pos
  have hmem : a / 360 * Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith, by nlinarith⟩
  have h := (Real.lt_arcsin_iff_sin_lt hmem ⟨by norm_num, by norm_num⟩).2 hs
  unfold deg θ₀
  linarith

/-- If `0 ≤ a ≤ 180` and `17/40 < sin (a° / 2)`, then `θ₀ < a°`. -/
private lemma theta0_lt_deg {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 180)
    (hs : 17 / 40 < Real.sin (a / 360 * Real.pi)) : θ₀ < deg a := by
  have hpi := Real.pi_pos
  have hmem : a / 360 * Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith, by nlinarith⟩
  have h := (Real.arcsin_lt_iff_lt_sin ⟨by norm_num, by norm_num⟩ hmem).2 hs
  unfold deg θ₀
  linarith

/-! ### The rows -/

theorem lem_8_1_proved : deg 50.3 < θ₀ ∧ Real.sin (503 * Real.pi / 3600) < 17 / 40 := by
  have hs : Real.sin ((503 / 3600 : ℝ) * Real.pi) < 17 / 40 :=
    sin_mul_pi_lt (by norm_num) (by norm_num)
  refine ⟨deg_lt_theta0 (by norm_num) (by norm_num) ?_, ?_⟩
  · convert hs using 3
    norm_num
  · convert hs using 2
    ring

theorem intro_theta0_approx_proved : deg 50.295 < θ₀ ∧ θ₀ < deg 50.305 := by
  refine ⟨deg_lt_theta0 (by norm_num) (by norm_num) (sin_mul_pi_lt (by norm_num) (by norm_num)),
    theta0_lt_deg (by norm_num) (by norm_num) (lt_sin_mul_pi (by norm_num) (by norm_num))⟩

theorem sec8_cover_proved :
    deg 180 = Real.pi ∧ ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi →
      θ ≤ θ₀ ∨ (deg 50.3 ≤ θ ∧ θ ≤ deg 135) ∨ (deg 135 ≤ θ ∧ θ ≤ deg 180) := by
  have h180 : deg 180 = Real.pi := by
    unfold deg
    ring
  refine ⟨h180, fun θ _ hθ => ?_⟩
  by_cases h1 : θ ≤ θ₀
  · exact Or.inl h1
  · right
    have h2 := lem_8_1_proved.1
    by_cases h3 : θ ≤ deg 135
    · exact Or.inl ⟨by linarith, h3⟩
    · exact Or.inr ⟨by linarith, by rw [h180]; exact hθ⟩

end Robinson.Proofs
