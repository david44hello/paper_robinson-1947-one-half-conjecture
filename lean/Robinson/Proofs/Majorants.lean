/-
Robinson/Proofs/Majorants.lean — proofs of sec4_majorant_rules, sec4_hw_coeff, lem_4_4_i,
sec4_majorant_conv.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.NearP

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The majorant rules -/

/-- A majorant has nonnegative coefficients. -/
private lemma maj_nonneg {F : ℕ → ℂ} {Z : ℕ → ℝ} (h : Majorizes F Z) (n : ℕ) : 0 ≤ Z n :=
  (norm_nonneg _).trans (h n)

/-- `|F(ξ)| ≤ Z(|ξ|)` wherever `Z` converges. -/
private lemma maj_eval (F : ℕ → ℂ) (Z : ℕ → ℝ) (ξ : ℂ) (hFZ : Majorizes F Z)
    (hs : Summable (fun n => Z n * ‖ξ‖ ^ n)) :
    Summable (fun n => F n * ξ ^ n) ∧ ‖∑' n, F n * ξ ^ n‖ ≤ ∑' n, Z n * ‖ξ‖ ^ n := by
  have hb : ∀ n, ‖F n * ξ ^ n‖ ≤ Z n * ‖ξ‖ ^ n := fun n => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hFZ n) (pow_nonneg (norm_nonneg _) _)
  exact ⟨Summable.of_norm_bounded hs hb, tsum_of_norm_bounded hs.hasSum hb⟩

private lemma maj_add {F G : ℕ → ℂ} {Z W : ℕ → ℝ} (hF : Majorizes F Z) (hG : Majorizes G W) :
    Majorizes (fun n => F n + G n) (fun n => Z n + W n) := fun n =>
  (norm_add_le _ _).trans (add_le_add (hF n) (hG n))

private lemma maj_mul {F G : ℕ → ℂ} {Z W : ℕ → ℝ} (hF : Majorizes F Z) (hG : Majorizes G W) :
    Majorizes (cmul F G) (cmul Z W) := by
  intro n
  unfold cmul
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hF k) (hG (n - k)) (norm_nonneg _) (maj_nonneg hF k)

/-- `(1 - F)⁻¹ ≪ (1 - Z)⁻¹`: the solutions of `g = 1 + F g` and `G = 1 + Z G`, by strong induction. -/
private lemma maj_inv (F g : ℕ → ℂ) (Z G : ℕ → ℝ) (hF : Majorizes F Z) (hF0 : F 0 = 0) (hZ0 : Z 0 = 0)
    (hg : ∀ n, g n = (if n = 0 then 1 else 0) + cmul F g n)
    (hG : ∀ n, G n = (if n = 0 then 1 else 0) + cmul Z G n) : Majorizes g G := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rw [hg n, hG n]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs <;> simp
  · unfold cmul
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hF0, hZ0]
    · have hlt : n - k < n := by
        have := Finset.mem_range.mp hk
        omega
      exact mul_le_mul (hF k) (ih _ hlt) (norm_nonneg _) (maj_nonneg hF k)

theorem sec4_majorant_rules_proved :
    (∀ (F : ℕ → ℂ) (Z : ℕ → ℝ) (ξ : ℂ), Majorizes F Z → Summable (fun n => Z n * ‖ξ‖ ^ n) →
      Summable (fun n => F n * ξ ^ n) ∧ ‖∑' n, F n * ξ ^ n‖ ≤ ∑' n, Z n * ‖ξ‖ ^ n) ∧
    (∀ (F G : ℕ → ℂ) (Z W : ℕ → ℝ), Majorizes F Z → Majorizes G W →
      Majorizes (fun n => F n + G n) (fun n => Z n + W n) ∧ Majorizes (cmul F G) (cmul Z W)) ∧
    (∀ (F g : ℕ → ℂ) (Z G : ℕ → ℝ), Majorizes F Z → F 0 = 0 → Z 0 = 0 →
      (∀ n, g n = (if n = 0 then 1 else 0) + cmul F g n) →
      (∀ n, G n = (if n = 0 then 1 else 0) + cmul Z G n) → Majorizes g G) :=
  ⟨maj_eval, fun _ _ _ _ hF hG => ⟨maj_add hF hG, maj_mul hF hG⟩, maj_inv⟩

/-! ### `B₁`: its power-series coefficients and the positivity of the denominators -/

/-- The coefficients of `B₁(x) = (16/15) x²/(1 - 2x) = ∑_{n ≥ 2} (16/15) 2^{n-2} xⁿ`. -/
private noncomputable def b1coef (n : ℕ) : ℝ := if 2 ≤ n then 16 / 15 * 2 ^ (n - 2) else 0

private lemma b1coef_nonneg (n : ℕ) : 0 ≤ b1coef n := by
  unfold b1coef
  split_ifs <;> positivity

private lemma b1_hasSum (y : ℂ) (hy : ‖y‖ < 1 / 2) :
    HasSum (fun n => (b1coef n : ℂ) * y ^ n) (B1c y) := by
  have h2y : ‖2 * y‖ < 1 := by
    rw [norm_mul]
    norm_num
    linarith
  have hg := (hasSum_geometric_of_norm_lt_one h2y).mul_left (16 / 15 * y ^ 2)
  rw [← hasSum_nat_add_iff' 2]
  have hfun : (fun n => (b1coef (n + 2) : ℂ) * y ^ (n + 2)) = fun n => 16 / 15 * y ^ 2 * (2 * y) ^ n := by
    funext n
    simp only [b1coef, show 2 ≤ n + 2 from by omega, ite_true, Nat.add_sub_cancel]
    push_cast
    ring
  have hval : B1c y - ∑ i ∈ Finset.range 2, (b1coef i : ℂ) * y ^ i =
      16 / 15 * y ^ 2 * (1 - 2 * y)⁻¹ := by
    simp [Finset.sum_range_succ, b1coef, B1c, div_eq_mul_inv]
    ring
  rw [hfun, hval]
  exact hg

private lemma b1_series : HasFPowerSeriesOnBall B1c
    (FormalMultilinearSeries.ofScalars ℂ (fun n => (b1coef n : ℂ))) 0 ((1 / 4 : NNReal) : ENNReal) := by
  have h14 : ((1 / 4 : NNReal) : ℝ) = 1 / 4 := by norm_num
  refine ⟨?_, ENNReal.coe_pos.mpr (by norm_num), ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ 2 fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_of_nonneg (b1coef_nonneg n), h14]
    unfold b1coef
    split_ifs
    · have e1 : (2 : ℝ) ^ (n - 2) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 2)
      have e2 : (2 : ℝ) ^ n * (1 / 4) ^ n ≤ 1 := by
        rw [← mul_pow]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have e3 : (0 : ℝ) ≤ (1 / 4) ^ n := by positivity
      nlinarith
    · norm_num
  · intro y hy
    rw [Metric.eball_coe, mem_ball_zero_iff, h14] at hy
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
    exact b1_hasSum y (by linarith)

/-- The coefficients of `B₁` at `0` are `(16/15) 2^{n-2}` for `n ≥ 2` and `0` below. -/
private lemma coeff_B1c (n : ℕ) : coeff B1c n = (b1coef n : ℂ) := by
  have hp := b1_series.hasFPowerSeriesAt
  have hq := hp.analyticAt.hasFPowerSeriesAt
  have heq := hq.eq_formalMultilinearSeries hp
  have h2 := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ heq
  unfold coeff
  exact congrFun h2 n

/-- `0 ≤ B₁(x) ≤ 2/15` for `|x| ≤ 1/4`. -/
private lemma B1_bounds (x : ℝ) (hx : |x| ≤ 1 / 4) : 0 ≤ B1 x ∧ B1 x ≤ 2 / 15 := by
  have hxl := abs_le.mp hx
  have h1 : 1 / 2 ≤ 1 - 2 * x := by linarith
  have hpos : 0 < 1 - 2 * x := by linarith
  have hx2 : x ^ 2 ≤ 1 / 16 := by nlinarith
  unfold B1
  constructor
  · positivity
  · have : x ^ 2 / (1 - 2 * x) ≤ 1 / 8 := by
      rw [div_le_iff₀ hpos]
      linarith
    linarith

theorem sec4_majorant_conv_proved (νp ηp : ℝ) (hν0 : 0 ≤ νp) (hν : νp ≤ 2) (hη0 : 0 ≤ ηp) (hη : ηp ≤ 1) :
    1 / 2 - 2 / 15 ≤ fdOf νp ηp (1 / 4) ∧ (∀ n : ℕ, (coeff B1c n).im = 0 ∧ 0 ≤ (coeff B1c n).re) ∧
      ∀ x : ℝ, |x| ≤ 1 / 4 → 0 < 1 - 2 / 3 * x ∧ 0 < 1 - 2 * x ∧ 0 < faOf νp x ∧ 0 < fdOf νp ηp x := by
  have hs0 : 0 ≤ Real.sqrt ηp := Real.sqrt_nonneg _
  have hs1 : Real.sqrt ηp ≤ 1 :=
    calc Real.sqrt ηp ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hη
      _ = 1 := Real.sqrt_one
  have hνx : ∀ x : ℝ, |x| ≤ 1 / 4 → νp * x ≤ 1 / 2 := by
    intro x hx
    have hxl := abs_le.mp hx
    nlinarith
  have key : ∀ x : ℝ, |x| ≤ 1 / 4 → 1 / 2 - 2 / 15 ≤ fdOf νp ηp x := by
    intro x hx
    obtain ⟨hB0, hB1⟩ := B1_bounds x hx
    have h1 := hνx x hx
    have h2 : Real.sqrt ηp * B1 x ≤ 2 / 15 := by nlinarith
    unfold fdOf faOf
    linarith
  refine ⟨key _ (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]), fun n => ?_, fun x hx => ?_⟩
  · rw [coeff_B1c]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact b1coef_nonneg n⟩
  · have hxl := abs_le.mp hx
    have h1 := hνx x hx
    have h2 := key x hx
    refine ⟨by linarith, by linarith, ?_, by linarith⟩
    unfold faOf
    linarith

/-! ### Odd and even parts of a power series with nonnegative coefficients -/

/-- A sum of nonnegative terms is monotone in the terms. -/
private lemma tsum_le_of_terms {f g : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n) (hg : Summable g) :
    ∑' n, f n ≤ ∑' n, g n :=
  Summable.tsum_le_tsum hfg (Summable.of_nonneg_of_le hf0 hfg hg) hg

private lemma inj_odd : Function.Injective (fun m : ℕ => 2 * m + 1) := fun a b h => by
  simp only at h
  omega

private lemma inj_even2 : Function.Injective (fun m : ℕ => 2 * m + 2) := fun a b h => by
  simp only at h
  omega

private lemma inj_even : Function.Injective (fun m : ℕ => 2 * m) := fun a b h => by
  simp only at h
  omega

/-- Inside the radius, the derivative-type series `∑ n Zₙ sⁿ` converges. -/
private lemma summable_n_mul {Z : ℕ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n)
    (hS : ∀ x : ℝ, |x| < r → Summable (fun n => Z n * x ^ n)) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < r) :
    Summable (fun n : ℕ => (n : ℝ) * Z n * s ^ n) := by
  obtain ⟨s', hss', hs'r⟩ : ∃ s', s < s' ∧ s' < r := ⟨(s + r) / 2, by linarith, by linarith⟩
  have hs'0 : 0 < s' := by linarith
  have hs'abs : |s'| < r := by rwa [abs_of_pos hs'0]
  have hq0 : 0 ≤ s / s' := div_nonneg hs0 hs'0.le
  have hq1 : s / s' < 1 := (div_lt_one hs'0).mpr hss'
  have hqn : ‖s / s'‖ < 1 := by rwa [Real.norm_of_nonneg hq0]
  have hgeo := hasSum_coe_mul_geometric_of_norm_lt_one hqn
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((hS s' hs'abs).mul_left ((s / s') / (1 - s / s') ^ 2))
  · have := hZ n
    positivity
  · have hle : (n : ℝ) * (s / s') ^ n ≤ (s / s') / (1 - s / s') ^ 2 :=
      le_hasSum hgeo n (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_nonneg hq0 j))
    have hsq : s = s / s' * s' := (div_mul_cancel₀ s hs'0.ne').symm
    calc (n : ℝ) * Z n * s ^ n = ((n : ℝ) * (s / s') ^ n) * (Z n * s' ^ n) := by
          conv_lhs => rw [hsq]
          rw [mul_pow]
          ring
      _ ≤ (s / s') / (1 - s / s') ^ 2 * (Z n * s' ^ n) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (hZ n) (pow_nonneg hs'0.le n))

private lemma odd_hasSum {Z : ℕ → ℝ} {Zf : ℝ → ℝ} {r : ℝ}
    (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) {t : ℝ} (ht : |t| < r) :
    HasSum (fun m : ℕ => Z (2 * m + 1) * t ^ (2 * m + 1)) (oddPart Zf t) := by
  have h1 := hsum t ht
  have h2 := hsum (-t) (by rwa [abs_neg])
  have h3 : HasSum (fun n => (Z n * t ^ n - Z n * (-t) ^ n) / 2) (oddPart Zf t) :=
    (h1.sub h2).div_const 2
  have hzero : ∀ n, n ∉ Set.range (fun m : ℕ => 2 * m + 1) →
      (Z n * t ^ n - Z n * (-t) ^ n) / 2 = 0 := by
    intro n hn
    have hev : Even n := by
      rcases Nat.even_or_odd n with h | ⟨m, rfl⟩
      · exact h
      · exact absurd ⟨m, rfl⟩ hn
    rw [hev.neg_pow]
    ring
  have h4 := (inj_odd.hasSum_iff hzero).mpr h3
  convert h4 using 1
  funext m
  show Z (2 * m + 1) * t ^ (2 * m + 1) =
    (Z (2 * m + 1) * t ^ (2 * m + 1) - Z (2 * m + 1) * (-t) ^ (2 * m + 1)) / 2
  rw [(odd_two_mul_add_one m).neg_pow]
  ring

private lemma even_hasSum {Z : ℕ → ℝ} {Zf : ℝ → ℝ} {r : ℝ}
    (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) {t : ℝ} (ht : |t| < r) :
    HasSum (fun m : ℕ => Z (2 * m + 2) * t ^ (2 * m + 2)) (evenPart Zf t - Z 0) := by
  have h1 := hsum t ht
  have h2 := hsum (-t) (by rwa [abs_neg])
  have h3 : HasSum (fun n => (Z n * t ^ n + Z n * (-t) ^ n) / 2) (evenPart Zf t) :=
    (h1.add h2).div_const 2
  have hzero : ∀ n, n ∉ Set.range (fun m : ℕ => 2 * m) →
      (Z n * t ^ n + Z n * (-t) ^ n) / 2 = 0 := by
    intro n hn
    have hod : Odd n := by
      rcases Nat.even_or_odd n with ⟨m, rfl⟩ | h
      · exact absurd ⟨m, two_mul m⟩ hn
      · exact h
    rw [hod.neg_pow]
    ring
  have h4 := (inj_even.hasSum_iff hzero).mpr h3
  have h5 := (hasSum_nat_add_iff' 1).mpr h4
  convert h5 using 1
  · funext m
    simp only [Function.comp_apply]
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, (show Even (2 * m + 2) from ⟨m + 1, by ring⟩).neg_pow]
    ring
  · simp

private lemma odd_deriv_summable {Z : ℕ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n)
    (hS : ∀ x : ℝ, |x| < r → Summable (fun n => Z n * x ^ n)) {s : ℝ} (hs0 : 0 < s) (hs : s < r) :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * Z (2 * m + 1) * s ^ (2 * m)) := by
  have h := ((summable_n_mul hZ hS hs0.le hs).comp_injective inj_odd).mul_left s⁻¹
  convert h using 1
  funext m
  simp only [Function.comp_apply]
  push_cast
  rw [pow_succ]
  field_simp

private lemma even_deriv_summable {Z : ℕ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n)
    (hS : ∀ x : ℝ, |x| < r → Summable (fun n => Z n * x ^ n)) {s : ℝ} (hs0 : 0 < s) (hs : s < r) :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 2) * Z (2 * m + 2) * s ^ (2 * m + 1)) := by
  have h := ((summable_n_mul hZ hS hs0.le hs).comp_injective inj_even2).mul_left s⁻¹
  convert h using 1
  funext m
  simp only [Function.comp_apply]
  push_cast
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, pow_succ]
  field_simp
  ring

private lemma odd_series_hasDerivAt {Z : ℕ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n)
    (hS : ∀ x : ℝ, |x| < r → Summable (fun n => Z n * x ^ n)) {x : ℝ} (hx : |x| < r) :
    HasDerivAt (fun t => ∑' m : ℕ, Z (2 * m + 1) * t ^ (2 * m + 1))
      (∑' m : ℕ, (2 * (m : ℝ) + 1) * Z (2 * m + 1) * x ^ (2 * m)) x := by
  obtain ⟨s, hxs, hsr⟩ : ∃ s, |x| < s ∧ s < r := ⟨(|x| + r) / 2, by linarith, by linarith⟩
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg x) hxs
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun m : ℕ => (2 * (m : ℝ) + 1) * Z (2 * m + 1) * s ^ (2 * m))
    (g := fun m t => Z (2 * m + 1) * t ^ (2 * m + 1))
    (g' := fun m t => (2 * (m : ℝ) + 1) * Z (2 * m + 1) * t ^ (2 * m))
    (t := ball (0 : ℝ) s) (y₀ := 0)
    (odd_deriv_summable hZ hS hs0 hsr) isOpen_ball (convex_ball 0 s).isPreconnected ?_ ?_
    (mem_ball_self hs0) ?_ ?_
  · intro m y _
    have h := (hasDerivAt_pow (2 * m + 1) y).const_mul (Z (2 * m + 1))
    convert h using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  · intro m y hy
    have hy' : ‖y‖ ≤ s := (mem_ball_zero_iff.mp hy).le
    rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m + 1),
      Real.norm_of_nonneg (hZ _)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy' _)
      (mul_nonneg (by positivity) (hZ _))
  · simp
  · rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact hxs

private lemma even_series_hasDerivAt {Z : ℕ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n)
    (hS : ∀ x : ℝ, |x| < r → Summable (fun n => Z n * x ^ n)) {x : ℝ} (hx : |x| < r) :
    HasDerivAt (fun t => ∑' m : ℕ, Z (2 * m + 2) * t ^ (2 * m + 2))
      (∑' m : ℕ, (2 * (m : ℝ) + 2) * Z (2 * m + 2) * x ^ (2 * m + 1)) x := by
  obtain ⟨s, hxs, hsr⟩ : ∃ s, |x| < s ∧ s < r := ⟨(|x| + r) / 2, by linarith, by linarith⟩
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg x) hxs
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun m : ℕ => (2 * (m : ℝ) + 2) * Z (2 * m + 2) * s ^ (2 * m + 1))
    (g := fun m t => Z (2 * m + 2) * t ^ (2 * m + 2))
    (g' := fun m t => (2 * (m : ℝ) + 2) * Z (2 * m + 2) * t ^ (2 * m + 1))
    (t := ball (0 : ℝ) s) (y₀ := 0)
    (even_deriv_summable hZ hS hs0 hsr) isOpen_ball (convex_ball 0 s).isPreconnected ?_ ?_
    (mem_ball_self hs0) ?_ ?_
  · intro m y _
    have h := (hasDerivAt_pow (2 * m + 2) y).const_mul (Z (2 * m + 2))
    convert h using 1
    rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega]
    push_cast
    ring
  · intro m y hy
    have hy' : ‖y‖ ≤ s := (mem_ball_zero_iff.mp hy).le
    rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m + 2),
      Real.norm_of_nonneg (hZ _)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy' _)
      (mul_nonneg (by positivity) (hZ _))
  · simp
  · rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact hxs

private lemma isOpen_abs_lt (r : ℝ) : IsOpen {t : ℝ | |t| < r} :=
  isOpen_lt continuous_abs continuous_const

private lemma oddPart_hasDerivAt {Z : ℕ → ℝ} {Zf : ℝ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n)
    (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) {x : ℝ} (hx : |x| < r) :
    HasDerivAt (oddPart Zf) (∑' m : ℕ, (2 * (m : ℝ) + 1) * Z (2 * m + 1) * x ^ (2 * m)) x := by
  refine (odd_series_hasDerivAt hZ (fun t ht => (hsum t ht).summable) hx).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_abs_lt r).mem_nhds hx] with t ht
  exact (odd_hasSum hsum ht).tsum_eq.symm

private lemma evenPart_hasDerivAt {Z : ℕ → ℝ} {Zf : ℝ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n)
    (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) {x : ℝ} (hx : |x| < r) :
    HasDerivAt (evenPart Zf) (∑' m : ℕ, (2 * (m : ℝ) + 2) * Z (2 * m + 2) * x ^ (2 * m + 1)) x := by
  refine ((even_series_hasDerivAt hZ (fun t ht => (hsum t ht).summable) hx).const_add (Z 0)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_abs_lt r).mem_nhds hx] with t ht
  rw [(even_hasSum hsum ht).tsum_eq]
  ring

private lemma hasSum_hCoef_terms {Z : ℕ → ℝ} {Zf : ℝ → ℝ} {r : ℝ} (hZ1 : Z 1 = 0)
    (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) {x : ℝ} (hx0 : 0 < x) (hxr : x < r) :
    HasSum (fun j : ℕ => if 1 ≤ j then Z (2 * j + 1) * x ^ (2 * j) else 0) (frakHat Zf x) := by
  have hx : |x| < r := by rwa [abs_of_pos hx0]
  have h := (odd_hasSum hsum hx).div_const x
  unfold frakHat
  convert h using 1
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hZ1]
  · simp only [show 1 ≤ j from by omega, ite_true]
    rw [pow_succ]
    field_simp

private lemma hasSum_wCoef_terms {Z : ℕ → ℝ} {Zf : ℝ → ℝ} {r : ℝ} (hZ : ∀ n, 0 ≤ Z n) (hZ1 : Z 1 = 0)
    (hZ2 : Z 2 = 0) (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) {x : ℝ} (hx0 : 0 < x)
    (hxr : x < r) :
    HasSum (fun j : ℕ => if 1 ≤ j then
      ((2 * (j : ℝ) + 10 / 3) * Z (2 * j + 1) + ((j : ℝ) + 1) * Z (2 * j + 2)) * x ^ (2 * j - 2) else 0)
      (frakWat Zf x) := by
  have hx : |x| < r := by rwa [abs_of_pos hx0]
  have hS : ∀ x : ℝ, |x| < r → Summable (fun n => Z n * x ^ n) := fun x hx => (hsum x hx).summable
  have hA := (odd_deriv_summable hZ hS hx0 hxr).hasSum
  have hO := odd_hasSum hsum hx
  have hB := (even_deriv_summable hZ hS hx0 hxr).hasSum
  have h := (((hA.mul_left x).add (hO.mul_left (7 / 3))).div_const (x ^ 3)).add (hB.div_const (2 * x ^ 3))
  unfold frakWat
  rw [(oddPart_hasDerivAt hZ hsum hx).deriv, (evenPart_hasDerivAt hZ hsum hx).deriv]
  convert h using 1
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hZ1, hZ2]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [show 1 ≤ k + 1 from by omega, ite_true]
    rw [show 2 * (k + 1) - 2 = 2 * k by omega]
    push_cast
    field_simp
    ring

theorem sec4_hw_coeff_proved (Z : ℕ → ℝ) (hZ : ∀ n, 0 ≤ Z n) (hZ1 : Z 1 = 0) (hZ2 : Z 2 = 0) (Zf : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r) (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) :
    (∀ x : ℝ, 0 < x → x < r → frakHat Zf x = hCoef Z x ∧ frakWat Zf x = wCoef Z x) ∧
      MonotoneOn (hCoef Z) (Set.Ico 0 r) ∧ MonotoneOn (wCoef Z) (Set.Ico 0 r) := by
  refine ⟨fun x hx0 hxr => ⟨(hasSum_hCoef_terms hZ1 hsum hx0 hxr).tsum_eq.symm,
    (hasSum_wCoef_terms hZ hZ1 hZ2 hsum hx0 hxr).tsum_eq.symm⟩, ?_, ?_⟩
  · intro a ha b hb hab
    rcases eq_or_lt_of_le hb.1 with hb0 | hb0
    · obtain rfl : a = b := le_antisymm hab (hb0 ▸ ha.1)
      exact le_rfl
    · unfold hCoef
      refine tsum_le_of_terms (fun j => ?_) (fun j => ?_) (hasSum_hCoef_terms hZ1 hsum hb0 hb.2).summable
      · split_ifs
        · exact mul_nonneg (hZ _) (pow_nonneg ha.1 _)
        · exact le_rfl
      · split_ifs
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.1 hab _) (hZ _)
        · exact le_rfl
  · intro a ha b hb hab
    rcases eq_or_lt_of_le hb.1 with hb0 | hb0
    · obtain rfl : a = b := le_antisymm hab (hb0 ▸ ha.1)
      exact le_rfl
    · unfold wCoef
      have hc : ∀ j : ℕ, 0 ≤ (2 * (j : ℝ) + 10 / 3) * Z (2 * j + 1) + ((j : ℝ) + 1) * Z (2 * j + 2) :=
        fun j => add_nonneg (mul_nonneg (by positivity) (hZ _)) (mul_nonneg (by positivity) (hZ _))
      refine tsum_le_of_terms (fun j => ?_) (fun j => ?_)
        (hasSum_wCoef_terms hZ hZ1 hZ2 hsum hb0 hb.2).summable
      · split_ifs
        · exact mul_nonneg (hc j) (pow_nonneg ha.1 _)
        · exact le_rfl
      · split_ifs
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.1 hab _) (hc j)
        · exact le_rfl

/-! ### Lemma 4.4 (i): the linear rules at `ξ = iy` -/

private lemma norm_Iy_pow (y : ℝ) (hy : 0 < y) (n : ℕ) : ‖(I * (y : ℂ)) ^ n‖ = y ^ n := by
  rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg hy.le]

/-- `|π₂| = |2c - τ|/v ≤ (2 + τ)/v ≤ 10/3` for `τ ∈ [9/20, 1/2]`, `|c| ≤ 1`. -/
private lemma p2_norm_le (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖(2 * c - (τ : ℂ)) / (vτ τ : ℂ)‖ ≤ 10 / 3 := by
  have hv : 0 < vτ τ := by
    unfold vτ
    nlinarith
  rw [norm_div, Complex.norm_of_nonneg hv.le, div_le_iff₀ hv]
  have hn : ‖2 * c - (τ : ℂ)‖ ≤ 2 + τ := by
    calc ‖2 * c - (τ : ℂ)‖ ≤ ‖2 * c‖ + ‖(τ : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 + τ := by
          rw [norm_mul, Complex.norm_of_nonneg (by linarith : (0 : ℝ) ≤ τ)]
          norm_num
          linarith
  unfold vτ
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0 : ℝ) ≤ 5 * τ + 4)]

private lemma ups_term_bound (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (p2 : ℂ) (hp2 : ‖p2‖ ≤ 10 / 3)
    (dp : ℕ → ℂ) (Z : ℕ → ℝ) (hmaj : Majorizes dp Z) (j : ℕ) (w : ℂ) :
    ‖((2 * (j : ℂ) + 2 * (τ : ℂ) * p2) * dp (2 * j + 1) - 2 * (τ : ℂ) * ((j : ℂ) + 1) * dp (2 * j + 2)) * w‖ ≤
      ((2 * (j : ℝ) + 10 / 3) * Z (2 * j + 1) + ((j : ℝ) + 1) * Z (2 * j + 2)) * ‖w‖ := by
  have hτ : ‖(τ : ℂ)‖ = τ := Complex.norm_of_nonneg (by linarith)
  have hA : ‖2 * (j : ℂ) + 2 * (τ : ℂ) * p2‖ ≤ 2 * j + 10 / 3 := by
    calc ‖2 * (j : ℂ) + 2 * (τ : ℂ) * p2‖ ≤ ‖2 * (j : ℂ)‖ + ‖2 * (τ : ℂ) * p2‖ := norm_add_le _ _
      _ = 2 * j + 2 * τ * ‖p2‖ := by
          rw [norm_mul, norm_mul, norm_mul, hτ, Complex.norm_natCast]
          norm_num
      _ ≤ 2 * j + 10 / 3 := by nlinarith [norm_nonneg p2]
  have hB : ‖2 * (τ : ℂ) * ((j : ℂ) + 1)‖ ≤ (j : ℝ) + 1 := by
    rw [norm_mul, norm_mul, hτ, show (j : ℂ) + 1 = ((j + 1 : ℕ) : ℂ) from (Nat.cast_succ j).symm,
      Complex.norm_natCast]
    push_cast
    norm_num
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
  calc _ ≤ ‖(2 * (j : ℂ) + 2 * (τ : ℂ) * p2) * dp (2 * j + 1)‖ +
        ‖2 * (τ : ℂ) * ((j : ℂ) + 1) * dp (2 * j + 2)‖ := norm_sub_le _ _
    _ = ‖2 * (j : ℂ) + 2 * (τ : ℂ) * p2‖ * ‖dp (2 * j + 1)‖ +
        ‖2 * (τ : ℂ) * ((j : ℂ) + 1)‖ * ‖dp (2 * j + 2)‖ := by rw [norm_mul, norm_mul]
    _ ≤ _ := add_le_add (mul_le_mul hA (hmaj _) (norm_nonneg _) (by positivity))
        (mul_le_mul hB (hmaj _) (norm_nonneg _) (by positivity))

private lemma summable_h_terms {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {y : ℝ} (hy : 0 < y)
    (hZs : Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * y ^ n)) :
    Summable (fun j : ℕ => if 1 ≤ j then Z (2 * j + 1) * y ^ (2 * j) else 0) := by
  have hc := (hZs.comp_injective inj_odd).mul_left y⁻¹
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hc
  · split_ifs
    · exact mul_nonneg (hZ _) (pow_nonneg hy.le _)
    · exact le_rfl
  · simp only [Function.comp_apply]
    have hA0 : 0 ≤ Z (2 * j + 1) * y ^ (2 * j) := mul_nonneg (hZ _) (pow_nonneg hy.le _)
    have e : y⁻¹ * ((((2 * j + 1 : ℕ) : ℝ) + 1) * Z (2 * j + 1) * y ^ (2 * j + 1)) =
        (2 * (j : ℝ) + 2) * (Z (2 * j + 1) * y ^ (2 * j)) := by
      push_cast
      rw [pow_succ]
      field_simp
      ring
    refine le_trans ?_ (le_of_eq e.symm)
    split_ifs
    · nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    · positivity

private lemma summable_w_terms {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {y : ℝ} (hy : 0 < y)
    (hZs : Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * y ^ n)) :
    Summable (fun j : ℕ => if 1 ≤ j then
      ((2 * (j : ℝ) + 10 / 3) * Z (2 * j + 1) + ((j : ℝ) + 1) * Z (2 * j + 2)) * y ^ (2 * j - 2) else 0) := by
  have hc := ((hZs.comp_injective inj_odd).mul_left (10 / 3 * (y ^ 3)⁻¹)).add
    ((hZs.comp_injective inj_even2).mul_left (y ^ 4)⁻¹)
  have hy3 : 0 ≤ (y ^ 3)⁻¹ := by positivity
  have hy4 : 0 ≤ (y ^ 4)⁻¹ := by positivity
  have ht0 : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * Z n * y ^ n := fun n =>
    mul_nonneg (mul_nonneg (by positivity) (hZ n)) (pow_nonneg hy.le n)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hc
  · split_ifs
    · exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) (hZ _)) (mul_nonneg (by positivity) (hZ _)))
        (pow_nonneg hy.le _)
    · exact le_rfl
  · simp only [Function.comp_apply]
    split_ifs with hj
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hA0 : 0 ≤ Z (2 * (k + 1) + 1) * y ^ (2 * k) := mul_nonneg (hZ _) (pow_nonneg hy.le _)
      have hB0 : 0 ≤ Z (2 * (k + 1) + 2) * y ^ (2 * k) := mul_nonneg (hZ _) (pow_nonneg hy.le _)
      have e : 10 / 3 * (y ^ 3)⁻¹ * ((((2 * (k + 1) + 1 : ℕ) : ℝ) + 1) * Z (2 * (k + 1) + 1) *
            y ^ (2 * (k + 1) + 1)) +
          (y ^ 4)⁻¹ * ((((2 * (k + 1) + 2 : ℕ) : ℝ) + 1) * Z (2 * (k + 1) + 2) * y ^ (2 * (k + 1) + 2)) =
          10 / 3 * ((2 * (k : ℝ) + 4) * (Z (2 * (k + 1) + 1) * y ^ (2 * k))) +
            (2 * (k : ℝ) + 5) * (Z (2 * (k + 1) + 2) * y ^ (2 * k)) := by
        push_cast
        field_simp
        ring
      refine le_trans ?_ (le_of_eq e.symm)
      rw [show 2 * (k + 1) - 2 = 2 * k by omega]
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hA0, mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hB0]
    · exact add_nonneg (mul_nonneg (by positivity) (ht0 _)) (mul_nonneg hy4 (ht0 _))

theorem lem_4_4_i_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (y : ℝ) (hy : 0 < y) (hy0 : y ≤ y0) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (dp : ℕ → ℂ) (Z : ℕ → ℝ) (hdp : ∀ n, n ≤ 2 → dp n = 0) (hmaj : Majorizes dp Z)
    (hZs : Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * y ^ n)) :
    ‖PiOddSer dp (I * (y : ℂ))‖ ≤ hCoef Z y ∧
      ‖UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) dp (I * (y : ℂ))‖ ≤ wCoef Z y := by
  have hZ : ∀ n, 0 ≤ Z n := fun n => (norm_nonneg _).trans (hmaj n)
  constructor
  · unfold PiOddSer hCoef
    refine tsum_of_norm_bounded (summable_h_terms hZ hy hZs).hasSum fun m => ?_
    rw [norm_mul, norm_Iy_pow y hy]
    split_ifs with hm
    · exact mul_le_mul_of_nonneg_right (hmaj _) (pow_nonneg hy.le _)
    · obtain rfl : m = 0 := by omega
      simp [hdp 1 (by norm_num)]
  · unfold UpsLin wCoef
    refine tsum_of_norm_bounded (summable_w_terms hZ hy hZs).hasSum fun j => ?_
    split_ifs with hj
    · have h := ups_term_bound τ h1 h2 _ (p2_norm_le τ h1 h2 c hc) dp Z hmaj j ((I * (y : ℂ)) ^ (2 * j - 2))
      rwa [norm_Iy_pow y hy] at h
    · simp

end Robinson.Proofs
