/-
Robinson/Proofs/Lem43.lean — proofs of sec4_circle, lem_4_3, lem_4_5_i and sec4_TJ_holo.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Near

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### `Q̂ = 𝒫/𝒬` with polynomials `𝒫`, `𝒬` in `c`

Multiplying numerator and denominator of `Q̂` by `v⁴` gives `Q̂ = 𝒫(c)/𝒬(c)` with `𝒫` of degree `3` and `𝒬` of
degree `4` in `c` (the coefficient of `c²` in `𝒬` is `0`). -/

/-- Coefficients of the numerator `𝒫(c) = p₀ + p₁c + p₂c² + p₃c³`. -/
private noncomputable def p0 (t : ℝ) : ℝ := 2 - (11 / 2) * t ^ 2 + (7 / 2) * t ^ 4
private noncomputable def p1 (t : ℝ) : ℝ := -3 * t + 6 * t ^ 3 - 3 * t ^ 5
private noncomputable def p2 (t : ℝ) : ℝ := -(3 / 2) + (15 / 2) * t ^ 2 - 6 * t ^ 4
private noncomputable def p3 (t : ℝ) : ℝ := t - 5 * t ^ 3 + 4 * t ^ 5

/-- Coefficients of the denominator `𝒬(c) = q₀ + q₁c + q₃c³ + q₄c⁴`. -/
private noncomputable def q0 (t : ℝ) : ℝ := 1 - (7 / 2) * t ^ 2 + (49 / 16) * t ^ 4
private noncomputable def q1 (t : ℝ) : ℝ := -(1 / 2) * t + (23 / 8) * t ^ 3 - (7 / 2) * t ^ 5
private noncomputable def q3 (t : ℝ) : ℝ := (1 / 8) * t - t ^ 3 + 2 * t ^ 5
private noncomputable def q4 (t : ℝ) : ℝ := -(1 / 16) + (1 / 2) * t ^ 2 - t ^ 4

/-- The numerator `𝒫(c)`. -/
private noncomputable def Pc (t : ℝ) (c : ℂ) : ℂ :=
  (p0 t : ℂ) + (p1 t : ℂ) * c + (p2 t : ℂ) * c ^ 2 + (p3 t : ℂ) * c ^ 3

/-- The denominator `𝒬(c)`. -/
private noncomputable def Qc (t : ℝ) (c : ℂ) : ℂ :=
  (q0 t : ℂ) + (q1 t : ℂ) * c + (q3 t : ℂ) * c ^ 3 + (q4 t : ℂ) * c ^ 4

/-- If `N = P/V` and `D = Q/V` with `V ≠ 0`, then `N/D = P/Q` (also when `Q = 0`). -/
private lemma div_eq_of_scaled {N D P Q V : ℂ} (hV : V ≠ 0) (hN : N = P / V) (hD : D = Q / V) :
    N / D = P / Q := by
  rw [hN, hD, div_div_div_cancel_right₀ hV]

/-- `v = 1 - τ² > 0` for `9/20 ≤ τ ≤ 1/2`. -/
private lemma v_pos (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 0 < vτ τ := by
  unfold vτ; nlinarith

/-- The denominator of `Q̂` is `𝒬(c)/v⁴`. -/
private lemma den_eq (τ : ℝ) (hv : vτ τ ≠ 0) (c : ℂ) :
    (1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) * (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)) =
      Qc τ c / (vτ τ : ℂ) ^ 4 := by
  have hv' : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast hv
  simp only [nuτ, βτ, ysq, Qc, q0, q1, q3, q4]
  unfold vτ at hv' ⊢
  push_cast at hv' ⊢
  field_simp
  ring

/-- `Q̂(τ, c) = 𝒫(c)/𝒬(c)` for every `c`. -/
private lemma qhat_eq (τ : ℝ) (hv : vτ τ ≠ 0) (c : ℂ) : Qhat τ c = Pc τ c / Qc τ c := by
  have hv' : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast hv
  simp only [Qhat]
  refine div_eq_of_scaled (pow_ne_zero 4 hv') ?_ (den_eq τ hv c)
  simp only [Dτ, nuτ, βτ, ysq, Pc, p0, p1, p2, p3]
  unfold vτ at hv' ⊢
  push_cast at hv' ⊢
  field_simp
  ring

/-! ### The denominator does not vanish on the closed disc -/

/-- `|ν| ≤ 1/(1 - τ) ≤ 2` for `|c| ≤ 1`. -/
private lemma nu_norm_le (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖nuτ τ c‖ ≤ 2 := by
  have hv := v_pos τ h1 h2
  have hct : ‖c - (τ : ℂ)‖ ≤ 1 + τ := by
    calc ‖c - (τ : ℂ)‖ ≤ ‖c‖ + ‖(τ : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + τ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
  rw [nuτ, norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le, div_le_iff₀ hv]
  unfold vτ
  nlinarith

/-- `1 + z ≠ 0` when `|z| < 1`. -/
private lemma one_add_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro h
  have : z = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hz
  exact lt_irrefl _ hz

/-- `1 - z ≠ 0` when `|z| < 1`. -/
private lemma one_sub_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, norm_one] at hz
  exact lt_irrefl _ hz

/-- `𝒬(c) ≠ 0` for `9/20 ≤ τ ≤ 1/2` and `|c| ≤ 1`. -/
private lemma Qc_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) : Qc τ c ≠ 0 := by
  have hv := v_pos τ h1 h2
  have hν := nu_norm_le τ h1 h2 c hc
  have hs0 : 0 ≤ ysq τ := by unfold ysq; nlinarith
  have hs1 : ysq τ ≤ 19 / 400 := by unfold ysq; nlinarith
  have hβ0 : 0 ≤ βτ τ := by unfold βτ; positivity
  have hβ1 : βτ τ ≤ 2 / 3 := by
    unfold βτ; rw [div_le_iff₀ hv]; unfold vτ; nlinarith
  have hn0 : 0 ≤ ‖nuτ τ c‖ := norm_nonneg _
  have hA : ‖nuτ τ c ^ 2 * (ysq τ : ℂ)‖ < 1 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0]
    nlinarith
  have hB : ‖nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)‖ < 1 := by
    have h2β : ‖nuτ τ c + 2 * (βτ τ : ℂ)‖ ≤ 2 + 4 / 3 := by
      calc ‖nuτ τ c + 2 * (βτ τ : ℂ)‖ ≤ ‖nuτ τ c‖ + ‖2 * (βτ τ : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 + 4 / 3 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0, Complex.norm_two]
          linarith
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    have hm : ‖nuτ τ c‖ * ‖nuτ τ c + 2 * (βτ τ : ℂ)‖ ≤ 2 * (2 + 4 / 3) :=
      mul_le_mul hν h2β (norm_nonneg _) (by norm_num)
    nlinarith [norm_nonneg (nuτ τ c + 2 * (βτ τ : ℂ))]
  have hD := den_eq τ hv.ne' c
  have hD0 : Qc τ c / (vτ τ : ℂ) ^ 4 ≠ 0 := by
    rw [← hD]
    exact mul_ne_zero (one_add_ne_zero_of_norm_lt hA) (one_sub_ne_zero_of_norm_lt hB)
  intro h
  rw [h, zero_div] at hD0
  exact hD0 rfl

/-! ### Real and imaginary parts on the unit circle (Chebyshev polynomials) -/

/-- On `|c| = 1`, with `x = Re c`, `y = Im c`: `Re cⁿ = 𝒯_n(x)` and `Im cⁿ = y U_{n-1}(x)` for `n = 2, 3, 4`. -/
private lemma cheb (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    (c ^ 2).re = 2 * c.re ^ 2 - 1 ∧ (c ^ 2).im = c.im * (2 * c.re) ∧
    (c ^ 3).re = 4 * c.re ^ 3 - 3 * c.re ∧ (c ^ 3).im = c.im * (4 * c.re ^ 2 - 1) ∧
    (c ^ 4).re = 8 * c.re ^ 4 - 8 * c.re ^ 2 + 1 ∧ (c ^ 4).im = c.im * (8 * c.re ^ 3 - 4 * c.re) := by
  have h2 : c ^ 2 = c * c := by ring
  have h3 : c ^ 3 = c * c * c := by ring
  have h4 : c ^ 4 = c * c * c * c := by ring
  simp only [h2, h3, h4, mul_re, mul_im]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-1 : ℝ) * h
  · ring
  · linear_combination (-3 * c.re) * h
  · linear_combination (-c.im) * h
  · linear_combination (1 - 7 * c.re ^ 2 + c.im ^ 2) * h
  · linear_combination (-4 * c.re * c.im) * h

/-- `Re 𝒫` on the circle, as a polynomial in `(τ, x)`. -/
private noncomputable def PRf (t x : ℝ) : ℝ :=
  p0 t + p1 t * x + p2 t * (2 * x ^ 2 - 1) + p3 t * (4 * x ^ 3 - 3 * x)

/-- `Im 𝒫 / y` on the circle. -/
private noncomputable def PIf (t x : ℝ) : ℝ := p1 t + p2 t * (2 * x) + p3 t * (4 * x ^ 2 - 1)

/-- `Re 𝒬` on the circle. -/
private noncomputable def QRf (t x : ℝ) : ℝ :=
  q0 t + q1 t * x + q3 t * (4 * x ^ 3 - 3 * x) + q4 t * (8 * x ^ 4 - 8 * x ^ 2 + 1)

/-- `Im 𝒬 / y` on the circle. -/
private noncomputable def QIf (t x : ℝ) : ℝ := q1 t + q3 t * (4 * x ^ 2 - 1) + q4 t * (8 * x ^ 3 - 4 * x)

private lemma Pc_re (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Pc t c).re = PRf t c.re := by
  obtain ⟨h2r, -, h3r, -, -, -⟩ := cheb c h
  simp only [Pc, PRf, add_re, re_ofReal_mul, ofReal_re, h2r, h3r]

private lemma Pc_im (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Pc t c).im = c.im * PIf t c.re := by
  obtain ⟨-, h2i, -, h3i, -, -⟩ := cheb c h
  simp only [Pc, PIf, add_im, im_ofReal_mul, ofReal_im, h2i, h3i]
  ring

private lemma Qc_re (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Qc t c).re = QRf t c.re := by
  obtain ⟨-, -, h3r, -, h4r, -⟩ := cheb c h
  simp only [Qc, QRf, add_re, re_ofReal_mul, ofReal_re, h3r, h4r]

private lemma Qc_im (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Qc t c).im = c.im * QIf t c.re := by
  obtain ⟨-, -, -, h3i, -, h4i⟩ := cheb c h
  simp only [Qc, QIf, add_im, im_ofReal_mul, ofReal_im, h3i, h4i]
  ring

/-! ### The polynomial `𝓕(τ, x)` of the proof of Lemma 4.3 and its Bernstein form -/

/-- `𝓕(τ, x)`, of degree `11` in `τ` and `5` in `x`. -/
private noncomputable def Fm (t x : ℝ) : ℝ :=
  (6885 / 8192) + (18765 / 8192) * x - (257 / 160) * x ^ 2 + (7 / 160) * x ^ 3 + (327 / 160) * x ^ 4
    + (63 / 160) * x ^ 5 + (2997 / 1024) * t + (5921 / 2048) * t * x - (244049 / 51200) * t * x ^ 2
    - (2191 / 3200) * t * x ^ 3 + (8889 / 3200) * t * x ^ 4 + (63 / 100) * t * x ^ 5 - (11491 / 2048) * t ^ 2
    - (44099 / 2048) * t ^ 2 * x + (14133 / 1280) * t ^ 2 * x ^ 2 - (485 / 128) * t ^ 2 * x ^ 3
    - (7773 / 320) * t ^ 2 * x ^ 4 - (1449 / 320) * t ^ 2 * x ^ 5 - (23551 / 1280) * t ^ 3
    - (299187 / 10240) * t ^ 3 * x + (2261057 / 51200) * t ^ 3 * x ^ 2 + (131917 / 12800) * t ^ 3 * x ^ 3
    - (406059 / 12800) * t ^ 3 * x ^ 4 - (1449 / 200) * t ^ 3 * x ^ 5 + (210811 / 20480) * t ^ 4
    + (1343459 / 20480) * t ^ 4 * x - (11783 / 1280) * t ^ 4 * x ^ 2 + (68313 / 1600) * t ^ 4 * x ^ 3
    + (1351611 / 12800) * t ^ 4 * x ^ 4 + (47439 / 2560) * t ^ 4 * x ^ 5 + (395671 / 12800) * t ^ 5
    + (5156221 / 51200) * t ^ 5 * x - (7546887 / 51200) * t ^ 5 * x ^ 2 - (724047 / 12800) * t ^ 5 * x ^ 3
    + (1645713 / 12800) * t ^ 5 * x ^ 4 + (47439 / 1600) * t ^ 5 * x ^ 5 - (116463 / 10240) * t ^ 6
    - (632319 / 10240) * t ^ 6 * x - (92717 / 1280) * t ^ 6 * x ^ 2 - (595001 / 3200) * t ^ 6 * x ^ 3
    - (164031 / 800) * t ^ 6 * x ^ 4 - (10143 / 320) * t ^ 6 * x ^ 5 - (6843 / 6400) * t ^ 7
    - (6813221 / 51200) * t ^ 7 * x + (11927531 / 51200) * t ^ 7 * x ^ 2 + (214757 / 1600) * t ^ 7 * x ^ 3
    - (347151 / 1600) * t ^ 7 * x ^ 4 - (10143 / 200) * t ^ 7 * x ^ 5 + (1385561 / 40960) * t ^ 8
    - (8040379 / 204800) * t ^ 8 * x + (1067487 / 6400) * t ^ 8 * x ^ 2 + (28169 / 80) * t ^ 8 * x ^ 3
    + (27867 / 160) * t ^ 8 * x ^ 4 + (3087 / 160) * t ^ 8 * x ^ 5 - (382579 / 25600) * t ^ 9
    + (444819 / 25600) * t ^ 9 * x - (2590751 / 12800) * t ^ 9 * x ^ 2 - (96439 / 800) * t ^ 9 * x ^ 3
    + (103929 / 800) * t ^ 9 * x ^ 4 + (3087 / 100) * t ^ 9 * x ^ 5 - (26147 / 640) * t ^ 10
    + (233959 / 3200) * t ^ 10 * x - (161387 / 1600) * t ^ 10 * x ^ 2 - (48153 / 200) * t ^ 10 * x ^ 3
    - (4851 / 100) * t ^ 10 * x ^ 4 - (4367 / 400) * t ^ 11 + (27577 / 400) * t ^ 11 * x
    + (2289 / 25) * t ^ 11 * x ^ 2 + (441 / 25) * t ^ 11 * x ^ 3

/-- The Bernstein form: with `a = τ - 9/20`, `b = 1/2 - τ`, `p = 1 + x`, `q = 1 - x`, the `72` coefficients are
positive (they are the coefficients after the substitution `τ = (9/20 + u/2)/(1 + u)`, `x = (w - 1)/(w + 1)`). -/
private noncomputable def bernS (a b p q : ℝ) : ℝ :=
  p ^ 0 * q ^ 5 * ((13603014527949 / 1280000000000000) * a ^ 0 * b ^ 11
    + (5044866479248167 / 16384000000000000) * a ^ 1 * b ^ 10
    + (1004027295093903 / 409600000000000) * a ^ 2 * b ^ 9
    + (6522813387379809 / 655360000000000) * a ^ 3 * b ^ 8 + (2541838769199 / 102400000000) * a ^ 4 * b ^ 7
    + (67544360477631 / 1638400000000) * a ^ 5 * b ^ 6 + (15491762487 / 327680000) * a ^ 6 * b ^ 5
    + (1237989933783 / 32768000000) * a ^ 7 * b ^ 4 + (4246688169 / 204800000) * a ^ 8 * b ^ 3
    + (6121413 / 819200) * a ^ 9 * b ^ 2 + (1633689 / 1024000) * a ^ 10 * b ^ 1
    + (1003833 / 6553600) * a ^ 11 * b ^ 0)
    + p ^ 1 * q ^ 4 * ((249900516638041699 / 327680000000000000) * a ^ 0 * b ^ 11
      + (557018142018537511 / 65536000000000000) * a ^ 1 * b ^ 10
      + (560619483825086001 / 13107200000000000) * a ^ 2 * b ^ 9
      + (67280958040153121 / 524288000000000) * a ^ 3 * b ^ 8
      + (8359353805991959 / 32768000000000) * a ^ 4 * b ^ 7 + (2312478435823563 / 6553600000000) * a ^ 5 * b ^ 6
      + (227100359323179 / 655360000000) * a ^ 6 * b ^ 5 + (31669392722643 / 131072000000) * a ^ 7 * b ^ 4
      + (48008311929 / 409600000) * a ^ 8 * b ^ 3 + (6171271497 / 163840000) * a ^ 9 * b ^ 2
      + (189147069 / 26214400) * a ^ 10 * b ^ 1 + (16356573 / 26214400) * a ^ 11 * b ^ 0)
    + p ^ 2 * q ^ 3 * ((47747391749535837 / 16384000000000000) * a ^ 0 * b ^ 11
      + (19621503437097253 / 655360000000000) * a ^ 1 * b ^ 10
      + (456174941588540251 / 3276800000000000) * a ^ 2 * b ^ 9
      + (253323104026483647 / 655360000000000) * a ^ 3 * b ^ 8
      + (11661061057741517 / 16384000000000) * a ^ 4 * b ^ 7 + (149411247046819 / 163840000000) * a ^ 5 * b ^ 6
      + (33956933651643 / 40960000000) * a ^ 6 * b ^ 5 + (17505321961779 / 32768000000) * a ^ 7 * b ^ 4
      + (391332722337 / 1638400000) * a ^ 8 * b ^ 3 + (11543938803 / 163840000) * a ^ 9 * b ^ 2
      + (403613037 / 32768000) * a ^ 10 * b ^ 1 + (6318243 / 6553600) * a ^ 11 * b ^ 0)
    + p ^ 3 * q ^ 2 * ((573837472306865597 / 163840000000000000) * a ^ 0 * b ^ 11
      + (1148680002674592709 / 32768000000000000) * a ^ 1 * b ^ 10
      + (1038827473198343023 / 6553600000000000) * a ^ 2 * b ^ 9
      + (559813770846149407 / 1310720000000000) * a ^ 3 * b ^ 8
      + (1247091427784029 / 1638400000000) * a ^ 4 * b ^ 7 + (3083045239124671 / 3276800000000) * a ^ 5 * b ^ 6
      + (269270648256439 / 327680000000) * a ^ 6 * b ^ 5 + (6632087844609 / 13107200000) * a ^ 7 * b ^ 4
      + (351599137371 / 1638400000) * a ^ 8 * b ^ 3 + (9739051443 / 163840000) * a ^ 9 * b ^ 2
      + (630033147 / 65536000) * a ^ 10 * b ^ 1 + (8916399 / 13107200) * a ^ 11 * b ^ 0)
    + p ^ 4 * q ^ 1 * ((99265311218559981 / 81920000000000000) * a ^ 0 * b ^ 11
      + (100913404043816617 / 8192000000000000) * a ^ 1 * b ^ 10
      + (185144866646669239 / 3276800000000000) * a ^ 2 * b ^ 9
      + (50512147344741841 / 327680000000000) * a ^ 3 * b ^ 8
      + (4546531449469099 / 16384000000000) * a ^ 4 * b ^ 7 + (113160775431281 / 327680000000) * a ^ 5 * b ^ 6
      + (24760295450273 / 81920000000) * a ^ 6 * b ^ 5 + (1517472862371 / 8192000000) * a ^ 7 * b ^ 4
      + (126799697403 / 1638400000) * a ^ 8 * b ^ 3 + (3402681129 / 163840000) * a ^ 9 * b ^ 2
      + (103539141 / 32768000) * a ^ 10 * b ^ 1 + (649539 / 3276800) * a ^ 11 * b ^ 0)
    + p ^ 5 * q ^ 0 * ((12955278613509023 / 65536000000000000) * a ^ 0 * b ^ 11
      + (25127530134375867 / 13107200000000000) * a ^ 1 * b ^ 10
      + (21948175163299077 / 2621440000000000) * a ^ 2 * b ^ 9
      + (11376935284409761 / 524288000000000) * a ^ 3 * b ^ 8
      + (242478421886481 / 6553600000000) * a ^ 4 * b ^ 7 + (11387277252567 / 262144000000) * a ^ 5 * b ^ 6
      + (4675184443843 / 131072000000) * a ^ 6 * b ^ 5 + (533208953727 / 26214400000) * a ^ 7 * b ^ 4
      + (2556910881 / 327680000) * a ^ 8 * b ^ 3 + (7690221 / 4096000) * a ^ 9 * b ^ 2
      + (6383853 / 26214400) * a ^ 10 * b ^ 1 + (59049 / 5242880) * a ^ 11 * b ^ 0)

private lemma bernS_nonneg (a b p q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ bernS a b p q := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' ^ 2 := ⟨Real.sqrt a, (Real.sq_sqrt ha).symm⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' ^ 2 := ⟨Real.sqrt p, (Real.sq_sqrt hp).symm⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' ^ 2 := ⟨Real.sqrt q, (Real.sq_sqrt hq).symm⟩
  unfold bernS
  positivity

private lemma Fm_eq (t x : ℝ) :
    Fm t x = 20 ^ 11 / 32 * bernS (t - 9 / 20) (1 / 2 - t) (1 + x) (1 - x) := by
  unfold Fm bernS
  ring

/-- `𝓕 ≥ 0` on `[9/20, 1/2] × [-1, 1]`. -/
private lemma Fm_nonneg (t x : ℝ) (h1 : 9 / 20 ≤ t) (h2 : t ≤ 1 / 2) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    0 ≤ Fm t x := by
  rw [Fm_eq]
  have := bernS_nonneg (t - 9 / 20) (1 / 2 - t) (1 + x) (1 - x) (by linarith) (by linarith) (by linarith)
    (by linarith)
  positivity

/-- The identity behind (sec4:circle): `q₂ 𝒜 - (q₁ + q₂ E) ℬ = (1 - x) 𝓕` with `𝒜 = Re(𝒫 𝒬̄)`, `ℬ = |𝒬|²` on the
circle, `q₁ = 1/2 - τ`, `q₂ = (3/4)(5/4 + 2τ)`, `E = (13/10) e - (21/200) e²`, `e = 2(1 - x)`. -/
private lemma key_circle (t x : ℝ) :
    3 / 4 * (5 / 4 + 2 * t) * (PRf t x * QRf t x + (1 - x ^ 2) * (PIf t x * QIf t x)) -
        ((1 / 2 - t) + 3 / 4 * (5 / 4 + 2 * t) * (13 / 10 * (2 * (1 - x)) - 21 / 200 * (2 * (1 - x)) ^ 2)) *
          (QRf t x ^ 2 + (1 - x ^ 2) * QIf t x ^ 2) =
      (1 - x) * Fm t x := by
  unfold PRf PIf QRf QIf Fm p0 p1 p2 p3 q0 q1 q3 q4
  ring

/-- From `q₂ A - (q₁ + q₂ E) B = F ≥ 0` with `B, q₂ > 0`: `q₁/q₂ + E ≤ A/B`. -/
private lemma le_of_key {A B q1 q2 E F : ℝ} (hB : 0 < B) (hq2 : 0 < q2)
    (h : q2 * A - (q1 + q2 * E) * B = F) (hF : 0 ≤ F) : q1 / q2 + E ≤ A / B := by
  rw [div_add' _ _ _ hq2.ne', div_le_div_iff₀ hq2 hB]
  nlinarith

/-- (sec4:circle): `Re Q̂ ≥ Q_k + (13/10) e - (21/200) e²` on `|c| = 1`. -/
private lemma circle_ineq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ = 1) :
    Qk τ + 13 / 10 * edef c - 21 / 200 * edef c ^ 2 ≤ (Qhat τ c).re := by
  have hxy : c.re ^ 2 + c.im ^ 2 = 1 := by
    have h := Complex.sq_norm c
    rw [hc, Complex.normSq_apply] at h
    linear_combination -h
  have hy : c.im ^ 2 = 1 - c.re ^ 2 := by linear_combination hxy
  have hx1 : -1 ≤ c.re := by nlinarith
  have hx2 : c.re ≤ 1 := by nlinarith
  have hv := v_pos τ h1 h2.le
  have hQ := Qc_ne τ h1 h2.le c hc.le
  have hB : 0 < normSq (Qc τ c) := Complex.normSq_pos.mpr hQ
  rw [qhat_eq τ hv.ne' c, div_re, ← add_div]
  rw [Complex.normSq_apply] at hB ⊢
  rw [Pc_re τ c hxy, Pc_im τ c hxy, Qc_re τ c hxy, Qc_im τ c hxy] at ⊢
  rw [Qc_re τ c hxy, Qc_im τ c hxy] at hB
  have hQk : Qk τ + 13 / 10 * edef c - 21 / 200 * edef c ^ 2 =
      (1 / 2 - τ) / (3 / 4 * (5 / 4 + 2 * τ)) +
        (13 / 10 * (2 * (1 - c.re)) - 21 / 200 * (2 * (1 - c.re)) ^ 2) := by
    unfold Qk edef; ring
  rw [hQk]
  have hF : 0 ≤ (1 - c.re) * Fm τ c.re := mul_nonneg (by linarith) (Fm_nonneg τ c.re h1 h2.le hx1 hx2)
  refine le_of_key hB (by linarith) ?_ hF
  have hk := key_circle τ c.re
  linear_combination hk +
    (3 / 4 * (5 / 4 + 2 * τ) * (PIf τ c.re * QIf τ c.re) -
      ((1 / 2 - τ) + 3 / 4 * (5 / 4 + 2 * τ) *
        (13 / 10 * (2 * (1 - c.re)) - 21 / 200 * (2 * (1 - c.re)) ^ 2)) * QIf τ c.re ^ 2) * hy

/-! ### Row `sec4_circle` -/

theorem sec4_circle_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ = 1) :
    Qk τ + 13 / 10 * edef c - 21 / 200 * edef c ^ 2 ≤ (Qhat τ c).re ∧
      13 / 10 * edef c - 21 / 200 * edef c ^ 2 = (1 - c.re) * (109 / 50 + 21 / 50 * c.re) :=
  ⟨circle_ineq τ h1 h2 c hc, by unfold edef; ring⟩

/-! ### From the circle to the disc -/

/-- Minimum principle for `Re g`, `g` holomorphic near the closed disc: apply the maximum modulus principle to
`exp(-g)`, whose modulus is `exp(-Re g)`. -/
private lemma re_nonneg_of_sphere {g : ℂ → ℂ} (hd : DifferentiableOn ℂ g (closedBall (0 : ℂ) 1))
    (hb : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ (g z).re) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    0 ≤ (g z).re := by
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hfr : frontier (ball (0 : ℂ) 1) = sphere 0 1 := frontier_ball 0 one_ne_zero
  have hdc : DiffContOnCl ℂ (fun w => Complex.exp (-g w)) (ball (0 : ℂ) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [hcl]
    exact hd.neg.cexp
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (C := 1)
    (fun w hw => by
      rw [hfr] at hw
      rw [Complex.norm_exp, neg_re, Real.exp_le_one_iff]
      linarith [hb w hw])
    (by rwa [hcl])
  rw [Complex.norm_exp, neg_re, Real.exp_le_one_iff] at hle
  linarith

/-- The holomorphic function `Q̂ - Q_k - (13/5)(1 - c) + (21/200)(6 - 8c + 2c²)`; on the circle
`Re(6 - 8c + 2c²) = e²`, inside it is `e² + 2η`. -/
private noncomputable def gfun (τ : ℝ) (c : ℂ) : ℂ :=
  Qhat τ c - (Qk τ : ℂ) - ((13 / 5 : ℝ) : ℂ) * (1 - c) +
    ((21 / 200 : ℝ) : ℂ) * ((6 : ℝ) - (8 : ℝ) * c + (2 : ℝ) * c ^ 2)

private lemma gfun_re (τ : ℝ) (c : ℂ) :
    (gfun τ c).re = (Qhat τ c).re - Qk τ - 13 / 5 * (1 - c.re) +
      21 / 200 * (6 - 8 * c.re + 2 * (c.re ^ 2 - c.im ^ 2)) := by
  have h2 : c ^ 2 = c * c := by ring
  simp only [gfun, h2, sub_re, add_re, mul_re, ofReal_re, ofReal_im, one_re, sub_im, add_im, mul_im, one_im]
  ring

private lemma gfun_diff (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    DifferentiableOn ℂ (gfun τ) (closedBall (0 : ℂ) 1) := by
  have hv := v_pos τ h1 h2.le
  have hfun : gfun τ = fun c => Pc τ c / Qc τ c - (Qk τ : ℂ) - ((13 / 5 : ℝ) : ℂ) * (1 - c) +
      ((21 / 200 : ℝ) : ℂ) * ((6 : ℝ) - (8 : ℝ) * c + (2 : ℝ) * c ^ 2) := by
    funext c
    simp only [gfun, qhat_eq τ hv.ne' c]
  intro z hz
  have hQ : Qc τ z ≠ 0 := Qc_ne τ h1 h2.le z (mem_closedBall_zero_iff.mp hz)
  have hPd : Differentiable ℂ (Pc τ) := by unfold Pc; fun_prop
  have hQd : Differentiable ℂ (Qc τ) := by unfold Qc; fun_prop
  have hq : DifferentiableAt ℂ (fun c => Pc τ c / Qc τ c) z := (hPd z).div (hQd z) hQ
  rw [hfun]
  apply DifferentiableAt.differentiableWithinAt
  fun_prop

private lemma gfun_re_nonneg (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    0 ≤ (gfun τ c).re := by
  refine re_nonneg_of_sphere (gfun_diff τ h1 h2) (fun z hz => ?_) (mem_closedBall_zero_iff.mpr hc)
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hci := circle_ineq τ h1 h2 z hz1
  have hxy : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm z
    rw [hz1, Complex.normSq_apply] at h
    linear_combination -h
  rw [gfun_re]
  unfold edef at hci
  nlinarith

/-- `Q_k(τ) ≥ (16/27) y²` (eq:Qk). -/
private lemma Qk_ge (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) : 16 / 27 * ysq τ ≤ Qk τ := by
  unfold Qk ysq
  rw [le_div_iff₀ (by nlinarith)]
  have hb : 0 ≤ 1 / 2 - τ := by linarith
  nlinarith [mul_nonneg (mul_nonneg hb hb) (by linarith : (0 : ℝ) ≤ τ + 13 / 8)]

/-! ### Row `lem_4_3` -/

theorem lem_4_3_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1) :
    Qk τ + edef c * mρ (etadef c / edef c) ≤ (Qhat τ c).re ∧
      16 / 27 * ysq τ + edef c * mρ (etadef c / edef c) ≤ Qk τ + edef c * mρ (etadef c / edef c) := by
  refine ⟨?_, by linarith [Qk_ge τ h1 h2.le]⟩
  have hg := gfun_re_nonneg τ h1 h2 c hc
  rw [gfun_re] at hg
  have hxy : c.re ^ 2 + c.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm c
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg c]
  have hx1 : c.re < 1 := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have hre : c.re = 1 := by nlinarith [sq_nonneg c.im]
    have him : c.im = 0 := by nlinarith [sq_nonneg c.im]
    exact hc1 (Complex.ext (by simp [hre]) (by simp [him]))
  have he : 0 < edef c := by unfold edef; linarith
  have heta : etadef c = 1 - (c.re ^ 2 + c.im ^ 2) := by
    unfold etadef
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hm : edef c * mρ (etadef c / edef c) = 22 / 25 * edef c + 21 / 100 * etadef c := by
    unfold mρ
    field_simp
  rw [hm, heta]
  unfold edef
  nlinarith [sq_nonneg c.im]

/-! ### Lemma 4.5(i): from the circle to the disc

`∑_{j=2}^{5} |T_j|²/(2j - 1)` is subharmonic in `c` and `20 + 130e = Re(20 + 260(1 - c))` is harmonic. The step is done
with the minimum principle above: for a fixed point `z₀` and `μ_j = T_j(z₀)`, the function
`K = 20 + 260(1 - c) - ∑ (2 μ̄_j T_j - |μ_j|²)/(2j - 1)` is holomorphic, `Re K ≥ 20 + 130e - ∑ |T_j|²/(2j - 1)` on the disc
(because `2 Re(μ̄ T) - |μ|² ≤ |T|²`), with equality at `z₀`. -/

/-- `2 Re(μ̄ a) - |μ|² ≤ |a|²`, divided by `r > 0`. -/
private lemma term_re_le (μ a : ℂ) (r : ℝ) (hr : 0 < r) :
    ((((2 : ℝ) : ℂ) * conj μ * a - ((‖μ‖ ^ 2 : ℝ) : ℂ)) / (r : ℂ)).re ≤ ‖a‖ ^ 2 / r := by
  rw [div_ofReal_re, div_le_div_iff_of_pos_right hr]
  simp only [sub_re, mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im]
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  nlinarith [sq_nonneg (a.re - μ.re), sq_nonneg (a.im - μ.im)]

/-- Equality at `a = μ`. -/
private lemma term_re_eq (μ : ℂ) (r : ℝ) :
    ((((2 : ℝ) : ℂ) * conj μ * μ - ((‖μ‖ ^ 2 : ℝ) : ℂ)) / (r : ℂ)).re = ‖μ‖ ^ 2 / r := by
  rw [div_ofReal_re]
  congr 1
  simp only [sub_re, mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im]
  rw [Complex.sq_norm, normSq_apply]
  ring

/-- If `h_j` (`j ∈ S`) and `L` are holomorphic near the closed disc, `w_j > 0`, and `∑ |h_j|²/w_j ≤ Re L` on the
circle, then the same holds on the closed disc. -/
theorem sum_sq_le_of_sphere (S : Finset ℕ) (h : ℕ → ℂ → ℂ) (wt : ℕ → ℝ) (hwt : ∀ j ∈ S, 0 < wt j)
    (hd : ∀ j ∈ S, DifferentiableOn ℂ (h j) (closedBall (0 : ℂ) 1)) (L : ℂ → ℂ)
    (hL : DifferentiableOn ℂ L (closedBall (0 : ℂ) 1))
    (hb : ∀ w : ℂ, ‖w‖ = 1 → ∑ j ∈ S, ‖h j w‖ ^ 2 / wt j ≤ (L w).re) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∑ j ∈ S, ‖h j z‖ ^ 2 / wt j ≤ (L z).re := by
  let term : ℕ → ℂ → ℂ := fun j w =>
    (((2 : ℝ) : ℂ) * conj (h j z) * h j w - ((‖h j z‖ ^ 2 : ℝ) : ℂ)) / ((wt j : ℝ) : ℂ)
  have hdt : ∀ j ∈ S, DifferentiableOn ℂ (term j) (closedBall (0 : ℂ) 1) := fun j hj =>
    (((hd j hj).const_mul (((2 : ℝ) : ℂ) * conj (h j z))).sub_const _).div_const _
  have hdK : DifferentiableOn ℂ (fun w => L w - ∑ j ∈ S, term j w) (closedBall (0 : ℂ) 1) :=
    hL.sub (DifferentiableOn.fun_sum hdt)
  have hre := re_nonneg_of_sphere hdK (fun w hw => ?_) (mem_closedBall_zero_iff.mpr hz)
  · simp only [sub_re, re_sum] at hre
    have heq : ∀ j ∈ S, (term j z).re = ‖h j z‖ ^ 2 / wt j := fun j _ => term_re_eq _ _
    rw [Finset.sum_congr rfl heq] at hre
    linarith
  · have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
    simp only [sub_re, re_sum]
    have hle : ∑ j ∈ S, (term j w).re ≤ ∑ j ∈ S, ‖h j w‖ ^ 2 / wt j :=
      Finset.sum_le_sum (fun j hj => term_re_le _ _ _ (hwt j hj))
    linarith [hb w hw1]

/-! ### Lemma 4.5(i): the functions `c ↦ T_j(τ, c)` are holomorphic near the closed disc -/

/-- `y² > 0` for `τ < 1/2`. -/
private lemma ysq_pos (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : 0 < ysq τ := by
  unfold ysq; nlinarith

/-- `ξ² = -y²`. -/
private lemma xi_sq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : xiτ τ ^ 2 = -(ysq τ : ℂ) := by
  unfold xiτ yτ
  rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (ysq_pos τ h1 h2).le]
  ring

/-- `|ξ| = y < 1/2`. -/
private lemma norm_xi_lt (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : ‖xiτ τ‖ < 1 / 2 := by
  have hs := ysq_pos τ h1 h2
  have hs1 : ysq τ < 1 / 4 := by unfold ysq; nlinarith
  have hy0 : 0 ≤ yτ τ := Real.sqrt_nonneg _
  have hy2 : yτ τ ^ 2 = ysq τ := Real.sq_sqrt hs.le
  unfold xiτ
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hy0]
  nlinarith

private lemma xi_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : xiτ τ ≠ 0 := by
  intro h
  have := xi_sq τ h1 h2
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, ofReal_eq_zero] at this
  exact (ysq_pos τ h1 h2).ne' this

/-- `1 - νζ ≠ 0` for `|c| ≤ 1`, `|ζ| < 1/2`. -/
private lemma one_sub_nu_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (ζ : ℂ)
    (hζ : ‖ζ‖ < 1 / 2) : 1 - nuτ τ c * ζ ≠ 0 := by
  apply one_sub_ne_zero_of_norm_lt
  rw [norm_mul]
  have := nu_norm_le τ h1 h2.le c hc
  nlinarith [norm_nonneg ζ, norm_nonneg (nuτ τ c)]

/-- `1 + βζ ≠ 0` for `|ζ| < 1/2`. -/
private lemma one_add_beta_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (ζ : ℂ) (hζ : ‖ζ‖ < 1 / 2) :
    1 + (βτ τ : ℂ) * ζ ≠ 0 := by
  have hv := v_pos τ h1 h2.le
  have hβ0 : 0 ≤ βτ τ := by unfold βτ; positivity
  have hβ1 : βτ τ ≤ 2 / 3 := by
    unfold βτ; rw [div_le_iff₀ hv]; unfold vτ; nlinarith
  apply one_add_ne_zero_of_norm_lt
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
  nlinarith [norm_nonneg ζ]

/-- The part `-2ξ^{j+1}(1 + βξ)^{2-j}/v^j` of `Π_j`, which does not depend on `c`. -/
private noncomputable def aJ (τ : ℝ) (j : ℕ) (ζ : ℂ) : ℂ :=
  -2 * ζ ^ (j + 1) * (1 + (βτ τ : ℂ) * ζ) ^ ((2 : ℤ) - j) / (vτ τ : ℂ) ^ j

private lemma PiJ_eq (τ : ℝ) (c : ℂ) (j : ℕ) :
    PiJ τ c j = fun ζ => aJ τ j ζ * ((1 - nuτ τ c * ζ) ^ 3)⁻¹ := by
  funext ζ
  simp only [PiJ, aJ, div_eq_mul_inv, mul_inv]
  ring

/-- The derivative `Π_j'(ζ)` with the `c`-dependence explicit. -/
private noncomputable def dPiJf (τ : ℝ) (c : ℂ) (j : ℕ) (ζ : ℂ) : ℂ :=
  deriv (aJ τ j) ζ * ((1 - nuτ τ c * ζ) ^ 3)⁻¹ +
    aJ τ j ζ * (3 * nuτ τ c * (1 - nuτ τ c * ζ) ^ 2 / ((1 - nuτ τ c * ζ) ^ 3) ^ 2)

private lemma deriv_PiJ (τ : ℝ) (c : ℂ) (j : ℕ) (ζ : ℂ) (hb : 1 + (βτ τ : ℂ) * ζ ≠ 0)
    (hn : 1 - nuτ τ c * ζ ≠ 0) : deriv (PiJ τ c j) ζ = dPiJf τ c j ζ := by
  rw [PiJ_eq]
  have ha : DifferentiableAt ℂ (aJ τ j) ζ := by
    unfold aJ
    fun_prop (disch := exact Or.inl hb)
  have h0 : HasDerivAt (fun w => 1 - nuτ τ c * w) (-nuτ τ c) ζ := by
    simpa using ((hasDerivAt_id ζ).const_mul (nuτ τ c)).const_sub 1
  have h3 := (h0.fun_pow 3).fun_inv (pow_ne_zero 3 hn)
  have h3' : HasDerivAt (fun w => ((1 - nuτ τ c * w) ^ 3)⁻¹)
      (3 * nuτ τ c * (1 - nuτ τ c * ζ) ^ 2 / ((1 - nuτ τ c * ζ) ^ 3) ^ 2) ζ := by
    convert h3 using 1
    norm_num
    ring
  exact (ha.hasDerivAt.fun_mul h3').deriv

/-- `T_j` with the derivatives and `Q̂` in explicit form. -/
private noncomputable def TJf (τ : ℝ) (c : ℂ) (j : ℕ) : ℂ :=
  (-1 / (ysq τ : ℂ)) *
    (((-(τ : ℂ) + xiτ τ) * dPiJf τ c j (xiτ τ) + ((τ : ℂ) + xiτ τ) * dPiJf τ c j (-xiτ τ) -
        (Pc τ c / Qc τ c - 1) * (PiJ τ c j (xiτ τ) - PiJ τ c j (-xiτ τ))) /
      (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ)))

private lemma TJ_eq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (j : ℕ) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    TJ τ c j = TJf τ c j := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  unfold TJ TJf
  rw [deriv_PiJ τ c j _ (one_add_beta_ne τ h1 h2 _ hxi) (one_sub_nu_ne τ h1 h2 c hc _ hxi),
    deriv_PiJ τ c j _ (one_add_beta_ne τ h1 h2 _ hxi') (one_sub_nu_ne τ h1 h2 c hc _ hxi'),
    qhat_eq τ (v_pos τ h1 h2.le).ne' c]

/-- `1 - ν(ν + 2β)y² ≠ 0` and `1 + ν²y² ≠ 0` for `|c| ≤ 1`. -/
private lemma den_factors_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    1 + nuτ τ c ^ 2 * (ysq τ : ℂ) ≠ 0 ∧ 1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ) ≠ 0 := by
  have hv := v_pos τ h1 h2.le
  have hQ := Qc_ne τ h1 h2.le c hc
  have hD := den_eq τ hv.ne' c
  have hD0 : Qc τ c / (vτ τ : ℂ) ^ 4 ≠ 0 :=
    div_ne_zero hQ (pow_ne_zero 4 (by exact_mod_cast hv.ne'))
  rw [← hD] at hD0
  exact ⟨left_ne_zero_of_mul hD0, right_ne_zero_of_mul hD0⟩

/-- `Π̂(ξ) - Π̂(-ξ) ≠ 0`: it equals `2ξ(1 - ν(ν + 2β)y²)/((1 - νξ)(1 + νξ))²`. -/
private lemma pihat_sub_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ) ≠ 0 := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  have ha := pow_ne_zero 2 (one_sub_nu_ne τ h1 h2 c hc _ hxi)
  have hb := pow_ne_zero 2 (one_sub_nu_ne τ h1 h2 c hc _ hxi')
  have hsq := xi_sq τ h1 h2
  unfold Pihat
  rw [div_sub_div _ _ ha hb]
  refine div_ne_zero ?_ (mul_ne_zero ha hb)
  have hnum : xiτ τ * (1 + (βτ τ : ℂ) * xiτ τ) * (1 - nuτ τ c * -xiτ τ) ^ 2 -
      (1 - nuτ τ c * xiτ τ) ^ 2 * (-xiτ τ * (1 + (βτ τ : ℂ) * -xiτ τ)) =
      2 * xiτ τ * (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)) := by
    linear_combination (2 * xiτ τ * (nuτ τ c ^ 2 + 2 * (βτ τ : ℂ) * nuτ τ c)) * hsq
  rw [hnum]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (xi_ne τ h1 h2)) (den_factors_ne τ h1 h2 c hc).2

private lemma TJf_diffAt (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (j : ℕ) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    DifferentiableAt ℂ (fun c => TJf τ c j) c := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  have hn1 := one_sub_nu_ne τ h1 h2 c hc _ hxi
  have hn2 := one_sub_nu_ne τ h1 h2 c hc _ hxi'
  have hQ := Qc_ne τ h1 h2.le c hc
  have hden := pihat_sub_ne τ h1 h2 c hc
  have hν : Differentiable ℂ (fun c => nuτ τ c) := by unfold nuτ; fun_prop
  have hPd : Differentiable ℂ (Pc τ) := by unfold Pc; fun_prop
  have hQd : Differentiable ℂ (Qc τ) := by unfold Qc; fun_prop
  have hq : DifferentiableAt ℂ (fun c => Pc τ c / Qc τ c) c := (hPd c).div (hQd c) hQ
  have hdP : ∀ ζ : ℂ, 1 - nuτ τ c * ζ ≠ 0 → DifferentiableAt ℂ (fun c => dPiJf τ c j ζ) c := by
    intro ζ hζ
    have h3 : (1 - nuτ τ c * ζ) ^ 3 ≠ 0 := pow_ne_zero 3 hζ
    have h6 : ((1 - nuτ τ c * ζ) ^ 3) ^ 2 ≠ 0 := pow_ne_zero 2 h3
    unfold dPiJf
    fun_prop (disch := assumption)
  have hPJ : ∀ ζ : ℂ, 1 - nuτ τ c * ζ ≠ 0 → DifferentiableAt ℂ (fun c => PiJ τ c j ζ) c := by
    intro ζ hζ
    have h3 : (1 - nuτ τ c * ζ) ^ 3 ≠ 0 := pow_ne_zero 3 hζ
    have h3' : ((1 - nuτ τ c * ζ) ^ 3)⁻¹ = ((1 - nuτ τ c * ζ) ^ 3)⁻¹ := rfl
    simp only [PiJ_eq]
    fun_prop (disch := assumption)
  have hPh : ∀ ζ : ℂ, 1 - nuτ τ c * ζ ≠ 0 → DifferentiableAt ℂ (fun c => Pihat τ c ζ) c := by
    intro ζ hζ
    have h2' : (1 - nuτ τ c * ζ) ^ 2 ≠ 0 := pow_ne_zero 2 hζ
    unfold Pihat
    fun_prop (disch := assumption)
  have hA := hdP _ hn1
  have hB := hdP _ hn2
  have hC := hPJ _ hn1
  have hD := hPJ _ hn2
  have hE := hPh _ hn1
  have hF := hPh _ hn2
  unfold TJf
  fun_prop (disch := assumption)

private lemma TJ_diffOn (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (j : ℕ) :
    DifferentiableOn ℂ (fun c => TJ τ c j) (closedBall (0 : ℂ) 1) := by
  have hf : DifferentiableOn ℂ (fun c => TJf τ c j) (closedBall (0 : ℂ) 1) := fun c hc =>
    (TJf_diffAt τ h1 h2 j c (mem_closedBall_zero_iff.mp hc)).differentiableWithinAt
  exact hf.congr (fun c hc => TJ_eq τ h1 h2 j c (mem_closedBall_zero_iff.mp hc))

/-- `TJ = TJf` wherever `1 - νξ ≠ 0` and `1 + νξ ≠ 0` (the proof of `TJ_eq`, without `‖c‖ ≤ 1`). -/
private lemma TJ_eq_of_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (j : ℕ) (c : ℂ)
    (hn1 : 1 - nuτ τ c * xiτ τ ≠ 0) (hn2 : 1 - nuτ τ c * -xiτ τ ≠ 0) : TJ τ c j = TJf τ c j := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  unfold TJ TJf
  rw [deriv_PiJ τ c j _ (one_add_beta_ne τ h1 h2 _ hxi) hn1, deriv_PiJ τ c j _ (one_add_beta_ne τ h1 h2 _ hxi') hn2,
    qhat_eq τ (v_pos τ h1 h2.le).ne' c]

/-- `TJf` is differentiable at `c` wherever its four denominators do not vanish (the proof of `TJf_diffAt`). -/
private lemma TJf_diffAt_of_ne (τ : ℝ) (j : ℕ) (c : ℂ) (hn1 : 1 - nuτ τ c * xiτ τ ≠ 0)
    (hn2 : 1 - nuτ τ c * -xiτ τ ≠ 0) (hQ : Qc τ c ≠ 0) (hden : Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ) ≠ 0) :
    DifferentiableAt ℂ (fun c => TJf τ c j) c := by
  have hν : Differentiable ℂ (fun c => nuτ τ c) := by unfold nuτ; fun_prop
  have hPd : Differentiable ℂ (Pc τ) := by unfold Pc; fun_prop
  have hQd : Differentiable ℂ (Qc τ) := by unfold Qc; fun_prop
  have hq : DifferentiableAt ℂ (fun c => Pc τ c / Qc τ c) c := (hPd c).div (hQd c) hQ
  have hdP : ∀ ζ : ℂ, 1 - nuτ τ c * ζ ≠ 0 → DifferentiableAt ℂ (fun c => dPiJf τ c j ζ) c := by
    intro ζ hζ
    have h3 : (1 - nuτ τ c * ζ) ^ 3 ≠ 0 := pow_ne_zero 3 hζ
    have h6 : ((1 - nuτ τ c * ζ) ^ 3) ^ 2 ≠ 0 := pow_ne_zero 2 h3
    unfold dPiJf
    fun_prop (disch := assumption)
  have hPJ : ∀ ζ : ℂ, 1 - nuτ τ c * ζ ≠ 0 → DifferentiableAt ℂ (fun c => PiJ τ c j ζ) c := by
    intro ζ hζ
    have h3 : (1 - nuτ τ c * ζ) ^ 3 ≠ 0 := pow_ne_zero 3 hζ
    have h3' : ((1 - nuτ τ c * ζ) ^ 3)⁻¹ = ((1 - nuτ τ c * ζ) ^ 3)⁻¹ := rfl
    simp only [PiJ_eq]
    fun_prop (disch := assumption)
  have hPh : ∀ ζ : ℂ, 1 - nuτ τ c * ζ ≠ 0 → DifferentiableAt ℂ (fun c => Pihat τ c ζ) c := by
    intro ζ hζ
    have h2' : (1 - nuτ τ c * ζ) ^ 2 ≠ 0 := pow_ne_zero 2 hζ
    unfold Pihat
    fun_prop (disch := assumption)
  have hA := hdP _ hn1
  have hB := hdP _ hn2
  have hC := hPJ _ hn1
  have hD := hPJ _ hn2
  have hE := hPh _ hn1
  have hF := hPh _ hn2
  unfold TJf
  fun_prop (disch := assumption)

/-- sec_04_near.tex:239: "the `T_j` are holomorphic in `c` there", i.e. near the closed disc `|c| ≤ 1`: on a disc of
radius `R > 1`. (The set where the four denominators of `TJf` do not vanish is open and contains the closed disc; a
compact set inside an open set has a thickening inside it.) -/
theorem sec4_TJ_holo_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    ∃ R : ℝ, 1 < R ∧ ∀ j : ℕ, DifferentiableOn ℂ (fun c => TJ τ c j) (ball (0 : ℂ) R) := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  let U : Set ℂ := {c | 1 - nuτ τ c * xiτ τ ≠ 0 ∧ 1 - nuτ τ c * -xiτ τ ≠ 0 ∧ Qc τ c ≠ 0 ∧
    Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ) ≠ 0}
  have hc1 : Continuous (fun c => 1 - nuτ τ c * xiτ τ) := by unfold nuτ; fun_prop
  have hc2 : Continuous (fun c => 1 - nuτ τ c * -xiτ τ) := by unfold nuτ; fun_prop
  have hcQ : Continuous (Qc τ) := by unfold Qc; fun_prop
  have hν : Differentiable ℂ (fun c => nuτ τ c) := by unfold nuτ; fun_prop
  have hcP : ∀ ζ : ℂ, ∀ c : ℂ, 1 - nuτ τ c * ζ ≠ 0 → ContinuousAt (fun c => Pihat τ c ζ) c := by
    intro ζ c hζ
    have h2' : (1 - nuτ τ c * ζ) ^ 2 ≠ 0 := pow_ne_zero 2 hζ
    have hd : DifferentiableAt ℂ (fun c => Pihat τ c ζ) c := by
      unfold Pihat
      fun_prop (disch := assumption)
    exact hd.continuousAt
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro c hc
    obtain ⟨hn1, hn2, hQ, hD⟩ := hc
    have e1 := hc1.continuousAt.eventually_ne hn1
    have e2 := hc2.continuousAt.eventually_ne hn2
    have e3 := hcQ.continuousAt.eventually_ne hQ
    have e4 := ((hcP _ c hn1).sub (hcP _ c hn2)).eventually_ne hD
    filter_upwards [e1, e2, e3, e4] with c' a b d e using ⟨a, b, d, e⟩
  have hsub : closedBall (0 : ℂ) 1 ⊆ U := by
    intro c hc
    have hc' : ‖c‖ ≤ 1 := mem_closedBall_zero_iff.mp hc
    exact ⟨one_sub_nu_ne τ h1 h2 c hc' _ hxi, one_sub_nu_ne τ h1 h2 c hc' _ hxi', Qc_ne τ h1 h2.le c hc',
      pihat_sub_ne τ h1 h2 c hc'⟩
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hU hsub
  have hball : ball (0 : ℂ) (δ + 1) ⊆ U := by
    rw [← thickening_closedBall hδ zero_le_one]
    exact hδU
  refine ⟨δ + 1, by linarith, fun j c hc => ?_⟩
  have hcU : c ∈ U := hball hc
  have hev : (fun c => TJ τ c j) =ᶠ[𝓝 c] (fun c => TJf τ c j) := by
    filter_upwards [hU.mem_nhds hcU] with c' hc'
    exact TJ_eq_of_ne τ h1 h2 j c' hc'.1 hc'.2.1
  exact ((TJf_diffAt_of_ne τ j c hcU.1 hcU.2.1 hcU.2.2.1 hcU.2.2.2).congr_of_eventuallyEq hev).differentiableWithinAt

/-- Lemma 4.5(i) on the disc, given it on the circle `|c| = 1` (for the same `τ`). -/
theorem lem_4_5_i_of_circle (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (hcirc : ∀ c : ℂ, ‖c‖ = 1 →
      ∑ j ∈ Finset.Icc 2 5, ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) ≤ 20 + 130 * edef c)
    (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ∑ j ∈ Finset.Icc 2 5, ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) ≤ 20 + 130 * edef c := by
  have hL : ∀ w : ℂ, (((20 : ℝ) : ℂ) + ((260 : ℝ) : ℂ) * (1 - w)).re = 20 + 130 * edef w := by
    intro w
    simp only [add_re, ofReal_re, re_ofReal_mul, sub_re, one_re, edef]
    ring
  have hwt : ∀ j ∈ Finset.Icc (2 : ℕ) 5, (0 : ℝ) < 2 * (j : ℝ) - 1 := by
    intro j hj
    have : (2 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    linarith
  have hmain := sum_sq_le_of_sphere (Finset.Icc 2 5) (fun j c => TJ τ c j) (fun j => 2 * (j : ℝ) - 1) hwt
    (fun j _ => TJ_diffOn τ h1 h2 j) (fun w => ((20 : ℝ) : ℂ) + ((260 : ℝ) : ℂ) * (1 - w)) (by fun_prop)
    (fun w hw => by rw [hL]; exact hcirc w hw) c hc
  rw [hL] at hmain
  exact hmain


/-! ### Lemma 4.5(i) on the circle: closed forms `T_j = N_j/(256 K^{k_j} 𝒬²)` and the certificate -/

/-- `K(τ) = 7τ² - 4`. -/
private noncomputable def Kt (t : ℝ) : ℝ := 7 * t ^ 2 - 4

private noncomputable def n2_0 (t : ℝ) : ℝ :=
  (-1024 : ℝ) + (2560 : ℝ) * t ^ 2 + (-2112 : ℝ) * t ^ 4 + (2368 : ℝ) * t ^ 6 + (-1792 : ℝ) * t ^ 8

private noncomputable def n2_1 (t : ℝ) : ℝ :=
  (1024 : ℝ) * t + (2816 : ℝ) * t ^ 3 + (-14592 : ℝ) * t ^ 5 + (9728 : ℝ) * t ^ 7 + (1024 : ℝ) * t ^ 9

private noncomputable def n2_2 (t : ℝ) : ℝ :=
  (1536 : ℝ) + (-9600 : ℝ) * t ^ 2 + (12672 : ℝ) * t ^ 4 + (7680 : ℝ) * t ^ 6 + (-12288 : ℝ) * t ^ 8

private noncomputable def n2_3 (t : ℝ) : ℝ :=
  (-1280 : ℝ) * t + (8960 : ℝ) * t ^ 3 + (-16896 : ℝ) * t ^ 5 + (5120 : ℝ) * t ^ 7 + (4096 : ℝ) * t ^ 9

private noncomputable def n2_4 (t : ℝ) : ℝ :=
  (-64 : ℝ) + (832 : ℝ) * t ^ 2 + (-3840 : ℝ) * t ^ 4 + (7168 : ℝ) * t ^ 6 + (-4096 : ℝ) * t ^ 8

/-- The numerator `N_2(τ, c)` of `T_2`. -/
private noncomputable def Nc2 (t : ℝ) (c : ℂ) : ℂ :=
  (n2_0 t : ℂ) + (n2_1 t : ℂ) * c + (n2_2 t : ℂ) * c ^ 2 + (n2_3 t : ℂ) * c ^ 3 + (n2_4 t : ℂ) * c ^ 4

private noncomputable def NR2 (t x : ℝ) : ℝ :=
  n2_0 t * (1) + n2_1 t * (x) + n2_2 t * (2*x^2 - 1) + n2_3 t * (4*x^3 - 3*x) + n2_4 t * (8*x^4 - 8*x^2 + 1)

private noncomputable def NI2 (t x : ℝ) : ℝ :=
  n2_1 t * (1) + n2_2 t * (2*x) + n2_3 t * (4*x^2 - 1) + n2_4 t * (8*x^3 - 4*x)

private noncomputable def n3_0 (t : ℝ) : ℝ :=
  (49152 : ℝ) * t ^ 3 + (-264192 : ℝ) * t ^ 5 + (565248 : ℝ) * t ^ 7 + (-653952 : ℝ) * t ^ 9 + (454272 : ℝ) * t ^ 11 + (-150528 : ℝ) * t ^ 13

private noncomputable def n3_1 (t : ℝ) : ℝ :=
  (24576 : ℝ) + (-231424 : ℝ) * t ^ 2 + (832000 : ℝ) * t ^ 4 + (-1601408 : ℝ) * t ^ 6 + (1947264 : ℝ) * t ^ 8 + (-1428736 : ℝ) * t ^ 10 + (343040 : ℝ) * t ^ 12 + (114688 : ℝ) * t ^ 14

private noncomputable def n3_2 (t : ℝ) : ℝ :=
  (-12288 : ℝ) * t + (98304 : ℝ) * t ^ 3 + (-277248 : ℝ) * t ^ 5 + (506496 : ℝ) * t ^ 7 + (-1069440 : ℝ) * t ^ 9 + (1528320 : ℝ) * t ^ 11 + (-774144 : ℝ) * t ^ 13

private noncomputable def n3_3 (t : ℝ) : ℝ :=
  (-3072 : ℝ) + (32256 : ℝ) * t ^ 2 + (-92352 : ℝ) * t ^ 4 + (-73536 : ℝ) * t ^ 6 + (711168 : ℝ) * t ^ 8 + (-918528 : ℝ) * t ^ 10 + (147456 : ℝ) * t ^ 12 + (196608 : ℝ) * t ^ 14

private noncomputable def n3_4 (t : ℝ) : ℝ :=
  (3072 : ℝ) * t + (-36608 : ℝ) * t ^ 3 + (148864 : ℝ) * t ^ 5 + (-204416 : ℝ) * t ^ 7 + (-80896 : ℝ) * t ^ 9 + (333824 : ℝ) * t ^ 11 + (-163840 : ℝ) * t ^ 13

private noncomputable def n3_5 (t : ℝ) : ℝ :=
  (-1536 : ℝ) * t ^ 2 + (19200 : ℝ) * t ^ 4 + (-82176 : ℝ) * t ^ 6 + (125952 : ℝ) * t ^ 8 + (-12288 : ℝ) * t ^ 10 + (-49152 : ℝ) * t ^ 12

private noncomputable def n3_6 (t : ℝ) : ℝ :=
  (1152 : ℝ) * t ^ 3 + (-14976 : ℝ) * t ^ 5 + (69120 : ℝ) * t ^ 7 + (-129024 : ℝ) * t ^ 9 + (73728 : ℝ) * t ^ 11

private noncomputable def n3_7 (t : ℝ) : ℝ :=
  (64 : ℝ) + (-1088 : ℝ) * t ^ 2 + (7168 : ℝ) * t ^ 4 + (-22528 : ℝ) * t ^ 6 + (32768 : ℝ) * t ^ 8 + (-16384 : ℝ) * t ^ 10

/-- The numerator `N_3(τ, c)` of `T_3`. -/
private noncomputable def Nc3 (t : ℝ) (c : ℂ) : ℂ :=
  (n3_0 t : ℂ) + (n3_1 t : ℂ) * c + (n3_2 t : ℂ) * c ^ 2 + (n3_3 t : ℂ) * c ^ 3 + (n3_4 t : ℂ) * c ^ 4 + (n3_5 t : ℂ) * c ^ 5 + (n3_6 t : ℂ) * c ^ 6 + (n3_7 t : ℂ) * c ^ 7

private noncomputable def NR3 (t x : ℝ) : ℝ :=
  n3_0 t * (1) + n3_1 t * (x) + n3_2 t * (2*x^2 - 1) + n3_3 t * (4*x^3 - 3*x) + n3_4 t * (8*x^4 - 8*x^2 + 1) + n3_5 t * (16*x^5 - 20*x^3 + 5*x) + n3_6 t * (32*x^6 - 48*x^4 + 18*x^2 - 1) + n3_7 t * (64*x^7 - 112*x^5 + 56*x^3 - 7*x)

private noncomputable def NI3 (t x : ℝ) : ℝ :=
  n3_1 t * (1) + n3_2 t * (2*x) + n3_3 t * (4*x^2 - 1) + n3_4 t * (8*x^3 - 4*x) + n3_5 t * (16*x^4 - 12*x^2 + 1) + n3_6 t * (32*x^5 - 32*x^3 + 6*x) + n3_7 t * (64*x^6 - 80*x^4 + 24*x^2 - 1)

private noncomputable def n4_0 (t : ℝ) : ℝ :=
  (-32768 : ℝ) + (344064 : ℝ) * t ^ 2 + (-1556480 : ℝ) * t ^ 4 + (4424704 : ℝ) * t ^ 6 + (-8938368 : ℝ) * t ^ 8 + (12549760 : ℝ) * t ^ 10 + (-11485952 : ℝ) * t ^ 12 + (6300672 : ℝ) * t ^ 14 + (-1605632 : ℝ) * t ^ 16

private noncomputable def n4_1 (t : ℝ) : ℝ :=
  (-24576 : ℝ) * t + (559104 : ℝ) * t ^ 3 + (-4056576 : ℝ) * t ^ 5 + (13609344 : ℝ) * t ^ 7 + (-24346560 : ℝ) * t ^ 9 + (24257856 : ℝ) * t ^ 11 + (-12136704 : ℝ) * t ^ 13 + (761856 : ℝ) * t ^ 15 + (1376256 : ℝ) * t ^ 17

private noncomputable def n4_2 (t : ℝ) : ℝ :=
  (36864 : ℝ) + (-476160 : ℝ) * t ^ 2 + (2277120 : ℝ) * t ^ 4 + (-4646592 : ℝ) * t ^ 6 + (1806528 : ℝ) * t ^ 8 + (9594624 : ℝ) * t ^ 10 + (-20524032 : ℝ) * t ^ 12 + (18812928 : ℝ) * t ^ 14 + (-6881280 : ℝ) * t ^ 16

private noncomputable def n4_3 (t : ℝ) : ℝ :=
  (-24576 : ℝ) * t + (359424 : ℝ) * t ^ 3 + (-2139136 : ℝ) * t ^ 5 + (6864576 : ℝ) * t ^ 7 + (-13415616 : ℝ) * t ^ 9 + (16509440 : ℝ) * t ^ 11 + (-10939392 : ℝ) * t ^ 13 + (1474560 : ℝ) * t ^ 15 + (1310720 : ℝ) * t ^ 17

private noncomputable def n4_4 (t : ℝ) : ℝ :=
  (15360 : ℝ) * t ^ 4 + (-195840 : ℝ) * t ^ 6 + (859392 : ℝ) * t ^ 8 + (-1330176 : ℝ) * t ^ 10 + (-184320 : ℝ) * t ^ 12 + (1622016 : ℝ) * t ^ 14 + (-786432 : ℝ) * t ^ 16

private noncomputable def n4_5 (t : ℝ) : ℝ :=
  (1536 : ℝ) * t + (-29568 : ℝ) * t ^ 3 + (218304 : ℝ) * t ^ 5 + (-777792 : ℝ) * t ^ 7 + (1413888 : ℝ) * t ^ 9 + (-1502208 : ℝ) * t ^ 11 + (1462272 : ℝ) * t ^ 13 + (-786432 : ℝ) * t ^ 15

private noncomputable def n4_6 (t : ℝ) : ℝ :=
  (-768 : ℝ) + (13376 : ℝ) * t ^ 2 + (-94272 : ℝ) * t ^ 4 + (354048 : ℝ) * t ^ 6 + (-821248 : ℝ) * t ^ 8 + (1351680 : ℝ) * t ^ 10 + (-1523712 : ℝ) * t ^ 12 + (720896 : ℝ) * t ^ 14

private noncomputable def n4_7 (t : ℝ) : ℝ :=
  (576 : ℝ) * t ^ 3 + (-9792 : ℝ) * t ^ 5 + (64512 : ℝ) * t ^ 7 + (-202752 : ℝ) * t ^ 9 + (294912 : ℝ) * t ^ 11 + (-147456 : ℝ) * t ^ 13

/-- The numerator `N_4(τ, c)` of `T_4`. -/
private noncomputable def Nc4 (t : ℝ) (c : ℂ) : ℂ :=
  (n4_0 t : ℂ) + (n4_1 t : ℂ) * c + (n4_2 t : ℂ) * c ^ 2 + (n4_3 t : ℂ) * c ^ 3 + (n4_4 t : ℂ) * c ^ 4 + (n4_5 t : ℂ) * c ^ 5 + (n4_6 t : ℂ) * c ^ 6 + (n4_7 t : ℂ) * c ^ 7

private noncomputable def NR4 (t x : ℝ) : ℝ :=
  n4_0 t * (1) + n4_1 t * (x) + n4_2 t * (2*x^2 - 1) + n4_3 t * (4*x^3 - 3*x) + n4_4 t * (8*x^4 - 8*x^2 + 1) + n4_5 t * (16*x^5 - 20*x^3 + 5*x) + n4_6 t * (32*x^6 - 48*x^4 + 18*x^2 - 1) + n4_7 t * (64*x^7 - 112*x^5 + 56*x^3 - 7*x)

private noncomputable def NI4 (t x : ℝ) : ℝ :=
  n4_1 t * (1) + n4_2 t * (2*x) + n4_3 t * (4*x^2 - 1) + n4_4 t * (8*x^3 - 4*x) + n4_5 t * (16*x^4 - 12*x^2 + 1) + n4_6 t * (32*x^5 - 32*x^3 + 6*x) + n4_7 t * (64*x^6 - 80*x^4 + 24*x^2 - 1)

private noncomputable def n5_0 (t : ℝ) : ℝ :=
  (98304 : ℝ) * t + (-1753088 : ℝ) * t ^ 3 + (12488704 : ℝ) * t ^ 5 + (-48398336 : ℝ) * t ^ 7 + (118009216 : ℝ) * t ^ 9 + (-194842688 : ℝ) * t ^ 11 + (221377984 : ℝ) * t ^ 13 + (-167076608 : ℝ) * t ^ 15 + (76152832 : ℝ) * t ^ 17 + (-16056320 : ℝ) * t ^ 19

private noncomputable def n5_1 (t : ℝ) : ℝ :=
  (-147456 : ℝ) + (2260992 : ℝ) * t ^ 2 + (-14989312 : ℝ) * t ^ 4 + (58760192 : ℝ) * t ^ 6 + (-155642944 : ℝ) * t ^ 8 + (287306048 : ℝ) * t ^ 10 + (-353092864 : ℝ) * t ^ 12 + (259656704 : ℝ) * t ^ 14 + (-83980288 : ℝ) * t ^ 16 + (-14811136 : ℝ) * t ^ 18 + (14680064 : ℝ) * t ^ 20

private noncomputable def n5_2 (t : ℝ) : ℝ :=
  (233472 : ℝ) * t ^ 3 + (-2761728 : ℝ) * t ^ 5 + (10313472 : ℝ) * t ^ 7 + (-2500800 : ℝ) * t ^ 9 + (-80356416 : ℝ) * t ^ 11 + (234481152 : ℝ) * t ^ 13 + (-309617664 : ℝ) * t ^ 15 + (210763776 : ℝ) * t ^ 17 + (-60555264 : ℝ) * t ^ 19

private noncomputable def n5_3 (t : ℝ) : ℝ :=
  (16384 : ℝ) + (-217088 : ℝ) * t ^ 2 + (642048 : ℝ) * t ^ 4 + (4143360 : ℝ) * t ^ 6 + (-37653504 : ℝ) * t ^ 8 + (126180096 : ℝ) * t ^ 10 + (-227791872 : ℝ) * t ^ 12 + (234934272 : ℝ) * t ^ 14 + (-125681664 : ℝ) * t ^ 16 + (17039360 : ℝ) * t ^ 18 + (8388608 : ℝ) * t ^ 20

private noncomputable def n5_4 (t : ℝ) : ℝ :=
  (-22528 : ℝ) * t + (423936 : ℝ) * t ^ 3 + (-3298176 : ℝ) * t ^ 5 + (13829952 : ℝ) * t ^ 7 + (-34511040 : ℝ) * t ^ 9 + (53860608 : ℝ) * t ^ 11 + (-52036608 : ℝ) * t ^ 13 + (25030656 : ℝ) * t ^ 15 + (-1179648 : ℝ) * t ^ 17 + (-2097152 : ℝ) * t ^ 19

private noncomputable def n5_5 (t : ℝ) : ℝ :=
  (3072 : ℝ) + (-56832 : ℝ) * t ^ 2 + (460992 : ℝ) * t ^ 4 + (-2291136 : ℝ) * t ^ 6 + (8193792 : ℝ) * t ^ 8 + (-21571584 : ℝ) * t ^ 10 + (38313984 : ℝ) * t ^ 12 + (-42123264 : ℝ) * t ^ 14 + (28508160 : ℝ) * t ^ 16 + (-9437184 : ℝ) * t ^ 18

private noncomputable def n5_6 (t : ℝ) : ℝ :=
  (2048 : ℝ) * t + (-54016 : ℝ) * t ^ 3 + (580544 : ℝ) * t ^ 5 + (-3318976 : ℝ) * t ^ 7 + (11033600 : ℝ) * t ^ 9 + (-22054912 : ℝ) * t ^ 11 + (26968064 : ℝ) * t ^ 13 + (-19972096 : ℝ) * t ^ 15 + (6815744 : ℝ) * t ^ 17

private noncomputable def n5_7 (t : ℝ) : ℝ :=
  (-512 : ℝ) + (11392 : ℝ) * t ^ 2 + (-106880 : ℝ) * t ^ 4 + (551680 : ℝ) * t ^ 6 + (-1725440 : ℝ) * t ^ 8 + (3432448 : ℝ) * t ^ 10 + (-4456448 : ℝ) * t ^ 12 + (3604480 : ℝ) * t ^ 14 + (-1310720 : ℝ) * t ^ 16

/-- The numerator `N_5(τ, c)` of `T_5`. -/
private noncomputable def Nc5 (t : ℝ) (c : ℂ) : ℂ :=
  (n5_0 t : ℂ) + (n5_1 t : ℂ) * c + (n5_2 t : ℂ) * c ^ 2 + (n5_3 t : ℂ) * c ^ 3 + (n5_4 t : ℂ) * c ^ 4 + (n5_5 t : ℂ) * c ^ 5 + (n5_6 t : ℂ) * c ^ 6 + (n5_7 t : ℂ) * c ^ 7

private noncomputable def NR5 (t x : ℝ) : ℝ :=
  n5_0 t * (1) + n5_1 t * (x) + n5_2 t * (2*x^2 - 1) + n5_3 t * (4*x^3 - 3*x) + n5_4 t * (8*x^4 - 8*x^2 + 1) + n5_5 t * (16*x^5 - 20*x^3 + 5*x) + n5_6 t * (32*x^6 - 48*x^4 + 18*x^2 - 1) + n5_7 t * (64*x^7 - 112*x^5 + 56*x^3 - 7*x)

private noncomputable def NI5 (t x : ℝ) : ℝ :=
  n5_1 t * (1) + n5_2 t * (2*x) + n5_3 t * (4*x^2 - 1) + n5_4 t * (8*x^3 - 4*x) + n5_5 t * (16*x^4 - 12*x^2 + 1) + n5_6 t * (32*x^5 - 32*x^3 + 6*x) + n5_7 t * (64*x^6 - 80*x^4 + 24*x^2 - 1)

private noncomputable def R0 (b : ℝ) : ℝ :=
  (6210828009194846877 / 549755813888 : ℝ) + b * ((5853211211230020981 / 21474836480 : ℝ) + b * ((2001929987258819111480693131545790591041256848772565960273 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((12447338993448891507711 / 34359738368000 : ℝ) + b * ((109062620341164585049689 / 687194767360000 : ℝ) + b * ((136858165512091483162347 / 3435973836800000 : ℝ) + b * ((18853207941115858438809 / 4294967296000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((17671735901810851196139 / 6871947673600000000 : ℝ) + b * ((1302277409042976634996683 / 3435973836800000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((133197246600200019941931 / 858993459200000000000000 : ℝ) + b * ((2116945681580776165312203 / 34359738368000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((427946366101828480074977 / 17179869184000000000000000000 : ℝ) + b * ((901029736437641468513389 / 343597383680000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((223174389621921934979 / 171798691840000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((15129731761108499713341 / 68719476736000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((932096390874893604901 / 6871947673600000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((1168123930084035765213 / 3435973836800000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((708289978620321070169 / 343597383680000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((70016287021434111309 / 34359738368000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((142077657153131133 / 214748364800000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((468890219 / 6553600000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((363517 / 204800000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H0 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((2590948111799622279306868454209408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2590948111799622279306868454209408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2590948111799622279306868454209408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2590948111799622279306868454209408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2590948111799622279306868454209408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((839560734742541501620055954209408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((52283108290434777488583141709408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((116029022843584534242516709408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((116029022843584534242516709408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((116029022843584534242516709408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((24647079045209518388964896908958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((9792114395404456258384408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((9792114395404456258384408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((9792114395404456258384408958743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2137256150190487170645382396243151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((1084895716765045828931146243151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((1084895716765045828931146243151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((1084895716765045828931146243151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((13180658225543181532540618151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((245994976051678144756743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((245994976051678144756743151227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((5437187171015814764819401227434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((39330326743110475100869977434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((39330326743110475100869977434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((1574340550595244402477434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((1574340550595244402477434039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((161290148417108712858684039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((161290148417108712858684039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((325063706425340742184039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((325063706425340742184039727 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((22467935975457752819419 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((22467935975457752819419 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((2143782468789720647 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((2143782468789720647 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((460685113 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((460685113 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((847 / 256000000000000000000000000000000000000000 : ℝ) + b * ((847 / 256000000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def R1 (b : ℝ) : ℝ :=
  (49981437297925857423 / 549755813888 : ℝ) + b * ((30799829759004355707 / 17179869184 : ℝ) + b * ((1759586256872387618453793776455998673656871627340498898451 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((99320672368980910426491 / 34359738368000 : ℝ) + b * ((1055826368265510698412159 / 687194767360000 : ℝ) + b * ((1779355318273132709069847 / 3435973836800000 : ℝ) + b * ((1741710185073415720661247 / 17179869184000000 : ℝ) + b * ((1871026261022451298699611 / 343597383680000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1361814274932476109921 / 1342177280000000000 : ℝ) + b * ((39346074897835854763033911 / 3435973836800000000000 : ℝ) + b * ((43401463697598084225833949 / 68719476736000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((71040432375652667029054839 / 34359738368000000000000000 : ℝ) + b * ((337809477085608813363442917 / 2748779069440000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((66777723894149861899675361 / 343597383680000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((519672797238403225826761 / 6871947673600000000000000000000 : ℝ) + b * ((1483714824511273512124977 / 3435973836800000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((6655476884575485222373413 / 343597383680000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((421378643112600681746263 / 137438953472000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((11533069452663238240531 / 3435973836800000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((35712214202581832786463 / 54975581388800000000000000000000000000000000 : ℝ) + b * ((10605810749077909101 / 34359738368000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((148542485658669417 / 42949672960000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((13045194113 / 32768000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((1948331 / 204800000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H1 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((1563816228140439044643723544001326343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1563816228140439044643723544001326343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1563816228140439044643723544001326343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1563816228140439044643723544001326343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1563816228140439044643723544001326343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1563816228140439044643723544001326343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((280671684379667665988004989313826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((95830165613105808489848688826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((95830165613105808489848688826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((95830165613105808489848688826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((95830165613105808489848688826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((6635169968434876684577618513843128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((12489468805556190138228826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((12489468805556190138228826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((12489468805556190138228826343128372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((257839704918825823652900561878372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((3020305619967067274144686878372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((3020305619967067274144686878372659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((524611893765792137171479456497659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((182541033093181270690534622659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((182541033093181270690534622659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((182541033093181270690534622659501101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((113187052211296789942235940751101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((113187052211296789942235940751101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((21978756251638632436104690751101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((66807830112725086590143876101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((66807830112725086590143876101549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((32840508312214931886532351549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((32840508312214931886532351549 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((86185419390809427664049 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((86185419390809427664049 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((86185419390809427664049 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((11989869369845539837 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((11989869369845539837 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((2509873373 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((2509873373 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((4487 / 256000000000000000000000000000000000000000 : ℝ) + b * ((4487 / 256000000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def R2 (b : ℝ) : ℝ :=
  (44065422513098092953 / 137438953472 : ℝ) + b * ((219090340633481487639 / 42949672960 : ℝ) + b * ((124170549800832574928519551780821389850873197189802467123 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((6950410502154941748069 / 858993459200 : ℝ) + b * ((741256403270126707996227 / 171798691840000 : ℝ) + b * ((655149331371804158877273 / 429496729600000 : ℝ) + b * ((3033176632953298176463371 / 8589934592000000 : ℝ) + b * ((1794490422594147081441297 / 42949672960000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((12928134748352704761877101 / 429496729600000000000 : ℝ) + b * ((26062493408843370575528313 / 3435973836800000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1261274042824736074703793 / 858993459200000000000000 : ℝ) + b * ((1390421474475501896891788251 / 687194767360000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((54333448316881921899226987 / 42949672960000000000000000000 : ℝ) + b * ((43637214629052853245600001 / 343597383680000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((8339811209766376555917689 / 85899345920000000000000000000000 : ℝ) + b * ((40920844326989086549163379 / 429496729600000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((3402400360916109045091359 / 42949672960000000000000000000000000 : ℝ) + b * ((20915237096641089082426343 / 858993459200000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((831660682069961483635811 / 6871947673600000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((1000139344962216808333857 / 8589934592000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((466653107995216050455097 / 13743895347200000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((98818786065155026473 / 42949672960000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((6963550979 / 8192000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((39081 / 2048000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H2 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((73033354380876717714823219178610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((73033354380876717714823219178610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((73033354380876717714823219178610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((73033354380876717714823219178610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((73033354380876717714823219178610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((73033354380876717714823219178610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((30568854535533485536281246522360149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((2942777686903736040394287147360149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((4740257627259125505821678610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((4740257627259125505821678610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((4740257627259125505821678610149126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((1933415001300040881900577672649126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((955583825450977428641094524126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((955583825450977428641094524126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((955583825450977428641094524126802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((282607559449577403985129242876802810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((221851495745727082437385064302810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((221851495745727082437385064302810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((221851495745727082437385064302810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((96732053720343419740298677810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((96732053720343419740298677810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((96732053720343419740298677810197532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((31109688102515856613099294572532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((31109688102515856613099294572532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((31109688102515856613099294572532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((58784127698800539135741447532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((58784127698800539135741447532877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((31050967958094239470416282877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((31050967958094239470416282877 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((4736796375519073918470377 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((4736796375519073918470377 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((64758375094371589127 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((64758375094371589127 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((941167926968900127 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((261374883 / 51200000000000000000000000000000000000000 : ℝ) + b * ((261374883 / 51200000000000000000000000000000000000000 : ℝ) + b * ((427 / 12800000000000000000000000000000000000000 : ℝ) + b * ((427 / 12800000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def R3 (b : ℝ) : ℝ :=
  (89015284699297433127 / 137438953472 : ℝ) + b * ((353209877907525136071 / 42949672960 : ℝ) + b * ((935499099376392793462027162842297510012664993624015548177 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((24483083397083174873907 / 2147483648000 : ℝ) + b * ((882178010655137429934393 / 171798691840000 : ℝ) + b * ((244131922559151271156077 / 214748364800000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1091135188787446173547359 / 2147483648000000000 : ℝ) + b * ((55608436187436202100132193 / 85899345920000000000 : ℝ) + b * ((9554234933118994798569759 / 214748364800000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((30027989825936265831657831 / 171798691840000000000000 : ℝ) + b * ((48917084109118436168242227 / 2147483648000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((49425375136955151001775387 / 1717986918400000000000000000 : ℝ) + b * ((5317216494539281777246861 / 4294967296000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((5824933496724684321384967 / 2147483648000000000000000000000 : ℝ) + b * ((132320323375436245504062713 / 85899345920000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((11052488640436787407147369 / 21474836480000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((12585367331192153630995449 / 171798691840000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((286795253762921489075541 / 1717986918400000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((1039486466647767118185639 / 13743895347200000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((339027166313405610467 / 42949672960000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((1327028532726603 / 107374182400000000000000000000000000000000000 : ℝ) + b * ((6528908113 / 8192000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((767291 / 51200000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H3 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((9355590932307487224144712157702489987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((9355590932307487224144712157702489987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((9355590932307487224144712157702489987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((9355590932307487224144712157702489987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((7069451863142678441033423095202489987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1202184826866243520388919970202489987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((911190962137718853410927233739987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((911190962137718853410927233739987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((911190962137718853410927233739987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((911190962137718853410927233739987335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((94188428731491533652482292333737335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((172783353589515094891045458737335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((172783353589515094891045458737335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((172783353589515094891045458737335006375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((15638133882074471462684810788116256375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((18229542194924042913820163116256375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((18229542194924042913820163116256375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((18229542194924042913820163116256375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((6409630291182680641027452193875984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((6409630291182680641027452193875984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((6409630291182680641027452193875984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((149225423514592511094446256375984451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1569274272668589178412727079109451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1569274272668589178412727079109451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((10802386952704050891047313484451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((304936883111514404655469734451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((304936883111514404655469734451823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((283059150383969999838171951823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((283059150383969999838171951823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((63820696657928520375076823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((63820696657928520375076823 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((604935072142322194987 / 16777216000000000000000000000000000000000000000 : ℝ) + b * ((604935072142322194987 / 16777216000000000000000000000000000000000000000 : ℝ) + b * ((1156100267 / 256000000000000000000000000000000000000000 : ℝ) + b * ((1156100267 / 256000000000000000000000000000000000000000 : ℝ) + b * ((1156100267 / 256000000000000000000000000000000000000000 : ℝ) + b * ((1323 / 64000000000000000000000000000000000000000 : ℝ) + b * ((1323 / 64000000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def R4 (b : ℝ) : ℝ :=
  (225633750604097948091 / 274877906944 : ℝ) + b * ((71065811034536817555 / 8589934592 : ℝ) + b * ((705016005308044741349310110070828495355686374894666433717 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((166601520652915467341199 / 17179869184000 : ℝ) + b * ((1430200647293857724906667 / 343597383680000 : ℝ) + b * ((2042377283455979616200043 / 1717986918400000 : ℝ) + b * ((2338356436629119721104643 / 8589934592000000 : ℝ) + b * ((9761982143714341273593423 / 171798691840000000 : ℝ) + b * ((52990332932803973486584329 / 6871947673600000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((192503130529590461524751073 / 34359738368000000000000 : ℝ) + b * ((306855353732234812896807 / 274877906944000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((499618039858206197519869129 / 1374389534720000000000000000 : ℝ) + b * ((335008835426254709598955103 / 1717986918400000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((240052982308020080373020149 / 3435973836800000000000000000000 : ℝ) + b * ((143375392197944560275497281 / 17179869184000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((252420460436064498851128033 / 68719476736000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((11478991906420429190814889 / 17179869184000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((572955773138312011737939 / 8589934592000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((1616275401138905073359499 / 27487790694400000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((803291989338287496957 / 85899345920000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((147136485754614699 / 1073741824000000000000000000000000000000000000 : ℝ) + b * ((2502273473 / 16384000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1519 / 128000000000000000000000000000000000000000 : ℝ)))))))))))))))))))))))))))))))))))))))))

private noncomputable def H4 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((46524784222415931877389929171504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((46524784222415931877389929171504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((46524784222415931877389929171504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((46524784222415931877389929171504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((46524784222415931877389929171504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((46524784222415931877389929171504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((46524784222415931877389929171504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((22116313117628673588170063546504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((1991851068793076130467798546504644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3476094772568411016783390254644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3476094772568411016783390254644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3476094772568411016783390254644313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((947209964172688574754063067144313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((346566181824284890288051519313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((346566181824284890288051519313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((346566181824284890288051519313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((84398778139383560701126344313625105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((36791735215848026350253376125105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((36791735215848026350253376125105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((36791735215848026350253376125105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((969509991003679005286614250105333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((5206430464592939076958656355333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((5206430464592939076958656355333566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((451276481220389205157616667833566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((714241819177046850819917833566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((714241819177046850819917833566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((43090040460147747668115177316283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((134165785288230015554083566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((134165785288230015554083566283 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((49391186602454071096378783 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((49391186602454071096378783 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((747736563764608939227 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((747736563764608939227 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((5111827 / 12800000000000000000000000000000000000000 : ℝ) + b * ((5111827 / 12800000000000000000000000000000000000000 : ℝ) + b * ((5111827 / 12800000000000000000000000000000000000000 : ℝ) + b * ((175861 / 102400000000000000000000000000000000000000 : ℝ)))))))))))))))))))))))))))))))))))))))

private noncomputable def R5 (b : ℝ) : ℝ :=
  (184221647110303596801 / 274877906944 : ℝ) + b * ((115849023413299251831 / 21474836480 : ℝ) + b * ((436823229228201873152223404395398125746069982761390261713 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((102021831606167006454783 / 17179869184000 : ℝ) + b * ((816517014687411522173829 / 343597383680000 : ℝ) + b * ((792400756433641439061339 / 1717986918400000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((15291351756267966799058061 / 85899345920000000000 : ℝ) + b * ((8446349014595118849994191 / 343597383680000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((21958745477255052995883567 / 3435973836800000000000000 : ℝ) + b * ((301797207391209962953991003 / 1374389534720000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((15920464382394582102252361 / 34359738368000000000000000000 : ℝ) + b * ((41812348929808233402361899 / 3435973836800000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((24307376019426365587128413 / 1717986918400000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((2057350764070878813353939 / 858993459200000000000000000000000000 : ℝ) + b * ((24662045652920971586529 / 687194767360000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((371469317756199528445997 / 1717986918400000000000000000000000000000 : ℝ) + b * ((2004613679139851405601 / 536870912000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((495962977245870719630801 / 27487790694400000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((415528940222806208407 / 85899345920000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((147654053735783889 / 1073741824000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((40250413 / 20480000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((1519 / 128000000000000000000000000000000000000000 : ℝ)))))))))))))))))))))))))))))))))))))))))

private noncomputable def H5 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((3382489596622773075401595604601874253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3382489596622773075401595604601874253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3382489596622773075401595604601874253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3382489596622773075401595604601874253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((2257989339013193291633558104601874253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((407160769111211877013377792101874253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((10482442540740314208974690539374253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((101855165340704835474524914374253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((101855165340704835474524914374253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((101855165340704835474524914374253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((27793782017907169203703550311753930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((297137795259209352429122499253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3342185433432399020757249253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3342185433432399020757249253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((3342185433432399020757249253930017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((123044913837223121899757972680017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((158721353743661616696666430017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((158721353743661616696666430017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((158721353743661616696666430017238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((707620141761563411818883142238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((19041707719345774628469392238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((19041707719345774628469392238609738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((2297680665596760522460050832359738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((387832543073209489151144859738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((387832543073209489151144859738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((387832543073209489151144859738287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((26348348098170332386265988287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((26348348098170332386265988287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((26348348098170332386265988287 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((20259995776034578283800787 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((20259995776034578283800787 / 53687091200000000000000000000000000000000000000 : ℝ) + b * ((487319798386008229103 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((487319798386008229103 / 13421772800000000000000000000000000000000000000 : ℝ) + b * ((114471837221 / 409600000000000000000000000000000000000000 : ℝ) + b * ((114471837221 / 409600000000000000000000000000000000000000 : ℝ) + b * ((796299 / 102400000000000000000000000000000000000000 : ℝ) + b * ((796299 / 102400000000000000000000000000000000000000 : ℝ)))))))))))))))))))))))))))))))))))))))

private noncomputable def R6 (b : ℝ) : ℝ :=
  (47603181205503081837 / 137438953472 : ℝ) + b * ((19634790866434013025 / 8589934592 : ℝ) + b * ((239316230058288068641038496493187526306354030248853340827 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((6077754098586484646967 / 2147483648000 : ℝ) + b * ((237285256705210020621987 / 171798691840000 : ℝ) + b * ((95615084815539170107221 / 214748364800000 : ℝ) + b * ((820535396432798724581601 / 8589934592000000 : ℝ) + b * ((267330672137767927617387 / 21474836480000000 : ℝ) + b * ((1578798411229027989651771 / 3435973836800000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((4999046977829069405590293 / 17179869184000000000000 : ℝ) + b * ((1429384020697435867562169 / 21474836480000000000000 : ℝ) + b * ((1681326045956707882581753 / 858993459200000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((5439830592661502949081 / 1342177280000000000000000 : ℝ) + b * ((42923982484523195203737 / 68719476736000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((207726284535313733504127 / 2147483648000000000000000000000 : ℝ) + b * ((408736795554835330684703 / 17179869184000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((86949930034047739931701 / 21474836480000000000000000000000000 : ℝ) + b * ((1416403304381464950173 / 6871947673600000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((7698339124275063662579 / 214748364800000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((25950975983148626525549 / 13743895347200000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((43858082818693491537 / 42949672960000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((5498534604631033 / 107374182400000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((7409437 / 10240000000000000000000000000000000000000 : ℝ) + b * ((79429 / 51200000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H6 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((14275953906586543727128506812473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((14275953906586543727128506812473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((14275953906586543727128506812473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((14275953906586543727128506812473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((14275953906586543727128506812473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((14275953906586543727128506812473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((14275953906586543727128506812473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((2666510394738794897807350562473693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((162700362553791794179902906223693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((48683946614276023498843723693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((48683946614276023498843723693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((48683946614276023498843723693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((48683946614276023498843723693645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((3903563991199878167502692443645969751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1557390478060040356515002239719751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1557390478060040356515002239719751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1557390478060040356515002239719751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((300626173260104358557192864719751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((50402426398972166006185032251146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((50402426398972166006185032251146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((50402426398972166006185032251146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((6100585711148162903280344751146659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1113982290108393944959985521659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1113982290108393944959985521659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((1113982290108393944959985521659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((2625784254105910486016771659173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((76193093265056617867943534173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((76193093265056617867943534173 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((929493433679434155029471673 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((4042913070736621645096673 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((4042913070736621645096673 / 67108864000000000000000000000000000000000000000 : ℝ) + b * ((164594732976272004637 / 16777216000000000000000000000000000000000000000 : ℝ) + b * ((164594732976272004637 / 16777216000000000000000000000000000000000000000 : ℝ) + b * ((176967139293 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((176967139293 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((1323 / 64000000000000000000000000000000000000000 : ℝ) + b * ((1323 / 64000000000000000000000000000000000000000 : ℝ) + b * ((1323 / 64000000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def R7 (b : ℝ) : ℝ :=
  (14485348588959270603 / 137438953472 : ℝ) + b * ((25816242532250861649 / 42949672960 : ℝ) + b * ((3299767930919046089503797318128839812558180825496527087 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((3628851807417529174641 / 4294967296000 : ℝ) + b * ((77123292093058755358593 / 171798691840000 : ℝ) + b * ((66853895806570217108697 / 429496729600000 : ℝ) + b * ((297135677047615218824589 / 8589934592000000 : ℝ) + b * ((179238247772380476391449 / 42949672960000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((43037381950197749796357 / 429496729600000000000 : ℝ) + b * ((3113478604629213834154671 / 17179869184000000000000 : ℝ) + b * ((539140542394984581736701 / 42949672960000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1787590998238051828540401 / 687194767360000000000000000 : ℝ) + b * ((619091332319982882099219 / 429496729600000000000000000 : ℝ) + b * ((150869322166351825709781 / 8589934592000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((174941764186938975010443 / 4294967296000000000000000000000 : ℝ) + b * ((75700230798781383551791 / 85899345920000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((4605185594827607398027 / 8589934592000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1214998950579443848373 / 34359738368000000000000000000000000000 : ℝ) + b * ((578125408525841793887 / 429496729600000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((8165100183438718611 / 8589934592000000000000000000000000000000 : ℝ) + b * ((939132207772520727787 / 13743895347200000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((2665093360117528523 / 42949672960000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((2199840024070171 / 536870912000000000000000000000000000000000000 : ℝ) + b * ((85044701 / 8192000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((623 / 81920000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H7 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((427067319535606468858931871160187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((427067319535606468858931871160187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((427067319535606468858931871160187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((427067319535606468858931871160187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((427067319535606468858931871160187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((427067319535606468858931871160187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((355691584247385526465061753972687441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((41600502763618157173790660222687441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((4509136284577706655152410187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((4509136284577706655152410187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((4509136284577706655152410187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((4509136284577706655152410187441819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((600022517168054639755835968691819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((29156960779051792233624941819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((29156960779051792233624941819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((29156960779051792233624941819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((29156960779051792233624941819174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((649939685463393159463926194174503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((557997380291930722533616049503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((557997380291930722533616049503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((557997380291930722533616049503472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((5784074218268126543201987003472913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((16983321118131423950912784722913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((16983321118131423950912784722913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((4111079956861016548572940972913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((307317938777117640909722913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((307317938777117640909722913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((307317938777117640909722913 / 3355443200000000000000000000000000000000000000 : ℝ) + b * ((1297922584774980463411 / 419430400000000000000000000000000000000000000 : ℝ) + b * ((1297922584774980463411 / 419430400000000000000000000000000000000000000 : ℝ) + b * ((1297922584774980463411 / 419430400000000000000000000000000000000000000 : ℝ) + b * ((294095322425850911 / 419430400000000000000000000000000000000000000 : ℝ) + b * ((294095322425850911 / 419430400000000000000000000000000000000000000 : ℝ) + b * ((32191383 / 51200000000000000000000000000000000000000 : ℝ) + b * ((32191383 / 51200000000000000000000000000000000000000 : ℝ) + b * ((32191383 / 51200000000000000000000000000000000000000 : ℝ) + b * ((427 / 12800000000000000000000000000000000000000 : ℝ) + b * ((427 / 12800000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def R8 (b : ℝ) : ℝ :=
  (8569333804131506133 / 549755813888 : ℝ) + b * ((3523209899692243131 / 42949672960 : ℝ) + b * ((66155106704623029072942005937907178478387214652342719651 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((657854406823788048879 / 6871947673600 : ℝ) + b * ((31163003118704964135609 / 687194767360000 : ℝ) + b * ((47294185413336305478183 / 3435973836800000 : ℝ) + b * ((885400621158152478519 / 343597383680000 : ℝ) + b * ((76413170394708223955787 / 343597383680000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((29597374186777143932283 / 687194767360000000000 : ℝ) + b * ((768451929663452681697651 / 68719476736000000000000 : ℝ) + b * ((20552183232731292757959 / 68719476736000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1304625968423180078013687 / 2748779069440000000000000000 : ℝ) + b * ((213448261377940519101939 / 3435973836800000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((6354391841549309364939 / 1374389534720000000000000000000 : ℝ) + b * ((11416324984084979342001 / 6871947673600000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((14667197234196971538759 / 137438953472000000000000000000000000 : ℝ) + b * ((4986694683501831677829 / 343597383680000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((887193163737890136429 / 687194767360000000000000000000000000000 : ℝ) + b * ((4570540154468338701 / 687194767360000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((13868481486137393101 / 343597383680000000000000000000000000000000 : ℝ) + b * ((39656233362293335653 / 54975581388800000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((183385066586511063 / 171798691840000000000000000000000000000000000 : ℝ) + b * ((278140318917909 / 42949672960000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((992357919 / 32768000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((923349 / 204800000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H8 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((13780688804770747682994062092821521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13780688804770747682994062092821521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13780688804770747682994062092821521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13780688804770747682994062092821521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13780688804770747682994062092821521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13780688804770747682994062092821521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((4141045415267433724037148030321521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((316988858648677486424007405321521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((53974332999980473698030321521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((53974332999980473698030321521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((53974332999980473698030321521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((53974332999980473698030321521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((3736587031230336692182821521612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1069874564068811867430896612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1069874564068811867430896612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1069874564068811867430896612785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((198700775042728491210615362785347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13282610727165880491925285347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13282610727165880491925285347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((13282610727165880491925285347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((3085573553477199554044035347657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((263712953222173404191597657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((263712953222173404191597657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((263712953222173404191597657280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((11983338593932068927535157280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1008737250579205238282280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1008737250579205238282280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((1008737250579205238282280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((29153715729976907280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((29153715729976907280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((29153715729976907280349 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((267247744992085487 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((267247744992085487 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((267247744992085487 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((511158473 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((511158473 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((4487 / 256000000000000000000000000000000000000000 : ℝ) + b * ((4487 / 256000000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def R9 (b : ℝ) : ℝ :=
  (294813224367082407 / 549755813888 : ℝ) + b * ((39696318641013993 / 17179869184 : ℝ) + b * ((13362969082803104464027444961003798534020455551347342723 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((75653602994235993039 / 34359738368000 : ℝ) + b * ((654517707273005757327 / 687194767360000 : ℝ) + b * ((898903916545819695003 / 3435973836800000 : ℝ) + b * ((734687516051199368253 / 17179869184000000 : ℝ) + b * ((876425549717407921263 / 343597383680000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((3675223877044518748827 / 3435973836800000000000 : ℝ) + b * ((10304035416679172583933 / 68719476736000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((27818781263929762439757 / 2748779069440000000000000000 : ℝ) + b * ((1820573828658555683967 / 3435973836800000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1683042074956661460849 / 6871947673600000000000000000000 : ℝ) + b * ((521995698709627767633 / 34359738368000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((595590596400728326197 / 137438953472000000000000000000000000 : ℝ) + b * ((24837852143830362129 / 343597383680000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((4348934908942324137 / 34359738368000000000000000000000000000 : ℝ) + b * ((23068160912851580211 / 687194767360000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((1205723153696984393 / 343597383680000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((31213336146464469 / 171798691840000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((0 : ℝ) + b * ((189098889 / 32768000000000000000000000000000000000000 : ℝ) + b * ((0 : ℝ) + b * ((178563 / 204800000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))

private noncomputable def H9 (b : ℝ) : ℝ :=
  (0 : ℝ) + b * ((0 : ℝ) + b * ((2598972974376018472555038996201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2598972974376018472555038996201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2598972974376018472555038996201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2598972974376018472555038996201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2598972974376018472555038996201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2598972974376018472555038996201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((520138640822672266644101496201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((24059585202805430871476496201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((15573239587561122626496201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((15573239587561122626496201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((15573239587561122626496201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((6731850072719858995783701465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((187674090846387287721201465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((241205851788243804576465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((241205851788243804576465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((241205851788243804576465979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((14729400014619821305965979544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((4833520925970811928479544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((4833520925970811928479544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((4833520925970811928479544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((198502874066126361954544448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((61335640397147210794448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((61335640397147210794448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((61335640397147210794448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((5266883151828169448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((5266883151828169448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((5266883151828169448652657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((175710274975845424902657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((146578118477329152657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((146578118477329152657277 / 4294967296000000000000000000000000000000000000000 : ℝ) + b * ((2478779903388938994269 / 536870912000000000000000000000000000000000000000 : ℝ) + b * ((142133323920254947 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((142133323920254947 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((44125259919056197 / 268435456000000000000000000000000000000000000000 : ℝ) + b * ((100024813 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((100024813 / 1024000000000000000000000000000000000000000 : ℝ) + b * ((847 / 256000000000000000000000000000000000000000 : ℝ) + b * ((847 / 256000000000000000000000000000000000000000 : ℝ))))))))))))))))))))))))))))))))))))))))


private noncomputable def E2_0 (t : ℝ) : ℝ :=
  (6885376 : ℝ) + (-62873600 : ℝ) * t ^ 2 + (238219264 : ℝ) * t ^ 4 + (-445300736 : ℝ) * t ^ 6 + (354414592 : ℝ) * t ^ 8 + (31694848 : ℝ) * t ^ 10 + (-175960064 : ℝ) * t ^ 12 + (30834688 : ℝ) * t ^ 14 + (12648448 : ℝ) * t ^ 16 + (9437184 : ℝ) * t ^ 18

private noncomputable def E2_1 (t : ℝ) : ℝ :=
  (-10190848 : ℝ) * t + (107970560 : ℝ) * t ^ 3 + (-516161536 : ℝ) * t ^ 5 + (1247215616 : ℝ) * t ^ 7 + (-1373470720 : ℝ) * t ^ 9 + (295927808 : ℝ) * t ^ 11 + (450166784 : ℝ) * t ^ 13 + (-107610112 : ℝ) * t ^ 15 + (-93847552 : ℝ) * t ^ 17

private noncomputable def E2_2 (t : ℝ) : ℝ :=
  (-7733248 : ℝ) + (73629696 : ℝ) * t ^ 2 + (-298844160 : ℝ) * t ^ 4 + (837353472 : ℝ) * t ^ 6 + (-1812332544 : ℝ) * t ^ 8 + (2343272448 : ℝ) * t ^ 10 + (-1106509824 : ℝ) * t ^ 12 + (-397934592 : ℝ) * t ^ 14 + (352321536 : ℝ) * t ^ 16 + (16777216 : ℝ) * t ^ 18

private noncomputable def E2_3 (t : ℝ) : ℝ :=
  (9961472 : ℝ) * t + (-94240768 : ℝ) * t ^ 3 + (338296832 : ℝ) * t ^ 5 + (-693501952 : ℝ) * t ^ 7 + (1185284096 : ℝ) * t ^ 9 + (-1672216576 : ℝ) * t ^ 11 + (1274544128 : ℝ) * t ^ 13 + (-255852544 : ℝ) * t ^ 15 + (-92274688 : ℝ) * t ^ 17

private noncomputable def E2_4 (t : ℝ) : ℝ :=
  (1048576 : ℝ) + (-16252928 : ℝ) * t ^ 2 + (99155968 : ℝ) * t ^ 4 + (-305266688 : ℝ) * t ^ 6 + (523829248 : ℝ) * t ^ 8 + (-579338240 : ℝ) * t ^ 10 + (520093696 : ℝ) * t ^ 12 + (-360710144 : ℝ) * t ^ 14 + (117440512 : ℝ) * t ^ 16

/-- `|N_2|²` on the circle, reduced. -/
private noncomputable def E2 (t x : ℝ) : ℝ :=
  E2_0 t + E2_1 t * x + E2_2 t * x ^ 2 + E2_3 t * x ^ 3 + E2_4 t * x ^ 4

private noncomputable def E3_0 (t : ℝ) : ℝ :=
  (760877056 : ℝ) + (-14335483904 : ℝ) * t ^ 2 + (118752096256 : ℝ) * t ^ 4 + (-569242828800 : ℝ) * t ^ 6 + (1751418744832 : ℝ) * t ^ 8 + (-3620308885504 : ℝ) * t ^ 10 + (5103506804736 : ℝ) * t ^ 12 + (-4884455964672 : ℝ) * t ^ 14 + (3124374650880 : ℝ) * t ^ 16 + (-1236621131776 : ℝ) * t ^ 18 + (-46680506368 : ℝ) * t ^ 20 + (722825658368 : ℝ) * t ^ 22 + (-644107468800 : ℝ) * t ^ 24 + (187402551296 : ℝ) * t ^ 26 + (6710886400 : ℝ) * t ^ 28

private noncomputable def E3_1 (t : ℝ) : ℝ :=
  (-1009385472 : ℝ) * t + (22899769344 : ℝ) * t ^ 3 + (-217966166016 : ℝ) * t ^ 5 + (1169832787968 : ℝ) * t ^ 7 + (-3988859731968 : ℝ) * t ^ 9 + (9168779132928 : ℝ) * t ^ 11 + (-14668916539392 : ℝ) * t ^ 13 + (16823060545536 : ℝ) * t ^ 15 + (-14831397421056 : ℝ) * t ^ 17 + (11477923037184 : ℝ) * t ^ 19 + (-7855920709632 : ℝ) * t ^ 21 + (3352049221632 : ℝ) * t ^ 23 + (-159859605504 : ℝ) * t ^ 25 + (-290614935552 : ℝ) * t ^ 27

private noncomputable def E3_2 (t : ℝ) : ℝ :=
  (-242221056 : ℝ) + (4903796736 : ℝ) * t ^ 2 + (-46073511936 : ℝ) * t ^ 4 + (256679116800 : ℝ) * t ^ 6 + (-907817385984 : ℝ) * t ^ 8 + (2047743688704 : ℝ) * t ^ 10 + (-2715941928960 : ℝ) * t ^ 12 + (1126700974080 : ℝ) * t ^ 14 + (2961440243712 : ℝ) * t ^ 16 + (-6049804320768 : ℝ) * t ^ 18 + (3870456348672 : ℝ) * t ^ 20 + (1401023102976 : ℝ) * t ^ 22 + (-3007089475584 : ℝ) * t ^ 24 + (967827259392 : ℝ) * t ^ 26 + (90194313216 : ℝ) * t ^ 28

private noncomputable def E3_3 (t : ℝ) : ℝ :=
  (637009920 : ℝ) * t + (-15582232576 : ℝ) * t ^ 3 + (163842031616 : ℝ) * t ^ 5 + (-976892854272 : ℝ) * t ^ 7 + (3659045470208 : ℝ) * t ^ 9 + (-8970434248704 : ℝ) * t ^ 11 + (14407705755648 : ℝ) * t ^ 13 + (-14313511452672 : ℝ) * t ^ 15 + (6525606100992 : ℝ) * t ^ 17 + (2892997066752 : ℝ) * t ^ 19 + (-6043011645440 : ℝ) * t ^ 21 + (2876898279424 : ℝ) * t ^ 23 + (179784646656 : ℝ) * t ^ 25 + (-387083927552 : ℝ) * t ^ 27

private noncomputable def E3_4 (t : ℝ) : ℝ :=
  (-154140672 : ℝ) + (3471310848 : ℝ) * t ^ 2 + (-31776768000 : ℝ) * t ^ 4 + (149170028544 : ℝ) * t ^ 6 + (-345397985280 : ℝ) * t ^ 8 + (92578775040 : ℝ) * t ^ 10 + (1707021434880 : ℝ) * t ^ 12 + (-4922831536128 : ℝ) * t ^ 14 + (6326088892416 : ℝ) * t ^ 16 + (-2833768513536 : ℝ) * t ^ 18 + (-2629891522560 : ℝ) * t ^ 20 + (4187203043328 : ℝ) * t ^ 22 + (-2006118825984 : ℝ) * t ^ 24 + (304405807104 : ℝ) * t ^ 26

private noncomputable def E3_5 (t : ℝ) : ℝ :=
  (-25165824 : ℝ) * t + (830472192 : ℝ) * t ^ 3 + (-13767278592 : ℝ) * t ^ 5 + (129806106624 : ℝ) * t ^ 7 + (-738259107840 : ℝ) * t ^ 9 + (2663723040768 : ℝ) * t ^ 11 + (-6376353693696 : ℝ) * t ^ 13 + (10530396831744 : ℝ) * t ^ 15 + (-12125507420160 : ℝ) * t ^ 17 + (9019066417152 : ℝ) * t ^ 19 + (-3131182153728 : ℝ) * t ^ 21 + (-466071060480 : ℝ) * t ^ 23 + (507343011840 : ℝ) * t ^ 25

private noncomputable def E3_6 (t : ℝ) : ℝ :=
  (100663296 : ℝ) + (-2659188736 : ℝ) * t ^ 2 + (30796677120 : ℝ) * t ^ 4 + (-202469015552 : ℝ) * t ^ 6 + (819783008256 : ℝ) * t ^ 8 + (-2074439319552 : ℝ) * t ^ 10 + (3126035742720 : ℝ) * t ^ 12 + (-2142951702528 : ℝ) * t ^ 14 + (-1281314783232 : ℝ) * t ^ 16 + (4740926668800 : ℝ) * t ^ 18 + (-5450598711296 : ℝ) * t ^ 20 + (3267329261568 : ℝ) * t ^ 22 + (-830539300864 : ℝ) * t ^ 24

private noncomputable def E3_7 (t : ℝ) : ℝ :=
  (402653184 : ℝ) * t ^ 3 + (-9009364992 : ℝ) * t ^ 5 + (86520102912 : ℝ) * t ^ 7 + (-468207009792 : ℝ) * t ^ 9 + (1581388922880 : ℝ) * t ^ 11 + (-3505621303296 : ℝ) * t ^ 13 + (5248357761024 : ℝ) * t ^ 15 + (-5376325976064 : ℝ) * t ^ 17 + (3710851743744 : ℝ) * t ^ 19 + (-1584037625856 : ℝ) * t ^ 21 + (315680096256 : ℝ) * t ^ 23

/-- `|N_3|²` on the circle, reduced. -/
private noncomputable def E3 (t x : ℝ) : ℝ :=
  E3_0 t + E3_1 t * x + E3_2 t * x ^ 2 + E3_3 t * x ^ 3 + E3_4 t * x ^ 4 + E3_5 t * x ^ 5 + E3_6 t * x ^ 6 + E3_7 t * x ^ 7

private noncomputable def E4_0 (t : ℝ) : ℝ :=
  (4742250496 : ℝ) + (-111123202048 : ℝ) * t ^ 2 + (1164419174400 : ℝ) * t ^ 4 + (-7159435956224 : ℝ) * t ^ 6 + (28312624640000 : ℝ) * t ^ 8 + (-73304863490048 : ℝ) * t ^ 10 + (116053593665536 : ℝ) * t ^ 12 + (-69842162335744 : ℝ) * t ^ 14 + (-139754711265280 : ℝ) * t ^ 16 + (420739754885120 : ℝ) * t ^ 18 + (-520283776434176 : ℝ) * t ^ 20 + (302489981521920 : ℝ) * t ^ 22 + (53572220518400 : ℝ) * t ^ 24 + (-257429213216768 : ℝ) * t ^ 26 + (227535418818560 : ℝ) * t ^ 28 + (-101948330082304 : ℝ) * t ^ 30 + (19956565540864 : ℝ) * t ^ 32 + (4294967296 : ℝ) * t ^ 34

private noncomputable def E4_1 (t : ℝ) : ℝ :=
  (-7615021056 : ℝ) * t + (204888244224 : ℝ) * t ^ 3 + (-2508224765952 : ℝ) * t ^ 5 + (18282220904448 : ℝ) * t ^ 7 + (-87354829135872 : ℝ) * t ^ 9 + (284196667219968 : ℝ) * t ^ 11 + (-629797498724352 : ℝ) * t ^ 13 + (896853270700032 : ℝ) * t ^ 15 + (-598570250084352 : ℝ) * t ^ 17 + (-519290531438592 : ℝ) * t ^ 19 + (1924938668064768 : ℝ) * t ^ 21 + (-2615563681824768 : ℝ) * t ^ 23 + (2153435887042560 : ℝ) * t ^ 25 + (-1090465483456512 : ℝ) * t ^ 27 + (262333884530688 : ℝ) * t ^ 29 + (27652207411200 : ℝ) * t ^ 31 + (-24339579666432 : ℝ) * t ^ 33

private noncomputable def E4_2 (t : ℝ) : ℝ :=
  (-3472883712 : ℝ) + (76982255616 : ℝ) * t ^ 2 + (-778441457664 : ℝ) * t ^ 4 + (4986106970112 : ℝ) * t ^ 6 + (-24065496170496 : ℝ) * t ^ 8 + (96044577423360 : ℝ) * t ^ 10 + (-319006386044928 : ℝ) * t ^ 12 + (847801358647296 : ℝ) * t ^ 14 + (-1738717686546432 : ℝ) * t ^ 16 + (2686096953999360 : ℝ) * t ^ 18 + (-3031776016711680 : ℝ) * t ^ 20 + (2308747177820160 : ℝ) * t ^ 22 + (-852188004089856 : ℝ) * t ^ 24 + (-367021117145088 : ℝ) * t ^ 26 + (696497146429440 : ℝ) * t ^ 28 + (-384853497348096 : ℝ) * t ^ 30 + (70944269795328 : ℝ) * t ^ 32 + (7215545057280 : ℝ) * t ^ 34

private noncomputable def E4_3 (t : ℝ) : ℝ :=
  (8304721920 : ℝ) * t + (-213808840704 : ℝ) * t ^ 3 + (2484015726592 : ℝ) * t ^ 5 + (-17334464413696 : ℝ) * t ^ 7 + (81699120676864 : ℝ) * t ^ 9 + (-277484326813696 : ℝ) * t ^ 11 + (708041528442880 : ℝ) * t ^ 13 + (-1399786784948224 : ℝ) * t ^ 15 + (2209554043699200 : ℝ) * t ^ 17 + (-2889799241367552 : ℝ) * t ^ 19 + (3238448884482048 : ℝ) * t ^ 21 + (-3087184629858304 : ℝ) * t ^ 23 + (2324327003324416 : ℝ) * t ^ 25 + (-1201286473056256 : ℝ) * t ^ 27 + (313171835355136 : ℝ) * t ^ 29 + (20849918738432 : ℝ) * t ^ 31 + (-25494925869056 : ℝ) * t ^ 33

private noncomputable def E4_4 (t : ℝ) : ℝ :=
  (-2868903936 : ℝ) + (80580968448 : ℝ) * t ^ 2 + (-1020165881856 : ℝ) * t ^ 4 + (7714268774400 : ℝ) * t ^ 6 + (-38936020451328 : ℝ) * t ^ 8 + (138973934321664 : ℝ) * t ^ 10 + (-363421796597760 : ℝ) * t ^ 12 + (715097565954048 : ℝ) * t ^ 14 + (-1085747795066880 : ℝ) * t ^ 16 + (1299699481116672 : ℝ) * t ^ 18 + (-1222502372081664 : ℝ) * t ^ 20 + (836542157291520 : ℝ) * t ^ 22 + (-303615549898752 : ℝ) * t ^ 24 + (-74159807791104 : ℝ) * t ^ 26 + (138611747979264 : ℝ) * t ^ 28 + (-50199577755648 : ℝ) * t ^ 30 + (2886218022912 : ℝ) * t ^ 32

private noncomputable def E4_5 (t : ℝ) : ℝ :=
  (-1006632960 : ℝ) * t + (28563210240 : ℝ) * t ^ 3 + (-354404007936 : ℝ) * t ^ 5 + (2569696444416 : ℝ) * t ^ 7 + (-12370197479424 : ℝ) * t ^ 9 + (42846696898560 : ℝ) * t ^ 11 + (-112288048742400 : ℝ) * t ^ 13 + (225627645542400 : ℝ) * t ^ 15 + (-343072981647360 : ℝ) * t ^ 17 + (403087506800640 : ℝ) * t ^ 19 + (-431176883896320 : ℝ) * t ^ 21 + (522950604226560 : ℝ) * t ^ 23 + (-630151628980224 : ℝ) * t ^ 25 + (563936319504384 : ℝ) * t ^ 27 + (-303787331813376 : ℝ) * t ^ 29 + (72155450572800 : ℝ) * t ^ 31

private noncomputable def E4_6 (t : ℝ) : ℝ :=
  (1610612736 : ℝ) + (-44962938880 : ℝ) * t ^ 2 + (567841652736 : ℝ) * t ^ 4 + (-4332288212992 : ℝ) * t ^ 6 + (22535106199552 : ℝ) * t ^ 8 + (-85480521596928 : ℝ) * t ^ 10 + (246370584494080 : ℝ) * t ^ 12 + (-554903485808640 : ℝ) * t ^ 14 + (1004756961853440 : ℝ) * t ^ 16 + (-1516934544752640 : ℝ) * t ^ 18 + (1964326386663424 : ℝ) * t ^ 20 + (-2149995365007360 : ℝ) * t ^ 22 + (1866339853533184 : ℝ) * t ^ 24 + (-1172199385858048 : ℝ) * t ^ 26 + (466059786190848 : ℝ) * t ^ 28 + (-87067577024512 : ℝ) * t ^ 30

private noncomputable def E4_7 (t : ℝ) : ℝ :=
  (-2415919104 : ℝ) * t ^ 3 + (66437775360 : ℝ) * t ^ 5 + (-816580657152 : ℝ) * t ^ 7 + (5968603643904 : ℝ) * t ^ 9 + (-29223703019520 : ℝ) * t ^ 11 + (102666181017600 : ℝ) * t ^ 13 + (-270465493893120 : ℝ) * t ^ 15 + (546866221547520 : ℝ) * t ^ 17 + (-849481322987520 : ℝ) * t ^ 19 + (994570477240320 : ℝ) * t ^ 21 + (-847224175067136 : ℝ) * t ^ 23 + (496302261534720 : ℝ) * t ^ 25 + (-179531780456448 : ℝ) * t ^ 27 + (30305289240576 : ℝ) * t ^ 29

/-- `|N_4|²` on the circle, reduced. -/
private noncomputable def E4 (t x : ℝ) : ℝ :=
  E4_0 t + E4_1 t * x + E4_2 t * x ^ 2 + E4_3 t * x ^ 3 + E4_4 t * x ^ 4 + E4_5 t * x ^ 5 + E4_6 t * x ^ 6 + E4_7 t * x ^ 7

private noncomputable def E5_0 (t : ℝ) : ℝ :=
  (25681985536 : ℝ) + (-766951948288 : ℝ) * t ^ 2 + (10412981305344 : ℝ) * t ^ 4 + (-85243142029312 : ℝ) * t ^ 6 + (470642708008960 : ℝ) * t ^ 8 + (-1858516409782272 : ℝ) * t ^ 10 + (5441741358411776 : ℝ) * t ^ 12 + (-12147203486990336 : ℝ) * t ^ 14 + (21333339218915328 : ℝ) * t ^ 16 + (-30832264044232704 : ℝ) * t ^ 18 + (38412114917167104 : ℝ) * t ^ 20 + (-40531470100217856 : ℝ) * t ^ 22 + (29212051565412352 : ℝ) * t ^ 24 + (1624200066633728 : ℝ) * t ^ 26 + (-41154455211638784 : ℝ) * t ^ 28 + (63695255330947072 : ℝ) * t ^ 30 + (-55489752098406400 : ℝ) * t ^ 32 + (30070835263832064 : ℝ) * t ^ 34 + (-9488922786660352 : ℝ) * t ^ 36 + (1278392720687104 : ℝ) * t ^ 38 + (39582418599936 : ℝ) * t ^ 40

private noncomputable def E5_1 (t : ℝ) : ℝ :=
  (-59018051584 : ℝ) * t + (1903080767488 : ℝ) * t ^ 3 + (-27917728481280 : ℝ) * t ^ 5 + (247766755557376 : ℝ) * t ^ 7 + (-1491763958210560 : ℝ) * t ^ 9 + (6476012921511936 : ℝ) * t ^ 11 + (-21056574216593408 : ℝ) * t ^ 13 + (52831585108385792 : ℝ) * t ^ 15 + (-105845780868440064 : ℝ) * t ^ 17 + (178173725285425152 : ℝ) * t ^ 19 + (-269050395894521856 : ℝ) * t ^ 21 + (379040088555282432 : ℝ) * t ^ 23 + (-482577929540927488 : ℝ) * t ^ 25 + (511948209648566272 : ℝ) * t ^ 27 + (-414916879844376576 : ℝ) * t ^ 29 + (232877431413800960 : ℝ) * t ^ 31 + (-73696176741810176 : ℝ) * t ^ 33 + (790210094825472 : ℝ) * t ^ 35 + (8584144976084992 : ℝ) * t ^ 37 + (-2307600028794880 : ℝ) * t ^ 39

private noncomputable def E5_2 (t : ℝ) : ℝ :=
  (631242752 : ℝ) + (-39547568128 : ℝ) * t ^ 2 + (934658048000 : ℝ) * t ^ 4 + (-12409299304448 : ℝ) * t ^ 6 + (107715790372864 : ℝ) * t ^ 8 + (-662821656166400 : ℝ) * t ^ 10 + (3056611107094528 : ℝ) * t ^ 12 + (-11052025731055616 : ℝ) * t ^ 14 + (32439144225095680 : ℝ) * t ^ 16 + (-78408829022601216 : ℝ) * t ^ 18 + (153728232554545152 : ℝ) * t ^ 20 + (-233227975256309760 : ℝ) * t ^ 22 + (248983417030000640 : ℝ) * t ^ 24 + (-138230646878175232 : ℝ) * t ^ 26 + (-65796884958281728 : ℝ) * t ^ 28 + (227766704119218176 : ℝ) * t ^ 30 + (-242884423563870208 : ℝ) * t ^ 32 + (146387535549956096 : ℝ) * t ^ 34 + (-48948745840099328 : ℝ) * t ^ 36 + (6261924878614528 : ℝ) * t ^ 38 + (492581209243648 : ℝ) * t ^ 40

private noncomputable def E5_3 (t : ℝ) : ℝ :=
  (34183577600 : ℝ) * t + (-1150965252096 : ℝ) * t ^ 3 + (17436606201856 : ℝ) * t ^ 5 + (-156648915206144 : ℝ) * t ^ 7 + (922918687277056 : ℝ) * t ^ 9 + (-3692358682345472 : ℝ) * t ^ 11 + (9785738679943168 : ℝ) * t ^ 13 + (-14072362020896768 : ℝ) * t ^ 15 + (-8082975840468992 : ℝ) * t ^ 17 + (106545787768209408 : ℝ) * t ^ 19 + (-328049522901647360 : ℝ) * t ^ 21 + (652129177197215744 : ℝ) * t ^ 23 + (-951115623335723008 : ℝ) * t ^ 25 + (1051756724731510784 : ℝ) * t ^ 27 + (-878983112632041472 : ℝ) * t ^ 29 + (537513581411827712 : ℝ) * t ^ 31 + (-222884275714785280 : ℝ) * t ^ 33 + (51692791855579136 : ℝ) * t ^ 35 + (-2002348113133568 : ℝ) * t ^ 37 + (-1323811999842304 : ℝ) * t ^ 39

private noncomputable def E5_4 (t : ℝ) : ℝ :=
  (-14629732352 : ℝ) + (467614564352 : ℝ) * t ^ 2 + (-6514811076608 : ℝ) * t ^ 4 + (50591313166336 : ℝ) * t ^ 6 + (-221523647922176 : ℝ) * t ^ 8 + (335627039801344 : ℝ) * t ^ 10 + (2262907640676352 : ℝ) * t ^ 12 + (-18989636564221952 : ℝ) * t ^ 14 + (77515284727005184 : ℝ) * t ^ 16 + (-214887322825916416 : ℝ) * t ^ 18 + (440445475568222208 : ℝ) * t ^ 20 + (-691231759767764992 : ℝ) * t ^ 22 + (844301150490460160 : ℝ) * t ^ 24 + (-807490341050515456 : ℝ) * t ^ 26 + (603568714696097792 : ℝ) * t ^ 28 + (-349477247276548096 : ℝ) * t ^ 30 + (154574022389006336 : ℝ) * t ^ 32 + (-51325670936018944 : ℝ) * t ^ 34 + (12253644774703104 : ℝ) * t ^ 36 + (-1677854743986176 : ℝ) * t ^ 38

private noncomputable def E5_5 (t : ℝ) : ℝ :=
  (11274289152 : ℝ) * t + (-403794034688 : ℝ) * t ^ 3 + (6625926578176 : ℝ) * t ^ 5 + (-66626703589376 : ℝ) * t ^ 7 + (463761018191872 : ℝ) * t ^ 9 + (-2392226232270848 : ℝ) * t ^ 11 + (9540553693855744 : ℝ) * t ^ 13 + (-30226229266350080 : ℝ) * t ^ 15 + (77514493428367360 : ℝ) * t ^ 17 + (-163513820117073920 : ℝ) * t ^ 19 + (288211500274810880 : ℝ) * t ^ 21 + (-429656030580834304 : ℝ) * t ^ 23 + (542981327780052992 : ℝ) * t ^ 25 + (-574950646063562752 : ℝ) * t ^ 27 + (496664003276177408 : ℝ) * t ^ 29 + (-335080766864097280 : ℝ) * t ^ 31 + (164885572609900544 : ℝ) * t ^ 33 + (-52431723798986752 : ℝ) * t ^ 35 + (8050624138575872 : ℝ) * t ^ 37

private noncomputable def E5_6 (t : ℝ) : ℝ :=
  (4831838208 : ℝ) + (-168711684096 : ℝ) * t ^ 2 + (2578658099200 : ℝ) * t ^ 4 + (-22176342212608 : ℝ) * t ^ 6 + (111052194840576 : ℝ) * t ^ 8 + (-247539557728256 : ℝ) * t ^ 10 + (-706861651197952 : ℝ) * t ^ 12 + (8643752588476416 : ℝ) * t ^ 14 + (-40393216520093696 : ℝ) * t ^ 16 + (125057925578227712 : ℝ) * t ^ 18 + (-286877481710125056 : ℝ) * t ^ 20 + (508843631307653120 : ℝ) * t ^ 22 + (-709743174276349952 : ℝ) * t ^ 24 + (779726037410906112 : ℝ) * t ^ 26 + (-666559799722246144 : ℝ) * t ^ 28 + (430521088158466048 : ℝ) * t ^ 30 + (-198491114720722944 : ℝ) * t ^ 32 + (58370804575895552 : ℝ) * t ^ 34 + (-8235342092042240 : ℝ) * t ^ 36

private noncomputable def E5_7 (t : ℝ) : ℝ :=
  (-6442450944 : ℝ) * t + (258234908672 : ℝ) * t ^ 3 + (-4719632187392 : ℝ) * t ^ 5 + (52307668500480 : ℝ) * t ^ 7 + (-394666046390272 : ℝ) * t ^ 9 + (2159228716318720 : ℝ) * t ^ 11 + (-8915224567480320 : ℝ) * t ^ 13 + (28553948702965760 : ℝ) * t ^ 15 + (-72312280690196480 : ℝ) * t ^ 17 + (146574122491576320 : ℝ) * t ^ 19 + (-239101278427283456 : ℝ) * t ^ 21 + (313469697007812608 : ℝ) * t ^ 23 + (-327331833307987968 : ℝ) * t ^ 25 + (267135973379276800 : ℝ) * t ^ 27 + (-164719675203125248 : ℝ) * t ^ 29 + (72324629334589440 : ℝ) * t ^ 31 + (-20184284706897920 : ℝ) * t ^ 33 + (2693803488051200 : ℝ) * t ^ 35

/-- `|N_5|²` on the circle, reduced. -/
private noncomputable def E5 (t x : ℝ) : ℝ :=
  E5_0 t + E5_1 t * x + E5_2 t * x ^ 2 + E5_3 t * x ^ 3 + E5_4 t * x ^ 4 + E5_5 t * x ^ 5 + E5_6 t * x ^ 6 + E5_7 t * x ^ 7

private noncomputable def Bp_0 (t : ℝ) : ℝ :=
  (225 / 256 : ℝ) + (-335 / 64 : ℝ) * t ^ 2 + (1027 / 128 : ℝ) * t ^ 4 + (609 / 64 : ℝ) * t ^ 6 + (-9823 / 256 : ℝ) * t ^ 8 + (121 / 4 : ℝ) * t ^ 10

private noncomputable def Bp_1 (t : ℝ) : ℝ :=
  (-125 / 64 : ℝ) * t + (1325 / 64 : ℝ) * t ^ 3 + (-5115 / 64 : ℝ) * t ^ 5 + (8591 / 64 : ℝ) * t ^ 7 + (-1331 / 16 : ℝ) * t ^ 9

private noncomputable def Bp_2 (t : ℝ) : ℝ :=
  (1 : ℝ) + (-47 / 4 : ℝ) * t ^ 2 + (101 / 2 : ℝ) * t ^ 4 + (-391 / 4 : ℝ) * t ^ 6 + (86 : ℝ) * t ^ 8 + (-28 : ℝ) * t ^ 10

private noncomputable def Bp_3 (t : ℝ) : ℝ :=
  (5 / 4 : ℝ) * t + (-239 / 16 : ℝ) * t ^ 3 + (1029 / 16 : ℝ) * t ^ 5 + (-235 / 2 : ℝ) * t ^ 7 + (77 : ℝ) * t ^ 9

private noncomputable def Bp_4 (t : ℝ) : ℝ :=
  (-1 : ℝ) + (23 / 2 : ℝ) * t ^ 2 + (-753 / 16 : ℝ) * t ^ 4 + (161 / 2 : ℝ) * t ^ 6 + (-49 : ℝ) * t ^ 8

/-- `|𝒬|²` on the circle, reduced. -/
private noncomputable def Bp (t x : ℝ) : ℝ :=
  Bp_0 t + Bp_1 t * x + Bp_2 t * x ^ 2 + Bp_3 t * x ^ 3 + Bp_4 t * x ^ 4

/-- One step of the Chebyshev recursion for `Re cⁿ`, `Im cⁿ / Im c` on `|c| = 1`. -/
private lemma cpow_step (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) {m n : ℕ} (hn : n = m + 1) {A B A' B' : ℝ}
    (hA : (c ^ m).re = A) (hB : (c ^ m).im = c.im * B) (hA' : A * c.re - (1 - c.re ^ 2) * B = A')
    (hB' : A + c.re * B = B') : (c ^ n).re = A' ∧ (c ^ n).im = c.im * B' := by
  subst hn
  rw [pow_succ, mul_re, mul_im, hA, hB, ← hA', ← hB']
  constructor
  · linear_combination (-B) * h
  · ring

private noncomputable def Gtx_0 (t : ℝ) : ℝ :=
  (228661516828672 : ℝ) + (-6050397189701632 : ℝ) * t ^ 2 + (72599889511858176 : ℝ) * t ^ 4 + (-516543838868488192 : ℝ) * t ^ 6 + (2367096420897292288 : ℝ) * t ^ 8 + (-6896869295521935360 : ℝ) * t ^ 10 + (10149264684049481216 : ℝ) * t ^ 12 + (9612483507748718848 : ℝ) * t ^ 14 + (-92845012660286681976 : ℝ) * t ^ 16 + (245345078966148875328 : ℝ) * t ^ 18 + (-338965015480386877728 : ℝ) * t ^ 20 + (118602383033783249856 : ℝ) * t ^ 22 + (536854159132298735920 : ℝ) * t ^ 24 + (-1321739352772237807168 : ℝ) * t ^ 26 + (1670222034994942732512 : ℝ) * t ^ 28 + (-1347433616085137038016 : ℝ) * t ^ 30 + (702001404119435204744 : ℝ) * t ^ 32 + (-217556103410153315328 : ℝ) * t ^ 34 + (30778941090249605120 : ℝ) * t ^ 36 + (-44753215626936320 : ℝ) * t ^ 38 + (-1385384650997760 : ℝ) * t ^ 40

private noncomputable def Gtx_1 (t : ℝ) : ℝ :=
  (-271724544000000 : ℝ) + (-1206608025616384 : ℝ) * t + (7040684851200000 : ℝ) * t ^ 2 + (37298050967535616 : ℝ) * t ^ 3 + (-83210743848960000 : ℝ) * t ^ 4 + (-530476485914394624 : ℝ) * t ^ 5 + (587130039595008000 : ℝ) * t ^ 6 + (4593206130070994944 : ℝ) * t ^ 7 + (-2696756282354534400 : ℝ) * t ^ 8 + (-26919940571505639424 : ℝ) * t ^ 9 + (8065691475445094400 : ℝ) * t ^ 10 + (111799983273643524096 : ℝ) * t ^ 11 + (-13493793806558956800 : ℝ) * t ^ 12 + (-331548965933240545280 : ℝ) * t ^ 13 + (-1561806799445692800 : ℝ) * t ^ 14 + (671673298740253165568 : ℝ) * t ^ 15 + (76508959321214702100 : ℝ) * t ^ 16 + (-740478667211661247296 : ℝ) * t ^ 17 + (-218915493748504207200 : ℝ) * t ^ 18 + (-415806123551392984512 : ℝ) * t ^ 19 + (309727637861889265200 : ℝ) * t ^ 20 + (3723680842523454082752 : ℝ) * t ^ 21 + (-109226581636189399200 : ℝ) * t ^ 22 + (-8655109232501941902528 : ℝ) * t ^ 23 + (-497524520385741630600 : ℝ) * t ^ 24 + (12589968232455717553472 : ℝ) * t ^ 25 + (1226250503628712380000 : ℝ) * t ^ 26 + (-12723985408622065416512 : ℝ) * t ^ 27 + (-1549843171093114606800 : ℝ) * t ^ 28 + (9014327368310735807040 : ℝ) * t ^ 29 + (1249853429428989184800 : ℝ) * t ^ 30 + (-4305790784422499963968 : ℝ) * t ^ 31 + (-650606882013875486700 : ℝ) * t ^ 32 + (1252063810984471293184 : ℝ) * t ^ 33 + (201265042184990784000 : ℝ) * t ^ 34 + (-167811112103166787584 : ℝ) * t ^ 35 + (-28313848926281318400 : ℝ) * t ^ 36 + (-246776300998492160 : ℝ) * t ^ 37 + (80766001007820800 : ℝ) * t ^ 39

private noncomputable def Gtx_2 (t : ℝ) : ℝ :=
  (725487271804928 : ℝ) + (1207664640000000 : ℝ) * t + (-21088171292360704 : ℝ) * t ^ 2 + (-36900864000000000 : ℝ) * t ^ 3 + (273406509457473536 : ℝ) * t ^ 4 + (520147869696000000 : ℝ) * t ^ 5 + (-2025351636874330112 : ℝ) * t ^ 6 + (-4471525262131200000 : ℝ) * t ^ 7 + (8729872923052343296 : ℝ) * t ^ 8 + (26054709508638720000 : ℝ) * t ^ 9 + (-14516749631449530368 : ℝ) * t ^ 10 + (-107717955838643404800 : ℝ) * t ^ 11 + (-75744863425320058880 : ℝ) * t ^ 12 + (318520667032846387200 : ℝ) * t ^ 13 + (691554559801742811136 : ℝ) * t ^ 14 + (-645426338420810419200 : ℝ) * t ^ 15 + (-2948175540333108666368 : ℝ) * t ^ 16 + (720676082037214648800 : ℝ) * t ^ 17 + (8518792269773402239104 : ℝ) * t ^ 18 + (348881592194054992800 : ℝ) * t ^ 19 + (-18158853654788436672768 : ℝ) * t ^ 20 + (-3427124867629735053600 : ℝ) * t ^ 21 + (29389474480813556258688 : ℝ) * t ^ 22 + (8017892275326092359200 : ℝ) * t ^ 23 + (-36349654182706566521344 : ℝ) * t ^ 24 + (-11679237995452051096800 : ℝ) * t ^ 25 + (34087926530504377704320 : ℝ) * t ^ 26 + (11805537495511189029600 : ℝ) * t ^ 27 + (-23716104372104332499200 : ℝ) * t ^ 28 + (-8361952406631570146400 : ℝ) * t ^ 29 + (11756620905500169093248 : ℝ) * t ^ 30 + (3992871058587543132000 : ℝ) * t ^ 31 + (-3862525812208628257792 : ℝ) * t ^ 32 + (-1160709804588436502400 : ℝ) * t ^ 33 + (729391454237328017408 : ℝ) * t ^ 34 + (155726169094547251200 : ℝ) * t ^ 35 + (-54886384712331296768 : ℝ) * t ^ 36 + (-235077647602810880 : ℝ) * t ^ 38 + (-17240342323527680 : ℝ) * t ^ 40

private noncomputable def Gtx_3 (t : ℝ) : ℝ :=
  (-618324295680000 : ℝ) + (-733388021432320 : ℝ) * t + (18262465708032000 : ℝ) * t ^ 2 + (29378577294163968 : ℝ) * t ^ 3 + (-239196005675827200 : ℝ) * t ^ 4 + (-544624906775035904 : ℝ) * t ^ 5 + (1778415343475097600 : ℝ) * t ^ 6 + (6203321017185992704 : ℝ) * t ^ 7 + (-7601796469319270400 : ℝ) * t ^ 8 + (-48656546776627085312 : ℝ) * t ^ 9 + (11595395656573747200 : ℝ) * t ^ 10 + (279254365051718926336 : ℝ) * t ^ 11 + (75857864019569049600 : ℝ) * t ^ 12 + (-1216169481277790289920 : ℝ) * t ^ 13 + (-655023180826951372800 : ℝ) * t ^ 14 + (4111497393658869268480 : ℝ) * t ^ 15 + (2761254909593987788800 : ℝ) * t ^ 16 + (-10940217360878254459904 : ℝ) * t ^ 17 + (-7943886566058204216000 : ℝ) * t ^ 18 + (23076824276233291440384 : ℝ) * t ^ 19 + (16896987262645577942400 : ℝ) * t ^ 20 + (-38640679481272383282944 : ℝ) * t ^ 21 + (-27315273992581556654400 : ℝ) * t ^ 22 + (51134520786819842912768 : ℝ) * t ^ 23 + (33763049639997271776000 : ℝ) * t ^ 24 + (-52887238170588353853952 : ℝ) * t ^ 25 + (-31653797401856467656000 : ℝ) * t ^ 26 + (41900695578562308478208 : ℝ) * t ^ 27 + (22023376896081419913600 : ℝ) * t ^ 28 + (-24580856851933413284608 : ℝ) * t ^ 29 + (-10922002463355649848000 : ℝ) * t ^ 30 + (10069800581938145355776 : ℝ) * t ^ 31 + (3592704138542682508800 : ℝ) * t ^ 32 + (-2573232600859014148096 : ℝ) * t ^ 33 + (-681216899333568998400 : ℝ) * t ^ 34 + (308601425948572123136 : ℝ) * t ^ 35 + (52415720326338969600 : ℝ) * t ^ 36 + (126298495500943360 : ℝ) * t ^ 37 + (46333419994480640 : ℝ) * t ^ 39

private noncomputable def Gtx_4 (t : ℝ) : ℝ :=
  (-289223500365824 : ℝ) + (601148620800000 : ℝ) * t + (4948432208789504 : ℝ) * t ^ 2 + (-25286887342080000 : ℝ) * t ^ 3 + (11684893092216832 : ℝ) * t ^ 4 + (482665662775296000 : ℝ) * t ^ 5 + (-1148154850391883776 : ℝ) * t ^ 6 + (-5595563371423334400 : ℝ) * t ^ 7 + (16085075864809111552 : ℝ) * t ^ 8 + (44365938635302502400 : ℝ) * t ^ 9 + (-129658104245899231232 : ℝ) * t ^ 10 + (-256334586227977420800 : ℝ) * t ^ 11 + (718870676786268798976 : ℝ) * t ^ 12 + (1121031555470113996800 : ℝ) * t ^ 13 + (-2938280613346573549568 : ℝ) * t ^ 14 + (-3799984696663705804800 : ℝ) * t ^ 15 + (9165423403639374229504 : ℝ) * t ^ 16 + (10128917615624961753600 : ℝ) * t ^ 17 + (-22214276176664855296000 : ℝ) * t ^ 18 + (-21390470387559788860800 : ℝ) * t ^ 19 + (42153463014030376631040 : ℝ) * t ^ 20 + (35846149288837638441600 : ℝ) * t ^ 21 + (-62594546517987229379584 : ℝ) * t ^ 22 + (-47464647088517195846400 : ℝ) * t ^ 23 + (72128822522611533152768 : ℝ) * t ^ 24 + (49114426700463257952000 : ℝ) * t ^ 25 + (-63368545503352100322304 : ℝ) * t ^ 26 + (-38927533586287598179200 : ℝ) * t ^ 27 + (41155597145941081389824 : ℝ) * t ^ 28 + (22846651637377200796800 : ℝ) * t ^ 29 + (-18740601093793539770368 : ℝ) * t ^ 30 + (-9365152921747752729600 : ℝ) * t ^ 31 + (5426727046836922953728 : ℝ) * t ^ 32 + (2396000965698692352000 : ℝ) * t ^ 33 + (-803706823237526290432 : ℝ) * t ^ 34 + (-288286461794864332800 : ℝ) * t ^ 35 + (25689313144681267200 : ℝ) * t ^ 36 + (58724916039516160 : ℝ) * t ^ 38

private noncomputable def Gtx_5 (t : ℝ) : ℝ :=
  (266566474137600 : ℝ) + (2427526789988352 : ℝ) * t + (-4541248438272000 : ℝ) * t ^ 2 + (-89147614586470400 : ℝ) * t ^ 3 + (-11541881762611200 : ℝ) * t ^ 4 + (1520681555398230016 : ℝ) * t ^ 5 + (1071956884665139200 : ℝ) * t ^ 6 + (-16003997407561908224 : ℝ) * t ^ 7 + (-14972632110858240000 : ℝ) * t ^ 8 + (116392751177691824128 : ℝ) * t ^ 9 + (120579068079990374400 : ℝ) * t ^ 10 + (-620786326009777750016 : ℝ) * t ^ 11 + (-668261268062812569600 : ℝ) * t ^ 12 + (2514179715931933769728 : ℝ) * t ^ 13 + (2730822886561583923200 : ℝ) * t ^ 14 + (-7896098757769612230656 : ℝ) * t ^ 15 + (-8517099760475310950400 : ℝ) * t ^ 16 + (19461968238802988843008 : ℝ) * t ^ 17 + (20640792582566726169600 : ℝ) * t ^ 18 + (-37839240777254135078912 : ℝ) * t ^ 19 + (-39164425292380466332800 : ℝ) * t ^ 20 + (57982502533638680007680 : ℝ) * t ^ 21 + (58152342909654616896000 : ℝ) * t ^ 22 + (-69535963364732359373824 : ℝ) * t ^ 23 + (-67007212470682224249600 : ℝ) * t ^ 24 + (64342403252568728873984 : ℝ) * t ^ 25 + (58868482524661376985600 : ℝ) * t ^ 26 + (-44845390749988903656448 : ℝ) * t ^ 27 + (-38234697196935371932800 : ℝ) * t ^ 28 + (22637935641539747631104 : ℝ) * t ^ 29 + (17413043041561139481600 : ℝ) * t ^ 30 + (-7745119893298703319040 : ℝ) * t ^ 31 + (-5044217050533527193600 : ℝ) * t ^ 32 + (1584082474980120657920 : ℝ) * t ^ 33 + (748034058314266214400 : ℝ) * t ^ 34 + (-142009043959498670080 : ℝ) * t ^ 35 + (-24258515192355225600 : ℝ) * t ^ 36 + (-281771844850155520 : ℝ) * t ^ 37

private noncomputable def Gtx_6 (t : ℝ) : ℝ :=
  (-760584484159488 : ℝ) + (-2253448544256000 : ℝ) * t + (28910289634197504 : ℝ) * t ^ 2 + (82756523733811200 : ℝ) * t ^ 3 + (-511743510978756608 : ℝ) * t ^ 4 + (-1411670779468185600 : ℝ) * t ^ 5 + (5607176847818227712 : ℝ) * t ^ 6 + (14856790449586176000 : ℝ) * t ^ 7 + (-42632594443261181952 : ℝ) * t ^ 8 + (-108050323683881779200 : ℝ) * t ^ 9 + (238930830939590754304 : ℝ) * t ^ 10 + (576301796877297254400 : ℝ) * t ^ 11 + (-1023098568943926771712 : ℝ) * t ^ 12 + (-2334083356168755609600 : ℝ) * t ^ 13 + (3422259819586823651328 : ℝ) * t ^ 14 + (7330758313175403724800 : ℝ) * t ^ 15 + (-9061934283373530841088 : ℝ) * t ^ 16 + (-18069360561693342720000 : ℝ) * t ^ 17 + (19120555421762635857920 : ℝ) * t ^ 18 + (35133492541977710899200 : ℝ) * t ^ 19 + (-32173652756289606696960 : ℝ) * t ^ 20 + (-53839722643419396902400 : ℝ) * t ^ 21 + (42958707416186586761216 : ℝ) * t ^ 22 + (64572713629632998899200 : ℝ) * t ^ 23 + (-44984049806225443991552 : ℝ) * t ^ 24 + (-59756232480732554457600 : ℝ) * t ^ 25 + (36183984329621037090816 : ℝ) * t ^ 26 + (41655821498446349376000 : ℝ) * t ^ 27 + (-21597997969889078444032 : ℝ) * t ^ 28 + (-21034118311413364684800 : ℝ) * t ^ 29 + (9015717856807133839360 : ℝ) * t ^ 30 + (7201101750758466969600 : ℝ) * t ^ 31 + (-2349349521483571396608 : ℝ) * t ^ 32 + (-1475572920199276953600 : ℝ) * t ^ 33 + (287151893571491594240 : ℝ) * t ^ 34 + (133421833557953740800 : ℝ) * t ^ 35 + (288236973221478400 : ℝ) * t ^ 36

private noncomputable def Gtx_7 (t : ℝ) : ℝ :=
  (703515643084800 : ℝ) + (-946814802984960 : ℝ) * t + (-26755579301068800 : ℝ) * t ^ 2 + (35452866063761408 : ℝ) * t ^ 3 + (473850762913382400 : ℝ) * t ^ 4 + (-615262324910981120 : ℝ) * t ^ 5 + (-5194601492329267200 : ℝ) * t ^ 6 + (6571376214722740224 : ℝ) * t ^ 7 + (39514588469998387200 : ℝ) * t ^ 8 + (-48367305936697556992 : ℝ) * t ^ 9 + (-221554562390242099200 : ℝ) * t ^ 10 + (260252481669881135104 : ℝ) * t ^ 11 + (949072989124244275200 : ℝ) * t ^ 12 + (-1059480934285751353344 : ℝ) * t ^ 13 + (-3175748808300704563200 : ℝ) * t ^ 14 + (3330321541974377627648 : ℝ) * t ^ 15 + (8411644536894731059200 : ℝ) * t ^ 16 + (-8172825747574963306496 : ℝ) * t ^ 17 + (-17752685007102577459200 : ℝ) * t ^ 18 + (15718085937568076070912 : ℝ) * t ^ 19 + (29877742218880462233600 : ℝ) * t ^ 20 + (-23622230788797131964416 : ℝ) * t ^ 21 + (-39899661183968490777600 : ℝ) * t ^ 22 + (27462094424090976481280 : ℝ) * t ^ 23 + (41787226228677282662400 : ℝ) * t ^ 24 + (-24220549673973897744384 : ℝ) * t ^ 25 + (-33618604057888229452800 : ℝ) * t ^ 26 + (15672256214330156449792 : ℝ) * t ^ 27 + (20072114254574445772800 : ℝ) * t ^ 28 + (-7018819618799804612608 : ℝ) * t ^ 29 + (-8382906643369453977600 : ℝ) * t ^ 30 + (1944172458438643679232 : ℝ) * t ^ 31 + (2186948463367952793600 : ℝ) * t ^ 32 + (-250809213364946862080 : ℝ) * t ^ 33 + (-268359824315429683200 : ℝ) * t ^ 34 + (-94283122081792000 : ℝ) * t ^ 35

private noncomputable def Gtx_8 (t : ℝ) : ℝ :=
  (378816115507200 : ℝ) + (879394553856000 : ℝ) * t + (-14016196273766400 : ℝ) * t ^ 2 + (-32933326041907200 : ℝ) * t ^ 3 + (240216769246003200 : ℝ) * t ^ 4 + (571595467574476800 : ℝ) * t ^ 5 + (-2532409408172851200 : ℝ) * t ^ 6 + (-6105336843652300800 : ℝ) * t ^ 7 + (18389082299380531200 : ℝ) * t ^ 8 + (44937978196053196800 : ℝ) * t ^ 9 + (-97579281667011379200 : ℝ) * t ^ 10 + (-241797540912876748800 : ℝ) * t ^ 11 + (391618664483468083200 : ℝ) * t ^ 12 + (984320391609896140800 : ℝ) * t ^ 13 + (-1213235907081220915200 : ℝ) * t ^ 14 + (-3093932278304656588800 : ℝ) * t ^ 15 + (2933786226978599731200 : ℝ) * t ^ 16 + (7592362779617692876800 : ℝ) * t ^ 17 + (-5558865122589946675200 : ℝ) * t ^ 18 + (-14601138829464976588800 : ℝ) * t ^ 19 + (8229876815259987148800 : ℝ) * t ^ 20 + (21942996531374203084800 : ℝ) * t ^ 21 + (-9424719663097968230400 : ℝ) * t ^ 22 + (-25509726165936076646400 : ℝ) * t ^ 23 + (8187994590383149516800 : ℝ) * t ^ 24 + (22499213502394514995200 : ℝ) * t ^ 25 + (-5219181639705238732800 : ℝ) * t ^ 26 + (-14559591835296416563200 : ℝ) * t ^ 27 + (2302838687989673164800 : ℝ) * t ^ 28 + (6521696045273338675200 : ℝ) * t ^ 29 + (-628622100417282048000 : ℝ) * t ^ 30 + (-1807259381830464307200 : ℝ) * t ^ 31 + (80006449144017715200 : ℝ) * t ^ 32 + (233488208726419046400 : ℝ) * t ^ 33

private noncomputable def Gtx_9 (t : ℝ) : ℝ :=
  (-351757821542400 : ℝ) + (13015039397068800 : ℝ) * t ^ 2 + (-223058428585574400 : ℝ) * t ^ 4 + (2351523021874790400 : ℝ) * t ^ 6 + (-17075576420853350400 : ℝ) * t ^ 8 + (90609332976510566400 : ℝ) * t ^ 10 + (-363645902734648934400 : ℝ) * t ^ 12 + (1126576199432562278400 : ℝ) * t ^ 14 + (-2724230067908699750400 : ℝ) * t ^ 16 + (5161803328119236198400 : ℝ) * t ^ 18 + (-7642028471312845209600 : ℝ) * t ^ 20 + (8751525401448113356800 : ℝ) * t ^ 22 + (-7603137833927210265600 : ℝ) * t ^ 24 + (4846382951154864537600 : ℝ) * t ^ 26 + (-2138350210276125081600 : ℝ) * t ^ 28 + (583720521816047616000 : ℝ) * t ^ 30 + (-74291702776587878400 : ℝ) * t ^ 32

/-- The polynomial of the proof of Lemma 4.5(i), degree 40 in `τ` and 9 in `x`. -/
private noncomputable def Gtx (t x : ℝ) : ℝ :=
  Gtx_0 t + Gtx_1 t * x + Gtx_2 t * x ^ 2 + Gtx_3 t * x ^ 3 + Gtx_4 t * x ^ 4 + Gtx_5 t * x ^ 5 + Gtx_6 t * x ^ 6 + Gtx_7 t * x ^ 7 + Gtx_8 t * x ^ 8 + Gtx_9 t * x ^ 9

/-- On `|c| = 1`: `Re cᵐ = T_m(x)`, `Im cᵐ = y U_{m-1}(x)` for `m = 2, …, 7`. -/
private lemma cheb7 (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    (c ^ 2).re = 2*c.re^2 - 1 ∧ (c ^ 2).im = c.im * (2*c.re) ∧
    (c ^ 3).re = 4*c.re^3 - 3*c.re ∧ (c ^ 3).im = c.im * (4*c.re^2 - 1) ∧
    (c ^ 4).re = 8*c.re^4 - 8*c.re^2 + 1 ∧ (c ^ 4).im = c.im * (8*c.re^3 - 4*c.re) ∧
    (c ^ 5).re = 16*c.re^5 - 20*c.re^3 + 5*c.re ∧ (c ^ 5).im = c.im * (16*c.re^4 - 12*c.re^2 + 1) ∧
    (c ^ 6).re = 32*c.re^6 - 48*c.re^4 + 18*c.re^2 - 1 ∧ (c ^ 6).im = c.im * (32*c.re^5 - 32*c.re^3 + 6*c.re) ∧
    (c ^ 7).re = 64*c.re^7 - 112*c.re^5 + 56*c.re^3 - 7*c.re ∧ (c ^ 7).im = c.im * (64*c.re^6 - 80*c.re^4 + 24*c.re^2 - 1) := by
  have e1 : (c ^ 1).re = c.re ∧ (c ^ 1).im = c.im * 1 := by simp
  have e2 := cpow_step c h (m := 1) (n := 2) (by norm_num) e1.1 e1.2
    (A' := 2*c.re^2 - 1) (B' := 2*c.re) (by ring) (by ring)
  have e3 := cpow_step c h (m := 2) (n := 3) (by norm_num) e2.1 e2.2
    (A' := 4*c.re^3 - 3*c.re) (B' := 4*c.re^2 - 1) (by ring) (by ring)
  have e4 := cpow_step c h (m := 3) (n := 4) (by norm_num) e3.1 e3.2
    (A' := 8*c.re^4 - 8*c.re^2 + 1) (B' := 8*c.re^3 - 4*c.re) (by ring) (by ring)
  have e5 := cpow_step c h (m := 4) (n := 5) (by norm_num) e4.1 e4.2
    (A' := 16*c.re^5 - 20*c.re^3 + 5*c.re) (B' := 16*c.re^4 - 12*c.re^2 + 1) (by ring) (by ring)
  have e6 := cpow_step c h (m := 5) (n := 6) (by norm_num) e5.1 e5.2
    (A' := 32*c.re^6 - 48*c.re^4 + 18*c.re^2 - 1) (B' := 32*c.re^5 - 32*c.re^3 + 6*c.re) (by ring) (by ring)
  have e7 := cpow_step c h (m := 6) (n := 7) (by norm_num) e6.1 e6.2
    (A' := 64*c.re^7 - 112*c.re^5 + 56*c.re^3 - 7*c.re) (B' := 64*c.re^6 - 80*c.re^4 + 24*c.re^2 - 1) (by ring) (by ring)
  exact ⟨e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2⟩

set_option maxHeartbeats 4000000 in
private lemma Gtx_cert (t x : ℝ) :
    Gtx t x =
      (R0 (10 - 20 * t) + (20 * t - 9) * H0 (10 - 20 * t)) * (1 + x) ^ 0 * (1 - x) ^ 9
      + (R1 (10 - 20 * t) + (20 * t - 9) * H1 (10 - 20 * t)) * (1 + x) ^ 1 * (1 - x) ^ 8
      + (R2 (10 - 20 * t) + (20 * t - 9) * H2 (10 - 20 * t)) * (1 + x) ^ 2 * (1 - x) ^ 7
      + (R3 (10 - 20 * t) + (20 * t - 9) * H3 (10 - 20 * t)) * (1 + x) ^ 3 * (1 - x) ^ 6
      + (R4 (10 - 20 * t) + (20 * t - 9) * H4 (10 - 20 * t)) * (1 + x) ^ 4 * (1 - x) ^ 5
      + (R5 (10 - 20 * t) + (20 * t - 9) * H5 (10 - 20 * t)) * (1 + x) ^ 5 * (1 - x) ^ 4
      + (R6 (10 - 20 * t) + (20 * t - 9) * H6 (10 - 20 * t)) * (1 + x) ^ 6 * (1 - x) ^ 3
      + (R7 (10 - 20 * t) + (20 * t - 9) * H7 (10 - 20 * t)) * (1 + x) ^ 7 * (1 - x) ^ 2
      + (R8 (10 - 20 * t) + (20 * t - 9) * H8 (10 - 20 * t)) * (1 + x) ^ 8 * (1 - x) ^ 1
      + (R9 (10 - 20 * t) + (20 * t - 9) * H9 (10 - 20 * t)) * (1 + x) ^ 9 * (1 - x) ^ 0 := by
  unfold Gtx Gtx_0 Gtx_1 Gtx_2 Gtx_3 Gtx_4 Gtx_5 Gtx_6 Gtx_7 Gtx_8 Gtx_9 R0 H0 R1 H1 R2 H2 R3 H3 R4 H4 R5 H5 R6 H6 R7 H7 R8 H8 R9 H9
  ring

private lemma Nc2_re (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Nc2 t c).re = NR2 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc2, NR2, add_re, re_ofReal_mul, ofReal_re, h2r, h3r, h4r]
  try ring

private lemma Nc2_im (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    (Nc2 t c).im = c.im * NI2 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc2, NI2, add_im, im_ofReal_mul, ofReal_im, h2i, h3i, h4i]
  ring

private lemma Nc2_sq (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    ‖Nc2 t c‖ ^ 2 = NR2 t c.re ^ 2 + (1 - c.re ^ 2) * NI2 t c.re ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, Nc2_re t c h, Nc2_im t c h]
  linear_combination (NI2 t c.re ^ 2) * h

set_option maxHeartbeats 4000000 in
private lemma E2_eq (t x : ℝ) : NR2 t x ^ 2 + (1 - x ^ 2) * NI2 t x ^ 2 = E2 t x := by
  unfold NR2 NI2 E2 E2_0 E2_1 E2_2 E2_3 E2_4 n2_0 n2_1 n2_2 n2_3 n2_4
  ring

private lemma Nc3_re (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Nc3 t c).re = NR3 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc3, NR3, add_re, re_ofReal_mul, ofReal_re, h2r, h3r, h4r, h5r, h6r, h7r]
  try ring

private lemma Nc3_im (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    (Nc3 t c).im = c.im * NI3 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc3, NI3, add_im, im_ofReal_mul, ofReal_im, h2i, h3i, h4i, h5i, h6i, h7i]
  ring

private lemma Nc3_sq (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    ‖Nc3 t c‖ ^ 2 = NR3 t c.re ^ 2 + (1 - c.re ^ 2) * NI3 t c.re ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, Nc3_re t c h, Nc3_im t c h]
  linear_combination (NI3 t c.re ^ 2) * h

set_option maxHeartbeats 4000000 in
private lemma E3_eq (t x : ℝ) : NR3 t x ^ 2 + (1 - x ^ 2) * NI3 t x ^ 2 = E3 t x := by
  unfold NR3 NI3 E3 E3_0 E3_1 E3_2 E3_3 E3_4 E3_5 E3_6 E3_7 n3_0 n3_1 n3_2 n3_3 n3_4 n3_5 n3_6 n3_7
  ring

private lemma Nc4_re (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Nc4 t c).re = NR4 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc4, NR4, add_re, re_ofReal_mul, ofReal_re, h2r, h3r, h4r, h5r, h6r, h7r]
  try ring

private lemma Nc4_im (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    (Nc4 t c).im = c.im * NI4 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc4, NI4, add_im, im_ofReal_mul, ofReal_im, h2i, h3i, h4i, h5i, h6i, h7i]
  ring

private lemma Nc4_sq (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    ‖Nc4 t c‖ ^ 2 = NR4 t c.re ^ 2 + (1 - c.re ^ 2) * NI4 t c.re ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, Nc4_re t c h, Nc4_im t c h]
  linear_combination (NI4 t c.re ^ 2) * h

set_option maxHeartbeats 4000000 in
private lemma E4_eq (t x : ℝ) : NR4 t x ^ 2 + (1 - x ^ 2) * NI4 t x ^ 2 = E4 t x := by
  unfold NR4 NI4 E4 E4_0 E4_1 E4_2 E4_3 E4_4 E4_5 E4_6 E4_7 n4_0 n4_1 n4_2 n4_3 n4_4 n4_5 n4_6 n4_7
  ring

private lemma Nc5_re (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) : (Nc5 t c).re = NR5 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc5, NR5, add_re, re_ofReal_mul, ofReal_re, h2r, h3r, h4r, h5r, h6r, h7r]
  try ring

private lemma Nc5_im (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    (Nc5 t c).im = c.im * NI5 t c.re := by
  obtain ⟨h2r, h2i, h3r, h3i, h4r, h4i, h5r, h5i, h6r, h6i, h7r, h7i⟩ := cheb7 c h
  simp only [Nc5, NI5, add_im, im_ofReal_mul, ofReal_im, h2i, h3i, h4i, h5i, h6i, h7i]
  ring

private lemma Nc5_sq (t : ℝ) (c : ℂ) (h : c.re ^ 2 + c.im ^ 2 = 1) :
    ‖Nc5 t c‖ ^ 2 = NR5 t c.re ^ 2 + (1 - c.re ^ 2) * NI5 t c.re ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, Nc5_re t c h, Nc5_im t c h]
  linear_combination (NI5 t c.re ^ 2) * h

set_option maxHeartbeats 4000000 in
private lemma E5_eq (t x : ℝ) : NR5 t x ^ 2 + (1 - x ^ 2) * NI5 t x ^ 2 = E5 t x := by
  unfold NR5 NI5 E5 E5_0 E5_1 E5_2 E5_3 E5_4 E5_5 E5_6 E5_7 n5_0 n5_1 n5_2 n5_3 n5_4 n5_5 n5_6 n5_7
  ring

private lemma Bp_eq (t x : ℝ) : QRf t x ^ 2 + (1 - x ^ 2) * QIf t x ^ 2 = Bp t x := by
  unfold QRf QIf Bp Bp_0 Bp_1 Bp_2 Bp_3 Bp_4 q0 q1 q3 q4
  ring

set_option maxHeartbeats 4000000 in
/-- The polynomial of Lemma 4.5(i) is `Gtx`. -/
private lemma Gtx_eq (t x : ℝ) :
    315 * ((20 + 260 * (1 - x)) * 65536 * Kt t ^ 8 * Bp t x ^ 2) -
      (105 * E2 t x * Kt t ^ 8 + 63 * E3 t x * Kt t ^ 4 + 45 * E4 t x * Kt t ^ 2 + 35 * E5 t x) = Gtx t x := by
  unfold Kt Bp E2 E3 E4 E5 Gtx E2_0 E2_1 E2_2 E2_3 E2_4 E3_0 E3_1 E3_2 E3_3 E3_4 E3_5 E3_6 E3_7 E4_0 E4_1 E4_2 E4_3 E4_4 E4_5 E4_6 E4_7 E5_0 E5_1 E5_2 E5_3 E5_4 E5_5 E5_6 E5_7 Bp_0 Bp_1 Bp_2 Bp_3 Bp_4 Gtx_0 Gtx_1 Gtx_2 Gtx_3 Gtx_4 Gtx_5 Gtx_6 Gtx_7 Gtx_8 Gtx_9
  ring

private lemma R0_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R0 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R0
  positivity

private lemma H0_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H0 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H0
  positivity

private lemma R1_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R1 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R1
  positivity

private lemma H1_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H1 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H1
  positivity

private lemma R2_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R2 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R2
  positivity

private lemma H2_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H2 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H2
  positivity

private lemma R3_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R3 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R3
  positivity

private lemma H3_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H3 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H3
  positivity

private lemma R4_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R4 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R4
  positivity

private lemma H4_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H4 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H4
  positivity

private lemma R5_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R5 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R5
  positivity

private lemma H5_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H5 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H5
  positivity

private lemma R6_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R6 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R6
  positivity

private lemma H6_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H6 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H6
  positivity

private lemma R7_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R7 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R7
  positivity

private lemma H7_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H7 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H7
  positivity

private lemma R8_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R8 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R8
  positivity

private lemma H8_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H8 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H8
  positivity

private lemma R9_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ R9 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold R9
  positivity

private lemma H9_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ H9 b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ^ 2 := ⟨Real.sqrt b, (Real.sq_sqrt hb).symm⟩
  unfold H9
  positivity

/-- `Gtx ≥ 0` on `[9/20, 1/2] × [-1, 1]` (Bernstein form in `x`, nonnegative coefficients in `β = 10 - 20τ`). -/
private lemma Gtx_nonneg (t x : ℝ) (h1 : 9 / 20 ≤ t) (h2 : t ≤ 1 / 2) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    0 ≤ Gtx t x := by
  have hb : 0 ≤ 10 - 20 * t := by linarith
  have he : 0 ≤ 20 * t - 9 := by linarith
  have hp : 0 ≤ 1 + x := by linarith
  have hq : 0 ≤ 1 - x := by linarith
  have hR0 := R0_nonneg (10 - 20 * t) hb
  have hH0 := H0_nonneg (10 - 20 * t) hb
  have hR1 := R1_nonneg (10 - 20 * t) hb
  have hH1 := H1_nonneg (10 - 20 * t) hb
  have hR2 := R2_nonneg (10 - 20 * t) hb
  have hH2 := H2_nonneg (10 - 20 * t) hb
  have hR3 := R3_nonneg (10 - 20 * t) hb
  have hH3 := H3_nonneg (10 - 20 * t) hb
  have hR4 := R4_nonneg (10 - 20 * t) hb
  have hH4 := H4_nonneg (10 - 20 * t) hb
  have hR5 := R5_nonneg (10 - 20 * t) hb
  have hH5 := H5_nonneg (10 - 20 * t) hb
  have hR6 := R6_nonneg (10 - 20 * t) hb
  have hH6 := H6_nonneg (10 - 20 * t) hb
  have hR7 := R7_nonneg (10 - 20 * t) hb
  have hH7 := H7_nonneg (10 - 20 * t) hb
  have hR8 := R8_nonneg (10 - 20 * t) hb
  have hH8 := H8_nonneg (10 - 20 * t) hb
  have hR9 := R9_nonneg (10 - 20 * t) hb
  have hH9 := H9_nonneg (10 - 20 * t) hb
  rw [Gtx_cert]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (add_nonneg (hR0) (mul_nonneg he (hH0))) (pow_nonneg hp 0)) (pow_nonneg hq 9))
      (mul_nonneg (mul_nonneg (add_nonneg (hR1) (mul_nonneg he (hH1))) (pow_nonneg hp 1)) (pow_nonneg hq 8)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR2) (mul_nonneg he (hH2))) (pow_nonneg hp 2)) (pow_nonneg hq 7)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR3) (mul_nonneg he (hH3))) (pow_nonneg hp 3)) (pow_nonneg hq 6)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR4) (mul_nonneg he (hH4))) (pow_nonneg hp 4)) (pow_nonneg hq 5)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR5) (mul_nonneg he (hH5))) (pow_nonneg hp 5)) (pow_nonneg hq 4)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR6) (mul_nonneg he (hH6))) (pow_nonneg hp 6)) (pow_nonneg hq 3)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR7) (mul_nonneg he (hH7))) (pow_nonneg hp 7)) (pow_nonneg hq 2)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR8) (mul_nonneg he (hH8))) (pow_nonneg hp 8)) (pow_nonneg hq 1)))
      (mul_nonneg (mul_nonneg (add_nonneg (hR9) (mul_nonneg he (hH9))) (pow_nonneg hp 9)) (pow_nonneg hq 0))

/-- The real form of (sec4:finite) on the circle. -/
private lemma real_ineq (t x : ℝ) (h1 : 9 / 20 ≤ t) (h2 : t ≤ 1 / 2) (hx1 : -1 ≤ x) (hx2 : x ≤ 1)
    (hB : 0 < Bp t x) :
    E2 t x / (256 ^ 2 * Bp t x ^ 2) / 3 + E3 t x / ((256 * Kt t ^ 2) ^ 2 * Bp t x ^ 2) / 5 +
        E4 t x / ((256 * Kt t ^ 3) ^ 2 * Bp t x ^ 2) / 7 + E5 t x / ((256 * Kt t ^ 4) ^ 2 * Bp t x ^ 2) / 9 ≤
      20 + 130 * (2 * (1 - x)) := by
  have hK : Kt t ≠ 0 := by unfold Kt; nlinarith
  have hG := Gtx_nonneg t x h1 h2 hx1 hx2
  rw [← Gtx_eq] at hG
  have hD : 0 < 315 * 65536 * Kt t ^ 8 * Bp t x ^ 2 := by positivity
  have hL : E2 t x / (256 ^ 2 * Bp t x ^ 2) / 3 + E3 t x / ((256 * Kt t ^ 2) ^ 2 * Bp t x ^ 2) / 5 +
        E4 t x / ((256 * Kt t ^ 3) ^ 2 * Bp t x ^ 2) / 7 + E5 t x / ((256 * Kt t ^ 4) ^ 2 * Bp t x ^ 2) / 9 =
      (105 * E2 t x * Kt t ^ 8 + 63 * E3 t x * Kt t ^ 4 + 45 * E4 t x * Kt t ^ 2 + 35 * E5 t x) /
        (315 * 65536 * Kt t ^ 8 * Bp t x ^ 2) := by
    field_simp
    ring
  rw [hL, div_le_iff₀ hD]
  linarith

private lemma TJ_sq (τ : ℝ) (c : ℂ) (j : ℕ) (N : ℂ) (k : ℝ) (hT : TJ τ c j = N / ((k : ℂ) * Qc τ c ^ 2)) :
    ‖TJ τ c j‖ ^ 2 = ‖N‖ ^ 2 / (k ^ 2 * (‖Qc τ c‖ ^ 2) ^ 2) := by
  rw [hT, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_pow, mul_pow, sq_abs]

/-- Lemma 4.5(i) on the circle, given the closed forms of `T_2, …, T_5`. -/
private lemma lem45_circle_of_closed (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ = 1)
    (hT2 : TJ τ c 2 = Nc2 τ c / (((256 : ℝ) : ℂ) * Qc τ c ^ 2))
    (hT3 : TJ τ c 3 = Nc3 τ c / (((256 * Kt τ ^ 2 : ℝ) : ℂ) * Qc τ c ^ 2))
    (hT4 : TJ τ c 4 = Nc4 τ c / (((256 * Kt τ ^ 3 : ℝ) : ℂ) * Qc τ c ^ 2))
    (hT5 : TJ τ c 5 = Nc5 τ c / (((256 * Kt τ ^ 4 : ℝ) : ℂ) * Qc τ c ^ 2)) :
    ∑ j ∈ Finset.Icc 2 5, ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) ≤ 20 + 130 * edef c := by
  have hxy : c.re ^ 2 + c.im ^ 2 = 1 := by
    have h := Complex.sq_norm c
    rw [hc, Complex.normSq_apply] at h
    linear_combination -h
  have hx1 : -1 ≤ c.re := by nlinarith
  have hx2 : c.re ≤ 1 := by nlinarith
  have hQ : ‖Qc τ c‖ ^ 2 = Bp τ c.re := by
    rw [Complex.sq_norm, normSq_apply, Qc_re τ c hxy, Qc_im τ c hxy, ← Bp_eq]
    linear_combination (QIf τ c.re ^ 2) * hxy
  have hB : 0 < Bp τ c.re := by
    rw [← hQ]
    exact pow_pos (norm_pos_iff.mpr (Qc_ne τ h1 h2.le c hc.le)) 2
  have e2 : ‖TJ τ c 2‖ ^ 2 = E2 τ c.re / (256 ^ 2 * Bp τ c.re ^ 2) := by
    rw [TJ_sq τ c 2 _ _ hT2, Nc2_sq τ c hxy, E2_eq, hQ]
  have e3 : ‖TJ τ c 3‖ ^ 2 = E3 τ c.re / ((256 * Kt τ ^ 2) ^ 2 * Bp τ c.re ^ 2) := by
    rw [TJ_sq τ c 3 _ _ hT3, Nc3_sq τ c hxy, E3_eq, hQ]
  have e4 : ‖TJ τ c 4‖ ^ 2 = E4 τ c.re / ((256 * Kt τ ^ 3) ^ 2 * Bp τ c.re ^ 2) := by
    rw [TJ_sq τ c 4 _ _ hT4, Nc4_sq τ c hxy, E4_eq, hQ]
  have e5 : ‖TJ τ c 5‖ ^ 2 = E5 τ c.re / ((256 * Kt τ ^ 4) ^ 2 * Bp τ c.re ^ 2) := by
    rw [TJ_sq τ c 5 _ _ hT5, Nc5_sq τ c hxy, E5_eq, hQ]
  have hS : Finset.Icc 2 5 = ({2, 3, 4, 5} : Finset ℕ) := by decide
  have hsum : ∑ j ∈ Finset.Icc 2 5, ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) =
      ‖TJ τ c 2‖ ^ 2 / 3 + ‖TJ τ c 3‖ ^ 2 / 5 + ‖TJ τ c 4‖ ^ 2 / 7 + ‖TJ τ c 5‖ ^ 2 / 9 := by
    rw [hS, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num
    try ring
  rw [hsum, e2, e3, e4, e5]
  have key := real_ineq τ c.re h1 h2.le hx1 hx2 hB
  unfold edef
  linarith

/-! ### Lemma 4.5(i): the closed forms `T_j = N_j/(256 K^{k_j} 𝒬²)` -/

/-- The derivative of the `c`-free factor `-2ζ^{j+1}(1 + βζ)^{2-j}/v^j` of `Π_j`. -/
private lemma deriv_aJ (τ : ℝ) (j : ℕ) (ζ : ℂ) (hb : 1 + (βτ τ : ℂ) * ζ ≠ 0) :
    deriv (aJ τ j) ζ = -2 * (((j : ℂ) + 1) * ζ ^ j * (1 + (βτ τ : ℂ) * ζ) ^ ((2 : ℤ) - j) +
      ζ ^ (j + 1) * ((2 - (j : ℂ)) * (1 + (βτ τ : ℂ) * ζ) ^ ((2 : ℤ) - j - 1) * (βτ τ : ℂ))) /
        (vτ τ : ℂ) ^ j := by
  have h1 : HasDerivAt (fun w : ℂ => w ^ (j + 1)) (((j : ℂ) + 1) * ζ ^ j) ζ := by
    simpa using hasDerivAt_pow (j + 1) ζ
  have h2 : HasDerivAt (fun w : ℂ => 1 + (βτ τ : ℂ) * w) (βτ τ : ℂ) ζ := by
    simpa using ((hasDerivAt_id ζ).const_mul (βτ τ : ℂ)).const_add 1
  have h3 := (hasDerivAt_zpow ((2 : ℤ) - j) (1 + (βτ τ : ℂ) * ζ) (Or.inl hb)).comp ζ h2
  have h4 := ((h1.mul h3).const_mul (-2 : ℂ)).div_const ((vτ τ : ℂ) ^ j)
  have hfun : aJ τ j = fun w => -2 * (w ^ (j + 1) * (1 + (βτ τ : ℂ) * w) ^ ((2 : ℤ) - j)) / (vτ τ : ℂ) ^ j := by
    funext w
    unfold aJ
    ring
  rw [hfun]
  refine h4.deriv.trans ?_
  simp only [Function.comp_apply]
  push_cast
  ring

/-- `𝒫` and `𝒬` with a complex first variable. -/
private noncomputable def PcC (t c : ℂ) : ℂ :=
  (2 - 11 / 2 * t ^ 2 + 7 / 2 * t ^ 4) + (-3 * t + 6 * t ^ 3 - 3 * t ^ 5) * c +
    (-3 / 2 + 15 / 2 * t ^ 2 - 6 * t ^ 4) * c ^ 2 + (t - 5 * t ^ 3 + 4 * t ^ 5) * c ^ 3

private noncomputable def QcC (t c : ℂ) : ℂ :=
  (1 - 7 / 2 * t ^ 2 + 49 / 16 * t ^ 4) + (-1 / 2 * t + 23 / 8 * t ^ 3 - 7 / 2 * t ^ 5) * c +
    (1 / 8 * t - t ^ 3 + 2 * t ^ 5) * c ^ 3 + (-1 / 16 + 1 / 2 * t ^ 2 - t ^ 4) * c ^ 4

/-- `4v²(1 - ν(ν + 2β)y²)` and `4v²(1 + ν²y²)` as polynomials. -/
private noncomputable def F1p (t c : ℂ) : ℂ := 4 * c ^ 2 * t ^ 2 - c ^ 2 - 7 * t ^ 2 + 4

private noncomputable def F2p (t c : ℂ) : ℂ := -4 * c ^ 2 * t ^ 2 + c ^ 2 + 8 * c * t ^ 3 - 2 * c * t - 7 * t ^ 2 + 4

private lemma Pc_C (τ : ℝ) (c : ℂ) : Pc τ c = PcC τ c := by
  unfold Pc PcC p0 p1 p2 p3
  push_cast
  ring

private lemma Qc_C (τ : ℝ) (c : ℂ) : Qc τ c = QcC τ c := by
  unfold Qc QcC q0 q1 q3 q4
  push_cast
  ring

private lemma QcC_F (t c : ℂ) : QcC t c = F1p t c * F2p t c / 16 := by
  unfold QcC F1p F2p
  ring

private noncomputable def Ncp2 (t c : ℂ) : ℂ :=
  (4096 : ℂ) * t ^ 9 * c ^ 3 + (1024 : ℂ) * t ^ 9 * c + (-4096 : ℂ) * t ^ 8 * c ^ 4 + (-12288 : ℂ) * t ^ 8 * c ^ 2 + (-1792 : ℂ) * t ^ 8 + (5120 : ℂ) * t ^ 7 * c ^ 3 + (9728 : ℂ) * t ^ 7 * c + (7168 : ℂ) * t ^ 6 * c ^ 4 + (7680 : ℂ) * t ^ 6 * c ^ 2 + (2368 : ℂ) * t ^ 6 + (-16896 : ℂ) * t ^ 5 * c ^ 3 + (-14592 : ℂ) * t ^ 5 * c + (-3840 : ℂ) * t ^ 4 * c ^ 4 + (12672 : ℂ) * t ^ 4 * c ^ 2 + (-2112 : ℂ) * t ^ 4 + (8960 : ℂ) * t ^ 3 * c ^ 3 + (2816 : ℂ) * t ^ 3 * c + (832 : ℂ) * t ^ 2 * c ^ 4 + (-9600 : ℂ) * t ^ 2 * c ^ 2 + (2560 : ℂ) * t ^ 2 + (-1280 : ℂ) * t * c ^ 3 + (1024 : ℂ) * t * c + (-64 : ℂ) * c ^ 4 + (1536 : ℂ) * c ^ 2 + (-1024 : ℂ)

private noncomputable def Ncp3 (t c : ℂ) : ℂ :=
  (196608 : ℂ) * t ^ 14 * c ^ 3 + (114688 : ℂ) * t ^ 14 * c + (-163840 : ℂ) * t ^ 13 * c ^ 4 + (-774144 : ℂ) * t ^ 13 * c ^ 2 + (-150528 : ℂ) * t ^ 13 + (-49152 : ℂ) * t ^ 12 * c ^ 5 + (147456 : ℂ) * t ^ 12 * c ^ 3 + (343040 : ℂ) * t ^ 12 * c + (73728 : ℂ) * t ^ 11 * c ^ 6 + (333824 : ℂ) * t ^ 11 * c ^ 4 + (1528320 : ℂ) * t ^ 11 * c ^ 2 + (454272 : ℂ) * t ^ 11 + (-16384 : ℂ) * t ^ 10 * c ^ 7 + (-12288 : ℂ) * t ^ 10 * c ^ 5 + (-918528 : ℂ) * t ^ 10 * c ^ 3 + (-1428736 : ℂ) * t ^ 10 * c + (-129024 : ℂ) * t ^ 9 * c ^ 6 + (-80896 : ℂ) * t ^ 9 * c ^ 4 + (-1069440 : ℂ) * t ^ 9 * c ^ 2 + (-653952 : ℂ) * t ^ 9 + (32768 : ℂ) * t ^ 8 * c ^ 7 + (125952 : ℂ) * t ^ 8 * c ^ 5 + (711168 : ℂ) * t ^ 8 * c ^ 3 + (1947264 : ℂ) * t ^ 8 * c + (69120 : ℂ) * t ^ 7 * c ^ 6 + (-204416 : ℂ) * t ^ 7 * c ^ 4 + (506496 : ℂ) * t ^ 7 * c ^ 2 + (565248 : ℂ) * t ^ 7 + (-22528 : ℂ) * t ^ 6 * c ^ 7 + (-82176 : ℂ) * t ^ 6 * c ^ 5 + (-73536 : ℂ) * t ^ 6 * c ^ 3 + (-1601408 : ℂ) * t ^ 6 * c + (-14976 : ℂ) * t ^ 5 * c ^ 6 + (148864 : ℂ) * t ^ 5 * c ^ 4 + (-277248 : ℂ) * t ^ 5 * c ^ 2 + (-264192 : ℂ) * t ^ 5 + (7168 : ℂ) * t ^ 4 * c ^ 7 + (19200 : ℂ) * t ^ 4 * c ^ 5 + (-92352 : ℂ) * t ^ 4 * c ^ 3 + (832000 : ℂ) * t ^ 4 * c + (1152 : ℂ) * t ^ 3 * c ^ 6 + (-36608 : ℂ) * t ^ 3 * c ^ 4 + (98304 : ℂ) * t ^ 3 * c ^ 2 + (49152 : ℂ) * t ^ 3 + (-1088 : ℂ) * t ^ 2 * c ^ 7 + (-1536 : ℂ) * t ^ 2 * c ^ 5 + (32256 : ℂ) * t ^ 2 * c ^ 3 + (-231424 : ℂ) * t ^ 2 * c + (3072 : ℂ) * t * c ^ 4 + (-12288 : ℂ) * t * c ^ 2 + (64 : ℂ) * c ^ 7 + (-3072 : ℂ) * c ^ 3 + (24576 : ℂ) * c

private noncomputable def Ncp4 (t c : ℂ) : ℂ :=
  (1310720 : ℂ) * t ^ 17 * c ^ 3 + (1376256 : ℂ) * t ^ 17 * c + (-786432 : ℂ) * t ^ 16 * c ^ 4 + (-6881280 : ℂ) * t ^ 16 * c ^ 2 + (-1605632 : ℂ) * t ^ 16 + (-786432 : ℂ) * t ^ 15 * c ^ 5 + (1474560 : ℂ) * t ^ 15 * c ^ 3 + (761856 : ℂ) * t ^ 15 * c + (720896 : ℂ) * t ^ 14 * c ^ 6 + (1622016 : ℂ) * t ^ 14 * c ^ 4 + (18812928 : ℂ) * t ^ 14 * c ^ 2 + (6300672 : ℂ) * t ^ 14 + (-147456 : ℂ) * t ^ 13 * c ^ 7 + (1462272 : ℂ) * t ^ 13 * c ^ 5 + (-10939392 : ℂ) * t ^ 13 * c ^ 3 + (-12136704 : ℂ) * t ^ 13 * c + (-1523712 : ℂ) * t ^ 12 * c ^ 6 + (-184320 : ℂ) * t ^ 12 * c ^ 4 + (-20524032 : ℂ) * t ^ 12 * c ^ 2 + (-11485952 : ℂ) * t ^ 12 + (294912 : ℂ) * t ^ 11 * c ^ 7 + (-1502208 : ℂ) * t ^ 11 * c ^ 5 + (16509440 : ℂ) * t ^ 11 * c ^ 3 + (24257856 : ℂ) * t ^ 11 * c + (1351680 : ℂ) * t ^ 10 * c ^ 6 + (-1330176 : ℂ) * t ^ 10 * c ^ 4 + (9594624 : ℂ) * t ^ 10 * c ^ 2 + (12549760 : ℂ) * t ^ 10 + (-202752 : ℂ) * t ^ 9 * c ^ 7 + (1413888 : ℂ) * t ^ 9 * c ^ 5 + (-13415616 : ℂ) * t ^ 9 * c ^ 3 + (-24346560 : ℂ) * t ^ 9 * c + (-821248 : ℂ) * t ^ 8 * c ^ 6 + (859392 : ℂ) * t ^ 8 * c ^ 4 + (1806528 : ℂ) * t ^ 8 * c ^ 2 + (-8938368 : ℂ) * t ^ 8 + (64512 : ℂ) * t ^ 7 * c ^ 7 + (-777792 : ℂ) * t ^ 7 * c ^ 5 + (6864576 : ℂ) * t ^ 7 * c ^ 3 + (13609344 : ℂ) * t ^ 7 * c + (354048 : ℂ) * t ^ 6 * c ^ 6 + (-195840 : ℂ) * t ^ 6 * c ^ 4 + (-4646592 : ℂ) * t ^ 6 * c ^ 2 + (4424704 : ℂ) * t ^ 6 + (-9792 : ℂ) * t ^ 5 * c ^ 7 + (218304 : ℂ) * t ^ 5 * c ^ 5 + (-2139136 : ℂ) * t ^ 5 * c ^ 3 + (-4056576 : ℂ) * t ^ 5 * c + (-94272 : ℂ) * t ^ 4 * c ^ 6 + (15360 : ℂ) * t ^ 4 * c ^ 4 + (2277120 : ℂ) * t ^ 4 * c ^ 2 + (-1556480 : ℂ) * t ^ 4 + (576 : ℂ) * t ^ 3 * c ^ 7 + (-29568 : ℂ) * t ^ 3 * c ^ 5 + (359424 : ℂ) * t ^ 3 * c ^ 3 + (559104 : ℂ) * t ^ 3 * c + (13376 : ℂ) * t ^ 2 * c ^ 6 + (-476160 : ℂ) * t ^ 2 * c ^ 2 + (344064 : ℂ) * t ^ 2 + (1536 : ℂ) * t * c ^ 5 + (-24576 : ℂ) * t * c ^ 3 + (-24576 : ℂ) * t * c + (-768 : ℂ) * c ^ 6 + (36864 : ℂ) * c ^ 2 + (-32768 : ℂ)

private noncomputable def Ncp5 (t c : ℂ) : ℂ :=
  (8388608 : ℂ) * t ^ 20 * c ^ 3 + (14680064 : ℂ) * t ^ 20 * c + (-2097152 : ℂ) * t ^ 19 * c ^ 4 + (-60555264 : ℂ) * t ^ 19 * c ^ 2 + (-16056320 : ℂ) * t ^ 19 + (-9437184 : ℂ) * t ^ 18 * c ^ 5 + (17039360 : ℂ) * t ^ 18 * c ^ 3 + (-14811136 : ℂ) * t ^ 18 * c + (6815744 : ℂ) * t ^ 17 * c ^ 6 + (-1179648 : ℂ) * t ^ 17 * c ^ 4 + (210763776 : ℂ) * t ^ 17 * c ^ 2 + (76152832 : ℂ) * t ^ 17 + (-1310720 : ℂ) * t ^ 16 * c ^ 7 + (28508160 : ℂ) * t ^ 16 * c ^ 5 + (-125681664 : ℂ) * t ^ 16 * c ^ 3 + (-83980288 : ℂ) * t ^ 16 * c + (-19972096 : ℂ) * t ^ 15 * c ^ 6 + (25030656 : ℂ) * t ^ 15 * c ^ 4 + (-309617664 : ℂ) * t ^ 15 * c ^ 2 + (-167076608 : ℂ) * t ^ 15 + (3604480 : ℂ) * t ^ 14 * c ^ 7 + (-42123264 : ℂ) * t ^ 14 * c ^ 5 + (234934272 : ℂ) * t ^ 14 * c ^ 3 + (259656704 : ℂ) * t ^ 14 * c + (26968064 : ℂ) * t ^ 13 * c ^ 6 + (-52036608 : ℂ) * t ^ 13 * c ^ 4 + (234481152 : ℂ) * t ^ 13 * c ^ 2 + (221377984 : ℂ) * t ^ 13 + (-4456448 : ℂ) * t ^ 12 * c ^ 7 + (38313984 : ℂ) * t ^ 12 * c ^ 5 + (-227791872 : ℂ) * t ^ 12 * c ^ 3 + (-353092864 : ℂ) * t ^ 12 * c + (-22054912 : ℂ) * t ^ 11 * c ^ 6 + (53860608 : ℂ) * t ^ 11 * c ^ 4 + (-80356416 : ℂ) * t ^ 11 * c ^ 2 + (-194842688 : ℂ) * t ^ 11 + (3432448 : ℂ) * t ^ 10 * c ^ 7 + (-21571584 : ℂ) * t ^ 10 * c ^ 5 + (126180096 : ℂ) * t ^ 10 * c ^ 3 + (287306048 : ℂ) * t ^ 10 * c + (11033600 : ℂ) * t ^ 9 * c ^ 6 + (-34511040 : ℂ) * t ^ 9 * c ^ 4 + (-2500800 : ℂ) * t ^ 9 * c ^ 2 + (118009216 : ℂ) * t ^ 9 + (-1725440 : ℂ) * t ^ 8 * c ^ 7 + (8193792 : ℂ) * t ^ 8 * c ^ 5 + (-37653504 : ℂ) * t ^ 8 * c ^ 3 + (-155642944 : ℂ) * t ^ 8 * c + (-3318976 : ℂ) * t ^ 7 * c ^ 6 + (13829952 : ℂ) * t ^ 7 * c ^ 4 + (10313472 : ℂ) * t ^ 7 * c ^ 2 + (-48398336 : ℂ) * t ^ 7 + (551680 : ℂ) * t ^ 6 * c ^ 7 + (-2291136 : ℂ) * t ^ 6 * c ^ 5 + (4143360 : ℂ) * t ^ 6 * c ^ 3 + (58760192 : ℂ) * t ^ 6 * c + (580544 : ℂ) * t ^ 5 * c ^ 6 + (-3298176 : ℂ) * t ^ 5 * c ^ 4 + (-2761728 : ℂ) * t ^ 5 * c ^ 2 + (12488704 : ℂ) * t ^ 5 + (-106880 : ℂ) * t ^ 4 * c ^ 7 + (460992 : ℂ) * t ^ 4 * c ^ 5 + (642048 : ℂ) * t ^ 4 * c ^ 3 + (-14989312 : ℂ) * t ^ 4 * c + (-54016 : ℂ) * t ^ 3 * c ^ 6 + (423936 : ℂ) * t ^ 3 * c ^ 4 + (233472 : ℂ) * t ^ 3 * c ^ 2 + (-1753088 : ℂ) * t ^ 3 + (11392 : ℂ) * t ^ 2 * c ^ 7 + (-56832 : ℂ) * t ^ 2 * c ^ 5 + (-217088 : ℂ) * t ^ 2 * c ^ 3 + (2260992 : ℂ) * t ^ 2 * c + (2048 : ℂ) * t * c ^ 6 + (-22528 : ℂ) * t * c ^ 4 + (98304 : ℂ) * t + (-512 : ℂ) * c ^ 7 + (3072 : ℂ) * c ^ 5 + (16384 : ℂ) * c ^ 3 + (-147456 : ℂ) * c

private lemma Nc2_C (τ : ℝ) (c : ℂ) : Nc2 τ c = Ncp2 τ c := by
  unfold Nc2 Ncp2 n2_0 n2_1 n2_2 n2_3 n2_4
  push_cast
  ring

private lemma Nc3_C (τ : ℝ) (c : ℂ) : Nc3 τ c = Ncp3 τ c := by
  unfold Nc3 Ncp3 n3_0 n3_1 n3_2 n3_3 n3_4 n3_5 n3_6 n3_7
  push_cast
  ring

private lemma Nc4_C (τ : ℝ) (c : ℂ) : Nc4 τ c = Ncp4 τ c := by
  unfold Nc4 Ncp4 n4_0 n4_1 n4_2 n4_3 n4_4 n4_5 n4_6 n4_7
  push_cast
  ring

private lemma Nc5_C (τ : ℝ) (c : ℂ) : Nc5 τ c = Ncp5 τ c := by
  unfold Nc5 Ncp5 n5_0 n5_1 n5_2 n5_3 n5_4 n5_5 n5_6 n5_7
  push_cast
  ring

/-- The numerator of `T_2` over the denominator `𝒬 (A₊A₋)^1 (L₊L₋)⁴`, with `A_± = v ± τξ`, `L_± = v ∓ (c - τ)ξ`. -/
private noncomputable def NUMP2 (t c z v P Q : ℂ) : ℂ :=
  Q * ((-t + z) * (-2 * v * z ^ 2) * (3 * (v + t * z) * (v - (c - t) * z) - 0 * t * z * (v - (c - t) * z) + 3 * (c - t) * z * (v + t * z)) * (v - t * z) ^ 1 * (v + (c - t) * z) ^ 4 +
    (t + z) * (-2 * v * (-z) ^ 2) * (3 * (v - t * z) * (v + (c - t) * z) + 0 * t * z * (v + (c - t) * z) - 3 * (c - t) * z * (v - t * z)) * (v + t * z) ^ 1 * (v - (c - t) * z) ^ 4) -
  (P - Q) * (-2 * v * z ^ 3 * (v + t * z) * (v - (c - t) * z) * (v - t * z) ^ 1 * (v + (c - t) * z) ^ 4 +
    2 * v * (-z) ^ 3 * (v - t * z) * (v + (c - t) * z) * (v + t * z) ^ 1 * (v - (c - t) * z) ^ 4)

/-- The numerator of `T_3` over the denominator `𝒬 (A₊A₋)^2 (L₊L₋)⁴`, with `A_± = v ± τξ`, `L_± = v ∓ (c - τ)ξ`. -/
private noncomputable def NUMP3 (t c z v P Q : ℂ) : ℂ :=
  Q * ((-t + z) * (-2 * v * z ^ 3) * (4 * (v + t * z) * (v - (c - t) * z) - 1 * t * z * (v - (c - t) * z) + 3 * (c - t) * z * (v + t * z)) * (v - t * z) ^ 2 * (v + (c - t) * z) ^ 4 +
    (t + z) * (-2 * v * (-z) ^ 3) * (4 * (v - t * z) * (v + (c - t) * z) + 1 * t * z * (v + (c - t) * z) - 3 * (c - t) * z * (v - t * z)) * (v + t * z) ^ 2 * (v - (c - t) * z) ^ 4) -
  (P - Q) * (-2 * v * z ^ 4 * (v + t * z) * (v - (c - t) * z) * (v - t * z) ^ 2 * (v + (c - t) * z) ^ 4 +
    2 * v * (-z) ^ 4 * (v - t * z) * (v + (c - t) * z) * (v + t * z) ^ 2 * (v - (c - t) * z) ^ 4)

/-- The numerator of `T_4` over the denominator `𝒬 (A₊A₋)^3 (L₊L₋)⁴`, with `A_± = v ± τξ`, `L_± = v ∓ (c - τ)ξ`. -/
private noncomputable def NUMP4 (t c z v P Q : ℂ) : ℂ :=
  Q * ((-t + z) * (-2 * v * z ^ 4) * (5 * (v + t * z) * (v - (c - t) * z) - 2 * t * z * (v - (c - t) * z) + 3 * (c - t) * z * (v + t * z)) * (v - t * z) ^ 3 * (v + (c - t) * z) ^ 4 +
    (t + z) * (-2 * v * (-z) ^ 4) * (5 * (v - t * z) * (v + (c - t) * z) + 2 * t * z * (v + (c - t) * z) - 3 * (c - t) * z * (v - t * z)) * (v + t * z) ^ 3 * (v - (c - t) * z) ^ 4) -
  (P - Q) * (-2 * v * z ^ 5 * (v + t * z) * (v - (c - t) * z) * (v - t * z) ^ 3 * (v + (c - t) * z) ^ 4 +
    2 * v * (-z) ^ 5 * (v - t * z) * (v + (c - t) * z) * (v + t * z) ^ 3 * (v - (c - t) * z) ^ 4)

/-- The numerator of `T_5` over the denominator `𝒬 (A₊A₋)^4 (L₊L₋)⁴`, with `A_± = v ± τξ`, `L_± = v ∓ (c - τ)ξ`. -/
private noncomputable def NUMP5 (t c z v P Q : ℂ) : ℂ :=
  Q * ((-t + z) * (-2 * v * z ^ 5) * (6 * (v + t * z) * (v - (c - t) * z) - 3 * t * z * (v - (c - t) * z) + 3 * (c - t) * z * (v + t * z)) * (v - t * z) ^ 4 * (v + (c - t) * z) ^ 4 +
    (t + z) * (-2 * v * (-z) ^ 5) * (6 * (v - t * z) * (v + (c - t) * z) + 3 * t * z * (v + (c - t) * z) - 3 * (c - t) * z * (v - t * z)) * (v + t * z) ^ 4 * (v - (c - t) * z) ^ 4) -
  (P - Q) * (-2 * v * z ^ 6 * (v + t * z) * (v - (c - t) * z) * (v - t * z) ^ 4 * (v + (c - t) * z) ^ 4 +
    2 * v * (-z) ^ 6 * (v - t * z) * (v + (c - t) * z) * (v + t * z) ^ 4 * (v - (c - t) * z) ^ 4)

/-- The numerator in the definition of `T_j`. -/
private noncomputable def NUMdef (τ : ℝ) (c : ℂ) (j : ℕ) : ℂ :=
  (-(τ : ℂ) + xiτ τ) * dPiJf τ c j (xiτ τ) + ((τ : ℂ) + xiτ τ) * dPiJf τ c j (-xiτ τ) -
    (Pc τ c / Qc τ c - 1) * (PiJ τ c j (xiτ τ) - PiJ τ c j (-xiτ τ))

private lemma TJf_eq (τ : ℝ) (c : ℂ) (j : ℕ) :
    TJf τ c j = (-1 / (ysq τ : ℂ)) * (NUMdef τ c j / (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ))) := rfl

private lemma hβC (τ : ℝ) : (βτ τ : ℂ) = (τ : ℂ) / (vτ τ : ℂ) := by
  simp only [βτ, Complex.ofReal_div]

private lemma hνC (τ : ℝ) (c : ℂ) : nuτ τ c = (c - τ) / (vτ τ : ℂ) := rfl

private lemma fA (t v ζ : ℂ) (hv : v ≠ 0) : 1 + t / v * ζ = (v + t * ζ) / v := by
  field_simp

private lemma fA' (t v ζ : ℂ) (hv : v ≠ 0) : 1 + t / v * -ζ = (v - t * ζ) / v := by
  field_simp
  ring

private lemma fL (t c v ζ : ℂ) (hv : v ≠ 0) : 1 - (c - t) / v * ζ = (v - (c - t) * ζ) / v := by
  field_simp

private lemma fL' (t c v ζ : ℂ) (hv : v ≠ 0) : 1 - (c - t) / v * -ζ = (v + (c - t) * ζ) / v := by
  field_simp
  ring

/-- The four factors `A_± = v(1 ± βξ)`, `L_± = v(1 ∓ νξ)` do not vanish. -/
private lemma factors_ne (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    (vτ τ : ℂ) + τ * xiτ τ ≠ 0 ∧ (vτ τ : ℂ) - τ * xiτ τ ≠ 0 ∧
      (vτ τ : ℂ) - (c - τ) * xiτ τ ≠ 0 ∧ (vτ τ : ℂ) + (c - τ) * xiτ τ ≠ 0 := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  have hb1 := one_add_beta_ne τ h1 h2 _ hxi
  have hb2 := one_add_beta_ne τ h1 h2 _ hxi'
  have hn1 := one_sub_nu_ne τ h1 h2 c hc _ hxi
  have hn2 := one_sub_nu_ne τ h1 h2 c hc _ hxi'
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  rw [hβC, fA (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0] at hb1
  rw [hβC, fA' (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0] at hb2
  rw [hνC, fL (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0] at hn1
  rw [hνC, fL' (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0] at hn2
  exact ⟨fun h => hb1 (by rw [h, zero_div]), fun h => hb2 (by rw [h, zero_div]),
    fun h => hn1 (by rw [h, zero_div]), fun h => hn2 (by rw [h, zero_div])⟩

/-- `Π̂(ξ) - Π̂(-ξ) = vξ(A₊L₋² + A₋L₊²)/(L₊L₋)²`. -/
private lemma DEN_eq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ) =
      (vτ τ : ℂ) * xiτ τ * (((vτ τ : ℂ) + τ * xiτ τ) * ((vτ τ : ℂ) + (c - τ) * xiτ τ) ^ 2 +
        ((vτ τ : ℂ) - τ * xiτ τ) * ((vτ τ : ℂ) - (c - τ) * xiτ τ) ^ 2) /
          (((vτ τ : ℂ) - (c - τ) * xiτ τ) * ((vτ τ : ℂ) + (c - τ) * xiτ τ)) ^ 2 := by
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  obtain ⟨hAp, hAm, hLp, hLm⟩ := factors_ne τ h1 h2 c hc
  unfold Pihat
  rw [hβC, hνC, fA (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0, fA' (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0,
    fL (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0, fL' (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0]
  generalize (vτ τ : ℂ) + τ * xiτ τ = Ap at *
  generalize (vτ τ : ℂ) - τ * xiτ τ = Am at *
  generalize (vτ τ : ℂ) - (c - τ) * xiτ τ = Lp at *
  generalize (vτ τ : ℂ) + (c - τ) * xiτ τ = Lm at *
  rw [eq_div_iff (pow_ne_zero 2 (mul_ne_zero hLp hLm))]
  field_simp
  ring

private lemma relAA (t z v : ℂ) (hz : z ^ 2 = t ^ 2 - 1 / 4) (hv : v = 1 - t ^ 2) :
    (v + t * z) * (v - t * z) = (4 - 7 * t ^ 2) / 4 := by
  subst hv
  linear_combination (-t ^ 2) * hz

private lemma relLL (t c z v : ℂ) (hz : z ^ 2 = t ^ 2 - 1 / 4) (hv : v = 1 - t ^ 2) :
    (v - (c - t) * z) * (v + (c - t) * z) = F2p t c / 4 := by
  subst hv
  unfold F2p
  linear_combination (-(c - t) ^ 2) * hz

private lemma relX (t c z v : ℂ) (hz : z ^ 2 = t ^ 2 - 1 / 4) (hv : v = 1 - t ^ 2) :
    (v + t * z) * (v + (c - t) * z) ^ 2 + (v - t * z) * (v - (c - t) * z) ^ 2 = v * F1p t c / 2 := by
  subst hv
  unfold F1p
  linear_combination ((2 : ℂ) * t ^ 4 + (-2 : ℂ) * t ^ 2 * c ^ 2 + (-2 : ℂ) * t ^ 2 + (2 : ℂ) * c ^ 2) * hz

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The ξ-elimination for `T_2`: `NUMP2 ≡ ` its closed form modulo `ξ² = τ² - 1/4`. -/
private lemma core2 (t c z v s : ℂ) (hz : z ^ 2 = t ^ 2 - 1 / 4) (hv : v = 1 - t ^ 2) (hs : s = 1 / 4 - t ^ 2) :
    NUMP2 t c z v (PcC t c) (QcC t c) = -(Ncp2 t c * s * F2p t c * v ^ 2 * z * (4 - 7 * t ^ 2)) / 2048 := by
  subst hv hs
  unfold NUMP2 PcC QcC Ncp2 F2p
  linear_combination ((-80 : ℂ) * t ^ 19 * c ^ 3 * z ^ 3 + (124 : ℂ) * t ^ 19 * c * z ^ 3 + (128 : ℂ) * t ^ 18 * c ^ 4 * z ^ 3 + (-112 : ℂ) * t ^ 18 * c ^ 4 * z + (-144 : ℂ) * t ^ 18 * c ^ 2 * z ^ 3 + (-28 : ℂ) * t ^ 18 * c ^ 2 * z + (-112 : ℂ) * t ^ 18 * z ^ 3 + (-48 : ℂ) * t ^ 17 * c ^ 5 * z ^ 3 + (168 : ℂ) * t ^ 17 * c ^ 5 * z + (32 : ℂ) * t ^ 17 * c ^ 3 * z ^ 5 + (576 : ℂ) * t ^ 17 * c ^ 3 * z ^ 3 + (448 : ℂ) * t ^ 17 * c ^ 3 * z + (-88 : ℂ) * t ^ 17 * c * z ^ 5 + (-762 : ℂ) * t ^ 17 * c * z ^ 3 + (147 / 2 : ℂ) * t ^ 17 * c * z + (-56 : ℂ) * t ^ 16 * c ^ 6 * z + (-1024 : ℂ) * t ^ 16 * c ^ 4 * z ^ 3 + (-90 : ℂ) * t ^ 16 * c ^ 4 * z + (56 : ℂ) * t ^ 16 * c ^ 2 * z ^ 5 + (1028 : ℂ) * t ^ 16 * c ^ 2 * z ^ 3 + (-1011 / 2 : ℂ) * t ^ 16 * c ^ 2 * z + (70 : ℂ) * t ^ 16 * z ^ 5 + (855 : ℂ) * t ^ 16 * z ^ 3 + (-343 / 8 : ℂ) * t ^ 16 * z + (-144 : ℂ) * t ^ 15 * c ^ 5 * z ^ 5 + (516 : ℂ) * t ^ 15 * c ^ 5 * z ^ 3 + (-600 : ℂ) * t ^ 15 * c ^ 5 * z + (48 : ℂ) * t ^ 15 * c ^ 3 * z ^ 7 + (20 : ℂ) * t ^ 15 * c ^ 3 * z ^ 5 + (-1352 : ℂ) * t ^ 15 * c ^ 3 * z ^ 3 + (-1250 : ℂ) * t ^ 15 * c ^ 3 * z + (-36 : ℂ) * t ^ 15 * c * z ^ 7 + (508 : ℂ) * t ^ 15 * c * z ^ 5 + (1800 : ℂ) * t ^ 15 * c * z ^ 3 + (-189 / 4 : ℂ) * t ^ 15 * c * z + (160 : ℂ) * t ^ 14 * c ^ 6 * z ^ 5 + (-56 : ℂ) * t ^ 14 * c ^ 6 * z ^ 3 + (256 : ℂ) * t ^ 14 * c ^ 6 * z + (-192 : ℂ) * t ^ 14 * c ^ 4 * z ^ 7 + (-168 : ℂ) * t ^ 14 * c ^ 4 * z ^ 5 + (2678 : ℂ) * t ^ 14 * c ^ 4 * z ^ 3 + (3207 / 2 : ℂ) * t ^ 14 * c ^ 4 * z + (72 : ℂ) * t ^ 14 * c ^ 2 * z ^ 7 + (-836 : ℂ) * t ^ 14 * c ^ 2 * z ^ 5 + (-7697 / 2 : ℂ) * t ^ 14 * c ^ 2 * z ^ 3 + (9123 / 4 : ℂ) * t ^ 14 * c ^ 2 * z + (42 : ℂ) * t ^ 14 * z ^ 7 + (-843 / 2 : ℂ) * t ^ 14 * z ^ 5 + (-23041 / 8 : ℂ) * t ^ 14 * z ^ 3 + (6125 / 32 : ℂ) * t ^ 14 * z + (-48 : ℂ) * t ^ 13 * c ^ 7 * z ^ 5 + (288 : ℂ) * t ^ 13 * c ^ 5 * z ^ 7 + (744 : ℂ) * t ^ 13 * c ^ 5 * z ^ 5 + (-1650 : ℂ) * t ^ 13 * c ^ 5 * z ^ 3 + (1395 / 2 : ℂ) * t ^ 13 * c ^ 5 * z + (-84 : ℂ) * t ^ 13 * c ^ 3 * z ^ 7 + (228 : ℂ) * t ^ 13 * c ^ 3 * z ^ 5 + (2054 : ℂ) * t ^ 13 * c ^ 3 * z ^ 3 + (211 : ℂ) * t ^ 13 * c ^ 3 * z + (-24 : ℂ) * t ^ 13 * c * z ^ 7 + (-963 : ℂ) * t ^ 13 * c * z ^ 5 + (-4737 / 4 : ℂ) * t ^ 13 * c * z ^ 3 + (-9843 / 16 : ℂ) * t ^ 13 * c * z + (-192 : ℂ) * t ^ 12 * c ^ 6 * z ^ 7 + (-816 : ℂ) * t ^ 12 * c ^ 6 * z ^ 5 + (242 : ℂ) * t ^ 12 * c ^ 6 * z ^ 3 + (-485 : ℂ) * t ^ 12 * c ^ 6 * z + (336 : ℂ) * t ^ 12 * c ^ 4 * z ^ 7 + (198 : ℂ) * t ^ 12 * c ^ 4 * z ^ 5 + (-3214 : ℂ) * t ^ 12 * c ^ 4 * z ^ 3 + (-27123 / 8 : ℂ) * t ^ 12 * c ^ 4 * z + (-90 : ℂ) * t ^ 12 * c ^ 2 * z ^ 7 + (5535 / 2 : ℂ) * t ^ 12 * c ^ 2 * z ^ 5 + (64261 / 8 : ℂ) * t ^ 12 * c ^ 2 * z ^ 3 + (-110001 / 32 : ℂ) * t ^ 12 * c ^ 2 * z + (-150 : ℂ) * t ^ 12 * z ^ 7 + (2025 / 2 : ℂ) * t ^ 12 * z ^ 5 + (44035 / 8 : ℂ) * t ^ 12 * z ^ 3 + (-12271 / 32 : ℂ) * t ^ 12 * z + (48 : ℂ) * t ^ 11 * c ^ 7 * z ^ 7 + (252 : ℂ) * t ^ 11 * c ^ 7 * z ^ 5 + (-684 : ℂ) * t ^ 11 * c ^ 5 * z ^ 7 + (-1236 : ℂ) * t ^ 11 * c ^ 5 * z ^ 5 + (2490 : ℂ) * t ^ 11 * c ^ 5 * z ^ 3 + (-327 / 4 : ℂ) * t ^ 11 * c ^ 5 * z + (-60 : ℂ) * t ^ 11 * c ^ 3 * z ^ 7 + (-1666 : ℂ) * t ^ 11 * c ^ 3 * z ^ 5 + (-7203 / 2 : ℂ) * t ^ 11 * c ^ 3 * z ^ 3 + (23927 / 8 : ℂ) * t ^ 11 * c ^ 3 * z + (384 : ℂ) * t ^ 11 * c * z ^ 7 + (581 : ℂ) * t ^ 11 * c * z ^ 5 + (-11625 / 4 : ℂ) * t ^ 11 * c * z ^ 3 + (23901 / 16 : ℂ) * t ^ 11 * c * z + (552 : ℂ) * t ^ 10 * c ^ 6 * z ^ 7 + (1608 : ℂ) * t ^ 10 * c ^ 6 * z ^ 5 + (-849 / 2 : ℂ) * t ^ 10 * c ^ 6 * z ^ 3 + (989 / 2 : ℂ) * t ^ 10 * c ^ 6 * z + (150 : ℂ) * t ^ 10 * c ^ 4 * z ^ 7 + (1443 / 2 : ℂ) * t ^ 10 * c ^ 4 * z ^ 5 + (15673 / 8 : ℂ) * t ^ 10 * c ^ 4 * z ^ 3 + (99675 / 32 : ℂ) * t ^ 10 * c ^ 4 * z + (-306 : ℂ) * t ^ 10 * c ^ 2 * z ^ 7 + (-8225 / 2 : ℂ) * t ^ 10 * c ^ 2 * z ^ 5 + (-72923 / 8 : ℂ) * t ^ 10 * c ^ 2 * z ^ 3 + (58695 / 32 : ℂ) * t ^ 10 * c ^ 2 * z + (198 : ℂ) * t ^ 10 * z ^ 7 + (-2497 / 2 : ℂ) * t ^ 10 * z ^ 5 + (-51699 / 8 : ℂ) * t ^ 10 * z ^ 3 + (16055 / 32 : ℂ) * t ^ 10 * z + (-156 : ℂ) * t ^ 9 * c ^ 7 * z ^ 7 + (-540 : ℂ) * t ^ 9 * c ^ 7 * z ^ 5 + (288 : ℂ) * t ^ 9 * c ^ 5 * z ^ 7 + (429 : ℂ) * t ^ 9 * c ^ 5 * z ^ 5 + (-8169 / 4 : ℂ) * t ^ 9 * c ^ 5 * z ^ 3 + (-7755 / 16 : ℂ) * t ^ 9 * c ^ 5 * z + (300 : ℂ) * t ^ 9 * c ^ 3 * z ^ 7 + (3230 : ℂ) * t ^ 9 * c ^ 3 * z ^ 5 + (10985 / 2 : ℂ) * t ^ 9 * c ^ 3 * z ^ 3 + (-36925 / 8 : ℂ) * t ^ 9 * c ^ 3 * z + (-648 : ℂ) * t ^ 9 * c * z ^ 7 + (307 : ℂ) * t ^ 9 * c * z ^ 5 + (29529 / 4 : ℂ) * t ^ 9 * c * z ^ 3 + (-22293 / 16 : ℂ) * t ^ 9 * c * z + (-486 : ℂ) * t ^ 8 * c ^ 6 * z ^ 7 + (-2935 / 2 : ℂ) * t ^ 8 * c ^ 6 * z ^ 5 + (3107 / 8 : ℂ) * t ^ 8 * c ^ 6 * z ^ 3 + (-9463 / 32 : ℂ) * t ^ 8 * c ^ 6 * z + (-570 : ℂ) * t ^ 8 * c ^ 4 * z ^ 7 + (-3465 / 2 : ℂ) * t ^ 8 * c ^ 4 * z ^ 5 + (-5939 / 8 : ℂ) * t ^ 8 * c ^ 4 * z ^ 3 + (-42081 / 32 : ℂ) * t ^ 8 * c ^ 4 * z + (738 : ℂ) * t ^ 8 * c ^ 2 * z ^ 7 + (6665 / 2 : ℂ) * t ^ 8 * c ^ 2 * z ^ 5 + (39787 / 8 : ℂ) * t ^ 8 * c ^ 2 * z ^ 3 + (18561 / 32 : ℂ) * t ^ 8 * c ^ 2 * z + (-114 : ℂ) * t ^ 8 * z ^ 7 + (1671 / 2 : ℂ) * t ^ 8 * z ^ 5 + (37961 / 8 : ℂ) * t ^ 8 * z ^ 3 + (-16489 / 32 : ℂ) * t ^ 8 * z + (180 : ℂ) * t ^ 7 * c ^ 7 * z ^ 7 + (600 : ℂ) * t ^ 7 * c ^ 7 * z ^ 5 + (360 : ℂ) * t ^ 7 * c ^ 5 * z ^ 7 + (885 : ℂ) * t ^ 7 * c ^ 5 * z ^ 5 + (3831 / 4 : ℂ) * t ^ 7 * c ^ 5 * z ^ 3 + (7101 / 16 : ℂ) * t ^ 7 * c ^ 5 * z + (-420 : ℂ) * t ^ 7 * c ^ 3 * z ^ 7 + (-3042 : ℂ) * t ^ 7 * c ^ 3 * z ^ 5 + (-10097 / 2 : ℂ) * t ^ 7 * c ^ 3 * z ^ 3 + (25181 / 8 : ℂ) * t ^ 7 * c ^ 3 * z + (420 : ℂ) * t ^ 7 * c * z ^ 7 + (-549 : ℂ) * t ^ 7 * c * z ^ 5 + (-29859 / 4 : ℂ) * t ^ 7 * c * z ^ 3 + (8355 / 16 : ℂ) * t ^ 7 * c * z + (66 : ℂ) * t ^ 6 * c ^ 6 * z ^ 7 + (993 / 2 : ℂ) * t ^ 6 * c ^ 6 * z ^ 5 + (-1589 / 8 : ℂ) * t ^ 6 * c ^ 6 * z ^ 3 + (3401 / 32 : ℂ) * t ^ 6 * c ^ 6 * z + (330 : ℂ) * t ^ 6 * c ^ 4 * z ^ 7 + (2865 / 2 : ℂ) * t ^ 6 * c ^ 4 * z ^ 5 + (2947 / 8 : ℂ) * t ^ 6 * c ^ 4 * z ^ 3 + (4185 / 32 : ℂ) * t ^ 6 * c ^ 4 * z + (-558 : ℂ) * t ^ 6 * c ^ 2 * z ^ 7 + (-3267 / 2 : ℂ) * t ^ 6 * c ^ 2 * z ^ 5 + (-2549 / 8 : ℂ) * t ^ 6 * c ^ 2 * z ^ 3 + (-38139 / 32 : ℂ) * t ^ 6 * c ^ 2 * z + (24 : ℂ) * t ^ 6 * z ^ 7 + (-288 : ℂ) * t ^ 6 * z ^ 5 + (-2122 : ℂ) * t ^ 6 * z ^ 3 + (815 / 2 : ℂ) * t ^ 6 * z + (-84 : ℂ) * t ^ 5 * c ^ 7 * z ^ 7 + (-360 : ℂ) * t ^ 5 * c ^ 7 * z ^ 5 + (-288 : ℂ) * t ^ 5 * c ^ 5 * z ^ 7 + (-1005 : ℂ) * t ^ 5 * c ^ 5 * z ^ 5 + (-1047 / 4 : ℂ) * t ^ 5 * c ^ 5 * z ^ 3 + (-2757 / 16 : ℂ) * t ^ 5 * c ^ 5 * z + (312 : ℂ) * t ^ 5 * c ^ 3 * z ^ 7 + (1670 : ℂ) * t ^ 5 * c ^ 3 * z ^ 5 + (5079 / 2 : ℂ) * t ^ 5 * c ^ 3 * z ^ 3 + (-8935 / 8 : ℂ) * t ^ 5 * c ^ 3 * z + (-96 : ℂ) * t ^ 5 * c * z ^ 7 + (236 : ℂ) * t ^ 5 * c * z ^ 5 + (3999 : ℂ) * t ^ 5 * c * z ^ 3 + (69 / 4 : ℂ) * t ^ 5 * c * z + (78 : ℂ) * t ^ 4 * c ^ 6 * z ^ 7 + (231 / 2 : ℂ) * t ^ 4 * c ^ 6 * z ^ 5 + (453 / 8 : ℂ) * t ^ 4 * c ^ 6 * z ^ 3 + (-721 / 32 : ℂ) * t ^ 4 * c ^ 6 * z + (-78 : ℂ) * t ^ 4 * c ^ 4 * z ^ 7 + (-1119 / 2 : ℂ) * t ^ 4 * c ^ 4 * z ^ 5 + (-1649 / 8 : ℂ) * t ^ 4 * c ^ 4 * z ^ 3 + (2673 / 32 : ℂ) * t ^ 4 * c ^ 4 * z + (144 : ℂ) * t ^ 4 * c ^ 2 * z ^ 7 + (506 : ℂ) * t ^ 4 * c ^ 2 * z ^ 5 + (-2003 / 2 : ℂ) * t ^ 4 * c ^ 2 * z ^ 3 + (4659 / 8 : ℂ) * t ^ 4 * c ^ 2 * z + (40 : ℂ) * t ^ 4 * z ^ 5 + (528 : ℂ) * t ^ 4 * z ^ 3 + (-215 : ℂ) * t ^ 4 * z + (12 : ℂ) * t ^ 3 * c ^ 7 * z ^ 7 + (108 : ℂ) * t ^ 3 * c ^ 7 * z ^ 5 + (36 : ℂ) * t ^ 3 * c ^ 5 * z ^ 7 + (363 : ℂ) * t ^ 3 * c ^ 5 * z ^ 5 + (165 / 4 : ℂ) * t ^ 3 * c ^ 5 * z ^ 3 + (507 / 16 : ℂ) * t ^ 3 * c ^ 5 * z + (-96 : ℂ) * t ^ 3 * c ^ 3 * z ^ 7 + (-568 : ℂ) * t ^ 3 * c ^ 3 * z ^ 5 + (-644 : ℂ) * t ^ 3 * c ^ 3 * z ^ 3 + (199 : ℂ) * t ^ 3 * c ^ 3 * z + (-32 : ℂ) * t ^ 3 * c * z ^ 5 + (-1116 : ℂ) * t ^ 3 * c * z ^ 3 + (-63 : ℂ) * t ^ 3 * c * z + (-18 : ℂ) * t ^ 2 * c ^ 6 * z ^ 7 + (-229 / 2 : ℂ) * t ^ 2 * c ^ 6 * z ^ 5 + (-67 / 8 : ℂ) * t ^ 2 * c ^ 6 * z ^ 3 + (83 / 32 : ℂ) * t ^ 2 * c ^ 6 * z + (24 : ℂ) * t ^ 2 * c ^ 4 * z ^ 7 + (132 : ℂ) * t ^ 2 * c ^ 4 * z ^ 5 + (59 : ℂ) * t ^ 2 * c ^ 4 * z ^ 3 + (-111 / 4 : ℂ) * t ^ 2 * c ^ 4 * z + (-80 : ℂ) * t ^ 2 * c ^ 2 * z ^ 5 + (458 : ℂ) * t ^ 2 * c ^ 2 * z ^ 3 + (-249 / 2 : ℂ) * t ^ 2 * c ^ 2 * z + (-56 : ℂ) * t ^ 2 * z ^ 3 + (64 : ℂ) * t ^ 2 * z + (-12 : ℂ) * t * c ^ 7 * z ^ 5 + (-36 : ℂ) * t * c ^ 5 * z ^ 5 + (-3 : ℂ) * t * c ^ 5 * z ^ 3 + (-9 / 4 : ℂ) * t * c ^ 5 * z + (96 : ℂ) * t * c ^ 3 * z ^ 5 + (64 : ℂ) * t * c ^ 3 * z ^ 3 + (-14 : ℂ) * t * c ^ 3 * z + (128 : ℂ) * t * c * z ^ 3 + (12 : ℂ) * t * c * z + (18 : ℂ) * c ^ 6 * z ^ 5 + (1 / 2 : ℂ) * c ^ 6 * z ^ 3 + (-1 / 8 : ℂ) * c ^ 6 * z + (-24 : ℂ) * c ^ 4 * z ^ 5 + (-6 : ℂ) * c ^ 4 * z ^ 3 + (5 / 2 : ℂ) * c ^ 4 * z + (-64 : ℂ) * c ^ 2 * z ^ 3 + (10 : ℂ) * c ^ 2 * z + (-8 : ℂ) * z) * hz

set_option maxHeartbeats 1000000 in
private lemma NUM2_eq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NUMdef τ c 2 = NUMP2 (τ : ℂ) c (xiτ τ) (vτ τ : ℂ) (Pc τ c) (Qc τ c) /
      (Qc τ c * (((vτ τ : ℂ) + τ * xiτ τ) * ((vτ τ : ℂ) - τ * xiτ τ)) ^ 1 *
        (((vτ τ : ℂ) - (c - τ) * xiτ τ) * ((vτ τ : ℂ) + (c - τ) * xiτ τ)) ^ 4) := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  have hb1 := one_add_beta_ne τ h1 h2 _ hxi
  have hb2 := one_add_beta_ne τ h1 h2 _ hxi'
  have hQ := Qc_ne τ h1 h2.le c hc
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  obtain ⟨hAp, hAm, hLp, hLm⟩ := factors_ne τ h1 h2 c hc
  unfold NUMdef dPiJf
  rw [deriv_aJ τ 2 _ hb1, deriv_aJ τ 2 _ hb2]
  unfold aJ PiJ NUMP2
  simp only [Nat.cast_ofNat, Int.reduceSub, zpow_neg, zpow_ofNat]
  rw [hβC, hνC, fA (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0, fA' (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0,
    fL (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0, fL' (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0]
  generalize (vτ τ : ℂ) + τ * xiτ τ = Ap at *
  generalize (vτ τ : ℂ) - τ * xiτ τ = Am at *
  generalize (vτ τ : ℂ) - (c - τ) * xiτ τ = Lp at *
  generalize (vτ τ : ℂ) + (c - τ) * xiτ τ = Lm at *
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hQ (pow_ne_zero _ (mul_ne_zero hAp hAm)))
    (pow_ne_zero _ (mul_ne_zero hLp hLm)))]
  field_simp
  ring

/-- The closed form of `T_2`. -/
private lemma TJ2_closed (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    TJ τ c 2 = Nc2 τ c / (((256 : ℝ) : ℂ) * Qc τ c ^ 2) := by
  have hz : xiτ τ ^ 2 = (τ : ℂ) ^ 2 - 1 / 4 := by
    rw [xi_sq τ h1 h2]
    unfold ysq
    push_cast
    ring
  have hvd : (vτ τ : ℂ) = 1 - (τ : ℂ) ^ 2 := by
    unfold vτ
    push_cast
    ring
  have hsd : (ysq τ : ℂ) = 1 / 4 - (τ : ℂ) ^ 2 := by
    unfold ysq
    push_cast
    ring
  have hs0 : (ysq τ : ℂ) ≠ 0 := by exact_mod_cast (ysq_pos τ h1 h2).ne'
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  have hz0 := xi_ne τ h1 h2
  have hQ0 := Qc_ne τ h1 h2.le c hc
  rw [Qc_C, QcC_F] at hQ0
  have hF1 : F1p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hF2 : F2p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hW0 : (4 - 7 * (τ : ℂ) ^ 2) ≠ 0 := by
    have h47 : (4 : ℝ) - 7 * τ ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast h47
  rw [TJ_eq τ h1 h2 2 c hc, TJf_eq, NUM2_eq τ h1 h2 c hc, DEN_eq τ h1 h2 c hc, Pc_C, Qc_C,
    core2 (τ : ℂ) c (xiτ τ) _ _ hz hvd hsd, relAA _ _ _ hz hvd, relLL _ _ _ _ hz hvd,
    relX _ _ _ _ hz hvd, Nc2_C, QcC_F]
  rw [show ((256 : ℝ) : ℂ) = 256 by norm_num]
  generalize F1p (τ : ℂ) c = F1 at *
  generalize F2p (τ : ℂ) c = F2 at *
  generalize Ncp2 (τ : ℂ) c = N at *
  generalize (4 - 7 * (τ : ℂ) ^ 2) = W at *
  generalize xiτ τ = z at *
  generalize (vτ τ : ℂ) = v at *
  generalize (ysq τ : ℂ) = s at *
  field_simp
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The ξ-elimination for `T_3`: `NUMP3 ≡ ` its closed form modulo `ξ² = τ² - 1/4`. -/
private lemma core3 (t c z v s : ℂ) (hz : z ^ 2 = t ^ 2 - 1 / 4) (hv : v = 1 - t ^ 2) (hs : s = 1 / 4 - t ^ 2) :
    NUMP3 t c z v (PcC t c) (QcC t c) = -(Ncp3 t c * s * F2p t c * v ^ 2 * z) / 8192 := by
  subst hv hs
  unfold NUMP3 PcC QcC Ncp3 F2p
  linear_combination ((32 : ℂ) * t ^ 22 * c ^ 3 * z ^ 3 + (-56 : ℂ) * t ^ 22 * c * z ^ 3 + (-16 : ℂ) * t ^ 21 * c ^ 4 * z ^ 3 + (192 : ℂ) * t ^ 21 * c ^ 4 * z + (112 : ℂ) * t ^ 21 * c ^ 2 * z + (49 : ℂ) * t ^ 21 * z ^ 3 + (-256 : ℂ) * t ^ 20 * c ^ 5 * z + (192 : ℂ) * t ^ 20 * c ^ 3 * z ^ 5 + (-296 : ℂ) * t ^ 20 * c ^ 3 * z ^ 3 + (-980 : ℂ) * t ^ 20 * c ^ 3 * z + (-272 : ℂ) * t ^ 20 * c * z ^ 5 + (536 : ℂ) * t ^ 20 * c * z ^ 3 + (-245 : ℂ) * t ^ 20 * c * z + (32 : ℂ) * t ^ 19 * c ^ 6 * z + (-432 : ℂ) * t ^ 19 * c ^ 4 * z ^ 5 + (340 : ℂ) * t ^ 19 * c ^ 4 * z ^ 3 + (230 : ℂ) * t ^ 19 * c ^ 4 * z + (500 : ℂ) * t ^ 19 * c ^ 2 * z ^ 5 + (112 : ℂ) * t ^ 19 * c ^ 2 * z ^ 3 + (818 : ℂ) * t ^ 19 * c ^ 2 * z + (252 : ℂ) * t ^ 19 * z ^ 5 + (-1939 / 4 : ℂ) * t ^ 19 * z ^ 3 + (1029 / 8 : ℂ) * t ^ 19 * z + (96 : ℂ) * t ^ 18 * c ^ 7 * z + (320 : ℂ) * t ^ 18 * c ^ 5 * z ^ 5 + (-256 : ℂ) * t ^ 18 * c ^ 5 * z ^ 3 + (872 : ℂ) * t ^ 18 * c ^ 5 * z + (-160 : ℂ) * t ^ 18 * c ^ 3 * z ^ 7 + (-1576 : ℂ) * t ^ 18 * c ^ 3 * z ^ 5 + (244 : ℂ) * t ^ 18 * c ^ 3 * z ^ 3 + (3458 : ℂ) * t ^ 18 * c ^ 3 * z + (280 : ℂ) * t ^ 18 * c * z ^ 7 + (1394 : ℂ) * t ^ 18 * c * z ^ 5 + (-2549 : ℂ) * t ^ 18 * c * z ^ 3 + (2933 / 4 : ℂ) * t ^ 18 * c * z + (-52 : ℂ) * t ^ 17 * c ^ 8 * z + (-80 : ℂ) * t ^ 17 * c ^ 6 * z ^ 5 + (32 : ℂ) * t ^ 17 * c ^ 6 * z ^ 3 + (-310 : ℂ) * t ^ 17 * c ^ 6 * z + (432 : ℂ) * t ^ 17 * c ^ 4 * z ^ 7 + (3196 : ℂ) * t ^ 17 * c ^ 4 * z ^ 5 + (-334 : ℂ) * t ^ 17 * c ^ 4 * z ^ 3 + (-3175 : ℂ) * t ^ 17 * c ^ 4 * z + (-584 : ℂ) * t ^ 17 * c ^ 2 * z ^ 7 + (-3118 : ℂ) * t ^ 17 * c ^ 2 * z ^ 5 + (846 : ℂ) * t ^ 17 * c ^ 2 * z ^ 3 + (-43001 / 8 : ℂ) * t ^ 17 * c ^ 2 * z + (-245 : ℂ) * t ^ 17 * z ^ 7 + (-7443 / 4 : ℂ) * t ^ 17 * z ^ 5 + (36663 / 16 : ℂ) * t ^ 17 * z ^ 3 + (-46011 / 64 : ℂ) * t ^ 17 * z + (8 : ℂ) * t ^ 16 * c ^ 9 * z + (96 : ℂ) * t ^ 16 * c ^ 7 * z ^ 3 + (-322 : ℂ) * t ^ 16 * c ^ 7 * z + (-384 : ℂ) * t ^ 16 * c ^ 5 * z ^ 7 + (-2504 : ℂ) * t ^ 16 * c ^ 5 * z ^ 5 + (808 : ℂ) * t ^ 16 * c ^ 5 * z ^ 3 + (-1367 / 2 : ℂ) * t ^ 16 * c ^ 5 * z + (-64 : ℂ) * t ^ 16 * c ^ 3 * z ^ 9 + (1048 : ℂ) * t ^ 16 * c ^ 3 * z ^ 7 + (4740 : ℂ) * t ^ 16 * c ^ 3 * z ^ 5 + (237 : ℂ) * t ^ 16 * c ^ 3 * z ^ 3 + (-30377 / 8 : ℂ) * t ^ 16 * c ^ 3 * z + (48 : ℂ) * t ^ 16 * c * z ^ 9 + (-1028 : ℂ) * t ^ 16 * c * z ^ 7 + (-2079 : ℂ) * t ^ 16 * c * z ^ 5 + (6528 : ℂ) * t ^ 16 * c * z ^ 3 + (-1483 / 16 : ℂ) * t ^ 16 * c * z + (-52 : ℂ) * t ^ 15 * c ^ 8 * z ^ 3 + (212 : ℂ) * t ^ 15 * c ^ 8 * z + (112 : ℂ) * t ^ 15 * c ^ 6 * z ^ 7 + (612 : ℂ) * t ^ 15 * c ^ 6 * z ^ 5 + (-302 : ℂ) * t ^ 15 * c ^ 6 * z ^ 3 + (1753 / 2 : ℂ) * t ^ 15 * c ^ 6 * z + (272 : ℂ) * t ^ 15 * c ^ 4 * z ^ 9 + (-2060 : ℂ) * t ^ 15 * c ^ 4 * z ^ 7 + (-8610 : ℂ) * t ^ 15 * c ^ 4 * z ^ 5 + (-3235 / 2 : ℂ) * t ^ 15 * c ^ 4 * z ^ 3 + (54013 / 8 : ℂ) * t ^ 15 * c ^ 4 * z + (-108 : ℂ) * t ^ 15 * c ^ 2 * z ^ 9 + (3334 : ℂ) * t ^ 15 * c ^ 2 * z ^ 7 + (18217 / 2 : ℂ) * t ^ 15 * c ^ 2 * z ^ 5 + (-41309 / 8 : ℂ) * t ^ 15 * c ^ 2 * z ^ 3 + (388273 / 32 : ℂ) * t ^ 15 * c ^ 2 * z + (-56 : ℂ) * t ^ 15 * z ^ 9 + (1407 : ℂ) * t ^ 15 * z ^ 7 + (24189 / 4 : ℂ) * t ^ 15 * z ^ 5 + (-102753 / 16 : ℂ) * t ^ 15 * z ^ 3 + (117285 / 64 : ℂ) * t ^ 15 * z + (8 : ℂ) * t ^ 14 * c ^ 9 * z ^ 3 + (-34 : ℂ) * t ^ 14 * c ^ 9 * z + (96 : ℂ) * t ^ 14 * c ^ 7 * z ^ 5 + (-298 : ℂ) * t ^ 14 * c ^ 7 * z ^ 3 + (356 : ℂ) * t ^ 14 * c ^ 7 * z + (-448 : ℂ) * t ^ 14 * c ^ 5 * z ^ 9 + (1960 : ℂ) * t ^ 14 * c ^ 5 * z ^ 7 + (7502 : ℂ) * t ^ 14 * c ^ 5 * z ^ 5 + (-963 / 2 : ℂ) * t ^ 14 * c ^ 5 * z ^ 3 + (-7823 / 8 : ℂ) * t ^ 14 * c ^ 5 * z + (136 : ℂ) * t ^ 14 * c ^ 3 * z ^ 9 + (-4194 : ℂ) * t ^ 14 * c ^ 3 * z ^ 7 + (-9000 : ℂ) * t ^ 14 * c ^ 3 * z ^ 5 + (13681 / 8 : ℂ) * t ^ 14 * c ^ 3 * z ^ 3 + (-4567 / 16 : ℂ) * t ^ 14 * c ^ 3 * z + (46 : ℂ) * t ^ 14 * c * z ^ 9 + (209 : ℂ) * t ^ 14 * c * z ^ 7 + (-10497 / 4 : ℂ) * t ^ 14 * c * z ^ 5 + (-154699 / 16 : ℂ) * t ^ 14 * c * z ^ 3 + (-171793 / 64 : ℂ) * t ^ 14 * c * z + (-52 : ℂ) * t ^ 13 * c ^ 8 * z ^ 5 + (199 : ℂ) * t ^ 13 * c ^ 8 * z ^ 3 + (-695 / 2 : ℂ) * t ^ 13 * c ^ 8 * z + (352 : ℂ) * t ^ 13 * c ^ 6 * z ^ 9 + (-728 : ℂ) * t ^ 13 * c ^ 6 * z ^ 7 + (-2114 : ℂ) * t ^ 13 * c ^ 6 * z ^ 5 + (801 : ℂ) * t ^ 13 * c ^ 6 * z ^ 3 + (-8753 / 8 : ℂ) * t ^ 13 * c ^ 6 * z + (-476 : ℂ) * t ^ 13 * c ^ 4 * z ^ 9 + (5144 : ℂ) * t ^ 13 * c ^ 4 * z ^ 7 + (11704 : ℂ) * t ^ 13 * c ^ 4 * z ^ 5 + (14493 / 4 : ℂ) * t ^ 13 * c ^ 4 * z ^ 3 + (-50771 / 8 : ℂ) * t ^ 13 * c ^ 4 * z + (112 : ℂ) * t ^ 13 * c ^ 2 * z ^ 9 + (-6382 : ℂ) * t ^ 13 * c ^ 2 * z ^ 7 + (-28273 / 2 : ℂ) * t ^ 13 * c ^ 2 * z ^ 5 + (86741 / 8 : ℂ) * t ^ 13 * c ^ 2 * z ^ 3 + (-490361 / 32 : ℂ) * t ^ 13 * c ^ 2 * z + (200 : ℂ) * t ^ 13 * z ^ 9 + (-3279 : ℂ) * t ^ 13 * z ^ 7 + (-44613 / 4 : ℂ) * t ^ 13 * z ^ 5 + (186897 / 16 : ℂ) * t ^ 13 * z ^ 3 + (-180813 / 64 : ℂ) * t ^ 13 * z + (8 : ℂ) * t ^ 12 * c ^ 9 * z ^ 5 + (-32 : ℂ) * t ^ 12 * c ^ 9 * z ^ 3 + (59 : ℂ) * t ^ 12 * c ^ 9 * z + (-128 : ℂ) * t ^ 12 * c ^ 7 * z ^ 9 + (128 : ℂ) * t ^ 12 * c ^ 7 * z ^ 7 + (-274 : ℂ) * t ^ 12 * c ^ 7 * z ^ 5 + (563 / 2 : ℂ) * t ^ 12 * c ^ 7 * z ^ 3 + (-283 / 4 : ℂ) * t ^ 12 * c ^ 7 * z + (1024 : ℂ) * t ^ 12 * c ^ 5 * z ^ 9 + (-4588 : ℂ) * t ^ 12 * c ^ 5 * z ^ 7 + (-23075 / 2 : ℂ) * t ^ 12 * c ^ 5 * z ^ 5 + (-4393 / 4 : ℂ) * t ^ 12 * c ^ 5 * z ^ 3 + (71935 / 32 : ℂ) * t ^ 12 * c ^ 5 * z + (50 : ℂ) * t ^ 12 * c ^ 3 * z ^ 9 + (17483 / 2 : ℂ) * t ^ 12 * c ^ 3 * z ^ 7 + (107425 / 8 : ℂ) * t ^ 12 * c ^ 3 * z ^ 5 + (-194365 / 32 : ℂ) * t ^ 12 * c ^ 3 * z ^ 3 + (520393 / 128 : ℂ) * t ^ 12 * c ^ 3 * z + (-562 : ℂ) * t ^ 12 * c * z ^ 9 + (3993 : ℂ) * t ^ 12 * c * z ^ 7 + (56915 / 4 : ℂ) * t ^ 12 * c * z ^ 5 + (134761 / 16 : ℂ) * t ^ 12 * c * z ^ 3 + (375155 / 64 : ℂ) * t ^ 12 * c * z + (16 : ℂ) * t ^ 11 * c ^ 8 * z ^ 9 + (-52 : ℂ) * t ^ 11 * c ^ 8 * z ^ 7 + (186 : ℂ) * t ^ 11 * c ^ 8 * z ^ 5 + (-1191 / 4 : ℂ) * t ^ 11 * c ^ 8 * z ^ 3 + (1181 / 4 : ℂ) * t ^ 11 * c ^ 8 * z + (-964 : ℂ) * t ^ 11 * c ^ 6 * z ^ 9 + (1850 : ℂ) * t ^ 11 * c ^ 6 * z ^ 7 + (7895 / 2 : ℂ) * t ^ 11 * c ^ 6 * z ^ 5 + (-7151 / 8 : ℂ) * t ^ 11 * c ^ 6 * z ^ 3 + (20047 / 32 : ℂ) * t ^ 11 * c ^ 6 * z + (-220 : ℂ) * t ^ 11 * c ^ 4 * z ^ 9 + (-8209 : ℂ) * t ^ 11 * c ^ 4 * z ^ 7 + (-37139 / 4 : ℂ) * t ^ 11 * c ^ 4 * z ^ 5 + (-37321 / 16 : ℂ) * t ^ 11 * c ^ 4 * z ^ 3 + (174965 / 64 : ℂ) * t ^ 11 * c ^ 4 * z + (536 : ℂ) * t ^ 11 * c ^ 2 * z ^ 9 + (4062 : ℂ) * t ^ 11 * c ^ 2 * z ^ 7 + (19405 / 2 : ℂ) * t ^ 11 * c ^ 2 * z ^ 5 + (-100905 / 8 : ℂ) * t ^ 11 * c ^ 2 * z ^ 3 + (411877 / 32 : ℂ) * t ^ 11 * c ^ 2 * z + (-264 : ℂ) * t ^ 11 * z ^ 9 + (3973 : ℂ) * t ^ 11 * z ^ 7 + (50607 / 4 : ℂ) * t ^ 11 * z ^ 5 + (-231663 / 16 : ℂ) * t ^ 11 * z ^ 3 + (184767 / 64 : ℂ) * t ^ 11 * z + (8 : ℂ) * t ^ 10 * c ^ 9 * z ^ 7 + (-30 : ℂ) * t ^ 10 * c ^ 9 * z ^ 5 + (51 : ℂ) * t ^ 10 * c ^ 9 * z ^ 3 + (-217 / 4 : ℂ) * t ^ 10 * c ^ 9 * z + (392 : ℂ) * t ^ 10 * c ^ 7 * z ^ 9 + (-418 : ℂ) * t ^ 10 * c ^ 7 * z ^ 7 + (213 : ℂ) * t ^ 10 * c ^ 7 * z ^ 5 + (-3 / 8 : ℂ) * t ^ 10 * c ^ 7 * z ^ 3 + (-601 / 4 : ℂ) * t ^ 10 * c ^ 7 * z + (-334 : ℂ) * t ^ 10 * c ^ 5 * z ^ 9 + (12877 / 2 : ℂ) * t ^ 10 * c ^ 5 * z ^ 7 + (79439 / 8 : ℂ) * t ^ 10 * c ^ 5 * z ^ 5 + (63149 / 32 : ℂ) * t ^ 10 * c ^ 5 * z ^ 3 + (-223337 / 128 : ℂ) * t ^ 10 * c ^ 5 * z + (-502 : ℂ) * t ^ 10 * c ^ 3 * z ^ 9 + (-17877 / 2 : ℂ) * t ^ 10 * c ^ 3 * z ^ 7 + (-115815 / 8 : ℂ) * t ^ 10 * c ^ 3 * z ^ 5 + (240099 / 32 : ℂ) * t ^ 10 * c ^ 3 * z ^ 3 + (-498095 / 128 : ℂ) * t ^ 10 * c ^ 3 * z + (930 : ℂ) * t ^ 10 * c * z ^ 9 + (-7473 : ℂ) * t ^ 10 * c * z ^ 7 + (-92235 / 4 : ℂ) * t ^ 10 * c * z ^ 5 + (-56649 / 16 : ℂ) * t ^ 10 * c * z ^ 3 + (-440107 / 64 : ℂ) * t ^ 10 * c * z + (-52 : ℂ) * t ^ 9 * c ^ 8 * z ^ 9 + (173 : ℂ) * t ^ 9 * c ^ 8 * z ^ 7 + (-1005 / 4 : ℂ) * t ^ 9 * c ^ 8 * z ^ 5 + (3533 / 16 : ℂ) * t ^ 9 * c ^ 8 * z ^ 3 + (-9037 / 64 : ℂ) * t ^ 9 * c ^ 8 * z + (744 : ℂ) * t ^ 9 * c ^ 6 * z ^ 9 + (-2544 : ℂ) * t ^ 9 * c ^ 6 * z ^ 7 + (-4212 : ℂ) * t ^ 9 * c ^ 6 * z ^ 5 + (403 : ℂ) * t ^ 9 * c ^ 6 * z ^ 3 + (-97 : ℂ) * t ^ 9 * c ^ 6 * z + (860 : ℂ) * t ^ 9 * c ^ 4 * z ^ 9 + (7899 : ℂ) * t ^ 9 * c ^ 4 * z ^ 7 + (19857 / 4 : ℂ) * t ^ 9 * c ^ 4 * z ^ 5 + (-5237 / 16 : ℂ) * t ^ 9 * c ^ 4 * z ^ 3 + (-13303 / 64 : ℂ) * t ^ 9 * c ^ 4 * z + (-1200 : ℂ) * t ^ 9 * c ^ 2 * z ^ 9 + (1782 : ℂ) * t ^ 9 * c ^ 2 * z ^ 7 + (4153 / 2 : ℂ) * t ^ 9 * c ^ 2 * z ^ 5 + (77743 / 8 : ℂ) * t ^ 9 * c ^ 2 * z ^ 3 + (-250439 / 32 : ℂ) * t ^ 9 * c ^ 2 * z + (152 : ℂ) * t ^ 9 * z ^ 9 + (-2640 : ℂ) * t ^ 9 * z ^ 7 + (-8985 : ℂ) * t ^ 9 * z ^ 5 + (49821 / 4 : ℂ) * t ^ 9 * z ^ 3 + (-31629 / 16 : ℂ) * t ^ 9 * z + (-28 : ℂ) * t ^ 8 * c ^ 9 * z ^ 7 + (87 / 2 : ℂ) * t ^ 8 * c ^ 9 * z ^ 5 + (-83 / 2 : ℂ) * t ^ 8 * c ^ 9 * z ^ 3 + (925 / 32 : ℂ) * t ^ 8 * c ^ 9 * z + (-402 : ℂ) * t ^ 8 * c ^ 7 * z ^ 9 + (1021 / 2 : ℂ) * t ^ 8 * c ^ 7 * z ^ 7 + (423 / 8 : ℂ) * t ^ 8 * c ^ 7 * z ^ 5 + (-4811 / 32 : ℂ) * t ^ 8 * c ^ 7 * z ^ 3 + (16639 / 128 : ℂ) * t ^ 8 * c ^ 7 * z + (-670 : ℂ) * t ^ 8 * c ^ 5 * z ^ 9 + (-11367 / 2 : ℂ) * t ^ 8 * c ^ 5 * z ^ 7 + (-37517 / 8 : ℂ) * t ^ 8 * c ^ 5 * z ^ 5 + (-40047 / 32 : ℂ) * t ^ 8 * c ^ 5 * z ^ 3 + (80683 / 128 : ℂ) * t ^ 8 * c ^ 5 * z + (806 : ℂ) * t ^ 8 * c ^ 3 * z ^ 9 + (7765 / 2 : ℂ) * t ^ 8 * c ^ 3 * z ^ 7 + (74751 / 8 : ℂ) * t ^ 8 * c ^ 3 * z ^ 5 + (-152435 / 32 : ℂ) * t ^ 8 * c ^ 3 * z ^ 3 + (247207 / 128 : ℂ) * t ^ 8 * c ^ 3 * z + (-598 : ℂ) * t ^ 8 * c * z ^ 9 + (5911 : ℂ) * t ^ 8 * c * z ^ 7 + (79413 / 4 : ℂ) * t ^ 8 * c * z ^ 5 + (-13981 / 16 : ℂ) * t ^ 8 * c * z ^ 3 + (337661 / 64 : ℂ) * t ^ 8 * c * z + (60 : ℂ) * t ^ 7 * c ^ 8 * z ^ 9 + (-208 : ℂ) * t ^ 7 * c ^ 8 * z ^ 7 + (158 : ℂ) * t ^ 7 * c ^ 8 * z ^ 5 + (-86 : ℂ) * t ^ 7 * c ^ 8 * z ^ 3 + (313 / 8 : ℂ) * t ^ 7 * c ^ 8 * z + (32 : ℂ) * t ^ 7 * c ^ 6 * z ^ 9 + (2172 : ℂ) * t ^ 7 * c ^ 6 * z ^ 7 + (2605 : ℂ) * t ^ 7 * c ^ 6 * z ^ 5 + (15 / 4 : ℂ) * t ^ 7 * c ^ 6 * z ^ 3 + (-967 / 16 : ℂ) * t ^ 7 * c ^ 6 * z + (-580 : ℂ) * t ^ 7 * c ^ 4 * z ^ 9 + (-4055 : ℂ) * t ^ 7 * c ^ 4 * z ^ 7 + (-8441 / 4 : ℂ) * t ^ 7 * c ^ 4 * z ^ 5 + (17349 / 16 : ℂ) * t ^ 7 * c ^ 4 * z ^ 3 + (-17137 / 64 : ℂ) * t ^ 7 * c ^ 4 * z + (884 : ℂ) * t ^ 7 * c ^ 2 * z ^ 9 + (-3644 : ℂ) * t ^ 7 * c ^ 2 * z ^ 7 + (-8453 : ℂ) * t ^ 7 * c ^ 2 * z ^ 5 + (-21587 / 4 : ℂ) * t ^ 7 * c ^ 2 * z ^ 3 + (55043 / 16 : ℂ) * t ^ 7 * c ^ 2 * z + (-32 : ℂ) * t ^ 7 * z ^ 9 + (912 : ℂ) * t ^ 7 * z ^ 7 + (3888 : ℂ) * t ^ 7 * z ^ 5 + (-7347 : ℂ) * t ^ 7 * z ^ 3 + (3471 / 4 : ℂ) * t ^ 7 * z + (73 / 2 : ℂ) * t ^ 6 * c ^ 9 * z ^ 7 + (-245 / 8 : ℂ) * t ^ 6 * c ^ 9 * z ^ 5 + (593 / 32 : ℂ) * t ^ 6 * c ^ 9 * z ^ 3 + (-1181 / 128 : ℂ) * t ^ 6 * c ^ 9 * z + (134 : ℂ) * t ^ 6 * c ^ 7 * z ^ 9 + (-619 / 2 : ℂ) * t ^ 6 * c ^ 7 * z ^ 7 + (-1097 / 8 : ℂ) * t ^ 6 * c ^ 7 * z ^ 5 + (2957 / 32 : ℂ) * t ^ 6 * c ^ 7 * z ^ 3 + (-6017 / 128 : ℂ) * t ^ 6 * c ^ 7 * z + (494 : ℂ) * t ^ 6 * c ^ 5 * z ^ 9 + (5927 / 2 : ℂ) * t ^ 6 * c ^ 5 * z ^ 7 + (7573 / 8 : ℂ) * t ^ 6 * c ^ 5 * z ^ 5 + (10159 / 32 : ℂ) * t ^ 6 * c ^ 5 * z ^ 3 + (-10211 / 128 : ℂ) * t ^ 6 * c ^ 5 * z + (-602 : ℂ) * t ^ 6 * c ^ 3 * z ^ 9 + (-99 / 2 : ℂ) * t ^ 6 * c ^ 3 * z ^ 7 + (-21821 / 8 : ℂ) * t ^ 6 * c ^ 3 * z ^ 5 + (56717 / 32 : ℂ) * t ^ 6 * c ^ 3 * z ^ 3 + (-80093 / 128 : ℂ) * t ^ 6 * c ^ 3 * z + (136 : ℂ) * t ^ 6 * c * z ^ 9 + (-2212 : ℂ) * t ^ 6 * c * z ^ 7 + (-9712 : ℂ) * t ^ 6 * c * z ^ 5 + (4451 / 2 : ℂ) * t ^ 6 * c * z ^ 3 + (-21587 / 8 : ℂ) * t ^ 6 * c * z + (-28 : ℂ) * t ^ 5 * c ^ 8 * z ^ 9 + (106 : ℂ) * t ^ 5 * c ^ 8 * z ^ 7 + (-93 / 2 : ℂ) * t ^ 5 * c ^ 8 * z ^ 5 + (141 / 8 : ℂ) * t ^ 5 * c ^ 8 * z ^ 3 + (-197 / 32 : ℂ) * t ^ 5 * c ^ 8 * z + (-200 : ℂ) * t ^ 5 * c ^ 6 * z ^ 9 + (-1184 : ℂ) * t ^ 5 * c ^ 6 * z ^ 7 + (-920 : ℂ) * t ^ 5 * c ^ 6 * z ^ 5 + (-119 / 2 : ℂ) * t ^ 5 * c ^ 6 * z ^ 3 + (32 : ℂ) * t ^ 5 * c ^ 6 * z + (208 : ℂ) * t ^ 5 * c ^ 4 * z ^ 9 + (865 : ℂ) * t ^ 5 * c ^ 4 * z ^ 7 + (2827 / 4 : ℂ) * t ^ 5 * c ^ 4 * z ^ 5 + (-8203 / 16 : ℂ) * t ^ 5 * c ^ 4 * z ^ 3 + (6635 / 64 : ℂ) * t ^ 5 * c ^ 4 * z + (-224 : ℂ) * t ^ 5 * c ^ 2 * z ^ 9 + (1688 : ℂ) * t ^ 5 * c ^ 2 * z ^ 7 + (5948 : ℂ) * t ^ 5 * c ^ 2 * z ^ 5 + (2091 : ℂ) * t ^ 5 * c ^ 2 * z ^ 3 + (-4027 / 4 : ℂ) * t ^ 5 * c ^ 2 * z + (-128 : ℂ) * t ^ 5 * z ^ 7 + (-936 : ℂ) * t ^ 5 * z ^ 5 + (2832 : ℂ) * t ^ 5 * z ^ 3 + (-219 : ℂ) * t ^ 5 * z + (-43 / 2 : ℂ) * t ^ 4 * c ^ 9 * z ^ 7 + (87 / 8 : ℂ) * t ^ 4 * c ^ 9 * z ^ 5 + (-147 / 32 : ℂ) * t ^ 4 * c ^ 9 * z ^ 3 + (223 / 128 : ℂ) * t ^ 4 * c ^ 9 * z + (10 : ℂ) * t ^ 4 * c ^ 7 * z ^ 9 + (251 / 2 : ℂ) * t ^ 4 * c ^ 7 * z ^ 7 + (465 / 8 : ℂ) * t ^ 4 * c ^ 7 * z ^ 5 + (-765 / 32 : ℂ) * t ^ 4 * c ^ 7 * z ^ 3 + (1129 / 128 : ℂ) * t ^ 4 * c ^ 7 * z + (-74 : ℂ) * t ^ 4 * c ^ 5 * z ^ 9 + (-1525 / 2 : ℂ) * t ^ 4 * c ^ 5 * z ^ 7 + (893 / 8 : ℂ) * t ^ 4 * c ^ 5 * z ^ 5 + (-13 / 32 : ℂ) * t ^ 4 * c ^ 5 * z ^ 3 + (-1619 / 128 : ℂ) * t ^ 4 * c ^ 5 * z + (176 : ℂ) * t ^ 4 * c ^ 3 * z ^ 9 + (-394 : ℂ) * t ^ 4 * c ^ 3 * z ^ 7 + (-315 / 2 : ℂ) * t ^ 4 * c ^ 3 * z ^ 5 + (-3445 / 8 : ℂ) * t ^ 4 * c ^ 3 * z ^ 3 + (4645 / 32 : ℂ) * t ^ 4 * c ^ 3 * z + (320 : ℂ) * t ^ 4 * c * z ^ 7 + (2550 : ℂ) * t ^ 4 * c * z ^ 5 + (-1384 : ℂ) * t ^ 4 * c * z ^ 3 + (872 : ℂ) * t ^ 4 * c * z + (4 : ℂ) * t ^ 3 * c ^ 8 * z ^ 9 + (-20 : ℂ) * t ^ 3 * c ^ 8 * z ^ 7 + (6 : ℂ) * t ^ 3 * c ^ 8 * z ^ 5 + (-7 / 4 : ℂ) * t ^ 3 * c ^ 8 * z ^ 3 + (1 / 2 : ℂ) * t ^ 3 * c ^ 8 * z + (36 : ℂ) * t ^ 3 * c ^ 6 * z ^ 9 + (362 : ℂ) * t ^ 3 * c ^ 6 * z ^ 7 + (351 / 2 : ℂ) * t ^ 3 * c ^ 6 * z ^ 5 + (137 / 8 : ℂ) * t ^ 3 * c ^ 6 * z ^ 3 + (-185 / 32 : ℂ) * t ^ 3 * c ^ 6 * z + (-64 : ℂ) * t ^ 3 * c ^ 4 * z ^ 9 + (-16 : ℂ) * t ^ 3 * c ^ 4 * z ^ 7 + (-150 : ℂ) * t ^ 3 * c ^ 4 * z ^ 5 + (199 / 2 : ℂ) * t ^ 3 * c ^ 4 * z ^ 3 + (-119 / 8 : ℂ) * t ^ 3 * c ^ 4 * z + (-256 : ℂ) * t ^ 3 * c ^ 2 * z ^ 7 + (-1852 : ℂ) * t ^ 3 * c ^ 2 * z ^ 5 + (-484 : ℂ) * t ^ 3 * c ^ 2 * z ^ 3 + (169 : ℂ) * t ^ 3 * c ^ 2 * z + (96 : ℂ) * t ^ 3 * z ^ 5 + (-640 : ℂ) * t ^ 3 * z ^ 3 + (24 : ℂ) * t ^ 3 * z + (11 / 2 : ℂ) * t ^ 2 * c ^ 9 * z ^ 7 + (-15 / 8 : ℂ) * t ^ 2 * c ^ 9 * z ^ 5 + (19 / 32 : ℂ) * t ^ 2 * c ^ 9 * z ^ 3 + (-23 / 128 : ℂ) * t ^ 2 * c ^ 9 * z + (-6 : ℂ) * t ^ 2 * c ^ 7 * z ^ 9 + (-85 / 2 : ℂ) * t ^ 2 * c ^ 7 * z ^ 7 + (-75 / 8 : ℂ) * t ^ 2 * c ^ 7 * z ^ 5 + (91 / 32 : ℂ) * t ^ 2 * c ^ 7 * z ^ 3 + (-107 / 128 : ℂ) * t ^ 2 * c ^ 7 * z + (8 : ℂ) * t ^ 2 * c ^ 5 * z ^ 9 + (56 : ℂ) * t ^ 2 * c ^ 5 * z ^ 7 + (-91 : ℂ) * t ^ 2 * c ^ 5 * z ^ 5 + (-51 / 4 : ℂ) * t ^ 2 * c ^ 5 * z ^ 3 + (75 / 16 : ℂ) * t ^ 2 * c ^ 5 * z + (64 : ℂ) * t ^ 2 * c ^ 3 * z ^ 7 + (282 : ℂ) * t ^ 2 * c ^ 3 * z ^ 5 + (143 / 2 : ℂ) * t ^ 2 * c ^ 3 * z ^ 3 + (-175 / 8 : ℂ) * t ^ 2 * c ^ 3 * z + (-280 : ℂ) * t ^ 2 * c * z ^ 5 + (408 : ℂ) * t ^ 2 * c * z ^ 3 + (-158 : ℂ) * t ^ 2 * c * z + (1 : ℂ) * t * c ^ 8 * z ^ 7 + (-1 / 4 : ℂ) * t * c ^ 8 * z ^ 5 + (1 / 16 : ℂ) * t * c ^ 8 * z ^ 3 + (-1 / 64 : ℂ) * t * c ^ 8 * z + (-40 : ℂ) * t * c ^ 6 * z ^ 7 + (-14 : ℂ) * t * c ^ 6 * z ^ 5 + (-3 / 2 : ℂ) * t * c ^ 6 * z ^ 3 + (3 / 8 : ℂ) * t * c ^ 6 * z + (16 : ℂ) * t * c ^ 4 * z ^ 5 + (-7 : ℂ) * t * c ^ 4 * z ^ 3 + (3 / 4 : ℂ) * t * c ^ 4 * z + (224 : ℂ) * t * c ^ 2 * z ^ 5 + (48 : ℂ) * t * c ^ 2 * z ^ 3 + (-12 : ℂ) * t * c ^ 2 * z + (64 : ℂ) * t * z ^ 3 + (-1 / 2 : ℂ) * c ^ 9 * z ^ 7 + (1 / 8 : ℂ) * c ^ 9 * z ^ 5 + (-1 / 32 : ℂ) * c ^ 9 * z ^ 3 + (1 / 128 : ℂ) * c ^ 9 * z + (6 : ℂ) * c ^ 7 * z ^ 7 + (1 / 2 : ℂ) * c ^ 7 * z ^ 5 + (-1 / 8 : ℂ) * c ^ 7 * z ^ 3 + (1 / 32 : ℂ) * c ^ 7 * z + (12 : ℂ) * c ^ 5 * z ^ 5 + (3 / 2 : ℂ) * c ^ 5 * z ^ 3 + (-3 / 8 : ℂ) * c ^ 5 * z + (-48 : ℂ) * c ^ 3 * z ^ 5 + (-6 : ℂ) * c ^ 3 * z ^ 3 + (3 / 2 : ℂ) * c ^ 3 * z + (-48 : ℂ) * c * z ^ 3 + (12 : ℂ) * c * z) * hz

set_option maxHeartbeats 1000000 in
private lemma NUM3_eq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NUMdef τ c 3 = NUMP3 (τ : ℂ) c (xiτ τ) (vτ τ : ℂ) (Pc τ c) (Qc τ c) /
      (Qc τ c * (((vτ τ : ℂ) + τ * xiτ τ) * ((vτ τ : ℂ) - τ * xiτ τ)) ^ 2 *
        (((vτ τ : ℂ) - (c - τ) * xiτ τ) * ((vτ τ : ℂ) + (c - τ) * xiτ τ)) ^ 4) := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  have hb1 := one_add_beta_ne τ h1 h2 _ hxi
  have hb2 := one_add_beta_ne τ h1 h2 _ hxi'
  have hQ := Qc_ne τ h1 h2.le c hc
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  obtain ⟨hAp, hAm, hLp, hLm⟩ := factors_ne τ h1 h2 c hc
  unfold NUMdef dPiJf
  rw [deriv_aJ τ 3 _ hb1, deriv_aJ τ 3 _ hb2]
  unfold aJ PiJ NUMP3
  simp only [Nat.cast_ofNat, Int.reduceSub, zpow_neg, zpow_ofNat]
  rw [hβC, hνC, fA (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0, fA' (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0,
    fL (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0, fL' (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0]
  generalize (vτ τ : ℂ) + τ * xiτ τ = Ap at *
  generalize (vτ τ : ℂ) - τ * xiτ τ = Am at *
  generalize (vτ τ : ℂ) - (c - τ) * xiτ τ = Lp at *
  generalize (vτ τ : ℂ) + (c - τ) * xiτ τ = Lm at *
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hQ (pow_ne_zero _ (mul_ne_zero hAp hAm)))
    (pow_ne_zero _ (mul_ne_zero hLp hLm)))]
  field_simp
  ring

/-- The closed form of `T_3`. -/
private lemma TJ3_closed (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    TJ τ c 3 = Nc3 τ c / (((256 * Kt τ ^ 2 : ℝ) : ℂ) * Qc τ c ^ 2) := by
  have hz : xiτ τ ^ 2 = (τ : ℂ) ^ 2 - 1 / 4 := by
    rw [xi_sq τ h1 h2]
    unfold ysq
    push_cast
    ring
  have hvd : (vτ τ : ℂ) = 1 - (τ : ℂ) ^ 2 := by
    unfold vτ
    push_cast
    ring
  have hsd : (ysq τ : ℂ) = 1 / 4 - (τ : ℂ) ^ 2 := by
    unfold ysq
    push_cast
    ring
  have hs0 : (ysq τ : ℂ) ≠ 0 := by exact_mod_cast (ysq_pos τ h1 h2).ne'
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  have hz0 := xi_ne τ h1 h2
  have hQ0 := Qc_ne τ h1 h2.le c hc
  rw [Qc_C, QcC_F] at hQ0
  have hF1 : F1p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hF2 : F2p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hW0 : (4 - 7 * (τ : ℂ) ^ 2) ≠ 0 := by
    have h47 : (4 : ℝ) - 7 * τ ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast h47
  rw [TJ_eq τ h1 h2 3 c hc, TJf_eq, NUM3_eq τ h1 h2 c hc, DEN_eq τ h1 h2 c hc, Pc_C, Qc_C,
    core3 (τ : ℂ) c (xiτ τ) _ _ hz hvd hsd, relAA _ _ _ hz hvd, relLL _ _ _ _ hz hvd,
    relX _ _ _ _ hz hvd, Nc3_C, QcC_F]
  rw [show ((256 * Kt τ ^ 2 : ℝ) : ℂ) = 256 * (-(4 - 7 * (τ : ℂ) ^ 2)) ^ 2 by unfold Kt; push_cast; ring]
  generalize F1p (τ : ℂ) c = F1 at *
  generalize F2p (τ : ℂ) c = F2 at *
  generalize Ncp3 (τ : ℂ) c = N at *
  generalize (4 - 7 * (τ : ℂ) ^ 2) = W at *
  generalize xiτ τ = z at *
  generalize (vτ τ : ℂ) = v at *
  generalize (ysq τ : ℂ) = s at *
  field_simp
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The ξ-elimination for `T_4`: `NUMP4 ≡ ` its closed form modulo `ξ² = τ² - 1/4`. -/
private lemma core4 (t c z v s : ℂ) (hz : z ^ 2 = t ^ 2 - 1 / 4) (hv : v = 1 - t ^ 2) (hs : s = 1 / 4 - t ^ 2) :
    NUMP4 t c z v (PcC t c) (QcC t c) = Ncp4 t c * s * F2p t c * v ^ 2 * z / 32768 := by
  subst hv hs
  unfold NUMP4 PcC QcC Ncp4 F2p
  linear_combination ((-320 : ℂ) * t ^ 24 * c ^ 4 * z + (-336 : ℂ) * t ^ 24 * c ^ 2 * z + (352 : ℂ) * t ^ 23 * c ^ 5 * z + (-208 : ℂ) * t ^ 23 * c ^ 3 * z ^ 5 + (2128 : ℂ) * t ^ 23 * c ^ 3 * z + (348 : ℂ) * t ^ 23 * c * z ^ 5 + (686 : ℂ) * t ^ 23 * c * z + (96 : ℂ) * t ^ 22 * c ^ 6 * z + (240 : ℂ) * t ^ 22 * c ^ 4 * z ^ 5 + (-320 : ℂ) * t ^ 22 * c ^ 4 * z ^ 3 + (-648 : ℂ) * t ^ 22 * c ^ 4 * z + (-228 : ℂ) * t ^ 22 * c ^ 2 * z ^ 5 + (-336 : ℂ) * t ^ 22 * c ^ 2 * z ^ 3 + (-1096 : ℂ) * t ^ 22 * c ^ 2 * z + (-308 : ℂ) * t ^ 22 * z ^ 5 + (-343 : ℂ) * t ^ 22 * z + (-272 : ℂ) * t ^ 21 * c ^ 7 * z + (-72 : ℂ) * t ^ 21 * c ^ 5 * z ^ 5 + (352 : ℂ) * t ^ 21 * c ^ 5 * z ^ 3 + (-1176 : ℂ) * t ^ 21 * c ^ 5 * z + (-272 : ℂ) * t ^ 21 * c ^ 3 * z ^ 7 + (1904 : ℂ) * t ^ 21 * c ^ 3 * z ^ 5 + (2128 : ℂ) * t ^ 21 * c ^ 3 * z ^ 3 + (-9063 : ℂ) * t ^ 21 * c ^ 3 * z + (332 : ℂ) * t ^ 21 * c * z ^ 7 + (-6105 / 2 : ℂ) * t ^ 21 * c * z ^ 5 + (686 : ℂ) * t ^ 21 * c * z ^ 3 + (-6027 / 2 : ℂ) * t ^ 21 * c * z + (124 : ℂ) * t ^ 20 * c ^ 8 * z + (96 : ℂ) * t ^ 20 * c ^ 6 * z ^ 3 + (-221 : ℂ) * t ^ 20 * c ^ 6 * z + (704 : ℂ) * t ^ 20 * c ^ 4 * z ^ 7 + (-2516 : ℂ) * t ^ 20 * c ^ 4 * z ^ 5 + (-728 : ℂ) * t ^ 20 * c ^ 4 * z ^ 3 + (31863 / 4 : ℂ) * t ^ 20 * c ^ 4 * z + (-744 : ℂ) * t ^ 20 * c ^ 2 * z ^ 7 + (1812 : ℂ) * t ^ 20 * c ^ 2 * z ^ 5 + (-1180 : ℂ) * t ^ 20 * c ^ 2 * z ^ 3 + (190185 / 16 : ℂ) * t ^ 20 * c ^ 2 * z + (-322 : ℂ) * t ^ 20 * z ^ 7 + (5987 / 2 : ℂ) * t ^ 20 * z ^ 5 + (-343 : ℂ) * t ^ 20 * z ^ 3 + (71295 / 32 : ℂ) * t ^ 20 * z + (-18 : ℂ) * t ^ 19 * c ^ 9 * z + (-272 : ℂ) * t ^ 19 * c ^ 7 * z ^ 3 + (1131 : ℂ) * t ^ 19 * c ^ 7 * z + (-656 : ℂ) * t ^ 19 * c ^ 5 * z ^ 7 + (1018 : ℂ) * t ^ 19 * c ^ 5 * z ^ 5 + (-1088 : ℂ) * t ^ 19 * c ^ 5 * z ^ 3 + (468 : ℂ) * t ^ 19 * c ^ 5 * z + (400 : ℂ) * t ^ 19 * c ^ 3 * z ^ 9 + (2372 : ℂ) * t ^ 19 * c ^ 3 * z ^ 7 + (-5652 : ℂ) * t ^ 19 * c ^ 3 * z ^ 5 + (-8531 : ℂ) * t ^ 19 * c ^ 3 * z ^ 3 + (222069 / 16 : ℂ) * t ^ 19 * c ^ 3 * z + (-620 : ℂ) * t ^ 19 * c * z ^ 9 + (-1307 : ℂ) * t ^ 19 * c * z ^ 7 + (98251 / 8 : ℂ) * t ^ 19 * c * z ^ 5 + (-2842 : ℂ) * t ^ 19 * c * z ^ 3 + (572425 / 128 : ℂ) * t ^ 19 * c * z + (124 : ℂ) * t ^ 18 * c ^ 8 * z ^ 3 + (-537 : ℂ) * t ^ 18 * c ^ 8 * z + (256 : ℂ) * t ^ 18 * c ^ 6 * z ^ 7 + (96 : ℂ) * t ^ 18 * c ^ 6 * z ^ 5 + (-197 : ℂ) * t ^ 18 * c ^ 6 * z ^ 3 + (249 / 2 : ℂ) * t ^ 18 * c ^ 6 * z + (-1360 : ℂ) * t ^ 18 * c ^ 4 * z ^ 9 + (-5084 : ℂ) * t ^ 18 * c ^ 4 * z ^ 7 + (8150 : ℂ) * t ^ 18 * c ^ 4 * z ^ 5 + (31135 / 4 : ℂ) * t ^ 18 * c ^ 4 * z ^ 3 + (-331563 / 16 : ℂ) * t ^ 18 * c ^ 4 * z + (1660 : ℂ) * t ^ 18 * c ^ 2 * z ^ 9 + (3689 : ℂ) * t ^ 18 * c ^ 2 * z ^ 7 + (-10312 : ℂ) * t ^ 18 * c ^ 2 * z ^ 5 + (185465 / 16 : ℂ) * t ^ 18 * c ^ 2 * z ^ 3 + (-68159 / 2 : ℂ) * t ^ 18 * c ^ 2 * z + (560 : ℂ) * t ^ 18 * z ^ 9 + (4463 / 2 : ℂ) * t ^ 18 * z ^ 7 + (-107289 / 8 : ℂ) * t ^ 18 * z ^ 5 + (68551 / 32 : ℂ) * t ^ 18 * z ^ 3 + (-851165 / 128 : ℂ) * t ^ 18 * z + (-18 : ℂ) * t ^ 17 * c ^ 9 * z ^ 3 + (153 / 2 : ℂ) * t ^ 17 * c ^ 9 * z + (-32 : ℂ) * t ^ 17 * c ^ 7 * z ^ 7 + (-272 : ℂ) * t ^ 17 * c ^ 7 * z ^ 5 + (1063 : ℂ) * t ^ 17 * c ^ 7 * z ^ 3 + (-2016 : ℂ) * t ^ 17 * c ^ 7 * z + (1784 : ℂ) * t ^ 17 * c ^ 5 * z ^ 9 + (4714 : ℂ) * t ^ 17 * c ^ 5 * z ^ 7 + (-3754 : ℂ) * t ^ 17 * c ^ 5 * z ^ 5 + (196 : ℂ) * t ^ 17 * c ^ 5 * z ^ 3 + (13389 / 4 : ℂ) * t ^ 17 * c ^ 5 * z + (80 : ℂ) * t ^ 17 * c ^ 3 * z ^ 11 + (-3384 : ℂ) * t ^ 17 * c ^ 3 * z ^ 9 + (-6545 : ℂ) * t ^ 17 * c ^ 3 * z ^ 7 + (10661 : ℂ) * t ^ 17 * c ^ 3 * z ^ 5 + (187945 / 16 : ℂ) * t ^ 17 * c ^ 3 * z ^ 3 + (-143457 / 32 : ℂ) * t ^ 17 * c ^ 3 * z + (-60 : ℂ) * t ^ 17 * c * z ^ 11 + (3495 / 2 : ℂ) * t ^ 17 * c * z ^ 9 + (2945 / 8 : ℂ) * t ^ 17 * c * z ^ 7 + (-866197 / 32 : ℂ) * t ^ 17 * c * z ^ 5 + (481481 / 128 : ℂ) * t ^ 17 * c * z ^ 3 + (128499 / 512 : ℂ) * t ^ 17 * c * z + (124 : ℂ) * t ^ 16 * c ^ 8 * z ^ 5 + (-506 : ℂ) * t ^ 16 * c ^ 8 * z ^ 3 + (981 : ℂ) * t ^ 16 * c ^ 8 * z + (-1152 : ℂ) * t ^ 16 * c ^ 6 * z ^ 9 + (-1664 : ℂ) * t ^ 16 * c ^ 6 * z ^ 7 + (-173 : ℂ) * t ^ 16 * c ^ 6 * z ^ 5 + (301 / 4 : ℂ) * t ^ 16 * c ^ 6 * z ^ 3 + (-711 / 8 : ℂ) * t ^ 16 * c ^ 6 * z + (-352 : ℂ) * t ^ 16 * c ^ 4 * z ^ 11 + (7080 : ℂ) * t ^ 16 * c ^ 4 * z ^ 9 + (12798 : ℂ) * t ^ 16 * c ^ 4 * z ^ 7 + (-55281 / 4 : ℂ) * t ^ 16 * c ^ 4 * z ^ 5 + (-75107 / 4 : ℂ) * t ^ 16 * c ^ 4 * z ^ 3 + (1763775 / 64 : ℂ) * t ^ 16 * c ^ 4 * z + (144 : ℂ) * t ^ 16 * c ^ 2 * z ^ 11 + (-7815 : ℂ) * t ^ 16 * c ^ 2 * z ^ 9 + (-31939 / 4 : ℂ) * t ^ 16 * c ^ 2 * z ^ 7 + (538681 / 16 : ℂ) * t ^ 16 * c ^ 2 * z ^ 5 + (-1995623 / 64 : ℂ) * t ^ 16 * c ^ 2 * z ^ 3 + (13420893 / 256 : ℂ) * t ^ 16 * c ^ 2 * z + (70 : ℂ) * t ^ 16 * z ^ 11 + (-3155 : ℂ) * t ^ 16 * z ^ 9 + (-27227 / 4 : ℂ) * t ^ 16 * z ^ 7 + (572311 / 16 : ℂ) * t ^ 16 * z ^ 5 + (-391307 / 64 : ℂ) * t ^ 16 * z ^ 3 + (3090063 / 256 : ℂ) * t ^ 16 * z + (-18 : ℂ) * t ^ 15 * c ^ 9 * z ^ 5 + (72 : ℂ) * t ^ 15 * c ^ 9 * z ^ 3 + (-531 / 4 : ℂ) * t ^ 15 * c ^ 9 * z + (400 : ℂ) * t ^ 15 * c ^ 7 * z ^ 9 + (-40 : ℂ) * t ^ 15 * c ^ 7 * z ^ 7 + (995 : ℂ) * t ^ 15 * c ^ 7 * z ^ 5 + (-7001 / 4 : ℂ) * t ^ 15 * c ^ 7 * z ^ 3 + (17193 / 8 : ℂ) * t ^ 15 * c ^ 7 * z + (608 : ℂ) * t ^ 15 * c ^ 5 * z ^ 11 + (-8976 : ℂ) * t ^ 15 * c ^ 5 * z ^ 9 + (-13038 : ℂ) * t ^ 15 * c ^ 5 * z ^ 7 + (6642 : ℂ) * t ^ 15 * c ^ 5 * z ^ 5 + (13585 / 4 : ℂ) * t ^ 15 * c ^ 5 * z ^ 3 + (-113625 / 16 : ℂ) * t ^ 15 * c ^ 5 * z + (-188 : ℂ) * t ^ 15 * c ^ 3 * z ^ 11 + (12409 : ℂ) * t ^ 15 * c ^ 3 * z ^ 9 + (36831 / 4 : ℂ) * t ^ 15 * c ^ 3 * z ^ 7 + (-308691 / 16 : ℂ) * t ^ 15 * c ^ 3 * z ^ 5 + (-98969 / 64 : ℂ) * t ^ 15 * c ^ 3 * z ^ 3 + (-3970251 / 256 : ℂ) * t ^ 15 * c ^ 3 * z + (-68 : ℂ) * t ^ 15 * c * z ^ 11 + (4085 / 2 : ℂ) * t ^ 15 * c * z ^ 9 + (64855 / 8 : ℂ) * t ^ 15 * c * z ^ 7 + (1033357 / 32 : ℂ) * t ^ 15 * c * z ^ 5 + (152495 / 128 : ℂ) * t ^ 15 * c * z ^ 3 + (-5380155 / 512 : ℂ) * t ^ 15 * c * z + (-80 : ℂ) * t ^ 14 * c ^ 8 * z ^ 9 + (124 : ℂ) * t ^ 14 * c ^ 8 * z ^ 7 + (-475 : ℂ) * t ^ 14 * c ^ 8 * z ^ 5 + (1709 / 2 : ℂ) * t ^ 14 * c ^ 8 * z ^ 3 + (-8133 / 8 : ℂ) * t ^ 14 * c ^ 8 * z + (-512 : ℂ) * t ^ 14 * c ^ 6 * z ^ 11 + (6068 : ℂ) * t ^ 14 * c ^ 6 * z ^ 9 + (4979 : ℂ) * t ^ 14 * c ^ 6 * z ^ 7 + (32 : ℂ) * t ^ 14 * c ^ 6 * z ^ 5 + (-1121 / 16 : ℂ) * t ^ 14 * c ^ 6 * z ^ 3 + (579 / 2 : ℂ) * t ^ 14 * c ^ 6 * z + (616 : ℂ) * t ^ 14 * c ^ 4 * z ^ 11 + (-17013 : ℂ) * t ^ 14 * c ^ 4 * z ^ 9 + (-56457 / 4 : ℂ) * t ^ 14 * c ^ 4 * z ^ 7 + (258667 / 16 : ℂ) * t ^ 14 * c ^ 4 * z ^ 5 + (1463347 / 64 : ℂ) * t ^ 14 * c ^ 4 * z ^ 3 + (-5599737 / 256 : ℂ) * t ^ 14 * c ^ 4 * z + (-134 : ℂ) * t ^ 14 * c ^ 2 * z ^ 11 + (22385 / 2 : ℂ) * t ^ 14 * c ^ 2 * z ^ 9 + (59043 / 8 : ℂ) * t ^ 14 * c ^ 2 * z ^ 7 + (-2057303 / 32 : ℂ) * t ^ 14 * c ^ 2 * z ^ 5 + (5712635 / 128 : ℂ) * t ^ 14 * c ^ 2 * z ^ 3 + (-25461999 / 512 : ℂ) * t ^ 14 * c ^ 2 * z + (-250 : ℂ) * t ^ 14 * z ^ 11 + (7255 : ℂ) * t ^ 14 * z ^ 9 + (47009 / 4 : ℂ) * t ^ 14 * z ^ 7 + (-998749 / 16 : ℂ) * t ^ 14 * z ^ 5 + (674689 / 64 : ℂ) * t ^ 14 * z ^ 3 + (-3796533 / 256 : ℂ) * t ^ 14 * z + (8 : ℂ) * t ^ 13 * c ^ 9 * z ^ 9 + (-18 : ℂ) * t ^ 13 * c ^ 9 * z ^ 7 + (135 / 2 : ℂ) * t ^ 13 * c ^ 9 * z ^ 5 + (-459 / 4 : ℂ) * t ^ 13 * c ^ 9 * z ^ 3 + (1953 / 16 : ℂ) * t ^ 13 * c ^ 9 * z + (208 : ℂ) * t ^ 13 * c ^ 7 * z ^ 11 + (-2288 : ℂ) * t ^ 13 * c ^ 7 * z ^ 9 + (199 : ℂ) * t ^ 13 * c ^ 7 * z ^ 7 + (-3003 / 2 : ℂ) * t ^ 13 * c ^ 7 * z ^ 5 + (27385 / 16 : ℂ) * t ^ 13 * c ^ 7 * z ^ 3 + (-13203 / 8 : ℂ) * t ^ 13 * c ^ 7 * z + (-1364 : ℂ) * t ^ 13 * c ^ 5 * z ^ 11 + (18960 : ℂ) * t ^ 13 * c ^ 5 * z ^ 9 + (17568 : ℂ) * t ^ 13 * c ^ 5 * z ^ 7 + (-28805 / 4 : ℂ) * t ^ 13 * c ^ 5 * z ^ 5 + (-12505 / 2 : ℂ) * t ^ 13 * c ^ 5 * z ^ 3 + (452241 / 64 : ℂ) * t ^ 13 * c ^ 5 * z + (-40 : ℂ) * t ^ 13 * c ^ 3 * z ^ 11 + (-21463 : ℂ) * t ^ 13 * c ^ 3 * z ^ 9 + (-32529 / 4 : ℂ) * t ^ 13 * c ^ 3 * z ^ 7 + (503461 / 16 : ℂ) * t ^ 13 * c ^ 3 * z ^ 5 + (-1017305 / 64 : ℂ) * t ^ 13 * c ^ 3 * z ^ 3 + (7231869 / 256 : ℂ) * t ^ 13 * c ^ 3 * z + (740 : ℂ) * t ^ 13 * c * z ^ 11 + (-27665 / 2 : ℂ) * t ^ 13 * c * z ^ 9 + (-182635 / 8 : ℂ) * t ^ 13 * c * z ^ 7 + (-416913 / 32 : ℂ) * t ^ 13 * c * z ^ 5 + (-1306915 / 128 : ℂ) * t ^ 13 * c * z ^ 3 + (9000951 / 512 : ℂ) * t ^ 13 * c * z + (-32 : ℂ) * t ^ 12 * c ^ 8 * z ^ 11 + (520 : ℂ) * t ^ 12 * c ^ 8 * z ^ 9 + (-444 : ℂ) * t ^ 12 * c ^ 8 * z ^ 7 + (2943 / 4 : ℂ) * t ^ 12 * c ^ 8 * z ^ 5 + (-803 : ℂ) * t ^ 12 * c ^ 8 * z ^ 3 + (44343 / 64 : ℂ) * t ^ 12 * c ^ 8 * z + (1376 : ℂ) * t ^ 12 * c ^ 6 * z ^ 11 + (-12737 : ℂ) * t ^ 12 * c ^ 6 * z ^ 9 + (-32501 / 4 : ℂ) * t ^ 12 * c ^ 6 * z ^ 7 + (-993 / 16 : ℂ) * t ^ 12 * c ^ 6 * z ^ 5 + (17407 / 64 : ℂ) * t ^ 12 * c ^ 6 * z ^ 3 + (-65637 / 256 : ℂ) * t ^ 12 * c ^ 6 * z + (290 : ℂ) * t ^ 12 * c ^ 4 * z ^ 11 + (47031 / 2 : ℂ) * t ^ 12 * c ^ 4 * z ^ 9 + (35237 / 8 : ℂ) * t ^ 12 * c ^ 4 * z ^ 7 + (-500081 / 32 : ℂ) * t ^ 12 * c ^ 4 * z ^ 5 + (-2068195 / 128 : ℂ) * t ^ 12 * c ^ 4 * z ^ 3 + (5341767 / 512 : ℂ) * t ^ 12 * c ^ 4 * z + (-766 : ℂ) * t ^ 12 * c ^ 2 * z ^ 11 + (865 / 2 : ℂ) * t ^ 12 * c ^ 2 * z ^ 9 + (25915 / 8 : ℂ) * t ^ 12 * c ^ 2 * z ^ 7 + (2443113 / 32 : ℂ) * t ^ 12 * c ^ 2 * z ^ 5 + (-4937341 / 128 : ℂ) * t ^ 12 * c ^ 2 * z ^ 3 + (15062433 / 512 : ℂ) * t ^ 12 * c ^ 2 * z + (330 : ℂ) * t ^ 12 * z ^ 11 + (-8715 : ℂ) * t ^ 12 * z ^ 9 + (-49565 / 4 : ℂ) * t ^ 12 * z ^ 7 + (1188921 / 16 : ℂ) * t ^ 12 * z ^ 5 + (-780461 / 64 : ℂ) * t ^ 12 * z ^ 3 + (3328545 / 256 : ℂ) * t ^ 12 * z + (-60 : ℂ) * t ^ 11 * c ^ 9 * z ^ 9 + (63 : ℂ) * t ^ 11 * c ^ 9 * z ^ 7 + (-783 / 8 : ℂ) * t ^ 11 * c ^ 9 * z ^ 5 + (747 / 8 : ℂ) * t ^ 11 * c ^ 9 * z ^ 3 + (-8325 / 128 : ℂ) * t ^ 11 * c ^ 9 * z + (-628 : ℂ) * t ^ 11 * c ^ 7 * z ^ 11 + (4927 : ℂ) * t ^ 11 * c ^ 7 * z ^ 9 + (73 / 4 : ℂ) * t ^ 11 * c ^ 7 * z ^ 7 + (21379 / 16 : ℂ) * t ^ 11 * c ^ 7 * z ^ 5 + (-78239 / 64 : ℂ) * t ^ 11 * c ^ 7 * z ^ 3 + (250731 / 256 : ℂ) * t ^ 11 * c ^ 7 * z + (380 : ℂ) * t ^ 11 * c ^ 5 * z ^ 11 + (-21849 : ℂ) * t ^ 11 * c ^ 5 * z ^ 9 + (-43031 / 4 : ℂ) * t ^ 11 * c ^ 5 * z ^ 7 + (94931 / 16 : ℂ) * t ^ 11 * c ^ 5 * z ^ 5 + (352201 / 64 : ℂ) * t ^ 11 * c ^ 5 * z ^ 3 + (-1103253 / 256 : ℂ) * t ^ 11 * c ^ 5 * z + (704 : ℂ) * t ^ 11 * c ^ 3 * z ^ 11 + (15955 : ℂ) * t ^ 11 * c ^ 3 * z ^ 9 + (16513 / 4 : ℂ) * t ^ 11 * c ^ 3 * z ^ 7 + (-602893 / 16 : ℂ) * t ^ 11 * c ^ 3 * z ^ 5 + (1553641 / 64 : ℂ) * t ^ 11 * c ^ 3 * z ^ 3 + (-6400005 / 256 : ℂ) * t ^ 11 * c ^ 3 * z + (-1212 : ℂ) * t ^ 11 * c * z ^ 11 + (43895 / 2 : ℂ) * t ^ 11 * c * z ^ 9 + (243989 / 8 : ℂ) * t ^ 11 * c * z ^ 7 + (-614413 / 32 : ℂ) * t ^ 11 * c * z ^ 5 + (1923509 / 128 : ℂ) * t ^ 11 * c * z ^ 3 + (-7986525 / 512 : ℂ) * t ^ 11 * c * z + (104 : ℂ) * t ^ 10 * c ^ 8 * z ^ 11 + (-1187 : ℂ) * t ^ 10 * c ^ 8 * z ^ 9 + (2499 / 4 : ℂ) * t ^ 10 * c ^ 8 * z ^ 7 + (-9905 / 16 : ℂ) * t ^ 10 * c ^ 8 * z ^ 5 + (31495 / 64 : ℂ) * t ^ 10 * c ^ 8 * z ^ 3 + (-87525 / 256 : ℂ) * t ^ 10 * c ^ 8 * z + (-1002 : ℂ) * t ^ 10 * c ^ 6 * z ^ 11 + (27575 / 2 : ℂ) * t ^ 10 * c ^ 6 * z ^ 9 + (58181 / 8 : ℂ) * t ^ 10 * c ^ 6 * z ^ 7 + (8207 / 32 : ℂ) * t ^ 10 * c ^ 6 * z ^ 5 + (-24115 / 128 : ℂ) * t ^ 10 * c ^ 6 * z ^ 3 + (-1881 / 512 : ℂ) * t ^ 10 * c ^ 6 * z + (-1150 : ℂ) * t ^ 10 * c ^ 4 * z ^ 11 + (-36973 / 2 : ℂ) * t ^ 10 * c ^ 4 * z ^ 9 + (44817 / 8 : ℂ) * t ^ 10 * c ^ 4 * z ^ 7 + (398187 / 32 : ℂ) * t ^ 10 * c ^ 4 * z ^ 5 + (818393 / 128 : ℂ) * t ^ 10 * c ^ 4 * z ^ 3 + (-1196397 / 512 : ℂ) * t ^ 10 * c ^ 4 * z + (1662 : ℂ) * t ^ 10 * c ^ 2 * z ^ 11 + (-32485 / 2 : ℂ) * t ^ 10 * c ^ 2 * z ^ 9 + (-122783 / 8 : ℂ) * t ^ 10 * c ^ 2 * z ^ 7 + (-1837189 / 32 : ℂ) * t ^ 10 * c ^ 2 * z ^ 5 + (2531273 / 128 : ℂ) * t ^ 10 * c ^ 2 * z ^ 3 + (-4897293 / 512 : ℂ) * t ^ 10 * c ^ 2 * z + (-190 : ℂ) * t ^ 10 * z ^ 11 + (5765 : ℂ) * t ^ 10 * z ^ 9 + (32293 / 4 : ℂ) * t ^ 10 * z ^ 7 + (-976781 / 16 : ℂ) * t ^ 10 * z ^ 5 + (637021 / 64 : ℂ) * t ^ 10 * z ^ 3 + (-2146989 / 256 : ℂ) * t ^ 10 * z + (297 / 2 : ℂ) * t ^ 9 * c ^ 9 * z ^ 9 + (-657 / 8 : ℂ) * t ^ 9 * c ^ 9 * z ^ 7 + (2205 / 32 : ℂ) * t ^ 9 * c ^ 9 * z ^ 5 + (-5337 / 128 : ℂ) * t ^ 9 * c ^ 9 * z ^ 3 + (10629 / 512 : ℂ) * t ^ 9 * c ^ 9 * z + (624 : ℂ) * t ^ 9 * c ^ 7 * z ^ 11 + (-5155 : ℂ) * t ^ 9 * c ^ 7 * z ^ 9 + (-1525 / 4 : ℂ) * t ^ 9 * c ^ 7 * z ^ 7 + (-14215 / 16 : ℂ) * t ^ 9 * c ^ 7 * z ^ 5 + (43123 / 64 : ℂ) * t ^ 9 * c ^ 7 * z ^ 3 + (-108591 / 256 : ℂ) * t ^ 9 * c ^ 7 * z + (980 : ℂ) * t ^ 9 * c ^ 5 * z ^ 11 + (14815 : ℂ) * t ^ 9 * c ^ 5 * z ^ 9 + (-1011 / 4 : ℂ) * t ^ 9 * c ^ 5 * z ^ 7 + (-66633 / 16 : ℂ) * t ^ 9 * c ^ 5 * z ^ 5 + (-187763 / 64 : ℂ) * t ^ 9 * c ^ 5 * z ^ 3 + (454527 / 256 : ℂ) * t ^ 9 * c ^ 5 * z + (-1192 : ℂ) * t ^ 9 * c ^ 3 * z ^ 11 + (-241 : ℂ) * t ^ 9 * c ^ 3 * z ^ 9 + (2505 / 4 : ℂ) * t ^ 9 * c ^ 3 * z ^ 7 + (496599 / 16 : ℂ) * t ^ 9 * c ^ 3 * z ^ 5 + (-1211591 / 64 : ℂ) * t ^ 9 * c ^ 3 * z ^ 3 + (3488823 / 256 : ℂ) * t ^ 9 * c ^ 3 * z + (776 : ℂ) * t ^ 9 * c * z ^ 11 + (-16465 : ℂ) * t ^ 9 * c * z ^ 9 + (-92797 / 4 : ℂ) * t ^ 9 * c * z ^ 7 + (576053 / 16 : ℂ) * t ^ 9 * c * z ^ 5 + (-757877 / 64 : ℂ) * t ^ 9 * c * z ^ 3 + (2161845 / 256 : ℂ) * t ^ 9 * c * z + (-120 : ℂ) * t ^ 8 * c ^ 8 * z ^ 11 + (2503 / 2 : ℂ) * t ^ 8 * c ^ 8 * z ^ 9 + (-3703 / 8 : ℂ) * t ^ 8 * c ^ 8 * z ^ 7 + (10795 / 32 : ℂ) * t ^ 8 * c ^ 8 * z ^ 5 + (-28015 / 128 : ℂ) * t ^ 8 * c ^ 8 * z ^ 3 + (64131 / 512 : ℂ) * t ^ 8 * c ^ 8 * z + (-130 : ℂ) * t ^ 8 * c ^ 6 * z ^ 11 + (-16785 / 2 : ℂ) * t ^ 8 * c ^ 6 * z ^ 9 + (-25403 / 8 : ℂ) * t ^ 8 * c ^ 6 * z ^ 7 + (-3977 / 32 : ℂ) * t ^ 8 * c ^ 6 * z ^ 5 + (-6499 / 128 : ℂ) * t ^ 8 * c ^ 6 * z ^ 3 + (54591 / 512 : ℂ) * t ^ 8 * c ^ 6 * z + (830 : ℂ) * t ^ 8 * c ^ 4 * z ^ 11 + (13409 / 2 : ℂ) * t ^ 8 * c ^ 4 * z ^ 9 + (-56493 / 8 : ℂ) * t ^ 8 * c ^ 4 * z ^ 7 + (-236431 / 32 : ℂ) * t ^ 8 * c ^ 4 * z ^ 5 + (-94501 / 128 : ℂ) * t ^ 8 * c ^ 4 * z ^ 3 + (-197991 / 512 : ℂ) * t ^ 8 * c ^ 4 * z + (-1210 : ℂ) * t ^ 8 * c ^ 2 * z ^ 11 + (33145 / 2 : ℂ) * t ^ 8 * c ^ 2 * z ^ 9 + (129423 / 8 : ℂ) * t ^ 8 * c ^ 2 * z ^ 7 + (823249 / 32 : ℂ) * t ^ 8 * c ^ 2 * z ^ 5 + (-591505 / 128 : ℂ) * t ^ 8 * c ^ 2 * z ^ 3 + (246609 / 512 : ℂ) * t ^ 8 * c ^ 2 * z + (40 : ℂ) * t ^ 8 * z ^ 11 + (-1990 : ℂ) * t ^ 8 * z ^ 9 + (-3139 : ℂ) * t ^ 8 * z ^ 7 + (136517 / 4 : ℂ) * t ^ 8 * z ^ 5 + (-94373 / 16 : ℂ) * t ^ 8 * z ^ 3 + (258885 / 64 : ℂ) * t ^ 8 * z + (-335 / 2 : ℂ) * t ^ 7 * c ^ 9 * z ^ 9 + (387 / 8 : ℂ) * t ^ 7 * c ^ 9 * z ^ 7 + (-783 / 32 : ℂ) * t ^ 7 * c ^ 9 * z ^ 5 + (1323 / 128 : ℂ) * t ^ 7 * c ^ 9 * z ^ 3 + (-2007 / 512 : ℂ) * t ^ 7 * c ^ 9 * z + (-184 : ℂ) * t ^ 7 * c ^ 7 * z ^ 11 + (2795 : ℂ) * t ^ 7 * c ^ 7 * z ^ 9 + (1273 / 4 : ℂ) * t ^ 7 * c ^ 7 * z ^ 7 + (7227 / 16 : ℂ) * t ^ 7 * c ^ 7 * z ^ 5 + (-16367 / 64 : ℂ) * t ^ 7 * c ^ 7 * z ^ 3 + (31491 / 256 : ℂ) * t ^ 7 * c ^ 7 * z + (-700 : ℂ) * t ^ 7 * c ^ 5 * z ^ 11 + (-5759 : ℂ) * t ^ 7 * c ^ 5 * z ^ 9 + (18579 / 4 : ℂ) * t ^ 7 * c ^ 5 * z ^ 7 + (35329 / 16 : ℂ) * t ^ 7 * c ^ 5 * z ^ 5 + (66691 / 64 : ℂ) * t ^ 7 * c ^ 5 * z ^ 3 + (-130311 / 256 : ℂ) * t ^ 7 * c ^ 5 * z + (892 : ℂ) * t ^ 7 * c ^ 3 * z ^ 11 + (-6648 : ℂ) * t ^ 7 * c ^ 3 * z ^ 9 + (-2685 : ℂ) * t ^ 7 * c ^ 3 * z ^ 7 + (-68807 / 4 : ℂ) * t ^ 7 * c ^ 3 * z ^ 5 + (142327 / 16 : ℂ) * t ^ 7 * c ^ 3 * z ^ 3 + (-302247 / 64 : ℂ) * t ^ 7 * c ^ 3 * z + (-176 : ℂ) * t ^ 7 * c * z ^ 11 + (6060 : ℂ) * t ^ 7 * c * z ^ 9 + (10210 : ℂ) * t ^ 7 * c * z ^ 7 + (-28419 : ℂ) * t ^ 7 * c * z ^ 5 + (21937 / 4 : ℂ) * t ^ 7 * c * z ^ 3 + (-44697 / 16 : ℂ) * t ^ 7 * c * z + (56 : ℂ) * t ^ 6 * c ^ 8 * z ^ 11 + (-1265 / 2 : ℂ) * t ^ 6 * c ^ 8 * z ^ 9 + (1773 / 8 : ℂ) * t ^ 6 * c ^ 8 * z ^ 7 + (-4305 / 32 : ℂ) * t ^ 6 * c ^ 8 * z ^ 5 + (9029 / 128 : ℂ) * t ^ 6 * c ^ 8 * z ^ 3 + (-16713 / 512 : ℂ) * t ^ 6 * c ^ 8 * z + (322 : ℂ) * t ^ 6 * c ^ 6 * z ^ 11 + (5989 / 2 : ℂ) * t ^ 6 * c ^ 6 * z ^ 9 + (1727 / 8 : ℂ) * t ^ 6 * c ^ 6 * z ^ 7 + (-2619 / 32 : ℂ) * t ^ 6 * c ^ 6 * z ^ 5 + (12023 / 128 : ℂ) * t ^ 6 * c ^ 6 * z ^ 3 + (-30771 / 512 : ℂ) * t ^ 6 * c ^ 6 * z + (-338 : ℂ) * t ^ 6 * c ^ 4 * z ^ 11 + (491 / 2 : ℂ) * t ^ 6 * c ^ 4 * z ^ 9 + (27917 / 8 : ℂ) * t ^ 6 * c ^ 4 * z ^ 7 + (98995 / 32 : ℂ) * t ^ 6 * c ^ 4 * z ^ 5 + (-73123 / 128 : ℂ) * t ^ 6 * c ^ 4 * z ^ 3 + (230035 / 512 : ℂ) * t ^ 6 * c ^ 4 * z + (304 : ℂ) * t ^ 6 * c ^ 2 * z ^ 11 + (-6840 : ℂ) * t ^ 6 * c ^ 2 * z ^ 9 + (-8374 : ℂ) * t ^ 6 * c ^ 2 * z ^ 7 + (-9987 / 2 : ℂ) * t ^ 6 * c ^ 2 * z ^ 5 + (-5389 / 8 : ℂ) * t ^ 6 * c ^ 2 * z ^ 3 + (28629 / 32 : ℂ) * t ^ 6 * c ^ 2 * z + (280 : ℂ) * t ^ 6 * z ^ 9 + (658 : ℂ) * t ^ 6 * z ^ 7 + (-12396 : ℂ) * t ^ 6 * z ^ 5 + (5141 / 2 : ℂ) * t ^ 6 * z ^ 3 + (-11589 / 8 : ℂ) * t ^ 6 * z + (183 / 2 : ℂ) * t ^ 5 * c ^ 9 * z ^ 9 + (-99 / 8 : ℂ) * t ^ 5 * c ^ 9 * z ^ 7 + (135 / 32 : ℂ) * t ^ 5 * c ^ 9 * z ^ 5 + (-171 / 128 : ℂ) * t ^ 5 * c ^ 9 * z ^ 3 + (207 / 512 : ℂ) * t ^ 5 * c ^ 9 * z + (-32 : ℂ) * t ^ 5 * c ^ 7 * z ^ 11 + (-805 : ℂ) * t ^ 5 * c ^ 7 * z ^ 9 + (-395 / 4 : ℂ) * t ^ 5 * c ^ 7 * z ^ 7 + (-2285 / 16 : ℂ) * t ^ 5 * c ^ 7 * z ^ 5 + (3781 / 64 : ℂ) * t ^ 5 * c ^ 7 * z ^ 3 + (-5661 / 256 : ℂ) * t ^ 5 * c ^ 7 * z + (112 : ℂ) * t ^ 5 * c ^ 5 * z ^ 11 + (1021 : ℂ) * t ^ 5 * c ^ 5 * z ^ 9 + (-11753 / 4 : ℂ) * t ^ 5 * c ^ 5 * z ^ 7 + (-11647 / 16 : ℂ) * t ^ 5 * c ^ 5 * z ^ 5 + (-15905 / 64 : ℂ) * t ^ 5 * c ^ 5 * z ^ 3 + (25025 / 256 : ℂ) * t ^ 5 * c ^ 5 * z + (-256 : ℂ) * t ^ 5 * c ^ 3 * z ^ 11 + (3548 : ℂ) * t ^ 5 * c ^ 3 * z ^ 9 + (1744 : ℂ) * t ^ 5 * c ^ 3 * z ^ 7 + (6075 : ℂ) * t ^ 5 * c ^ 3 * z ^ 5 + (-9995 / 4 : ℂ) * t ^ 5 * c ^ 3 * z ^ 3 + (16091 / 16 : ℂ) * t ^ 5 * c ^ 3 * z + (-880 : ℂ) * t ^ 5 * c * z ^ 9 + (-2420 : ℂ) * t ^ 5 * c * z ^ 7 + (12544 : ℂ) * t ^ 5 * c * z ^ 5 + (-2845 / 2 : ℂ) * t ^ 5 * c * z ^ 3 + (4205 / 8 : ℂ) * t ^ 5 * c * z + (-8 : ℂ) * t ^ 4 * c ^ 8 * z ^ 11 + (277 / 2 : ℂ) * t ^ 4 * c ^ 8 * z ^ 9 + (-633 / 8 : ℂ) * t ^ 4 * c ^ 8 * z ^ 7 + (1181 / 32 : ℂ) * t ^ 4 * c ^ 8 * z ^ 5 + (-1921 / 128 : ℂ) * t ^ 4 * c ^ 8 * z ^ 3 + (2853 / 512 : ℂ) * t ^ 4 * c ^ 8 * z + (-54 : ℂ) * t ^ 4 * c ^ 6 * z ^ 11 + (-1241 / 2 : ℂ) * t ^ 4 * c ^ 6 * z ^ 9 + (2993 / 8 : ℂ) * t ^ 4 * c ^ 6 * z ^ 7 + (2351 / 32 : ℂ) * t ^ 4 * c ^ 6 * z ^ 5 + (-4687 / 128 : ℂ) * t ^ 4 * c ^ 6 * z ^ 3 + (7791 / 512 : ℂ) * t ^ 4 * c ^ 6 * z + (104 : ℂ) * t ^ 4 * c ^ 4 * z ^ 11 + (-838 : ℂ) * t ^ 4 * c ^ 4 * z ^ 9 + (-1581 / 2 : ℂ) * t ^ 4 * c ^ 4 * z ^ 7 + (-7071 / 8 : ℂ) * t ^ 4 * c ^ 4 * z ^ 5 + (9807 / 32 : ℂ) * t ^ 4 * c ^ 4 * z ^ 3 + (-17631 / 128 : ℂ) * t ^ 4 * c ^ 4 * z + (1040 : ℂ) * t ^ 4 * c ^ 2 * z ^ 9 + (2204 : ℂ) * t ^ 4 * c ^ 2 * z ^ 7 + (-821 : ℂ) * t ^ 4 * c ^ 2 * z ^ 5 + (2905 / 4 : ℂ) * t ^ 4 * c ^ 2 * z ^ 3 + (-5657 / 16 : ℂ) * t ^ 4 * c ^ 2 * z + (-56 : ℂ) * t ^ 4 * z ^ 7 + (2634 : ℂ) * t ^ 4 * z ^ 5 + (-806 : ℂ) * t ^ 4 * z ^ 3 + (731 / 2 : ℂ) * t ^ 4 * z + (-45 / 2 : ℂ) * t ^ 3 * c ^ 9 * z ^ 9 + (9 / 8 : ℂ) * t ^ 3 * c ^ 9 * z ^ 7 + (-9 / 32 : ℂ) * t ^ 3 * c ^ 9 * z ^ 5 + (9 / 128 : ℂ) * t ^ 3 * c ^ 9 * z ^ 3 + (-9 / 512 : ℂ) * t ^ 3 * c ^ 9 * z + (12 : ℂ) * t ^ 3 * c ^ 7 * z ^ 11 + (138 : ℂ) * t ^ 3 * c ^ 7 * z ^ 9 + (37 / 2 : ℂ) * t ^ 3 * c ^ 7 * z ^ 7 + (187 / 8 : ℂ) * t ^ 3 * c ^ 7 * z ^ 5 + (-235 / 32 : ℂ) * t ^ 3 * c ^ 7 * z ^ 3 + (283 / 128 : ℂ) * t ^ 3 * c ^ 7 * z + (-16 : ℂ) * t ^ 3 * c ^ 5 * z ^ 11 + (20 : ℂ) * t ^ 3 * c ^ 5 * z ^ 9 + (792 : ℂ) * t ^ 3 * c ^ 5 * z ^ 7 + (255 / 2 : ℂ) * t ^ 3 * c ^ 5 * z ^ 5 + (285 / 8 : ℂ) * t ^ 3 * c ^ 5 * z ^ 3 + (-357 / 32 : ℂ) * t ^ 3 * c ^ 5 * z + (-576 : ℂ) * t ^ 3 * c ^ 3 * z ^ 9 + (-508 : ℂ) * t ^ 3 * c ^ 3 * z ^ 7 + (-1208 : ℂ) * t ^ 3 * c ^ 3 * z ^ 5 + (381 : ℂ) * t ^ 3 * c ^ 3 * z ^ 3 + (-477 / 4 : ℂ) * t ^ 3 * c ^ 3 * z + (240 : ℂ) * t ^ 3 * c * z ^ 7 + (-3004 : ℂ) * t ^ 3 * c * z ^ 5 + (170 : ℂ) * t ^ 3 * c * z ^ 3 + (-93 / 2 : ℂ) * t ^ 3 * c * z + (-21 / 2 : ℂ) * t ^ 2 * c ^ 8 * z ^ 9 + (137 / 8 : ℂ) * t ^ 2 * c ^ 8 * z ^ 7 + (-185 / 32 : ℂ) * t ^ 2 * c ^ 8 * z ^ 5 + (233 / 128 : ℂ) * t ^ 2 * c ^ 8 * z ^ 3 + (-281 / 512 : ℂ) * t ^ 2 * c ^ 8 * z + (52 : ℂ) * t ^ 2 * c ^ 6 * z ^ 9 + (-151 : ℂ) * t ^ 2 * c ^ 6 * z ^ 7 + (-73 / 4 : ℂ) * t ^ 2 * c ^ 6 * z ^ 5 + (97 / 16 : ℂ) * t ^ 2 * c ^ 6 * z ^ 3 + (-121 / 64 : ℂ) * t ^ 2 * c ^ 6 * z + (152 : ℂ) * t ^ 2 * c ^ 4 * z ^ 9 + (52 : ℂ) * t ^ 2 * c ^ 4 * z ^ 7 + (309 / 2 : ℂ) * t ^ 2 * c ^ 4 * z ^ 5 + (-489 / 8 : ℂ) * t ^ 2 * c ^ 4 * z ^ 3 + (633 / 32 : ℂ) * t ^ 2 * c ^ 4 * z + (-240 : ℂ) * t ^ 2 * c ^ 2 * z ^ 7 + (584 : ℂ) * t ^ 2 * c ^ 2 * z ^ 5 + (-172 : ℂ) * t ^ 2 * c ^ 2 * z ^ 3 + (57 : ℂ) * t ^ 2 * c ^ 2 * z + (-248 : ℂ) * t ^ 2 * z ^ 5 + (164 : ℂ) * t ^ 2 * z ^ 3 + (-57 : ℂ) * t ^ 2 * z + (2 : ℂ) * t * c ^ 9 * z ^ 9 + (-12 : ℂ) * t * c ^ 7 * z ^ 9 + (-2 : ℂ) * t * c ^ 7 * z ^ 7 + (-3 / 2 : ℂ) * t * c ^ 7 * z ^ 5 + (3 / 8 : ℂ) * t * c ^ 7 * z ^ 3 + (-3 / 32 : ℂ) * t * c ^ 7 * z + (-16 : ℂ) * t * c ^ 5 * z ^ 9 + (-76 : ℂ) * t * c ^ 5 * z ^ 7 + (-9 : ℂ) * t * c ^ 5 * z ^ 5 + (-9 / 4 : ℂ) * t * c ^ 5 * z ^ 3 + (9 / 16 : ℂ) * t * c ^ 5 * z + (64 : ℂ) * t * c ^ 3 * z ^ 7 + (100 : ℂ) * t * c ^ 3 * z ^ 5 + (-24 : ℂ) * t * c ^ 3 * z ^ 3 + (6 : ℂ) * t * c ^ 3 * z + (304 : ℂ) * t * c * z ^ 5 + (-4 : ℂ) * t * c * z ^ 3 + (1 : ℂ) * t * c * z + (-3 / 2 : ℂ) * c ^ 8 * z ^ 7 + (3 / 8 : ℂ) * c ^ 8 * z ^ 5 + (-3 / 32 : ℂ) * c ^ 8 * z ^ 3 + (3 / 128 : ℂ) * c ^ 8 * z + (18 : ℂ) * c ^ 6 * z ^ 7 + (3 / 2 : ℂ) * c ^ 6 * z ^ 5 + (-3 / 8 : ℂ) * c ^ 6 * z ^ 3 + (3 / 32 : ℂ) * c ^ 6 * z + (-12 : ℂ) * c ^ 4 * z ^ 5 + (9 / 2 : ℂ) * c ^ 4 * z ^ 3 + (-9 / 8 : ℂ) * c ^ 4 * z + (-80 : ℂ) * c ^ 2 * z ^ 5 + (14 : ℂ) * c ^ 2 * z ^ 3 + (-7 / 2 : ℂ) * c ^ 2 * z + (-16 : ℂ) * z ^ 3 + (4 : ℂ) * z) * hz

set_option maxHeartbeats 1000000 in
private lemma NUM4_eq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NUMdef τ c 4 = NUMP4 (τ : ℂ) c (xiτ τ) (vτ τ : ℂ) (Pc τ c) (Qc τ c) /
      (Qc τ c * (((vτ τ : ℂ) + τ * xiτ τ) * ((vτ τ : ℂ) - τ * xiτ τ)) ^ 3 *
        (((vτ τ : ℂ) - (c - τ) * xiτ τ) * ((vτ τ : ℂ) + (c - τ) * xiτ τ)) ^ 4) := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  have hb1 := one_add_beta_ne τ h1 h2 _ hxi
  have hb2 := one_add_beta_ne τ h1 h2 _ hxi'
  have hQ := Qc_ne τ h1 h2.le c hc
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  obtain ⟨hAp, hAm, hLp, hLm⟩ := factors_ne τ h1 h2 c hc
  unfold NUMdef dPiJf
  rw [deriv_aJ τ 4 _ hb1, deriv_aJ τ 4 _ hb2]
  unfold aJ PiJ NUMP4
  simp only [Nat.cast_ofNat, Int.reduceSub, zpow_neg, zpow_ofNat]
  rw [hβC, hνC, fA (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0, fA' (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0,
    fL (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0, fL' (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0]
  generalize (vτ τ : ℂ) + τ * xiτ τ = Ap at *
  generalize (vτ τ : ℂ) - τ * xiτ τ = Am at *
  generalize (vτ τ : ℂ) - (c - τ) * xiτ τ = Lp at *
  generalize (vτ τ : ℂ) + (c - τ) * xiτ τ = Lm at *
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hQ (pow_ne_zero _ (mul_ne_zero hAp hAm)))
    (pow_ne_zero _ (mul_ne_zero hLp hLm)))]
  field_simp
  ring

/-- The closed form of `T_4`. -/
private lemma TJ4_closed (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    TJ τ c 4 = Nc4 τ c / (((256 * Kt τ ^ 3 : ℝ) : ℂ) * Qc τ c ^ 2) := by
  have hz : xiτ τ ^ 2 = (τ : ℂ) ^ 2 - 1 / 4 := by
    rw [xi_sq τ h1 h2]
    unfold ysq
    push_cast
    ring
  have hvd : (vτ τ : ℂ) = 1 - (τ : ℂ) ^ 2 := by
    unfold vτ
    push_cast
    ring
  have hsd : (ysq τ : ℂ) = 1 / 4 - (τ : ℂ) ^ 2 := by
    unfold ysq
    push_cast
    ring
  have hs0 : (ysq τ : ℂ) ≠ 0 := by exact_mod_cast (ysq_pos τ h1 h2).ne'
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  have hz0 := xi_ne τ h1 h2
  have hQ0 := Qc_ne τ h1 h2.le c hc
  rw [Qc_C, QcC_F] at hQ0
  have hF1 : F1p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hF2 : F2p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hW0 : (4 - 7 * (τ : ℂ) ^ 2) ≠ 0 := by
    have h47 : (4 : ℝ) - 7 * τ ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast h47
  rw [TJ_eq τ h1 h2 4 c hc, TJf_eq, NUM4_eq τ h1 h2 c hc, DEN_eq τ h1 h2 c hc, Pc_C, Qc_C,
    core4 (τ : ℂ) c (xiτ τ) _ _ hz hvd hsd, relAA _ _ _ hz hvd, relLL _ _ _ _ hz hvd,
    relX _ _ _ _ hz hvd, Nc4_C, QcC_F]
  rw [show ((256 * Kt τ ^ 3 : ℝ) : ℂ) = 256 * (-(4 - 7 * (τ : ℂ) ^ 2)) ^ 3 by unfold Kt; push_cast; ring]
  generalize F1p (τ : ℂ) c = F1 at *
  generalize F2p (τ : ℂ) c = F2 at *
  generalize Ncp4 (τ : ℂ) c = N at *
  generalize (4 - 7 * (τ : ℂ) ^ 2) = W at *
  generalize xiτ τ = z at *
  generalize (vτ τ : ℂ) = v at *
  generalize (ysq τ : ℂ) = s at *
  field_simp
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The ξ-elimination for `T_5`: `NUMP5 ≡ ` its closed form modulo `ξ² = τ² - 1/4`. -/
private lemma core5 (t c z v s : ℂ) (hz : z ^ 2 = t ^ 2 - 1 / 4) (hv : v = 1 - t ^ 2) (hs : s = 1 / 4 - t ^ 2) :
    NUMP5 t c z v (PcC t c) (QcC t c) = -(Ncp5 t c * s * F2p t c * v ^ 2 * z) / 131072 := by
  subst hv hs
  unfold NUMP5 PcC QcC Ncp5 F2p
  linear_combination ((512 : ℂ) * t ^ 27 * c ^ 4 * z + (896 : ℂ) * t ^ 27 * c ^ 2 * z + (-384 : ℂ) * t ^ 26 * c ^ 5 * z + (48 : ℂ) * t ^ 26 * c ^ 3 * z ^ 5 + (-4592 : ℂ) * t ^ 26 * c ^ 3 * z + (-84 : ℂ) * t ^ 26 * c * z ^ 5 + (-1764 : ℂ) * t ^ 26 * c * z + (-512 : ℂ) * t ^ 25 * c ^ 6 * z + (-24 : ℂ) * t ^ 25 * c ^ 4 * z ^ 5 + (512 : ℂ) * t ^ 25 * c ^ 4 * z ^ 3 + (1848 : ℂ) * t ^ 25 * c ^ 4 * z + (896 : ℂ) * t ^ 25 * c ^ 2 * z ^ 3 + (804 : ℂ) * t ^ 25 * c ^ 2 * z + (147 / 2 : ℂ) * t ^ 25 * z ^ 5 + (1715 / 2 : ℂ) * t ^ 25 * z + (704 : ℂ) * t ^ 24 * c ^ 7 * z + (-384 : ℂ) * t ^ 24 * c ^ 5 * z ^ 3 + (776 : ℂ) * t ^ 24 * c ^ 5 * z + (720 : ℂ) * t ^ 24 * c ^ 3 * z ^ 7 + (-540 : ℂ) * t ^ 24 * c ^ 3 * z ^ 5 + (-4592 : ℂ) * t ^ 24 * c ^ 3 * z ^ 3 + (22882 : ℂ) * t ^ 24 * c ^ 3 * z + (-1164 : ℂ) * t ^ 24 * c * z ^ 7 + (972 : ℂ) * t ^ 24 * c * z ^ 5 + (-1764 : ℂ) * t ^ 24 * c * z ^ 3 + (9660 : ℂ) * t ^ 24 * c * z + (-288 : ℂ) * t ^ 23 * c ^ 8 * z + (-512 : ℂ) * t ^ 23 * c ^ 6 * z ^ 3 + (2564 : ℂ) * t ^ 23 * c ^ 6 * z + (-1128 : ℂ) * t ^ 23 * c ^ 4 * z ^ 7 + (782 : ℂ) * t ^ 23 * c ^ 4 * z ^ 5 + (1976 : ℂ) * t ^ 23 * c ^ 4 * z ^ 3 + (-20058 : ℂ) * t ^ 23 * c ^ 4 * z + (1236 : ℂ) * t ^ 23 * c ^ 2 * z ^ 7 + (896 : ℂ) * t ^ 23 * c ^ 2 * z ^ 5 + (1028 : ℂ) * t ^ 23 * c ^ 2 * z ^ 3 + (-98985 / 4 : ℂ) * t ^ 23 * c ^ 2 * z + (2079 / 2 : ℂ) * t ^ 23 * z ^ 7 + (-6993 / 8 : ℂ) * t ^ 23 * z ^ 5 + (1715 / 2 : ℂ) * t ^ 23 * z ^ 3 + (-6272 : ℂ) * t ^ 23 * z + (40 : ℂ) * t ^ 22 * c ^ 9 * z + (704 : ℂ) * t ^ 22 * c ^ 7 * z ^ 3 + (-3603 : ℂ) * t ^ 22 * c ^ 7 * z + (576 : ℂ) * t ^ 22 * c ^ 5 * z ^ 7 + (-384 : ℂ) * t ^ 22 * c ^ 5 * z ^ 5 + (680 : ℂ) * t ^ 22 * c ^ 5 * z ^ 3 + (13203 / 4 : ℂ) * t ^ 22 * c ^ 5 * z + (112 : ℂ) * t ^ 22 * c ^ 3 * z ^ 9 + (-6792 : ℂ) * t ^ 22 * c ^ 3 * z ^ 7 + (-1820 : ℂ) * t ^ 22 * c ^ 3 * z ^ 5 + (21734 : ℂ) * t ^ 22 * c ^ 3 * z ^ 3 + (-710713 / 16 : ℂ) * t ^ 22 * c ^ 3 * z + (28 : ℂ) * t ^ 22 * c * z ^ 9 + (9555 : ℂ) * t ^ 22 * c * z ^ 7 + (-6912 : ℂ) * t ^ 22 * c * z ^ 5 + (9219 : ℂ) * t ^ 22 * c * z ^ 3 + (-1366689 / 64 : ℂ) * t ^ 22 * c * z + (-288 : ℂ) * t ^ 21 * c ^ 8 * z ^ 3 + (2955 / 2 : ℂ) * t ^ 21 * c ^ 8 * z + (-96 : ℂ) * t ^ 21 * c ^ 6 * z ^ 7 + (-512 : ℂ) * t ^ 21 * c ^ 6 * z ^ 5 + (2436 : ℂ) * t ^ 21 * c ^ 6 * z ^ 3 + (-24385 / 4 : ℂ) * t ^ 21 * c ^ 6 * z + (-184 : ℂ) * t ^ 21 * c ^ 4 * z ^ 9 + (10688 : ℂ) * t ^ 21 * c ^ 4 * z ^ 7 + (718 : ℂ) * t ^ 21 * c ^ 4 * z ^ 5 + (-19564 : ℂ) * t ^ 21 * c ^ 4 * z ^ 3 + (58465 : ℂ) * t ^ 21 * c ^ 4 * z + (-156 : ℂ) * t ^ 21 * c ^ 2 * z ^ 9 + (-10177 : ℂ) * t ^ 21 * c ^ 2 * z ^ 7 + (1252 : ℂ) * t ^ 21 * c ^ 2 * z ^ 5 + (-97957 / 4 : ℂ) * t ^ 21 * c ^ 2 * z ^ 3 + (5713489 / 64 : ℂ) * t ^ 21 * c ^ 2 * z + (49 / 2 : ℂ) * t ^ 21 * z ^ 9 + (-39777 / 4 : ℂ) * t ^ 21 * z ^ 7 + (180143 / 32 : ℂ) * t ^ 21 * z ^ 5 + (-48461 / 8 : ℂ) * t ^ 21 * z ^ 3 + (10863797 / 512 : ℂ) * t ^ 21 * z + (40 : ℂ) * t ^ 20 * c ^ 9 * z ^ 3 + (-200 : ℂ) * t ^ 20 * c ^ 9 * z + (704 : ℂ) * t ^ 20 * c ^ 7 * z ^ 5 + (-3427 : ℂ) * t ^ 20 * c ^ 7 * z ^ 3 + (33261 / 4 : ℂ) * t ^ 20 * c ^ 7 * z + (-5616 : ℂ) * t ^ 20 * c ^ 5 * z ^ 7 + (584 : ℂ) * t ^ 20 * c ^ 5 * z ^ 5 + (13883 / 4 : ℂ) * t ^ 20 * c ^ 5 * z ^ 3 + (-127683 / 8 : ℂ) * t ^ 20 * c ^ 5 * z + (-784 : ℂ) * t ^ 20 * c ^ 3 * z ^ 11 + (-396 : ℂ) * t ^ 20 * c ^ 3 * z ^ 9 + (24232 : ℂ) * t ^ 20 * c ^ 3 * z ^ 7 + (12006 : ℂ) * t ^ 20 * c ^ 3 * z ^ 5 + (-623777 / 16 : ℂ) * t ^ 20 * c ^ 3 * z ^ 3 + (2089597 / 64 : ℂ) * t ^ 20 * c ^ 3 * z + (1148 : ℂ) * t ^ 20 * c * z ^ 11 + (-1008 : ℂ) * t ^ 20 * c * z ^ 9 + (-137757 / 4 : ℂ) * t ^ 20 * c * z ^ 7 + (25278 : ℂ) * t ^ 20 * c * z ^ 5 + (-1219185 / 64 : ℂ) * t ^ 20 * c * z ^ 3 + (653319 / 32 : ℂ) * t ^ 20 * c * z + (-288 : ℂ) * t ^ 19 * c ^ 8 * z ^ 5 + (2811 / 2 : ℂ) * t ^ 19 * c ^ 8 * z ^ 3 + (-27147 / 8 : ℂ) * t ^ 19 * c ^ 8 * z + (160 : ℂ) * t ^ 19 * c ^ 6 * z ^ 9 + (376 : ℂ) * t ^ 19 * c ^ 6 * z ^ 7 + (2308 : ℂ) * t ^ 19 * c ^ 6 * z ^ 5 + (-21949 / 4 : ℂ) * t ^ 19 * c ^ 6 * z ^ 3 + (9259 : ℂ) * t ^ 19 * c ^ 6 * z + (2952 : ℂ) * t ^ 19 * c ^ 4 * z ^ 11 + (834 : ℂ) * t ^ 19 * c ^ 4 * z ^ 9 + (-38568 : ℂ) * t ^ 19 * c ^ 4 * z ^ 7 + (-14748 : ℂ) * t ^ 19 * c ^ 4 * z ^ 5 + (53574 : ℂ) * t ^ 19 * c ^ 4 * z ^ 3 + (-1442739 / 16 : ℂ) * t ^ 19 * c ^ 4 * z + (-3460 : ℂ) * t ^ 19 * c ^ 2 * z ^ 11 + (4034 : ℂ) * t ^ 19 * c ^ 2 * z ^ 9 + (179991 / 4 : ℂ) * t ^ 19 * c ^ 2 * z ^ 7 + (-96705 / 4 : ℂ) * t ^ 19 * c ^ 2 * z ^ 5 + (5321661 / 64 : ℂ) * t ^ 19 * c ^ 2 * z ^ 3 + (-21442425 / 128 : ℂ) * t ^ 19 * c ^ 2 * z + (-2107 / 2 : ℂ) * t ^ 19 * z ^ 11 + (2583 / 8 : ℂ) * t ^ 19 * z ^ 9 + (1390061 / 32 : ℂ) * t ^ 19 * z ^ 7 + (-2772705 / 128 : ℂ) * t ^ 19 * z ^ 5 + (10088421 / 512 : ℂ) * t ^ 19 * z ^ 3 + (-90055353 / 2048 : ℂ) * t ^ 19 * z + (40 : ℂ) * t ^ 18 * c ^ 9 * z ^ 5 + (-190 : ℂ) * t ^ 18 * c ^ 9 * z ^ 3 + (887 / 2 : ℂ) * t ^ 18 * c ^ 9 * z + (-112 : ℂ) * t ^ 18 * c ^ 7 * z ^ 9 + (704 : ℂ) * t ^ 18 * c ^ 7 * z ^ 7 + (-3251 : ℂ) * t ^ 18 * c ^ 7 * z ^ 5 + (14917 / 2 : ℂ) * t ^ 18 * c ^ 7 * z ^ 3 + (-46151 / 4 : ℂ) * t ^ 18 * c ^ 7 * z + (-4416 : ℂ) * t ^ 18 * c ^ 5 * z ^ 11 + (564 : ℂ) * t ^ 18 * c ^ 5 * z ^ 9 + (21632 : ℂ) * t ^ 18 * c ^ 5 * z ^ 7 + (14467 / 4 : ℂ) * t ^ 18 * c ^ 5 * z ^ 5 + (-241483 / 16 : ℂ) * t ^ 18 * c ^ 5 * z ^ 3 + (970505 / 32 : ℂ) * t ^ 18 * c ^ 5 * z + (-96 : ℂ) * t ^ 18 * c ^ 3 * z ^ 13 + (7424 : ℂ) * t ^ 18 * c ^ 3 * z ^ 11 + (-6021 : ℂ) * t ^ 18 * c ^ 3 * z ^ 9 + (-53066 : ℂ) * t ^ 18 * c ^ 3 * z ^ 7 + (-256313 / 16 : ℂ) * t ^ 18 * c ^ 3 * z ^ 5 + (366455 / 16 : ℂ) * t ^ 18 * c ^ 3 * z ^ 3 + (5887975 / 256 : ℂ) * t ^ 18 * c ^ 3 * z + (72 : ℂ) * t ^ 18 * c * z ^ 13 + (-2681 : ℂ) * t ^ 18 * c * z ^ 11 + (14787 / 4 : ℂ) * t ^ 18 * c * z ^ 9 + (1033923 / 16 : ℂ) * t ^ 18 * c * z ^ 7 + (-3359697 / 64 : ℂ) * t ^ 18 * c * z ^ 5 + (4007367 / 256 : ℂ) * t ^ 18 * c * z ^ 3 + (5040315 / 1024 : ℂ) * t ^ 18 * c * z + (24 : ℂ) * t ^ 17 * c ^ 8 * z ^ 9 + (-288 : ℂ) * t ^ 17 * c ^ 8 * z ^ 7 + (2667 / 2 : ℂ) * t ^ 17 * c ^ 8 * z ^ 5 + (-3042 : ℂ) * t ^ 17 * c ^ 8 * z ^ 3 + (74601 / 16 : ℂ) * t ^ 17 * c ^ 8 * z + (3360 : ℂ) * t ^ 17 * c ^ 6 * z ^ 11 + (-1976 : ℂ) * t ^ 17 * c ^ 6 * z ^ 9 + (-1492 : ℂ) * t ^ 17 * c ^ 6 * z ^ 7 + (-19641 / 4 : ℂ) * t ^ 17 * c ^ 6 * z ^ 5 + (126195 / 16 : ℂ) * t ^ 17 * c ^ 6 * z ^ 3 + (-315723 / 32 : ℂ) * t ^ 17 * c ^ 6 * z + (432 : ℂ) * t ^ 17 * c ^ 4 * z ^ 13 + (-15868 : ℂ) * t ^ 17 * c ^ 4 * z ^ 11 + (5294 : ℂ) * t ^ 17 * c ^ 4 * z ^ 9 + (76920 : ℂ) * t ^ 17 * c ^ 4 * z ^ 7 + (79809 / 2 : ℂ) * t ^ 17 * c ^ 4 * z ^ 5 + (-1228443 / 16 : ℂ) * t ^ 17 * c ^ 4 * z ^ 3 + (5364567 / 64 : ℂ) * t ^ 17 * c ^ 4 * z + (-180 : ℂ) * t ^ 17 * c ^ 2 * z ^ 13 + (14803 : ℂ) * t ^ 17 * c ^ 2 * z ^ 11 + (-65359 / 4 : ℂ) * t ^ 17 * c ^ 2 * z ^ 9 + (-1938285 / 16 : ℂ) * t ^ 17 * c ^ 2 * z ^ 7 + (4934841 / 64 : ℂ) * t ^ 17 * c ^ 2 * z ^ 5 + (-37563189 / 256 : ℂ) * t ^ 17 * c ^ 2 * z ^ 3 + (203584545 / 1024 : ℂ) * t ^ 17 * c ^ 2 * z + (-84 : ℂ) * t ^ 17 * z ^ 13 + (11739 / 2 : ℂ) * t ^ 17 * z ^ 11 + (-19831 / 8 : ℂ) * t ^ 17 * z ^ 9 + (-3611581 / 32 : ℂ) * t ^ 17 * z ^ 7 + (6876609 / 128 : ℂ) * t ^ 17 * z ^ 5 + (-19991733 / 512 : ℂ) * t ^ 17 * z ^ 3 + (127491609 / 2048 : ℂ) * t ^ 17 * z + (40 : ℂ) * t ^ 16 * c ^ 9 * z ^ 7 + (-180 : ℂ) * t ^ 16 * c ^ 9 * z ^ 5 + (396 : ℂ) * t ^ 16 * c ^ 9 * z ^ 3 + (-2343 / 4 : ℂ) * t ^ 16 * c ^ 9 * z + (-1392 : ℂ) * t ^ 16 * c ^ 7 * z ^ 11 + (1532 : ℂ) * t ^ 16 * c ^ 7 * z ^ 9 + (-3075 : ℂ) * t ^ 16 * c ^ 7 * z ^ 7 + (26583 / 4 : ℂ) * t ^ 16 * c ^ 7 * z ^ 5 + (-77385 / 8 : ℂ) * t ^ 16 * c ^ 7 * z ^ 3 + (341217 / 32 : ℂ) * t ^ 16 * c ^ 7 * z + (-768 : ℂ) * t ^ 16 * c ^ 5 * z ^ 13 + (22004 : ℂ) * t ^ 16 * c ^ 5 * z ^ 11 + (-6268 : ℂ) * t ^ 16 * c ^ 5 * z ^ 9 + (-184629 / 4 : ℂ) * t ^ 16 * c ^ 5 * z ^ 7 + (-28377 / 2 : ℂ) * t ^ 16 * c ^ 5 * z ^ 5 + (1699527 / 64 : ℂ) * t ^ 16 * c ^ 5 * z ^ 3 + (-33750 : ℂ) * t ^ 16 * c ^ 5 * z + (240 : ℂ) * t ^ 16 * c ^ 3 * z ^ 13 + (-26237 : ℂ) * t ^ 16 * c ^ 3 * z ^ 11 + (122279 / 4 : ℂ) * t ^ 16 * c ^ 3 * z ^ 9 + (1452095 / 16 : ℂ) * t ^ 16 * c ^ 3 * z ^ 7 + (-748317 / 64 : ℂ) * t ^ 16 * c ^ 3 * z ^ 5 + (7353795 / 256 : ℂ) * t ^ 16 * c ^ 3 * z ^ 3 + (-79061073 / 1024 : ℂ) * t ^ 16 * c ^ 3 * z + (90 : ℂ) * t ^ 16 * c * z ^ 13 + (-12735 / 2 : ℂ) * t ^ 16 * c * z ^ 11 + (-31005 / 8 : ℂ) * t ^ 16 * c * z ^ 9 + (-1643847 / 32 : ℂ) * t ^ 16 * c * z ^ 7 + (8459259 / 128 : ℂ) * t ^ 16 * c * z ^ 5 + (4523841 / 512 : ℂ) * t ^ 16 * c * z ^ 3 + (-80557101 / 2048 : ℂ) * t ^ 16 * c * z + (312 : ℂ) * t ^ 15 * c ^ 8 * z ^ 11 + (-462 : ℂ) * t ^ 15 * c ^ 8 * z ^ 9 + (2523 / 2 : ℂ) * t ^ 15 * c ^ 8 * z ^ 7 + (-21669 / 8 : ℂ) * t ^ 15 * c ^ 8 * z ^ 5 + (62433 / 16 : ℂ) * t ^ 15 * c ^ 8 * z ^ 3 + (-273771 / 64 : ℂ) * t ^ 15 * c ^ 8 * z + (672 : ℂ) * t ^ 15 * c ^ 6 * z ^ 13 + (-17044 : ℂ) * t ^ 15 * c ^ 6 * z ^ 11 + (7860 : ℂ) * t ^ 15 * c ^ 6 * z ^ 9 + (18251 / 4 : ℂ) * t ^ 15 * c ^ 6 * z ^ 7 + (53277 / 8 : ℂ) * t ^ 15 * c ^ 6 * z ^ 5 + (-505251 / 64 : ℂ) * t ^ 15 * c ^ 6 * z ^ 3 + (30495 / 4 : ℂ) * t ^ 15 * c ^ 6 * z + (-756 : ℂ) * t ^ 15 * c ^ 4 * z ^ 13 + (37636 : ℂ) * t ^ 15 * c ^ 4 * z ^ 11 + (-32197 : ℂ) * t ^ 15 * c ^ 4 * z ^ 9 + (-198171 / 2 : ℂ) * t ^ 15 * c ^ 4 * z ^ 7 + (-824097 / 16 : ℂ) * t ^ 15 * c ^ 4 * z ^ 5 + (1034031 / 16 : ℂ) * t ^ 15 * c ^ 4 * z ^ 3 + (-11941035 / 256 : ℂ) * t ^ 15 * c ^ 4 * z + (156 : ℂ) * t ^ 15 * c ^ 2 * z ^ 13 + (-17109 : ℂ) * t ^ 15 * c ^ 2 * z ^ 11 + (112457 / 4 : ℂ) * t ^ 15 * c ^ 2 * z ^ 9 + (3262803 / 16 : ℂ) * t ^ 15 * c ^ 2 * z ^ 7 + (-8157087 / 64 : ℂ) * t ^ 15 * c ^ 2 * z ^ 5 + (41505339 / 256 : ℂ) * t ^ 15 * c ^ 2 * z ^ 3 + (-164676903 / 1024 : ℂ) * t ^ 15 * c ^ 2 * z + (300 : ℂ) * t ^ 15 * z ^ 13 + (-26775 / 2 : ℂ) * t ^ 15 * z ^ 11 + (56827 / 8 : ℂ) * t ^ 15 * z ^ 9 + (6144257 / 32 : ℂ) * t ^ 15 * z ^ 7 + (-11680317 / 128 : ℂ) * t ^ 15 * z ^ 5 + (26874969 / 512 : ℂ) * t ^ 15 * z ^ 3 + (-130034517 / 2048 : ℂ) * t ^ 15 * z + (-32 : ℂ) * t ^ 14 * c ^ 9 * z ^ 11 + (40 : ℂ) * t ^ 14 * c ^ 9 * z ^ 9 + (-170 : ℂ) * t ^ 14 * c ^ 9 * z ^ 7 + (351 : ℂ) * t ^ 14 * c ^ 9 * z ^ 5 + (-1947 / 4 : ℂ) * t ^ 14 * c ^ 9 * z ^ 3 + (16635 / 32 : ℂ) * t ^ 14 * c ^ 9 * z + (-288 : ℂ) * t ^ 14 * c ^ 7 * z ^ 13 + (7344 : ℂ) * t ^ 14 * c ^ 7 * z ^ 11 + (-5563 : ℂ) * t ^ 14 * c ^ 7 * z ^ 9 + (5877 : ℂ) * t ^ 14 * c ^ 7 * z ^ 7 + (-128187 / 16 : ℂ) * t ^ 14 * c ^ 7 * z ^ 5 + (32979 / 4 : ℂ) * t ^ 14 * c ^ 7 * z ^ 3 + (-1733499 / 256 : ℂ) * t ^ 14 * c ^ 7 * z + (1704 : ℂ) * t ^ 14 * c ^ 5 * z ^ 13 + (-45029 : ℂ) * t ^ 14 * c ^ 5 * z ^ 11 + (95843 / 4 : ℂ) * t ^ 14 * c ^ 5 * z ^ 9 + (999843 / 16 : ℂ) * t ^ 14 * c ^ 5 * z ^ 7 + (1472511 / 64 : ℂ) * t ^ 14 * c ^ 5 * z ^ 5 + (-6940473 / 256 : ℂ) * t ^ 14 * c ^ 5 * z ^ 3 + (24853995 / 1024 : ℂ) * t ^ 14 * c ^ 5 * z + (30 : ℂ) * t ^ 14 * c ^ 3 * z ^ 13 + (82393 / 2 : ℂ) * t ^ 14 * c ^ 3 * z ^ 11 + (-484741 / 8 : ℂ) * t ^ 14 * c ^ 3 * z ^ 9 + (-4105775 / 32 : ℂ) * t ^ 14 * c ^ 3 * z ^ 7 + (7687251 / 128 : ℂ) * t ^ 14 * c ^ 3 * z ^ 5 + (-35853639 / 512 : ℂ) * t ^ 14 * c ^ 3 * z ^ 3 + (174566475 / 2048 : ℂ) * t ^ 14 * c ^ 3 * z + (-918 : ℂ) * t ^ 14 * c * z ^ 13 + (61333 / 2 : ℂ) * t ^ 14 * c * z ^ 11 + (-37305 / 8 : ℂ) * t ^ 14 * c * z ^ 9 + (-1147347 / 32 : ℂ) * t ^ 14 * c * z ^ 7 + (-6308913 / 128 : ℂ) * t ^ 14 * c * z ^ 5 + (-19008315 / 512 : ℂ) * t ^ 14 * c * z ^ 3 + (114122007 / 2048 : ℂ) * t ^ 14 * c * z + (48 : ℂ) * t ^ 13 * c ^ 8 * z ^ 13 + (-1740 : ℂ) * t ^ 13 * c ^ 8 * z ^ 11 + (3471 / 2 : ℂ) * t ^ 13 * c ^ 8 * z ^ 9 + (-9573 / 4 : ℂ) * t ^ 13 * c ^ 8 * z ^ 7 + (103197 / 32 : ℂ) * t ^ 13 * c ^ 8 * z ^ 5 + (-105669 / 32 : ℂ) * t ^ 13 * c ^ 8 * z ^ 3 + (1396287 / 512 : ℂ) * t ^ 13 * c ^ 8 * z + (-1788 : ℂ) * t ^ 13 * c ^ 6 * z ^ 13 + (34365 : ℂ) * t ^ 13 * c ^ 6 * z ^ 11 + (-67825 / 4 : ℂ) * t ^ 13 * c ^ 6 * z ^ 9 + (-136699 / 16 : ℂ) * t ^ 13 * c ^ 6 * z ^ 7 + (-398697 / 64 : ℂ) * t ^ 13 * c ^ 6 * z ^ 5 + (1446429 / 256 : ℂ) * t ^ 13 * c ^ 6 * z ^ 3 + (-4546017 / 1024 : ℂ) * t ^ 13 * c ^ 6 * z + (-360 : ℂ) * t ^ 13 * c ^ 4 * z ^ 13 + (-48999 : ℂ) * t ^ 13 * c ^ 4 * z ^ 11 + (277163 / 4 : ℂ) * t ^ 13 * c ^ 4 * z ^ 9 + (1433769 / 16 : ℂ) * t ^ 13 * c ^ 4 * z ^ 7 + (2215899 / 64 : ℂ) * t ^ 13 * c ^ 4 * z ^ 5 + (-7804911 / 256 : ℂ) * t ^ 13 * c ^ 4 * z ^ 3 + (12495699 / 1024 : ℂ) * t ^ 13 * c ^ 4 * z + (996 : ℂ) * t ^ 13 * c ^ 2 * z ^ 13 + (-11611 : ℂ) * t ^ 13 * c ^ 2 * z ^ 11 + (-84193 / 4 : ℂ) * t ^ 13 * c ^ 2 * z ^ 9 + (-3442899 / 16 : ℂ) * t ^ 13 * c ^ 2 * z ^ 7 + (8337063 / 64 : ℂ) * t ^ 13 * c ^ 2 * z ^ 5 + (-30792891 / 256 : ℂ) * t ^ 13 * c ^ 2 * z ^ 3 + (94513167 / 1024 : ℂ) * t ^ 13 * c ^ 2 * z + (-396 : ℂ) * t ^ 13 * z ^ 13 + (31985 / 2 : ℂ) * t ^ 13 * z ^ 11 + (-88905 / 8 : ℂ) * t ^ 13 * z ^ 9 + (-7129039 / 32 : ℂ) * t ^ 13 * z ^ 7 + (14126343 / 128 : ℂ) * t ^ 13 * z ^ 5 + (-25789887 / 512 : ℂ) * t ^ 13 * z ^ 3 + (97986039 / 2048 : ℂ) * t ^ 13 * z + (192 : ℂ) * t ^ 12 * c ^ 9 * z ^ 11 + (-160 : ℂ) * t ^ 12 * c ^ 9 * z ^ 9 + (617 / 2 : ℂ) * t ^ 12 * c ^ 9 * z ^ 7 + (-399 : ℂ) * t ^ 12 * c ^ 9 * z ^ 5 + (12741 / 32 : ℂ) * t ^ 12 * c ^ 9 * z ^ 3 + (-5223 / 16 : ℂ) * t ^ 12 * c ^ 9 * z + (864 : ℂ) * t ^ 12 * c ^ 7 * z ^ 13 + (-15051 : ℂ) * t ^ 12 * c ^ 7 * z ^ 11 + (40097 / 4 : ℂ) * t ^ 12 * c ^ 7 * z ^ 9 + (-104679 / 16 : ℂ) * t ^ 12 * c ^ 7 * z ^ 7 + (399477 / 64 : ℂ) * t ^ 12 * c ^ 7 * z ^ 5 + (-1205835 / 256 : ℂ) * t ^ 12 * c ^ 7 * z ^ 3 + (3025929 / 1024 : ℂ) * t ^ 12 * c ^ 7 * z + (-426 : ℂ) * t ^ 12 * c ^ 5 * z ^ 13 + (97137 / 2 : ℂ) * t ^ 12 * c ^ 5 * z ^ 11 + (-370517 / 8 : ℂ) * t ^ 12 * c ^ 5 * z ^ 9 + (-1821231 / 32 : ℂ) * t ^ 12 * c ^ 5 * z ^ 7 + (-2733981 / 128 : ℂ) * t ^ 12 * c ^ 5 * z ^ 5 + (8956761 / 512 : ℂ) * t ^ 12 * c ^ 5 * z ^ 3 + (-23392965 / 2048 : ℂ) * t ^ 12 * c ^ 5 * z + (-906 : ℂ) * t ^ 12 * c ^ 3 * z ^ 13 + (-47087 / 2 : ℂ) * t ^ 12 * c ^ 3 * z ^ 11 + (496443 / 8 : ℂ) * t ^ 12 * c ^ 3 * z ^ 9 + (4479241 / 32 : ℂ) * t ^ 12 * c ^ 3 * z ^ 7 + (-10665789 / 128 : ℂ) * t ^ 12 * c ^ 3 * z ^ 5 + (34678209 / 512 : ℂ) * t ^ 12 * c ^ 3 * z ^ 3 + (-114069141 / 2048 : ℂ) * t ^ 12 * c ^ 3 * z + (1494 : ℂ) * t ^ 12 * c * z ^ 13 + (-91993 / 2 : ℂ) * t ^ 12 * c * z ^ 11 + (139293 / 8 : ℂ) * t ^ 12 * c * z ^ 9 + (4439679 / 32 : ℂ) * t ^ 12 * c * z ^ 7 + (2008869 / 128 : ℂ) * t ^ 12 * c * z ^ 5 + (23778423 / 512 : ℂ) * t ^ 12 * c * z ^ 3 + (-96218451 / 2048 : ℂ) * t ^ 12 * c * z + (-156 : ℂ) * t ^ 11 * c ^ 8 * z ^ 13 + (7347 / 2 : ℂ) * t ^ 11 * c ^ 8 * z ^ 11 + (-24495 / 8 : ℂ) * t ^ 11 * c ^ 8 * z ^ 9 + (84051 / 32 : ℂ) * t ^ 11 * c ^ 8 * z ^ 7 + (-319479 / 128 : ℂ) * t ^ 11 * c ^ 8 * z ^ 5 + (973611 / 512 : ℂ) * t ^ 11 * c ^ 8 * z ^ 3 + (-2481327 / 2048 : ℂ) * t ^ 11 * c ^ 8 * z + (1260 : ℂ) * t ^ 11 * c ^ 6 * z ^ 13 + (-35097 : ℂ) * t ^ 11 * c ^ 6 * z ^ 11 + (92341 / 4 : ℂ) * t ^ 11 * c ^ 6 * z ^ 9 + (164519 / 16 : ℂ) * t ^ 11 * c ^ 6 * z ^ 7 + (261933 / 64 : ℂ) * t ^ 11 * c ^ 6 * z ^ 5 + (-774897 / 256 : ℂ) * t ^ 11 * c ^ 6 * z ^ 3 + (2089509 / 1024 : ℂ) * t ^ 11 * c ^ 6 * z + (1440 : ℂ) * t ^ 11 * c ^ 4 * z ^ 13 + (34217 : ℂ) * t ^ 11 * c ^ 4 * z ^ 11 + (-316213 / 4 : ℂ) * t ^ 11 * c ^ 4 * z ^ 9 + (-954399 / 16 : ℂ) * t ^ 11 * c ^ 4 * z ^ 7 + (-491205 / 64 : ℂ) * t ^ 11 * c ^ 4 * z ^ 5 + (1172697 / 256 : ℂ) * t ^ 11 * c ^ 4 * z ^ 3 + (2109411 / 1024 : ℂ) * t ^ 11 * c ^ 4 * z + (-2124 : ℂ) * t ^ 11 * c ^ 2 * z ^ 13 + (43789 : ℂ) * t ^ 11 * c ^ 2 * z ^ 11 + (-9349 / 4 : ℂ) * t ^ 11 * c ^ 2 * z ^ 9 + (2146869 / 16 : ℂ) * t ^ 11 * c ^ 2 * z ^ 7 + (-5613957 / 64 : ℂ) * t ^ 11 * c ^ 2 * z ^ 5 + (15930069 / 256 : ℂ) * t ^ 11 * c ^ 2 * z ^ 3 + (-39744549 / 1024 : ℂ) * t ^ 11 * c ^ 2 * z + (228 : ℂ) * t ^ 11 * z ^ 13 + (-10545 : ℂ) * t ^ 11 * z ^ 11 + (41497 / 4 : ℂ) * t ^ 11 * z ^ 9 + (2850343 / 16 : ℂ) * t ^ 11 * z ^ 7 + (-6203607 / 64 : ℂ) * t ^ 11 * z ^ 5 + (9024519 / 256 : ℂ) * t ^ 11 * z ^ 3 + (-27407031 / 1024 : ℂ) * t ^ 11 * z + (-426 : ℂ) * t ^ 10 * c ^ 9 * z ^ 11 + (537 / 2 : ℂ) * t ^ 10 * c ^ 9 * z ^ 9 + (-2575 / 8 : ℂ) * t ^ 10 * c ^ 9 * z ^ 7 + (9549 / 32 : ℂ) * t ^ 10 * c ^ 9 * z ^ 5 + (-29043 / 128 : ℂ) * t ^ 10 * c ^ 9 * z ^ 3 + (74913 / 512 : ℂ) * t ^ 10 * c ^ 9 * z + (-846 : ℂ) * t ^ 10 * c ^ 7 * z ^ 13 + (30447 / 2 : ℂ) * t ^ 10 * c ^ 7 * z ^ 11 + (-86387 / 8 : ℂ) * t ^ 10 * c ^ 7 * z ^ 9 + (147399 / 32 : ℂ) * t ^ 10 * c ^ 7 * z ^ 7 + (-403179 / 128 : ℂ) * t ^ 10 * c ^ 7 * z ^ 5 + (910047 / 512 : ℂ) * t ^ 10 * c ^ 7 * z ^ 3 + (-1807587 / 2048 : ℂ) * t ^ 10 * c ^ 7 * z + (-1290 : ℂ) * t ^ 10 * c ^ 5 * z ^ 13 + (-58475 / 2 : ℂ) * t ^ 10 * c ^ 5 * z ^ 11 + (413191 / 8 : ℂ) * t ^ 10 * c ^ 5 * z ^ 9 + (1119117 / 32 : ℂ) * t ^ 10 * c ^ 5 * z ^ 7 + (1555695 / 128 : ℂ) * t ^ 10 * c ^ 5 * z ^ 5 + (-3609051 / 512 : ℂ) * t ^ 10 * c ^ 5 * z ^ 3 + (6732855 / 2048 : ℂ) * t ^ 10 * c ^ 5 * z + (1578 : ℂ) * t ^ 10 * c ^ 3 * z ^ 13 + (-21349 / 2 : ℂ) * t ^ 10 * c ^ 3 * z ^ 11 + (-248423 / 8 : ℂ) * t ^ 10 * c ^ 3 * z ^ 9 + (-3473933 / 32 : ℂ) * t ^ 10 * c ^ 3 * z ^ 7 + (8208033 / 128 : ℂ) * t ^ 10 * c ^ 3 * z ^ 5 + (-19847733 / 512 : ℂ) * t ^ 10 * c ^ 3 * z ^ 3 + (48904905 / 2048 : ℂ) * t ^ 10 * c ^ 3 * z + (-954 : ℂ) * t ^ 10 * c * z ^ 13 + (67545 / 2 : ℂ) * t ^ 10 * c * z ^ 11 + (-169017 / 8 : ℂ) * t ^ 10 * c * z ^ 9 + (-5320599 / 32 : ℂ) * t ^ 10 * c * z ^ 7 + (1048551 / 128 : ℂ) * t ^ 10 * c * z ^ 5 + (-18110007 / 512 : ℂ) * t ^ 10 * c * z ^ 3 + (56107143 / 2048 : ℂ) * t ^ 10 * c * z + (180 : ℂ) * t ^ 9 * c ^ 8 * z ^ 13 + (-7473 / 2 : ℂ) * t ^ 9 * c ^ 8 * z ^ 11 + (25221 / 8 : ℂ) * t ^ 9 * c ^ 8 * z ^ 9 + (-58857 / 32 : ℂ) * t ^ 9 * c ^ 8 * z ^ 7 + (163533 / 128 : ℂ) * t ^ 9 * c ^ 8 * z ^ 5 + (-376929 / 512 : ℂ) * t ^ 9 * c ^ 8 * z ^ 3 + (757413 / 2048 : ℂ) * t ^ 9 * c ^ 8 * z + (228 : ℂ) * t ^ 9 * c ^ 6 * z ^ 13 + (19181 : ℂ) * t ^ 9 * c ^ 6 * z ^ 11 + (-81945 / 4 : ℂ) * t ^ 9 * c ^ 6 * z ^ 9 + (-131275 / 16 : ℂ) * t ^ 9 * c ^ 6 * z ^ 7 + (-128241 / 64 : ℂ) * t ^ 9 * c ^ 6 * z ^ 5 + (328653 / 256 : ℂ) * t ^ 9 * c ^ 6 * z ^ 3 + (-755913 / 1024 : ℂ) * t ^ 9 * c ^ 6 * z + (-1080 : ℂ) * t ^ 9 * c ^ 4 * z ^ 13 + (-8477 : ℂ) * t ^ 9 * c ^ 4 * z ^ 11 + (205541 / 4 : ℂ) * t ^ 9 * c ^ 4 * z ^ 9 + (480135 / 16 : ℂ) * t ^ 9 * c ^ 4 * z ^ 7 + (-380859 / 64 : ℂ) * t ^ 9 * c ^ 4 * z ^ 5 + (820527 / 256 : ℂ) * t ^ 9 * c ^ 4 * z ^ 3 + (-3017699 / 1024 : ℂ) * t ^ 9 * c ^ 4 * z + (1536 : ℂ) * t ^ 9 * c ^ 2 * z ^ 13 + (-39996 : ℂ) * t ^ 9 * c ^ 2 * z ^ 11 + (17549 : ℂ) * t ^ 9 * c ^ 2 * z ^ 9 + (-142677 / 4 : ℂ) * t ^ 9 * c ^ 2 * z ^ 7 + (644757 / 16 : ℂ) * t ^ 9 * c ^ 2 * z ^ 5 + (-1488405 / 64 : ℂ) * t ^ 9 * c ^ 2 * z ^ 3 + (3156373 / 256 : ℂ) * t ^ 9 * c ^ 2 * z + (-48 : ℂ) * t ^ 9 * z ^ 13 + (3636 : ℂ) * t ^ 9 * z ^ 11 + (-5761 : ℂ) * t ^ 9 * z ^ 9 + (-386987 / 4 : ℂ) * t ^ 9 * z ^ 7 + (991275 / 16 : ℂ) * t ^ 9 * z ^ 5 + (-1148907 / 64 : ℂ) * t ^ 9 * z ^ 3 + (2802891 / 256 : ℂ) * t ^ 9 * z + (451 : ℂ) * t ^ 8 * c ^ 9 * z ^ 11 + (-1019 / 4 : ℂ) * t ^ 8 * c ^ 9 * z ^ 9 + (3487 / 16 : ℂ) * t ^ 8 * c ^ 9 * z ^ 7 + (-9747 / 64 : ℂ) * t ^ 8 * c ^ 9 * z ^ 5 + (22935 / 256 : ℂ) * t ^ 8 * c ^ 9 * z ^ 3 + (-47211 / 1024 : ℂ) * t ^ 8 * c ^ 9 * z + (234 : ℂ) * t ^ 8 * c ^ 7 * z ^ 13 + (-15873 / 2 : ℂ) * t ^ 8 * c ^ 7 * z ^ 11 + (58597 / 8 : ℂ) * t ^ 8 * c ^ 7 * z ^ 9 + (-63945 / 32 : ℂ) * t ^ 8 * c ^ 7 * z ^ 7 + (126717 / 128 : ℂ) * t ^ 8 * c ^ 7 * z ^ 5 + (-224385 / 512 : ℂ) * t ^ 8 * c ^ 7 * z ^ 3 + (370773 / 2048 : ℂ) * t ^ 8 * c ^ 7 * z + (906 : ℂ) * t ^ 8 * c ^ 5 * z ^ 13 + (18407 / 2 : ℂ) * t ^ 8 * c ^ 5 * z ^ 11 + (-277667 / 8 : ℂ) * t ^ 8 * c ^ 5 * z ^ 9 + (-438369 / 32 : ℂ) * t ^ 8 * c ^ 5 * z ^ 7 + (-513339 / 128 : ℂ) * t ^ 8 * c ^ 5 * z ^ 5 + (780951 / 512 : ℂ) * t ^ 8 * c ^ 5 * z ^ 3 + (-860595 / 2048 : ℂ) * t ^ 8 * c ^ 5 * z + (-1182 : ℂ) * t ^ 8 * c ^ 3 * z ^ 13 + (41845 / 2 : ℂ) * t ^ 8 * c ^ 3 * z ^ 11 + (10427 / 8 : ℂ) * t ^ 8 * c ^ 3 * z ^ 9 + (1779109 / 32 : ℂ) * t ^ 8 * c ^ 3 * z ^ 7 + (-3881445 / 128 : ℂ) * t ^ 8 * c ^ 3 * z ^ 5 + (7264293 / 512 : ℂ) * t ^ 8 * c ^ 3 * z ^ 3 + (-14215781 / 2048 : ℂ) * t ^ 8 * c ^ 3 * z + (216 : ℂ) * t ^ 8 * c * z ^ 13 + (-12334 : ℂ) * t ^ 8 * c * z ^ 11 + (26523 / 2 : ℂ) * t ^ 8 * c * z ^ 9 + (896805 / 8 : ℂ) * t ^ 8 * c * z ^ 7 + (-427461 / 32 : ℂ) * t ^ 8 * c * z ^ 5 + (2374821 / 128 : ℂ) * t ^ 8 * c * z ^ 3 + (-5900805 / 512 : ℂ) * t ^ 8 * c * z + (-84 : ℂ) * t ^ 7 * c ^ 8 * z ^ 13 + (3777 / 2 : ℂ) * t ^ 7 * c ^ 8 * z ^ 11 + (-16221 / 8 : ℂ) * t ^ 7 * c ^ 8 * z ^ 9 + (26169 / 32 : ℂ) * t ^ 7 * c ^ 8 * z ^ 7 + (-53349 / 128 : ℂ) * t ^ 7 * c ^ 8 * z ^ 5 + (95121 / 512 : ℂ) * t ^ 7 * c ^ 8 * z ^ 3 + (-154557 / 2048 : ℂ) * t ^ 7 * c ^ 8 * z + (-444 : ℂ) * t ^ 7 * c ^ 6 * z ^ 13 + (-5511 : ℂ) * t ^ 7 * c ^ 6 * z ^ 11 + (46823 / 4 : ℂ) * t ^ 7 * c ^ 6 * z ^ 9 + (67025 / 16 : ℂ) * t ^ 7 * c ^ 6 * z ^ 7 + (50103 / 64 : ℂ) * t ^ 7 * c ^ 6 * z ^ 5 + (-106815 / 256 : ℂ) * t ^ 7 * c ^ 6 * z ^ 3 + (200903 / 1024 : ℂ) * t ^ 7 * c ^ 6 * z + (468 : ℂ) * t ^ 7 * c ^ 4 * z ^ 13 + (-3849 : ℂ) * t ^ 7 * c ^ 4 * z ^ 11 + (-70315 / 4 : ℂ) * t ^ 7 * c ^ 4 * z ^ 9 + (-182541 / 16 : ℂ) * t ^ 7 * c ^ 4 * z ^ 7 + (352797 / 64 : ℂ) * t ^ 7 * c ^ 4 * z ^ 5 + (-549293 / 256 : ℂ) * t ^ 7 * c ^ 4 * z ^ 3 + (1132989 / 1024 : ℂ) * t ^ 7 * c ^ 4 * z + (-384 : ℂ) * t ^ 7 * c ^ 2 * z ^ 13 + (16016 : ℂ) * t ^ 7 * c ^ 2 * z ^ 11 + (-14056 : ℂ) * t ^ 7 * c ^ 2 * z ^ 9 + (-10704 : ℂ) * t ^ 7 * c ^ 2 * z ^ 7 + (-13182 : ℂ) * t ^ 7 * c ^ 2 * z ^ 5 + (13031 / 2 : ℂ) * t ^ 7 * c ^ 2 * z ^ 3 + (-23919 / 8 : ℂ) * t ^ 7 * c ^ 2 * z + (-512 : ℂ) * t ^ 7 * z ^ 11 + (1752 : ℂ) * t ^ 7 * z ^ 9 + (34078 : ℂ) * t ^ 7 * z ^ 7 + (-56571 / 2 : ℂ) * t ^ 7 * z ^ 5 + (51687 / 8 : ℂ) * t ^ 7 * z ^ 3 + (-100871 / 32 : ℂ) * t ^ 7 * z + (-237 : ℂ) * t ^ 6 * c ^ 9 * z ^ 11 + (617 / 4 : ℂ) * t ^ 6 * c ^ 9 * z ^ 9 + (-1565 / 16 : ℂ) * t ^ 6 * c ^ 9 * z ^ 7 + (3297 / 64 : ℂ) * t ^ 6 * c ^ 9 * z ^ 5 + (-6069 / 256 : ℂ) * t ^ 6 * c ^ 9 * z ^ 3 + (10137 / 1024 : ℂ) * t ^ 6 * c ^ 9 * z + (54 : ℂ) * t ^ 6 * c ^ 7 * z ^ 13 + (4101 / 2 : ℂ) * t ^ 6 * c ^ 7 * z ^ 11 + (-24185 / 8 : ℂ) * t ^ 6 * c ^ 7 * z ^ 9 + (15693 / 32 : ℂ) * t ^ 6 * c ^ 7 * z ^ 7 + (-24417 / 128 : ℂ) * t ^ 6 * c ^ 7 * z ^ 5 + (36597 / 512 : ℂ) * t ^ 6 * c ^ 7 * z ^ 3 + (-53257 / 2048 : ℂ) * t ^ 6 * c ^ 7 * z + (-150 : ℂ) * t ^ 6 * c ^ 5 * z ^ 13 + (-1743 / 2 : ℂ) * t ^ 6 * c ^ 5 * z ^ 11 + (110359 / 8 : ℂ) * t ^ 6 * c ^ 5 * z ^ 9 + (92697 / 32 : ℂ) * t ^ 6 * c ^ 5 * z ^ 7 + (66903 / 128 : ℂ) * t ^ 6 * c ^ 5 * z ^ 5 + (-19911 / 512 : ℂ) * t ^ 6 * c ^ 5 * z ^ 3 + (-105673 / 2048 : ℂ) * t ^ 6 * c ^ 5 * z + (336 : ℂ) * t ^ 6 * c ^ 3 * z ^ 13 + (-9904 : ℂ) * t ^ 6 * c ^ 3 * z ^ 11 + (6582 : ℂ) * t ^ 6 * c ^ 3 * z ^ 9 + (-33833 / 2 : ℂ) * t ^ 6 * c ^ 3 * z ^ 7 + (71601 / 8 : ℂ) * t ^ 6 * c ^ 3 * z ^ 5 + (-108617 / 32 : ℂ) * t ^ 6 * c ^ 3 * z ^ 3 + (176641 / 128 : ℂ) * t ^ 6 * c ^ 3 * z + (1792 : ℂ) * t ^ 6 * c * z ^ 11 + (-4284 : ℂ) * t ^ 6 * c * z ^ 9 + (-45003 : ℂ) * t ^ 6 * c * z ^ 7 + (34059 / 4 : ℂ) * t ^ 6 * c * z ^ 5 + (-110187 / 16 : ℂ) * t ^ 6 * c * z ^ 3 + (221595 / 64 : ℂ) * t ^ 6 * c * z + (12 : ℂ) * t ^ 5 * c ^ 8 * z ^ 13 + (-867 / 2 : ℂ) * t ^ 5 * c ^ 8 * z ^ 11 + (6267 / 8 : ℂ) * t ^ 5 * c ^ 8 * z ^ 9 + (-6795 / 32 : ℂ) * t ^ 5 * c ^ 8 * z ^ 7 + (10443 / 128 : ℂ) * t ^ 5 * c ^ 8 * z ^ 5 + (-14859 / 512 : ℂ) * t ^ 5 * c ^ 8 * z ^ 3 + (20043 / 2048 : ℂ) * t ^ 5 * c ^ 8 * z + (72 : ℂ) * t ^ 5 * c ^ 6 * z ^ 13 + (786 : ℂ) * t ^ 5 * c ^ 6 * z ^ 11 + (-8401 / 2 : ℂ) * t ^ 5 * c ^ 6 * z ^ 9 + (-10127 / 8 : ℂ) * t ^ 5 * c ^ 6 * z ^ 7 + (-7089 / 32 : ℂ) * t ^ 5 * c ^ 6 * z ^ 5 + (11761 / 128 : ℂ) * t ^ 5 * c ^ 6 * z ^ 3 + (-17713 / 512 : ℂ) * t ^ 5 * c ^ 6 * z + (-144 : ℂ) * t ^ 5 * c ^ 4 * z ^ 13 + (2900 : ℂ) * t ^ 5 * c ^ 4 * z ^ 11 + (1757 : ℂ) * t ^ 5 * c ^ 4 * z ^ 9 + (12321 / 4 : ℂ) * t ^ 5 * c ^ 4 * z ^ 7 + (-31025 / 16 : ℂ) * t ^ 5 * c ^ 4 * z ^ 5 + (36481 / 64 : ℂ) * t ^ 5 * c ^ 4 * z ^ 3 + (-55281 / 256 : ℂ) * t ^ 5 * c ^ 4 * z + (-2432 : ℂ) * t ^ 5 * c ^ 2 * z ^ 11 + (4880 : ℂ) * t ^ 5 * c ^ 2 * z ^ 9 + (11688 : ℂ) * t ^ 5 * c ^ 2 * z ^ 7 + (3220 : ℂ) * t ^ 5 * c ^ 2 * z ^ 5 + (-1361 : ℂ) * t ^ 5 * c ^ 2 * z ^ 3 + (2109 / 4 : ℂ) * t ^ 5 * c ^ 2 * z + (-224 : ℂ) * t ^ 5 * z ^ 9 + (-7016 : ℂ) * t ^ 5 * z ^ 7 + (8778 : ℂ) * t ^ 5 * z ^ 5 + (-1537 : ℂ) * t ^ 5 * z ^ 3 + (2381 / 4 : ℂ) * t ^ 5 * z + (57 : ℂ) * t ^ 4 * c ^ 9 * z ^ 11 + (-237 / 4 : ℂ) * t ^ 4 * c ^ 9 * z ^ 9 + (433 / 16 : ℂ) * t ^ 4 * c ^ 9 * z ^ 7 + (-693 / 64 : ℂ) * t ^ 4 * c ^ 9 * z ^ 5 + (1017 / 256 : ℂ) * t ^ 4 * c ^ 9 * z ^ 3 + (-1405 / 1024 : ℂ) * t ^ 4 * c ^ 9 * z + (-18 : ℂ) * t ^ 4 * c ^ 7 * z ^ 13 + (-501 / 2 : ℂ) * t ^ 4 * c ^ 7 * z ^ 11 + (5605 / 8 : ℂ) * t ^ 4 * c ^ 7 * z ^ 9 + (-2181 / 32 : ℂ) * t ^ 4 * c ^ 7 * z ^ 7 + (3045 / 128 : ℂ) * t ^ 4 * c ^ 7 * z ^ 5 + (-4165 / 512 : ℂ) * t ^ 4 * c ^ 7 * z ^ 3 + (5541 / 2048 : ℂ) * t ^ 4 * c ^ 7 * z + (24 : ℂ) * t ^ 4 * c ^ 5 * z ^ 13 + (-286 : ℂ) * t ^ 4 * c ^ 5 * z ^ 11 + (-5759 / 2 : ℂ) * t ^ 4 * c ^ 5 * z ^ 9 + (-969 / 8 : ℂ) * t ^ 4 * c ^ 5 * z ^ 7 + (2937 / 32 : ℂ) * t ^ 4 * c ^ 5 * z ^ 5 + (-7849 / 128 : ℂ) * t ^ 4 * c ^ 5 * z ^ 3 + (14553 / 512 : ℂ) * t ^ 4 * c ^ 5 * z + (1600 : ℂ) * t ^ 4 * c ^ 3 * z ^ 11 + (-2960 : ℂ) * t ^ 4 * c ^ 3 * z ^ 9 + (2351 : ℂ) * t ^ 4 * c ^ 3 * z ^ 7 + (-6535 / 4 : ℂ) * t ^ 4 * c ^ 3 * z ^ 5 + (8503 / 16 : ℂ) * t ^ 4 * c ^ 3 * z ^ 3 + (-11831 / 64 : ℂ) * t ^ 4 * c ^ 3 * z + (560 : ℂ) * t ^ 4 * c * z ^ 9 + (10044 : ℂ) * t ^ 4 * c * z ^ 7 + (-3255 : ℂ) * t ^ 4 * c * z ^ 5 + (6963 / 4 : ℂ) * t ^ 4 * c * z ^ 3 + (-11211 / 16 : ℂ) * t ^ 4 * c * z + (36 : ℂ) * t ^ 3 * c ^ 8 * z ^ 11 + (-156 : ℂ) * t ^ 3 * c ^ 8 * z ^ 9 + (57 / 2 : ℂ) * t ^ 3 * c ^ 8 * z ^ 7 + (-69 / 8 : ℂ) * t ^ 3 * c ^ 8 * z ^ 5 + (81 / 32 : ℂ) * t ^ 3 * c ^ 8 * z ^ 3 + (-93 / 128 : ℂ) * t ^ 3 * c ^ 8 * z + (-40 : ℂ) * t ^ 3 * c ^ 6 * z ^ 11 + (888 : ℂ) * t ^ 3 * c ^ 6 * z ^ 9 + (206 : ℂ) * t ^ 3 * c ^ 6 * z ^ 7 + (73 / 2 : ℂ) * t ^ 3 * c ^ 6 * z ^ 5 + (-93 / 8 : ℂ) * t ^ 3 * c ^ 6 * z ^ 3 + (113 / 32 : ℂ) * t ^ 3 * c ^ 6 * z + (-512 : ℂ) * t ^ 3 * c ^ 4 * z ^ 11 + (564 : ℂ) * t ^ 3 * c ^ 4 * z ^ 9 + (-503 : ℂ) * t ^ 3 * c ^ 4 * z ^ 7 + (1295 / 4 : ℂ) * t ^ 3 * c ^ 4 * z ^ 5 + (-1175 / 16 : ℂ) * t ^ 3 * c ^ 4 * z ^ 3 + (1415 / 64 : ℂ) * t ^ 3 * c ^ 4 * z + (-640 : ℂ) * t ^ 3 * c ^ 2 * z ^ 9 + (-3536 : ℂ) * t ^ 3 * c ^ 2 * z ^ 7 + (-556 : ℂ) * t ^ 3 * c ^ 2 * z ^ 5 + (187 : ℂ) * t ^ 3 * c ^ 2 * z ^ 3 + (-235 / 4 : ℂ) * t ^ 3 * c ^ 2 * z + (640 : ℂ) * t ^ 3 * z ^ 7 + (-1660 : ℂ) * t ^ 3 * z ^ 5 + (211 : ℂ) * t ^ 3 * z ^ 3 + (-259 / 4 : ℂ) * t ^ 3 * z + (-5 : ℂ) * t ^ 2 * c ^ 9 * z ^ 11 + (49 / 4 : ℂ) * t ^ 2 * c ^ 9 * z ^ 9 + (-65 / 16 : ℂ) * t ^ 2 * c ^ 9 * z ^ 7 + (81 / 64 : ℂ) * t ^ 2 * c ^ 9 * z ^ 5 + (-97 / 256 : ℂ) * t ^ 2 * c ^ 9 * z ^ 3 + (113 / 1024 : ℂ) * t ^ 2 * c ^ 9 * z + (12 : ℂ) * t ^ 2 * c ^ 7 * z ^ 11 + (-91 : ℂ) * t ^ 2 * c ^ 7 * z ^ 9 + (27 / 4 : ℂ) * t ^ 2 * c ^ 7 * z ^ 7 + (-35 / 16 : ℂ) * t ^ 2 * c ^ 7 * z ^ 5 + (43 / 64 : ℂ) * t ^ 2 * c ^ 7 * z ^ 3 + (-51 / 256 : ℂ) * t ^ 2 * c ^ 7 * z + (64 : ℂ) * t ^ 2 * c ^ 5 * z ^ 11 + (194 : ℂ) * t ^ 2 * c ^ 5 * z ^ 9 + (-141 / 2 : ℂ) * t ^ 2 * c ^ 5 * z ^ 7 + (-307 / 8 : ℂ) * t ^ 2 * c ^ 5 * z ^ 5 + (419 / 32 : ℂ) * t ^ 2 * c ^ 5 * z ^ 3 + (-531 / 128 : ℂ) * t ^ 2 * c ^ 5 * z + (400 : ℂ) * t ^ 2 * c ^ 3 * z ^ 9 + (40 : ℂ) * t ^ 2 * c ^ 3 * z ^ 7 + (180 : ℂ) * t ^ 2 * c ^ 3 * z ^ 5 + (-52 : ℂ) * t ^ 2 * c ^ 3 * z ^ 3 + (31 / 2 : ℂ) * t ^ 2 * c ^ 3 * z + (-960 : ℂ) * t ^ 2 * c * z ^ 7 + (726 : ℂ) * t ^ 2 * c * z ^ 5 + (-531 / 2 : ℂ) * t ^ 2 * c * z ^ 3 + (675 / 8 : ℂ) * t ^ 2 * c * z + (12 : ℂ) * t * c ^ 8 * z ^ 9 + (-3 / 2 : ℂ) * t * c ^ 8 * z ^ 7 + (3 / 8 : ℂ) * t * c ^ 8 * z ^ 5 + (-3 / 32 : ℂ) * t * c ^ 8 * z ^ 3 + (3 / 128 : ℂ) * t * c ^ 8 * z + (-80 : ℂ) * t * c ^ 6 * z ^ 9 + (-14 : ℂ) * t * c ^ 6 * z ^ 7 + (-5 / 2 : ℂ) * t * c ^ 6 * z ^ 5 + (5 / 8 : ℂ) * t * c ^ 6 * z ^ 3 + (-5 / 32 : ℂ) * t * c ^ 6 * z + (-112 : ℂ) * t * c ^ 4 * z ^ 9 + (36 : ℂ) * t * c ^ 4 * z ^ 7 + (-21 : ℂ) * t * c ^ 4 * z ^ 5 + (15 / 4 : ℂ) * t * c ^ 4 * z ^ 3 + (-15 / 16 : ℂ) * t * c ^ 4 * z + (384 : ℂ) * t * c ^ 2 * z ^ 7 + (48 : ℂ) * t * c ^ 2 * z ^ 5 + (-12 : ℂ) * t * c ^ 2 * z ^ 3 + (3 : ℂ) * t * c ^ 2 * z + (144 : ℂ) * t * z ^ 5 + (-12 : ℂ) * t * z ^ 3 + (3 : ℂ) * t * z + (-1 : ℂ) * c ^ 9 * z ^ 9 + (1 / 4 : ℂ) * c ^ 9 * z ^ 7 + (-1 / 16 : ℂ) * c ^ 9 * z ^ 5 + (1 / 64 : ℂ) * c ^ 9 * z ^ 3 + (-1 / 256 : ℂ) * c ^ 9 * z + (6 : ℂ) * c ^ 7 * z ^ 9 + (-1 / 2 : ℂ) * c ^ 7 * z ^ 7 + (1 / 8 : ℂ) * c ^ 7 * z ^ 5 + (-1 / 32 : ℂ) * c ^ 7 * z ^ 3 + (1 / 128 : ℂ) * c ^ 7 * z + (8 : ℂ) * c ^ 5 * z ^ 9 + (10 : ℂ) * c ^ 5 * z ^ 7 + (7 / 2 : ℂ) * c ^ 5 * z ^ 5 + (-7 / 8 : ℂ) * c ^ 5 * z ^ 3 + (7 / 32 : ℂ) * c ^ 5 * z + (-32 : ℂ) * c ^ 3 * z ^ 7 + (-10 : ℂ) * c ^ 3 * z ^ 5 + (5 / 2 : ℂ) * c ^ 3 * z ^ 3 + (-5 / 8 : ℂ) * c ^ 3 * z + (-72 : ℂ) * c * z ^ 5 + (18 : ℂ) * c * z ^ 3 + (-9 / 2 : ℂ) * c * z) * hz

set_option maxHeartbeats 1000000 in
private lemma NUM5_eq (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NUMdef τ c 5 = NUMP5 (τ : ℂ) c (xiτ τ) (vτ τ : ℂ) (Pc τ c) (Qc τ c) /
      (Qc τ c * (((vτ τ : ℂ) + τ * xiτ τ) * ((vτ τ : ℂ) - τ * xiτ τ)) ^ 4 *
        (((vτ τ : ℂ) - (c - τ) * xiτ τ) * ((vτ τ : ℂ) + (c - τ) * xiτ τ)) ^ 4) := by
  have hxi := norm_xi_lt τ h1 h2
  have hxi' : ‖-xiτ τ‖ < 1 / 2 := by rwa [norm_neg]
  have hb1 := one_add_beta_ne τ h1 h2 _ hxi
  have hb2 := one_add_beta_ne τ h1 h2 _ hxi'
  have hQ := Qc_ne τ h1 h2.le c hc
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  obtain ⟨hAp, hAm, hLp, hLm⟩ := factors_ne τ h1 h2 c hc
  unfold NUMdef dPiJf
  rw [deriv_aJ τ 5 _ hb1, deriv_aJ τ 5 _ hb2]
  unfold aJ PiJ NUMP5
  simp only [Nat.cast_ofNat, Int.reduceSub, zpow_neg, zpow_ofNat]
  rw [hβC, hνC, fA (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0, fA' (τ : ℂ) (vτ τ : ℂ) (xiτ τ) hv0,
    fL (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0, fL' (τ : ℂ) c (vτ τ : ℂ) (xiτ τ) hv0]
  generalize (vτ τ : ℂ) + τ * xiτ τ = Ap at *
  generalize (vτ τ : ℂ) - τ * xiτ τ = Am at *
  generalize (vτ τ : ℂ) - (c - τ) * xiτ τ = Lp at *
  generalize (vτ τ : ℂ) + (c - τ) * xiτ τ = Lm at *
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hQ (pow_ne_zero _ (mul_ne_zero hAp hAm)))
    (pow_ne_zero _ (mul_ne_zero hLp hLm)))]
  field_simp
  ring

/-- The closed form of `T_5`. -/
private lemma TJ5_closed (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    TJ τ c 5 = Nc5 τ c / (((256 * Kt τ ^ 4 : ℝ) : ℂ) * Qc τ c ^ 2) := by
  have hz : xiτ τ ^ 2 = (τ : ℂ) ^ 2 - 1 / 4 := by
    rw [xi_sq τ h1 h2]
    unfold ysq
    push_cast
    ring
  have hvd : (vτ τ : ℂ) = 1 - (τ : ℂ) ^ 2 := by
    unfold vτ
    push_cast
    ring
  have hsd : (ysq τ : ℂ) = 1 / 4 - (τ : ℂ) ^ 2 := by
    unfold ysq
    push_cast
    ring
  have hs0 : (ysq τ : ℂ) ≠ 0 := by exact_mod_cast (ysq_pos τ h1 h2).ne'
  have hv0 : (vτ τ : ℂ) ≠ 0 := by exact_mod_cast (v_pos τ h1 h2.le).ne'
  have hz0 := xi_ne τ h1 h2
  have hQ0 := Qc_ne τ h1 h2.le c hc
  rw [Qc_C, QcC_F] at hQ0
  have hF1 : F1p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hF2 : F2p (τ : ℂ) c ≠ 0 := fun h => hQ0 (by rw [h]; ring)
  have hW0 : (4 - 7 * (τ : ℂ) ^ 2) ≠ 0 := by
    have h47 : (4 : ℝ) - 7 * τ ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast h47
  rw [TJ_eq τ h1 h2 5 c hc, TJf_eq, NUM5_eq τ h1 h2 c hc, DEN_eq τ h1 h2 c hc, Pc_C, Qc_C,
    core5 (τ : ℂ) c (xiτ τ) _ _ hz hvd hsd, relAA _ _ _ hz hvd, relLL _ _ _ _ hz hvd,
    relX _ _ _ _ hz hvd, Nc5_C, QcC_F]
  rw [show ((256 * Kt τ ^ 4 : ℝ) : ℂ) = 256 * (-(4 - 7 * (τ : ℂ) ^ 2)) ^ 4 by unfold Kt; push_cast; ring]
  generalize F1p (τ : ℂ) c = F1 at *
  generalize F2p (τ : ℂ) c = F2 at *
  generalize Ncp5 (τ : ℂ) c = N at *
  generalize (4 - 7 * (τ : ℂ) ^ 2) = W at *
  generalize xiτ τ = z at *
  generalize (vτ τ : ℂ) = v at *
  generalize (ysq τ : ℂ) = s at *
  field_simp
  ring

/-! ### Row `lem_4_5_i` -/

theorem lem_4_5_i_proved (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ∑ j ∈ Finset.Icc 2 5, ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) ≤ 20 + 130 * edef c :=
  lem_4_5_i_of_circle τ h1 h2
    (fun w hw => lem45_circle_of_closed τ h1 h2 w hw (TJ2_closed τ h1 h2 w hw.le) (TJ3_closed τ h1 h2 w hw.le)
      (TJ4_closed τ h1 h2 w hw.le) (TJ5_closed τ h1 h2 w hw.le)) c hc

end Robinson.Proofs
