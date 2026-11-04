/-
Robinson/Proofs/LamNonneg.lean — proofs of sec4_Lam_nonneg.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Near

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The weights `𝔥[Z]` and `𝔴[Z]` through the values and derivatives of `Z` at `±y₀` -/

private lemma y0_pos : (0 : ℝ) < y0 := by norm_num [y0]

/-- `Z_o'(y₀) = (Z'(y₀) + Z'(-y₀))/2` and `Z_e'(y₀) = (Z'(y₀) - Z'(-y₀))/2`. -/
private lemma frakW_eq (Z : ℝ → ℝ) (D1 D2 : ℝ) (h1 : HasDerivAt Z D1 y0) (h2 : HasDerivAt Z D2 (-y0)) :
    frakW Z = (y0 * ((D1 + D2) / 2) + 7 / 3 * oddPart Z y0) / y0 ^ 3 + (D1 - D2) / 2 / (2 * y0 ^ 3) := by
  have hneg : HasDerivAt (fun x => Z (-x)) (D2 * (-1)) y0 := h2.comp y0 (hasDerivAt_neg y0)
  have ho : HasDerivAt (oddPart Z) ((D1 - D2 * (-1)) / 2) y0 := (h1.fun_sub hneg).div_const 2
  have he : HasDerivAt (evenPart Z) ((D1 + D2 * (-1)) / 2) y0 := (h1.fun_add hneg).div_const 2
  unfold frakW
  rw [ho.deriv, he.deriv]
  ring

/-- `𝔴[Z] ≥ 0` when `Z_o(y₀) ≥ 0`, `Z'(y₀) ≥ 0` and `Z'(-y₀) ≤ Z'(y₀)`: the numerator of `𝔴[Z]` is
`y₀ Z'(y₀) + (¼ - y₀/2)(Z'(y₀) - Z'(-y₀)) + (7/3) Z_o(y₀)`. -/
private lemma frakW_nonneg_of (Z : ℝ → ℝ) (D1 D2 : ℝ) (h1 : HasDerivAt Z D1 y0) (h2 : HasDerivAt Z D2 (-y0))
    (hD1 : 0 ≤ D1) (hD12 : D2 ≤ D1) (hodd : 0 ≤ oddPart Z y0) : 0 ≤ frakW Z := by
  rw [frakW_eq Z D1 D2 h1 h2]
  have hy := y0_pos
  have key : (y0 * ((D1 + D2) / 2) + 7 / 3 * oddPart Z y0) / y0 ^ 3 + (D1 - D2) / 2 / (2 * y0 ^ 3) =
      (D1 * y0 + (D1 - D2) * (1 / 4 - y0 / 2) + 7 / 3 * oddPart Z y0) / y0 ^ 3 := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  have hc : 0 ≤ 1 / 4 - y0 / 2 := by norm_num [y0]
  have := mul_nonneg (sub_nonneg.mpr hD12) hc
  nlinarith [mul_nonneg hD1 hy.le]

/-- `Z_o(y₀) ≥ 0` when `Z(y₀) ≥ 0 ≥ Z(-y₀)`. -/
private lemma oddPart_nonneg_of (Z : ℝ → ℝ) (hp : 0 ≤ Z y0) (hn : Z (-y0) ≤ 0) : 0 ≤ oddPart Z y0 := by
  unfold oddPart
  linarith

/-- `𝔥[Z] ≥ 0` when `Z(y₀) ≥ 0 ≥ Z(-y₀)`. -/
private lemma frakH_nonneg_of (Z : ℝ → ℝ) (hp : 0 ≤ Z y0) (hn : Z (-y0) ≤ 0) : 0 ≤ frakH Z :=
  div_nonneg (oddPart_nonneg_of Z hp hn) y0_pos.le

/-! ### Derivatives of the pieces -/

/-- The bracket `K = 2/(a³d) + 1/(a²d²)` of `Z₂` has a nonnegative derivative where `a, d > 0` are
nonincreasing. -/
private lemma K_deriv (a d : ℝ → ℝ) (p q x : ℝ) (ha : HasDerivAt a (-p) x) (hd : HasDerivAt d (-q) x)
    (ha0 : 0 < a x) (hd0 : 0 < d x) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∃ K', HasDerivAt (fun y => 2 / (a y ^ 3 * d y) + 1 / (a y ^ 2 * d y ^ 2)) K' x ∧ 0 ≤ K' := by
  have h1 := (hasDerivAt_const x (2 : ℝ)).fun_div ((ha.fun_pow 3).fun_mul hd) (by positivity)
  have h2 := (hasDerivAt_const x (1 : ℝ)).fun_div ((ha.fun_pow 2).fun_mul (hd.fun_pow 2)) (by positivity)
  refine ⟨2 * (3 * a x ^ 2 * p * d x + a x ^ 3 * q) / (a x ^ 3 * d x) ^ 2 +
      (2 * a x * p * d x ^ 2 + 2 * a x ^ 2 * d x * q) / (a x ^ 2 * d x ^ 2) ^ 2,
    (h1.fun_add h2).congr_deriv ?_, by positivity⟩
  norm_num
  ring

/-- `N₊'(x) = 1 + (4/3)x`. -/
private lemma Nplus_hasDerivAt (x : ℝ) : HasDerivAt Nplus (1 + 4 / 3 * x) x :=
  ((hasDerivAt_id' x).fun_mul (((hasDerivAt_id' x).const_mul (2 / 3 : ℝ)).const_add 1)).congr_deriv (by ring)

/-- `𝔞'(x) = -ν⁺`. -/
private lemma fa_hasDerivAt (νp x : ℝ) : HasDerivAt (faOf νp) (-νp) x :=
  (((hasDerivAt_id' x).const_mul νp).const_sub 1).congr_deriv (by ring)

/-- `B₁'(x) = (16/15)(2x(1 - 2x) + 2x²)/(1 - 2x)²`. -/
private noncomputable def B1d (x : ℝ) : ℝ := 16 / 15 * ((2 * x * (1 - 2 * x) + 2 * x ^ 2) / (1 - 2 * x) ^ 2)

private lemma B1_hasDerivAt (x : ℝ) (hw : 1 - 2 * x ≠ 0) : HasDerivAt B1 (B1d x) x := by
  have hw' : HasDerivAt (fun y => 1 - 2 * y) (-(2 * 1)) x :=
    ((hasDerivAt_id' x).const_mul (2 : ℝ)).const_sub 1
  refine ((((hasDerivAt_id' x).fun_pow 2).fun_div hw' hw).const_mul (16 / 15 : ℝ)).congr_deriv ?_
  unfold B1d
  norm_num
  ring

/-- `𝔡'(x) = -(ν⁺ + √η⁺ B₁'(x))`. -/
private lemma fd_hasDerivAt (νp ηp x : ℝ) (hw : 1 - 2 * x ≠ 0) :
    HasDerivAt (fdOf νp ηp) (-(νp + Real.sqrt ηp * B1d x)) x :=
  ((fa_hasDerivAt νp x).fun_sub ((B1_hasDerivAt x hw).const_mul (Real.sqrt ηp))).congr_deriv (by ring)

/-- `(N₊B₂)'(y₀) ≥ 1/40` (its value is `0.02759…`). -/
private lemma P_deriv_at_pos : ∃ D, HasDerivAt (fun y => Nplus y * B2 y) D y0 ∧ 1 / 40 ≤ D := by
  have hu : HasDerivAt (fun y => 1 - 2 / 3 * y) (-(2 / 3 * 1)) y0 :=
    ((hasDerivAt_id' y0).const_mul (2 / 3 : ℝ)).const_sub 1
  have hw : HasDerivAt (fun y => 1 - 2 * y) (-(2 * 1)) y0 := ((hasDerivAt_id' y0).const_mul (2 : ℝ)).const_sub 1
  have hu0 : (1 - 2 / 3 * y0 : ℝ) ≠ 0 := by norm_num [y0]
  have hw0 : (1 - 2 * y0 : ℝ) ≠ 0 := by norm_num [y0]
  have t1 := (((hasDerivAt_id' y0).fun_pow 4).fun_div (hu.fun_pow 2) (pow_ne_zero 2 hu0)).const_mul (256 / 243 : ℝ)
  have t2 := (((hasDerivAt_id' y0).fun_pow 5).fun_div ((hu.fun_pow 2).fun_mul hw)
    (mul_ne_zero (pow_ne_zero 2 hu0) hw0)).const_mul (4096 / 3645 : ℝ)
  have hB2 : HasDerivAt B2 _ y0 := t1.fun_add t2
  refine ⟨_, (Nplus_hasDerivAt y0).fun_mul hB2, ?_⟩
  norm_num [Nplus, B2, y0]

/-- `0 ≤ (N₊B₂)'(-y₀) ≤ 1/100` (its value is `0.00529…`). -/
private lemma P_deriv_at_neg :
    ∃ D, HasDerivAt (fun y => Nplus y * B2 y) D (-y0) ∧ 0 ≤ D ∧ D ≤ 1 / 100 := by
  have hu : HasDerivAt (fun y => 1 - 2 / 3 * y) (-(2 / 3 * 1)) (-y0) :=
    ((hasDerivAt_id' (-y0)).const_mul (2 / 3 : ℝ)).const_sub 1
  have hw : HasDerivAt (fun y => 1 - 2 * y) (-(2 * 1)) (-y0) :=
    ((hasDerivAt_id' (-y0)).const_mul (2 : ℝ)).const_sub 1
  have hu0 : (1 - 2 / 3 * -y0 : ℝ) ≠ 0 := by norm_num [y0]
  have hw0 : (1 - 2 * -y0 : ℝ) ≠ 0 := by norm_num [y0]
  have t1 := (((hasDerivAt_id' (-y0)).fun_pow 4).fun_div (hu.fun_pow 2) (pow_ne_zero 2 hu0)).const_mul
    (256 / 243 : ℝ)
  have t2 := (((hasDerivAt_id' (-y0)).fun_pow 5).fun_div ((hu.fun_pow 2).fun_mul hw)
    (mul_ne_zero (pow_ne_zero 2 hu0) hw0)).const_mul (4096 / 3645 : ℝ)
  have hB2 : HasDerivAt B2 _ (-y0) := t1.fun_add t2
  refine ⟨_, (Nplus_hasDerivAt (-y0)).fun_mul hB2, ?_, ?_⟩
  · norm_num [Nplus, B2, y0]
  · norm_num [Nplus, B2, y0]

/-! ### Rational values at `±y₀` -/

private lemma Nplus_at_pos : 0 < Nplus y0 := by norm_num [Nplus, y0]

private lemma Nplus_at_neg : Nplus (-y0) < 0 := by norm_num [Nplus, y0]

private lemma B1_at_pos : 0 < B1 y0 ∧ B1 y0 ≤ 1 / 10 := by constructor <;> norm_num [B1, y0]

private lemma B1_at_neg : 0 < B1 (-y0) ∧ B1 (-y0) ≤ 1 / 20 := by constructor <;> norm_num [B1, y0]

private lemma B2_at_pos : 0 < B2 y0 := by norm_num [B2, y0]

/-- `B₂(-y₀) = y₀⁴/(1 + ⅔y₀)² · [256/243 - (4096/3645) y₀/(1 + 2y₀)] > 0`. -/
private lemma B2_at_neg : 0 < B2 (-y0) := by norm_num [B2, y0]

private lemma B1d_at_pos : 0 ≤ B1d y0 := by norm_num [B1d, y0]

private lemma B1d_at_neg : -3 / 10 ≤ B1d (-y0) := by norm_num [B1d, y0]

/-! ### The box `20/29 ≤ ν⁺ ≤ 2`, `η⁺ ≤ 1` (so `0 ≤ √η⁺ ≤ 1`) -/

private lemma sqrt_box (ηp : ℝ) (h : ηp ≤ 1) : 0 ≤ Real.sqrt ηp ∧ Real.sqrt ηp ≤ 1 :=
  ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr h⟩

/-- At `y₀`: `0 < 𝔡(y₀) ≤ 𝔞(y₀) ≤ 1`. -/
private lemma fa_fd_at_pos (νp ηp : ℝ) (h1 : 20 / 29 ≤ νp) (h2 : νp ≤ 2) (h3 : ηp ≤ 1) :
    0 < fdOf νp ηp y0 ∧ fdOf νp ηp y0 ≤ faOf νp y0 ∧ faOf νp y0 ≤ 1 := by
  obtain ⟨hs0, hs1⟩ := sqrt_box ηp h3
  obtain ⟨hb0, hb1⟩ := B1_at_pos
  have hy : y0 = 17 / 80 := rfl
  have hsb : Real.sqrt ηp * B1 y0 ≤ 1 / 10 := by nlinarith [mul_le_mul_of_nonneg_right hs1 hb0.le]
  have hsb0 : 0 ≤ Real.sqrt ηp * B1 y0 := mul_nonneg hs0 hb0.le
  have hνy : νp * y0 ≤ 17 / 40 := by rw [hy]; nlinarith
  have hνy0 : 0 ≤ νp * y0 := by rw [hy]; nlinarith
  unfold fdOf faOf
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- At `-y₀`: `𝔞(-y₀) ≥ 1` and `𝔡(-y₀) ≥ 9/10`. -/
private lemma fa_fd_at_neg (νp ηp : ℝ) (h1 : 20 / 29 ≤ νp) (h3 : ηp ≤ 1) :
    1 ≤ faOf νp (-y0) ∧ 9 / 10 ≤ fdOf νp ηp (-y0) := by
  obtain ⟨hs0, hs1⟩ := sqrt_box ηp h3
  obtain ⟨hb0, hb1⟩ := B1_at_neg
  have hy : y0 = 17 / 80 := rfl
  have hsb : Real.sqrt ηp * B1 (-y0) ≤ 1 / 20 := by nlinarith [mul_le_mul_of_nonneg_right hs1 hb0.le]
  have ha : 1 ≤ faOf νp (-y0) := by
    unfold faOf
    rw [hy]
    nlinarith
  refine ⟨ha, ?_⟩
  unfold fdOf
  linarith

/-- `K(y₀) ≥ 2` when `0 < 𝔡 ≤ 𝔞 ≤ 1`. -/
private lemma K_lower (A Dd : ℝ) (hD : 0 < Dd) (hDA : Dd ≤ A) (hA1 : A ≤ 1) :
    2 ≤ 2 / (A ^ 3 * Dd) + 1 / (A ^ 2 * Dd ^ 2) := by
  have hA : 0 < A := lt_of_lt_of_le hD hDA
  have hp : 0 < A ^ 3 * Dd := by positivity
  have hle : A ^ 3 * Dd ≤ 1 := by
    have := mul_le_mul (pow_le_one₀ (n := 3) hA.le hA1) (le_trans hDA hA1) hD.le zero_le_one
    linarith
  have h2 : 2 ≤ 2 / (A ^ 3 * Dd) := (le_div_iff₀ hp).mpr (by linarith)
  have h3 : 0 ≤ 1 / (A ^ 2 * Dd ^ 2) := by positivity
  linarith

/-- `K(-y₀) ≤ 4` when `𝔞 ≥ 1` and `𝔡 ≥ 9/10`. -/
private lemma K_upper (A Dd : ℝ) (hA : 1 ≤ A) (hD : 9 / 10 ≤ Dd) :
    2 / (A ^ 3 * Dd) + 1 / (A ^ 2 * Dd ^ 2) ≤ 4 := by
  have hA3 : 1 ≤ A ^ 3 := one_le_pow₀ hA
  have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA
  have hD2 : 81 / 100 ≤ Dd ^ 2 := by nlinarith
  have hp1 : 9 / 10 ≤ A ^ 3 * Dd := by nlinarith
  have hp2 : 81 / 100 ≤ A ^ 2 * Dd ^ 2 := by nlinarith
  have h1 : 2 / (A ^ 3 * Dd) ≤ 20 / 9 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have h2 : 1 / (A ^ 2 * Dd ^ 2) ≤ 100 / 81 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

/-! ### Signs of `Z₁, Z₂` at `±y₀` and the weights `𝔥` -/

private lemma Z1_signs (νp ηp : ℝ) (h1 : 20 / 29 ≤ νp) (h2 : νp ≤ 2) (h3 : ηp ≤ 1) :
    0 ≤ Z1Of νp ηp y0 ∧ Z1Of νp ηp (-y0) ≤ 0 := by
  obtain ⟨hdp, hdap, -⟩ := fa_fd_at_pos νp ηp h1 h2 h3
  obtain ⟨han, hdn⟩ := fa_fd_at_neg νp ηp h1 h3
  have hap : 0 < faOf νp y0 := lt_of_lt_of_le hdp hdap
  have han' : 0 < faOf νp (-y0) := by linarith
  have hdn' : 0 < fdOf νp ηp (-y0) := by linarith
  have hN1 := Nplus_at_pos
  have hN2 := Nplus_at_neg
  have hB1 := B1_at_pos.1
  have hB2 := B1_at_neg.1
  unfold Z1Of
  constructor
  · positivity
  · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hN2.le hB2.le) (by positivity)

private lemma Z2_signs (νp ηp : ℝ) (h1 : 20 / 29 ≤ νp) (h2 : νp ≤ 2) (h3 : ηp ≤ 1) :
    0 ≤ Z2Of νp ηp y0 ∧ Z2Of νp ηp (-y0) ≤ 0 := by
  obtain ⟨hdp, hdap, -⟩ := fa_fd_at_pos νp ηp h1 h2 h3
  obtain ⟨han, hdn⟩ := fa_fd_at_neg νp ηp h1 h3
  have hap : 0 < faOf νp y0 := lt_of_lt_of_le hdp hdap
  have han' : 0 < faOf νp (-y0) := by linarith
  have hdn' : 0 < fdOf νp ηp (-y0) := by linarith
  have hN1 := Nplus_at_pos
  have hN2 := Nplus_at_neg
  have hB1 := B2_at_pos
  have hB2 := B2_at_neg
  unfold Z2Of
  constructor
  · positivity
  · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hN2.le hB2.le) (by positivity)

private lemma frakH_Z1_nonneg (νp ηp : ℝ) (h1 : 20 / 29 ≤ νp) (h2 : νp ≤ 2) (h3 : ηp ≤ 1) :
    0 ≤ frakH (Z1Of νp ηp) :=
  frakH_nonneg_of _ (Z1_signs νp ηp h1 h2 h3).1 (Z1_signs νp ηp h1 h2 h3).2

private lemma frakH_Z2_nonneg (νp ηp : ℝ) (h1 : 20 / 29 ≤ νp) (h2 : νp ≤ 2) (h3 : ηp ≤ 1) :
    0 ≤ frakH (Z2Of νp ηp) :=
  frakH_nonneg_of _ (Z2_signs νp ηp h1 h2 h3).1 (Z2_signs νp ηp h1 h2 h3).2

/-! ### The weight `𝔴[Z₂]`

`Z₂ = P · K` with `P = N₊B₂` (no caps) and `K = 2/(𝔞³𝔡) + 1/(𝔞²𝔡²)`. At `y₀`: `P, P', K, K' ≥ 0` and
`P'(y₀) ≥ 1/40`, `K(y₀) ≥ 2`, so `Z₂'(y₀) ≥ 1/20`. At `-y₀`: `P(-y₀) < 0 ≤ K'(-y₀)`, `0 ≤ P'(-y₀) ≤ 1/100`,
`0 ≤ K(-y₀) ≤ 4`, so `Z₂'(-y₀) ≤ 1/25`. -/

private lemma frakW_Z2_nonneg (νp ηp : ℝ) (h1 : 20 / 29 ≤ νp) (h2 : νp ≤ 2) (h3 : ηp ≤ 1) :
    0 ≤ frakW (Z2Of νp ηp) := by
  obtain ⟨hs0, hs1⟩ := sqrt_box ηp h3
  obtain ⟨hdp, hdap, hap1⟩ := fa_fd_at_pos νp ηp h1 h2 h3
  obtain ⟨han, hdn⟩ := fa_fd_at_neg νp ηp h1 h3
  have hap : 0 < faOf νp y0 := lt_of_lt_of_le hdp hdap
  have hw1 : (1 - 2 * y0 : ℝ) ≠ 0 := by norm_num [y0]
  have hw2 : (1 - 2 * -y0 : ℝ) ≠ 0 := by norm_num [y0]
  have hq1 : 0 ≤ νp + Real.sqrt ηp * B1d y0 := by
    have := mul_nonneg hs0 B1d_at_pos
    linarith
  have hq2 : 0 ≤ νp + Real.sqrt ηp * B1d (-y0) := by
    have := mul_nonneg hs0 (by linarith [B1d_at_neg] : (0 : ℝ) ≤ B1d (-y0) + 3 / 10)
    nlinarith
  obtain ⟨K1, hK1, hK1n⟩ := K_deriv (faOf νp) (fdOf νp ηp) νp _ y0 (fa_hasDerivAt νp y0)
    (fd_hasDerivAt νp ηp y0 hw1) hap hdp (by linarith) hq1
  obtain ⟨K2, hK2, hK2n⟩ := K_deriv (faOf νp) (fdOf νp ηp) νp _ (-y0) (fa_hasDerivAt νp (-y0))
    (fd_hasDerivAt νp ηp (-y0) hw2) (by linarith) (by linarith) (by linarith) hq2
  obtain ⟨P1, hP1, hP1b⟩ := P_deriv_at_pos
  obtain ⟨P2, hP2, hP2a, hP2b⟩ := P_deriv_at_neg
  have hKv1 := K_lower _ _ hdp hdap hap1
  have hKv2 := K_upper _ _ han hdn
  have hKv2n : 0 ≤ 2 / (faOf νp (-y0) ^ 3 * fdOf νp ηp (-y0)) + 1 / (faOf νp (-y0) ^ 2 * fdOf νp ηp (-y0) ^ 2) := by
    have : 0 < faOf νp (-y0) := by linarith
    have : 0 < fdOf νp ηp (-y0) := by linarith
    positivity
  have hPv1 : 0 ≤ Nplus y0 * B2 y0 := mul_nonneg Nplus_at_pos.le B2_at_pos.le
  have hPv2 : Nplus (-y0) * B2 (-y0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg Nplus_at_neg.le B2_at_neg.le
  refine frakW_nonneg_of (Z2Of νp ηp) _ _ (hP1.fun_mul hK1) (hP2.fun_mul hK2) ?_ ?_
    (oddPart_nonneg_of _ (Z2_signs νp ηp h1 h2 h3).1 (Z2_signs νp ηp h1 h2 h3).2)
  · exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hPv1 hK1n)
  · have e1 := mul_nonpos_of_nonpos_of_nonneg hPv2 hK2n
    have e2 := mul_le_mul hP2b hKv2 hKv2n (by norm_num)
    have e3 := mul_le_mul hP1b hKv1 (by norm_num) (by linarith)
    have e4 := mul_nonneg hPv1 hK1n
    linarith

/-! ### `T⁺ ≥ 0`, `Π₋ > 0`, and `Λ ≥ 0` on the box -/

private lemma TPlusOf_nonneg (νp : ℝ) (h0 : 0 ≤ νp) (h2 : νp ≤ 2) : 0 ≤ TPlusOf νp := by
  have h3 : νp ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h2 3
  have h4 : νp ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h2 4
  have hy := y0_pos
  unfold TPlusOf calVOf
  apply div_nonneg
  · positivity
  · rw [show y0 = 17 / 80 from rfl]
    nlinarith [pow_nonneg h0 3, pow_nonneg h0 4]

/-- `Π₋ ≥ 1 - ε(y₀) = 0.42… > 0`. -/
private lemma PiLowOf_pos (νp ηp : ℝ) : 0 < PiLowOf νp ηp :=
  lt_of_lt_of_le (by norm_num [epsY0, epsOf, y0]) (le_max_left _ _)

private lemma LamOf_nonneg (νp ηp np : ℝ) (h1 : 20 / 29 ≤ νp) (h2 : νp ≤ 2) (h3 : ηp ≤ 1) (hn : 0 ≤ np) :
    0 ≤ LamOf νp ηp np :=
  div_nonneg
    (add_nonneg
      (add_nonneg (frakW_Z2_nonneg νp ηp h1 h2 h3)
        (mul_nonneg (TPlusOf_nonneg νp (by linarith) h2) (frakH_Z2_nonneg νp ηp h1 h2 h3)))
      (mul_nonneg hn (frakH_Z1_nonneg νp ηp h1 h2 h3)))
    (PiLowOf_pos νp ηp).le

/-! ### The row -/

/-- On every cell `[i/256, (i+1)/256]`: `20/29 ≤ ν⁺ ≤ 2`, `η⁺ ≤ 1` and `n⁺ ≥ 0`, so `Λ ≥ 0`. -/
theorem sec4_Lam_nonneg_proved : ∀ i : ℕ, i ≤ 255 → 0 ≤ Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) := by
  intro i _
  have hρ : (0 : ℝ) ≤ (i : ℝ) / 256 := by positivity
  unfold Lam
  exact LamOf_nonneg _ _ _ (le_max_left _ _) (max_le (by norm_num) (by linarith)) (min_le_left _ _)
    (Real.sqrt_nonneg _)

end Robinson.Proofs
