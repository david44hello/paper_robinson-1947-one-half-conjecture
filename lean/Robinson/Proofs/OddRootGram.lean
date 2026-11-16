/-
Robinson/Proofs/OddRootGram.lean — proofs of sec3_oddroot_exists, sec3_oddroot_mem_S, eq_gram,
sec5_a_conj, sec5_uv_gram, sec6_UV_values, sec7_be_deriv, sec7_gram, sec3_oddroot_parity, sec7_identity_O2.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Matrix2
import Robinson.Defs.Far
import Robinson.Defs.Grunsky

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## Elementary series -/

/-- For `Re a > 0` and `Re b > 0` the principal logarithm satisfies `log(a/b) = log a - log b`
(both arguments lie in `(-π/2, π/2)`). -/
private theorem log_div_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    log (a / b) = log a - log b := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hA : |arg a| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hB : |arg b| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hexp : a / b = exp (log a - log b) := by rw [exp_sub, exp_log ha0, exp_log hb0]
  rw [hexp, log_exp]
  · rw [sub_im, log_im, log_im]
    have := abs_lt.mp hA
    have := abs_lt.mp hB
    linarith
  · rw [sub_im, log_im, log_im]
    have := abs_lt.mp hA
    have := abs_lt.mp hB
    linarith

/-- `∑_{n odd} wⁿ/n = artanh w` for `|w| < 1`. -/
private theorem hasSum_odd_artanh {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => if n % 2 = 1 then w ^ n / n else 0) (cartanh w) := by
  have h1 := hasSum_taylorSeries_neg_log hw
  have h2 := hasSum_taylorSeries_neg_log (z := -w) (by rwa [norm_neg])
  have h3 := (h1.sub h2).div_const 2
  have hre1 : 0 < (1 + w).re := by
    have := abs_le.mp (abs_re_le_norm w)
    simp only [add_re, one_re]; linarith
  have hre2 : 0 < (1 - w).re := by
    have := abs_le.mp (abs_re_le_norm w)
    simp only [sub_re, one_re]; linarith
  convert h3 using 1
  · funext n
    rcases Nat.even_or_odd n with he | ho
    · have : n % 2 ≠ 1 := by rw [Nat.even_iff] at he; omega
      rw [ite_eq_right this, he.neg_pow]; ring
    · have : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [ite_eq_left this, ho.neg_pow]; ring
  · rw [cartanh, log_div_of_re_pos hre1 hre2, sub_neg_eq_add]; ring

/-- `∑_{n even, n ≥ 2} wⁿ/n = -½ log(1 - w²)` for `|w| < 1`. -/
private theorem hasSum_even_log {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => if n % 2 = 0 ∧ n ≠ 0 then w ^ n / n else 0) (-(1 / 2 : ℂ) * log (1 - w ^ 2)) := by
  have hw2 : ‖w ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg w]
  have h := (hasSum_taylorSeries_neg_log hw2).mul_left (1 / 2 : ℂ)
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · convert h using 1
    · funext k
      simp only [Function.comp_apply]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have h2k : (2 * k) % 2 = 0 ∧ 2 * k ≠ 0 := ⟨by omega, by omega⟩
        rw [ite_eq_left h2k, ← pow_mul]
        have : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        push_cast
        field_simp
    · ring
  · intro x hx
    have : ¬ (x % 2 = 0 ∧ x ≠ 0) := by
      rintro ⟨h0, -⟩
      exact hx ⟨x / 2, by simp only; omega⟩
    rw [ite_eq_right this]

/-- `∑ n wⁿ` with the index `0` dropped, as a sum over even `n = 2k` with weight `2k`:
`∑_{n even, n ≥ 2} n wⁿ = 2w²/(1 - w²)²`. -/
private theorem hasSum_even_mul_geom {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => if n % 2 = 0 ∧ n ≠ 0 then (n : ℂ) * w ^ n else 0) (2 * w ^ 2 / (1 - w ^ 2) ^ 2) := by
  have hw2 : ‖w ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg w]
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hw2).mul_left (2 : ℂ)
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · convert h using 1
    · funext k
      simp only [Function.comp_apply]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have h2k : (2 * k) % 2 = 0 ∧ 2 * k ≠ 0 := ⟨by omega, by omega⟩
        rw [ite_eq_left h2k, ← pow_mul]
        push_cast
        ring
    · ring
  · intro x hx
    have : ¬ (x % 2 = 0 ∧ x ≠ 0) := by
      rintro ⟨h0, -⟩
      exact hx ⟨x / 2, by simp only; omega⟩
    rw [ite_eq_right this]

/-- `∑_{n even, n ≥ 2} wⁿ = w²/(1 - w²)`. -/
private theorem hasSum_even_geom {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => if n % 2 = 0 ∧ n ≠ 0 then w ^ n else 0) (w ^ 2 / (1 - w ^ 2)) := by
  have hw2 : ‖w ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg w]
  have hg := hasSum_geometric_of_norm_lt_one hw2
  have h : HasSum (fun k : ℕ => (w ^ 2) ^ k - if k = 0 then 1 else 0) ((1 - w ^ 2)⁻¹ - 1) :=
    hg.sub (hasSum_ite_eq 0 1)
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · convert h using 1
    · funext k
      simp only [Function.comp_apply]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have h2k : (2 * k) % 2 = 0 ∧ 2 * k ≠ 0 := ⟨by omega, by omega⟩
        rw [ite_eq_left h2k, ← pow_mul, ite_eq_right hk.ne', sub_zero]
    · have : (1 - w ^ 2) ≠ 0 := by
        intro h0
        have : w ^ 2 = 1 := by linear_combination -h0
        have := congrArg norm this
        rw [norm_one] at this
        linarith
      field_simp
      ring
  · intro x hx
    have : ¬ (x % 2 = 0 ∧ x ≠ 0) := by
      rintro ⟨h0, -⟩
      exact hx ⟨x / 2, by simp only; omega⟩
    rw [ite_eq_right this]

/-! ## Coefficient identities -/

private theorem sqrt_cast_sq (n : ℕ) : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := by
  rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl

private theorem sqrt_cast_ne (n : ℕ) (hn : n ≠ 0) : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
  rw [Ne, ofReal_eq_zero, Real.sqrt_eq_zero (Nat.cast_nonneg _)]
  exact_mod_cast hn

private theorem norm_sqrt_cast (n : ℕ) : ‖((Real.sqrt n : ℝ) : ℂ)‖ = Real.sqrt n :=
  Complex.norm_of_nonneg (Real.sqrt_nonneg _)

private theorem norm_sq_pow_div_sqrt (z : ℂ) (n : ℕ) :
    ‖z ^ n / (Real.sqrt n : ℂ)‖ ^ 2 = (‖z‖ ^ 2) ^ n / n := by
  rw [norm_div, norm_pow, norm_sqrt_cast, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

private theorem norm_sq_sqrt_mul_pow (z : ℂ) (n : ℕ) :
    ‖(Real.sqrt n : ℂ) * z ^ n‖ ^ 2 = n * (‖z‖ ^ 2) ^ n := by
  rw [norm_mul, norm_pow, norm_sqrt_cast, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

private theorem sq_pow_div_sqrt (z : ℂ) (n : ℕ) : (z ^ n / (Real.sqrt n : ℂ)) ^ 2 = (z ^ 2) ^ n / n := by
  rw [div_pow, sqrt_cast_sq]; ring

private theorem sq_sqrt_mul_pow (z : ℂ) (n : ℕ) : ((Real.sqrt n : ℂ) * z ^ n) ^ 2 = n * (z ^ 2) ^ n := by
  rw [mul_pow, sqrt_cast_sq]; ring

private theorem mul_conj_eq_norm_sq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A real series from a complex one with real terms. -/
private theorem hasSum_real_of_complex {g : ℕ → ℝ} {F : ℕ → ℂ} {a : ℝ} (hF : ∀ n, ((g n : ℝ) : ℂ) = F n)
    (h : HasSum F (a : ℂ)) : HasSum g a := by
  refine Complex.hasSum_ofReal.mp ?_
  simp only [hF]
  exact h

/-- `∑ xⁿ/n = -log(1 - x)` for real `0 ≤ x < 1`. -/
private theorem real_hasSum_pow_div {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n : ℕ => x ^ n / n) (-Real.log (1 - x)) := by
  have h := hasSum_taylorSeries_neg_log (z := (x : ℂ)) (by rw [Complex.norm_of_nonneg hx0]; exact hx)
  refine hasSum_real_of_complex (fun n => by push_cast; rfl) ?_
  rw [ofReal_neg, Complex.ofReal_log (by linarith)]
  push_cast
  exact h

/-- Real and imaginary parts of a termwise product, from the sums of `x ȳ` and `x y`. -/
private theorem hasSum_parts {x y : ℕ → ℂ} {P R : ℂ} (hP : HasSum (fun n => x n * conj (y n)) P)
    (hR : HasSum (fun n => x n * y n) R) :
    HasSum (fun n => (x n).re * (y n).re) ((P.re + R.re) / 2) ∧
      HasSum (fun n => (x n).im * (y n).im) ((P.re - R.re) / 2) ∧
      HasSum (fun n => (x n).re * (y n).im) ((R.im - P.im) / 2) ∧
      HasSum (fun n => (x n).im * (y n).re) ((R.im + P.im) / 2) := by
  have hPr := Complex.hasSum_re hP
  have hPi := Complex.hasSum_im hP
  have hRr := Complex.hasSum_re hR
  have hRi := Complex.hasSum_im hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert (hPr.add hRr).div_const 2 using 1
    funext n; simp only [mul_re, conj_re, conj_im]; ring
  · convert (hPr.sub hRr).div_const 2 using 1
    funext n; simp only [mul_re, conj_re, conj_im]; ring
  · convert (hRi.sub hPi).div_const 2 using 1
    funext n; simp only [mul_im, conj_re, conj_im]; ring
  · convert (hRi.add hPi).div_const 2 using 1
    funext n; simp only [mul_im, conj_re, conj_im]; ring

/-! ## The constants -/

private theorem Ao_eq : (Ao : ℂ) = cartanh (1 / 2) := by
  rw [Ao, Real.artanh_eq_half_log (by norm_num), cartanh]
  push_cast
  rw [Complex.ofReal_log (by norm_num)]
  norm_num

private theorem Ae_eq : (Ae : ℂ) = -(1 / 2 : ℂ) * log (1 - (1 / 2 : ℂ) ^ 2) := by
  rw [Ae]
  push_cast
  rw [Complex.ofReal_log (by norm_num)]
  norm_num

private theorem norm_sθ_sq (θ : ℝ) : ‖sθ θ‖ ^ 2 = 1 / 2 := by
  rw [sθ, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

private theorem sθ_sq (θ : ℝ) : sθ θ ^ 2 = zθ θ := by
  rw [sθ, zθ, mul_pow, ← Complex.exp_nat_mul]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  push_cast
  rw [inv_pow, h2]
  congr 1
  · norm_num
  · congr 1; ring

private theorem sθ_mul_conj (θ : ℝ) : sθ θ * conj (sθ θ) = 1 / 2 := by
  rw [mul_conj_eq_norm_sq, norm_sθ_sq]; norm_num

/-! ## Rows: eq:gram, conjugation, the Gram coordinates -/

theorem eq_gram_proved (s : ℂ) (hs : ‖s‖ ^ 2 = 1 / 2) :
    HasSum (fun n => ‖aOdd s n‖ ^ 2) Ao ∧ HasSum (fun n => aOdd s n ^ 2) (cartanh (s ^ 2)) ∧
      HasSum (fun n => ‖aEven s n‖ ^ 2) Ae ∧
      HasSum (fun n => aEven s n ^ 2) (-(1 / 2 : ℂ) * log (1 - (s ^ 2) ^ 2)) := by
  have hs2 : ‖s ^ 2‖ < 1 := by rw [norm_pow, hs]; norm_num
  have hhalf : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hasSum_real_of_complex (F := fun n : ℕ => if n % 2 = 1 then (1 / 2 : ℂ) ^ n / n else 0)
      (fun n => ?_) ?_
    · simp only [aOdd]
      split_ifs
      · rw [norm_sq_pow_div_sqrt, hs]; push_cast; rfl
      · simp
    · rw [Ao_eq]; exact hasSum_odd_artanh hhalf
  · convert hasSum_odd_artanh hs2 using 1
    funext n
    simp only [aOdd]
    split_ifs
    · rw [sq_pow_div_sqrt]
    · simp
  · refine hasSum_real_of_complex
      (F := fun n : ℕ => if n % 2 = 0 ∧ n ≠ 0 then (1 / 2 : ℂ) ^ n / n else 0) (fun n => ?_) ?_
    · simp only [aEven]
      split_ifs
      · rw [norm_sq_pow_div_sqrt, hs]; push_cast; rfl
      · simp
    · rw [Ae_eq]; exact hasSum_even_log hhalf
  · convert hasSum_even_log hs2 using 1
    funext n
    simp only [aEven]
    split_ifs
    · rw [sq_pow_div_sqrt]
    · simp

theorem sec5_a_conj_proved (s : ℂ) (n : ℕ) :
    aOdd (conj s) n = conj (aOdd s n) ∧ aEven (conj s) n = conj (aEven s n) ∧ bEven (conj s) n = conj (bEven s n) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [aOdd, aEven, bEven] <;> split_ifs <;> simp [map_div₀, map_pow, conj_ofReal]

theorem sec5_uv_gram_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    HasSum (fun n => uvec θ n ^ 2) ((Ao + (Zo θ).re) / 2) ∧ HasSum (fun n => vvec θ n ^ 2) ((Ao - (Zo θ).re) / 2) ∧
      HasSum (fun n => uvec θ n * vvec θ n) ((Zo θ).im / 2) := by
  obtain ⟨hA, hZ, -, -⟩ := eq_gram_proved (sθ θ) (norm_sθ_sq θ)
  rw [sθ_sq] at hZ
  have hP : HasSum (fun n => aOdd (sθ θ) n * conj (aOdd (sθ θ) n)) (Ao : ℂ) := by
    simp only [mul_conj_eq_norm_sq]
    exact Complex.hasSum_ofReal.mpr hA
  have hR : HasSum (fun n => aOdd (sθ θ) n * aOdd (sθ θ) n) (Zo θ) := by
    simpa only [sq, Zo] using hZ
  obtain ⟨h1, h2, h3, -⟩ := hasSum_parts hP hR
  have e1 : (fun n => uvec θ n ^ 2) = fun n => (aOdd (sθ θ) n).re * (aOdd (sθ θ) n).re := by
    funext n; simp only [uvec, sq]
  have e2 : (fun n => vvec θ n ^ 2) = fun n => (aOdd (sθ θ) n).im * (aOdd (sθ θ) n).im := by
    funext n; simp only [vvec, sq]
  have e3 : (fun n => uvec θ n * vvec θ n) = fun n => (aOdd (sθ θ) n).re * (aOdd (sθ θ) n).im := by
    funext n; simp only [uvec, vvec]
  rw [e1, e2, e3]
  simp only [ofReal_re, ofReal_im, sub_zero] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem sec6_UV_values_proved (z : ℂ) (hz : ‖z‖ = 1 / 2) :
    HasSum (fun n => ‖betaV z n‖ ^ 2) U0 ∧ HasSum (fun n => ‖alphaV z n‖ ^ 2) V0 ∧
      HasSum (fun n => betaV z n ^ 2) (z ^ 2 / (1 - z ^ 2) ^ 2) ∧ HasSum (fun n => alphaV z n ^ 2) (-log (1 - z ^ 2)) ∧
      ∀ n, alphaV (conj z) n = conj (alphaV z n) ∧ betaV (conj z) n = conj (betaV z n) := by
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow, hz]; norm_num
  have hzsq : ‖z‖ ^ 2 = 1 / 4 := by rw [hz]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 4) (by norm_num)
    convert h using 1
    · funext n
      simp only [betaV]
      split_ifs with hn
      · simp [hn]
      · rw [norm_sq_sqrt_mul_pow, hzsq]
    · rw [U0]; norm_num
  · have h := real_hasSum_pow_div (x := 1 / 4) (by norm_num) (by norm_num)
    convert h using 1
    · funext n
      simp only [alphaV]
      split_ifs with hn
      · simp [hn]
      · rw [norm_sq_pow_div_sqrt, hzsq]
    · rw [V0, show (4 / 3 : ℝ) = (1 - 1 / 4)⁻¹ by norm_num, Real.log_inv]
  · convert hasSum_coe_mul_geometric_of_norm_lt_one hz2 using 1
    funext n
    simp only [betaV]
    split_ifs with hn
    · simp [hn]
    · rw [sq_sqrt_mul_pow]
  · convert hasSum_taylorSeries_neg_log hz2 using 1
    funext n
    simp only [alphaV]
    split_ifs with hn
    · simp [hn]
    · rw [sq_pow_div_sqrt]
  · intro n
    constructor <;> simp only [alphaV, betaV] <;> split_ifs <;> simp [map_div₀, map_pow, conj_ofReal]

theorem sec7_be_deriv_proved (s : ℂ) (n : ℕ) : bEven s n = s * deriv (fun x => aEven x n) s := by
  by_cases hc : n % 2 = 0 ∧ n ≠ 0
  · have hfun : (fun x => aEven x n) = fun x => x ^ n / (Real.sqrt n : ℂ) := by
      funext x; simp only [aEven, ite_eq_left hc]
    rw [hfun, ((hasDerivAt_pow n s).div_const _).deriv, bEven, ite_eq_left hc]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hne := sqrt_cast_ne (k + 1) hc.2
    have hsq := sqrt_cast_sq (k + 1)
    simp only [Nat.add_sub_cancel]
    rw [← hsq]
    field_simp
    ring
  · have hfun : (fun x => aEven x n) = fun _ => (0 : ℂ) := by
      funext x; simp only [aEven, ite_eq_right hc]
    rw [hfun, deriv_const, bEven, ite_eq_right hc, mul_zero]

/-- The complex sums behind `G(θ)`, at `s = s_θ`. -/
private theorem gram_complex_sums (θ : ℝ) :
    HasSum (fun n => aEven (sθ θ) n * conj (aEven (sθ θ) n)) (Ae : ℂ) ∧
      HasSum (fun n => aEven (sθ θ) n * aEven (sθ θ) n) (Ze θ) ∧
      HasSum (fun n => bEven (sθ θ) n * conj (bEven (sθ θ) n)) (Me : ℂ) ∧
      HasSum (fun n => bEven (sθ θ) n * bEven (sθ θ) n) (Mz θ) ∧
      HasSum (fun n => aEven (sθ θ) n * conj (bEven (sθ θ) n)) (Le : ℂ) ∧
      HasSum (fun n => aEven (sθ θ) n * bEven (sθ θ) n) (Lz θ) ∧
      HasSum (fun n => bEven (sθ θ) n * conj (aEven (sθ θ) n)) (Le : ℂ) ∧
      HasSum (fun n => bEven (sθ θ) n * aEven (sθ θ) n) (Lz θ) := by
  obtain ⟨-, -, hA, hZ⟩ := eq_gram_proved (sθ θ) (norm_sθ_sq θ)
  have hsc := sθ_mul_conj θ
  have hz := sθ_sq θ
  have hz1 : ‖zθ θ‖ < 1 := by
    rw [← hz, norm_pow, norm_sθ_sq]; norm_num
  have hhalf : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hMe : (Me : ℂ) = 2 * (1 / 2 : ℂ) ^ 2 / (1 - (1 / 2 : ℂ) ^ 2) ^ 2 := by rw [Me]; norm_num
  have hLe : (Le : ℂ) = (1 / 2 : ℂ) ^ 2 / (1 - (1 / 2 : ℂ) ^ 2) := by rw [Le]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mul_conj_eq_norm_sq]
    exact Complex.hasSum_ofReal.mpr hA
  · rw [hz] at hZ
    simpa only [sq, Ze] using hZ
  · rw [hMe]
    convert hasSum_even_mul_geom hhalf using 1
    funext n
    simp only [bEven]
    split_ifs with hc
    · rw [map_mul, map_pow, conj_ofReal, ← hsc]
      calc (Real.sqrt n : ℂ) * sθ θ ^ n * ((Real.sqrt n : ℂ) * conj (sθ θ) ^ n)
          = (Real.sqrt n : ℂ) ^ 2 * (sθ θ * conj (sθ θ)) ^ n := by ring
        _ = _ := by rw [sqrt_cast_sq]
    · simp
  · rw [Mz, ← hz]
    convert hasSum_even_mul_geom (w := sθ θ ^ 2) (by rw [hz]; exact hz1) using 1
    · funext n
      simp only [bEven]
      split_ifs with hc
      · rw [← sq, sq_sqrt_mul_pow]
      · simp
  · rw [hLe]
    convert hasSum_even_geom hhalf using 1
    funext n
    simp only [aEven, bEven]
    split_ifs with hc
    · have hne := sqrt_cast_ne n hc.2
      rw [map_mul, map_pow, conj_ofReal, ← hsc, mul_pow]
      field_simp
    · simp
  · rw [Lz, ← hz]
    convert hasSum_even_geom (w := sθ θ ^ 2) (by rw [hz]; exact hz1) using 1
    funext n
    simp only [aEven, bEven]
    split_ifs with hc
    · have hne := sqrt_cast_ne n hc.2
      rw [← pow_mul, mul_comm 2 n, pow_mul]
      field_simp
    · simp
  · rw [hLe]
    convert hasSum_even_geom hhalf using 1
    funext n
    simp only [aEven, bEven]
    split_ifs with hc
    · have hne := sqrt_cast_ne n hc.2
      rw [map_div₀, map_pow, conj_ofReal, ← hsc, mul_pow]
      field_simp
    · simp
  · rw [Lz, ← hz]
    convert hasSum_even_geom (w := sθ θ ^ 2) (by rw [hz]; exact hz1) using 1
    funext n
    simp only [aEven, bEven]
    split_ifs with hc
    · have hne := sqrt_cast_ne n hc.2
      rw [← pow_mul, mul_comm 2 n, pow_mul]
      field_simp
    · simp

theorem sec7_gram_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    ∀ i j : Fin 4, HasSum (fun n => wEven θ i n * wEven θ j n) (Gram θ i j) := by
  obtain ⟨haac, haa, hbbc, hbb, habc, hab, hbac, hba⟩ := gram_complex_sums θ
  have Paa := hasSum_parts haac haa
  have Pbb := hasSum_parts hbbc hbb
  have Pab := hasSum_parts habc hab
  have Pba := hasSum_parts hbac hba
  intro i j
  fin_cases i <;> fin_cases j
  · convert Paa.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Paa.2.2.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pab.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pab.2.2.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Paa.2.2.2 using 1 <;> simp [wEven, Gram]
    ring
  · convert Paa.2.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pab.2.2.2 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pab.2.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pba.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pba.2.2.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pbb.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pbb.2.2.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pba.2.2.2 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pba.2.1 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pbb.2.2.2 using 1 <;> simp [wEven, Gram]
    ring
  · convert Pbb.2.1 using 1 <;> simp [wEven, Gram]
    ring


/-! ## The odd square root -/

private theorem sq_mem_ball {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) : s ^ 2 ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hs ⊢
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hs two_ne_zero

private theorem neg_mem_ball {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) : -s ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_neg]
  exact mem_ball_zero_iff.mp hs

/-- For `f ∈ 𝒮`, the quotient `u = dslope f 0` (`u(z) = f(z)/z`, `u(0) = f'(0) = 1`) is holomorphic and zero-free
on the disc, and `z u(z) = f(z)`. -/
private theorem inS_dslope_props {f : ℂ → ℂ} (hf : InS f) :
    DifferentiableOn ℂ (dslope f 0) (ball 0 1) ∧ dslope f 0 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, dslope f 0 z ≠ 0) ∧ ∀ z, z * dslope f 0 z = f z := by
  refine ⟨(Complex.differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hf.differentiableOn, ?_, ?_, ?_⟩
  · rw [dslope_same, hf.deriv_zero]
  · intro z hz h0
    by_cases hz0 : z = 0
    · subst hz0
      rw [dslope_same, hf.deriv_zero] at h0
      exact one_ne_zero h0
    · have h1 := sub_smul_dslope f 0 z
      rw [h0, smul_zero, hf.map_zero, sub_zero] at h1
      exact hz0 (hf.injOn hz (mem_ball_self one_pos) (by rw [← h1, hf.map_zero]))
  · intro z
    have h1 := sub_smul_dslope f 0 z
    rwa [sub_zero, hf.map_zero, sub_zero, smul_eq_mul] at h1

/-- A zero-free holomorphic function on the unit disc with value `1` at `0` is `exp ∘ L` for a holomorphic `L` with
`L(0) = 0` (`L` a primitive of `u'/u`). -/
private theorem exists_log_ball {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u (ball 0 1)) (hu0 : u 0 = 1)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, u z ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ DifferentiableOn ℂ L (ball 0 1) ∧ ∀ z ∈ ball (0 : ℂ) 1, exp (L z) = u z := by
  have hopen : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have hg : DifferentiableOn ℂ (fun z => deriv u z / u z) (ball 0 1) := (hu.deriv hopen).div hu hne
  obtain ⟨L, hL0, hL⟩ := hg.isExactOn_ball.with_val_at 0 0
  have hLd : DifferentiableOn ℂ L (ball 0 1) := fun z hz => (hL z hz).differentiableAt.differentiableWithinAt
  have hφd : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt (fun w => u w * exp (-L w)) 0 z := by
    intro z hz
    have hu' : HasDerivAt u (deriv u z) z := (hu.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hE : HasDerivAt (fun w => exp (-L w)) (exp (-L z) * -(deriv u z / u z)) z := (hL z hz).neg.cexp
    convert hu'.mul hE using 1
    have hu0' := hne z hz
    calc (0 : ℂ) = deriv u z * exp (-L z) - exp (-L z) * deriv u z * (u z / u z) := by
          rw [div_self hu0', mul_one]; ring
      _ = _ := by ring
  have hconst := fun z (hz : z ∈ ball (0 : ℂ) 1) =>
    hopen.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun w hw => (hφd w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hφd w hw).deriv) hz
      (mem_ball_self one_pos)
  refine ⟨L, hL0, hLd, fun z hz => ?_⟩
  have h1 := hconst z hz
  simp only [hu0, hL0, neg_zero, exp_zero, mul_one, exp_neg] at h1
  exact ((mul_inv_eq_one₀ (exp_ne_zero _)).mp h1).symm

theorem sec3_oddroot_exists_proved (f : ℂ → ℂ) (hf : InS f) : ∃ h : ℂ → ℂ, IsOddRoot f h := by
  obtain ⟨hud, hu0, hune, hmul⟩ := inS_dslope_props hf
  obtain ⟨L, hL0, hLd, hexp⟩ := exists_log_ball hud hu0 hune
  have hE : DifferentiableOn ℂ (fun s => exp (L (s ^ 2) / 2)) (ball 0 1) :=
    ((hLd.comp (differentiableOn_pow 2) (fun s hs => sq_mem_ball hs)).div_const 2).cexp
  refine ⟨fun s => s * exp (L (s ^ 2) / 2), differentiableOn_id.mul hE, ?_, ?_, ?_⟩
  · intro s _
    simp only [neg_sq, neg_mul]
  · intro s hs
    have h2 : exp (L (s ^ 2) / 2) ^ 2 = exp (L (s ^ 2)) := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    simp only
    rw [mul_pow, h2, hexp _ (sq_mem_ball hs), hmul]
  · have hd0 : DifferentiableAt ℂ (fun s => exp (L (s ^ 2) / 2)) 0 :=
      hE.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    rw [((hasDerivAt_id' (0 : ℂ)).fun_mul hd0.hasDerivAt).deriv]
    simp [hL0]

theorem sec3_oddroot_mem_S_proved (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) : InS h := by
  obtain ⟨hd, hodd, hsq, hder⟩ := hh
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hzero : h 0 = 0 := by
    have h1 := hodd 0 h0mem
    rw [neg_zero] at h1
    linear_combination h1 / 2
  refine ⟨hd, ?_, hzero, hder⟩
  intro s hs t ht hst
  have hf2 : f (s ^ 2) = f (t ^ 2) := by rw [← hsq s hs, ← hsq t ht, hst]
  have h2 : s ^ 2 = t ^ 2 := hf.injOn (sq_mem_ball hs) (sq_mem_ball ht) hf2
  have hfac : (s - t) * (s + t) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hfac with h1 | h1
  · linear_combination h1
  · have ht' : t = -s := by linear_combination h1
    subst ht'
    have hs0 : h s = 0 := by
      have h3 := hodd s hs
      linear_combination (hst + h3) / 2
    have h4 : f (s ^ 2) = f 0 := by rw [← hsq s hs, hs0, hf.map_zero, zero_pow two_ne_zero]
    have hs2 : s ^ 2 = 0 := hf.injOn (sq_mem_ball hs) h0mem h4
    have hs00 : s = 0 := (pow_eq_zero_iff two_ne_zero).mp hs2
    rw [hs00, neg_zero]

/-! ## Uniqueness of power series coefficients -/

/-- `exp w = 1` and `‖w‖ < 1` force `w = 0` (`w ∈ 2πiℤ`). -/
private theorem eq_zero_of_exp_eq_one {w : ℂ} (h : exp w = 1) (hw : ‖w‖ < 1) : w = 0 := by
  obtain ⟨n, rfl⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnorm : ‖(n : ℂ) * (2 * Real.pi * I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
    rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hpi.le, Complex.norm_ofNat, mul_one]
  rw [hnorm] at hw
  have h1 : |(n : ℝ)| < 1 := by nlinarith [abs_nonneg (n : ℝ), Real.pi_gt_three]
  have h2 : |n| < 1 := by exact_mod_cast h1
  have h3 : n = 0 := by
    have := abs_lt.mp h2
    omega
  simp [h3]

/-- One-variable uniqueness: if `∑ ‖aₙ‖ ρⁿ < ∞` (`ρ > 0`) and `∑ aₙ zⁿ = 0` for `‖z‖ < δ` (`δ > 0`), then `a = 0`. -/
private theorem coeff_eq_zero_of_tsum {a : ℕ → ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hsum : Summable (fun n => ‖a n‖ * ρ ^ n)) (hz : ∀ z : ℂ, ‖z‖ < δ → ∑' n, a n * z ^ n = 0) (n : ℕ) :
    a n = 0 := by
  obtain ⟨p, hp⟩ : ∃ p, p = FormalMultilinearSeries.ofScalars ℂ a := ⟨_, rfl⟩
  have hrad : ((ρ.toNNReal : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm (hsum.congr (fun k => ?_))
    rw [Real.coe_toNNReal _ hρ.le, hp, FormalMultilinearSeries.ofScalars_norm]
  have hpos : 0 < p.radius := lt_of_lt_of_le (ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hρ)) hrad
  have hsumeq : ∀ z, p.sum z = ∑' k, a k * z ^ k := by
    intro z
    subst hp
    simp only [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hev : p.sum =ᶠ[𝓝 0] 0 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with z hzb
    rw [hsumeq, Pi.zero_apply]
    exact hz z (mem_ball_zero_iff.mp hzb)
  have hp0 : p = 0 := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt.eq_zero_of_eventually hev
  rw [hp] at hp0
  exact congrFun ((FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).mp hp0) n

/-- The terms of the double series at `(s, t)` are dominated by those at `(ρ, ρ)`. -/
private theorem norm_term_le (c : ℂ) {ρ : ℝ} {s t : ℂ} (hs : ‖s‖ ≤ ρ) (ht : ‖t‖ ≤ ρ) (n m : ℕ) :
    ‖c * s ^ n * t ^ m‖ ≤ ‖c‖ * ρ ^ n * ρ ^ m := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hs
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 : ‖s‖ ^ n ≤ ρ ^ n := pow_le_pow_left₀ (norm_nonneg _) hs n
  have h2 : ‖t‖ ^ m ≤ ρ ^ m := pow_le_pow_left₀ (norm_nonneg _) ht m
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (by positivity)
    (mul_nonneg (norm_nonneg _) (pow_nonneg hρ n))

private theorem norm_term_real (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n m : ℕ) :
    ‖c * (ρ : ℂ) ^ n * (ρ : ℂ) ^ m‖ = ‖c‖ * ρ ^ n * ρ ^ m := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_of_nonneg hρ]

/-- Two-variable uniqueness: if `∑ ‖c_{nm}‖ ρⁿ ρᵐ < ∞` and `∑ c_{nm} sⁿ tᵐ = 0` for `‖s‖, ‖t‖ < δ ≤ ρ`, then `c = 0`
(first the inner series in `t`, then the coefficients). -/
private theorem coeff2_eq_zero {c : ℕ → ℕ → ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hS : Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2‖ * ρ ^ nm.1 * ρ ^ nm.2))
    (hz : ∀ s t : ℂ, ‖s‖ < δ → ‖t‖ < δ → kser c s t = 0) (n m : ℕ) : c n m = 0 := by
  have hinner : ∀ t : ℂ, ‖t‖ < δ → ∀ k, ∑' j, c k j * t ^ j = 0 := by
    intro t ht
    have htρ : ‖t‖ ≤ ρ := ht.le.trans hδρ
    refine coeff_eq_zero_of_tsum (a := fun k => ∑' j, c k j * t ^ j) hρ hδ ?_ ?_
    · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_) hS.prod
      show ‖∑' j, c k j * t ^ j‖ * ρ ^ k ≤ ∑' j, ‖c k j‖ * ρ ^ k * ρ ^ j
      have hfac : Summable (fun j => ‖c k j‖ * ρ ^ k * ρ ^ j) := hS.prod_factor k
      have hρk : ρ ^ k ≠ 0 := by positivity
      have hnorm : Summable (fun j => ‖c k j * t ^ j‖) := by
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) (hfac.mul_left (ρ ^ k)⁻¹)
        have e : (ρ ^ k)⁻¹ * (‖c k j‖ * ρ ^ k * ρ ^ j) = ‖c k j‖ * ρ ^ j := by
          field_simp
        rw [e, norm_mul, norm_pow]
        gcongr
      calc ‖∑' j, c k j * t ^ j‖ * ρ ^ k ≤ (∑' j, ‖c k j * t ^ j‖) * ρ ^ k := by
            gcongr
            exact norm_tsum_le_tsum_norm hnorm
        _ = ∑' j, ‖c k j * t ^ j‖ * ρ ^ k := tsum_mul_right.symm
        _ ≤ ∑' j, ‖c k j‖ * ρ ^ k * ρ ^ j := by
            refine Summable.tsum_le_tsum (fun j => ?_) (hnorm.mul_right _) hfac
            rw [norm_mul, norm_pow]
            calc ‖c k j‖ * ‖t‖ ^ j * ρ ^ k ≤ ‖c k j‖ * ρ ^ j * ρ ^ k := by gcongr
              _ = ‖c k j‖ * ρ ^ k * ρ ^ j := by ring
    · intro s hs
      have hsρ : ‖s‖ ≤ ρ := hs.le.trans hδρ
      have hsum2 : Summable (fun nm : ℕ × ℕ => c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2) :=
        Summable.of_norm_bounded hS (fun nm => norm_term_le _ hsρ htρ nm.1 nm.2)
      calc ∑' k, (∑' j, c k j * t ^ j) * s ^ k = ∑' k, ∑' j, c k j * s ^ k * t ^ j := by
            refine tsum_congr (fun k => ?_)
            rw [← tsum_mul_right]
            exact tsum_congr (fun j => by ring)
        _ = kser c s t := hsum2.tsum_prod.symm
        _ = 0 := hz s t hs ht
  refine coeff_eq_zero_of_tsum (a := fun j => c n j) hρ hδ ?_ (fun t ht => hinner t ht n) m
  have hfac : Summable (fun j => ‖c n j‖ * ρ ^ n * ρ ^ j) := hS.prod_factor n
  have hρn : ρ ^ n ≠ 0 := by positivity
  refine (hfac.mul_left (ρ ^ n)⁻¹).congr (fun j => ?_)
  field_simp

/-- Near the origin the double series is small, when `c_{0m} = 0`: for `‖s‖, ‖t‖ < δ`, `‖∑ c_{nm} sⁿ tᵐ‖ < 1`. -/
private theorem kser_small {c : ℕ → ℕ → ℂ} (hc0 : ∀ m, c 0 m = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2‖ * ρ ^ nm.1 * ρ ^ nm.2)) :
    ∃ δ, 0 < δ ∧ δ ≤ ρ ∧ ∀ s t : ℂ, ‖s‖ < δ → ‖t‖ < δ → ‖kser c s t‖ < 1 := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑' nm : ℕ × ℕ, ‖c nm.1 nm.2‖ * ρ ^ nm.1 * ρ ^ nm.2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg (fun _ => by positivity)
  have hδρ : ρ / (S + 1) ≤ ρ := div_le_self hρ.le (by linarith)
  refine ⟨ρ / (S + 1), by positivity, hδρ, fun s t hs ht => ?_⟩
  have hsρ : ‖s‖ ≤ ρ := hs.le.trans hδρ
  have htρ : ‖t‖ ≤ ρ := ht.le.trans hδρ
  obtain ⟨x, hx⟩ : ∃ x, x = ‖s‖ / ρ := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by rw [hx]; exact (div_le_one hρ).mpr hsρ
  have hsx : ‖s‖ = x * ρ := by rw [hx]; field_simp
  have hterm : ∀ nm : ℕ × ℕ,
      ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖ ≤ x * (‖c nm.1 nm.2‖ * ρ ^ nm.1 * ρ ^ nm.2) := by
    rintro ⟨n, m⟩
    dsimp only
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0 m]
    · rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖s‖ ^ n ≤ x * ρ ^ n := by
        rw [hsx, mul_pow]
        gcongr
        exact pow_le_of_le_one hx0 hx1 hn.ne'
      have h2 : ‖t‖ ^ m ≤ ρ ^ m := pow_le_pow_left₀ (norm_nonneg _) htρ m
      calc ‖c n m‖ * ‖s‖ ^ n * ‖t‖ ^ m ≤ ‖c n m‖ * (x * ρ ^ n) * ρ ^ m := by gcongr
        _ = x * (‖c n m‖ * ρ ^ n * ρ ^ m) := by ring
  have hsum : Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hS.mul_left x)
  have hle : ‖kser c s t‖ ≤ x * S := by
    rw [hSdef, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_le_tsum hterm hsum (hS.mul_left x))
  have hs' : ‖s‖ * (S + 1) < ρ := (lt_div_iff₀ (by linarith)).mp hs
  have hxS : x * (S + 1) < 1 := by
    rw [hx, div_mul_eq_mul_div, div_lt_one hρ]
    exact hs'
  calc ‖kser c s t‖ ≤ x * S := hle
    _ ≤ x * (S + 1) := mul_le_mul_of_nonneg_left (by linarith) hx0
    _ < 1 := hxS

/-- If `c_{0m} = 0`, `∑ ‖c_{nm}‖ 2^{-n-m} < ∞` and `exp(∑ c_{nm} sⁿ tᵐ) = 1` on the bidisc, then `c = 0`. -/
private theorem coeff_zero_of_exp_kser_eq_one {c : ℕ → ℕ → ℂ} (hc0 : ∀ m, c 0 m = 0)
    (hS : Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2‖ * (1 / 2 : ℝ) ^ nm.1 * (1 / 2 : ℝ) ^ nm.2))
    (hexp : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → exp (kser c s t) = 1) (n m : ℕ) :
    c n m = 0 := by
  have hρ : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨δ, hδ, hδρ, hsmall⟩ := kser_small hc0 hρ hS
  refine coeff2_eq_zero hρ hδ hδρ hS (fun s t hs ht => ?_) n m
  have hs1 : s ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by linarith)
  have ht1 : t ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by linarith)
  exact eq_zero_of_exp_eq_one (hexp s t hs1 ht1) (hsmall s t hs ht)

private theorem half_mem_ball : (((1 / 2 : ℝ)) : ℂ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_of_nonneg (by norm_num)]
  norm_num

/-- The Grunsky series of `g` converges absolutely at `(½, ½)`. -/
private theorem grunsky_summable_half {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) :
    Summable (fun nm : ℕ × ℕ => ‖γ nm.1 nm.2‖ * (1 / 2 : ℝ) ^ nm.1 * (1 / 2 : ℝ) ^ nm.2) :=
  ((hγ.2 _ _ half_mem_ball half_mem_ball).1).congr (fun nm => norm_term_real _ (by norm_num) _ _)

/-! ## Parity of the Grunsky coefficients of the odd root -/

/-- The coefficients of `K(-s, -t) - K(s, t)`. -/
private noncomputable def parityDiff (γ : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ := ((-1) ^ (n + m) - 1) * γ n m

private theorem kser_parityDiff {γ : ℕ → ℕ → ℂ} {s t : ℂ}
    (h1 : Summable (fun nm : ℕ × ℕ => ‖γ nm.1 nm.2 * (-s) ^ nm.1 * (-t) ^ nm.2‖))
    (h2 : Summable (fun nm : ℕ × ℕ => ‖γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖)) :
    kser (parityDiff γ) s t = kser γ (-s) (-t) - kser γ s t := by
  unfold kser
  rw [← h1.of_norm.tsum_sub h2.of_norm]
  refine tsum_congr (fun nm => ?_)
  rw [parityDiff, neg_pow s, neg_pow t, pow_add]
  ring

/-- For `h` odd on the disc, the kernel quotient is even in `(s, t)` jointly. -/
private theorem kernelQuot_neg {h : ℂ → ℂ} (hodd : ∀ s ∈ ball (0 : ℂ) 1, h (-s) = -h s) {s t : ℂ}
    (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) : kernelQuot h (-s) (-t) = kernelQuot h s t := by
  have hderiv : deriv h (-s) = deriv h s := by
    have hev : (fun x => h (-x)) =ᶠ[𝓝 s] (fun x => -h x) := by
      filter_upwards [isOpen_ball.mem_nhds hs] with x hx using hodd x hx
    have h1 := hev.deriv_eq
    rw [deriv_comp_neg, deriv.fun_neg] at h1
    exact neg_inj.mp h1
  have q1 : (-h s - -h t) / (-s - -t) = (h s - h t) / (s - t) := by
    rw [show -h s - -h t = -(h s - h t) by ring, show -s - -t = -(s - t) by ring, neg_div_neg_eq]
  unfold kernelQuot
  rw [hodd s hs, hodd t ht, hderiv]
  simp only [neg_inj, neg_eq_zero, q1, neg_div_neg_eq]

theorem sec3_oddroot_parity_proved (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff h γ) :
    (∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → kser γ (-s) (-t) = kser γ s t) ∧
      ∀ n m : ℕ, (n + m) % 2 = 1 → γ n m = 0 := by
  have hodd := hh.2.1
  have hSγ := grunsky_summable_half hγ
  have hS : Summable (fun nm : ℕ × ℕ =>
      ‖parityDiff γ nm.1 nm.2‖ * (1 / 2 : ℝ) ^ nm.1 * (1 / 2 : ℝ) ^ nm.2) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun nm => ?_) (hSγ.mul_left 2)
    have h2 : ‖((-1 : ℂ) ^ (nm.1 + nm.2) - 1)‖ ≤ 2 := by
      calc _ ≤ ‖(-1 : ℂ) ^ (nm.1 + nm.2)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, norm_neg, norm_one, one_pow]; norm_num
    rw [parityDiff, norm_mul]
    calc ‖(-1 : ℂ) ^ (nm.1 + nm.2) - 1‖ * ‖γ nm.1 nm.2‖ * (1 / 2 : ℝ) ^ nm.1 * (1 / 2 : ℝ) ^ nm.2
        ≤ 2 * ‖γ nm.1 nm.2‖ * (1 / 2 : ℝ) ^ nm.1 * (1 / 2 : ℝ) ^ nm.2 := by gcongr
      _ = 2 * (‖γ nm.1 nm.2‖ * (1 / 2 : ℝ) ^ nm.1 * (1 / 2 : ℝ) ^ nm.2) := by ring
  have hc0 : ∀ m, parityDiff γ 0 m = 0 := fun m => by rw [parityDiff, hγ.1 0 m (Or.inl rfl), mul_zero]
  have hexp : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → exp (kser (parityDiff γ) s t) = 1 := by
    intro s t hs ht
    have hst := hγ.2 s t hs ht
    have hst' := hγ.2 (-s) (-t) (neg_mem_ball hs) (neg_mem_ball ht)
    rw [kser_parityDiff hst'.1 hst.1, exp_sub, hst'.2, kernelQuot_neg hodd hs ht, ← hst.2,
      div_self (exp_ne_zero _)]
  have hzero := coeff_zero_of_exp_kser_eq_one hc0 hS hexp
  have hcoef : ∀ n m : ℕ, (n + m) % 2 = 1 → γ n m = 0 := by
    intro n m hnm
    have h1 := hzero n m
    rw [parityDiff, (Nat.odd_iff.mpr hnm).neg_one_pow] at h1
    have h2 : (-1 - 1 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h1).resolve_left h2
  refine ⟨fun s t _ _ => ?_, hcoef⟩
  unfold kser
  refine tsum_congr (fun nm => ?_)
  rw [neg_pow s, neg_pow t]
  rcases Nat.even_or_odd (nm.1 + nm.2) with he | ho
  · have h1 : (-1 : ℂ) ^ nm.1 * (-1) ^ nm.2 = 1 := by rw [← pow_add, he.neg_one_pow]
    linear_combination (γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2) * h1
  · rw [hcoef _ _ (Nat.odd_iff.mp ho)]
    ring

/-! ## The identity function -/

private theorem kernelQuot_id (s t : ℂ) : kernelQuot (fun x => x) s t = 1 := by
  have e1 : (if s = t then deriv (fun x : ℂ => x) s else (s - t) / (s - t)) = 1 := by
    split_ifs with h
    · exact congrFun deriv_id'' s
    · exact div_self (sub_ne_zero.mpr h)
  have e2 : ∀ u : ℂ, (if u = 0 then 1 else u / u) = 1 := by
    intro u
    split_ifs with h
    · rfl
    · exact div_self h
  simp only [kernelQuot, e1, e2, mul_one]

theorem sec7_identity_O2_proved :
    IsOddRoot (fun z => z) (fun s => s) ∧ ∀ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff (fun s => s) γ → ∀ θ : ℝ, O2 γ θ = 0 := by
  refine ⟨⟨differentiableOn_id, fun s _ => rfl, fun s _ => rfl, congrFun deriv_id'' 0⟩, fun γ hγ θ => ?_⟩
  have hzero : ∀ n m, γ n m = 0 :=
    coeff_zero_of_exp_kser_eq_one (fun m => hγ.1 0 m (Or.inl rfl)) (grunsky_summable_half hγ)
      (fun s t hs ht => by rw [(hγ.2 s t hs ht).2, kernelQuot_id])
  ext i j
  simp [O2, bilinf, Oblock, Cmat, hzero]

end Robinson.Proofs
