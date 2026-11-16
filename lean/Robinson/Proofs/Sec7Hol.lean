/-
Robinson/Proofs/Sec7Hol.lean — proofs of lem_7_2, sec7_UR_zero, prop_7_5_i, lem_7_6_i, lem_7_6_ii.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Matrix2
import Robinson.ComputerChecked
import Robinson.Proofs.Arith

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## Lemma 7.6: the bands of Table 3 cover the two angle ranges -/

theorem lem_7_6_i_proved (h1 : Check_7_6_band01) (h2 : Check_7_6_band02) (h3 : Check_7_6_band03) (h4 : Check_7_6_band04)
    (h5 : Check_7_6_band05) : ∀ θ : ℝ, 50.3 ≤ θ → θ ≤ 90 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω := by
  intro θ ha hb α ψ ω hX
  rcases le_total θ 55 with h55 | h55
  · exact h1 θ ha h55 α ψ ω hX
  rcases le_total θ 60 with h60 | h60
  · exact h2 θ h55 h60 α ψ ω hX
  rcases le_total θ 70 with h70 | h70
  · exact h3 θ h60 h70 α ψ ω hX
  rcases le_total θ 80 with h80 | h80
  · exact h4 θ h70 h80 α ψ ω hX
  · exact h5 θ h80 hb α ψ ω hX

theorem lem_7_6_ii_proved (h6 : Check_7_6_band06) (h7 : Check_7_6_band07) (h8 : Check_7_6_band08)
    (h9 : Check_7_6_band09) (h10 : Check_7_6_band10) (h11 : Check_7_6_band11) :
    ∀ θ : ℝ, 90 ≤ θ → θ ≤ 135 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω := by
  intro θ ha hb α ψ ω hX
  rcases le_total θ 95 with h95 | h95
  · exact h6 θ ha h95 α ψ ω hX
  rcases le_total θ 100 with h100 | h100
  · exact h7 θ h95 h100 α ψ ω hX
  rcases le_total θ 105 with h105 | h105
  · exact h8 θ h100 h105 α ψ ω hX
  rcases le_total θ 115 with h115 | h115
  · exact h9 θ h105 h115 α ψ ω hX
  rcases le_total θ 125 with h125 | h125
  · exact h10 θ h115 h125 α ψ ω hX
  · exact h11 θ h125 hb α ψ ω hX

/-! ## Elementary facts: `tan(θ/4) > 0`, `χ ≠ 0` -/

private lemma tan_quarter_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < Real.tan (θ / 4) := by
  apply Real.tan_pos_of_pos_of_lt_pi_div_two
  · linarith
  · linarith [Real.pi_pos]

private lemma chi_ne_zero {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    chi θ M ≠ 0 := by
  have ht : (Real.tan (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast (tan_quarter_pos h0 hπ).ne'
  unfold chi
  exact mul_ne_zero (mul_ne_zero I_ne_zero ht) (Complex.exp_ne_zero _)

/-! ## The value at `M = 0` -/

private lemma bil_zero_mat (x y : Fin 2 → ℂ) : bil x 0 y = 0 := by simp [bil]

/-- `Log(1 + i tan x) - Log(1 - i tan x) = 2 i x` for `0 ≤ x < π/2`. -/
private lemma log_one_add_I_tan_sub (x : ℝ) (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    log (1 + I * (Real.tan x : ℂ)) - log (1 - I * (Real.tan x : ℂ)) = 2 * (x : ℂ) * I := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx⟩
  have hconj : 1 - I * (Real.tan x : ℂ) = conj (1 + I * (Real.tan x : ℂ)) := by
    rw [map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hre : 0 < (1 + I * (Real.tan x : ℂ)).re := by simp
  have harg_ne : (1 + I * (Real.tan x : ℂ)).arg ≠ Real.pi := by
    intro h
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  have hwform : 1 + I * (Real.tan x : ℂ) =
      ((1 / Real.cos x : ℝ) : ℂ) * (Complex.cos (x : ℂ) + Complex.sin (x : ℂ) * I) := by
    have hc : Complex.cos (x : ℂ) ≠ 0 := by rw [← Complex.ofReal_cos]; exact_mod_cast hcos.ne'
    rw [Real.tan_eq_sin_div_cos]
    push_cast
    linear_combination (-1 : ℂ) * mul_inv_cancel₀ hc
  have harg : (1 + I * (Real.tan x : ℂ)).arg = x := by
    rw [hwform, Complex.arg_real_mul _ (one_div_pos.mpr hcos), Complex.arg_cos_add_sin_mul_I]
    constructor <;> linarith [Real.pi_pos]
  rw [hconj, Complex.log_conj _ harg_ne, Complex.sub_conj, Complex.log_im, harg]
  push_cast
  ring

theorem sec7_UR_zero_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    I * Ufun θ 0 = 0 ∧ Rfun θ 0 = 0 := by
  have hA : cA θ 0 = 0 := bil_zero_mat _ _
  have hB : cB θ 0 = 0 := bil_zero_mat _ _
  have hC : cC θ 0 = 0 := bil_zero_mat _ _
  have h1 : ell1 θ 0 = 0 := by simp [ell1, hA, hB, hC]
  have h2 : ell2 θ 0 = 0 := by simp [ell2, hA, hB, hC]
  have hk : chi θ 0 = I * (Real.tan (θ / 4) : ℂ) := by simp [chi, kappa, hA, hB]
  constructor
  · have hlog := log_one_add_I_tan_sub (θ / 4) (by linarith) (by linarith [Real.pi_pos])
    simp only [Ufun, Delta, hk, hC]
    push_cast at hlog ⊢
    linear_combination (-I) * hlog
  · simp only [Rfun, Qrel, h1, h2, Complex.exp_zero]
    ring

/-! ## The series bound `|artanh z| ≤ artanh |z|` -/

/-- `log(1+z) - log(1-z) = ∑ (1 + (-1)^(n+1)) zⁿ/n` on the unit disc. -/
private lemma hasSum_log_sub_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (((1 + (-1 : ℝ) ^ (n + 1)) : ℝ) : ℂ) * z ^ n / n) (log (1 + z) - log (1 - z)) := by
  have h := (hasSum_taylorSeries_log hz).add (hasSum_taylorSeries_neg_log hz)
  rw [← sub_eq_add_neg] at h
  convert h using 1
  funext n
  push_cast
  ring

private lemma hasSum_log_sub_log_real {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    HasSum (fun n : ℕ => (1 + (-1 : ℝ) ^ (n + 1)) * r ^ n / n) (Real.log (1 + r) - Real.log (1 - r)) := by
  have h := hasSum_log_sub_log (z := (r : ℂ)) (by rwa [Complex.norm_real, Real.norm_of_nonneg hr0])
  have e1 : ((Real.log (1 + r) : ℝ) : ℂ) = log (1 + (r : ℂ)) := by
    rw [Complex.ofReal_log (by linarith)]; push_cast; rfl
  have e2 : ((Real.log (1 - r) : ℝ) : ℂ) = log (1 - (r : ℂ)) := by
    rw [Complex.ofReal_log (by linarith)]; push_cast; rfl
  rw [← Complex.hasSum_ofReal, Complex.ofReal_sub, e1, e2]
  convert h using 1
  funext n
  push_cast
  ring

private lemma norm_log_sub_log_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - log (1 - z)‖ ≤ Real.log (1 + ‖z‖) - Real.log (1 - ‖z‖) := by
  refine (hasSum_log_sub_log hz).norm_le_of_bounded (hasSum_log_sub_log_real (norm_nonneg z) hz) ?_
  intro n
  have hc : 0 ≤ 1 + (-1 : ℝ) ^ (n + 1) := by
    rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> norm_num
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc, Complex.norm_natCast]

/-- `Log((1+z)/(1-z)) = Log(1+z) - Log(1-z)` on the unit disc. -/
private lemma log_div_eq {z : ℂ} (hz : ‖z‖ < 1) :
    log ((1 + z) / (1 - z)) = log (1 + z) - log (1 - z) := by
  have hre := Complex.abs_re_le_norm z
  have hre1 : 0 < (1 + z).re := by
    rw [Complex.add_re, Complex.one_re]; linarith [(abs_le.mp hre).1]
  have hre2 : 0 < (1 - z).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith [(abs_le.mp hre).2]
  have hne1 : 1 + z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre1; exact lt_irrefl 0 hre1
  have hne2 : 1 - z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre2; exact lt_irrefl 0 hre2
  have ha1 := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1))
  have ha2 := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2))
  have key : exp (log (1 + z) - log (1 - z)) = (1 + z) / (1 - z) := by
    rw [Complex.exp_sub, Complex.exp_log hne1, Complex.exp_log hne2]
  have him : (log (1 + z) - log (1 - z)).im = (1 + z).arg - (1 - z).arg := by
    rw [Complex.sub_im, Complex.log_im, Complex.log_im]
  rw [← key, Complex.log_exp] <;> rw [him] <;> linarith [Real.pi_pos]

private lemma norm_zθ (θ : ℝ) : ‖zθ θ‖ = 1 / 2 := by
  rw [zθ, norm_mul, Complex.norm_exp_ofReal_mul_I]
  norm_num

private lemma Ao_eq : Ao = 1 / 2 * Real.log 3 := by
  have := sec6_L_log3_proved.1
  linarith

private lemma Ao_pos : 0 < Ao := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  rw [Ao_eq]
  linarith

/-- `|Z_o| ≤ A_o`, that is `|artanh z_θ| ≤ artanh ½`. -/
private lemma norm_Zo_le (θ : ℝ) : ‖Zo θ‖ ≤ Ao := by
  have hz1 : ‖zθ θ‖ = 1 / 2 := norm_zθ θ
  have hz : ‖zθ θ‖ < 1 := by rw [hz1]; norm_num
  have h := norm_log_sub_log_le hz
  rw [hz1] at h
  have h3 : Real.log (1 + 1 / 2) - Real.log (1 - 1 / 2) = Real.log 3 := by
    rw [← Real.log_div (by norm_num : (1 + 1 / 2 : ℝ) ≠ 0) (by norm_num : (1 - 1 / 2 : ℝ) ≠ 0)]
    norm_num
  rw [h3] at h
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [Zo, cartanh, log_div_eq hz, norm_mul, hhalf, Ao_eq]
  linarith

/-! ## The Gram–Schmidt coordinates: `|ũ|² + |ṽ|² = A_o` -/

private lemma coords_sum (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) :
    Real.sqrt a ^ 2 + ((c / Real.sqrt a) ^ 2 + Real.sqrt (b - (c / Real.sqrt a) ^ 2) ^ 2) = a + b := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp [Real.sq_sqrt hb]
  · have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have h21 : (c / Real.sqrt a) ^ 2 = c ^ 2 / a := by rw [div_pow, hs]
    have hle : c ^ 2 / a ≤ b := by rw [div_le_iff₀ h]; linarith
    rw [h21, hs, Real.sq_sqrt (by linarith)]
    ring

private lemma l_sum_le (θ : ℝ) : l11 θ ^ 2 + (l21 θ ^ 2 + l22 θ ^ 2) ≤ Ao := by
  have hZ := norm_Zo_le θ
  have hsq : (Zo θ).re ^ 2 + (Zo θ).im ^ 2 ≤ Ao ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hZ 2
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    nlinarith
  have hAo := Ao_pos
  have hre1 : -Ao ≤ (Zo θ).re := by nlinarith [sq_nonneg (Zo θ).im]
  have hre2 : (Zo θ).re ≤ Ao := by nlinarith [sq_nonneg (Zo θ).im]
  have hc : ((Zo θ).im / 2) ^ 2 ≤ ((Ao + (Zo θ).re) / 2) * ((Ao - (Zo θ).re) / 2) := by nlinarith
  have key := coords_sum ((Ao + (Zo θ).re) / 2) ((Ao - (Zo θ).re) / 2) ((Zo θ).im / 2)
    (by linarith) (by linarith) hc
  have e : l11 θ ^ 2 + (l21 θ ^ 2 + l22 θ ^ 2) = (Ao + (Zo θ).re) / 2 + (Ao - (Zo θ).re) / 2 := key
  linarith

/-! ## Bilinear forms with real vectors are bounded by the operator norm -/

private lemma norm_bil_le (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℝ) :
    ‖bil (fun i => (x i : ℂ)) M (fun i => (x i : ℂ))‖ ≤ opNorm M * (x 0 ^ 2 + x 1 ^ 2) := by
  have hstar : star (fun i => (x i : ℂ)) = fun i => (x i : ℂ) := by funext i; simp
  have hinner : bil (fun i => (x i : ℂ)) M (fun i => (x i : ℂ)) =
      inner ℂ (WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ (Fin 2))
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M (WithLp.toLp 2 (fun i => (x i : ℂ)))) := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, hstar, bil, dotProduct_comm]
  have hXn : ‖(WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ (Fin 2))‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp
  rw [hinner]
  refine (norm_inner_le_norm _ _).trans ?_
  calc _ ≤ ‖(WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ (Fin 2))‖ *
        (opNorm M * ‖(WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ (Fin 2))‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = opNorm M * ‖(WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ (Fin 2))‖ ^ 2 := by ring
    _ = _ := by rw [hXn]

private lemma ut_eq (θ : ℝ) : ut θ = fun i => ((![l11 θ, 0] : Fin 2 → ℝ) i : ℂ) := by
  funext i; fin_cases i <;> simp [ut]

private lemma vt_eq (θ : ℝ) : vt θ = fun i => ((![l21 θ, l22 θ] : Fin 2 → ℝ) i : ℂ) := by
  funext i; fin_cases i <;> simp [vt]

private lemma opNorm_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ opNorm M := by
  unfold opNorm; exact norm_nonneg _

private lemma norm_cA_le (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖cA θ M‖ ≤ opNorm M * l11 θ ^ 2 := by
  have h := norm_bil_le M ![l11 θ, 0]
  rw [← ut_eq] at h
  simpa [cA] using h

private lemma norm_cB_le (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖cB θ M‖ ≤ opNorm M * (l21 θ ^ 2 + l22 θ ^ 2) := by
  have h := norm_bil_le M ![l21 θ, l22 θ]
  rw [← vt_eq] at h
  simpa [cB] using h

private lemma norm_kappa_le (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖kappa θ M‖ ≤ opNorm M * Ao := by
  calc ‖kappa θ M‖ ≤ ‖cA θ M‖ + ‖cB θ M‖ := norm_add_le _ _
    _ ≤ opNorm M * l11 θ ^ 2 + opNorm M * (l21 θ ^ 2 + l22 θ ^ 2) :=
        add_le_add (norm_cA_le θ M) (norm_cB_le θ M)
    _ = opNorm M * (l11 θ ^ 2 + (l21 θ ^ 2 + l22 θ ^ 2)) := by ring
    _ ≤ opNorm M * Ao := mul_le_mul_of_nonneg_left (l_sum_le θ) (opNorm_nonneg M)

/-! ## The radius `π / log 9` -/

private lemma log9_eq : Real.log 9 = 4 * Ao := by
  rw [Ao_eq, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

private lemma log9_pos : 0 < Real.log 9 := Real.log_pos (by norm_num)

private lemma log9_lt_pi : Real.log 9 < Real.pi := by
  obtain ⟨h1, h2, h3⟩ := sec6_L_log3_proved
  rw [h2] at h3
  rw [log9_eq]
  linarith

private lemma one_lt_bound : 1 < Real.pi / Real.log 9 := by
  rw [one_lt_div log9_pos]
  exact log9_lt_pi

private lemma bound_mul_Ao : Real.pi / Real.log 9 * Ao = Real.pi / 4 := by
  rw [log9_eq, div_mul_eq_mul_div, mul_div_mul_right _ _ Ao_pos.ne']

private lemma kappa_small (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : opNorm M < Real.pi / Real.log 9) :
    ‖kappa θ M‖ < Real.pi / 4 :=
  calc ‖kappa θ M‖ ≤ opNorm M * Ao := norm_kappa_le θ M
    _ < Real.pi / Real.log 9 * Ao := mul_lt_mul_of_pos_right hM Ao_pos
    _ = Real.pi / 4 := bound_mul_Ao

/-- On `{‖M‖ < π/log 9}`, `Im χ = tan(θ/4) Re e^{2κ} > 0`. -/
private lemma chi_im_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : opNorm M < Real.pi / Real.log 9) : 0 < (chi θ M).im := by
  have ht := tan_quarter_pos h0 hπ
  have hk := kappa_small θ M hM
  have him : |(2 * kappa θ M).im| < Real.pi / 2 := by
    calc |(2 * kappa θ M).im| ≤ ‖2 * kappa θ M‖ := Complex.abs_im_le_norm _
      _ = 2 * ‖kappa θ M‖ := by rw [norm_mul]; norm_num
      _ < Real.pi / 2 := by linarith
  have hcos : 0 < Real.cos ((2 * kappa θ M).im) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp him).1], (abs_lt.mp him).2⟩
  have hre : 0 < (exp (2 * kappa θ M)).re := by
    rw [Complex.exp_re]; exact mul_pos (Real.exp_pos _) hcos
  have e : (chi θ M).im = Real.tan (θ / 4) * (exp (2 * kappa θ M)).re := by
    simp only [chi, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [e]
  exact mul_pos ht hre

private lemma one_add_chi_mem {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : opNorm M < Real.pi / Real.log 9) : 1 + chi θ M ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simpa using (chi_im_pos h0 hπ M hM).ne'

private lemma one_sub_chi_mem {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : opNorm M < Real.pi / Real.log 9) : 1 - chi θ M ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simpa using (chi_im_pos h0 hπ M hM).ne'

/-! ## Holomorphy in the entries `p = (a, b, d)` of `M = [[a, b], [b, d]]` -/

private lemma bil_symMat (x y : Fin 2 → ℂ) (p : ℂ × ℂ × ℂ) :
    bil x (symMat p) y = x 0 * (p.1 * y 0 + p.2.1 * y 1) + x 1 * (p.2.1 * y 0 + p.2.2 * y 1) := by
  simp [bil, symMat, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

private lemma diff_bil (x y : Fin 2 → ℂ) : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => bil x (symMat p) y) := by
  simp only [bil_symMat]
  fun_prop

private lemma diff_cA (θ : ℝ) : Differentiable ℂ (fun p => cA θ (symMat p)) := diff_bil _ _
private lemma diff_cB (θ : ℝ) : Differentiable ℂ (fun p => cB θ (symMat p)) := diff_bil _ _
private lemma diff_cC (θ : ℝ) : Differentiable ℂ (fun p => cC θ (symMat p)) := diff_bil _ _

private lemma diff_ell1 (θ : ℝ) : Differentiable ℂ (fun p => ell1 θ (symMat p)) :=
  (((diff_cA θ).sub (diff_cB θ)).const_mul 2).add ((diff_cC θ).const_mul (4 * I))

private lemma diff_ell2 (θ : ℝ) : Differentiable ℂ (fun p => ell2 θ (symMat p)) :=
  (((diff_cA θ).sub (diff_cB θ)).const_mul 2).sub ((diff_cC θ).const_mul (4 * I))

private lemma diff_chi (θ : ℝ) : Differentiable ℂ (fun p => chi θ (symMat p)) :=
  ((((diff_cA θ).add (diff_cB θ)).const_mul 2).cexp).const_mul (I * (Real.tan (θ / 4) : ℂ))

private lemma Qrel_eq (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Qrel θ M = 1 + (1 / 2 : ℂ) * (exp (ell1 θ M) + exp (ell2 θ M)) +
      (1 / 4 : ℂ) * ((exp (ell1 θ M) - exp (ell2 θ M)) * (chi θ M + (chi θ M)⁻¹)) := by
  unfold Qrel
  ring

private lemma diff_Qrel {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    Differentiable ℂ (fun p => Qrel θ (symMat p)) := by
  have he1 := (diff_ell1 θ).cexp
  have he2 := (diff_ell2 θ).cexp
  have hc := diff_chi θ
  have hci : Differentiable ℂ (fun p => (chi θ (symMat p))⁻¹) :=
    hc.inv (fun p => chi_ne_zero h0 hπ (symMat p))
  simp only [Qrel_eq]
  exact ((differentiable_const (1 : ℂ)).add ((he1.add he2).const_mul (1 / 2 : ℂ))).add
    (((he1.sub he2).mul (hc.add hci)).const_mul (1 / 4 : ℂ))

private lemma diff_Rfun {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    Differentiable ℂ (fun p => Rfun θ (symMat p)) :=
  ((diff_Qrel h0 hπ).sub (diff_ell1 θ).cexp).sub (diff_ell2 θ).cexp

private lemma diffOn_Delta {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    DifferentiableOn ℂ (fun p => Delta θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} := by
  intro p hp
  have hc := diff_chi θ
  have h1 : DifferentiableAt ℂ (fun q => log (1 + chi θ (symMat q))) p :=
    ((differentiableAt_const (1 : ℂ)).add (hc p)).clog (one_add_chi_mem h0 hπ _ hp)
  have h2 : DifferentiableAt ℂ (fun q => log (1 - chi θ (symMat q))) p :=
    ((differentiableAt_const (1 : ℂ)).sub (hc p)).clog (one_sub_chi_mem h0 hπ _ hp)
  exact (((differentiableAt_const (I * ((θ / 2 : ℝ) : ℂ))).sub h1).add h2).differentiableWithinAt

private lemma diffOn_Ufun {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    DifferentiableOn ℂ (fun p => Ufun θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} :=
  (diffOn_Delta h0 hπ).add ((diff_cC θ).const_mul (4 * I)).differentiableOn

/-! ## The set `{‖M‖ < π / log 9}` is open in `ℂ³` -/

private lemma continuous_symMat : Continuous symMat := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [symMat] <;> fun_prop

private lemma continuous_opNorm_symMat : Continuous (fun p : ℂ × ℂ × ℂ => opNorm (symMat p)) := by
  have hT : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M) :=
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  exact continuous_norm.comp (hT.comp continuous_symMat)

private lemma isOpen_bound : IsOpen {p : ℂ × ℂ × ℂ | opNorm (symMat p) < Real.pi / Real.log 9} :=
  isOpen_lt continuous_opNorm_symMat continuous_const

/-! ## Conjugation symmetry -/

private lemma bil_mconj_real (x y : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    bil (fun i => (x i : ℂ)) (mconj M) (fun i => (y i : ℂ)) =
      conj (bil (fun i => (x i : ℂ)) M (fun i => (y i : ℂ))) := by
  simp [bil, mconj, dotProduct, Matrix.mulVec, Fin.sum_univ_two, map_add, map_mul, Complex.conj_ofReal]

private lemma cA_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : cA θ (mconj M) = conj (cA θ M) := by
  rw [cA, cA, ut_eq]; exact bil_mconj_real _ _ _

private lemma cB_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : cB θ (mconj M) = conj (cB θ M) := by
  rw [cB, cB, vt_eq]; exact bil_mconj_real _ _ _

private lemma cC_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : cC θ (mconj M) = conj (cC θ M) := by
  rw [cC, cC, ut_eq, vt_eq]; exact bil_mconj_real _ _ _

private lemma ell1_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ell1 θ (mconj M) = conj (ell2 θ M) := by
  rw [ell1, ell2, cA_mconj, cB_mconj, cC_mconj]
  simp only [map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

private lemma ell2_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ell2 θ (mconj M) = conj (ell1 θ M) := by
  rw [ell1, ell2, cA_mconj, cB_mconj, cC_mconj]
  simp only [map_add, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

private lemma chi_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : chi θ (mconj M) = -conj (chi θ M) := by
  have hk : kappa θ (mconj M) = conj (kappa θ M) := by
    rw [kappa, kappa, cA_mconj, cB_mconj, map_add]
  rw [chi, chi, hk, show (2 : ℂ) * conj (kappa θ M) = conj (2 * kappa θ M) by
    rw [map_mul, map_ofNat], Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

private lemma Qrel_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Qrel θ (mconj M) = conj (Qrel θ M) := by
  rw [Qrel, Qrel, ell1_mconj, ell2_mconj, chi_mconj, Complex.exp_conj, Complex.exp_conj]
  simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_one, map_ofNat, inv_neg]
  ring

private lemma Rfun_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Rfun θ (mconj M) = conj (Rfun θ M) := by
  rw [Rfun, Rfun, Qrel_mconj, ell1_mconj, ell2_mconj, Complex.exp_conj, Complex.exp_conj]
  simp only [map_sub]
  ring

private lemma IU_mconj {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : opNorm M < Real.pi / Real.log 9) : I * Ufun θ (mconj M) = conj (I * Ufun θ M) := by
  have hp := (mem_slitPlane_iff_arg.mp (one_add_chi_mem h0 hπ M hM)).1
  have hm := (mem_slitPlane_iff_arg.mp (one_sub_chi_mem h0 hπ M hM)).1
  have e1 : 1 + chi θ (mconj M) = conj (1 - chi θ M) := by
    rw [chi_mconj, map_sub, map_one]; ring
  have e2 : 1 - chi θ (mconj M) = conj (1 + chi θ M) := by
    rw [chi_mconj, map_add, map_one]; ring
  rw [Ufun, Ufun, Delta, Delta, e1, e2, cC_mconj, Complex.log_conj _ hm, Complex.log_conj _ hp]
  simp only [map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-! ## Lemma 7.2 -/

theorem lem_7_2_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    1 < Real.pi / Real.log 9 ∧ IsOpen {p : ℂ × ℂ × ℂ | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      DifferentiableOn ℂ (fun p => Delta θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      DifferentiableOn ℂ (fun p => Ufun θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      DifferentiableOn ℂ (fun p => Rfun θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      ∀ M : Matrix (Fin 2) (Fin 2) ℂ, Mᵀ = M → opNorm M < Real.pi / Real.log 9 →
        I * Ufun θ (mconj M) = conj (I * Ufun θ M) ∧ Rfun θ (mconj M) = conj (Rfun θ M) :=
  ⟨one_lt_bound, isOpen_bound, diffOn_Delta h0 hπ, diffOn_Ufun h0 hπ, (diff_Rfun h0 hπ).differentiableOn,
    fun M _ hM => ⟨IU_mconj h0 hπ M hM, Rfun_mconj θ M⟩⟩

/-! ## Proposition 7.5 (i) -/

theorem prop_7_5_i_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    HolomorphicNearBall (Ffun θ) ∧ ∀ M, InBall M → Ffun θ (mconj M) = conj (Ffun θ M) := by
  refine ⟨⟨{p | opNorm (symMat p) < Real.pi / Real.log 9}, isOpen_bound, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact lt_of_le_of_lt hp.2 one_lt_bound
  · have hQ := (diff_Qrel h0 hπ).differentiableOn (s := {p | opNorm (symMat p) < Real.pi / Real.log 9})
    have hU := diffOn_Ufun h0 hπ
    have hR := (diff_Rfun h0 hπ).differentiableOn (s := {p | opNorm (symMat p) < Real.pi / Real.log 9})
    exact ((hQ.add ((hU.const_mul I).const_mul (4 / 5 : ℂ))).sub (hR.const_mul (1 / 2 : ℂ))).sub
      (differentiableOn_const _)
  · intro M hM
    have hM' : opNorm M < Real.pi / Real.log 9 := lt_of_le_of_lt hM.2 one_lt_bound
    rw [Ffun, Ffun, Qrel_mconj, IU_mconj h0 hπ M hM', Rfun_mconj]
    simp only [map_add, map_sub, map_mul, map_div₀, map_ofNat, map_one, Complex.conj_ofReal]

end Robinson.Proofs
