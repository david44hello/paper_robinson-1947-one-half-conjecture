/-
Robinson/Proofs/Sec5Finite.lean — proofs of sec5_s_sq, sec5_coords, sec5_tan_identity,
sec5_qrel_algebra, sec5_chi_qrel_entire, lem_5_4_qrel, rem_5_6.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Matrix2

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## `s² = z` and `t² = w` -/

theorem sec5_s_sq_proved (θ : ℝ) : sθ θ ^ 2 = zθ θ ∧ conj (sθ θ) ^ 2 = conj (zθ θ) := by
  have h : sθ θ ^ 2 = zθ θ := by
    unfold sθ zθ
    rw [mul_pow, ← Complex.exp_nat_mul]
    have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
      rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]
      push_cast
      ring
    have h3 : ((2 : ℕ) : ℂ) * (((θ / 4 : ℝ) : ℂ) * I) = ((θ / 2 : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h2, h3]
  exact ⟨h, by rw [← map_pow, h]⟩

/-! ## `(s - t)/(s + t) = i tan(θ/4)` -/

private lemma sθ_eq (θ : ℝ) :
    sθ θ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((Real.cos (θ / 4) : ℂ) + (Real.sin (θ / 4) : ℂ) * I) := by
  unfold sθ
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem sec5_tan_identity_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (sθ θ - conj (sθ θ)) / (sθ θ + conj (sθ θ)) = I * (Real.tan (θ / 4) : ℂ) := by
  have hc : 0 < Real.cos (θ / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have ha : 0 < (Real.sqrt 2)⁻¹ := by positivity
  rw [sθ_eq, Real.tan_eq_sin_div_cos]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  generalize hA : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = A
  have hA0 : A ≠ 0 := by rw [← hA]; exact_mod_cast ha.ne'
  have hc' : (Real.cos (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
  ring

/-! ## The algebra of the proof of Proposition 5.1 -/

theorem sec5_qrel_algebra_proved (p q χ fz fw : ℂ) (hχ0 : χ ≠ 0) (hχ1 : χ ≠ 1) (hfw : fw ≠ 0)
    (hne : fz ≠ fw) (hratio : fz / fw = ((1 + χ) / (1 - χ)) ^ 2) :
    1 + (p * fz - q * fw) / (fz - fw) = 1 + (p * ((1 + χ) / (1 - χ)) ^ 2 - q) / (((1 + χ) / (1 - χ)) ^ 2 - 1) ∧
      1 + (p * ((1 + χ) / (1 - χ)) ^ 2 - q) / (((1 + χ) / (1 - χ)) ^ 2 - 1) =
        1 + (p * (1 + χ) ^ 2 - q * (1 - χ) ^ 2) / (4 * χ) ∧
      1 + (p * (1 + χ) ^ 2 - q * (1 - χ) ^ 2) / (4 * χ) = 1 + (p + q) / 2 + (p - q) * (χ + χ⁻¹) / 4 := by
  have h1 : (1 - χ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hχ1)
  have h4 : (4 * χ) ≠ 0 := mul_ne_zero (by norm_num) hχ0
  set ρ := (1 + χ) / (1 - χ) with hρ
  have hfz : fz = ρ ^ 2 * fw := by rw [← hratio]; field_simp
  have hρ1 : ρ ^ 2 - 1 ≠ 0 := by
    intro h
    apply hne
    have : ρ ^ 2 = 1 := by linear_combination h
    rw [hfz, this, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfz, show p * (ρ ^ 2 * fw) - q * fw = (p * ρ ^ 2 - q) * fw by ring,
      show ρ ^ 2 * fw - fw = (ρ ^ 2 - 1) * fw by ring, mul_div_mul_right _ _ hfw]
  · congr 1
    rw [div_eq_div_iff hρ1 h4, hρ]
    field_simp
    ring
  · field_simp
    ring

/-! ## The symmetry `Q_rel(M̄) = conj Q_rel(M)` -/

private lemma cA_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : cA θ (mconj M) = conj (cA θ M) := by
  simp [cA, bil, ut, mconj, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

private lemma cB_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : cB θ (mconj M) = conj (cB θ M) := by
  simp [cB, bil, vt, mconj, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

private lemma cC_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : cC θ (mconj M) = conj (cC θ M) := by
  simp [cC, bil, ut, vt, mconj, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

set_option linter.unusedVariables false in
theorem lem_5_4_qrel_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Qrel θ (mconj M) = conj (Qrel θ M) := by
  have h1 : ell1 θ (mconj M) = conj (ell2 θ M) := by
    simp only [ell1, ell2, cA_mconj, cB_mconj, cC_mconj, map_sub, map_mul, map_ofNat, Complex.conj_I]
    ring
  have h2 : ell2 θ (mconj M) = conj (ell1 θ M) := by
    simp only [ell1, ell2, cA_mconj, cB_mconj, cC_mconj, map_sub, map_add, map_mul, map_ofNat,
      Complex.conj_I]
    ring
  have hχ : chi θ (mconj M) = -conj (chi θ M) := by
    simp only [chi, kappa, cA_mconj, cB_mconj, map_mul, map_add, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal, ← Complex.exp_conj]
    ring
  rw [Qrel, Qrel, h1, h2, hχ]
  simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, map_inv₀, ← Complex.exp_conj,
    inv_neg]
  ring

/-! ## `χ` never vanishes and `Q_rel` is entire -/

private lemma cA_symMat (θ : ℝ) (p : ℂ × ℂ × ℂ) : cA θ (symMat p) = (l11 θ : ℂ) ^ 2 * p.1 := by
  simp [cA, bil, ut, symMat, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

private lemma cB_symMat (θ : ℝ) (p : ℂ × ℂ × ℂ) :
    cB θ (symMat p) =
      (l21 θ : ℂ) ^ 2 * p.1 + 2 * (l21 θ : ℂ) * (l22 θ : ℂ) * p.2.1 + (l22 θ : ℂ) ^ 2 * p.2.2 := by
  simp [cB, bil, vt, symMat, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

private lemma cC_symMat (θ : ℝ) (p : ℂ × ℂ × ℂ) :
    cC θ (symMat p) = (l11 θ : ℂ) * ((l21 θ : ℂ) * p.1 + (l22 θ : ℂ) * p.2.1) := by
  simp [cC, bil, ut, vt, symMat, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  left
  ring

private lemma tan_quarter_pos (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < Real.tan (θ / 4) :=
  Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [Real.pi_pos])

theorem sec5_chi_qrel_entire_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ, chi θ M ≠ 0) ∧
      Differentiable ℂ (fun p : ℂ × ℂ × ℂ => Qrel θ (symMat p)) := by
  have hne : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, chi θ M ≠ 0 := by
    intro M
    have ht : (Real.tan (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast (tan_quarter_pos θ h0 hπ).ne'
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero ht) (Complex.exp_ne_zero _)
  refine ⟨hne, ?_⟩
  have hA : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => cA θ (symMat p)) := by
    simp only [cA_symMat]; fun_prop
  have hB : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => cB θ (symMat p)) := by
    simp only [cB_symMat]; fun_prop
  have hC : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => cC θ (symMat p)) := by
    simp only [cC_symMat]; fun_prop
  have he1 : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => ell1 θ (symMat p)) :=
    ((differentiable_const 2).mul (hA.sub hB)).add ((differentiable_const (4 * I)).mul hC)
  have he2 : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => ell2 θ (symMat p)) :=
    ((differentiable_const 2).mul (hA.sub hB)).sub ((differentiable_const (4 * I)).mul hC)
  have hk : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => kappa θ (symMat p)) := hA.add hB
  have hχ : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => chi θ (symMat p)) :=
    (differentiable_const _).mul ((differentiable_const 2).mul hk).cexp
  have hχi : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => (chi θ (symMat p))⁻¹) :=
    hχ.inv (fun p => hne (symMat p))
  have hQ : (fun p : ℂ × ℂ × ℂ => Qrel θ (symMat p)) = fun p =>
      1 + (exp (ell1 θ (symMat p)) + exp (ell2 θ (symMat p))) * (2 : ℂ)⁻¹ +
        (exp (ell1 θ (symMat p)) - exp (ell2 θ (symMat p))) * (chi θ (symMat p) + (chi θ (symMat p))⁻¹) *
          (4 : ℂ)⁻¹ := by
    funext p
    simp only [Qrel, div_eq_mul_inv]
  rw [hQ]
  exact ((differentiable_const (1 : ℂ)).add ((he1.cexp.add he2.cexp).mul_const _)).add
    (((he1.cexp.sub he2.cexp).mul (hχ.add hχi)).mul_const _)

/-! ## The series `log(1+z) - log(1-z) = 2 ∑_{n odd} zⁿ/n` and the bound `|artanh z| < artanh ½` -/

/-- The `n`-th term of `log(1+z) - log(1-z) = ∑ ((-1)^(n+1) + 1) zⁿ/n`. -/
private noncomputable def atTerm (z : ℂ) (n : ℕ) : ℂ := (-1) ^ (n + 1) * z ^ n / n + z ^ n / n

/-- The same term at `z = 1/2`, as a real number. -/
private noncomputable def atTermR (n : ℕ) : ℝ := (-1) ^ (n + 1) * (1 / 2) ^ n / n + (1 / 2) ^ n / n

private lemma re_one_add_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 + z).re := by
  have := Complex.abs_re_le_norm z
  simp only [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le z.re]

private lemma re_one_sub_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 - z).re := by
  have := Complex.abs_re_le_norm z
  simp only [Complex.sub_re, Complex.one_re]
  linarith [le_abs_self z.re]

private lemma log_div_eq {z : ℂ} (hz : ‖z‖ < 1) :
    log ((1 + z) / (1 - z)) = log (1 + z) - log (1 - z) := by
  have h1 := re_one_add_pos hz
  have h2 := re_one_sub_pos hz
  have hne1 : 1 + z ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hne2 : 1 - z ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have ha1 := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h1))
  have ha2 := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h2))
  have hexp : exp (log (1 + z) - log (1 - z)) = (1 + z) / (1 - z) := by
    rw [Complex.exp_sub, Complex.exp_log hne1, Complex.exp_log hne2]
  rw [← hexp, Complex.log_exp]
  · simp only [Complex.sub_im, Complex.log_im]; linarith
  · simp only [Complex.sub_im, Complex.log_im]; linarith

private lemma hasSum_atTerm {z : ℂ} (hz : ‖z‖ < 1) : HasSum (atTerm z) (2 * cartanh z) := by
  have h := (Complex.hasSum_taylorSeries_log hz).add (Complex.hasSum_taylorSeries_neg_log hz)
  have e : 2 * cartanh z = log (1 + z) + -log (1 - z) := by
    rw [cartanh, log_div_eq hz]; ring
  rw [e]
  exact h

private lemma norm_atTerm {z : ℂ} (hz : ‖z‖ = 1 / 2) (n : ℕ) : ‖atTerm z n‖ = atTermR n := by
  unfold atTerm atTermR
  rcases Nat.even_or_odd n with hn | hn
  · have h : Odd (n + 1) := hn.add_one
    rw [h.neg_one_pow, h.neg_one_pow]
    simp only [neg_one_mul, neg_div, neg_add_cancel, norm_zero]
  · have h : Even (n + 1) := hn.add_one
    rw [h.neg_one_pow, h.neg_one_pow, one_mul, one_mul, ← two_mul, ← two_mul, norm_mul, norm_div,
      norm_pow, hz, Complex.norm_natCast]
    norm_num

private lemma atTerm_half (n : ℕ) : atTerm (1 / 2) n = (atTermR n : ℂ) := by
  unfold atTerm atTermR
  push_cast
  ring

private lemma Ao_eq : Ao = 1 / 2 * Real.log 3 := by
  rw [Ao, Real.artanh_eq_half_log (by constructor <;> norm_num)]
  norm_num

private lemma two_cartanh_half : 2 * cartanh (1 / 2) = ((2 * Ao : ℝ) : ℂ) := by
  rw [cartanh, Ao_eq]
  have e : (1 + 1 / 2 : ℂ) / (1 - 1 / 2) = ((3 : ℝ) : ℂ) := by push_cast; norm_num
  rw [e, ← Complex.ofReal_log (by norm_num)]
  push_cast
  ring

private lemma norm_half : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [norm_div, norm_one, Complex.norm_two]

private lemma hasSum_atTermR : HasSum atTermR (2 * Ao) := by
  have h := hasSum_atTerm (z := 1 / 2) (by rw [norm_half]; norm_num)
  rw [two_cartanh_half, show atTerm (1 / 2) = fun n => (atTermR n : ℂ) from funext atTerm_half] at h
  exact Complex.hasSum_ofReal.mp h

private lemma atTermR_nonneg (n : ℕ) : 0 ≤ atTermR n := by
  rw [← norm_atTerm norm_half n]
  exact norm_nonneg _

private lemma sum_atTermR_le (N : ℕ) : ∑ i ∈ Finset.range N, atTermR i ≤ 2 * Ao :=
  sum_le_hasSum (Finset.range N) (fun i _ => atTermR_nonneg i) hasSum_atTermR

/-- On the circle `|z| = 1/2` the tail of the series for `2 artanh z` is bounded by the tail at `z = 1/2`. -/
private lemma norm_two_cartanh_sub_le {z : ℂ} (hz : ‖z‖ = 1 / 2) (N : ℕ) :
    ‖2 * cartanh z - ∑ i ∈ Finset.range N, atTerm z i‖ ≤ 2 * Ao - ∑ i ∈ Finset.range N, atTermR i := by
  have hz1 : ‖z‖ < 1 := by rw [hz]; norm_num
  have h1 := (hasSum_nat_add_iff' N).mpr (hasSum_atTerm hz1)
  have h2 := (hasSum_nat_add_iff' N).mpr hasSum_atTermR
  exact h1.norm_le_of_bounded h2 (fun n => (norm_atTerm hz (n + N)).le)

/-- The tail at `z = 1/2` after `N` terms is at most `4 · 2^{-N} / N`. -/
private lemma two_Ao_sub_le (N : ℕ) (hN : 0 < N) :
    2 * Ao - ∑ i ∈ Finset.range N, atTermR i ≤ 4 * (1 / 2) ^ N / N := by
  have h1 := (hasSum_nat_add_iff' N).mpr hasSum_atTermR
  have hg : HasSum (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ N / N * (1 / 2) ^ n)
      (2 * (1 / 2 : ℝ) ^ N / N * (1 - 1 / 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ∀ n : ℕ, atTermR (n + N) ≤ 2 * (1 / 2 : ℝ) ^ N / N * (1 / 2) ^ n := by
    intro n
    unfold atTermR
    have hk : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hkpos : (0 : ℝ) < ((n + N : ℕ) : ℝ) := lt_of_lt_of_le hNpos hk
    have hpm : (-1 : ℝ) ^ (n + N + 1) ≤ 1 := by
      rcases neg_one_pow_eq_or ℝ (n + N + 1) with h | h
      · exact h.le
      · rw [h]; norm_num
    have ha : (0 : ℝ) ≤ (1 / 2) ^ (n + N) := by positivity
    calc (-1 : ℝ) ^ (n + N + 1) * (1 / 2) ^ (n + N) / ((n + N : ℕ) : ℝ) + (1 / 2) ^ (n + N) / ((n + N : ℕ) : ℝ)
        = ((-1 : ℝ) ^ (n + N + 1) + 1) * (1 / 2) ^ (n + N) / ((n + N : ℕ) : ℝ) := by ring
      _ ≤ 2 * (1 / 2) ^ (n + N) / ((n + N : ℕ) : ℝ) := by
          gcongr
          linarith
      _ ≤ 2 * (1 / 2) ^ (n + N) / N := by gcongr
      _ = 2 * (1 / 2 : ℝ) ^ N / N * (1 / 2) ^ n := by rw [pow_add]; ring
  calc 2 * Ao - ∑ i ∈ Finset.range N, atTermR i ≤ 2 * (1 / 2 : ℝ) ^ N / N * (1 - 1 / 2)⁻¹ :=
        hasSum_le hle h1 hg
    _ = 4 * (1 / 2) ^ N / N := by norm_num; ring

private lemma norm_one_add_sq_div_three_lt {z : ℂ} (hz : ‖z‖ = 1 / 2) (hz2 : (z ^ 2).re < 1 / 4) :
    ‖1 + z ^ 2 / 3‖ < 13 / 12 := by
  have hw : (z ^ 2).re ^ 2 + (z ^ 2).im ^ 2 = 1 / 16 := by
    have : ‖z ^ 2‖ ^ 2 = 1 / 16 := by rw [norm_pow, hz]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    linarith
  have hre : (1 + z ^ 2 / 3).re = 1 + (z ^ 2).re / 3 := by simp
  have him : (1 + z ^ 2 / 3).im = (z ^ 2).im / 3 := by simp
  have hsq : ‖1 + z ^ 2 / 3‖ ^ 2 < (13 / 12) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith
  nlinarith [norm_nonneg (1 + z ^ 2 / 3)]

/-- `|artanh z| < artanh ½` on the circle `|z| = 1/2` away from `z² = 1/4`. -/
private lemma norm_cartanh_lt {z : ℂ} (hz : ‖z‖ = 1 / 2) (hz2 : (z ^ 2).re < 1 / 4) :
    ‖cartanh z‖ < Ao := by
  have h := norm_two_cartanh_sub_le hz 4
  have hS : ∑ i ∈ Finset.range 4, atTerm z i = 2 * z * (1 + z ^ 2 / 3) := by
    simp [Finset.sum_range_succ, atTerm]
    ring
  have hR : ∑ i ∈ Finset.range 4, atTermR i = 13 / 12 := by
    simp [Finset.sum_range_succ, atTermR]
    norm_num
  rw [hS, hR] at h
  have hlt : ‖2 * z * (1 + z ^ 2 / 3)‖ < 13 / 12 := by
    rw [norm_mul, norm_mul, Complex.norm_two, hz]
    have := norm_one_add_sq_div_three_lt hz hz2
    linarith
  have h2 : ‖2 * cartanh z‖ < 2 * Ao := by
    calc ‖2 * cartanh z‖ = ‖(2 * cartanh z - 2 * z * (1 + z ^ 2 / 3)) + 2 * z * (1 + z ^ 2 / 3)‖ := by
          ring_nf
      _ ≤ ‖2 * cartanh z - 2 * z * (1 + z ^ 2 / 3)‖ + ‖2 * z * (1 + z ^ 2 / 3)‖ := norm_add_le _ _
      _ < 2 * Ao := by linarith
  rw [norm_mul, Complex.norm_two] at h2
  linarith

/-! ## The coordinates `l₁₁, l₂₁, l₂₂` -/

private lemma norm_zθ (θ : ℝ) : ‖zθ θ‖ = 1 / 2 := by
  unfold zθ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, norm_half]
  norm_num

private lemma zθ_sq (θ : ℝ) : zθ θ ^ 2 = (1 / 4 : ℂ) * exp ((θ : ℂ) * I) := by
  unfold zθ
  rw [mul_pow, ← Complex.exp_nat_mul]
  have e : ((2 : ℕ) : ℂ) * (((θ / 2 : ℝ) : ℂ) * I) = (θ : ℂ) * I := by push_cast; ring
  rw [e]
  norm_num

private lemma zθ_sq_re (θ : ℝ) : (zθ θ ^ 2).re = Real.cos θ / 4 := by
  rw [zθ_sq, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  norm_num
  ring

private lemma cos_lt_one_of_pos_of_le_pi {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : Real.cos θ < 1 := by
  rcases lt_or_eq_of_le (Real.cos_le_one θ) with h | h
  · exact h
  · exfalso
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h
    linarith

/-- `|Z_o| < A_o` for `θ ∈ (0, π]`. -/
private lemma norm_Zo_lt (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : ‖Zo θ‖ < Ao :=
  norm_cartanh_lt (norm_zθ θ) (by rw [zθ_sq_re]; linarith [cos_lt_one_of_pos_of_le_pi h0 hπ])

theorem sec5_coords_proved (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
      l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2 := by
  have hlt := norm_Zo_lt θ h0 hπ
  have hsq : (Zo θ).re ^ 2 + (Zo θ).im ^ 2 < Ao ^ 2 := by
    have h1 : ‖Zo θ‖ ^ 2 = (Zo θ).re ^ 2 + (Zo θ).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h2 : 0 ≤ ‖Zo θ‖ := norm_nonneg _
    nlinarith
  have hX := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (Zo θ)) hlt)
  have hP : 0 < (Ao + (Zo θ).re) / 2 := by linarith
  have h11pos : 0 < l11 θ := Real.sqrt_pos.mpr hP
  have h11sq : l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 := Real.sq_sqrt hP.le
  have h21 : l11 θ * l21 θ = (Zo θ).im / 2 := by
    unfold l21
    field_simp
  have h21sq : l21 θ ^ 2 = (Zo θ).im ^ 2 / (2 * (Ao + (Zo θ).re)) := by
    unfold l21
    rw [div_pow, h11sq]
    field_simp
  have hrad : 0 < (Ao - (Zo θ).re) / 2 - l21 θ ^ 2 := by
    rw [h21sq, sub_pos, div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨h11pos, Real.sqrt_pos.mpr hrad, h11sq, h21, ?_⟩
  have h22sq : l22 θ ^ 2 = (Ao - (Zo θ).re) / 2 - l21 θ ^ 2 := Real.sq_sqrt hrad.le
  linarith

/-! ## Remark 5.6: `Re Q_rel ≈ -0.0777` at `θ = 60°`

Every numerical fact below is proved from rational bounds: Taylor bounds for `sin`, `cos` and `exp`, the series
of `artanh` with its tail bound, and interval arithmetic. -/

/-! ### Taylor bounds for `sin` and `cos` on `[0, ∞)`: if `f 0 = 0` and `f' ≥ 0` on `[0, ∞)`, then `f ≥ 0` there -/

private lemma nonneg_of_hasDerivAt' {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f 0 = 0)
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

private lemma cos_le_t4 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have key : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x :=
    nonneg_of_hasDerivAt' (f := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s)
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

private lemma sin_le_t5 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have key : 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x :=
    nonneg_of_hasDerivAt' (f := fun s => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s)
      (f' := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s)
      (fun t => ((((hasDerivAt_id' (x := t)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)).congr_deriv
        (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := cos_le_t4 ht
        linarith)
      hx
  linarith

private lemma t6_le_cos {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have key : 0 ≤ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) :=
    nonneg_of_hasDerivAt'
      (f := fun s => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
      (f' := fun s => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s)
      (fun t => ((Real.hasDerivAt_cos t).sub ((((hasDerivAt_const t (1 : ℝ)).sub
        ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).sub
        ((hasDerivAt_pow 6 t).div_const 720))).congr_deriv (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := sin_le_t5 ht
        linarith)
      hx
  linarith

private lemma t7_le_sin {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have key : 0 ≤ Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) :=
    nonneg_of_hasDerivAt'
      (f := fun s => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040))
      (f' := fun s => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
      (fun t => ((Real.hasDerivAt_sin t).sub ((((hasDerivAt_id' (x := t)).sub
        ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 120)).sub
        ((hasDerivAt_pow 7 t).div_const 5040))).congr_deriv (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := t6_le_cos ht
        linarith)
      hx
  linarith

private lemma cos_le_t8 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have key : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x :=
    nonneg_of_hasDerivAt'
      (f := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320 - Real.cos s)
      (f' := fun s => -s + s ^ 3 / 6 - s ^ 5 / 120 + s ^ 7 / 5040 + Real.sin s)
      (fun t => ((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
        ((hasDerivAt_pow 8 t).div_const 40320)).sub (Real.hasDerivAt_cos t)).congr_deriv
        (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := t7_le_sin ht
        linarith)
      hx
  linarith

private lemma sin_le_t9 {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 := by
  have key : 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - Real.sin x :=
    nonneg_of_hasDerivAt'
      (f := fun s => s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880 - Real.sin s)
      (f' := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320 - Real.cos s)
      (fun t => ((((((hasDerivAt_id' (x := t)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
        ((hasDerivAt_pow 9 t).div_const 362880)).sub (Real.hasDerivAt_sin t)).congr_deriv
        (by norm_num; ring))
      (by simp)
      (fun t ht => by
        have := cos_le_t8 ht
        linarith)
      hx
  linarith

/-! ### Small interval tools -/

/-- Rational bounds for `exp x` from the Taylor polynomial with remainder (`|x| ≤ 1`). -/
private lemma exp_mem {x lo hi : ℝ} (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1)
    (hlo : lo ≤ (∑ m ∈ Finset.range n, x ^ m / m.factorial) - |x| ^ n * (n.succ / (n.factorial * n)))
    (hhi : (∑ m ∈ Finset.range n, x ^ m / m.factorial) + |x| ^ n * (n.succ / (n.factorial * n)) ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have h := abs_le.mp (Real.exp_bound hx hn)
  constructor <;> linarith [h.1, h.2]

/-- The product of two nonnegative intervals. -/
private lemma mul_mem {x y a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hax : a ≤ x) (hxb : x ≤ b)
    (hcy : c ≤ y) (hyd : y ≤ d) : a * c ≤ x * y ∧ x * y ≤ b * d :=
  ⟨mul_le_mul hax hcy hc (ha.trans hax), mul_le_mul hxb hyd (hc.trans hcy) (ha.trans (hax.trans hxb))⟩

/-! ### The matrix of Remark 5.6 and the real form of `Q_rel` at a real matrix -/

private lemma rem_symmUnitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    IsSymmUnitary (-!![(c : ℂ), (s : ℂ); (s : ℂ), -(c : ℂ)]) := by
  have hC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hC

private lemma cA_rem (θ c s : ℝ) :
    cA θ (-!![(c : ℂ), (s : ℂ); (s : ℂ), -(c : ℂ)]) = ((-(c * l11 θ ^ 2) : ℝ) : ℂ) := by
  simp [cA, bil, ut, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

private lemma cB_rem (θ c s : ℝ) :
    cB θ (-!![(c : ℂ), (s : ℂ); (s : ℂ), -(c : ℂ)]) =
      ((-(c * l21 θ ^ 2) - 2 * s * l21 θ * l22 θ + c * l22 θ ^ 2 : ℝ) : ℂ) := by
  simp [cB, bil, vt, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

private lemma cC_rem (θ c s : ℝ) :
    cC θ (-!![(c : ℂ), (s : ℂ); (s : ℂ), -(c : ℂ)]) = ((l11 θ * (-(c * l21 θ) - s * l22 θ) : ℝ) : ℂ) := by
  simp [cC, bil, ut, vt, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  left
  ring

/-- At a matrix with real `A, B, C`, `Q_rel = 1 + E cos 4C - E sin 4C (T - T⁻¹)/2` with `E = e^{2(A-B)}` and
`T = tan(θ/4) e^{2(A+B)}` (so `χ = iT`). -/
private lemma Qrel_of_real (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (A B C : ℝ) (hA : cA θ M = A)
    (hB : cB θ M = B) (hC : cC θ M = C) :
    Qrel θ M = ((1 + Real.exp (2 * (A - B)) * Real.cos (4 * C) -
      Real.exp (2 * (A - B)) * Real.sin (4 * C) *
        (Real.tan (θ / 4) * Real.exp (2 * (A + B)) - (Real.tan (θ / 4) * Real.exp (2 * (A + B)))⁻¹) / 2 :
          ℝ) : ℂ) := by
  have e1 : exp (ell1 θ M) =
      (Real.exp (2 * (A - B)) : ℂ) * ((Real.cos (4 * C) : ℂ) + (Real.sin (4 * C) : ℂ) * I) := by
    rw [ell1, hA, hB, hC, show 2 * ((A : ℂ) - B) + 4 * I * C = ((2 * (A - B) : ℝ) : ℂ) + ((4 * C : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have e2 : exp (ell2 θ M) =
      (Real.exp (2 * (A - B)) : ℂ) * ((Real.cos (4 * C) : ℂ) - (Real.sin (4 * C) : ℂ) * I) := by
    rw [ell2, hA, hB, hC, show 2 * ((A : ℂ) - B) - 4 * I * C = ((2 * (A - B) : ℝ) : ℂ) + ((-(4 * C) : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hχ : chi θ M = I * ((Real.tan (θ / 4) * Real.exp (2 * (A + B)) : ℝ) : ℂ) := by
    rw [chi, kappa, hA, hB, show (2 : ℂ) * ((A : ℂ) + B) = ((2 * (A + B) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    push_cast
    ring
  rw [Qrel, e1, e2, hχ]
  generalize Real.tan (θ / 4) * Real.exp (2 * (A + B)) = T
  generalize Real.exp (2 * (A - B)) = E
  generalize Real.cos (4 * C) = k
  generalize Real.sin (4 * C) = w
  rw [mul_inv, Complex.inv_I]
  push_cast
  linear_combination ((E : ℂ) * (w : ℂ) * ((T : ℂ) - (T : ℂ)⁻¹) / 2) * Complex.I_sq

/-! ### The angle `θ = 60°` -/

private lemma deg60 : deg 60 = Real.pi / 3 := by unfold deg; ring

private lemma zθ_deg60 : zθ (deg 60) = ((Real.sqrt 3 : ℝ) + I) / 4 := by
  unfold zθ
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, deg60,
    show Real.pi / 3 / 2 = Real.pi / 6 by ring, Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

private lemma tan_deg60_quarter : Real.tan (deg 60 / 4) = 2 - Real.sqrt 3 := by
  have hx : deg 60 / 4 = Real.pi / 12 := by rw [deg60]; ring
  rw [hx, Real.tan_eq_sin_div_cos]
  have hK : 0 < Real.cos (Real.pi / 12) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h1 : 2 * Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12) = 1 / 2 := by
    rw [← Real.sin_two_mul, show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.sin_pi_div_six]
  have h2 : 2 * Real.cos (Real.pi / 12) ^ 2 = 1 + Real.sqrt 3 / 2 := by
    have := Real.cos_two_mul (Real.pi / 12)
    rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.cos_pi_div_six] at this
    linarith
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [div_eq_iff hK.ne']
  have : (Real.sin (Real.pi / 12) - (2 - Real.sqrt 3) * Real.cos (Real.pi / 12)) * Real.cos (Real.pi / 12) = 0 := by
    linear_combination (1 / 2) * h1 - ((2 - Real.sqrt 3) / 2) * h2 + (1 / 4) * hr
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hK.ne'

/-- The first `20` terms of the series of `2 artanh z` at `z = (√3 + i)/4 = z_{60°}`, using `z³ = i/8`. -/
private lemma partial_sum_z (r : ℝ) (hr : r ^ 2 = 3) :
    ∑ i ∈ Finset.range 20, atTerm (((r : ℂ) + I) / 4) i =
      2 * (((r * (417587764103 / 1695143690240) : ℝ) : ℂ) +
        (((4485370436951 / 15256293212160 : ℝ)) : ℂ) * I) := by
  have hrC : (r : ℂ) ^ 2 = 3 := by exact_mod_cast hr
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((r : ℂ) + I) / 4 := ⟨_, rfl⟩
  rw [← hz]
  have hz3 : z ^ 3 = I / 8 := by
    rw [hz]
    linear_combination ((r + 3 * I) / 64) * hrC + ((3 * r + I) / 64) * Complex.I_sq
  have hz2 : z ^ 2 = (1 + r * I) / 8 := by
    rw [hz]
    linear_combination (1 / 16 : ℂ) * hrC + (1 / 16 : ℂ) * Complex.I_sq
  have hz5 : z ^ 5 = (I - r) / 64 := by
    rw [show z ^ 5 = z ^ 2 * z ^ 3 by ring, hz2, hz3]
    linear_combination ((r : ℂ) / 64) * Complex.I_sq
  have hz6 : z ^ 6 = -1 / 64 := by
    rw [show z ^ 6 = (z ^ 3) ^ 2 by ring, hz3]
    linear_combination (1 / 64 : ℂ) * Complex.I_sq
  have hsum : ∑ i ∈ Finset.range 20, atTerm z i = 2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z * z ^ 6 / 7 +
      z ^ 3 * z ^ 6 / 9 + z ^ 5 * z ^ 6 / 11 + z * (z ^ 6) ^ 2 / 13 + z ^ 3 * (z ^ 6) ^ 2 / 15 +
      z ^ 5 * (z ^ 6) ^ 2 / 17 + z * (z ^ 6) ^ 3 / 19) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, atTerm]
    push_cast
    ring
  rw [hsum, hz6, hz5, hz3, hz]
  push_cast
  ring

private lemma tail20 : (4 * (1 / 2 : ℝ) ^ 20 / ((20 : ℕ) : ℝ)) = 1 / 5242880 := by norm_num

private lemma rem_Ao_bounds : 54930611 / 10 ^ 8 ≤ Ao ∧ Ao ≤ 54930622 / 10 ^ 8 := by
  have h1 := sum_atTermR_le 20
  have h2 := two_Ao_sub_le 20 (by norm_num)
  have hS : ∑ i ∈ Finset.range 20, atTermR i = 4190187576017 / 3814073303040 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, atTermR]
    norm_num
  rw [hS] at h1 h2
  rw [tail20] at h2
  constructor <;> linarith

private lemma sqrt3_bounds : (17320508 / 10 ^ 7 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 17320509 / 10 ^ 7 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

private lemma rem_XY_bounds :
    42667949 / 10 ^ 8 ≤ (Zo (deg 60)).re ∧ (Zo (deg 60)).re ≤ 42667972 / 10 ^ 8 ∧
      29400123 / 10 ^ 8 ≤ (Zo (deg 60)).im ∧ (Zo (deg 60)).im ≤ 29400143 / 10 ^ 8 := by
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨hr1, hr2⟩ := sqrt3_bounds
  have h := norm_two_cartanh_sub_le (norm_zθ (deg 60)) 20
  have h2 := two_Ao_sub_le 20 (by norm_num)
  rw [tail20] at h2
  have hZ : Zo (deg 60) = cartanh ((((Real.sqrt 3 : ℝ) : ℂ) + I) / 4) := by
    unfold Zo
    rw [zθ_deg60]
  rw [zθ_deg60, partial_sum_z _ hr, ← hZ] at h
  have hle := h.trans h2
  have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans hle)
  have him := abs_le.mp ((Complex.abs_im_le_norm _).trans hle)
  have ere : (2 * Zo (deg 60) - 2 * (((Real.sqrt 3 * (417587764103 / 1695143690240) : ℝ) : ℂ) +
      (((4485370436951 / 15256293212160 : ℝ)) : ℂ) * I)).re =
      2 * (Zo (deg 60)).re - 2 * (Real.sqrt 3 * (417587764103 / 1695143690240)) := by simp
  have eim : (2 * Zo (deg 60) - 2 * (((Real.sqrt 3 * (417587764103 / 1695143690240) : ℝ) : ℂ) +
      (((4485370436951 / 15256293212160 : ℝ)) : ℂ) * I)).im =
      2 * (Zo (deg 60)).im - 2 * (4485370436951 / 15256293212160) := by simp
  rw [ere] at hre
  rw [eim] at him
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hre.1, hre.2, him.1, him.2]

private lemma rem_cs_bounds :
    86026846 / 10 ^ 8 ≤ Real.cos 0.535 ∧ Real.cos 0.535 ≤ 86026863 / 10 ^ 8 ∧
      50984102 / 10 ^ 8 ≤ Real.sin 0.535 ∧ Real.sin 0.535 ≤ 50984104 / 10 ^ 8 := by
  have e : (0.535 : ℝ) = 107 / 200 := by norm_num
  rw [e]
  have h0 : (0 : ℝ) ≤ 107 / 200 := by norm_num
  have h1 := t6_le_cos h0
  have h2 := cos_le_t8 h0
  have h3 := t7_le_sin h0
  have h4 := sin_le_t9 h0
  norm_num at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Interval bounds for `A = -c l₁₁²`, `B = -c l₂₁² - 2 s l₂₁ l₂₂ + c l₂₂²`, `C = l₁₁(-c l₂₁ - s l₂₂)` from bounds on
`A_o, Re Z_o, Im Z_o, c, s` and the Gram relations of `l₁₁ = a, l₂₁ = b, l₂₂ = d`. -/
private lemma ABC_bounds {Ao X Y c s a b d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (h11 : a ^ 2 = (Ao + X) / 2) (h21 : a * b = Y / 2) (hsum : b ^ 2 + d ^ 2 = (Ao - X) / 2)
    (hAo1 : 54930611 / 10 ^ 8 ≤ Ao) (hAo2 : Ao ≤ 54930622 / 10 ^ 8)
    (hX1 : 42667949 / 10 ^ 8 ≤ X) (hX2 : X ≤ 42667972 / 10 ^ 8)
    (hY1 : 29400123 / 10 ^ 8 ≤ Y) (hY2 : Y ≤ 29400143 / 10 ^ 8)
    (hc1 : 86026846 / 10 ^ 8 ≤ c) (hc2 : c ≤ 86026863 / 10 ^ 8)
    (hs1 : 50984102 / 10 ^ 8 ≤ s) (hs2 : s ≤ 50984104 / 10 ^ 8) :
    -41980505 / 10 ^ 8 ≤ -(c * a ^ 2) ∧ -(c * a ^ 2) ≤ -41980481 / 10 ^ 8 ∧
      -5144576 / 10 ^ 8 ≤ -(c * b ^ 2) - 2 * s * b * d + c * d ^ 2 ∧
      -(c * b ^ 2) - 2 * s * b * d + c * d ^ 2 ≤ -5144527 / 10 ^ 8 ∧
      -17294046 / 10 ^ 8 ≤ a * (-(c * b) - s * d) ∧ a * (-(c * b) - s * d) ≤ -17294003 / 10 ^ 8 := by
  obtain ⟨m, hm⟩ : ∃ m, m = a * d := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ mul_pos ha hd
  have hmsq : m ^ 2 = (Ao ^ 2 - X ^ 2 - Y ^ 2) / 4 := by
    rw [hm]
    linear_combination a ^ 2 * hsum - (a * b + Y / 2) * h21 + ((Ao - X) / 2) * h11
  have hAosq1 : (54930611 / 10 ^ 8 : ℝ) ^ 2 ≤ Ao ^ 2 := pow_le_pow_left₀ (by norm_num) hAo1 2
  have hAosq2 : Ao ^ 2 ≤ (54930622 / 10 ^ 8 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hAo2 2
  have hXsq1 : (42667949 / 10 ^ 8 : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by norm_num) hX1 2
  have hXsq2 : X ^ 2 ≤ (42667972 / 10 ^ 8 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hX2 2
  have hYsq1 : (29400123 / 10 ^ 8 : ℝ) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (by norm_num) hY1 2
  have hYsq2 : Y ^ 2 ≤ (29400143 / 10 ^ 8 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hY2 2
  have hm1 : (9116575 / 10 ^ 8 : ℝ) ≤ m := by
    have : (9116575 / 10 ^ 8 : ℝ) ^ 2 ≤ m ^ 2 := by rw [hmsq]; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hm0.le (by norm_num)).mp this
  have hm2 : m ≤ 9116635 / 10 ^ 8 := by
    have : m ^ 2 ≤ (9116635 / 10 ^ 8 : ℝ) ^ 2 := by rw [hmsq]; linarith
    exact (pow_le_pow_iff_left₀ hm0.le (by norm_num) (by norm_num)).mp this
  -- `A`
  have hcP := mul_mem (by norm_num) (by norm_num) hc1 hc2 (add_le_add hAo1 hX1) (add_le_add hAo2 hX2)
  have hA : -(c * a ^ 2) = -(c * (Ao + X)) / 2 := by rw [h11]; ring
  -- `C`
  have hC : a * (-(c * b) - s * d) = -(c * Y) / 2 - s * m := by
    rw [hm]
    linear_combination (-c) * h21
  have hcY := mul_mem (by norm_num) (by norm_num) hc1 hc2 hY1 hY2
  have hsm := mul_mem (by norm_num) (by norm_num) hs1 hs2 hm1 hm2
  -- `B`
  have hBP : (-(c * b ^ 2) - 2 * s * b * d + c * d ^ 2) * ((Ao + X) / 2) =
      -(c * Y ^ 2) / 4 - s * Y * m + c * m ^ 2 := by
    rw [← h11, hm]
    linear_combination (-c * (a * b + Y / 2) - 2 * s * a * d) * h21
  have hcY2 := mul_mem (by norm_num) (by positivity) hc1 hc2 hYsq1 hYsq2
  have hsY := mul_mem (by norm_num) (by norm_num) hs1 hs2 hY1 hY2
  have hsYm := mul_mem (by positivity) (by norm_num) hsY.1 hsY.2 hm1 hm2
  have hmsq1 : (9116575 / 10 ^ 8 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm1 2
  have hmsq2 : m ^ 2 ≤ (9116635 / 10 ^ 8 : ℝ) ^ 2 := pow_le_pow_left₀ hm0.le hm2 2
  have hcm2 := mul_mem (by norm_num) (by positivity) hc1 hc2 hmsq1 hmsq2
  have hPpos : 0 < (Ao + X) / 2 := by linarith
  have hBlo : -5144576 / 10 ^ 8 * ((Ao + X) / 2) ≤
      (-(c * b ^ 2) - 2 * s * b * d + c * d ^ 2) * ((Ao + X) / 2) := by
    rw [hBP]
    linarith [hcY2.2, hsYm.2, hcm2.1]
  have hBhi : (-(c * b ^ 2) - 2 * s * b * d + c * d ^ 2) * ((Ao + X) / 2) ≤
      -5144527 / 10 ^ 8 * ((Ao + X) / 2) := by
    rw [hBP]
    linarith [hcY2.1, hsYm.1, hcm2.2]
  refine ⟨?_, ?_, le_of_mul_le_mul_right hBlo hPpos, le_of_mul_le_mul_right hBhi hPpos, ?_, ?_⟩
  · rw [hA]; linarith [hcP.2]
  · rw [hA]; linarith [hcP.1]
  · rw [hC]; linarith [hcY.2, hsm.2]
  · rw [hC]; linarith [hcY.1, hsm.1]

/-- The final interval estimate. With `u = e^{2A}`, `v = e^{-2B}`, `γ = -4C`, the value is
`1 + u v cos γ + sin γ ((2 - √3) u² - (2 + √3) v²)/2`. -/
private lemma final_ineq {A B C r : ℝ} (hr : r ^ 2 = 3) (hr1 : 17320508 / 10 ^ 7 < r)
    (hr2 : r < 17320509 / 10 ^ 7)
    (hA1 : -41980505 / 10 ^ 8 ≤ A) (hA2 : A ≤ -41980481 / 10 ^ 8)
    (hB1 : -5144576 / 10 ^ 8 ≤ B) (hB2 : B ≤ -5144527 / 10 ^ 8)
    (hC1 : -17294046 / 10 ^ 8 ≤ C) (hC2 : C ≤ -17294003 / 10 ^ 8) :
    -0.0785 < 1 + Real.exp (2 * (A - B)) * Real.cos (4 * C) - Real.exp (2 * (A - B)) * Real.sin (4 * C) *
        ((2 - r) * Real.exp (2 * (A + B)) - ((2 - r) * Real.exp (2 * (A + B)))⁻¹) / 2 ∧
      1 + Real.exp (2 * (A - B)) * Real.cos (4 * C) - Real.exp (2 * (A - B)) * Real.sin (4 * C) *
        ((2 - r) * Real.exp (2 * (A + B)) - ((2 - r) * Real.exp (2 * (A + B)))⁻¹) / 2 < -0.0775 := by
  -- bounds on `u = e^{2A}` and `v = e^{-2B}`
  have hu1 : (21593939 / 5 / 10 ^ 7 : ℝ) ≤ Real.exp (2 * A) := by
    have h := (exp_mem (x := -8396101 / 10 ^ 7) (lo := 21593939 / 5 / 10 ^ 7) (hi := 1) 10 (by norm_num)
      (by norm_num [abs_div]) (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])
      (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])).1
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have hu2 : Real.exp (2 * A) ≤ 4318791 / 10 ^ 7 := by
    have h := (exp_mem (x := -41980481 / 5 / 10 ^ 7) (lo := 0) (hi := 4318791 / 10 ^ 7) 10 (by norm_num)
      (by norm_num [abs_div]) (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])
      (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])).2
    exact (Real.exp_le_exp.mpr (by linarith)).trans h
  have hv1 : (6927313 / 625 / 10 ^ 4 : ℝ) ≤ Real.exp (-(2 * B)) := by
    have h := (exp_mem (x := 10289054 / 10 ^ 8) (lo := 6927313 / 625 / 10 ^ 4) (hi := 2) 10 (by norm_num)
      (by norm_num [abs_div]) (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])
      (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])).1
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have hv2 : Real.exp (-(2 * B)) ≤ 110837117 / 10 ^ 8 := by
    have h := (exp_mem (x := 10289152 / 10 ^ 8) (lo := 0) (hi := 110837117 / 10 ^ 8) 10 (by norm_num)
      (by norm_num [abs_div]) (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])
      (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_div])).2
    exact (Real.exp_le_exp.mpr (by linarith)).trans h
  -- bounds on `cos γ` and `sin γ`, `γ = -4C`
  have hpi := Real.pi_gt_three
  have hg1 : (69176012 / 10 ^ 8 : ℝ) ≤ -(4 * C) := by linarith
  have hg2 : -(4 * C) ≤ 69176184 / 10 ^ 8 := by linarith
  have hk2 : Real.cos (-(4 * C)) ≤ 15402489 / 2 / 10 ^ 7 := by
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) hg1
    have h2 := cos_le_t8 (x := 69176012 / 10 ^ 8) (by norm_num)
    norm_num at h2
    linarith
  have hk1 : (19253051 / 25 / 10 ^ 6 : ℝ) ≤ Real.cos (-(4 * C)) := by
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hg2
    have h2 := t6_le_cos (x := 69176184 / 10 ^ 8) (by norm_num)
    norm_num at h2
    linarith
  have hw1 : (31894679 / 5 / 10 ^ 7 : ℝ) ≤ Real.sin (-(4 * C)) := by
    have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hg1
    have h2 := t7_le_sin (x := 69176012 / 10 ^ 8) (by norm_num)
    norm_num at h2
    linarith
  have hw2 : Real.sin (-(4 * C)) ≤ 63789501 / 10 ^ 8 := by
    have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hg2
    have h2 := sin_le_t9 (x := 69176184 / 10 ^ 8) (by norm_num)
    norm_num at h2
    linarith
  -- the algebra
  have hE : Real.exp (2 * (A - B)) = Real.exp (2 * A) * Real.exp (-(2 * B)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hT : Real.exp (2 * (A + B)) = Real.exp (2 * A) * (Real.exp (-(2 * B)))⁻¹ := by
    rw [Real.exp_neg, inv_inv, ← Real.exp_add]; congr 1; ring
  have h2r : (2 - r)⁻¹ = 2 + r := inv_eq_of_mul_eq_one_right (by linear_combination -hr)
  have hcos : Real.cos (4 * C) = Real.cos (-(4 * C)) := (Real.cos_neg _).symm
  have hsin : Real.sin (4 * C) = -Real.sin (-(4 * C)) := by rw [Real.sin_neg, neg_neg]
  rw [hE, hT, hcos, hsin]
  have hu0 : 0 < Real.exp (2 * A) := Real.exp_pos _
  have hv0 : 0 < Real.exp (-(2 * B)) := Real.exp_pos _
  generalize Real.exp (2 * A) = u at hu1 hu2 hu0 ⊢
  generalize Real.exp (-(2 * B)) = v at hv1 hv2 hv0 ⊢
  generalize Real.cos (-(4 * C)) = k at hk1 hk2 ⊢
  generalize Real.sin (-(4 * C)) = w at hw1 hw2 ⊢
  have key : 1 + u * v * k - u * v * -w * ((2 - r) * (u * v⁻¹) - ((2 - r) * (u * v⁻¹))⁻¹) / 2 =
      1 + u * v * k + w * ((2 - r) * u ^ 2 - (2 + r) * v ^ 2) / 2 := by
    rw [mul_inv, mul_inv, inv_inv, h2r]
    field_simp
    ring
  rw [key]
  have huv := mul_mem (by norm_num) (by norm_num) hu1 hu2 hv1 hv2
  have huvk := mul_mem (by norm_num) (by norm_num) huv.1 huv.2 hk1 hk2
  have hu2sq := mul_mem (by norm_num) (by norm_num) hu1 hu2 hu1 hu2
  have hv2sq := mul_mem (by norm_num) (by norm_num) hv1 hv2 hv1 hv2
  have hru := mul_mem (x := 2 - r) (a := 2 - 17320509 / 10 ^ 7) (b := 2 - 17320508 / 10 ^ 7)
    (by norm_num) (by norm_num) (by linarith) (by linarith) hu2sq.1 hu2sq.2
  have hrv := mul_mem (x := 2 + r) (a := 2 + 17320508 / 10 ^ 7) (b := 2 + 17320509 / 10 ^ 7)
    (by norm_num) (by norm_num) (by linarith) (by linarith) hv2sq.1 hv2sq.2
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw1
  set bh : ℝ := (2 - 17320508 / 10 ^ 7) * (4318791 / 10 ^ 7 * (4318791 / 10 ^ 7)) -
    (2 + 17320508 / 10 ^ 7) * (6927313 / 625 / 10 ^ 4 * (6927313 / 625 / 10 ^ 4)) with hbh
  set bl : ℝ := (2 - 17320509 / 10 ^ 7) * (21593939 / 5 / 10 ^ 7 * (21593939 / 5 / 10 ^ 7)) -
    (2 + 17320509 / 10 ^ 7) * (110837117 / 10 ^ 8 * (110837117 / 10 ^ 8)) with hbl
  have hbr_hi : (2 - r) * u ^ 2 - (2 + r) * v ^ 2 ≤ bh := by
    rw [hbh, sq, sq]; linarith [hru.2, hrv.1]
  have hbr_lo : bl ≤ (2 - r) * u ^ 2 - (2 + r) * v ^ 2 := by
    rw [hbl, sq, sq]; linarith [hru.1, hrv.2]
  have hbh0 : bh ≤ 0 := by rw [hbh]; norm_num
  have hbl0 : bl ≤ 0 := by rw [hbl]; norm_num
  have hwhi : w * ((2 - r) * u ^ 2 - (2 + r) * v ^ 2) ≤ 31894679 / 5 / 10 ^ 7 * bh :=
    (mul_le_mul_of_nonneg_left hbr_hi hw0).trans (mul_le_mul_of_nonpos_right hw1 hbh0)
  have hwlo : 63789501 / 10 ^ 8 * bl ≤ w * ((2 - r) * u ^ 2 - (2 + r) * v ^ 2) :=
    (mul_le_mul_of_nonpos_right hw2 hbl0).trans (mul_le_mul_of_nonneg_left hbr_lo hw0)
  have e1 : (-0.0785 : ℝ) = -785 / 10000 := by norm_num
  have e2 : (-0.0775 : ℝ) = -775 / 10000 := by norm_num
  rw [e1, e2, hbh] at *
  rw [hbl] at hwlo
  constructor
  · linarith [huvk.1]
  · linarith [huvk.2]

theorem rem_5_6_proved :
    IsSymmUnitary (-!![(Real.cos 0.535 : ℂ), (Real.sin 0.535 : ℂ); (Real.sin 0.535 : ℂ), -(Real.cos 0.535 : ℂ)]) ∧
      -0.0785 < (Qrel (deg 60)
        (-!![(Real.cos 0.535 : ℂ), (Real.sin 0.535 : ℂ); (Real.sin 0.535 : ℂ), -(Real.cos 0.535 : ℂ)])).re ∧
      (Qrel (deg 60)
        (-!![(Real.cos 0.535 : ℂ), (Real.sin 0.535 : ℂ); (Real.sin 0.535 : ℂ), -(Real.cos 0.535 : ℂ)])).re < -0.0775 := by
  have hθ0 : 0 < deg 60 := by rw [deg60]; positivity
  have hθπ : deg 60 ≤ Real.pi := by rw [deg60]; linarith [Real.pi_pos]
  obtain ⟨h11pos, h22pos, h11, h21, hsum⟩ := sec5_coords_proved (deg 60) hθ0 hθπ
  obtain ⟨hAo1, hAo2⟩ := rem_Ao_bounds
  obtain ⟨hX1, hX2, hY1, hY2⟩ := rem_XY_bounds
  obtain ⟨hc1, hc2, hs1, hs2⟩ := rem_cs_bounds
  obtain ⟨hA1, hA2, hB1, hB2, hC1, hC2⟩ :=
    ABC_bounds h11pos h22pos h11 h21 hsum hAo1 hAo2 hX1 hX2 hY1 hY2 hc1 hc2 hs1 hs2
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨hr1, hr2⟩ := sqrt3_bounds
  refine ⟨rem_symmUnitary _ _ (Real.cos_sq_add_sin_sq _), ?_⟩
  rw [Qrel_of_real _ _ _ _ _ (cA_rem _ _ _) (cB_rem _ _ _) (cC_rem _ _ _), Complex.ofReal_re,
    tan_deg60_quarter]
  exact final_ineq hr hr1 hr2 hA1 hA2 hB1 hB2 hC1 hC2

end Robinson.Proofs
