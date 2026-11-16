/-
Robinson/Proofs/Sec5G.lean — proofs of sec5_O2_entries, prop_5_1, sec5_O2_contraction, sec5_relaxation,
sec5_not_all_from_S.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Matrix2
import Robinson.Defs.Grunsky
import Robinson.NotFormalized
import Robinson.ComputerChecked
import Robinson.Proofs.Chart

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The point `s = s_θ` -/

/-- `‖s_θ‖ = 2^{-1/2}`. -/
private lemma s5g_norm_sθ (θ : ℝ) : ‖sθ θ‖ = (Real.sqrt 2)⁻¹ := by
  unfold sθ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

private lemma s5g_sqrt2_inv_lt_one : (Real.sqrt 2)⁻¹ < 1 := by
  have h : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact inv_lt_one_of_one_lt₀ h

private lemma s5g_sθ_mem_ball (θ : ℝ) : sθ θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, s5g_norm_sθ]
  exact s5g_sqrt2_inv_lt_one

private lemma s5g_conj_sθ_mem_ball (θ : ℝ) : conj (sθ θ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_conj, s5g_norm_sθ]
  exact s5g_sqrt2_inv_lt_one

/-! ### The vectors `u`, `v`, `V₀`, `V₁` -/

private lemma s5g_aOdd_eq_zero (s : ℂ) {n : ℕ} (hn : n % 2 ≠ 1) : aOdd s n = 0 := by
  simp [aOdd, hn]

private lemma s5g_Vcol_zero (θ : ℝ) (n : ℕ) : Vcol θ 0 n = uvec θ n / l11 θ := by
  simp [Vcol]

private lemma s5g_Vcol_one (θ : ℝ) (n : ℕ) :
    Vcol θ 1 n = (vvec θ n - l21 θ * (uvec θ n / l11 θ)) / l22 θ := by
  simp [Vcol]

/-- `V₀`, `V₁` vanish at the even indices. -/
private lemma s5g_Vcol_even (θ : ℝ) (i : Fin 2) {n : ℕ} (hn : n % 2 ≠ 1) : Vcol θ i n = 0 := by
  have hu : uvec θ n = 0 := by simp [uvec, s5g_aOdd_eq_zero _ hn]
  have hv : vvec θ n = 0 := by simp [vvec, s5g_aOdd_eq_zero _ hn]
  fin_cases i
  · simp [s5g_Vcol_zero, hu]
  · simp [s5g_Vcol_one, hu, hv]

/-- `u = l₁₁ V₀`. -/
private lemma s5g_u_eq (θ : ℝ) (h11 : l11 θ ≠ 0) (n : ℕ) : uvec θ n = l11 θ * Vcol θ 0 n := by
  rw [s5g_Vcol_zero]
  field_simp

/-- `v = l₂₁ V₀ + l₂₂ V₁`. -/
private lemma s5g_v_eq (θ : ℝ) (h11 : l11 θ ≠ 0) (h22 : l22 θ ≠ 0) (n : ℕ) :
    vvec θ n = l21 θ * Vcol θ 0 n + l22 θ * Vcol θ 1 n := by
  rw [s5g_Vcol_zero, s5g_Vcol_one]
  field_simp
  ring

/-! ### Absolute summability of the bilinear forms -/

/-- `a(s)ₙ O_{nm} a(s)ₘ` is the odd part of the Grunsky double series. -/
private lemma s5g_aOdd_O_aOdd (γ : ℕ → ℕ → ℂ) (s : ℂ) (n m : ℕ) :
    aOdd s n * Oblock γ n m * aOdd s m =
      if n % 2 = 1 ∧ m % 2 = 1 then γ n m * s ^ n * s ^ m else 0 := by
  by_cases hn : n % 2 = 1
  · by_cases hm : m % 2 = 1
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
      have hsn : (Real.sqrt n : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hn0).ne'
      have hsm : (Real.sqrt m : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hm0).ne'
      simp only [aOdd, Oblock, Cmat, hn, hm, and_self, if_true]
      rw [Real.sqrt_mul hn0.le, Complex.ofReal_mul]
      field_simp
    · simp [aOdd, Oblock, hm]
  · simp [aOdd, Oblock, hn]

/-- A sequence dominated by a constant multiple of `‖a(s)‖`. -/
private def S5gDom (s : ℂ) (x : ℕ → ℂ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖x n‖ ≤ K * ‖aOdd s n‖

private lemma s5g_summable_F {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) {s : ℂ}
    (hs : s ∈ ball (0 : ℂ) 1) {x y : ℕ → ℂ} (hx : S5gDom s x) (hy : S5gDom s y) :
    Summable (fun p : ℕ × ℕ => x p.1 * Oblock γ p.1 p.2 * y p.2) := by
  obtain ⟨K, hK0, hK⟩ := hx
  obtain ⟨L, hL0, hL⟩ := hy
  have hsum := ((hγ.2 s s hs hs).1).mul_left (K * L)
  refine Summable.of_norm_bounded hsum (fun p => ?_)
  have h1 : ‖x p.1 * Oblock γ p.1 p.2 * y p.2‖ ≤
      (K * ‖aOdd s p.1‖) * ‖Oblock γ p.1 p.2‖ * (L * ‖aOdd s p.2‖) := by
    rw [norm_mul, norm_mul]
    have hK1 : 0 ≤ K * ‖aOdd s p.1‖ := (norm_nonneg _).trans (hK p.1)
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hK p.1) (norm_nonneg _)) (hL p.2) (norm_nonneg _)
      (mul_nonneg hK1 (norm_nonneg _))
  have h2 : ‖aOdd s p.1‖ * ‖Oblock γ p.1 p.2‖ * ‖aOdd s p.2‖ ≤ ‖γ p.1 p.2 * s ^ p.1 * s ^ p.2‖ := by
    rw [← norm_mul, ← norm_mul, s5g_aOdd_O_aOdd]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  calc ‖x p.1 * Oblock γ p.1 p.2 * y p.2‖ ≤ _ := h1
    _ = K * L * (‖aOdd s p.1‖ * ‖Oblock γ p.1 p.2‖ * ‖aOdd s p.2‖) := by ring
    _ ≤ K * L * ‖γ p.1 p.2 * s ^ p.1 * s ^ p.2‖ := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 hL0)

/-- The iterated sums of `bilinf` are the sum over `ℕ x ℕ` of an absolutely summable family. -/
private lemma s5g_bilinf_eq_tsum (x : ℕ → ℂ) (A : ℕ → ℕ → ℂ) (y : ℕ → ℂ)
    (h : Summable (fun p : ℕ × ℕ => x p.1 * A p.1 p.2 * y p.2)) :
    bilinf x A y = ∑' p : ℕ × ℕ, x p.1 * A p.1 p.2 * y p.2 := by
  rw [h.tsum_prod]
  unfold bilinf
  congr 1
  funext n
  rw [← tsum_mul_left]
  congr 1
  funext m
  ring

/-- Bilinearity of `bilinf` on combinations of two vectors with summable mutual forms. -/
private lemma s5g_bilinf_comb {γ : ℕ → ℕ → ℂ} {E0 E1 x y : ℕ → ℂ}
    (h00 : Summable (fun p : ℕ × ℕ => E0 p.1 * Oblock γ p.1 p.2 * E0 p.2))
    (h01 : Summable (fun p : ℕ × ℕ => E0 p.1 * Oblock γ p.1 p.2 * E1 p.2))
    (h10 : Summable (fun p : ℕ × ℕ => E1 p.1 * Oblock γ p.1 p.2 * E0 p.2))
    (h11 : Summable (fun p : ℕ × ℕ => E1 p.1 * Oblock γ p.1 p.2 * E1 p.2))
    (c0 c1 d0 d1 : ℂ) (hx : ∀ n, x n = c0 * E0 n + c1 * E1 n) (hy : ∀ n, y n = d0 * E0 n + d1 * E1 n) :
    bilinf x (Oblock γ) y =
      c0 * d0 * bilinf E0 (Oblock γ) E0 + c0 * d1 * bilinf E0 (Oblock γ) E1 +
        c1 * d0 * bilinf E1 (Oblock γ) E0 + c1 * d1 * bilinf E1 (Oblock γ) E1 := by
  have H := (((h00.hasSum.mul_left (c0 * d0)).add (h01.hasSum.mul_left (c0 * d1))).add
    (h10.hasSum.mul_left (c1 * d0))).add (h11.hasSum.mul_left (c1 * d1))
  have hxy : (fun p : ℕ × ℕ => x p.1 * Oblock γ p.1 p.2 * y p.2) =
      fun p => c0 * d0 * (E0 p.1 * Oblock γ p.1 p.2 * E0 p.2) + c0 * d1 * (E0 p.1 * Oblock γ p.1 p.2 * E1 p.2) +
        c1 * d0 * (E1 p.1 * Oblock γ p.1 p.2 * E0 p.2) + c1 * d1 * (E1 p.1 * Oblock γ p.1 p.2 * E1 p.2) := by
    funext p
    rw [hx, hy]
    ring
  have hs : Summable (fun p : ℕ × ℕ => x p.1 * Oblock γ p.1 p.2 * y p.2) := by
    rw [hxy]
    exact H.summable
  rw [s5g_bilinf_eq_tsum _ _ _ h00, s5g_bilinf_eq_tsum _ _ _ h01, s5g_bilinf_eq_tsum _ _ _ h10,
    s5g_bilinf_eq_tsum _ _ _ h11, s5g_bilinf_eq_tsum _ _ _ hs, hxy]
  exact H.tsum_eq

/-- `V₀` is dominated by `‖a(s_θ)‖`. -/
private lemma s5g_dom_V0 (θ : ℝ) : S5gDom (sθ θ) (fun n => (Vcol θ 0 n : ℂ)) := by
  refine ⟨|l11 θ|⁻¹, by positivity, fun n => ?_⟩
  have hu : |uvec θ n| ≤ ‖aOdd (sθ θ) n‖ := Complex.abs_re_le_norm _
  rw [Complex.norm_real, Real.norm_eq_abs, s5g_Vcol_zero, abs_div, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_left hu (inv_nonneg.2 (abs_nonneg _))

/-- `V₁` is dominated by `‖a(s_θ)‖`. -/
private lemma s5g_dom_V1 (θ : ℝ) : S5gDom (sθ θ) (fun n => (Vcol θ 1 n : ℂ)) := by
  refine ⟨(1 + |l21 θ| * |l11 θ|⁻¹) * |l22 θ|⁻¹, by positivity, fun n => ?_⟩
  have hu : |uvec θ n| ≤ ‖aOdd (sθ θ) n‖ := Complex.abs_re_le_norm _
  have hv : |vvec θ n| ≤ ‖aOdd (sθ θ) n‖ := Complex.abs_im_le_norm _
  rw [Complex.norm_real, Real.norm_eq_abs, s5g_Vcol_one, abs_div]
  have h1 : |vvec θ n - l21 θ * (uvec θ n / l11 θ)| ≤ (1 + |l21 θ| * |l11 θ|⁻¹) * ‖aOdd (sθ θ) n‖ := by
    calc |vvec θ n - l21 θ * (uvec θ n / l11 θ)| ≤ |vvec θ n| + |l21 θ * (uvec θ n / l11 θ)| :=
          abs_sub _ _
      _ = |vvec θ n| + |l21 θ| * (|uvec θ n| * |l11 θ|⁻¹) := by
          rw [abs_mul, abs_div, div_eq_mul_inv]
      _ ≤ ‖aOdd (sθ θ) n‖ + |l21 θ| * (‖aOdd (sθ θ) n‖ * |l11 θ|⁻¹) := by
          gcongr
      _ = (1 + |l21 θ| * |l11 θ|⁻¹) * ‖aOdd (sθ θ) n‖ := by ring
  calc |vvec θ n - l21 θ * (uvec θ n / l11 θ)| / |l22 θ|
      ≤ (1 + |l21 θ| * |l11 θ|⁻¹) * ‖aOdd (sθ θ) n‖ / |l22 θ| := by gcongr
    _ = (1 + |l21 θ| * |l11 θ|⁻¹) * |l22 θ|⁻¹ * ‖aOdd (sθ θ) n‖ := by ring

/-- `V₀` and `V₁` are dominated by `‖a(s_θ)‖`. -/
private lemma s5g_dom_V (θ : ℝ) (i : Fin 2) : S5gDom (sθ θ) (fun n => (Vcol θ i n : ℂ)) := by
  fin_cases i
  · exact s5g_dom_V0 θ
  · exact s5g_dom_V1 θ

/-- The mutual forms of `V₀`, `V₁` are absolutely summable. -/
private lemma s5g_summable_VV {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) (θ : ℝ) (i j : Fin 2) :
    Summable (fun p : ℕ × ℕ => (Vcol θ i p.1 : ℂ) * Oblock γ p.1 p.2 * (Vcol θ j p.2 : ℂ)) :=
  s5g_summable_F (x := fun n => (Vcol θ i n : ℂ)) (y := fun n => (Vcol θ j n : ℂ)) hγ (s5g_sθ_mem_ball θ)
    (s5g_dom_V θ i) (s5g_dom_V θ j)

/-- `xᵀ M y` for `2`-vectors, written out. -/
private lemma s5g_bil_two (c d : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    bil c M d = c 0 * d 0 * M 0 0 + c 0 * d 1 * M 0 1 + c 1 * d 0 * M 1 0 + c 1 * d 1 * M 1 1 := by
  simp only [bil, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The entries of `O₂` are the forms of `O` on `V₀`, `V₁`. -/
private lemma s5g_O2_apply (γ : ℕ → ℕ → ℂ) (θ : ℝ) (i j : Fin 2) :
    O2 γ θ i j = bilinf (fun n => (Vcol θ i n : ℂ)) (Oblock γ) (fun n => (Vcol θ j n : ℂ)) := rfl

/-- The bilinear form of `O` on two combinations of `V₀`, `V₁` is the form of `O₂` on the coefficients. -/
private lemma s5g_bilinf_V {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) (θ : ℝ) {x y : ℕ → ℂ}
    (c0 c1 d0 d1 : ℂ) (hx : ∀ n, x n = c0 * (Vcol θ 0 n : ℂ) + c1 * (Vcol θ 1 n : ℂ))
    (hy : ∀ n, y n = d0 * (Vcol θ 0 n : ℂ) + d1 * (Vcol θ 1 n : ℂ)) :
    bilinf x (Oblock γ) y =
      c0 * d0 * O2 γ θ 0 0 + c0 * d1 * O2 γ θ 0 1 + c1 * d0 * O2 γ θ 1 0 + c1 * d1 * O2 γ θ 1 1 := by
  rw [s5g_O2_apply, s5g_O2_apply, s5g_O2_apply, s5g_O2_apply]
  exact s5g_bilinf_comb (E0 := fun n => (Vcol θ 0 n : ℂ)) (E1 := fun n => (Vcol θ 1 n : ℂ))
    (s5g_summable_VV hγ θ 0 0) (s5g_summable_VV hγ θ 0 1) (s5g_summable_VV hγ θ 1 0)
    (s5g_summable_VV hγ θ 1 1) c0 c1 d0 d1 hx hy

/-! ### `sec5_O2_entries` -/

private lemma s5g_O2_entries_core {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) (θ : ℝ)
    (h11 : l11 θ ≠ 0) (h22 : l22 θ ≠ 0) :
    bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ) ∧
      bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ) ∧
      bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ) := by
  have hu : ∀ n, (uvec θ n : ℂ) = (l11 θ : ℂ) * (Vcol θ 0 n : ℂ) + 0 * (Vcol θ 1 n : ℂ) := by
    intro n
    rw [s5g_u_eq θ h11 n]
    push_cast
    ring
  have hv : ∀ n, (vvec θ n : ℂ) = (l21 θ : ℂ) * (Vcol θ 0 n : ℂ) + (l22 θ : ℂ) * (Vcol θ 1 n : ℂ) := by
    intro n
    rw [s5g_v_eq θ h11 h22 n]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [s5g_bilinf_V hγ θ _ _ _ _ hu hu, cA, s5g_bil_two]
    simp [ut]
  · rw [s5g_bilinf_V hγ θ _ _ _ _ hv hv, cB, s5g_bil_two]
    simp [vt]
  · rw [s5g_bilinf_V hγ θ _ _ _ _ hu hv, cC, s5g_bil_two]
    simp [ut, vt]

/-! ### The odd root is in `𝒮`; the Grunsky coefficients of `h` are symmetric -/

private lemma s5g_sq_mem_ball {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) : s ^ 2 ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hs ⊢
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hs two_ne_zero

private lemma s5g_neg_mem_ball {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) : -s ∈ ball (0 : ℂ) 1 := by
  rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]

/-- The odd square root `h` of `f ∈ 𝒮` is in `𝒮`. -/
private lemma s5g_oddroot_mem_S {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) : InS h := by
  have h0 : h 0 = 0 := by
    have e := hh.2.1 0 (mem_ball_self one_pos)
    rw [neg_zero] at e
    linear_combination e / 2
  refine ⟨hh.1, ?_, h0, hh.2.2.2⟩
  intro a ha b hb hab
  have hab2 : a ^ 2 = b ^ 2 := by
    apply hf.injOn (s5g_sq_mem_ball ha) (s5g_sq_mem_ball hb)
    rw [← hh.2.2.1 a ha, ← hh.2.2.1 b hb, hab]
  have hfac : (a - b) * (a + b) = 0 := by linear_combination hab2
  rcases mul_eq_zero.1 hfac with e | e
  · linear_combination e
  · have hba : a = -b := by linear_combination e
    have hha : h a = 0 := by
      have e2 := hh.2.1 b hb
      rw [← hba] at e2
      linear_combination (e2 + hab) / 2
    have ha0 : a = 0 := by
      have e3 : f (a ^ 2) = f 0 := by
        rw [← hh.2.2.1 a ha, hha, hf.map_zero]
        ring
      exact (pow_eq_zero_iff two_ne_zero).1 (hf.injOn (s5g_sq_mem_ball ha) (mem_ball_self one_pos) e3)
    rw [ha0] at hba ⊢
    linear_combination -hba

/-- The kernel quotient is symmetric in `s` and `t`. -/
private lemma s5g_kernelQuot_symm (g : ℂ → ℂ) (s t : ℂ) : kernelQuot g s t = kernelQuot g t s := by
  unfold kernelQuot
  by_cases hst : s = t
  · subst hst
    rfl
  · rw [if_neg hst, if_neg (Ne.symm hst)]
    have e : (g s - g t) / (s - t) = (g t - g s) / (t - s) := by
      rw [← neg_sub (g t), ← neg_sub t, neg_div_neg_eq]
    rw [e]
    ring

/-- If `γ` are Grunsky coefficients of `g`, so are the transposed coefficients. -/
private lemma s5g_isGrunsky_swap {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) :
    IsGrunskyCoeff g (fun n m => γ m n) := by
  refine ⟨fun n m hnm => hγ.1 m n hnm.symm, fun s t hs ht => ?_⟩
  obtain ⟨hsum, hexp⟩ := hγ.2 t s ht hs
  refine ⟨?_, ?_⟩
  · have e : (fun nm : ℕ × ℕ => ‖γ nm.2 nm.1 * s ^ nm.1 * t ^ nm.2‖) =
        fun nm => (fun q : ℕ × ℕ => ‖γ q.1 q.2 * t ^ q.1 * s ^ q.2‖) ((Equiv.prodComm ℕ ℕ) nm) := by
      funext nm
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      ring_nf
    rw [e]
    exact (Equiv.prodComm ℕ ℕ).summable_iff.2 hsum
  · have hk : kser (fun n m => γ m n) s t = kser γ t s := by
      unfold kser
      rw [← (Equiv.prodComm ℕ ℕ).tsum_eq (fun q : ℕ × ℕ => γ q.1 q.2 * t ^ q.1 * s ^ q.2)]
      congr 1
      funext nm
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      ring
    rw [hk, hexp, s5g_kernelQuot_symm]

/-- By uniqueness, the Grunsky coefficients of the odd root are symmetric. -/
private lemma s5g_symm_of_unique
    (hunique : ∀ (g : ℂ → ℂ) (hg : InS g) (γ γ' : ℕ → ℕ → ℂ) (h : IsGrunskyCoeff g γ)
      (h' : IsGrunskyCoeff g γ'), γ = γ')
    {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ) :
    ∀ n m, γ n m = γ m n := by
  have e := hunique h (s5g_oddroot_mem_S hf hh) γ _ hγ (s5g_isGrunsky_swap hγ)
  intro n m
  exact congrFun (congrFun e n) m

private lemma s5g_Oblock_symm {γ : ℕ → ℕ → ℂ} (hsym : ∀ n m, γ n m = γ m n) (n m : ℕ) :
    Oblock γ n m = Oblock γ m n := by
  unfold Oblock Cmat
  rw [hsym n m, mul_comm (n : ℝ) (m : ℝ)]
  by_cases hn : n % 2 = 1 <;> by_cases hm : m % 2 = 1 <;> simp [hn, hm]

/-- `O₂` is complex symmetric when `γ` is symmetric. -/
private lemma s5g_O2_symm {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ)
    (hsym : ∀ n m, γ n m = γ m n) (θ : ℝ) (i j : Fin 2) : O2 γ θ j i = O2 γ θ i j := by
  rw [s5g_O2_apply, s5g_O2_apply,
    s5g_bilinf_eq_tsum (fun n => (Vcol θ j n : ℂ)) (Oblock γ) (fun n => (Vcol θ i n : ℂ))
      (s5g_summable_VV hγ θ j i),
    s5g_bilinf_eq_tsum (fun n => (Vcol θ i n : ℂ)) (Oblock γ) (fun n => (Vcol θ j n : ℂ))
      (s5g_summable_VV hγ θ i j)]
  refine Eq.trans ((Equiv.prodComm ℕ ℕ).tsum_eq _).symm ?_
  congr 1
  funext q
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [s5g_Oblock_symm hsym]
  ring

/-! ### `V` has orthonormal columns; `O₂` is a contraction -/

private lemma s5g_orthonormal (θ : ℝ)
    (hg : HasSum (fun n => uvec θ n ^ 2) ((Ao + (Zo θ).re) / 2) ∧
      HasSum (fun n => vvec θ n ^ 2) ((Ao - (Zo θ).re) / 2) ∧
      HasSum (fun n => uvec θ n * vvec θ n) ((Zo θ).im / 2))
    (hc : 0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
      l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2) :
    ∀ i j : Fin 2, HasSum (fun n => Vcol θ i n * Vcol θ j n) (if i = j then 1 else 0) := by
  obtain ⟨huu, hvv, huv⟩ := hg
  obtain ⟨h11, h22, e11, e21, e22⟩ := hc
  have h11' := h11.ne'
  have h22' := h22.ne'
  have H00 : HasSum (fun n => Vcol θ 0 n * Vcol θ 0 n) 1 := by
    have H := huu.mul_left (1 / l11 θ ^ 2)
    convert H using 1
    · funext n
      rw [s5g_Vcol_zero]
      field_simp
    · rw [← e11]
      field_simp
  have H01 : HasSum (fun n => Vcol θ 0 n * Vcol θ 1 n) 0 := by
    have H := (huv.mul_left (1 / (l11 θ * l22 θ))).sub (huu.mul_left (l21 θ / (l11 θ ^ 2 * l22 θ)))
    convert H using 1
    · funext n
      rw [s5g_Vcol_zero, s5g_Vcol_one]
      field_simp
    · rw [← e11, ← e21]
      field_simp
      ring
  have H11 : HasSum (fun n => Vcol θ 1 n * Vcol θ 1 n) 1 := by
    have H := ((hvv.mul_left (1 / l22 θ ^ 2)).sub (huv.mul_left (2 * l21 θ / (l11 θ * l22 θ ^ 2)))).add
      (huu.mul_left (l21 θ ^ 2 / (l11 θ ^ 2 * l22 θ ^ 2)))
    convert H using 1
    · funext n
      rw [s5g_Vcol_one]
      field_simp
      ring
    · rw [← e11, ← e21, ← e22]
      field_simp
      ring
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using H00
  · simpa using H01
  · simpa [mul_comm] using H01
  · simpa using H11

/-- The form of `C(h)` on `V₀`, `V₁` is the form of `O` (they vanish at the even indices). -/
private lemma s5g_bilinf_Cmat (γ : ℕ → ℕ → ℂ) (θ : ℝ) (i j : Fin 2) :
    bilinf (fun n => (Vcol θ i n : ℂ)) (Cmat γ) (fun n => (Vcol θ j n : ℂ)) = O2 γ θ i j := by
  rw [s5g_O2_apply]
  unfold bilinf
  congr 1
  funext n
  by_cases hn : n % 2 = 1
  · congr 1
    congr 1
    funext m
    by_cases hm : m % 2 = 1
    · simp [Oblock, hn, hm]
    · simp [s5g_Vcol_even θ j hm]
  · simp [s5g_Vcol_even θ i hn]

/-- A `2 x 2` matrix whose bilinear form is bounded by `‖x‖ ‖y‖` has operator norm at most `1`. -/
private lemma s5g_opNorm_le_one (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ x y : Fin 2 → ℂ, ‖∑ i, ∑ j, x i * M i j * y j‖ ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2)) :
    opNorm M ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul]
  set T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M with hT
  have hTv : ∀ i, T v i = ∑ j, M i j * v j := by
    intro i
    show (WithLp.ofLp (T v)) i = _
    rw [hT, Matrix.ofLp_toEuclideanCLM]
    simp [Matrix.mulVec, dotProduct]
  have key := hM (fun i => conj (T v i)) (fun j => v j)
  beta_reduce at key
  have hsum : ∑ i, ∑ j, conj (T v i) * M i j * v j = ((∑ i, ‖T v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.conj_mul', hTv i, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at key
  simp only [Complex.norm_conj] at key
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  have hW : 0 ≤ ∑ i, ‖T v i‖ ^ 2 := by positivity
  rw [abs_of_nonneg hW] at key
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (∑ i, ‖T v i‖ ^ 2)) with e | e
  · rw [← e]
    exact Real.sqrt_nonneg _
  · have h2 : Real.sqrt (∑ i, ‖T v i‖ ^ 2) * Real.sqrt (∑ i, ‖T v i‖ ^ 2) ≤
        Real.sqrt (∑ i, ‖T v i‖ ^ 2) * Real.sqrt (∑ j, ‖v j‖ ^ 2) := by
      rw [Real.mul_self_sqrt hW]
      exact key
    exact le_of_mul_le_mul_left h2 e

/-- `O₂ ∈ 𝓑`, from the symmetry of `γ`, the orthonormality of `V` and the compression bound. -/
private lemma s5g_inBall_O2 {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ)
    (hsym : ∀ n m, γ n m = γ m n) (θ : ℝ)
    (hON : ∀ i j : Fin 2, HasSum (fun n => Vcol θ i n * Vcol θ j n) (if i = j then 1 else 0))
    (hcomp : ∀ (k : ℕ) (V : ℕ → Fin k → ℂ),
      (∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) →
      ∀ x y : Fin k → ℂ, ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) * y j‖ ≤
        Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2)) :
    InBall (O2 γ θ) := by
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.transpose_apply]
    exact s5g_O2_symm hγ hsym θ i j
  · apply s5g_opNorm_le_one
    intro x y
    have hON' : ∀ i j : Fin 2,
        HasSum (fun n => conj ((Vcol θ i n : ℂ)) * (Vcol θ j n : ℂ)) (if i = j then 1 else 0) := by
      intro i j
      have H := (Complex.hasSum_ofReal).2 (hON i j)
      convert H using 1
      · funext n
        simp
      · split_ifs <;> simp
    have H := hcomp 2 (fun n i => (Vcol θ i n : ℂ)) hON' x y
    simpa only [s5g_bilinf_Cmat] using H

/-! ### Proposition 5.1 -/

private lemma s5g_aOdd_conj (s : ℂ) (n : ℕ) : aOdd (conj s) n = conj (aOdd s n) := by
  unfold aOdd
  split_ifs
  · simp [map_div₀, map_pow, Complex.conj_ofReal]
  · simp

/-- `a(s) = (l₁₁ + i l₂₁) V₀ + i l₂₂ V₁`. -/
private lemma s5g_as_eq (θ : ℝ) (h11 : l11 θ ≠ 0) (h22 : l22 θ ≠ 0) (n : ℕ) :
    aOdd (sθ θ) n = ((l11 θ : ℂ) + I * l21 θ) * (Vcol θ 0 n : ℂ) + (I * l22 θ) * (Vcol θ 1 n : ℂ) := by
  have e : aOdd (sθ θ) n = (uvec θ n : ℂ) + (vvec θ n : ℂ) * I := (Complex.re_add_im _).symm
  rw [e, s5g_u_eq θ h11 n, s5g_v_eq θ h11 h22 n]
  push_cast
  ring

/-- `a(s̄) = (l₁₁ - i l₂₁) V₀ - i l₂₂ V₁`. -/
private lemma s5g_at_eq (θ : ℝ) (h11 : l11 θ ≠ 0) (h22 : l22 θ ≠ 0) (n : ℕ) :
    aOdd (conj (sθ θ)) n =
      ((l11 θ : ℂ) - I * l21 θ) * (Vcol θ 0 n : ℂ) + (-(I * l22 θ)) * (Vcol θ 1 n : ℂ) := by
  have e : aOdd (sθ θ) n = (uvec θ n : ℂ) + (vvec θ n : ℂ) * I := (Complex.re_add_im _).symm
  rw [s5g_aOdd_conj, e, s5g_u_eq θ h11 n, s5g_v_eq θ h11 h22 n]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma s5g_ut0 (θ : ℝ) : ut θ 0 = (l11 θ : ℂ) := rfl
private lemma s5g_ut1 (θ : ℝ) : ut θ 1 = 0 := rfl
private lemma s5g_vt0 (θ : ℝ) : vt θ 0 = (l21 θ : ℂ) := rfl
private lemma s5g_vt1 (θ : ℝ) : vt θ 1 = (l22 θ : ℂ) := rfl

private lemma s5g_cA (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : cA θ M = (l11 θ : ℂ) ^ 2 * M 0 0 := by
  rw [cA, s5g_bil_two, s5g_ut0, s5g_ut1]
  ring

private lemma s5g_cB (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    cB θ M = (l21 θ : ℂ) ^ 2 * M 0 0 + (l21 θ : ℂ) * l22 θ * M 0 1 + (l22 θ : ℂ) * l21 θ * M 1 0 +
      (l22 θ : ℂ) ^ 2 * M 1 1 := by
  rw [cB, s5g_bil_two, s5g_vt0, s5g_vt1]
  ring

private lemma s5g_cC (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    cC θ M = (l11 θ : ℂ) * l21 θ * M 0 0 + (l11 θ : ℂ) * l22 θ * M 0 1 := by
  rw [cC, s5g_bil_two, s5g_ut0, s5g_ut1, s5g_vt0, s5g_vt1]
  ring

private lemma s5g_sθ_eq (θ : ℝ) :
    sθ θ = ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.cos (θ / 4) : ℂ) + (Real.sin (θ / 4) : ℂ) * I) := by
  unfold sθ
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma s5g_conj_sθ_eq (θ : ℝ) :
    conj (sθ θ) = ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.cos (θ / 4) : ℂ) - (Real.sin (θ / 4) : ℂ) * I) := by
  rw [s5g_sθ_eq]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma s5g_sθ_sq (θ : ℝ) : sθ θ ^ 2 = zθ θ := by
  unfold sθ zθ
  rw [mul_pow, ← Complex.exp_nat_mul]
  have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring
  rw [h2]
  congr 2
  push_cast
  ring

/-- With `s = s_θ`, `t = s̄`: `s ≠ 0`, `t ≠ 0`, `s ≠ t`, `s ≠ -t` and `(s - t)/(s + t) = i tan(θ/4)`. -/
private lemma s5g_s_facts (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    sθ θ ≠ 0 ∧ conj (sθ θ) ≠ 0 ∧ sθ θ ≠ conj (sθ θ) ∧ sθ θ ≠ -conj (sθ θ) ∧
      (sθ θ - conj (sθ θ)) / (sθ θ + conj (sθ θ)) = I * (Real.tan (θ / 4) : ℂ) := by
  have hc : (Real.cos (θ / 4) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).ne'
  have hsn : (Real.sin (θ / 4) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hr : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (Real.sqrt 2)⁻¹ ≠ 0)
  have hsub : sθ θ - conj (sθ θ) = 2 * ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sin (θ / 4) : ℂ) * I := by
    rw [s5g_conj_sθ_eq, s5g_sθ_eq]
    ring
  have hadd : sθ θ + conj (sθ θ) = 2 * ((Real.sqrt 2)⁻¹ : ℝ) * (Real.cos (θ / 4) : ℂ) := by
    rw [s5g_conj_sθ_eq, s5g_sθ_eq]
    ring
  have hsub0 : sθ θ - conj (sθ θ) ≠ 0 := by
    rw [hsub]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hr) hsn) I_ne_zero
  have hadd0 : sθ θ + conj (sθ θ) ≠ 0 := by
    rw [hadd]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hr) hc
  have hs0 : sθ θ ≠ 0 := by
    apply norm_ne_zero_iff.1
    rw [s5g_norm_sθ]
    positivity
  refine ⟨hs0, (map_ne_zero _).2 hs0, sub_ne_zero.1 hsub0, ?_, ?_⟩
  · intro e
    apply hadd0
    linear_combination e
  · rw [hsub, hadd, Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    field_simp

private lemma s5g_deriv_f_sq {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1) : deriv f (x ^ 2) * (2 * x) = 2 * h x * deriv h x := by
  have hx2 := s5g_sq_mem_ball hx
  have hfd : DifferentiableAt ℂ f (x ^ 2) :=
    hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hx2)
  have hhd : DifferentiableAt ℂ h x := hh.1.differentiableAt (isOpen_ball.mem_nhds hx)
  have H1 : HasDerivAt (fun y => f (y ^ 2)) (deriv f (x ^ 2) * (2 * x)) x := by
    have H := hfd.hasDerivAt.comp x (hasDerivAt_pow 2 x)
    simpa [Function.comp_def] using H
  have H2 : HasDerivAt (fun y => h y ^ 2) (2 * h x * deriv h x) x := by
    have H := (hasDerivAt_pow 2 (h x)).comp x hhd.hasDerivAt
    simpa [Function.comp_def] using H
  have heq : (fun y => f (y ^ 2)) =ᶠ[𝓝 x] (fun y => h y ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (hh.2.2.1 y hy).symm
  exact ((H2.congr_of_eventuallyEq heq).unique H1).symm

/-- `p(x²) = exp(2 a(x)ᵀ O a(x))` for `x ≠ 0` in `𝔻`, from Lemma 3.1(i) at `t = x`. -/
private lemma s5g_pfun_sq
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1) (hx0 : x ≠ 0) :
    pfun f (x ^ 2) = exp (2 * bilinf (aOdd x) (Oblock γ) (aOdd x)) := by
  have hInS := s5g_oddroot_mem_S hf hh
  have hhx : h x ≠ 0 := by
    intro e
    exact hx0 (hInS.injOn hx (mem_ball_self one_pos) (e.trans hInS.map_zero.symm))
  have hxx : x ≠ -x := by
    intro e
    apply hx0
    linear_combination e / 2
  have h2x : x + x ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero hx0
  have h2h : h x + h x ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero hhx
  have hdf : deriv f (x ^ 2) = h x * deriv h x / x := by
    field_simp
    linear_combination s5g_deriv_f_sq hf hh hx / 2
  rw [(h31i f h hf hh γ hγ x x hx hx).1, Complex.exp_sub, (hγ.2 x x hx hx).2,
    (hγ.2 x (-x) hx (s5g_neg_mem_ball hx)).2]
  simp only [kernelQuot, if_true, if_neg hx0, if_neg hxx, if_neg (neg_ne_zero.2 hx0)]
  rw [hh.2.1 x hx, pfun, if_neg (pow_ne_zero 2 hx0), hdf, ← hh.2.2.1 x hx, sub_neg_eq_add, sub_neg_eq_add,
    neg_div_neg_eq]
  field_simp

private lemma s5g_final_algebra (a b p q : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (hab' : a + b ≠ 0) :
    1 + (p * a ^ 2 - q * b ^ 2) / (a ^ 2 - b ^ 2) =
      1 + (p + q) / 2 + (p - q) * ((a - b) / (a + b) + ((a - b) / (a + b))⁻¹) / 4 := by
  rw [inv_div]
  have h2 : a ^ 2 - b ^ 2 ≠ 0 := by
    have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [e]
    exact mul_ne_zero hab hab'
  field_simp
  ring

/-- Proposition 5.1 for symmetric Grunsky coefficients and `l₁₁, l₂₂ ≠ 0`. -/
private lemma s5g_prop_5_1_core
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ)
    (hsym : ∀ n m, γ n m = γ m n) {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (h11 : l11 θ ≠ 0)
    (h22 : l22 θ ≠ 0) :
    Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ) := by
  obtain ⟨hs0, ht0, hst, hst', htan⟩ := s5g_s_facts θ h0 hπ
  have hs := s5g_sθ_mem_ball θ
  have ht := s5g_conj_sθ_mem_ball θ
  have hInS := s5g_oddroot_mem_S hf hh
  have hhs : h (sθ θ) ≠ 0 := by
    intro e
    exact hs0 (hInS.injOn hs (mem_ball_self one_pos) (e.trans hInS.map_zero.symm))
  have hht : h (conj (sθ θ)) ≠ 0 := by
    intro e
    exact ht0 (hInS.injOn ht (mem_ball_self one_pos) (e.trans hInS.map_zero.symm))
  have hhst : h (sθ θ) - h (conj (sθ θ)) ≠ 0 := sub_ne_zero.2 (fun e => hst (hInS.injOn hs ht e))
  have hhst' : h (sθ θ) + h (conj (sθ θ)) ≠ 0 := by
    intro e
    have e2 : h (sθ θ) = h (-conj (sθ θ)) := by
      rw [hh.2.1 _ ht]
      linear_combination e
    exact hst' (hInS.injOn hs (s5g_neg_mem_ball ht) e2)
  have hM : O2 γ θ 1 0 = O2 γ θ 0 1 := s5g_O2_symm hγ hsym θ 0 1
  have Bss := s5g_bilinf_V hγ θ _ _ _ _ (s5g_as_eq θ h11 h22) (s5g_as_eq θ h11 h22)
  have Btt := s5g_bilinf_V hγ θ _ _ _ _ (s5g_at_eq θ h11 h22) (s5g_at_eq θ h11 h22)
  have Bst := s5g_bilinf_V hγ θ _ _ _ _ (s5g_as_eq θ h11 h22) (s5g_at_eq θ h11 h22)
  have e1 : ell1 θ (O2 γ θ) = 2 * bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ)) := by
    rw [Bss, ell1, s5g_cA, s5g_cB, s5g_cC, hM]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have e2 : ell2 θ (O2 γ θ) = 2 * bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ))) := by
    rw [Btt, ell2, s5g_cA, s5g_cB, s5g_cC, hM]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have ek : 2 * kappa θ (O2 γ θ) = 2 * bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (conj (sθ θ))) := by
    rw [Bst, kappa, s5g_cA, s5g_cB, hM]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hp : pfun f (sθ θ ^ 2) = exp (ell1 θ (O2 γ θ)) := by
    rw [e1]
    exact s5g_pfun_sq h31i hf hh hγ hs hs0
  have hq : pfun f (conj (sθ θ) ^ 2) = exp (ell2 θ (O2 γ θ)) := by
    rw [e2]
    exact s5g_pfun_sq h31i hf hh hγ ht ht0
  have hchi : chi θ (O2 γ θ) = (h (sθ θ) - h (conj (sθ θ))) / (h (sθ θ) + h (conj (sθ θ))) := by
    unfold chi
    rw [ek, (h31i f h hf hh γ hγ _ _ hs ht).2 hst hst', ← htan]
    have hsub0 : sθ θ - conj (sθ θ) ≠ 0 := sub_ne_zero.2 hst
    have hadd0 : sθ θ + conj (sθ θ) ≠ 0 := by
      intro e
      apply hst'
      linear_combination e
    field_simp
  have hzd : sθ θ ^ 2 * deriv f (sθ θ ^ 2) = exp (ell1 θ (O2 γ θ)) * h (sθ θ) ^ 2 := by
    rw [← hp, pfun, if_neg (pow_ne_zero 2 hs0), ← hh.2.2.1 _ hs]
    field_simp
  have hwd : conj (sθ θ) ^ 2 * deriv f (conj (sθ θ) ^ 2) =
      exp (ell2 θ (O2 γ θ)) * h (conj (sθ θ)) ^ 2 := by
    rw [← hq, pfun, if_neg (pow_ne_zero 2 ht0), ← hh.2.2.1 _ ht]
    field_simp
  have hw : conj (zθ θ) = conj (sθ θ) ^ 2 := by rw [← s5g_sθ_sq θ, map_pow]
  have hz : zθ θ = sθ θ ^ 2 := (s5g_sθ_sq θ).symm
  rw [hw, hz]
  unfold Q Qrel
  rw [hzd, hwd, ← hh.2.2.1 _ hs, ← hh.2.2.1 _ ht, hchi]
  exact s5g_final_algebra _ _ _ _ hhs hht hhst hhst'

/-! ### Remark 5.6's matrix -/

private lemma s5g_inBall_of_symmUnitary {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsSymmUnitary M) : InBall M := by
  refine ⟨hM.1, ?_⟩
  have hU : M ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact hM.2)
  have hU' := Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) hU
  have h := CStarRing.norm_mem_unitary_mul
    (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) hU'
  rw [mul_one] at h
  unfold opNorm
  rw [h, ContinuousLinearMap.one_def]
  exact ContinuousLinearMap.norm_id_le

/-- `M(α, π/2, π/2) = -[[cos α, sin α], [sin α, -cos α]]`. -/
private lemma s5g_chart_eq (α : ℝ) :
    chart α (Real.pi / 2) (Real.pi / 2) =
      -!![(Real.cos α : ℂ), (Real.sin α : ℂ); (Real.sin α : ℂ), -(Real.cos α : ℂ)] := by
  have e1 : exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    exact Complex.exp_pi_div_two_mul_I
  have e2 : exp (-(((Real.pi / 2 : ℝ) : ℂ) * I)) = -I := by
    rw [Complex.exp_neg, e1, Complex.inv_I]
  unfold chart
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply]; try (ring_nf; simp only [Complex.I_sq]; ring_nf))

/-! ### The rows -/

/-- sec_05_grunsky_q.tex:17, CONDITIONAL on the row `sec5_coords` (which gives `l₁₁ > 0`, `l₂₂ > 0`). -/
theorem sec5_O2_entries_proved_from
    (hcoords : ∀ (θ : ℝ), 0 < θ → θ ≤ Real.pi →
      0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
        l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2)
    (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ) ∧
      bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ) ∧
      bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ) :=
  s5g_O2_entries_core hγ θ (hcoords θ h0 hπ).1.ne' (hcoords θ h0 hπ).2.1.ne'

/-- Proposition 5.1 (sec_05_grunsky_q.tex:35-37), assuming the statements of `lem_3_1_i`, `sec3_grunsky_unique`
and `sec5_coords`. -/
theorem prop_5_1_proved_from
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    (hunique : ∀ (g : ℂ → ℂ) (hg : InS g) (γ γ' : ℕ → ℕ → ℂ) (h : IsGrunskyCoeff g γ)
      (h' : IsGrunskyCoeff g γ'), γ = γ')
    (hcoords : ∀ (θ : ℝ), 0 < θ → θ ≤ Real.pi →
      0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
        l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2)
    (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ) :=
  s5g_prop_5_1_core h31i hf hh hγ (s5g_symm_of_unique hunique hf hh hγ) h0 hπ (hcoords θ h0 hπ).1.ne'
    (hcoords θ h0 hπ).2.1.ne'

open Classical in
/-- sec_05_grunsky_q.tex:13-17 (`V` orthonormal, `u = V ũ`, `v = V ṽ`, `O₂ ∈ 𝓑`), assuming the statements of
`sec3_grunsky_unique`, `sec3_blocks_compressions`, `sec5_uv_gram` and `sec5_coords`. -/
theorem sec5_O2_contraction_proved_from
    (hunique : ∀ (g : ℂ → ℂ) (hg : InS g) (γ γ' : ℕ → ℕ → ℂ) (h : IsGrunskyCoeff g γ)
      (h' : IsGrunskyCoeff g γ'), γ = γ')
    (hblocks : ∀ (hG : FactGrunsky) (g : ℂ → ℂ) (hg : InS g) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff g γ),
      (∀ (S : Set ℕ) (x y : ℕ → ℂ), Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
        ‖bilinf x (fun n m => if n ∈ S ∧ m ∈ S then Cmat γ n m else 0) y‖ ≤
          Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2)) ∧
      ∀ (k : ℕ) (V : ℕ → Fin k → ℂ),
        (∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) →
        ∀ x y : Fin k → ℂ, ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) * y j‖ ≤
          Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2))
    (huv : ∀ (θ : ℝ), 0 < θ → θ ≤ Real.pi →
      HasSum (fun n => uvec θ n ^ 2) ((Ao + (Zo θ).re) / 2) ∧ HasSum (fun n => vvec θ n ^ 2) ((Ao - (Zo θ).re) / 2) ∧
        HasSum (fun n => uvec θ n * vvec θ n) ((Zo θ).im / 2))
    (hcoords : ∀ (θ : ℝ), 0 < θ → θ ≤ Real.pi →
      0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
        l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2)
    (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (∀ i j : Fin 2, HasSum (fun n => Vcol θ i n * Vcol θ j n) (if i = j then 1 else 0)) ∧
      (∀ n, uvec θ n = l11 θ * Vcol θ 0 n) ∧ (∀ n, vvec θ n = l21 θ * Vcol θ 0 n + l22 θ * Vcol θ 1 n) ∧
      InBall (O2 γ θ) := by
  have hc := hcoords θ h0 hπ
  have hON := s5g_orthonormal θ (huv θ h0 hπ) hc
  exact ⟨hON, s5g_u_eq θ hc.1.ne', s5g_v_eq θ hc.1.ne' hc.2.1.ne',
    s5g_inBall_O2 hγ (s5g_symm_of_unique hunique hf hh hγ) θ hON
      (hblocks hG h (s5g_oddroot_mem_S hf hh) γ hγ).2⟩

open Classical in
/-- sec_05_grunsky_q.tex:54 (the relaxation), assuming the statements of `sec3_oddroot_exists`,
`sec3_grunsky_exists`, `lem_3_1_i`, `sec3_blocks_compressions`, `sec5_uv_gram` and `sec5_coords`. -/
theorem sec5_relaxation_proved_from
    (hodd : ∀ (f : ℂ → ℂ) (hf : InS f), ∃ h : ℂ → ℂ, IsOddRoot f h)
    (hexists : ∀ (hB : FactBidiscPowerSeries) (g : ℂ → ℂ) (hg : InS g),
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    (hblocks : ∀ (hG : FactGrunsky) (g : ℂ → ℂ) (hg : InS g) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff g γ),
      (∀ (S : Set ℕ) (x y : ℕ → ℂ), Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
        ‖bilinf x (fun n m => if n ∈ S ∧ m ∈ S then Cmat γ n m else 0) y‖ ≤
          Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2)) ∧
      ∀ (k : ℕ) (V : ℕ → Fin k → ℂ),
        (∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) →
        ∀ x y : Fin k → ℂ, ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) * y j‖ ≤
          Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2))
    (huv : ∀ (θ : ℝ), 0 < θ → θ ≤ Real.pi →
      HasSum (fun n => uvec θ n ^ 2) ((Ao + (Zo θ).re) / 2) ∧ HasSum (fun n => vvec θ n ^ 2) ((Ao - (Zo θ).re) / 2) ∧
        HasSum (fun n => uvec θ n * vvec θ n) ((Zo θ).im / 2))
    (hcoords : ∀ (θ : ℝ), 0 < θ → θ ≤ Real.pi →
      0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
        l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2)
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi)
    (hpos : ∀ M, InBall M → 0 < (Qrel θ M).re) : ∀ f : ℂ → ℂ, InS f → 0 < (Q f (zθ θ) (conj (zθ θ))).re := by
  intro f hf
  obtain ⟨h, hh⟩ := hodd f hf
  have hInS := s5g_oddroot_mem_S hf hh
  obtain ⟨γ, hγ, hsym⟩ := hexists hB h hInS
  have hc := hcoords θ h0 hπ
  have hON := s5g_orthonormal θ (huv θ h0 hπ) hc
  rw [s5g_prop_5_1_core h31i hf hh hγ hsym h0 hπ hc.1.ne' hc.2.1.ne']
  exact hpos _ (s5g_inBall_O2 hγ hsym θ hON (hblocks hG h hInS γ hγ).2)

/-- sec_05_grunsky_q.tex:54 ("not every `M ∈ 𝓑` comes from a univalent function", at `θ = 60°`), assuming the
statements of `rem_5_6`, `prop_7_5_ii`, `lem_3_1_i`, `sec3_grunsky_unique` and `sec5_coords`. -/
theorem sec5_not_all_from_S_proved_from
    (hrem : IsSymmUnitary (!![-(Real.cos 0.535 : ℂ), -(Real.sin 0.535 : ℂ); -(Real.sin 0.535 : ℂ), (Real.cos 0.535 : ℂ)]) ∧
      -0.0785 < (Qrel (deg 60)
        (!![-(Real.cos 0.535 : ℂ), -(Real.sin 0.535 : ℂ); -(Real.sin 0.535 : ℂ), (Real.cos 0.535 : ℂ)])).re ∧
      (Qrel (deg 60)
        (!![-(Real.cos 0.535 : ℂ), -(Real.sin 0.535 : ℂ); -(Real.sin 0.535 : ℂ), (Real.cos 0.535 : ℂ)])).re < -0.0775)
    (h755 : ∀ (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
      (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi),
      (Ffun θ (O2 γ θ)).re ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    (hunique : ∀ (g : ℂ → ℂ) (hg : InS g) (γ γ' : ℕ → ℕ → ℂ) (h : IsGrunskyCoeff g γ)
      (h' : IsGrunskyCoeff g γ'), γ = γ')
    (hcoords : ∀ (θ : ℝ), 0 < θ → θ ≤ Real.pi →
      0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
        l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2)
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h2 : Check_7_6_band02) :
    ∃ M, InBall M ∧ ∀ f h : ℂ → ℂ, InS f → IsOddRoot f h → ∀ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff h γ →
      O2 γ (deg 60) ≠ M := by
  have hM : (-!![(Real.cos 0.535 : ℂ), (Real.sin 0.535 : ℂ); (Real.sin 0.535 : ℂ), -(Real.cos 0.535 : ℂ)]) =
      !![-(Real.cos 0.535 : ℂ), -(Real.sin 0.535 : ℂ); -(Real.sin 0.535 : ℂ), (Real.cos 0.535 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [← hM] at hrem
  refine ⟨_, s5g_inBall_of_symmUnitary hrem.1, ?_⟩
  intro f h hf hh γ hγ hO2
  have h60 : 0 < deg 60 := by
    unfold deg
    positivity
  have h60' : deg 60 ≤ Real.pi := by
    unfold deg
    linarith [Real.pi_pos]
  have hc := hcoords (deg 60) h60 h60'
  have hQ := s5g_prop_5_1_core h31i hf hh hγ (s5g_symm_of_unique hunique hf hh hγ) h60 h60' hc.1.ne'
    hc.2.1.ne'
  have hF := h755 hB hG f h hf hh γ hγ (deg 60) h60 h60'
  have hX : InX 0.535 (Real.pi / 2) (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three], by linarith [Real.pi_pos], le_rfl,
      by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hband := h2 60 (by norm_num) le_rfl 0.535 (Real.pi / 2) (Real.pi / 2) hX
  rw [PhiS, s5g_chart_eq] at hband
  rw [hO2] at hQ hF
  rw [hQ] at hF
  linarith [hrem.2.2]

end Robinson.Proofs
