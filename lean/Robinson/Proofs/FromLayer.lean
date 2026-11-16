/-
Robinson/Proofs/FromLayer.lean — proofs of cor_5_5, prop_6_1_from_layer, prop_7_1_from_layer.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Matrix2
import Robinson.Defs.Grunsky
import Robinson.Proofs.Takagi
import Robinson.Proofs.Chart
import Robinson.Proofs.Sec7Hol

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## Corollary 5.5 -/

/-- Corollary 5.5: the minimum of `Re Φ` over `𝓑` is attained at a symmetric unitary `M₀` (Proposition 5.2), and by
the conjugation symmetry `Re Φ(M₀)` is a value of `Re Φ` on the half chart `𝓧` (Lemma 5.4), hence positive. -/
theorem cor_5_5_proved (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (hhol : HolomorphicNearBall Φ)
    (hsym : ∀ M, InBall M → Φ (mconj M) = conj (Φ M)) (hpos : ∀ α ψ ω : ℝ, InX α ψ ω → 0 < (Φ (chart α ψ ω)).re) :
    ∀ M : Matrix (Fin 2) (Fin 2) ℂ, InBall M → 0 < (Φ M).re := by
  obtain ⟨M₀, -, hU, hmin⟩ := prop_5_2_proved Φ hhol
  have hmem : (Φ M₀).re ∈ {x : ℝ | ∃ M : Matrix (Fin 2) (Fin 2) ℂ, IsSymmUnitary M ∧ x = (Φ M).re} :=
    ⟨M₀, hU, rfl⟩
  rw [lem_5_4_proved Φ hsym] at hmem
  obtain ⟨α, ψ, ω, hX, hx⟩ := hmem
  have h0 : 0 < (Φ M₀).re := by rw [hx]; exact hpos α ψ ω hX
  intro M hM
  exact lt_of_lt_of_le h0 (hmin M hM)

/-! ## Proposition 6.1 from (eq:psum) and the bound on `R_f` -/

/-- `Re w ≥ Re(p + q) - |w - p - q|`. -/
private lemma re_ge_sub_norm (w p q : ℂ) : (p + q).re - ‖w - p - q‖ ≤ w.re := by
  have h := neg_abs_le (w - p - q).re
  have h' := Complex.abs_re_le_norm (w - p - q)
  have e : (w - p - q).re = w.re - (p + q).re := by simp only [sub_re, add_re]; ring
  rw [e] at h h'
  linarith

theorem prop_6_1_from_layer_proved
    (hpsum : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      277 / 400 < (pfun f (zθ θ) + pfun f (conj (zθ θ))).re)
    (hR : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      ‖Q f (zθ θ) (conj (zθ θ)) - pfun f (zθ θ) - pfun f (conj (zθ θ))‖ < 173 / 250) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 → 1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re := by
  intro f hf θ h1 h2
  have hp := hpsum f hf θ h1 h2
  have hr := hR f hf θ h1 h2
  have hle := re_ge_sub_norm (Q f (zθ θ) (conj (zθ θ))) (pfun f (zθ θ)) (pfun f (conj (zθ θ)))
  linarith

/-! ## `Q_rel` is entire in the entries of `M` and has the conjugation symmetry -/

private lemma tan_quarter_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < Real.tan (θ / 4) := by
  apply Real.tan_pos_of_pos_of_lt_pi_div_two
  · linarith
  · linarith [Real.pi_pos]

private lemma chi_ne_zero {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    chi θ M ≠ 0 := by
  have ht : (Real.tan (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast (tan_quarter_pos h0 hπ).ne'
  unfold chi
  exact mul_ne_zero (mul_ne_zero I_ne_zero ht) (Complex.exp_ne_zero _)

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

/-- For `θ ∈ (0, π]`, `χ` never vanishes, so `Q_rel` is entire in the entries `(a, b, d)` of `M`. -/
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

private lemma holNear_Qrel {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : HolomorphicNearBall (Qrel θ) :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, (diff_Qrel h0 hπ).differentiableOn⟩

private lemma ut_eq (θ : ℝ) : ut θ = fun i => ((![l11 θ, 0] : Fin 2 → ℝ) i : ℂ) := by
  funext i; fin_cases i <;> simp [ut]

private lemma vt_eq (θ : ℝ) : vt θ = fun i => ((![l21 θ, l22 θ] : Fin 2 → ℝ) i : ℂ) := by
  funext i; fin_cases i <;> simp [vt]

/-- For real vectors `x, y`, `xᵀ M̄ y = \overline{xᵀ M y}`. -/
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

/-- `ℓ₁(M̄) = \overline{ℓ₂(M)}`. -/
private lemma ell1_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ell1 θ (mconj M) = conj (ell2 θ M) := by
  rw [ell1, ell2, cA_mconj, cB_mconj, cC_mconj]
  simp only [map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

/-- `ℓ₂(M̄) = \overline{ℓ₁(M)}`. -/
private lemma ell2_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ell2 θ (mconj M) = conj (ell1 θ M) := by
  rw [ell1, ell2, cA_mconj, cB_mconj, cC_mconj]
  simp only [map_add, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

/-- `χ(M̄) = -\overline{χ(M)}`. -/
private lemma chi_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : chi θ (mconj M) = -conj (chi θ M) := by
  have hk : kappa θ (mconj M) = conj (kappa θ M) := by
    rw [kappa, kappa, cA_mconj, cB_mconj, map_add]
  rw [chi, chi, hk, show (2 : ℂ) * conj (kappa θ M) = conj (2 * kappa θ M) by
    rw [map_mul, map_ofNat], Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `Q_rel(M̄) = \overline{Q_rel(M)}` (for every `θ` and every `M`). -/
private lemma Qrel_mconj (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Qrel θ (mconj M) = conj (Qrel θ M) := by
  rw [Qrel, Qrel, ell1_mconj, ell2_mconj, chi_mconj, Complex.exp_conj, Complex.exp_conj]
  simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_one, map_ofNat, inv_neg]
  ring

/-! ## Proposition 7.1 from the layer -/

/-- An angle `θ` (radians) is `deg (θ · 180/π)`. -/
private lemma deg_toDeg (θ : ℝ) : deg (θ * 180 / Real.pi) = θ := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold deg
  field_simp

/-- `x° ≤ θ ↔ x ≤ θ · 180/π`. -/
private lemma deg_le_iff (x θ : ℝ) : deg x ≤ θ ↔ x ≤ θ * 180 / Real.pi := by
  rw [le_div_iff₀ Real.pi_pos, deg, div_le_iff₀ (by norm_num : (0 : ℝ) < 180)]

/-- `θ ≤ x° ↔ θ · 180/π ≤ x`. -/
private lemma le_deg_iff (x θ : ℝ) : θ ≤ deg x ↔ θ * 180 / Real.pi ≤ x := by
  rw [div_le_iff₀ Real.pi_pos, deg, le_div_iff₀ (by norm_num : (0 : ℝ) < 180)]

/-- On `[50.3°, 90°]`: `Re F > 0` on `𝓑` by Corollary 5.5 (with `Φ_F > 0` on `𝓧`). -/
private lemma ReF_pos_on_ball (hs : ∀ θ : ℝ, 50.3 ≤ θ → θ ≤ 90 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω)
    (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (h1 : deg 50.3 ≤ θ) (h2 : θ ≤ deg 90)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : InBall M) : 0 < (Ffun θ M).re := by
  have hF := prop_7_5_i_proved θ h0 hπ
  refine cor_5_5_proved (Ffun θ) hF.1 hF.2 (fun α ψ ω hX => ?_) M hM
  have h := hs (θ * 180 / Real.pi) ((deg_le_iff _ _).mp h1) ((le_deg_iff _ _).mp h2) α ψ ω hX
  rwa [PhiS, deg_toDeg] at h

/-- On `[90°, 135°]`: `Re Q_rel > 0` on `𝓑` by Corollary 5.5 (with `Φ_rel > 0` on `𝓧`). -/
private lemma ReQrel_pos_on_ball (hp : ∀ θ : ℝ, 90 ≤ θ → θ ≤ 135 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω)
    (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (h1 : deg 90 ≤ θ) (h2 : θ ≤ deg 135)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : InBall M) : 0 < (Qrel θ M).re := by
  refine cor_5_5_proved (Qrel θ) (holNear_Qrel h0 hπ) (fun M _ => Qrel_mconj θ M) (fun α ψ ω hX => ?_) M hM
  have h := hp (θ * 180 / Real.pi) ((deg_le_iff _ _).mp h1) ((le_deg_iff _ _).mp h2) α ψ ω hX
  rwa [PhiP, deg_toDeg] at h

theorem prop_7_1_from_layer_proved
    (hrep : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → ∃ M, InBall M ∧
      Q f (zθ θ) (conj (zθ θ)) = Qrel θ M ∧ (Ffun θ M).re ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hs : ∀ θ : ℝ, 50.3 ≤ θ → θ ≤ 90 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω)
    (hp : ∀ θ : ℝ, 90 ≤ θ → θ ≤ 135 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 → 0 < (Q f (zθ θ) (conj (zθ θ))).re := by
  intro f hf θ h1 h2
  have h0 : 0 < θ := by
    refine lt_of_lt_of_le ?_ h1
    unfold deg
    positivity
  have hπ : θ ≤ Real.pi := by
    refine h2.trans ?_
    unfold deg
    linarith [Real.pi_pos]
  obtain ⟨M, hM, hQ, hFQ⟩ := hrep f hf θ h0 hπ
  rcases le_total θ (deg 90) with h90 | h90
  · exact lt_of_lt_of_le (ReF_pos_on_ball hs θ h0 hπ h1 h90 M hM) hFQ
  · rw [hQ]
    exact ReQrel_pos_on_ball hp θ h0 hπ h90 h2 M hM

end Robinson.Proofs
