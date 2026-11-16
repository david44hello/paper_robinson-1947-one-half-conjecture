/-
Robinson/Proofs/Takagi.lean — proofs of sec5_takagi_2x2 and prop_5_2.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Matrix2

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Elementary algebra -/

/-- A unimodular `u` with `ū² c = |c|`. -/
private lemma exists_phase (c : ℂ) : ∃ u : ℂ, u * conj u = 1 ∧ conj u ^ 2 * c = (‖c‖ : ℂ) := by
  set t : ℂ := ((arg c / 2 : ℝ) : ℂ) * I with ht
  have hconj : conj (exp t) = exp (-t) := by
    rw [← exp_conj]
    congr 1
    rw [ht, map_mul, conj_ofReal, conj_I]
    ring
  refine ⟨exp t, ?_, ?_⟩
  · rw [hconj, ← exp_add, add_neg_cancel, exp_zero]
  · calc conj (exp t) ^ 2 * c = exp (-t) ^ 2 * ((‖c‖ : ℂ) * exp (arg c * I)) := by
          rw [hconj, norm_mul_exp_arg_mul_I]
      _ = (‖c‖ : ℂ) * (exp (-t) * exp (-t) * exp (arg c * I)) := by ring
      _ = (‖c‖ : ℂ) * exp (-t + -t + arg c * I) := by rw [← exp_add, ← exp_add]
      _ = (‖c‖ : ℂ) := by
          rw [show -t + -t + (arg c : ℂ) * I = 0 by rw [ht]; push_cast; ring, exp_zero, mul_one]

/-- Normalizing a nonzero solution `y` of `M ȳ = σ y` (with `M = [[m₀₀, m₀₁], [m₀₁, m₁₁]]`). -/
private lemma coneig_normalize (m00 m01 m11 y0 y1 : ℂ) (σ : ℝ) (hy : y0 ≠ 0 ∨ y1 ≠ 0)
    (h0 : m00 * conj y0 + m01 * conj y1 = σ * y0) (h1 : m01 * conj y0 + m11 * conj y1 = σ * y1) :
    ∃ a b : ℂ, a * conj a + b * conj b = 1 ∧ m00 * conj a + m01 * conj b = σ * a ∧
      m01 * conj a + m11 * conj b = σ * b := by
  have hNpos : 0 < normSq y0 + normSq y1 := by
    rcases hy with h | h
    · have := normSq_pos.mpr h
      have := normSq_nonneg y1
      linarith
    · have := normSq_pos.mpr h
      have := normSq_nonneg y0
      linarith
  set r : ℝ := Real.sqrt (normSq y0 + normSq y1) with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr hNpos
  have hr2 : r ^ 2 = normSq y0 + normSq y1 := Real.sq_sqrt hNpos.le
  have hc : conj ((r⁻¹ : ℝ) : ℂ) = ((r⁻¹ : ℝ) : ℂ) := conj_ofReal _
  have hreal : (r⁻¹) ^ 2 * (normSq y0 + normSq y1) = 1 := by
    rw [inv_pow, hr2]
    field_simp
  have hcplx : ((r⁻¹ : ℝ) : ℂ) ^ 2 * ((normSq y0 : ℂ) + (normSq y1 : ℂ)) = 1 := by
    exact_mod_cast hreal
  refine ⟨y0 * ((r⁻¹ : ℝ) : ℂ), y1 * ((r⁻¹ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, hc]
    linear_combination ((r⁻¹ : ℝ) : ℂ) ^ 2 * mul_conj y0 + ((r⁻¹ : ℝ) : ℂ) ^ 2 * mul_conj y1 + hcplx
  · rw [map_mul, map_mul, hc]
    linear_combination ((r⁻¹ : ℝ) : ℂ) * h0
  · rw [map_mul, map_mul, hc]
    linear_combination ((r⁻¹ : ℝ) : ℂ) * h1

/-- The `(1,0)` entry of a symmetric matrix equals its `(0,1)` entry. -/
private lemma symm_entry {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : Mᵀ = M) : M 1 0 = M 0 1 := by
  have := congrFun (congrFun hM 0) 1
  simpa using this

open scoped ComplexOrder in
/-- A coneigenvector of a symmetric `M`: a unit vector `(a, b)` with `M (ā, b̄)ᵀ = σ (a, b)ᵀ`, `σ ≥ 0`.
It is built from an eigenvector `v` of the Hermitian positive semidefinite matrix `M Mᴴ = M M̄`:
with `M M̄ v = σ² v` and `w = M v̄`, the vector `w + σ v` (or `i v` when `w + σ v = 0`) works. -/
private lemma exists_coneig (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Mᵀ = M) :
    ∃ (a b : ℂ) (σ : ℝ), 0 ≤ σ ∧ a * conj a + b * conj b = 1 ∧
      M 0 0 * conj a + M 0 1 * conj b = σ * a ∧ M 0 1 * conj a + M 1 1 * conj b = σ * b := by
  have h10 := symm_entry hM
  have hH : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (M * Mᴴ) *ᵥ v = (hH.1.eigenvalues 0) • v :=
    ⟨_, (WithLp.ofLp_eq_zero 2).ne.2 <| hH.1.eigenvectorBasis.orthonormal.ne_zero 0,
      hH.1.mulVec_eigenvectorBasis 0⟩
  have hμ : 0 ≤ hH.1.eigenvalues 0 := hH.eigenvalues_nonneg 0
  set μ := hH.1.eigenvalues 0 with hμ_def
  set σ : ℝ := Real.sqrt μ with hσ_def
  have hσ2 : (σ : ℂ) ^ 2 = μ := by exact_mod_cast Real.sq_sqrt hμ
  have e0 : M 0 0 * (conj (M 0 0) * v 0 + conj (M 0 1) * v 1) +
      M 0 1 * (conj (M 0 1) * v 0 + conj (M 1 1) * v 1) = μ * v 0 := by
    have := congrFun hv 0
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h10] at this
    linear_combination this
  have e1 : M 0 1 * (conj (M 0 0) * v 0 + conj (M 0 1) * v 1) +
      M 1 1 * (conj (M 0 1) * v 0 + conj (M 1 1) * v 1) = μ * v 1 := by
    have := congrFun hv 1
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h10] at this
    linear_combination this
  have hv01 : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    funext i
    fin_cases i
    · simpa using h.1
    · simpa using h.2
  set x0 := M 0 0 * conj (v 0) + M 0 1 * conj (v 1) + σ * v 0 with hx0
  set x1 := M 0 1 * conj (v 0) + M 1 1 * conj (v 1) + σ * v 1 with hx1
  by_cases hx : x0 ≠ 0 ∨ x1 ≠ 0
  · obtain ⟨a, b, hn, ha, hb⟩ := coneig_normalize (M 0 0) (M 0 1) (M 1 1) x0 x1 σ hx
      (by
        rw [hx0, hx1]
        simp only [map_add, map_mul, conj_conj, conj_ofReal]
        linear_combination e0 - v 0 * hσ2)
      (by
        rw [hx0, hx1]
        simp only [map_add, map_mul, conj_conj, conj_ofReal]
        linear_combination e1 - v 1 * hσ2)
    exact ⟨a, b, σ, Real.sqrt_nonneg _, hn, ha, hb⟩
  · push Not at hx
    obtain ⟨a, b, hn, ha, hb⟩ := coneig_normalize (M 0 0) (M 0 1) (M 1 1) (I * v 0) (I * v 1) σ
      (by simpa [I_ne_zero] using hv01)
      (by
        simp only [map_mul, conj_I]
        linear_combination (-I) * hx.1)
      (by
        simp only [map_mul, conj_I]
        linear_combination (-I) * hx.2)
    exact ⟨a, b, σ, Real.sqrt_nonneg _, hn, ha, hb⟩

/-- Takagi's factorization in the form `Wᴴ M W̄ = diag(σ₁, σ₂)` with `W` unitary and `σⱼ ≥ 0`: the first column
of `W` is a coneigenvector `x = (a, b)`, the second is `u (-b̄, ā)` with the phase `u` making the last entry `≥ 0`. -/
private lemma takagi_core (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Mᵀ = M) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℂ, W * Wᴴ = 1 ∧ ∃ σ₁ σ₂ : ℝ, 0 ≤ σ₁ ∧ 0 ≤ σ₂ ∧
      Wᴴ * M * W.map star = Matrix.diagonal ![(σ₁ : ℂ), (σ₂ : ℂ)] := by
  have h10 := symm_entry hM
  obtain ⟨a, b, σ, hσ, hn, h0, h1⟩ := exists_coneig M hM
  obtain ⟨u, hu1, hu2⟩ := exists_phase (b ^ 2 * M 0 0 - 2 * a * b * M 0 1 + a ^ 2 * M 1 1)
  refine ⟨!![a, -conj b * u; b, conj a * u], ?_, σ, ‖b ^ 2 * M 0 0 - 2 * a * b * M 0 1 + a ^ 2 * M 1 1‖,
    hσ, norm_nonneg _, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
      | linear_combination hn + b * conj b * hu1
      | linear_combination hn + a * conj a * hu1
      | linear_combination (-a * conj b) * hu1
      | linear_combination (-b * conj a) * hu1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h10] <;>
      first
      | linear_combination conj a * h0 + conj b * h1 + σ * hn
      | linear_combination (-b * conj u) * h0 + (a * conj u) * h1
      | linear_combination (b * conj u) * h0 - (a * conj u) * h1
      | linear_combination hu2

/-- Every symmetric matrix is `symMat` of its entries. -/
private lemma symMat_entries {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : Mᵀ = M) :
    symMat (M 0 0, M 0 1, M 1 1) = M := by
  have h10 := symm_entry hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat, h10]

/-- `symMat p` is symmetric. -/
private lemma symMat_transpose (p : ℂ × ℂ × ℂ) : (symMat p)ᵀ = symMat p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat]

/-- `symMat` is continuous. -/
private lemma continuous_symMat : Continuous symMat := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [symMat] <;> fun_prop

/-- `symMat 0 = 0`. -/
private lemma symMat_zero : symMat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat]

/-! ### The operator norm -/

section L2

open scoped Matrix.Norms.L2Operator

/-- `opNorm` is the L2 operator norm of matrices. -/
private lemma opNorm_eq_norm (M : Matrix (Fin 2) (Fin 2) ℂ) : opNorm M = ‖M‖ := rfl

/-- A unitary matrix has operator norm `1`. -/
private lemma norm_of_unitary {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖U‖ = 1 :=
  CStarRing.norm_of_mem_unitary hU

/-- For unitary `V`, `V'`: `‖V X V'‖ ≤ ‖X‖`. -/
private lemma norm_unitary_mul_mul_le {V V' X : Matrix (Fin 2) (Fin 2) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hV' : V' ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖V * X * V'‖ ≤ ‖X‖ := by
  calc ‖V * X * V'‖ ≤ ‖V * X‖ * ‖V'‖ := norm_mul_le _ _
    _ ≤ ‖V‖ * ‖X‖ * ‖V'‖ := by gcongr; exact norm_mul_le _ _
    _ = ‖X‖ := by rw [norm_of_unitary hV, norm_of_unitary hV', one_mul, mul_one]

/-- Each entry is bounded by the operator norm. -/
private lemma norm_entry_le (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ‖M i j‖ ≤ ‖M‖ := by
  set T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M with hT
  set e : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 (Pi.single j (1 : ℂ)) with he
  have h1 : ‖M i j‖ = ‖(T e) i‖ := by
    simp [T, e, Matrix.mulVec_single]
  have he1 : ‖e‖ = 1 := by
    simp [e, PiLp.norm_single]
  have h2 : ‖T‖ = ‖M‖ := rfl
  calc ‖M i j‖ = ‖(T e) i‖ := h1
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm _
    _ = ‖M‖ := by rw [h2, he1, mul_one]

/-- The set of coordinates of `𝓑` is compact. -/
private lemma isCompact_ballSet : IsCompact {p : ℂ × ℂ × ℂ | InBall (symMat p)} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have hc : Continuous (fun p : ℂ × ℂ × ℂ => ‖symMat p‖) := continuous_norm.comp continuous_symMat
    have : {p : ℂ × ℂ × ℂ | InBall (symMat p)} = (fun p => ‖symMat p‖) ⁻¹' Set.Iic 1 := by
      ext p
      simp [InBall, symMat_transpose, opNorm_eq_norm]
    rw [this]
    exact isClosed_Iic.preimage hc
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun p hp => ?_⟩
    have hp' : ‖symMat p‖ ≤ 1 := hp.2
    have e1 : ‖p.1‖ ≤ 1 := by
      have := (norm_entry_le (symMat p) 0 0).trans hp'
      simpa [symMat] using this
    have e2 : ‖p.2.1‖ ≤ 1 := by
      have := (norm_entry_le (symMat p) 0 1).trans hp'
      simpa [symMat] using this
    have e3 : ‖p.2.2‖ ≤ 1 := by
      have := (norm_entry_le (symMat p) 1 1).trans hp'
      simpa [symMat] using this
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.mpr ⟨e1, norm_prod_le_iff.mpr ⟨e2, e3⟩⟩

/-- Takagi's factorization with the bounds `σⱼ ≤ ‖M‖`. -/
private lemma takagi_full (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Mᵀ = M) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℂ, W * Wᴴ = 1 ∧ ∃ σ₁ σ₂ : ℝ, 0 ≤ σ₁ ∧ 0 ≤ σ₂ ∧ σ₁ ≤ opNorm M ∧
      σ₂ ≤ opNorm M ∧ M = W * Matrix.diagonal ![(σ₁ : ℂ), (σ₂ : ℂ)] * Wᵀ := by
  obtain ⟨W, hW, σ₁, σ₂, h1, h2, hD⟩ := takagi_core M hM
  have hWu : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.mem_unitaryGroup_iff.mpr hW
  have hWb : W.map star ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.map_star_mem_unitaryGroup_iff.mpr hWu
  have hWh : Wᴴ ∈ Matrix.unitaryGroup (Fin 2) ℂ := Unitary.star_mem hWu
  have hbT : W.map star * Wᵀ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hWb
    have e : star (W.map star) = Wᵀ := by
      ext i j
      simp [Matrix.star_apply]
    rwa [e] at h
  have hnorm : ‖Matrix.diagonal ![(σ₁ : ℂ), (σ₂ : ℂ)]‖ ≤ ‖M‖ := by
    rw [← hD]
    exact norm_unitary_mul_mul_le hWh hWb
  rw [Matrix.l2_opNorm_diagonal] at hnorm
  have b1 : σ₁ ≤ opNorm M := by
    have := (norm_le_pi_norm (![(σ₁ : ℂ), (σ₂ : ℂ)]) 0).trans hnorm
    rw [opNorm_eq_norm]
    simpa [abs_of_nonneg h1] using this
  have b2 : σ₂ ≤ opNorm M := by
    have := (norm_le_pi_norm (![(σ₁ : ℂ), (σ₂ : ℂ)]) 1).trans hnorm
    rw [opNorm_eq_norm]
    simpa [abs_of_nonneg h2] using this
  refine ⟨W, hW, σ₁, σ₂, h1, h2, b1, b2, ?_⟩
  calc M = (W * Wᴴ) * M * (W.map star * Wᵀ) := by rw [hW, hbT, Matrix.one_mul, Matrix.mul_one]
    _ = W * (Wᴴ * M * W.map star) * Wᵀ := by simp only [Matrix.mul_assoc]
    _ = W * Matrix.diagonal ![(σ₁ : ℂ), (σ₂ : ℂ)] * Wᵀ := by rw [hD]

/-- The matrix `W diag(ζ₁, ζ₂) Wᵀ`. -/
private noncomputable def tk (W : Matrix (Fin 2) (Fin 2) ℂ) (z1 z2 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  W * Matrix.diagonal ![z1, z2] * Wᵀ

/-- `W diag(ζ₁, ζ₂) Wᵀ` is symmetric. -/
private lemma tk_transpose (W : Matrix (Fin 2) (Fin 2) ℂ) (z1 z2 : ℂ) : (tk W z1 z2)ᵀ = tk W z1 z2 := by
  simp [tk, Matrix.transpose_mul, Matrix.mul_assoc]

/-- `W diag(ζ₁, ζ₂) Wᵀ ∈ 𝓑` for unitary `W` and `|ζⱼ| ≤ 1`. -/
private lemma tk_inBall {W : Matrix (Fin 2) (Fin 2) ℂ} (hW : W * Wᴴ = 1) {z1 z2 : ℂ} (h1 : ‖z1‖ ≤ 1)
    (h2 : ‖z2‖ ≤ 1) : InBall (tk W z1 z2) := by
  refine ⟨tk_transpose W z1 z2, ?_⟩
  have hWu : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.mem_unitaryGroup_iff.mpr hW
  have hWT : Wᵀ ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.transpose_mem_unitaryGroup_iff.mpr hWu
  rw [opNorm_eq_norm, tk]
  refine (norm_unitary_mul_mul_le hWu hWT).trans ?_
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  fin_cases i
  · simpa using h1
  · simpa using h2

/-- `W diag(ζ₁, ζ₂) Wᵀ` is unitary for unitary `W` and `|ζⱼ| = 1`. -/
private lemma tk_unitary {W : Matrix (Fin 2) (Fin 2) ℂ} (hW : W * Wᴴ = 1) {z1 z2 : ℂ} (h1 : ‖z1‖ = 1)
    (h2 : ‖z2‖ = 1) : tk W z1 z2 * (tk W z1 z2)ᴴ = 1 := by
  have hWu : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.mem_unitaryGroup_iff.mpr hW
  have hWT : Wᵀ ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.transpose_mem_unitaryGroup_iff.mpr hWu
  have hD : Matrix.diagonal ![z1, z2] ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_conj', h1, h2]
  have := Matrix.mem_unitaryGroup_iff.mp
    ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem hWu hD) hWT)
  exact this

end L2

/-- Linearity of `W diag(ζ₁, ζ₂) Wᵀ` in `ζ₁`. -/
private lemma tk_add1 (W : Matrix (Fin 2) (Fin 2) ℂ) (z1 z2 : ℂ) :
    tk W z1 z2 = tk W 0 z2 + z1 • tk W 1 0 := by
  have : Matrix.diagonal ![z1, z2] = Matrix.diagonal ![0, z2] + z1 • Matrix.diagonal ![1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [tk, tk, tk, this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Linearity of `W diag(ζ₁, ζ₂) Wᵀ` in `ζ₂`. -/
private lemma tk_add2 (W : Matrix (Fin 2) (Fin 2) ℂ) (z1 z2 : ℂ) :
    tk W z1 z2 = tk W z1 0 + z2 • tk W 0 1 := by
  have : Matrix.diagonal ![z1, z2] = Matrix.diagonal ![z1, 0] + z2 • Matrix.diagonal ![0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [tk, tk, tk, this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-! ### The minimum principle on a complex line -/

/-- On a complex line `z ↦ A + z B` lying in `𝓑` for `|z| ≤ 1`, the minimum of `Re Φ` over the closed unit disc is
attained on the unit circle: apply the maximum modulus principle to `exp(-Φ)`, `|exp(-Φ)| = exp(-Re Φ)`. -/
private lemma move_to_circle (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (hΦ : HolomorphicNearBall Φ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hball : ∀ z : ℂ, ‖z‖ ≤ 1 → InBall (A + z • B)) (z₀ : ℂ) (hz₀ : ‖z₀‖ ≤ 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (Φ (A + z • B)).re ≤ (Φ (A + z₀ • B)).re := by
  obtain ⟨U, -, hKU, hdiff⟩ := hΦ
  have hA10 := symm_entry hA
  have hB10 := symm_entry hB
  obtain ⟨p, hp_def⟩ : ∃ p : ℂ → ℂ × ℂ × ℂ,
      p = fun z => (A 0 0 + z * B 0 0, A 0 1 + z * B 0 1, A 1 1 + z * B 1 1) := ⟨_, rfl⟩
  have hp : ∀ z, symMat (p z) = A + z • B := by
    intro z
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symMat, hp_def, hA10, hB10]
  have hpd : Differentiable ℂ p := by
    rw [hp_def]
    fun_prop
  have hcl : closedBall (0 : ℂ) 1 ⊆ p ⁻¹' U := fun z hz =>
    hKU (show InBall (symMat (p z)) by rw [hp]; exact hball z (by simpa using hz))
  have h1 : DifferentiableOn ℂ (fun z => Φ (symMat (p z))) (p ⁻¹' U) :=
    hdiff.comp hpd.differentiableOn (fun z hz => hz)
  have hgd : DifferentiableOn ℂ (fun z => exp (-Φ (symMat (p z)))) (closedBall 0 1) :=
    (h1.mono hcl).neg.cexp
  have hdc : DiffContOnCl ℂ (fun z => exp (-Φ (symMat (p z)))) (ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hgd
  obtain ⟨z, hzfr, hmax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball ⟨0, mem_ball_self one_pos⟩ hdc
  rw [frontier_ball (0 : ℂ) one_ne_zero] at hzfr
  rw [closure_ball (0 : ℂ) one_ne_zero] at hmax
  have hle := isMaxOn_iff.mp hmax z₀ (by simpa using hz₀)
  simp only [Function.comp_apply, norm_exp, neg_re] at hle
  refine ⟨z, by simpa using hzfr, ?_⟩
  rw [← hp z, ← hp z₀]
  have := Real.exp_le_exp.mp hle
  linarith

/-- `Re Φ` attains its minimum over `𝓑` (a compact set, on a neighbourhood of which `Φ` is continuous). -/
private lemma exists_min_on_ball (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (hΦ : HolomorphicNearBall Φ) :
    ∃ M₀, InBall M₀ ∧ ∀ M, InBall M → (Φ M₀).re ≤ (Φ M).re := by
  obtain ⟨U, -, hKU, hdiff⟩ := hΦ
  have h0 : InBall (symMat 0) := by
    refine ⟨symMat_transpose 0, ?_⟩
    simp [opNorm, symMat_zero]
  have hcont : ContinuousOn (fun p => (Φ (symMat p)).re) {p | InBall (symMat p)} :=
    continuous_re.comp_continuousOn (hdiff.continuousOn.mono hKU)
  obtain ⟨p₀, hp₀, hmin⟩ := isCompact_ballSet.exists_isMinOn ⟨0, h0⟩ hcont
  refine ⟨symMat p₀, hp₀, fun M hM => ?_⟩
  have hM' : (M 0 0, M 0 1, M 1 1) ∈ {p : ℂ × ℂ × ℂ | InBall (symMat p)} := by
    show InBall _
    rw [symMat_entries hM.1]
    exact hM
  have := isMinOn_iff.mp hmin _ hM'
  simpa [symMat_entries hM.1] using this

/-! ### The two rows -/

/-- Takagi's factorization of a complex symmetric 2x2 matrix (sec_05_grunsky_q.tex, proof of Proposition 5.2). -/
theorem sec5_takagi_2x2_proved (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Mᵀ = M) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℂ, W * Wᴴ = 1 ∧ ∃ σ₁ σ₂ : ℝ, 0 ≤ σ₁ ∧ 0 ≤ σ₂ ∧ σ₁ ≤ opNorm M ∧
      σ₂ ≤ opNorm M ∧ M = W * Matrix.diagonal ![(σ₁ : ℂ), (σ₂ : ℂ)] * Wᵀ :=
  takagi_full M hM

/-- Proposition 5.2: the minimum of `Re Φ` over `𝓑` is attained at a symmetric unitary matrix. -/
theorem prop_5_2_proved (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (hΦ : HolomorphicNearBall Φ) :
    ∃ M₀ : Matrix (Fin 2) (Fin 2) ℂ, InBall M₀ ∧ IsSymmUnitary M₀ ∧
      ∀ M : Matrix (Fin 2) (Fin 2) ℂ, InBall M → (Φ M₀).re ≤ (Φ M).re := by
  obtain ⟨Mmin, hMmin, hle⟩ := exists_min_on_ball Φ hΦ
  obtain ⟨W, hW, σ₁, σ₂, h1, h2, b1, b2, hdec⟩ := takagi_full Mmin hMmin.1
  have hs1 : ‖(σ₁ : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_of_nonneg h1]
    exact b1.trans hMmin.2
  have hs2 : ‖(σ₂ : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_of_nonneg h2]
    exact b2.trans hMmin.2
  obtain ⟨z1, hz1, hle1⟩ := move_to_circle Φ hΦ (tk W 0 σ₂) (tk W 1 0) (tk_transpose _ _ _)
    (tk_transpose _ _ _) (fun z hz => by rw [← tk_add1 W z σ₂]; exact tk_inBall hW hz hs2) σ₁ hs1
  rw [← tk_add1 W z1 σ₂, ← tk_add1 W σ₁ σ₂] at hle1
  obtain ⟨z2, hz2, hle2⟩ := move_to_circle Φ hΦ (tk W z1 0) (tk W 0 1) (tk_transpose _ _ _)
    (tk_transpose _ _ _) (fun z hz => by rw [← tk_add2 W z1 z]; exact tk_inBall hW hz1.le hz) σ₂ hs2
  rw [← tk_add2 W z1 z2, ← tk_add2 W z1 σ₂] at hle2
  refine ⟨tk W z1 z2, tk_inBall hW hz1.le hz2.le, ⟨tk_transpose _ _ _, tk_unitary hW hz1 hz2⟩,
    fun M hM => ?_⟩
  have hmin := hle M hM
  have hdec' : Mmin = tk W σ₁ σ₂ := hdec
  rw [hdec'] at hmin
  linarith

end Robinson.Proofs
