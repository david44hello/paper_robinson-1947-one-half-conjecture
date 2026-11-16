/-
Robinson/Proofs/Sec7Lin.lean — proofs of sec7_CP_linear, sec7_CP_explicit, sec7_trace_bound.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Matrix2
import Robinson.Proofs.Arith

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## The cap `C_P` is a rational linear combination of the Gram entries -/

/-- The rational matrix `P`. -/
private def Pq : Matrix (Fin 4) (Fin 4) ℚ :=
  (1 / 10000 : ℚ) •
    !![16946, 3451, -992, 2537; 3451, 30184, 856, -108; -992, 856, 2733, -344; 2537, -108, -344, 879]

/-- The rational matrix `J = (4/5) J₁ + (1/2) J₂`. -/
private def Jq : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, -8 / 5, -1 / 2, 0; -8 / 5, 0, 0, -1 / 2; -1 / 2, 0, 0, 0; 0, -1 / 2, 0, 0]

/-- The rational matrix `K = ½ (P + J P⁻¹ J)`. -/
private noncomputable def Kq : Matrix (Fin 4) (Fin 4) ℚ := (1 / 2 : ℚ) • (Pq + Jq * Pq⁻¹ * Jq)

private lemma Pq_map : Pq.map (Rat.cast : ℚ → ℝ) = Pmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pq, Pmat]

private lemma Jq_map : Jq.map (Rat.cast : ℚ → ℝ) = Jmat (4 / 5) (1 / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jq, Jmat, J1, J2] <;> norm_num

private lemma Pq_det_ne : Pq.det ≠ 0 := by
  intro h
  have hd : Pmat.det = ((Pq.det : ℚ) : ℝ) := by
    rw [← Pq_map]
    exact (RingHom.map_det (Rat.castHom ℝ) Pq).symm
  have := Pmat_posDef.det_pos
  rw [hd, h, Rat.cast_zero] at this
  exact lt_irrefl _ this

private lemma Pq_inv_map : (Pq⁻¹).map (Rat.cast : ℚ → ℝ) = Pmat⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Pq_map]
  have h := Matrix.nonsing_inv_mul Pq (isUnit_iff_ne_zero.mpr Pq_det_ne)
  have key : (Rat.castHom ℝ).mapMatrix (Pq⁻¹) * (Rat.castHom ℝ).mapMatrix Pq = 1 := by
    rw [← map_mul, h, map_one]
  exact key

private lemma Kq_map : Kmat (4 / 5) (1 / 2) Pmat = Kq.map (↑) := by
  have hX : (Pq + Jq * Pq⁻¹ * Jq).map (Rat.cast : ℚ → ℝ) =
      Pmat + Jmat (4 / 5) (1 / 2) * Pmat⁻¹ * Jmat (4 / 5) (1 / 2) := by
    rw [← Pq_inv_map, ← Pq_map, ← Jq_map]
    have key : (Rat.castHom ℝ).mapMatrix (Pq + Jq * Pq⁻¹ * Jq) = (Rat.castHom ℝ).mapMatrix Pq +
        (Rat.castHom ℝ).mapMatrix Jq * (Rat.castHom ℝ).mapMatrix (Pq⁻¹) * (Rat.castHom ℝ).mapMatrix Jq := by
      rw [map_add, map_mul, map_mul]
    exact key
  ext i j
  have := congrFun (congrFun hX i) j
  simp only [Matrix.map_apply] at this
  simp only [Kmat, Kq, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Rat.cast_mul, ← this]
  norm_num

/-- The nine rational coefficients, read off from the entries of `K` and the shape of `G(θ)`. -/
private noncomputable def qCoef : Fin 9 → ℚ :=
  ![(Kq 0 0 + Kq 1 1) / 2, (Kq 0 0 - Kq 1 1) / 2, (Kq 1 0 + Kq 0 1) / 2,
    (Kq 2 0 + Kq 0 2 + Kq 3 1 + Kq 1 3) / 2, (Kq 2 0 + Kq 0 2 - Kq 3 1 - Kq 1 3) / 2,
    (Kq 3 0 + Kq 2 1 + Kq 1 2 + Kq 0 3) / 2,
    (Kq 2 2 + Kq 3 3) / 2, (Kq 2 2 - Kq 3 3) / 2, (Kq 3 2 + Kq 2 3) / 2]

theorem sec7_CP_linear_proved :
    (∃ Kq : Matrix (Fin 4) (Fin 4) ℚ, Kmat (4 / 5) (1 / 2) Pmat = Kq.map (↑)) ∧
      ∃ q : Fin 9 → ℚ, ∀ θ : ℝ, CP θ (4 / 5) (1 / 2) Pmat =
        q 0 * Ae + q 1 * (Ze θ).re + q 2 * (Ze θ).im + q 3 * Le + q 4 * (Lz θ).re + q 5 * (Lz θ).im +
          q 6 * Me + q 7 * (Mz θ).re + q 8 * (Mz θ).im := by
  refine ⟨⟨Kq, Kq_map⟩, qCoef, fun θ => ?_⟩
  rw [CP, Kq_map]
  simp [qCoef, Gram, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  ring

/-! ## `C_P(θ)` with its nine printed rational coefficients -/

/-- `P⁻¹`, exactly (`Pq * PqInv = 1`). -/
private def PqInv : Matrix (Fin 4) (Fin 4) ℚ :=
  (1 / 125044355055249 : ℚ) •
    !![136654064464000, -17186619290000, 5336867440000, -394438719032000;
       -17186619290000, 43960152370000, -13761297440000, 49620322270000;
       5336867440000, -13761297440000, 485548588690000, 172927032640000;
       -394438719032000, 49620322270000, 172927032640000, 2634790073686000]

private lemma Pq_mul_PqInv : Pq * PqInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pq, PqInv, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

private lemma Pq_inv_eq : Pq⁻¹ = PqInv := Matrix.inv_eq_right_inv Pq_mul_PqInv

/-- The entries of `K = ½ (P + J P⁻¹ J)`, exactly. -/
private lemma Kq_eq : Kq =
    !![235448458562402753 / 138938172283610000, 95947301639073811 / 277876344567220000,
        -2585362353487573 / 26050907303176875, 211505168045055571 / 833629033701660000;
       95947301639073811 / 277876344567220000, 104842201985681053 / 34734543070902500,
        8923903585803881 / 104203629212707500, -2245578249247241 / 208407258425415000;
       -2585362353487573 / 26050907303176875, 8923903585803881 / 104203629212707500,
        683381383525995517 / 2500887101104980000, -10747725795500707 / 312610887638122500;
       211505168045055571 / 833629033701660000, -2245578249247241 / 208407258425415000,
        -10747725795500707 / 312610887638122500, 219814369018563871 / 2500887101104980000] := by
  rw [Kq, Pq_inv_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pq, PqInv, Jq, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- `C_P(θ)` for `λ = 4/5`, `μ = ½` and the fixed `P`, with the nine rational coefficients as printed. -/
theorem sec7_CP_explicit_proved (θ : ℝ) :
    CP θ (4 / 5) (1 / 2) Pmat =
      130963453301025393 / 55575268913444000 * Ae - 183920349380321459 / 277876344567220000 * (Ze θ).re +
        95947301639073811 / 277876344567220000 * (Ze θ).im - 917139083085913 / 8336290337016600 * Le -
        6145773526217781 / 69469086141805000 * (Lz θ).re + 282896396731486619 / 833629033701660000 * (Lz θ).im +
        225798938136139847 / 1250443550552490000 * Me + 3679103289741521 / 39696620652460000 * (Mz θ).re -
        10747725795500707 / 312610887638122500 * (Mz θ).im := by
  rw [CP, Kq_map, Kq_eq]
  simp [Gram, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  ring

/-! ## The trace bound -/

/-- `tr(E X Yᵀ) = ∑_j y_jᵀ E x_j` over the columns `x_j`, `y_j` of `X`, `Y`. -/
private lemma trace_E_mul {N : ℕ} (E : Matrix (Fin N) (Fin N) ℂ) (X Y : Matrix (Fin N) (Fin 4) ℝ) :
    Matrix.trace (E * (X * Yᵀ).map (↑)) =
      ∑ j, (fun i => (Y i j : ℂ)) ⬝ᵥ (E *ᵥ (fun i => (X i j : ℂ))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma trace_transpose_mul_self {N : ℕ} (Z : Matrix (Fin N) (Fin 4) ℝ) :
    Matrix.trace (Zᵀ * Z) = ∑ j, ∑ i, Z i j ^ 2 := by
  simp [Matrix.trace, Matrix.mul_apply, sq]

private lemma sqrt_mul_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (1 / 2) * (a + b) := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- `|tr(E X Yᵀ)| ≤ ½ (tr XᵀX + tr YᵀY)` when `|yᵀ E x| ≤ ‖x‖ ‖y‖` on real vectors. -/
private lemma trace_bound_XY {N : ℕ} (E : Matrix (Fin N) (Fin N) ℂ)
    (hE : ∀ x y : Fin N → ℝ, ‖(fun i => (y i : ℂ)) ⬝ᵥ (E *ᵥ (fun i => (x i : ℂ)))‖ ≤
      Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (X Y : Matrix (Fin N) (Fin 4) ℝ) :
    ‖Matrix.trace (E * (X * Yᵀ).map (↑))‖ ≤
      (1 / 2) * (Matrix.trace (Xᵀ * X) + Matrix.trace (Yᵀ * Y)) := by
  rw [trace_E_mul, trace_transpose_mul_self, trace_transpose_mul_self]
  calc ‖∑ j, (fun i => (Y i j : ℂ)) ⬝ᵥ (E *ᵥ (fun i => (X i j : ℂ)))‖
      ≤ ∑ j, ‖(fun i => (Y i j : ℂ)) ⬝ᵥ (E *ᵥ (fun i => (X i j : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ j, Real.sqrt (∑ i, X i j ^ 2) * Real.sqrt (∑ i, Y i j ^ 2) :=
        Finset.sum_le_sum fun j _ => hE (fun i => X i j) (fun i => Y i j)
    _ ≤ ∑ j, (1 / 2) * (∑ i, X i j ^ 2 + ∑ i, Y i j ^ 2) :=
        Finset.sum_le_sum fun j _ => sqrt_mul_sqrt_le (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ = (1 / 2) * (∑ j, ∑ i, X i j ^ 2 + ∑ j, ∑ i, Y i j ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- A positive definite real `P` factors as `P = S Sᵀ` with `S Rᵀ = 1` for some `R`
(take `S = U D^{1/2}`, `R = U D^{-1/2}` from the spectral theorem `P = U D Uᵀ`). -/
private lemma exists_factor (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : P.PosDef) :
    ∃ S R : Matrix (Fin 4) (Fin 4) ℝ, S * Rᵀ = 1 ∧ S * Sᵀ = P := by
  classical
  set U : Matrix (Fin 4) (Fin 4) ℝ := (hP.1.eigenvectorUnitary : Matrix (Fin 4) (Fin 4) ℝ) with hU
  set ev : Fin 4 → ℝ := hP.1.eigenvalues with hev
  have hspec : P = U * Matrix.diagonal ev * Uᵀ := by
    have h := hP.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa [RCLike.ofReal_real_eq_id] using h
  have hUU : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hP.1.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hpos : ∀ i, 0 < ev i := fun i => hP.eigenvalues_pos i
  refine ⟨U * Matrix.diagonal (fun i => Real.sqrt (ev i)),
    U * Matrix.diagonal (fun i => (Real.sqrt (ev i))⁻¹), ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    have hD : Matrix.diagonal (fun i => Real.sqrt (ev i)) * Matrix.diagonal (fun i => (Real.sqrt (ev i))⁻¹)
        = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hpos i)).ne'
    calc U * Matrix.diagonal (fun i => Real.sqrt (ev i)) *
          (Matrix.diagonal (fun i => (Real.sqrt (ev i))⁻¹) * Uᵀ)
        = U * (Matrix.diagonal (fun i => Real.sqrt (ev i)) *
            Matrix.diagonal (fun i => (Real.sqrt (ev i))⁻¹)) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD, Matrix.mul_one, hUU]
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    have hD : Matrix.diagonal (fun i => Real.sqrt (ev i)) * Matrix.diagonal (fun i => Real.sqrt (ev i))
        = Matrix.diagonal ev := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hpos i).le
    calc U * Matrix.diagonal (fun i => Real.sqrt (ev i)) *
          (Matrix.diagonal (fun i => Real.sqrt (ev i)) * Uᵀ)
        = U * (Matrix.diagonal (fun i => Real.sqrt (ev i)) *
            Matrix.diagonal (fun i => Real.sqrt (ev i))) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = P := by rw [hD, ← hspec]

private lemma J1_transpose : J1ᵀ = J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J1]

private lemma J2_transpose : J2ᵀ = J2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2]

private lemma Jmat_transpose (lam mu : ℝ) : (Jmat lam mu)ᵀ = Jmat lam mu := by
  rw [Jmat, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, J1_transpose,
    J2_transpose]

/-- `tr(𝒲ᵀ𝒲 K) = ½ (tr(𝒲ᵀ𝒲 P) + tr(𝒲ᵀ𝒲 J P⁻¹ J))`. -/
private lemma trace_K {N : ℕ} (W : Matrix (Fin N) (Fin 4) ℝ) (lam mu : ℝ) (P : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.trace (Wᵀ * W * Kmat lam mu P) =
      (1 / 2) * (Matrix.trace (Wᵀ * W * P) +
        Matrix.trace (Wᵀ * W * (Jmat lam mu * P⁻¹ * Jmat lam mu))) := by
  rw [Kmat, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, smul_eq_mul]

theorem sec7_trace_bound_proved (N : ℕ) (E : Matrix (Fin N) (Fin N) ℂ)
    (hE : ∀ x y : Fin N → ℝ, ‖(fun i => (y i : ℂ)) ⬝ᵥ (E *ᵥ (fun i => (x i : ℂ)))‖ ≤
      Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (W : Matrix (Fin N) (Fin 4) ℝ) (lam mu : ℝ) (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : P.PosDef) :
    ‖Matrix.trace (E * (W * Jmat lam mu * Wᵀ).map (↑))‖ ≤ Matrix.trace (Wᵀ * W * Kmat lam mu P) := by
  obtain ⟨S, R, hSR, hSS⟩ := exists_factor P hP
  have hJ := Jmat_transpose lam mu
  set J := Jmat lam mu with hJdef
  have hRS : Rᵀ * S = 1 := mul_eq_one_comm.mp hSR
  have hRR : R * Rᵀ = P⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [← hSS]
    calc R * Rᵀ * (S * Sᵀ) = R * (Rᵀ * S) * Sᵀ := by simp only [Matrix.mul_assoc]
      _ = (S * Rᵀ)ᵀ := by rw [hRS, Matrix.mul_one, Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = 1 := by rw [hSR, Matrix.transpose_one]
  have hfac : W * J * Wᵀ = (W * S) * (W * J * R)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ]
    calc W * J * Wᵀ = W * (S * Rᵀ) * J * Wᵀ := by rw [hSR, Matrix.mul_one]
      _ = W * S * (Rᵀ * (J * Wᵀ)) := by simp only [Matrix.mul_assoc]
  have h1 : Matrix.trace ((W * S)ᵀ * (W * S)) = Matrix.trace (Wᵀ * W * P) := by
    rw [Matrix.transpose_mul, ← hSS]
    calc Matrix.trace (Sᵀ * Wᵀ * (W * S)) = Matrix.trace (Sᵀ * (Wᵀ * W * S)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Wᵀ * W * S * Sᵀ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Wᵀ * W * (S * Sᵀ)) := by simp only [Matrix.mul_assoc]
  have h2 : Matrix.trace ((W * J * R)ᵀ * (W * J * R)) = Matrix.trace (Wᵀ * W * (J * P⁻¹ * J)) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, ← hRR]
    calc Matrix.trace (Rᵀ * (J * Wᵀ) * (W * J * R)) = Matrix.trace (Rᵀ * (J * Wᵀ * W * J * R)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (J * Wᵀ * W * J * R * Rᵀ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (J * (Wᵀ * W * J * (R * Rᵀ))) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Wᵀ * W * J * (R * Rᵀ) * J) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Wᵀ * W * (J * (R * Rᵀ) * J)) := by simp only [Matrix.mul_assoc]
  rw [hfac]
  refine (trace_bound_XY E hE _ _).trans (le_of_eq ?_)
  rw [h1, h2, trace_K]

end Robinson.Proofs
