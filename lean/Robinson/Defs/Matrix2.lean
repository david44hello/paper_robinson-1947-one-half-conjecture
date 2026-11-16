/-
Robinson/Defs/Matrix2.lean — the finite-dimensional objects of Sections 5 and 7 (functions of a complex
symmetric 2x2 matrix M at the angle θ).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
TRUST SURFACE: every definition is read against sec_05_grunsky_q.tex and sec_07_middle.tex (their lines; AUDIT_NOTES.md
names the version).
-/
import Robinson.Defs.Basic

namespace Robinson

open Complex Metric Matrix
open ComplexConjugate

/-! ## Section 5 -/

/-- `s = 2^{-1/2} e^{iθ/4}` (sec_05_grunsky_q.tex:8); `t = s̄`. -/
noncomputable def sθ (θ : ℝ) : ℂ := ((Real.sqrt 2)⁻¹ : ℝ) * exp (((θ / 4 : ℝ) : ℂ) * I)

/-- The complex inverse hyperbolic tangent `artanh z = ½ log((1+z)/(1-z))` (sec_06_far.tex:48), principal logarithm.
For `|z| < 1`, `(1+z)/(1-z)` has positive real part, and this is `∑_{n odd} zⁿ/n` (sec_03_tools.tex:79). -/
noncomputable def cartanh (z : ℂ) : ℂ := (1 / 2 : ℂ) * log ((1 + z) / (1 - z))

/-- `A_o = artanh ½` (sec_05_grunsky_q.tex:17). -/
noncomputable def Ao : ℝ := Real.artanh (1 / 2)

/-- `Z_o = artanh z` at `z = z_θ` (sec_05_grunsky_q.tex:17). -/
noncomputable def Zo (θ : ℝ) : ℂ := cartanh (zθ θ)

/-- The Gram–Schmidt coordinates (sec_05_grunsky_q.tex:13-19): `u = V ũ`, `v = V ṽ`, `ũ = (l₁₁, 0)`,
`ṽ = (l₂₁, l₂₂)`, from `uᵀu = (A_o + Re Z_o)/2`, `vᵀv = (A_o - Re Z_o)/2`, `uᵀv = Im Z_o / 2`
(so `l₁₁ = |u|`, `l₂₁ = uᵀv/|u|`, `l₂₂ = (vᵀv - l₂₁²)^{1/2} > 0`). -/
noncomputable def l11 (θ : ℝ) : ℝ := Real.sqrt ((Ao + (Zo θ).re) / 2)

/-- See `l11`. -/
noncomputable def l21 (θ : ℝ) : ℝ := ((Zo θ).im / 2) / l11 θ

/-- See `l11`. -/
noncomputable def l22 (θ : ℝ) : ℝ := Real.sqrt ((Ao - (Zo θ).re) / 2 - l21 θ ^ 2)

/-- `ũ = (l₁₁, 0)ᵀ` (sec_05_grunsky_q.tex:13). -/
noncomputable def ut (θ : ℝ) : Fin 2 → ℂ := ![(l11 θ : ℂ), 0]

/-- `ṽ = (l₂₁, l₂₂)ᵀ` (sec_05_grunsky_q.tex:13). -/
noncomputable def vt (θ : ℝ) : Fin 2 → ℂ := ![(l21 θ : ℂ), (l22 θ : ℂ)]

/-- The bilinear (not Hermitian) form `xᵀ M y` (sec_03_tools.tex:36). -/
def bil (x : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (y : Fin 2 → ℂ) : ℂ := x ⬝ᵥ (M *ᵥ y)

/-- `m_uu = ũᵀ M ũ` (sec_05_grunsky_q.tex:23). -/
noncomputable def cA (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := bil (ut θ) M (ut θ)

/-- `m_vv = ṽᵀ M ṽ` (sec_05_grunsky_q.tex:23). -/
noncomputable def cB (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := bil (vt θ) M (vt θ)

/-- `m_uv = ũᵀ M ṽ` (sec_05_grunsky_q.tex:23). -/
noncomputable def cC (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := bil (ut θ) M (vt θ)

/-- `ℓ₁ = 2(m_uu - m_vv) + 4i m_uv` (sec_05_grunsky_q.tex:26). -/
noncomputable def ell1 (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 * (cA θ M - cB θ M) + 4 * I * cC θ M

/-- `ℓ₂ = 2(m_uu - m_vv) - 4i m_uv` (sec_05_grunsky_q.tex:26). -/
noncomputable def ell2 (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 * (cA θ M - cB θ M) - 4 * I * cC θ M

/-- `m₊ = m_uu + m_vv` (sec_05_grunsky_q.tex:26). -/
noncomputable def kappa (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := cA θ M + cB θ M

/-- `χ = i tan(θ/4) e^{2m₊}` (sec_05_grunsky_q.tex:30). -/
noncomputable def chi (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  I * (Real.tan (θ / 4) : ℂ) * exp (2 * kappa θ M)

/-- `Q_rel(M) = 1 + (e^{ℓ₁} + e^{ℓ₂})/2 + (e^{ℓ₁} - e^{ℓ₂})(χ + χ⁻¹)/4` (sec_05_grunsky_q.tex:31). -/
noncomputable def Qrel (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  1 + (exp (ell1 θ M) + exp (ell2 θ M)) / 2 +
    (exp (ell1 θ M) - exp (ell2 θ M)) * (chi θ M + (chi θ M)⁻¹) / 4

/-- The operator norm `‖M‖` of a 2x2 complex matrix on `ℂ²` with the Euclidean norm (sec_05_grunsky_q.tex:17). -/
noncomputable def opNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M‖

/-- `M ∈ 𝓑 = {M ∈ ℂ^{2x2} : M = Mᵀ, ‖M‖ ≤ 1}` (sec_05_grunsky_q.tex:52). -/
def InBall (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Mᵀ = M ∧ opNorm M ≤ 1

/-- `M` is symmetric and unitary (sec_05_grunsky_q.tex:60, 68). -/
def IsSymmUnitary (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Mᵀ = M ∧ M * Mᴴ = 1

/-- The entrywise complex conjugate `M̄` (sec_05_grunsky_q.tex:72). -/
def mconj (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := M.map conj

/-- The complex symmetric matrix `[[a, b], [b, d]]` with entries `p = (a, b, d) ∈ ℂ³` ("the space `ℂ³` of complex
symmetric 2x2 matrices", sec_05_grunsky_q.tex:60). -/
def symMat (p : ℂ × ℂ × ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![p.1, p.2.1; p.2.1, p.2.2]

/-- `Φ` is holomorphic on a neighbourhood of `𝓑` in the space `ℂ³` of complex symmetric 2x2 matrices
(sec_05_grunsky_q.tex:60). -/
def HolomorphicNearBall (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) : Prop :=
  ∃ U : Set (ℂ × ℂ × ℂ), IsOpen U ∧ {p | InBall (symMat p)} ⊆ U ∧ DifferentiableOn ℂ (fun p => Φ (symMat p)) U

/-- The chart `M(α, ψ, ω) = e^{iψ} [[e^{iω} cos α, i sin α], [i sin α, e^{-iω} cos α]]` (sec_05_grunsky_q.tex:70). -/
noncomputable def chart (α ψ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  exp ((ψ : ℂ) * I) •
    !![exp ((ω : ℂ) * I) * (Real.cos α : ℂ), I * (Real.sin α : ℂ);
       I * (Real.sin α : ℂ), exp (-((ω : ℂ) * I)) * (Real.cos α : ℂ)]

/-! ## Section 7 -/

/-- `Δ(M) = iθ/2 - Log(1 + χ) + Log(1 - χ)`, principal logarithm (sec_07_middle.tex:18). -/
noncomputable def Delta (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  I * ((θ / 2 : ℝ) : ℂ) - log (1 + chi θ M) + log (1 - chi θ M)

/-- `U(M) = Δ(M) + 4i m_uv` (sec_07_middle.tex:18). -/
noncomputable def Ufun (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := Delta θ M + 4 * I * cC θ M

/-- `R(M) = Q_rel(M) - e^{ℓ₁} - e^{ℓ₂}` (sec_07_middle.tex:19). -/
noncomputable def Rfun (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Qrel θ M - exp (ell1 θ M) - exp (ell2 θ M)

/-- `A_e = -½ log ¾` (sec_07_middle.tex:62). -/
noncomputable def Ae : ℝ := -(1 / 2) * Real.log (3 / 4)

/-- `Z_e = -½ log(1 - z²)` at `z = z_θ` (sec_07_middle.tex:62), principal logarithm (`Re(1 - z²) > 0`). -/
noncomputable def Ze (θ : ℝ) : ℂ := -(1 / 2 : ℂ) * log (1 - zθ θ ^ 2)

/-- `L_e = ⅓` (sec_07_middle.tex:63). -/
noncomputable def Le : ℝ := 1 / 3

/-- `L_z = z²/(1 - z²)` at `z = z_θ` (sec_07_middle.tex:63). -/
noncomputable def Lz (θ : ℝ) : ℂ := zθ θ ^ 2 / (1 - zθ θ ^ 2)

/-- `M_e = 8/9` (sec_07_middle.tex:64). -/
noncomputable def Me : ℝ := 8 / 9

/-- `M_z = 2z²/(1 - z²)²` at `z = z_θ` (sec_07_middle.tex:64). -/
noncomputable def Mz (θ : ℝ) : ℂ := 2 * zθ θ ^ 2 / (1 - zθ θ ^ 2) ^ 2

/-- The real 4x4 Gram matrix `G(θ)` of `u_e, v_e, β₀, β₁` (sec_07_middle.tex:54-66), written out from the blocks
`S(a, c) = ½ [[a + Re c, Im c], [Im c, a - Re c]]`: `G = [[S(A_e, Z_e), S(L_e, L_z)], [S(L_e, L_z), S(M_e, M_z)]]`. -/
noncomputable def Gram (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) •
    !![Ae + (Ze θ).re, (Ze θ).im, Le + (Lz θ).re, (Lz θ).im;
       (Ze θ).im, Ae - (Ze θ).re, (Lz θ).im, Le - (Lz θ).re;
       Le + (Lz θ).re, (Lz θ).im, Me + (Mz θ).re, (Mz θ).im;
       (Lz θ).im, Le - (Lz θ).re, (Mz θ).im, Me - (Mz θ).re]

/-- `J₁` (sec_07_middle.tex:72). -/
def J1 : Matrix (Fin 4) (Fin 4) ℝ := !![0, -2, 0, 0; -2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- `J₂` (sec_07_middle.tex:73). -/
def J2 : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, -1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, -1, 0, 0]

/-- `J = λ J₁ + μ J₂` (sec_07_middle.tex:70). -/
def Jmat (lam mu : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := lam • J1 + mu • J2

/-- `K = ½ (P + J P⁻¹ J)` (sec_07_middle.tex:75). -/
noncomputable def Kmat (lam mu : ℝ) (P : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (P + Jmat lam mu * P⁻¹ * Jmat lam mu)

/-- `C_P(θ) = tr(G(θ) K)` (sec_07_middle.tex:75). -/
noncomputable def CP (θ lam mu : ℝ) (P : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := trace (Gram θ * Kmat lam mu P)

/-- The fixed rational matrix `P` (sec_07_middle.tex:91). -/
noncomputable def Pmat : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 10000 : ℝ) •
    !![16946, 3451, -992, 2537; 3451, 30184, 856, -108; -992, 856, 2733, -344; 2537, -108, -344, 879]

/-- The supported objective `F(M) = Q_rel(M) + (4/5) iU(M) - ½ R(M) - C_P(θ)`, with `λ = 4/5`, `μ = ½` and the fixed
`P` (sec_07_middle.tex:89, 102). -/
noncomputable def Ffun (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Qrel θ M + (4 / 5 : ℂ) * (I * Ufun θ M) - (1 / 2 : ℂ) * Rfun θ M - (CP θ (4 / 5) (1 / 2) Pmat : ℂ)

/-- `Φ_F(θ, α, ψ, ω) = Re F(M(α, ψ, ω))`, `F` at the angle `θ` given IN DEGREES (sec_07_middle.tex:120-122). -/
noncomputable def PhiS (θdeg α ψ ω : ℝ) : ℝ := (Ffun (deg θdeg) (chart α ψ ω)).re

/-- `Φ_rel(θ, α, ψ, ω) = Re Q_rel(M(α, ψ, ω))`, `Q_rel` at the angle `θ` given IN DEGREES (sec_07_middle.tex:120-122). -/
noncomputable def PhiP (θdeg α ψ ω : ℝ) : ℝ := (Qrel (deg θdeg) (chart α ψ ω)).re

/-- The box `𝓧 = [0, π/2] x [-π/2, π/2] x [-π, π]` of `(α, ψ, ω)` (sec_07_middle.tex:120). -/
def InX (α ψ ω : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ Real.pi / 2 ∧ -(Real.pi / 2) ≤ ψ ∧ ψ ≤ Real.pi / 2 ∧ -Real.pi ≤ ω ∧ ω ≤ Real.pi

end Robinson
