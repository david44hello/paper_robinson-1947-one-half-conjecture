/-
Robinson/Defs/Grunsky.lean — the Grunsky layer (sec_03_tools.tex:23-79, Sections 5-7): the Grunsky
coefficients, the odd square root, `p = z f'/f`, the vectors `a(s)`, `a_e(s)`, `b_e(s)`, `α(z)`, `β(z)`, the blocks
`O`, `E`, the matrix `C(g)`, the compression `O₂`.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
TRUST SURFACE. No choice: the Grunsky coefficients and the odd root are PREDICATES (`IsGrunskyCoeff g γ`,
`IsOddRoot f h`), and every statement quantifies over them. Sequences are indexed by `n : ℕ` with the value `0`
at the indices the paper does not use (`n = 0`, or the other parity), so `ℓ²` sums run over all of `ℕ`.
-/
import Robinson.Defs.Matrix2

namespace Robinson

open Complex Metric

/-- The quotient under the logarithm in the Grunsky kernel (sec_03_tools.tex:24-26):
`((g(s) - g(t))/(s - t)) · (s/g(s)) · (t/g(t))`, where the first factor is extended by `g'(s)` on the diagonal and
`s/g(s)` by `1` at `s = 0`. -/
noncomputable def kernelQuot (g : ℂ → ℂ) (s t : ℂ) : ℂ :=
  (if s = t then deriv g s else (g s - g t) / (s - t)) * (if s = 0 then 1 else s / g s) *
    (if t = 0 then 1 else t / g t)

/-- The double power series `∑_{n,m} γ_{nm} sⁿ tᵐ` (sec_03_tools.tex:26). -/
noncomputable def kser (γ : ℕ → ℕ → ℂ) (s t : ℂ) : ℂ := ∑' nm : ℕ × ℕ, γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2

/-- `γ` are the Grunsky coefficients of `g` (sec_03_tools.tex:24-28): `γ_{nm} = 0` when `n = 0` or `m = 0`, and for
all `s, t ∈ 𝔻` the double series `∑ γ_{nm} sⁿ tᵐ` converges absolutely and its exponential is `kernelQuot g s t`.
(Its sum is then continuous on the connected bidisc and `0` at the origin, so it IS the kernel `K_g` built from the
"logarithms that are holomorphic on 𝔻 × 𝔻 (or 𝔻) and vanish at the origin", and `γ` is unique.) -/
def IsGrunskyCoeff (g : ℂ → ℂ) (γ : ℕ → ℕ → ℂ) : Prop :=
  (∀ n m : ℕ, n = 0 ∨ m = 0 → γ n m = 0) ∧
    ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖) ∧ exp (kser γ s t) = kernelQuot g s t

/-- The Grunsky matrix `C(g) = (√(nm) γ_{nm})_{n,m ≥ 1}` (sec_03_tools.tex:30). -/
noncomputable def Cmat (γ : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ := (Real.sqrt ((n : ℝ) * m) : ℂ) * γ n m

/-- The bilinear form `xᵀ A y = ∑ₙ xₙ ∑ₘ Aₙₘ yₘ` on sequences (sec_03_tools.tex:36), as iterated sums. -/
noncomputable def bilinf (x : ℕ → ℂ) (A : ℕ → ℕ → ℂ) (y : ℕ → ℂ) : ℂ := ∑' n : ℕ, x n * ∑' m : ℕ, A n m * y m

/-- `h` is the odd square root of `f` (sec_03_tools.tex:41-43): holomorphic on `𝔻`, odd, `h(s)² = f(s²)`, and
`h'(0) = 1` (the branch with `h(s) = s exp(½ log(f(s²)/s²))`, the logarithm vanishing at `s = 0`). -/
def IsOddRoot (f h : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ h (ball 0 1) ∧ (∀ s ∈ ball (0 : ℂ) 1, h (-s) = -h s) ∧
    (∀ s ∈ ball (0 : ℂ) 1, h s ^ 2 = f (s ^ 2)) ∧ deriv h 0 = 1

/-- `p(z) = z f'(z)/f(z)`, with its value `1` at `z = 0` (sec_03_tools.tex:49-51). -/
noncomputable def pfun (f : ℂ → ℂ) (z : ℂ) : ℂ := if z = 0 then 1 else z * deriv f z / f z

/-- `a(s) = (sⁿ/√n)_{n odd}` (sec_03_tools.tex:45). -/
noncomputable def aOdd (s : ℂ) (n : ℕ) : ℂ := if n % 2 = 1 then s ^ n / (Real.sqrt n : ℂ) else 0

/-- `a_e(s) = (sⁿ/√n)_{n even}`, `n ≥ 2` (sec_03_tools.tex:45). -/
noncomputable def aEven (s : ℂ) (n : ℕ) : ℂ := if n % 2 = 0 ∧ n ≠ 0 then s ^ n / (Real.sqrt n : ℂ) else 0

/-- `b_e(s) = (√n sⁿ)_{n even}`, `n ≥ 2` (sec_07_middle.tex:16). -/
noncomputable def bEven (s : ℂ) (n : ℕ) : ℂ := if n % 2 = 0 ∧ n ≠ 0 then (Real.sqrt n : ℂ) * s ^ n else 0

/-- `α(z) = (zⁿ/√n)_{n ≥ 1}` (sec_03_tools.tex:67). -/
noncomputable def alphaV (z : ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else z ^ n / (Real.sqrt n : ℂ)

/-- `β(z) = (√n zⁿ)_{n ≥ 1}` (sec_06_far.tex:57). -/
noncomputable def betaV (z : ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else (Real.sqrt n : ℂ) * z ^ n

/-- The odd block `O` of the Grunsky matrix (odd indices; `0` elsewhere) (sec_03_tools.tex:43). -/
noncomputable def Oblock (γ : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ := if n % 2 = 1 ∧ m % 2 = 1 then Cmat γ n m else 0

/-- The even block `E` of the Grunsky matrix (even indices `≥ 2`; `0` elsewhere) (sec_03_tools.tex:43). -/
noncomputable def Eblock (γ : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ :=
  if n % 2 = 0 ∧ n ≠ 0 ∧ m % 2 = 0 ∧ m ≠ 0 then Cmat γ n m else 0

/-- `u = Re a(s)`, `v = Im a(s)` at `s = s_θ` (sec_05_grunsky_q.tex:13), as real sequences. -/
noncomputable def uvec (θ : ℝ) (n : ℕ) : ℝ := (aOdd (sθ θ) n).re

/-- See `uvec`. -/
noncomputable def vvec (θ : ℝ) (n : ℕ) : ℝ := (aOdd (sθ θ) n).im

/-- The two orthonormal columns of `V` from Gram–Schmidt on `u, v` (sec_05_grunsky_q.tex:13):
`e₁ = u/l₁₁`, `e₂ = (v - l₂₁ e₁)/l₂₂`. -/
noncomputable def Vcol (θ : ℝ) (j : Fin 2) (n : ℕ) : ℝ :=
  if j = 0 then uvec θ n / l11 θ else (vvec θ n - l21 θ * (uvec θ n / l11 θ)) / l22 θ

/-- The compression `O₂ = Vᵀ O V` of the odd block (sec_05_grunsky_q.tex:15), `γ` the Grunsky coefficients of the
odd root `h` of `f`. -/
noncomputable def O2 (γ : ℕ → ℕ → ℂ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => bilinf (fun n => (Vcol θ i n : ℂ)) (Oblock γ) (fun n => (Vcol θ j n : ℂ))

/-- The four real columns `u_e, v_e, β₀, β₁` of `𝒲` (sec_07_middle.tex:50, 54): `a_e(s) = u_e + i v_e`,
`b_e(s) = β₀ + i β₁` at `s = s_θ`. -/
noncomputable def wEven (θ : ℝ) (j : Fin 4) (n : ℕ) : ℝ :=
  ![(aEven (sθ θ) n).re, (aEven (sθ θ) n).im, (bEven (sθ θ) n).re, (bEven (sθ θ) n).im] j

/-- `σ₊ = (A_o + |Z_o|)/2` (sec_06_far.tex:16). -/
noncomputable def sigP (θ : ℝ) : ℝ := (Ao + ‖Zo θ‖) / 2

/-- `σ₋ = (A_o - |Z_o|)/2` (sec_06_far.tex:16). -/
noncomputable def sigM (θ : ℝ) : ℝ := (Ao - ‖Zo θ‖) / 2

/-- `d = 4√(σ₊σ₋)` (sec_06_far.tex:16). -/
noncomputable def dFar (θ : ℝ) : ℝ := 4 * Real.sqrt (sigP θ * sigM θ)

/-- `φ = arg Z_o` (sec_06_far.tex:14). -/
noncomputable def phiFar (θ : ℝ) : ℝ := Complex.arg (Zo θ)

end Robinson
