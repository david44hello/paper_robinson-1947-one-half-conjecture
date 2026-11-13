/-
Robinson/Defs/NearP.lean — the power-series objects of Section 4 that depend on `f` (the coefficients
`b_{2j-1}` of `G_τ`, the series `Π`, `Π_o`, `Υ`, `T`, the first variation `Ṫ`) and the majorant calculus.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
TRUST SURFACE: every definition is to be compared with sec_04_near.tex (its lines; AUDIT_NOTES.md names the version).
Coefficients of a function at
`0` are `coeff g n = iteratedDeriv n g 0 / n!` (Robinson/Defs/Basic.lean); a sequence `p : ℕ → ℂ` stands for the
coefficients `(π_n)` of a power series.
-/
import Robinson.Defs.Near

namespace Robinson

open Complex Metric

/-! ## The Koebe transform at `-τ` and its square-root quotient -/

/-- The Koebe transform `f_{-τ}` (sec_04_near.tex:53-55). -/
noncomputable def fT (f : ℂ → ℂ) (τ : ℝ) : ℂ → ℂ := koebeTransform f (-(τ : ℂ))

/-- `c = A/2`, where `A` is the second coefficient of `f_{-τ}` (sec_04_near.tex:57). -/
noncomputable def cOf (f : ℂ → ℂ) (τ : ℝ) : ℂ := coeff (fT f τ) 2 / 2

/-- `φ` is the square root of `u/g(u)` on `𝔻` with `φ(0) = 1`, i.e. `g(u) φ(u)² = u`. For `g = f_{-τ}` this is
`φ(u) = 1 - cu + ∑_{j ≥ 2} b_{2j-1} u^j`, so that `f_{-τ}(u) = u (1 - cu + ∑ b_{2j-1} u^j)^{-2}` (sec_04_near.tex:81)
and `G_τ(ζ) = (f_{-τ}(ζ⁻²))^{-1/2} = ζ φ(ζ⁻²)` (sec_04_near.tex:63). The coefficients are `b_{2j-1} = coeff φ j`. -/
def IsSqrtQuot (g φ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ φ (ball (0 : ℂ) 1) ∧ φ 0 = 1 ∧ ∀ u ∈ ball (0 : ℂ) 1, g u * φ u ^ 2 = u

/-- `G_τ(ζ) = ζ φ(ζ⁻²)` (sec_04_near.tex:63). -/
noncomputable def Gtau (φ : ℂ → ℂ) (ζ : ℂ) : ℂ := ζ * φ ((ζ ^ 2)⁻¹)

/-- The coefficients of `G_τ(ζ) - ζ = -cζ⁻¹ + ∑_{j ≥ 2} b_{2j-1} ζ^{1-2j}` in powers `ζ^{-n}` (sec_04_near.tex:63):
`-c` at `n = 1`, `b_{2j-1} = coeff φ j` at `n = 2j - 1 ≥ 3`, `0` at even `n`. -/
noncomputable def Glaurent (c : ℂ) (φ : ℂ → ℂ) (n : ℕ) : ℂ :=
  if n = 1 then -c else if n % 2 = 1 then coeff φ ((n + 1) / 2) else 0

/-! ## `Π`, `N`, `L`, `B` and the quantities of Lemma 4.2 -/

/-- `Π(ξ) = (f(-τ + ξ) - f(-τ))/f'(-τ)` (sec_04_near.tex:77); `π_n = coeff (PiF f τ) n`. -/
noncomputable def PiF (f : ℂ → ℂ) (τ : ℝ) (ξ : ℂ) : ℂ :=
  (f (-(τ : ℂ) + ξ) - f (-(τ : ℂ))) / deriv f (-(τ : ℂ))

/-- `N(ξ) = ξ(1 + βξ)` (sec_04_near.tex:81). -/
noncomputable def Nfun (τ : ℝ) (ξ : ℂ) : ℂ := ξ * (1 + (βτ τ : ℂ) * ξ)

/-- `B(ξ) = ∑_{j ≥ 2} b_{2j-1} ξ^j / (v (v + τξ)^{j-1})` with `b_{2j-1} = coeff φ j` (sec_04_near.tex:81). -/
noncomputable def Bser (τ : ℝ) (φ : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  ∑' j : ℕ, if 2 ≤ j then coeff φ j * ξ ^ j / ((vτ τ : ℂ) * ((vτ τ : ℂ) + (τ : ℂ) * ξ) ^ (j - 1)) else 0

/-- `L(ξ) = 1 - νξ + B(ξ)` (sec_04_near.tex:81). -/
noncomputable def Lfun (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (ξ : ℂ) : ℂ := 1 - nuτ τ c * ξ + Bser τ φ ξ

/-- `Π_o` from coefficients `p`: `∑_{m ≥ 0} p_{2m+1} ξ^{2m}`, which is `(Π(ξ) - Π(-ξ))/(2ξ)` (Lemma 4.2,
sec_04_near.tex:86). -/
noncomputable def PiOddSer (p : ℕ → ℂ) (ξ : ℂ) : ℂ := ∑' m : ℕ, p (2 * m + 1) * ξ ^ (2 * m)

/-- `Υ` from coefficients `p`, with the coefficient `p2` given separately (it is kept fixed in Lemma 4.4(i)):
`∑_{j ≥ 1} [(2j + 2τp2) p_{2j+1} - 2τ(j+1) p_{2j+2}] ξ^{2j-2}` (Lemma 4.2, sec_04_near.tex:88). -/
noncomputable def UpsLin (τ : ℝ) (p2 : ℂ) (p : ℕ → ℂ) (ξ : ℂ) : ℂ :=
  ∑' j : ℕ, if 1 ≤ j then
    ((2 * (j : ℂ) + 2 * (τ : ℂ) * p2) * p (2 * j + 1) - 2 * (τ : ℂ) * ((j : ℂ) + 1) * p (2 * j + 2)) *
      ξ ^ (2 * j - 2) else 0

/-- `Υ(ξ)` of Lemma 4.2 (sec_04_near.tex:88): `UpsLin` with `p2 = p₂`. -/
noncomputable def UpsSer (τ : ℝ) (p : ℕ → ℂ) (ξ : ℂ) : ℂ := UpsLin τ (p 2) p ξ

/-- `T = Υ(iy)/Π_o(iy)` (sec_04_near.tex:92), `y = √(¼ - τ²)`. -/
noncomputable def Tser (τ : ℝ) (p : ℕ → ℂ) : ℂ := UpsSer τ p (xiτ τ) / PiOddSer p (xiτ τ)

/-! ## The first variation (sec_04_near.tex:212-216) -/

/-- The intermediate function with `B` replaced by `λB`: `N/(1 - νξ + λB)²` (sec_04_near.tex:212). -/
noncomputable def PiLam (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (lam : ℂ) (ξ : ℂ) : ℂ :=
  Nfun τ ξ / (1 - nuτ τ c * ξ + lam * Bser τ φ ξ) ^ 2

/-- `Ṫ = ∑_{j ≥ 2} b_{2j-1} T_j` (sec_04_near.tex:216), with `T_j` the closed form of Lemma 4.5(i) (`TJ`). -/
noncomputable def Tdot (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) : ℂ :=
  ∑' j : ℕ, if 2 ≤ j then coeff φ j * TJ τ c j else 0

/-! ## Majorants (sec_04_near.tex:159-169) -/

/-- `F ≪ Z`: `|F_n| ≤ [xⁿ]Z` for every `n` (sec_04_near.tex:159), on coefficient sequences. -/
def Majorizes (F : ℕ → ℂ) (Z : ℕ → ℝ) : Prop := ∀ n, ‖F n‖ ≤ Z n

/-- The coefficients of the product of two power series (Cauchy product). -/
noncomputable def cmul {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- `𝔥[Z](x) = ∑_{j ≥ 1} Z_{2j+1} x^{2j}`, the coefficient form of `(Z(x) - Z(-x))/(2x)` (sec_04_near.tex:166). -/
noncomputable def hCoef (Z : ℕ → ℝ) (x : ℝ) : ℝ := ∑' j : ℕ, if 1 ≤ j then Z (2 * j + 1) * x ^ (2 * j) else 0

/-- `𝔴[Z](x) = ∑_{j ≥ 1} [(2j + 10/3) Z_{2j+1} + (j+1) Z_{2j+2}] x^{2j-2}` (sec_04_near.tex:167). -/
noncomputable def wCoef (Z : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, if 1 ≤ j then
    ((2 * (j : ℝ) + 10 / 3) * Z (2 * j + 1) + ((j : ℝ) + 1) * Z (2 * j + 2)) * x ^ (2 * j - 2) else 0

/-- `𝔥[Z](x) = (Z(x) - Z(-x))/(2x)` for a function `Z`, at a general point `x` (sec_04_near.tex:161). -/
noncomputable def frakHat (Z : ℝ → ℝ) (x : ℝ) : ℝ := oddPart Z x / x

/-- `𝔴[Z](x) = (x Z_o'(x) + (7/3) Z_o(x))/x³ + Z_e'(x)/(2x³)` at a general point `x` (sec_04_near.tex:162). -/
noncomputable def frakWat (Z : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x * deriv (oddPart Z) x + 7 / 3 * oddPart Z x) / x ^ 3 + deriv (evenPart Z) x / (2 * x ^ 3)

/-- `B₁` as a function on `ℂ` (for its power-series coefficients; Lemma 4.4(iii), sec_04_near.tex:178). -/
noncomputable def B1c (x : ℂ) : ℂ := 16 / 15 * (x ^ 2 / (1 - 2 * x))

/-- `B₂` as a function on `ℂ` (Lemma 4.4(iii), sec_04_near.tex:179). -/
noncomputable def B2c (x : ℂ) : ℂ :=
  256 / 243 * (x ^ 4 / (1 - 2 / 3 * x) ^ 2) + 4096 / 3645 * (x ^ 5 / ((1 - 2 / 3 * x) ^ 2 * (1 - 2 * x)))

end Robinson
