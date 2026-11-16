/-
Robinson/NotFormalized.lean — published facts from areas that Lean's library (Mathlib) lacks entirely.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
Each fact is an ordinary proposition `def Fact… : Prop`, never a Lean postulate. A claim whose proof uses one takes it as an
explicit hypothesis and is PROVED GIVEN that fact; the fact itself is "not formalized". Each is stated exactly as
the paper uses it, and is true in full generality as typed.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Grunsky

namespace Robinson

open Complex Metric

/-- `G` is holomorphic on a neighbourhood of the closed disc `|z| ≤ ρ` (sec_02_reduction.tex:26). -/
def HolomorphicNearClosedDisc (G : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ closedBall (0 : ℂ) ρ ⊆ U ∧ DifferentiableOn ℂ G U

/-- The winding number about `c` of the image curve `J = G(|z| = ρ)`, as the contour integral
`(2πi)⁻¹ ∮_{|z| = ρ} G'(z) / (G(z) - c) dz` (sec_02_reduction.tex:30 `ind_J(c)`; for the image curve
`Γ = G ∘ γ` this integral is `n(Γ, c) = (2πi)⁻¹ ∫_Γ dζ / (ζ - c)`). -/
noncomputable def windingImage (G : ℂ → ℂ) (ρ : ℝ) (c : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ * circleIntegral (fun z => deriv G z / (G z - c)) 0 ρ

/-- NOT FORMALIZED: no argument principle in Lean's library. The argument principle [Ahl79, Chapter 4,
Section 5.2] as sec_02_reduction.tex:30 uses it: if `G` is holomorphic on a neighbourhood of `|z| ≤ ρ` and `G - c`
has no zero on the circle `|z| = ρ`, then `G - c` has finitely many zeros in `|z| < ρ`, each of finite order, and
their number counted with multiplicity, `N(c)`, equals the winding number `ind_J(c)` of the image curve about `c`. -/
def FactArgumentPrinciple : Prop :=
  ∀ (G : ℂ → ℂ) (ρ : ℝ) (c : ℂ), 0 < ρ → HolomorphicNearClosedDisc G ρ →
    (∀ z ∈ sphere (0 : ℂ) ρ, G z ≠ c) →
    ∃ Z : Finset ℂ, (∀ z : ℂ, z ∈ Z ↔ z ∈ ball (0 : ℂ) ρ ∧ G z = c) ∧
      (∀ z ∈ Z, analyticOrderAt (fun x => G x - c) z ≠ ⊤) ∧
      (((∑ z ∈ Z, (analyticOrderAt (fun x => G x - c) z).toNat : ℕ) : ℂ) = windingImage G ρ c)

/-- NOT FORMALIZED: no Jordan curve theorem in Lean's library. The Jordan curve theorem with winding numbers, as
sec_02_reduction.tex:30 uses it: if `G` is holomorphic on a neighbourhood of `|z| ≤ ρ` and injective on the circle
`|z| = ρ`, then its image `J` is a Jordan curve; `ℂ \ J` is the disjoint union of a bounded component `Ω` and an
unbounded component `Ω'` (connected open sets); `J` is the boundary of `Ω'`; `ind_J = 0` on `Ω'`, and `ind_J` is
constant on `Ω`, with value `1` or `-1`. Sources, as sec_02_reduction.tex:30 cites them: [HS18, Corollaries 1.4 and 1.6]
(Hemasundar and Simha: the two components, and `J` is the boundary of each), [Ahl79, Chapter 4, Section 2.1] (the
winding number is `0` on the unbounded component and constant on each component) and [HS18, Theorem 3.2] (its value
on `Ω` is `1` or `-1`). -/
def FactJordanCurve : Prop :=
  ∀ (G : ℂ → ℂ) (ρ : ℝ), 0 < ρ → HolomorphicNearClosedDisc G ρ → Set.InjOn G (sphere (0 : ℂ) ρ) →
    ∃ Ω Ω' : Set ℂ, IsOpen Ω ∧ IsOpen Ω' ∧ IsConnected Ω ∧ IsConnected Ω' ∧ Disjoint Ω Ω' ∧
      Ω ∪ Ω' = (G '' sphere (0 : ℂ) ρ)ᶜ ∧ Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded Ω' ∧
      frontier Ω' = G '' sphere (0 : ℂ) ρ ∧
      (∀ c ∈ Ω', windingImage G ρ c = 0) ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c ∈ Ω, windingImage G ρ c = (ε : ℂ)

/-- NOT FORMALIZED: no univalent-function theory in Lean's library. De Branges' theorem [deB85], as
sec_03_tools.tex:13-16 states it: the coefficients of every `f(z) = z + ∑_{n ≥ 2} a_n z^n` in `𝒮` satisfy
`|a_n| ≤ n` for `n ≥ 2`. -/
def FactDeBranges : Prop :=
  ∀ f : ℂ → ℂ, InS f → ∀ n : ℕ, 2 ≤ n → ‖coeff f n‖ ≤ (n : ℝ)

/-- NOT FORMALIZED: no univalent-function theory in Lean's library. The area theorem of Gronwall [Gro14],
[Dur83, Chapter 2], as sec_03_tools.tex:17-20 states it: if `g(ζ) = ζ + b₀ + ∑_{n ≥ 1} b_n ζ^{-n}` is holomorphic
and injective in `|ζ| > 1`, then `∑_{n ≥ 1} n |b_n|² ≤ 1`. -/
def FactArea : Prop :=
  ∀ (g : ℂ → ℂ) (b : ℕ → ℂ), DifferentiableOn ℂ g {ζ : ℂ | 1 < ‖ζ‖} → Set.InjOn g {ζ : ℂ | 1 < ‖ζ‖} →
    (∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℕ => b n * (ζ ^ n)⁻¹) (g ζ - ζ)) →
    Summable (fun n : ℕ => (n : ℝ) * ‖b n‖ ^ 2) ∧ ∑' n : ℕ, (n : ℝ) * ‖b n‖ ^ 2 ≤ 1

/-- NOT FORMALIZED: no univalent-function theory in Lean's library. The strong Grunsky inequality [Gru39],
[Pom75, Theorem 3.1], as sec_03_tools.tex:28-35 states it: for `g ∈ 𝒮` the matrix `C(g) = (√(nm) γ_{nm})` is an
operator on `ℓ²` of norm at most `1`; in the bilinear form (eq:cauchy) `|xᵀ C(g) y| ≤ ‖x‖ ‖y‖`, here for every finite
section (`x, y` supported on `n < N`, every `N`), which is equivalent to the norm bound. -/
def FactGrunsky : Prop :=
  ∀ (g : ℂ → ℂ) (γ : ℕ → ℕ → ℂ), InS g → IsGrunskyCoeff g γ →
    ∀ (N : ℕ) (x y : ℕ → ℂ),
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Cmat γ n m * y m‖ ≤
        Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2)

/-- NOT FORMALIZED: no holomorphic functions of several variables in Lean's library. The power series of a
holomorphic function on the bidisc (Osgood's lemma and the Cauchy formula on a polydisc), as sec_03_tools.tex:24-28
uses it for the Grunsky kernel: a function continuous on `𝔻 x 𝔻` and holomorphic in each variable separately is the
sum of a double power series `∑ c_{nm} sⁿ tᵐ` that converges absolutely on all of `𝔻 x 𝔻`. Source, as
sec_03_tools.tex:28 cites it: [Hor90, Section 2.2] (Hörmander). -/
def FactBidiscPowerSeries : Prop :=
  ∀ L : ℂ × ℂ → ℂ, ContinuousOn L (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) →
    (∀ t ∈ ball (0 : ℂ) 1, DifferentiableOn ℂ (fun s => L (s, t)) (ball (0 : ℂ) 1)) →
    (∀ s ∈ ball (0 : ℂ) 1, DifferentiableOn ℂ (fun t => L (s, t)) (ball (0 : ℂ) 1)) →
    ∃ c : ℕ → ℕ → ℂ, ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖) ∧
        L (s, t) = ∑' nm : ℕ × ℕ, c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2

end Robinson
