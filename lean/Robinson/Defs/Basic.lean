/-
Robinson/Defs/Basic.lean — the basic objects of the paper.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
TRUST SURFACE: every definition here is to be compared with the paper, line by line. Pointers are lines of the paper's
TeX sources (`sec_0N_*.tex:<line>`); AUDIT_NOTES.md names the version. A function `f : ℂ → ℂ` stands for a function
on the unit disc: only its values on `ball 0 1` enter the class `S`, and `deriv f z` at a point of the open disc
depends only on values near `z`.
-/
import Mathlib

namespace Robinson

open Complex Metric

/-- The class `𝒮` (sec_01_intro.tex:5): `f` is holomorphic and injective on the unit disc `𝔻 = {|z| < 1}`, with
`f 0 = 0` and `f' 0 = 1`, that is `f(z) = z + a₂ z² + a₃ z³ + ⋯` in `𝔻`. -/
structure InS (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (ball 0 1)
  injOn : Set.InjOn f (ball 0 1)
  map_zero : f 0 = 0
  deriv_zero : deriv f 0 = 1

/-- `Γ f (z) = (f(z) + z f'(z)) / 2` (sec_01_intro.tex:7). -/
noncomputable def Gam (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z + z * deriv f z) / 2

/-- `Q_f(z, w) = 1 + (z f'(z) - w f'(w)) / (f(z) - f(w))` (sec_02_reduction.tex:7; sec_01_intro.tex:19). The paper
uses it for distinct `z, w ∈ 𝔻`, where `f(z) ≠ f(w)`. -/
noncomputable def Q (f : ℂ → ℂ) (z w : ℂ) : ℂ := 1 + (z * deriv f z - w * deriv f w) / (f z - f w)

/-- `z_θ = ½ e^{iθ/2}` (sec_02_reduction.tex:49). -/
noncomputable def zθ (θ : ℝ) : ℂ := (1 / 2 : ℂ) * exp (((θ / 2 : ℝ) : ℂ) * I)

/-- The Koebe function `k(z) = z / (1 - z)²` (sec_01_intro.tex:9). -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- The rotation `f_φ(z) = e^{-iφ} f(e^{iφ} z)` (sec_02_reduction.tex:40). -/
noncomputable def rotate (φ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  exp (-((φ : ℂ) * I)) * f (exp ((φ : ℂ) * I) * z)

/-- The dilation `F(u) = f(2ru) / (2r)` (sec_02_reduction.tex:40). -/
noncomputable def dilate (r : ℝ) (f : ℂ → ℂ) (u : ℂ) : ℂ := f (2 * (r : ℂ) * u) / (2 * (r : ℂ))

/-- The Koebe transform `f_a(u) = (f((u + a)/(1 + ā u)) - f(a)) / ((1 - |a|²) f'(a))` (sec_03_tools.tex:11). -/
noncomputable def koebeTransform (f : ℂ → ℂ) (a : ℂ) (u : ℂ) : ℂ :=
  (f ((u + a) / (1 + (starRingEnd ℂ) a * u)) - f a) / (((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * deriv f a)

/-- The Taylor coefficient `a_n` of `f` at `0`: `f^{(n)}(0) / n!` (sec_01_intro.tex:5, 9; sec_03_tools.tex:13). -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- `θ₀ = 2 arcsin(17/40)` (sec_04_near.tex:22; sec_08_proof.tex:5). -/
noncomputable def θ₀ : ℝ := 2 * Real.arcsin (17 / 40)

/-- An angle given in degrees, in radians: `x° = x π / 180` (sec_02_reduction.tex:51 "We measure θ in degrees when
we name intervals of angles"). -/
noncomputable def deg (x : ℝ) : ℝ := x * Real.pi / 180

end Robinson
