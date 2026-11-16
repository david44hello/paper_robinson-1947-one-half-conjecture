/-
Robinson/Defs/Near.lean — the explicit objects of Section 4 (nearby pairs): functions of `τ` and of the
second-coefficient parameter `c`, and the cell data of Lemma 4.8.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
TRUST SURFACE: every definition is read against sec_04_near.tex (its lines; AUDIT_NOTES.md names the version). `y` is
`√(¼ - τ²)` (the pair is `-τ ± iy`, sec_04_near.tex:38).
-/
import Robinson.Defs.Basic

namespace Robinson

open Complex

/-- `y₀ = 17/80` (sec_04_near.tex:46). -/
noncomputable def y0 : ℝ := 17 / 80

/-- `Ψ = 1 - τ²` (sec_04_near.tex:50; Lemma 4.3, sec_04_near.tex:127). -/
noncomputable def vτ (τ : ℝ) : ℝ := 1 - τ ^ 2

/-- `τ₁ = τ / Ψ` (sec_04_near.tex:50). -/
noncomputable def βτ (τ : ℝ) : ℝ := τ / vτ τ

/-- `y² = ¼ - τ²` (sec_04_near.tex:38, 127). -/
noncomputable def ysq (τ : ℝ) : ℝ := 1 / 4 - τ ^ 2

/-- `y = √(¼ - τ²)` (sec_04_near.tex:38). -/
noncomputable def yτ (τ : ℝ) : ℝ := Real.sqrt (ysq τ)

/-- `ν = (c - τ)/Ψ` (sec_04_near.tex:83, 127). -/
noncomputable def nuτ (τ : ℝ) (c : ℂ) : ℂ := (c - τ) / (vτ τ : ℂ)

/-- `D = 2(1 - 2τc)/Ψ` (sec_04_near.tex:86, 127). -/
noncomputable def Dτ (τ : ℝ) (c : ℂ) : ℂ := 2 * (1 - 2 * τ * c) / (vτ τ : ℂ)

/-- `Q̂(τ, c) = (Q_0 - y²(6ν² + 8τ₁ν - 4τν³ - 6ττ₁ν²)) / ((1 + ν²y²)(1 - ν(ν + 2τ₁)y²))` (sec_04_near.tex:116, 129). -/
noncomputable def Qhat (τ : ℝ) (c : ℂ) : ℂ :=
  let ν := nuτ τ c
  let β : ℂ := βτ τ
  let y2 : ℂ := ysq τ
  (Dτ τ c - y2 * (6 * ν ^ 2 + 8 * β * ν - 4 * τ * ν ^ 3 - 6 * τ * β * ν ^ 2)) /
    ((1 + ν ^ 2 * y2) * (1 - ν * (ν + 2 * β) * y2))

/-- `Π̂_o(iy) = (1 - ν(ν + 2τ₁)y²) / (1 + ν²y²)²` (sec_04_near.tex:115). -/
noncomputable def PihatO (τ : ℝ) (c : ℂ) : ℂ :=
  let ν := nuτ τ c
  (1 - ν * (ν + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)) / (1 + ν ^ 2 * (ysq τ : ℂ)) ^ 2

/-- `T̂ = (-4τν³ + (6 + 2τ²/Ψ)ν² + (4τ/Ψ²)ν - Q_0(ν⁴ + 2τ₁ν³)y²) / (1 - 2τ₁νy² - (ν⁴ + 2τ₁ν³)y⁴)` (sec_04_near.tex:117). -/
noncomputable def That (τ : ℝ) (c : ℂ) : ℂ :=
  let ν := nuτ τ c
  let β : ℂ := βτ τ
  let v : ℂ := vτ τ
  let y2 : ℂ := ysq τ
  (-4 * τ * ν ^ 3 + (6 + 2 * τ ^ 2 / v) * ν ^ 2 + 4 * τ / v ^ 2 * ν - Dτ τ c * (ν ^ 4 + 2 * β * ν ^ 3) * y2) /
    (1 - 2 * β * ν * y2 - (ν ^ 4 + 2 * β * ν ^ 3) * y2 ^ 2)

/-- The Koebe value `Q_k(τ) = (½ - τ) / (¾ (5/4 + 2τ))` (sec_04_near.tex:122, 130). -/
noncomputable def Qk (τ : ℝ) : ℝ := (1 / 2 - τ) / ((3 / 4) * (5 / 4 + 2 * τ))

/-- `m(ρ) = 22/25 + (21/100) ρ` (sec_04_near.tex:134). -/
noncomputable def mρ (ρ : ℝ) : ℝ := 22 / 25 + 21 / 100 * ρ

/-- `e = 2(1 - Re c)` (sec_04_near.tex:59, 132). -/
noncomputable def edef (c : ℂ) : ℝ := 2 * (1 - c.re)

/-- `η = 1 - |c|²` (sec_04_near.tex:59, 132). -/
noncomputable def etadef (c : ℂ) : ℝ := 1 - ‖c‖ ^ 2

/-- `ξ = iy` (Lemma 4.5(i), sec_04_near.tex:220). -/
noncomputable def xiτ (τ : ℝ) : ℂ := I * (yτ τ : ℂ)

/-- `Π̂(ξ) = ξ(1 + τ₁ξ)/(1 - νξ)²` (Lemma 4.5(i), sec_04_near.tex:220). -/
noncomputable def Pihat (τ : ℝ) (c : ℂ) (ξ : ℂ) : ℂ := ξ * (1 + (βτ τ : ℂ) * ξ) / (1 - nuτ τ c * ξ) ^ 2

/-- `Π_j(ξ) = -2 ξ^{j+1} (1 + τ₁ξ)^{2-j} / (Ψ^j (1 - νξ)³)` (Lemma 4.5(i), sec_04_near.tex:222). -/
noncomputable def PiJ (τ : ℝ) (c : ℂ) (j : ℕ) (ξ : ℂ) : ℂ :=
  -2 * ξ ^ (j + 1) * (1 + (βτ τ : ℂ) * ξ) ^ ((2 : ℤ) - j) / ((vτ τ : ℂ) ^ j * (1 - nuτ τ c * ξ) ^ 3)

/-- `T_j = -(1/y²) · ((-τ + ξ)Π_j'(ξ) + (τ + ξ)Π_j'(-ξ) - (Q̂(τ, c) - 1)(Π_j(ξ) - Π_j(-ξ))) / (Π̂(ξ) - Π̂(-ξ))` at
`ξ = iy` (Lemma 4.5(i), sec_04_near.tex:223). -/
noncomputable def TJ (τ : ℝ) (c : ℂ) (j : ℕ) : ℂ :=
  (-1 / (ysq τ : ℂ)) *
    (((-(τ : ℂ) + xiτ τ) * deriv (PiJ τ c j) (xiτ τ) + ((τ : ℂ) + xiτ τ) * deriv (PiJ τ c j) (-xiτ τ) -
        (Qhat τ c - 1) * (PiJ τ c j (xiτ τ) - PiJ τ c j (-xiτ τ))) /
      (Pihat τ c (xiτ τ) - Pihat τ c (-xiτ τ)))

/-! ## The numbers of Lemma 4.8 (sec_04_near.tex:296-323), in the printed order -/

/-- `N₊(x) = x(1 + ⅔x)` (sec_04_near.tex:297). -/
noncomputable def Nplus (x : ℝ) : ℝ := x * (1 + 2 / 3 * x)

/-- `B₁(x) = (16/15) x²/(1 - 2x)` (sec_04_near.tex:299). -/
noncomputable def B1 (x : ℝ) : ℝ := 16 / 15 * (x ^ 2 / (1 - 2 * x))

/-- `B₂(x) = (256/243) x⁴/(1 - ⅔x)² + (4096/3645) x⁵/((1 - ⅔x)²(1 - 2x))` (sec_04_near.tex:300). -/
noncomputable def B2 (x : ℝ) : ℝ :=
  256 / 243 * (x ^ 4 / (1 - 2 / 3 * x) ^ 2) + 4096 / 3645 * (x ^ 5 / ((1 - 2 / 3 * x) ^ 2 * (1 - 2 * x)))

/-- `ς(y) = 16y²/(3(1 - 4y²)²) + 4y²/(1 - 4y²)` (Lemma 4.4(ii), sec_04_near.tex:175). -/
noncomputable def epsOf (y : ℝ) : ℝ := 16 * y ^ 2 / (3 * (1 - 4 * y ^ 2) ^ 2) + 4 * y ^ 2 / (1 - 4 * y ^ 2)

/-- `ς = ς(y₀)` (sec_04_near.tex:302). -/
noncomputable def epsY0 : ℝ := epsOf y0

/-- The odd part `Z_odd(x) = ½(Z(x) - Z(-x))` (sec_04_near.tex:302). -/
noncomputable def oddPart (Z : ℝ → ℝ) (x : ℝ) : ℝ := (Z x - Z (-x)) / 2

/-- The even part `Z_even(x) = ½(Z(x) + Z(-x))` (sec_04_near.tex:302). -/
noncomputable def evenPart (Z : ℝ → ℝ) (x : ℝ) : ℝ := (Z x + Z (-x)) / 2

/-- `𝔥[Z] = Z_odd(y₀)/y₀` (sec_04_near.tex:304). -/
noncomputable def frakH (Z : ℝ → ℝ) : ℝ := oddPart Z y0 / y0

/-- `𝔴[Z] = (y₀ Z_odd'(y₀) + (7/3) Z_odd(y₀))/y₀³ + Z_even'(y₀)/(2y₀³)` (sec_04_near.tex:305). -/
noncomputable def frakW (Z : ℝ → ℝ) : ℝ :=
  (y0 * deriv (oddPart Z) y0 + 7 / 3 * oddPart Z y0) / y0 ^ 3 + deriv (evenPart Z) y0 / (2 * y0 ^ 3)

/-- `ν⁺ = max(20/29, 2 - (8/3)ρ₋)` (sec_04_near.tex:309). -/
noncomputable def nuPlus (ρm : ℝ) : ℝ := max (20 / 29) (2 - 8 / 3 * ρm)

/-- `η⁺ = min(1, 4 max_{ρ₋ ≤ ρ ≤ ρ₊} ρ(1 - ρ))` (sec_04_near.tex:310). -/
noncomputable def etaPlus (ρm ρp : ℝ) : ℝ := min 1 (4 * sSup ((fun ρ => ρ * (1 - ρ)) '' Set.Icc ρm ρp))

/-- `e⁺ = 4(1 - ρ₋)` (sec_04_near.tex:311). -/
noncomputable def ePlus (ρm : ℝ) : ℝ := 4 * (1 - ρm)

/-- The sum `(ν⁺)⁴ + (4/3)(ν⁺)³`, as a function of the cap `ν⁺`; the text writes it out where it occurs
(sec_04_near.tex:183, 208, 313). -/
noncomputable def calVOf (νp : ℝ) : ℝ := νp ^ 4 + 4 / 3 * νp ^ 3

/-- `T⁺` as a function of the cap `ν⁺` (Lemma 4.4(iv), sec_04_near.tex:183; sec_04_near.tex:313). -/
noncomputable def TPlusOf (νp : ℝ) : ℝ :=
  (2 * νp ^ 3 + 20 / 3 * νp ^ 2 + 32 / 9 * νp + 16 / 3 * calVOf νp * y0 ^ 2) /
    (1 - 4 / 3 * νp * y0 ^ 2 - calVOf νp * y0 ^ 4)

/-- `Π̂₋ = (1 - min(20/9, (ν⁺)² + (4/3)ν⁺) y₀²) / (1 + (ν⁺)² y₀²)²` as a function of the cap `ν⁺`
(Lemma 4.4(iv), sec_04_near.tex:184; sec_04_near.tex:314). -/
noncomputable def PihatLowOf (νp : ℝ) : ℝ :=
  (1 - min (20 / 9) (νp ^ 2 + 4 / 3 * νp) * y0 ^ 2) / (1 + νp ^ 2 * y0 ^ 2) ^ 2

/-- `Z₆(x) = (20/33)(4/3)⁶ x⁷ / ((1 - ⅔x)³(1 - 2x)(1 - ν⁺x)³)` as a function of the cap `ν⁺` (Lemma 4.5(ii),
sec_04_near.tex:232; sec_04_near.tex:315). -/
noncomputable def Z6Of (νp : ℝ) (x : ℝ) : ℝ :=
  20 / 33 * (4 / 3) ^ 6 * (x ^ 7 / ((1 - 2 / 3 * x) ^ 3 * (1 - 2 * x) * (1 - νp * x) ^ 3))

/-- `N₆ = (𝔴[Z₆] + T⁺ 𝔥[Z₆]) / Π̂₋` as a function of the cap `ν⁺` (Lemma 4.5(ii), sec_04_near.tex:231). -/
noncomputable def N6Of (νp : ℝ) : ℝ := (frakW (Z6Of νp) + TPlusOf νp * frakH (Z6Of νp)) / PihatLowOf νp

/-- The sum `(ν⁺)⁴ + (4/3)(ν⁺)³` of Lemma 4.8, with `ν⁺ = ν⁺(ρ₋)` (written out in `T⁺`, sec_04_near.tex:313). -/
noncomputable def calV (ρm : ℝ) : ℝ := calVOf (nuPlus ρm)

/-- `T⁺` of Lemma 4.8 (sec_04_near.tex:313). -/
noncomputable def TPlus (ρm : ℝ) : ℝ := TPlusOf (nuPlus ρm)

/-- `Π̂₋` of Lemma 4.8 (sec_04_near.tex:314). -/
noncomputable def PihatLow (ρm : ℝ) : ℝ := PihatLowOf (nuPlus ρm)

/-- `Z₆` of Lemma 4.8 (sec_04_near.tex:315). -/
noncomputable def Z6 (ρm : ℝ) (x : ℝ) : ℝ := Z6Of (nuPlus ρm) x

/-- `N₆ = (𝔴[Z₆] + T⁺ 𝔥[Z₆]) / Π̂₋` (sec_04_near.tex:316). -/
noncomputable def N6 (ρm : ℝ) : ℝ := N6Of (nuPlus ρm)

/-- `M = 20 + N₆²` (sec_04_near.tex:316). -/
noncomputable def Mcap (ρm : ℝ) : ℝ := 20 + N6 ρm ^ 2

/-- `1 - ν⁺x` for a cap `ν⁺` (Lemma 4.6, sec_04_near.tex:254; the text writes it out). -/
noncomputable def faOf (νp : ℝ) (x : ℝ) : ℝ := 1 - νp * x

/-- `𝒴(x) = 1 - ν⁺x - √η⁺ B₁(x)` for caps `ν⁺, η⁺` (Lemma 4.6, sec_04_near.tex:254). -/
noncomputable def fdOf (νp ηp : ℝ) (x : ℝ) : ℝ := faOf νp x - Real.sqrt ηp * B1 x

/-- `Z₁ = N₊ B₁ [1/((1 - ν⁺x)²𝒴) + 1/((1 - ν⁺x)𝒴²)]` for caps `ν⁺, η⁺` (Lemma 4.6, sec_04_near.tex:256). -/
noncomputable def Z1Of (νp ηp : ℝ) (x : ℝ) : ℝ :=
  Nplus x * B1 x * (1 / (faOf νp x ^ 2 * fdOf νp ηp x) + 1 / (faOf νp x * fdOf νp ηp x ^ 2))

/-- `Z₂ = N₊ B₂ [2/((1 - ν⁺x)³𝒴) + 1/((1 - ν⁺x)²𝒴²)]` for caps `ν⁺, η⁺` (Lemma 4.6, sec_04_near.tex:257). -/
noncomputable def Z2Of (νp ηp : ℝ) (x : ℝ) : ℝ :=
  Nplus x * B2 x * (2 / (faOf νp x ^ 3 * fdOf νp ηp x) + 1 / (faOf νp x ^ 2 * fdOf νp ηp x ^ 2))

/-- `Π₋ = max(1 - ς(y₀), Π̂₋ - √η⁺ 𝔥[Z₁])` for caps `ν⁺, η⁺` (Lemma 4.6,
sec_04_near.tex:259). -/
noncomputable def PiLowOf (νp ηp : ℝ) : ℝ :=
  max (1 - epsY0) (PihatLowOf νp - Real.sqrt ηp * frakH (Z1Of νp ηp))

/-- `Λ = (𝔴[Z₂] + T⁺ 𝔥[Z₂] + n⁺ 𝔥[Z₁]) / Π₋` for caps `ν⁺, η⁺, n⁺` (Lemma 4.6, sec_04_near.tex:262). -/
noncomputable def LamOf (νp ηp np : ℝ) : ℝ :=
  (frakW (Z2Of νp ηp) + TPlusOf νp * frakH (Z2Of νp ηp) + np * frakH (Z1Of νp ηp)) / PiLowOf νp ηp

/-- `1 - ν⁺x` (sec_04_near.tex:317; the text writes it out). -/
noncomputable def fa (ρm : ℝ) (x : ℝ) : ℝ := faOf (nuPlus ρm) x

/-- `𝒴(x) = 1 - ν⁺x - √η⁺ B₁(x)` (sec_04_near.tex:317). -/
noncomputable def fd (ρm ρp : ℝ) (x : ℝ) : ℝ := fdOf (nuPlus ρm) (etaPlus ρm ρp) x

/-- `Z₁ = N₊ B₁ [1/((1 - ν⁺x)²𝒴) + 1/((1 - ν⁺x)𝒴²)]` (sec_04_near.tex:318). -/
noncomputable def Z1 (ρm ρp : ℝ) (x : ℝ) : ℝ := Z1Of (nuPlus ρm) (etaPlus ρm ρp) x

/-- `Z₂ = N₊ B₂ [2/((1 - ν⁺x)³𝒴) + 1/((1 - ν⁺x)²𝒴²)]` (sec_04_near.tex:319). -/
noncomputable def Z2 (ρm ρp : ℝ) (x : ℝ) : ℝ := Z2Of (nuPlus ρm) (etaPlus ρm ρp) x

/-- `Π₋ = max(1 - ς, Π̂₋ - √η⁺ 𝔥[Z₁])` (sec_04_near.tex:320). -/
noncomputable def PiLow (ρm ρp : ℝ) : ℝ := PiLowOf (nuPlus ρm) (etaPlus ρm ρp)

/-- `n⁺ = (M + 130e⁺)^{1/2}` (sec_04_near.tex:320). -/
noncomputable def nPlus (ρm : ℝ) : ℝ := Real.sqrt (Mcap ρm + 130 * ePlus ρm)

/-- `Λ = (𝔴[Z₂] + T⁺ 𝔥[Z₂] + n⁺ 𝔥[Z₁]) / Π₋` (sec_04_near.tex:321). -/
noncomputable def Lam (ρm ρp : ℝ) : ℝ := LamOf (nuPlus ρm) (etaPlus ρm ρp) (nPlus ρm)

/-- `δ = (1/y₀²)(22/25 + (21/100)ρ₋) - ρ₊Λ` (sec_04_near.tex:322). -/
noncomputable def dcap (ρm ρp : ℝ) : ℝ := 1 / y0 ^ 2 * (22 / 25 + 21 / 100 * ρm) - ρp * Lam ρm ρp

/-- The quadratic left side of Lemma 4.8 for the cell `[i/256, (i+1)/256]` at `e`:
`(293/540 + δ e)² - ρ₊ e (M + 130 e)` (sec_04_near.tex:326). The value about 0.1557 at sec_04_near.tex:333 is a run
description: the smallest value of this quadratic computed with the upper bounds for `𝔥[Z]`, `𝔴[Z]`,
not the minimum of `cellQuad`. -/
noncomputable def cellQuad (i : ℕ) (e : ℝ) : ℝ :=
  (293 / 540 + dcap ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) * e) ^ 2 -
    ((i : ℝ) + 1) / 256 * e * (Mcap ((i : ℝ) / 256) + 130 * e)

end Robinson
