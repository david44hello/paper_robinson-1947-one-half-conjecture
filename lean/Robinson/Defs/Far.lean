/-
Robinson/Defs/Far.lean — the explicit functions of `c = cos(θ/2)` in Lemmas 6.2 and 6.4.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
TRUST SURFACE: every definition is read against sec_06_far.tex (its lines; AUDIT_NOTES.md names the version).
-/
import Robinson.Defs.Basic

namespace Robinson

open Complex

/-- `L = log 3` (sec_06_far.tex:40). -/
noncomputable def Llog3 : ℝ := Real.log 3

/-- `u_o = ½ artanh(4c/5)` (sec_06_far.tex:40). -/
noncomputable def uo (c : ℝ) : ℝ := (1 / 2) * Real.artanh (4 * c / 5)

/-- `v_o = ½ arctan((4/3) √(1 - c²))` (sec_06_far.tex:40). -/
noncomputable def vo (c : ℝ) : ℝ := (1 / 2) * Real.arctan ((4 / 3) * Real.sqrt (1 - c ^ 2))

/-- `b₁ = √(L² - 4u_o²)` (sec_06_far.tex:42). -/
noncomputable def b1 (c : ℝ) : ℝ := Real.sqrt (Llog3 ^ 2 - 4 * uo c ^ 2)

/-- `b₂ = 4 u_o v_o / b₁` (sec_06_far.tex:42). -/
noncomputable def b2 (c : ℝ) : ℝ := 4 * uo c * vo c / b1 c

/-- `b₃ = L √(L² - 4u_o² - 4v_o²) / b₁` (sec_06_far.tex:42). -/
noncomputable def b3 (c : ℝ) : ℝ := Llog3 * Real.sqrt (Llog3 ^ 2 - 4 * uo c ^ 2 - 4 * vo c ^ 2) / b1 c

/-- `ϖ = 211/200` (sec_06_far.tex:44; Lean's name `Tfar`). -/
noncomputable def Tfar : ℝ := 211 / 200

/-- `U_R = 4/9` (sec_06_far.tex:85). -/
noncomputable def U0 : ℝ := 4 / 9

/-- `V_R = log(4/3)` (sec_06_far.tex:85). -/
noncomputable def V0 : ℝ := Real.log (4 / 3)

/-- The number `¼` of `z² = -¼e^{-iε}` (sec_06_far.tex:78) and of `A_R`, `B_R` (sec_06_far.tex:87); the text writes
the number, Lean names it `xfar`. -/
noncomputable def xfar : ℝ := 1 / 4

/-- `e^{-iε} = 1 - 2c² - 2ic√(1 - c²)` (sec_06_far.tex:85); `e^{iε}` is its inverse. -/
noncomputable def emeps (c : ℝ) : ℂ := ((1 - 2 * c ^ 2 : ℝ) : ℂ) - 2 * I * ((c * Real.sqrt (1 - c ^ 2) : ℝ) : ℂ)

/-- `A_R = Re(-x / (1 + x e^{-iε})²)` with `x = ¼`, that is the printed `Re(-4/(4 + e^{-iε})²)` (sec_06_far.tex:87;
the row `sec6_A0_printed` states the equality). -/
noncomputable def A0 (c : ℝ) : ℝ := (-(xfar : ℂ) / (1 + (xfar : ℂ) * emeps c) ^ 2).re

/-- `B_R = Re(-e^{iε} log(1 + ¼e^{-iε}))` (Lean: `x e^{-iε}` with `x = ¼`), principal logarithm
(sec_06_far.tex:87). -/
noncomputable def B0 (c : ℝ) : ℝ := (-(emeps c)⁻¹ * log (1 + (xfar : ℂ) * emeps c)).re

/-- The left side of Lemma 6.4: `√((U_R + A_R)(V_R + B_R)) + √((U_R - A_R)(V_R - B_R))` (sec_06_far.tex:89). -/
noncomputable def Rbound (c : ℝ) : ℝ :=
  Real.sqrt ((U0 + A0 c) * (V0 + B0 c)) + Real.sqrt ((U0 - A0 c) * (V0 - B0 c))

end Robinson
