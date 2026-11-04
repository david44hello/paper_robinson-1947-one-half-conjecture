/-
Robinson/Audit/NearRefactor.lean — the numbers of Lemma 4.8 (Robinson/Defs/Near.lean) equal their
printed formulas term for term (definitional equalities, proved by `rfl`). They were first written directly and are
now the general-cap functions evaluated at the cell's caps; these lemmas show that the values did not change.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Near

namespace Robinson.Audit

open Robinson

theorem epsY0_eq : epsY0 = 16 * y0 ^ 2 / (3 * (1 - 4 * y0 ^ 2) ^ 2) + 4 * y0 ^ 2 / (1 - 4 * y0 ^ 2) := rfl

theorem fa_eq (ρm x : ℝ) : fa ρm x = 1 - nuPlus ρm * x := rfl

theorem fd_eq (ρm ρp x : ℝ) : fd ρm ρp x = fa ρm x - Real.sqrt (etaPlus ρm ρp) * B1 x := rfl

theorem Z1_eq (ρm ρp x : ℝ) :
    Z1 ρm ρp x = Nplus x * B1 x * (1 / (fa ρm x ^ 2 * fd ρm ρp x) + 1 / (fa ρm x * fd ρm ρp x ^ 2)) := rfl

theorem Z2_eq (ρm ρp x : ℝ) :
    Z2 ρm ρp x = Nplus x * B2 x * (2 / (fa ρm x ^ 3 * fd ρm ρp x) + 1 / (fa ρm x ^ 2 * fd ρm ρp x ^ 2)) := rfl

theorem PiLow_eq (ρm ρp : ℝ) :
    PiLow ρm ρp = max (1 - epsY0) (PihatLow ρm - Real.sqrt (etaPlus ρm ρp) * frakH (Z1 ρm ρp)) := rfl

theorem Lam_eq (ρm ρp : ℝ) :
    Lam ρm ρp = (frakW (Z2 ρm ρp) + TPlus ρm * frakH (Z2 ρm ρp) + nPlus ρm * frakH (Z1 ρm ρp)) / PiLow ρm ρp :=
  rfl

end Robinson.Audit
