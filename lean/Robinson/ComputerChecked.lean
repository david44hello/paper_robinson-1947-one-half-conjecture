/-
Robinson/ComputerChecked.lean — the statements that the paper's programs check by computer.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
Each check is an ordinary proposition `def Check… : Prop`, never a Lean postulate, stated exactly as printed (variables,
range, function, strict inequality). A claim whose proof uses one takes it as an explicit hypothesis and is PROVED
GIVEN that check; the check itself is "checked by computer, NOT proved in Lean". Angles of Lemma 7.6 are in degrees.
-/
import Robinson.Defs.Far
import Robinson.Defs.Matrix2
import Robinson.Defs.Near

namespace Robinson

/-- COMPUTER-CHECKED: Lemma 4.8 (sec_04_near.tex:296-328), by the two exact rational programs of its proof
(sec_04_near.tex:333): checked by the first program on these 256 cells; the second checks the same inequalities on
320 cells. NOT proved in Lean.
For each of the 256 intervals `[ρ₋, ρ₊] = [i/256, (i+1)/256]`, `0 ≤ i ≤ 255`, with the numbers of Lemma 4.8: `𝔞` and
`𝔡` are positive at `x = ±y₀`, `Π₋ > 0`, and for every `e ∈ [0, e⁺]`, `293/540 + δ e > 0` and
`(293/540 + δ e)² - ρ₊ e (M + 130 e) > 0`.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: first program `near/check_B9_b.py` (output `near/results/check_B9_b.txt`); second program `near/check_B9_a.py`, on its own 320 cells (output `near/results/check_B9_a.txt`). -/
def Check_4_8 : Prop :=
  ∀ i : ℕ, i ≤ 255 →
    (0 < fa ((i : ℝ) / 256) y0 ∧ 0 < fa ((i : ℝ) / 256) (-y0) ∧
        0 < fd ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) y0 ∧ 0 < fd ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) (-y0)) ∧
      0 < PiLow ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ ePlus ((i : ℝ) / 256) →
        0 < 293 / 540 + dcap ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) * e ∧
          0 < (293 / 540 + dcap ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) * e) ^ 2 -
            ((i : ℝ) + 1) / 256 * e * (Mcap ((i : ℝ) / 256) + 130 * e)

/-- COMPUTER-CHECKED: Lemma 6.2 (sec_06_far.tex:39-45), by the two exact rational programs of its proof
(sec_06_far.tex:48; eleven cells, Bernstein coefficients on at most eight subintervals, eight equal ones in the second
program). NOT proved in Lean.
For all `c ∈ [0, 383/1000]` and `r₁ ∈ [0, 1]`: `b₂ r₁ + b₃ √(1 - r₁²) - log cos(b₁ r₁) < T = 211/200`.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: first program `far/check_sector135.py` (its output is the certificate `far/S135_certificate.json`); second program `far/S135_check_b.py` (output `far/results/S135_check_b.txt`). -/
def Check_6_2 : Prop :=
  ∀ c : ℝ, 0 ≤ c → c ≤ 383 / 1000 → ∀ r₁ : ℝ, 0 ≤ r₁ → r₁ ≤ 1 →
    b2 c * r₁ + b3 c * Real.sqrt (1 - r₁ ^ 2) - Real.log (Real.cos (b1 c * r₁)) < Tfar

/-- COMPUTER-CHECKED: Lemma 6.4 (sec_06_far.tex:84-90), by the two exact rational programs of its proof
(sec_06_far.tex:93): the first covers `[0, 383/1000]` by 234 cells; a second, independently written program checks
the same 234 cells in its own exact rational arithmetic. NOT proved in Lean.
For all `c ∈ [0, 383/1000]`: `√((U_R + A_R)(V_R + B_R)) + √((U_R - A_R)(V_R - B_R)) < 173/250`.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: first program `far/check_sector135.py` (its output is the certificate `far/S135_certificate.json`); second program `far/S135_check_b.py` (output `far/results/S135_check_b.txt`). -/
def Check_6_4 : Prop :=
  ∀ c : ℝ, 0 ≤ c → c ≤ 383 / 1000 → Rbound c < 173 / 250

/-- COMPUTER-CHECKED: Lemma 7.6(i), band `[50.3°, 55°]` of Table 3 (sec_07_middle.tex:147), function `Φ_F`, by the
two interval-arithmetic programs (sec_07_middle.tex:133-139). NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/joint_v040/`, program B `middle/programB/holq_support_tree_arb.py` with `--cap-packet middle/programB/HOLQ_joint_support_P55.json`; tree `middle/trees/50.3-55/cover.tree`; output `middle/results/HOLQ_JOINT_50p30_55_Arb001.json`. -/
def Check_7_6_band01 : Prop := ∀ θ : ℝ, 50.3 ≤ θ → θ ≤ 55 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(i), band `[55°, 60°]` of Table 3 (sec_07_middle.tex:148), function `Φ_F`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/joint_v040/`, program B `middle/programB/holq_support_tree_arb.py` with `--cap-packet middle/programB/HOLQ_joint_support_P55.json`; tree `middle/trees/55-60/cover.tree`; output `middle/results/HOLQ_JOINT_55_60_Arb001.json`. -/
def Check_7_6_band02 : Prop := ∀ θ : ℝ, 55 ≤ θ → θ ≤ 60 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(i), band `[60°, 70°]` of Table 3 (sec_07_middle.tex:149), function `Φ_F`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/joint_v040/`, program B `middle/programB/holq_support_tree_arb.py` with `--cap-packet middle/programB/HOLQ_joint_support_P55.json`; tree `middle/trees/60-70/cover.tree`; output `middle/results/HOLQ_JOINT_60_70_Arb001.json`. -/
def Check_7_6_band03 : Prop := ∀ θ : ℝ, 60 ≤ θ → θ ≤ 70 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(i), band `[70°, 80°]` of Table 3 (sec_07_middle.tex:150), function `Φ_F`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/joint_v040/`, program B `middle/programB/holq_support_tree_arb.py` with `--cap-packet middle/programB/HOLQ_joint_support_P55.json`; tree `middle/trees/70-80/cover.tree`; output `middle/results/HOLQ_JOINT_70_80_Arb001.json`. -/
def Check_7_6_band04 : Prop := ∀ θ : ℝ, 70 ≤ θ → θ ≤ 80 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(i), band `[80°, 90°]` of Table 3 (sec_07_middle.tex:151), function `Φ_F`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/joint_v040/`, program B `middle/programB/holq_support_tree_arb.py` with `--cap-packet middle/programB/HOLQ_joint_support_P55.json`; tree `middle/trees/80-90/cover.tree`; output `middle/results/HOLQ_JOINT_80_90_Arb001.json`. -/
def Check_7_6_band05 : Prop := ∀ θ : ℝ, 80 ≤ θ → θ ≤ 90 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(ii), band `[90°, 95°]` of Table 3 (sec_07_middle.tex:152), function `Φ_rel`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/plain_v060/`, program B `middle/programB/holq_peer_tree_arb.py`; tree `middle/trees/90-95/cover.tree`; output `middle/results/HOLQ_90_95_Arb001.json`. -/
def Check_7_6_band06 : Prop := ∀ θ : ℝ, 90 ≤ θ → θ ≤ 95 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(ii), band `[95°, 100°]` of Table 3 (sec_07_middle.tex:153), function `Φ_rel`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/plain_v060/`, program B `middle/programB/holq_peer_tree_arb.py`; tree `middle/trees/95-100/cover.tree`; output `middle/results/HOLQ_95_100_Arb001.json`. -/
def Check_7_6_band07 : Prop := ∀ θ : ℝ, 95 ≤ θ → θ ≤ 100 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(ii), band `[100°, 105°]` of Table 3 (sec_07_middle.tex:154), function `Φ_rel`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/plain_v060/`, program B `middle/programB/holq_peer_tree_arb.py`; tree `middle/trees/100-105/cover.tree`; output `middle/results/HOLQ_100_105_Arb002.json`. -/
def Check_7_6_band08 : Prop := ∀ θ : ℝ, 100 ≤ θ → θ ≤ 105 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(ii), band `[105°, 115°]` of Table 3 (sec_07_middle.tex:155), function `Φ_rel`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/plain_v060/`, program B `middle/programB/holq_peer_tree_arb.py`; tree `middle/trees/105-115/cover.tree`; output `middle/results/HOLQ_105_115_Arb001.json`. -/
def Check_7_6_band09 : Prop := ∀ θ : ℝ, 105 ≤ θ → θ ≤ 115 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(ii), band `[115°, 125°]` of Table 3 (sec_07_middle.tex:156), function `Φ_rel`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/plain_v060/`, program B `middle/programB/holq_peer_tree_arb.py`; tree `middle/trees/115-125/cover.tree`; output `middle/results/HOLQ_115_125_Arb001.json`. -/
def Check_7_6_band10 : Prop := ∀ θ : ℝ, 115 ≤ θ → θ ≤ 125 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω

/-- COMPUTER-CHECKED: Lemma 7.6(ii), band `[125°, 135°]` of Table 3 (sec_07_middle.tex:157), function `Φ_rel`, by the
two interval-arithmetic programs. NOT proved in Lean.
Programs and outputs in the repository folder `robinson-1947-one-half-conjecture/`: program A `middle/programA/plain_v060/`, program B `middle/programB/holq_peer_tree_arb.py`; tree `middle/trees/125-135/cover.tree`; output `middle/results/HOLQ_125_135_Arb001.json`. -/
def Check_7_6_band11 : Prop := ∀ θ : ℝ, 125 ≤ θ → θ ≤ 135 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω

end Robinson
