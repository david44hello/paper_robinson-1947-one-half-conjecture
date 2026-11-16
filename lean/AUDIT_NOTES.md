# Robinson's (1947) one-half conjecture is true — notes on the Lean proof

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_robinson-1947-one-half-conjecture).

Pointers of the form `sec_0N_*.tex:<line>` (and `abstract.tex:<line>`, `back_matter.tex:<line>`) are lines of the
TeX sources of version 3.03 of the paper. No line has moved since version 1.70: later versions change the words of
some lines in place, among them the abstract (abstract.tex:3), and add sentences that point to the figures at the
ends of lines.

Notation. Since version 2.80 of the paper (the previous release), the paper renamed some letters and wrote some
short names out. Where these notes,
`CLAIM_MAP.tsv` or the comments of the Lean files restate the paper in an older letter, read it by this table.
Quotes are the paper's own words. Lean's own names (`edef`, `Mcap`, `Tfar`, `vτ`, `βτ`, `cA`, `kappa`, `faOf`,
`fdOf`, `calVOf`, ...) are unchanged.

| older letter | the paper now | section |
|---|---|---|
| `ε` (the value of the winding number on `Ω`) | written in words ("its value on `Ω`") | 2 |
| `e`, `e⁺` | `ϰ`, `ϰ⁺` | 4 |
| `D` | `Q_0` | 4 |
| `M` | `20 + N₆²` | 4 |
| `v` | `Ψ` | 4 |
| `β` | `τ₁` | 4 |
| `ε(y)`, `ε` | `ς(y)`, `ς` | 4 |
| `x = Re c` on `|c| = 1`, `s_x` | `c₁`, `s_c` | 4, Appendix A |
| `𝒬` (the polynomial of the proof of Lemma 4.3) | `𝒥` | 4, Appendix A |
| `𝓑 = |𝒬|²` | written out | 4, Appendix A |
| `L(ξ)` | `1 − νξ + B`, written out | 4 |
| `Z_o`, `Z_e` (the odd and even parts of a majorant `Z`) | `Z_odd`, `Z_even` | 4 |
| `𝒱` | `(ν⁺)⁴ + (4/3)(ν⁺)³`, written out | 4 |
| `𝔞(x)` | `1 − ν⁺x`, written out | 4, Appendix A |
| `𝔡(x)` | `𝒴(x)` | 4, Appendix A |
| `A`, `B`, `C` | `m_uu`, `m_vv`, `m_uv` | 5 |
| `κ` | `m₊` | 5 |
| `c` | `c_θ` | 6 |
| `T` | `ϖ` | 6 |
| `N` (the compression of the odd block `O`) | `O'` | 6 |
| `X`, `Y` | `Lξ₁`, `dξ₂`, written out | 6 |
| `W` | `ℓ₊` | 6 |
| `x = ¼` | the number `¼` | 6, Appendix C |
| `x_*` | `cos γ_*` | 6 |
| `𝓡(a, c)` | `S(a, c)` | 7 |
| `c` (the centre of a box) | `𝐱₀` | 7.4 |
| `x` (a point of a box) | `𝐱` | 7.4 |

## The rows

Each claim of the paper is one Lean theorem, a *row*, in
[Robinson/Paper/Statements.lean](Robinson/Paper/Statements.lean). The rows are named by the paper's numbering; their
proofs are in [Robinson/Proofs/](Robinson/Proofs/), and the definitions they use in [Robinson/Defs/](Robinson/Defs/).
[CLAIM_MAP.tsv](CLAIM_MAP.tsv) maps every printed claim of the paper to its rows.

Lean checks a proof of every row. The audit does not judge whether a row says what the paper says: to trust the
result, compare the definitions, the facts and checks (below) and the rows with the paper.

## The status of a row

The claim audit ([AUDIT.md](AUDIT.md), data in [CLAIMS.json](CLAIMS.json)) gives every row one status:
153 rows; 117 PROVED; 36 PROVED GIVEN; 0 not proved yet; 0 FAIL.

The status words:

- **PROVED**: Lean checks the proof, and the row depends only on Lean's three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`).
- **PROVED GIVEN** *names*: as PROVED, and the row takes the named facts or computer checks as explicit hypotheses.
- **not proved yet**: the proof of the row, or of a row it uses, is unfinished.
- **FAIL**: the row depends on another axiom, or uses a fact or check other than as an explicit hypothesis.

A status is decided from Lean's own output, never from the source text. For each row, the audit runs Lean's
`#print axioms` and reads the row's elaborated type:

- an axiom other than `propext`, `Classical.choice`, `Quot.sound` and Lean's placeholder axiom for an unfinished
  proof gives **FAIL**; so does a fact or check that occurs in the type other than as the exact type of a hypothesis,
  and a hypothesis whose type is a named proposition that is neither a fact nor a check;
- else, the placeholder axiom among the axioms gives **not proved yet** (the row's own proof, or a row it uses, is
  unfinished);
- else, the facts and checks that the row takes as hypotheses give **PROVED GIVEN** with their names;
- else the row is **PROVED**.

## Facts and checks

The facts and checks are ordinary propositions (`def … : Prop`), never axioms; nothing is assumed globally. A row
that uses one takes it as an explicit hypothesis.

- [Robinson/NotFormalized.lean](Robinson/NotFormalized.lean): 6 published facts from areas that Lean's
  library (Mathlib) does not cover. They are NOT formalized.
- [Robinson/ComputerChecked.lean](Robinson/ComputerChecked.lean): 14 statements that the paper
  checks by computer (Lemmas 4.8, 6.2, 6.4 and 7.6). They are NOT proved in Lean.

The section "Trust surface" below states each of them, with its source and the rows that use it.

## The files

- `check.sh`: the one command. It downloads Mathlib's prebuilt files (`lake exe cache get`), builds the proof
  (`lake build`), runs the audit and the final gate (next section), and stops at the first failure.
- `scripts/ci_check.sh`: the check that GitHub runs at every change, after its own Mathlib download and build: it
  runs `./check.sh`. GitHub then also checks that the rerun audit leaves `AUDIT.md` exactly as published.
- `Robinson/Paper/Statements.lean`: the rows. `Robinson/Proofs/`: their proofs. `Robinson/Defs/`: the definitions.
- `Robinson/NotFormalized.lean` and `Robinson/ComputerChecked.lean`: the facts and the checks.
- `CLAIM_MAP.tsv`: every printed claim of the paper, its place in the paper, its rows and its status.
- `AUDIT.md` and `CLAIMS.json`: the audit's table and data. `scripts/audit.py` writes them, with
  `scripts/audit_axioms.lean` (the Lean file it runs) and `scripts/audit_output.log` (Lean's output; made locally
  and ignored by Git).
- `scripts/final_gate.py` and `scripts/OPEN_ROWS.txt`: the final gate and its list of rows that may stay unproved
  (empty in this release).
- `MD5SUMS.txt`: the MD5 sum of every other file.

## How to rerun only the audit

After `lake build` (for example, after one run of `./check.sh`), with Python 3:

```bash
LEAN_RUN_LOCK=none LEAN_RUN_GATE=none python3 scripts/audit.py
python3 scripts/final_gate.py Robinson/Paper/Statements.lean CLAIMS.json scripts/OPEN_ROWS.txt
```

The audit prints the `AUDIT:` line of README.md and rewrites `AUDIT.md`, `CLAIMS.json`, `scripts/audit_axioms.lean`
and `scripts/audit_output.log`. The first three are byte-identical to the files shipped here; `scripts/audit_output.log`
is generated locally and ignored by Git. Thus `git status` stays clean and `md5sum -c MD5SUMS.txt` passes.
(`LEAN_RUN_LOCK` and `LEAN_RUN_GATE` name a lock file
and a priority gate for shared machines; `none` runs Lean directly.) The final gate checks that an unfinished proof
stands only as the whole proof of a row named in `scripts/OPEN_ROWS.txt`, and that the statuses of the audit match
that list: with the empty list, no row is unfinished and none is FAIL.

## What the proof takes as given, what is not counted, and how rows differ from the paper

The census rows are the rows of the main results: Lemma 2.2 (`lem_2_2`), Proposition 2.4 (`prop_2_4`), Proposition
4.1 (`prop_4_1`), Proposition 6.1 (`prop_6_1`), Proposition 7.1 (`prop_7_1`), the proof of Theorems 1.1 and 1.2
(`sec8_assembly`), Theorem 1.1 (`thm_1_1`), Theorem 1.2 (`thm_1_2`), Remark 8.2 (`rem_8_2`). "Used by" lists the
census rows whose Lean statement takes the item as a hypothesis (from the audit, `CLAIMS.json`).

## Trust surface

The Lean proofs of the census rows rest on 6 published facts and 14 computer checks. Each one is an ordinary Lean
proposition (`def … : Prop`), never a Lean postulate. A row that uses one takes it as an explicit hypothesis, so its
status is PROVED GIVEN that fact or check.

### The 6 facts: "not formalized" (file Robinson/NotFormalized.lean)

1. `FactArgumentPrinciple`: if `G` is holomorphic near `|z| ≤ ρ` and `G − c` has no zero on `|z| = ρ`, then the number of zeros of `G − c` in `|z| < ρ` (with multiplicity) equals the winding number of the image curve `G(|z| = ρ)` about `c`. Source: [Ahl79, Chapter 4, Section 5.2], as sec_02_reduction.tex:30 uses it. Not formalized: no argument principle in Lean's library. Used by: `lem_2_2`, `prop_2_4`, `sec8_assembly`, `thm_1_1`.
2. `FactJordanCurve`: if `G` is holomorphic near `|z| ≤ ρ` and injective on `|z| = ρ`, the image `J` is a Jordan curve; `ℂ \ J` is a bounded component `Ω` and an unbounded component `Ω'` with boundary `J`; the winding number is `0` on `Ω'` and a constant `±1` on `Ω`. Source: the Jordan curve theorem, [HS18, Corollaries 1.4 and 1.6; Theorem 3.2] (Hemasundar and Simha) and [Ahl79, Chapter 4, Section 2.1], as sec_02_reduction.tex:30 cites them. Not formalized: no Jordan curve theorem in Lean's library. Used by: `lem_2_2`, `prop_2_4`, `sec8_assembly`, `thm_1_1`.
3. `FactDeBranges`: every `f(z) = z + Σ_{n≥2} a_n zⁿ` in `𝒮` has `|a_n| ≤ n` for `n ≥ 2`. Source: de Branges' theorem [deB85], sec_03_tools.tex:13-16 (citation on l.17). Not formalized: no univalent-function theory in Lean's library. Used by: `prop_4_1`, `thm_1_1`, `thm_1_2`, `rem_8_2`.
4. `FactArea`: if `g(ζ) = ζ + b₀ + Σ_{n≥1} b_n ζ⁻ⁿ` is holomorphic and injective in `|ζ| > 1`, then `Σ_{n≥1} n|b_n|² ≤ 1`. Source: the area theorem of Gronwall [Gro14], [Dur83, Chapter 2], sec_03_tools.tex:17-20. Not formalized: no univalent-function theory in Lean's library. Used by: `prop_4_1`, `thm_1_1`, `thm_1_2`, `rem_8_2`.
5. `FactGrunsky`: for `g ∈ 𝒮`, the Grunsky matrix `C(g) = (√(nm) γ_nm)` satisfies `|xᵀ C(g) y| ≤ ‖x‖ ‖y‖` on every finite section (equivalent to operator norm at most 1 on `ℓ²`). Source: the strong Grunsky inequality [Gru39], [Pom75, Theorem 3.1], sec_03_tools.tex:28-35. Not formalized: no univalent-function theory in Lean's library. Used by: `prop_6_1`, `prop_7_1`, `thm_1_1`, `thm_1_2`, `rem_8_2`.
6. `FactBidiscPowerSeries`: a function continuous on `𝔻 × 𝔻` and holomorphic in each variable separately is the sum of a double power series that converges absolutely on all of `𝔻 × 𝔻`. Source: Osgood's lemma and the Cauchy formula on a polydisc, [Hor90, Section 2.2] (Hörmander), as sec_03_tools.tex:28 cites it; the paper uses it for the Grunsky kernel (sec_03_tools.tex:24-28). Not formalized: no holomorphic functions of several variables in Lean's library. Used by: `prop_6_1`, `prop_7_1`, `thm_1_1`, `thm_1_2`, `rem_8_2`.

### The 14 checks: "checked by computer, NOT proved in Lean" (file Robinson/ComputerChecked.lean)

Each check is typed exactly as printed (variables, range, function, strict inequality). Angles of Lemma 7.6 are in degrees.

1. `Check_4_8`: Lemma 4.8 (sec_04_near.tex:296-328; computation at sec_04_near.tex:333): on each of the 256 cells `[i/256, (i+1)/256]`, the functions `1 − ν⁺x` and `𝒴` are positive at `x = ±y₀`, `Π₋ > 0`, and for every `ϰ ∈ [0, ϰ⁺]`: `293/540 + δϰ > 0` and `(293/540 + δϰ)² − ρ₊ϰ(20 + N₆² + 130ϰ) > 0`. Program and output in the repository folder `robinson-1947-one-half-conjecture/`: `near/check_B9_b.py` (output `near/results/check_B9_b.txt`). Checked by computer, NOT proved in Lean. Used by: `prop_4_1`, `thm_1_1`, `thm_1_2`, `rem_8_2`.
2. `Check_6_2`: Lemma 6.2 (sec_06_far.tex:39-45; computation at sec_06_far.tex:48): for all `c ∈ [0, 383/1000]` and `r₁ ∈ [0, 1]`, `b₂r₁ + b₃√(1 − r₁²) − log cos(b₁r₁) < ϖ = 211/200`. Program and output in the repository folder `robinson-1947-one-half-conjecture/`: `far/check_sector135.py` (its output is the certificate `far/S135_certificate.json`). Checked by computer, NOT proved in Lean. Used by: `prop_6_1`, `thm_1_1`, `thm_1_2`, `rem_8_2`.
3. `Check_6_4`: Lemma 6.4 (sec_06_far.tex:84-90; computation at sec_06_far.tex:93): for all `c ∈ [0, 383/1000]`, `√((U_R + A_R)(V_R + B_R)) + √((U_R − A_R)(V_R − B_R)) < 173/250`. Program and output in the repository folder `robinson-1947-one-half-conjecture/`: `far/check_sector135.py` (its output is the certificate `far/S135_certificate.json`). Checked by computer, NOT proved in Lean. Used by: `prop_6_1`, `thm_1_1`, `thm_1_2`, `rem_8_2`.
4. `Check_7_6_band01`: Lemma 7.6(i) (sec_07_middle.tex:128), Table 3 row `[50.3°, 55°]` (sec_07_middle.tex:147; computation at sec_07_middle.tex:133-139): `Φ_F(θ, α, ψ, ω) > 0` for `θ ∈ [50.3, 55]` and `(α, ψ, ω) ∈ 𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_support_tree_arb.py`; data: the cap packet `middle/programB/HOLQ_joint_support_P55.json` (passed with `--cap-packet`) and the subdivision `middle/trees/50.3-55/cover.tree`; output `middle/results/HOLQ_JOINT_50p30_55_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
5. `Check_7_6_band02`: Lemma 7.6(i) (sec_07_middle.tex:128), Table 3 row `[55°, 60°]` (sec_07_middle.tex:148): `Φ_F > 0` for `θ ∈ [55, 60]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_support_tree_arb.py`; data: the cap packet `middle/programB/HOLQ_joint_support_P55.json` (passed with `--cap-packet`) and the subdivision `middle/trees/55-60/cover.tree`; output `middle/results/HOLQ_JOINT_55_60_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
6. `Check_7_6_band03`: Lemma 7.6(i) (sec_07_middle.tex:128), Table 3 row `[60°, 70°]` (sec_07_middle.tex:149): `Φ_F > 0` for `θ ∈ [60, 70]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_support_tree_arb.py`; data: the cap packet `middle/programB/HOLQ_joint_support_P55.json` (passed with `--cap-packet`) and the subdivision `middle/trees/60-70/cover.tree`; output `middle/results/HOLQ_JOINT_60_70_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
7. `Check_7_6_band04`: Lemma 7.6(i) (sec_07_middle.tex:128), Table 3 row `[70°, 80°]` (sec_07_middle.tex:150): `Φ_F > 0` for `θ ∈ [70, 80]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_support_tree_arb.py`; data: the cap packet `middle/programB/HOLQ_joint_support_P55.json` (passed with `--cap-packet`) and the subdivision `middle/trees/70-80/cover.tree`; output `middle/results/HOLQ_JOINT_70_80_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
8. `Check_7_6_band05`: Lemma 7.6(i) (sec_07_middle.tex:128), Table 3 row `[80°, 90°]` (sec_07_middle.tex:151): `Φ_F > 0` for `θ ∈ [80, 90]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_support_tree_arb.py`; data: the cap packet `middle/programB/HOLQ_joint_support_P55.json` (passed with `--cap-packet`) and the subdivision `middle/trees/80-90/cover.tree`; output `middle/results/HOLQ_JOINT_80_90_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
9. `Check_7_6_band06`: Lemma 7.6(ii) (sec_07_middle.tex:129), Table 3 row `[90°, 95°]` (sec_07_middle.tex:152): `Φ_rel > 0` for `θ ∈ [90, 95]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_peer_tree_arb.py`; data: the subdivision `middle/trees/90-95/cover.tree`; output `middle/results/HOLQ_90_95_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
10. `Check_7_6_band07`: Lemma 7.6(ii) (sec_07_middle.tex:129), Table 3 row `[95°, 100°]` (sec_07_middle.tex:153): `Φ_rel > 0` for `θ ∈ [95, 100]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_peer_tree_arb.py`; data: the subdivision `middle/trees/95-100/cover.tree`; output `middle/results/HOLQ_95_100_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
11. `Check_7_6_band08`: Lemma 7.6(ii) (sec_07_middle.tex:129), Table 3 row `[100°, 105°]` (sec_07_middle.tex:154): `Φ_rel > 0` for `θ ∈ [100, 105]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_peer_tree_arb.py`; data: the subdivision `middle/trees/100-105/cover.tree`; output `middle/results/HOLQ_100_105_Arb002.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
12. `Check_7_6_band09`: Lemma 7.6(ii) (sec_07_middle.tex:129), Table 3 row `[105°, 115°]` (sec_07_middle.tex:155): `Φ_rel > 0` for `θ ∈ [105, 115]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_peer_tree_arb.py`; data: the subdivision `middle/trees/105-115/cover.tree`; output `middle/results/HOLQ_105_115_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
13. `Check_7_6_band10`: Lemma 7.6(ii) (sec_07_middle.tex:129), Table 3 row `[115°, 125°]` (sec_07_middle.tex:156): `Φ_rel > 0` for `θ ∈ [115, 125]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_peer_tree_arb.py`; data: the subdivision `middle/trees/115-125/cover.tree`; output `middle/results/HOLQ_115_125_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.
14. `Check_7_6_band11`: Lemma 7.6(ii) (sec_07_middle.tex:129), Table 3 row `[125°, 135°]` (sec_07_middle.tex:157): `Φ_rel > 0` for `θ ∈ [125, 135]` on `𝓧`. Program, data and output in the repository folder `robinson-1947-one-half-conjecture/`: the check `middle/programB/holq_peer_tree_arb.py`; data: the subdivision `middle/trees/125-135/cover.tree`; output `middle/results/HOLQ_125_135_Arb001.json`. Checked by computer, NOT proved in Lean. Used by: `prop_7_1`, `thm_1_1`, `thm_1_2`.

Note: outside the census, the row for sec_05_grunsky_q.tex:54 ("not every `M ∈ 𝓑` comes from a univalent function",
`sec5_not_all_from_S`) also uses `Check_7_6_band02` (the band that contains `θ = 60°`).

## Not counted

These printed sentences are not claims that the Lean work counts. Each line gives the place and the reason.

### History and attributions (accounts of earlier work, not claims of this paper)
1. abstract.tex:3: "Robinson proved r ≥ 0.38, observed that the Koebe function gives r ≤ 1/2, and conjectured r = 1/2" and "Barnard proved r ≥ 0.49 in 1978": history.
2. sec_01_intro.tex:5: "In a study of univalent majorants, R. M. Robinson …": attribution.
3. sec_01_intro.tex:9: Robinson's results, Robinson's quoted words, and "Robinson writes H = (zG)'": history (the factor remark itself is a counted row).
4. sec_01_intro.tex:11: Livingston (close-to-convex, hence starlike functions), Barnard, Pearce, Barnard's quote, "We know of no later improvement": history.
5. sec_01_intro.tex:21: "Barnard [Bar78, (1)] uses the same quotient": attribution.
6. sec_01_intro.tex:32-40: Table 1, its column "Best result before this paper" (with "the radius 1/2 cannot be enlarged (Robinson 1947)") and its caption "What was known before, and what this paper proves.": history and table layout (the column "New result" states Theorems 1.1 and 1.2).
7. sec_01_intro.tex:11: the pointers to Table 1 and Figure 1 after the history (earlier versions had a sentence of its own, on a line of that file that is now a comment): history.
8. sec_01_intro.tex:45: "Our proof does not use starlikeness": route words; its reason, that `(Γk)'(−½) = 0` on the circle `|z| = ½`, is a counted claim (the row `intro_koebe_critical_on_circle`).
9. sec_01_intro.tex:52: Figure 1, panel (a), and "The vertical axis starts at r = 0.40": history and figure layout.
10. sec_01_intro.tex:75: Wikström's work "also combines a compression of the Grunsky matrix with interval arithmetic", and sec_01_intro.tex:77: Barnard's split of `Q_f` and how this proof uses it ("We use this split as the main estimate only for large angles"): attribution and route words.
11. Robinson's observation that the radius 1/2 is sharp, credited at sec_01_intro.tex:14 ("as Robinson observed" [Rob47, p. 18]), sec_01_intro.tex:61 (Table 2, "(Robinson's observation)") and sec_02_reduction.tex:61 ("this is Robinson's observation"): attribution (the sharpness claim itself is counted).
12. back_matter.tex:3 and :6-7: the data-availability heading and the acknowledgments (the data sentence, l.4, is item 35).

### Route words and layout (they describe the proof; each step is its own row)
13. sec_01_intro.tex:81: the plan of the paper ("collects the classical tools", "assembles the proof"; in the expanded paper also the appendices).
14. sec_02_reduction.tex:23: "for completeness we give the proof": route words (`lem_2_2` has no hypothesis on the derivative on the circle).
15. sec_02_reduction.tex:37: "Barnard reduces … [Bar78, p. 136]": attribution and route words.
16. sec_03_tools.tex:6: "This section collects the results from the theory of univalent functions that the proof uses": description.
17. sec_04_near.tex:33: overview of the section's route.
18. sec_04_near.tex:294: "The next lemma states in full what is computed on these cells, with the quantities of … taken at the caps of each cell": no longer in this list (kept here so that the numbers of the other items stay); it is counted with sec_04_near.tex:330, the row `sec4_caps_valid` (Lean defines the numbers of Lemma 4.8 as these quantities at the caps).
19. sec_05_grunsky_q.tex:57: "real dimension 6" and "real dimension 3": dimension words (the content is in the rows for Proposition 5.2 and Lemma 5.3).
20. sec_05_grunsky_q.tex:103, second sentence ("This is why Section 7 uses …"): route words.
21. sec_07_middle.tex:89: "Lemma … (i) uses the following choice": why these values (the five band checks of Lemma 7.6(i) are typed with exactly these `λ`, `μ` and `P`, the constant `Pmat`). The clause before it, that Lemma 7.4 holds for all real `λ`, `μ` and all positive definite `P`, is the row `lem_7_4`.
22. sec_07_middle.tex:117: "Lemma … uses the Grunsky inequality for the even block, which the relaxation of Section … ignores": route words (the line's first sentence is a counted row, through `sec5_O2_contraction` and `prop_7_5_ii`).
23. sec_07_middle.tex:124: "Both are explicit elementary functions …": description.

### Descriptions of the computer runs (the 14 checks above carry the claims; the programs and logs are in the repository folder `robinson-1947-one-half-conjecture/`)
24. abstract.tex:3: "Both parts end in finite computations in exact rational or rigorous interval arithmetic": run description.
25. sec_01_intro.tex:61-67: Table 2 and its caption: "analysis only", "none", "72 and 410 coefficients", "256 cells", "about 3·10⁵ boxes": run description.
26. sec_04_near.tex:147: "whose 72 coefficients, computed exactly in …, are all positive": a program certificate (Lemma 4.3 itself is PROVED in Lean by its own certificate).
27. sec_04_near.tex:239 and :243, in the printed proof of Lemma 4.5(i): "is a polynomial in `τ` and `c` with rational coefficients" (each `T_j𝒟₅`) and "all its 410 coefficients, computed exactly in …, are positive": a program certificate (the computation asserts that each `T_j𝒟₅` is a polynomial and checks the 410 coefficients). Lemma 4.5(i) itself is PROVED in Lean, by its own route; the other steps of that proof are rows (`sec4_Qcal`, `sec4_hat_bounds`, `sec4_TJ_holo`).
28. sec_04_near.tex:333: how the computation works, and "These finitely many checks cover every … not only sample points, and both inequalities hold in all 256 cells": run description.
29. sec_04_near.tex:333: "the smallest value of the quadratic left side … with these upper bounds for 𝔥[Z] and 𝔴[Z], is about 0.1557, in the cell [227/256, 228/256]": a computed value, and no proof uses it (with the exact numbers of Lemma 4.8 the minimum is about 0.1574).
30. sec_06_far.tex:48: eleven cells; the reduction to `e^{y₁} cos y₂ > 1` and the display `(Σ_{j=0}^{8} y₁ʲ/j!)(1 − y₂²/2 + y₂⁴/24 − y₂⁶/720) > 1` that implies it (the method of `Check_6_2`; Lemma 6.2 is taken as given); degree 28, Bernstein coefficients on at most eight subintervals: run description.
31. sec_06_far.tex:93: 234 cells and the largest bound 3459999249/(5·10⁹): run description (its decimal value `0.69199984…` and `173/250 = 0.692` are the row `sec6_cover_bound_arith`).
32. sec_07_middle.tex:133-139: the method of the verification: its three lower bounds (the interval extension, the second-order Taylor form and its variant), the subdivision stored as data, and what the verification checks (the leaves partition the box exactly and the box contains `I × 𝓧`; a lower bound on every leaf, bisecting further where needed; a band is accepted only when every leaf has a strictly positive lower bound): run description (the band checks carry the claim).
33. sec_07_middle.tex:141-162: Table 3's box counts and its caption: run description (the arithmetic of Table 3's total IS a counted row).
34. sec_07_middle.tex:165: in the short paper an empty line (in version 2.80 it held a run description).
35. back_matter.tex:4: where the programs, their input data and their outputs are: data availability.

### Other
36. sec_08_proof.tex:5: "All their endpoints, measured in degrees, are rational, except θ₀ = 2 arcsin(17/40)": it motivates Lemma 8.1; θ₀ is only excluded, and its irrationality is not claimed.
37. P24_short.tex:11 and P24_long.tex:11, footnote 2 (its mark is in the abstract): "Additionally, Theorems 1.1 and 1.2 are proved in Lean 4 with six published theorems (the argument principle, the Jordan curve theorem, de Branges' theorem, the area theorem, the strong Grunsky inequality, and the double power series of a function holomorphic on the bidisc) and the explicit inequalities of Lemmas 4.8, 6.2, 6.4 and 7.6 taken as hypotheses, and checked with `lake comparator`": a remark about this Lean proof; its content is the status of Theorems 1.1 and 1.2 (AUDIT.md: PROVED GIVEN; Theorem 1.1 takes the six facts and the 14 checks, Theorem 1.2 four of the facts and the 14 checks; the six published theorems are the 6 published facts, Lemmas 4.8, 6.2, 6.4 and 7.6 the 14 checks; its last words (checked with lake comparator) are a run description, not counted: the comparator's run on this tag, outside these files).
38. P24_short.tex:11 and P24_long.tex:11, the end of footnote 2: the link "https://github.com/david44hello/paper_robinson-1947-one-half-conjecture/tree/v3.03/lean" to this Lean proof.
39. P24_short.tex:9 and :15 (short paper only): footnote 1 (its mark is in the abstract), which points to the expanded version of the paper (:9), and the manuscript's version line (:15): pointers, no mathematical claim.

The new figures depict already-counted objects and bounds: figures/fig_pairs.tex:10 uses the normalized pair (`sec2_pair_normal_form`, `sec2_values_eq`) and the three angular ranges (`sec8_cover`); figures/fig_koebe.tex:6 uses Proposition 2.5 (`prop_2_5`); figures/fig_near.tex:6 uses the pair and Koebe-transform coordinates (`sec4_midpoint`, `sec4_Pi_formula`); figures/fig_bounds.tex:6 uses Remark 8.2 (`rem_8_2`) and the Koebe quotient (`sec2_koebe_limit`, `eq_Qk`). Dots, insets, line styles and axis choices are figure layout, not additional claims.

## Rows stronger than printed, and route differences

No row is weaker than its printed claim.

### Rows stronger than printed
1. `sec4_first_variation` (sec_04_near.tex:212-216): typed for complex `λ`; the paper uses real `0 ≤ λ ≤ 1`.
2. `sec6_xi_ball` (sec_06_far.tex:26): holds for all `σ₊, σ₋ ≥ 0` with `σ₊ + σ₋ > 0` and every `O' ∈ 𝓑` (the paper's compression `O'` of the odd block), not only the numbers of the pair.
3. `sec6_psum_cos` (sec_06_far.tex:24-28): an identity for every real `φ` and all complex `X, Y`, not only `φ = arg Z_o` and the paper's `X = Lξ₁`, `Y = dξ₂`.
4. `sec6_b_change` (sec_06_far.tex:30-32): for all `L, d > 0`, real `φ` and all `ξ₁, ξ₂ ∈ ℂ`, with `|ζ₁|² + |ζ₂|² = |ξ₁|² + |ξ₂|²` (not only `≤ 1`).
5. `sec6_Wbound_finite` (sec_06_far.tex:34-36): for all `b₁, b₂, b₃ ≥ 0` with `b₁ < π/2`, not only the numbers of this range of `θ`.
6. `sec7_trace_bound` (sec_07_middle.tex:81-86): for every size `N`, every `E` with the bilinear bound, every real `𝒲` and all real `λ, μ`, not only the fixed `λ = 4/5`, `μ = 1/2`.
7. `sec6_sigma_pos` (sec_06_far.tex:18): states `σ₊ > 0` and `σ₋ > 0`; the paper says "nonzero".
8. `lem_4_4_i` (sec_04_near.tex:174): for any majorant `Z` with the needed convergence at `y`; the paper's majorants are the rational functions described at sec_04_near.tex:159.
9. `sec4_hw_coeff` (sec_04_near.tex:164-169): for any `Z` with nonnegative coefficients that converges on `|x| < r`; the paper uses it for the rational majorants of sec_04_near.tex:159.
10. `lem_4_2` (sec_04_near.tex:85-93): typed for the explicit range `0 < |ξ| < 1/4`; the paper says "For small ξ" (sec_04_near.tex:75). The use at `ξ = iy`, `y ≤ 17/80`, lies inside this range.

### Typing notes (same claim)
11. `sec4_no_constant` (sec_04_near.tex:31): the type does not ask `C₂ > 0` for the upper constant; it follows from `C₁ > 0` and the two bounds.
12. `lem_7_2` (sec_07_middle.tex:23-25): the type keeps `Mᵀ = M` (the paper's matrices are symmetric) for the conjugation part; the proof does not need it.
13. `sec6_L_log3` (sec_06_far.tex:16 and :34): the middle part `L = log 3` holds by definition; the other two parts are real proofs.
14. `sec4_majorant_rules` (sec_04_near.tex:159): typed with `F(0) = Z(0) = 0`, as the paper prints it since version 1.70.

### Route differences (same conclusion, different proof)
15. `prop_2_5` (sec_02_reduction.tex:72): `Γk` is shown not injective on `|z| < r`, `r > 1/2`, by an explicit pair `z, z̄` (`zz̄ = P ∈ (1/4, r²)`, `Re z = (3 − 1/P)/2`), not by the local-mapping argument at `z₀ = −1/2`.
16. `lem_4_4_ii`, `lem_4_4_iii` (sec_04_near.tex:172-179): Lemma 4.4 is printed for `9/20 ≤ τ ≤ 1/2`, while the shared rows for sec_04_near.tex:53-68 are typed on the printed range `9/20 < τ < 1/2` (sec_04_near.tex:48); so the Lean proof proves the area bound again on the closed range, including the endpoint `τ = 1/2`.
17. `lem_4_6` (proof at sec_04_near.tex:266-276): no series in powers of `B` (sec_04_near.tex:267-271) and no `q`-sums (sec_04_near.tex:272-275); instead the closed identities `Π − Π̂ = −NB(1/(aL²) + 1/(a²L))` and `Π − Π̂ − Π̇ = NB²(2/(a³L) + 1/(a²L²))` (`a = 1 − νξ`, `L = a + B`), and `1/L ≪ 1/𝒴` by the inverse rule (sec_04_near.tex:159); same `Z₁`, `Z₂`, same conclusion (sec_04_near.tex:276).
18. `sec4_first_variation`, `sec4_Tj_closed` (sec_04_near.tex:216): the printed "`T_j = −y⁻² ∂Q_f(−τ+iy, −τ−iy)/∂b_{2j−1}` at `λ = 0`" is the `λ`-derivative that the rows state, with the closed form of each `T_j`.
19. `sec4_Lam_nonneg` (sec_04_near.tex:342): `Λ ≥ 0` is proved from an explicit derivative of `Z₂` at `±y₀`, uniform over the cell caps; the paper argues from nonnegative coefficients. It is a support row, not a census hypothesis.
20. `prop_4_1` (proof at sec_04_near.tex:336-347): the case `e = 0` gives `f = k` directly, without Lemma 4.2 (sec_04_near.tex:337); `|c| ≤ 1` comes from Bieberbach's inequality (de Branges for `n = 2`) inside the proof (sec_04_near.tex:57), because the shared row for sec_04_near.tex:53-60 needs `9/20 < τ` strictly; `Π₋ > 0` comes from `Π₋ ≥ 1 − ς(y₀) ≈ 0.42` (sec_04_near.tex:259), not from the computer check.
21. `lem_4_3`, `sec4_circle`, `lem_4_5_i` (sec_04_near.tex:126-147 and :218-243): PROVED in Lean with no computer check, by certificates checked inside Lean; the paper uses programs (72 and 410 positive coefficients).
22. `eq_Kf` and Lemma 3.1 (sec_03_tools.tex:56-70): `eq_Kf` is proved by comparing two-variable coefficients, built on one-variable uniqueness; the parity of the odd root's Grunsky coefficients is proved inside the proof, with no extra hypothesis.
23. `lem_6_3` (sec_06_far.tex:59-61): proved with no hypothesis at all (it does not need the symmetry `γ_nm = γ_mn`).
24. `sec6_logp_logq`, `sec6_Rf_bound`, `eq_psum` (sec_06_far.tex:22-24): the Lean proof uses the symmetrized compression `(O' + O'ᵀ)/2`, with `‖O'‖ ≤ 1` from the bilinear compression bound; `σ₋ > 0` is proved inside (`σ₋ = 0` would make `z = s²` real).
25. `lem_7_3` (proof at sec_07_middle.tex:39-47): the branch bound `|Δ_f| ≤ 2 log 2 < π` comes from the Grunsky contraction (`|K_h(s, −s)| ≤ log 2`), not from the radial integration at sec_07_middle.tex:44.
26. `lem_7_4` (sec_07_middle.tex:69-86): the trace bound is proved on `N × N` sections (`sec7_trace_bound`), then `N → ∞`.
27. `sec5_not_all_from_S` (sec_05_grunsky_q.tex:54): proved from Proposition 7.5(ii) and the band check at `θ = 60°` (`Check_7_6_band02`), with Remark 5.6's matrix (`α = 0.535`, sec_05_grunsky_q.tex:103); in the Lean file it stands after Proposition 7.5(ii), which its proof uses.
