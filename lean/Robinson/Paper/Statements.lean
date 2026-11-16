/-
Robinson/Paper/Statements.lean — one Lean theorem per claim of the short paper.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.














Paper = the short paper (\longfalse); AUDIT_NOTES.md and CLAIM_MAP.tsv name its text version.
Pointers "sec_0N_*.tex:<line>" = lines of the paper's TeX sources. A row is proved iff its body is a proof term.
A row with a binder `(h : Fact…)` is PROVED GIVEN that published fact (Robinson/NotFormalized.lean); a row with a
binder `(h : Check…)` is PROVED GIVEN that computer check (Robinson/ComputerChecked.lean). No other hypotheses,
except in the rows `*_from_layer` and `sec8_assembly`: these are printed proofs written as implications, and
their hypotheses are discharged in the census rows prop_4_1, prop_6_1, prop_7_1, thm_1_1 and thm_1_2.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Matrix2
import Robinson.Defs.Far
import Robinson.Defs.Near
import Robinson.Defs.Grunsky
import Robinson.Defs.NearP
import Robinson.NotFormalized
import Robinson.ComputerChecked
import Robinson.Proofs.Sec2Basic
import Robinson.Proofs.Normalize
import Robinson.Proofs.Koebe
import Robinson.Proofs.Arith
import Robinson.Proofs.Connector
import Robinson.Proofs.Sec3Local
import Robinson.Proofs.Chart
import Robinson.Proofs.Sec4Elem
import Robinson.Proofs.Sec7Hol
import Robinson.Proofs.Sec2Rest
import Robinson.Proofs.Takagi
import Robinson.Proofs.Sec4Hat
import Robinson.Proofs.FromLayer
import Robinson.Proofs.Sec7Lin
import Robinson.Proofs.Sec6Values
import Robinson.Proofs.Assembly
import Robinson.Proofs.Sec5Finite
import Robinson.Proofs.GrunskyIneq
import Robinson.Proofs.Sec6Bounds
import Robinson.Proofs.OddRootGram
import Robinson.Proofs.GrunskyExist
import Robinson.Proofs.Lem31
import Robinson.Proofs.Lem43
import Robinson.Proofs.Sec5G
import Robinson.Proofs.Prop41
import Robinson.Proofs.Sec7G
import Robinson.Proofs.Sec6G
import Robinson.Proofs.LamNonneg
import Robinson.Proofs.NearP_A
import Robinson.Proofs.Lem44ii
import Robinson.Proofs.Majorants
import Robinson.Proofs.FirstVar
import Robinson.Proofs.Lem44iii
import Robinson.Proofs.NearP_C
import Robinson.Proofs.SigmaPos
import Robinson.Proofs.NearP_D
import Robinson.Proofs.GammaUnique
import Robinson.Proofs.Sec6PhiD
import Robinson.Proofs.Rows292

namespace Robinson.Paper

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## Section 1 (introduction) -/

/-- sec_01_intro.tex:7: "`Γ f(z) = (f(z) + z f'(z))/2 = ½ (z f(z))'`", at every point where `f` is differentiable. -/
theorem intro_gamma_deriv (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z) :
    Gam f z = (1 / 2 : ℂ) * deriv (fun x => x * f x) z := Proofs.intro_gamma_deriv_proved f z hf

/-- sec_01_intro.tex:9: "`Γ` multiplies the coefficient `a_n` by `(n+1)/2`" (for `f ∈ 𝒮`, every `n`). -/
theorem intro_gamma_coeff (f : ℂ → ℂ) (hf : InS f) (n : ℕ) :
    coeff (Gam f) n = ((n : ℂ) + 1) / 2 * coeff f n := Proofs.intro_gamma_coeff_proved f hf n

/-- sec_01_intro.tex:9: "`H = (zG)'`, which is `2 Γ G`; the factor does not affect univalence": on every set,
`2 Γ f` is injective iff `Γ f` is. (`(zf)' = 2 Γ f` is `intro_gamma_deriv`.) -/
theorem intro_factor_two (f : ℂ → ℂ) (U : Set ℂ) :
    Set.InjOn (fun z => 2 * Gam f z) U ↔ Set.InjOn (Gam f) U := Proofs.intro_factor_two_proved f U

/-- sec_01_intro.tex:9 and :45: the derivative of `Γ k` vanishes at `z = -½`, a point of the circle `|z| = ½`
("it cannot use `(Γ f)' ≠ 0` on the circle `|z| = ½`, since `(Γ k)'(-½) = 0`"). -/
theorem intro_koebe_critical_on_circle :
    ‖(-1 / 2 : ℂ)‖ = 1 / 2 ∧ deriv (Gam koebe) (-1 / 2) = 0 := Proofs.intro_koebe_critical_on_circle_proved

/-- sec_01_intro.tex:46 "`2 arcsin(17/40) ≈ 50.3°`" and sec_04_near.tex:22 "`θ₀ = 2 arcsin(17/40)`, about
`50.30°`": `50.295° < θ₀ < 50.305°`. -/
theorem intro_theta0_approx : deg 50.295 < θ₀ ∧ θ₀ < deg 50.305 := Proofs.intro_theta0_approx_proved

/-! ## Section 2 (reduction to pairs of points on the circle `|z| = ½`) -/

/-- sec_02_reduction.tex:5: "For `f ∈ 𝒮` and distinct points `z, w ∈ 𝔻` we have `f(z) ≠ f(w)`". -/
theorem sec2_f_ne (f : ℂ → ℂ) (hf : InS f) (z w : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1)
    (hzw : z ≠ w) : f z ≠ f w := Proofs.sec2_f_ne_proved f hf z w hz hw hzw

/-- sec_02_reduction.tex:9: "The quotient `Q_f` is symmetric in `z` and `w`" (for every `f`, `z`, `w`). -/
theorem sec2_Q_symm (f : ℂ → ℂ) (z w : ℂ) : Q f z w = Q f w z := Proofs.sec2_Q_symm_proved f z w

/-- Lemma 2.1 (sec_02_reduction.tex:11-17): for `f ∈ 𝒮` and distinct `z, w ∈ 𝔻`,
`Γ f(z) - Γ f(w) = ½ (f(z) - f(w)) Q_f(z, w)`; in particular `Γ f(z) = Γ f(w)` iff `Q_f(z, w) = 0`. -/
theorem lem_2_1 (f : ℂ → ℂ) (hf : InS f) (z w : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1)
    (hzw : z ≠ w) :
    Gam f z - Gam f w = (1 / 2 : ℂ) * (f z - f w) * Q f z w ∧ (Gam f z = Gam f w ↔ Q f z w = 0) := Proofs.lem_2_1_proved f hf z w hz hw hzw

/-- Lemma 2.2 (sec_02_reduction.tex:25-27): let `ρ > 0` and let `G` be holomorphic on a neighbourhood of the closed
disc `|z| ≤ ρ`. If `G` is injective on the circle `|z| = ρ`, then `G` is injective on the closed disc.
PROVED GIVEN the argument principle and the Jordan curve theorem (Lean's library has neither). -/
theorem lem_2_2 (hAP : FactArgumentPrinciple) (hJ : FactJordanCurve) (G : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hG : HolomorphicNearClosedDisc G ρ) (hinj : Set.InjOn G (sphere (0 : ℂ) ρ)) :
    Set.InjOn G (closedBall (0 : ℂ) ρ) := Proofs.lem_2_2_proved hAP hJ G ρ hρ hG hinj

/-- Lemma 2.3, rotation (sec_02_reduction.tex:39-40): for `f ∈ 𝒮` and real `φ`, the rotation
`f_φ(z) = e^{-iφ} f(e^{iφ} z)` belongs to `𝒮`, and `Q_{f_φ}(z, w) = Q_f(e^{iφ} z, e^{iφ} w)` (for all `z, w ∈ 𝔻`). -/
theorem lem_2_3_rot (f : ℂ → ℂ) (hf : InS f) (φ : ℝ) :
    InS (rotate φ f) ∧ ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
      Q (rotate φ f) z w = Q f (exp ((φ : ℂ) * I) * z) (exp ((φ : ℂ) * I) * w) := Proofs.lem_2_3_rot_proved f hf φ

/-- Lemma 2.3, dilation (sec_02_reduction.tex:40): for `f ∈ 𝒮` and `0 < r ≤ ½`, the dilation `F(u) = f(2ru)/(2r)`
belongs to `𝒮`, and `Q_F(z, w) = Q_f(2rz, 2rw)` (for all `z, w ∈ 𝔻`). -/
theorem lem_2_3_dil (f : ℂ → ℂ) (hf : InS f) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1 / 2) :
    InS (dilate r f) ∧ ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
      Q (dilate r f) z w = Q f (2 * (r : ℂ) * z) (2 * (r : ℂ) * w) := Proofs.lem_2_3_dil_proved f hf r hr hr'

/-- sec_02_reduction.tex:47-50: "Two distinct points on the circle `|z| = ½` have an angular distance `θ ∈ (0, π]`;
after naming them suitably they are `z = ½ e^{i(φ + θ/2)}` and `w = ½ e^{i(φ - θ/2)}` for some real `φ`. By
Lemma 2.3, `Q_f(z, w) = Q_{f_φ}(z_θ, \overline{z_θ})`." -/
theorem sec2_pair_normal_form (z w : ℂ) (hz : ‖z‖ = 1 / 2) (hw : ‖w‖ = 1 / 2) (hzw : z ≠ w) :
    ∃ φ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi ∧
      ((z = (1 / 2 : ℂ) * exp (((φ + θ / 2 : ℝ) : ℂ) * I) ∧ w = (1 / 2 : ℂ) * exp (((φ - θ / 2 : ℝ) : ℂ) * I)) ∨
        (w = (1 / 2 : ℂ) * exp (((φ + θ / 2 : ℝ) : ℂ) * I) ∧ z = (1 / 2 : ℂ) * exp (((φ - θ / 2 : ℝ) : ℂ) * I))) ∧
      ∀ f : ℂ → ℂ, InS f → Q f z w = Q (rotate φ f) (zθ θ) (conj (zθ θ)) := Proofs.sec2_pair_normal_form_proved z w hz hw hzw

/-- sec_02_reduction.tex:51: "So the values of `Q_f` on pairs of distinct points of the circle, over all `f ∈ 𝒮`,
are exactly the values `Q_f(z_θ, \overline{z_θ})`, over all `f ∈ 𝒮` and `0 < θ ≤ π`." -/
theorem sec2_values_eq :
    {v : ℂ | ∃ f : ℂ → ℂ, InS f ∧ ∃ z w : ℂ, ‖z‖ = 1 / 2 ∧ ‖w‖ = 1 / 2 ∧ z ≠ w ∧ v = Q f z w} =
      {v : ℂ | ∃ f : ℂ → ℂ, InS f ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi ∧ v = Q f (zθ θ) (conj (zθ θ))} := Proofs.sec2_values_eq_proved

/-- Proposition 2.4 (sec_02_reduction.tex:53-55): suppose that `Re Q_f(z_θ, \overline{z_θ}) > 0` for every `f ∈ 𝒮`
and every `θ ∈ (0, π]`. Then Theorems 1.1 and 1.2 hold (the sharpness of `1/2` in Theorem 1.1 is the Koebe
function, Proposition 2.5). PROVED GIVEN the facts of Lemma 2.2. -/
theorem prop_2_4 (hAP : FactArgumentPrinciple) (hJ : FactJordanCurve)
    (h : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re) :
    ((∀ f : ℂ → ℂ, InS f → Set.InjOn (Gam f) (closedBall (0 : ℂ) (1 / 2))) ∧
        ∀ r : ℝ, 1 / 2 < r → ∃ f : ℂ → ℂ, InS f ∧ ¬ Set.InjOn (Gam f) (ball (0 : ℂ) r)) ∧
      (∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r → z ≠ w →
        0 < (Q f z w).re) :=
  ⟨⟨(Proofs.prop_2_4_proved hAP hJ h).1, fun r hr => ⟨koebe, Proofs.koebe_mem_S_proved, Proofs.prop_2_5_proved.2.2.2 r hr⟩⟩,
    (Proofs.prop_2_4_proved hAP hJ h).2⟩

/-- The Koebe function belongs to `𝒮` (used by sec_01_intro.tex:9, sec_02_reduction.tex:61-68 and Theorem 1.1's
"sharp"). -/
theorem koebe_mem_S : InS koebe := Proofs.koebe_mem_S_proved

/-- Proposition 2.5 (sec_02_reduction.tex:63-69): for the Koebe function `k(z) = z/(1-z)²`,
`Γ k(z) = z/(1-z)³` and `(Γ k)'(z) = (1 + 2z)/(1-z)⁴` (in `𝔻`); hence `(Γ k)'(-½) = 0`, and `Γ k` is not injective on
`𝔻_r` for any `r > ½`. -/
theorem prop_2_5 :
    (∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → Gam koebe z = z / (1 - z) ^ 3) ∧
      (∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → deriv (Gam koebe) z = (1 + 2 * z) / (1 - z) ^ 4) ∧
      deriv (Gam koebe) (-1 / 2) = 0 ∧
      ∀ r : ℝ, 1 / 2 < r → ¬ Set.InjOn (Gam koebe) (ball (0 : ℂ) r) := Proofs.prop_2_5_proved

/-- sec_02_reduction.tex:75: "as `z` and `w` tend to `-½` along the circle, `Q_k(z, w)`
tends to `0`. In the normalized position this happens for the rotation `k_π(z) = -k(-z)` as `θ → 0`." -/
theorem sec2_koebe_limit :
    Tendsto (fun p : ℂ × ℂ => Q koebe p.1 p.2)
        (𝓝[{p : ℂ × ℂ | ‖p.1‖ = 1 / 2 ∧ ‖p.2‖ = 1 / 2 ∧ p.1 ≠ p.2}] ((-1 / 2 : ℂ), (-1 / 2 : ℂ))) (𝓝 0) ∧
      (∀ z : ℂ, rotate Real.pi koebe z = -koebe (-z)) ∧
      Tendsto (fun θ : ℝ => Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))) (𝓝[>] 0) (𝓝 0) := Proofs.sec2_koebe_limit_proved

/-! ## Section 3 (classical tools) -/

/-- sec_03_tools.tex:13: "`f'(a) ≠ 0` because `f` is injective" (for `f ∈ 𝒮` and every `a ∈ 𝔻`). -/
theorem sec3_deriv_ne_zero (f : ℂ → ℂ) (hf : InS f) (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) : deriv f a ≠ 0 := Proofs.sec3_deriv_ne_zero_proved f hf a ha

/-- sec_03_tools.tex:9-13: for `f ∈ 𝒮` and `a ∈ 𝔻` the Koebe transform `f_a` again belongs to `𝒮`. -/
theorem sec3_koebe_transform_mem_S (f : ℂ → ℂ) (hf : InS f) (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    InS (koebeTransform f a) := Proofs.sec3_koebe_transform_mem_S_proved f hf a ha

/-- sec_03_tools.tex:24: for `g ∈ 𝒮`, `(g(s) - g(t))/(s - t)`, extended by `g'(s)` on the diagonal, has no zero on
`𝔻 x 𝔻` and equals `1` at the origin, "and so does `g(s)/s` on `𝔻`" (extended by `g'(0) = 1` at `s = 0`). -/
theorem sec3_kernel_nonvanishing (g : ℂ → ℂ) (hg : InS g) :
    (∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      (if s = t then deriv g s else (g s - g t) / (s - t)) ≠ 0) ∧ deriv g 0 = 1 ∧
      ∀ s : ℂ, s ∈ ball (0 : ℂ) 1 → (if s = 0 then deriv g 0 else g s / s) ≠ 0 := Proofs.sec3_kernel_nonvanishing_proved g hg

/-- sec_03_tools.tex:24-28: for `g ∈ 𝒮` the Grunsky kernel `K_g` is a holomorphic function on `𝔻 x 𝔻` that vanishes
when `s = 0` or `t = 0`, with coefficients `γ_{nm} = γ_{mn}`: Grunsky coefficients exist and are symmetric.
PROVED GIVEN the power series of holomorphic functions on the bidisc. -/
theorem sec3_grunsky_exists (hB : FactBidiscPowerSeries) (g : ℂ → ℂ) (hg : InS g) :
    ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n := Proofs.sec3_grunsky_exists_proved hB g hg

/-- sec_03_tools.tex:28 ("the Grunsky coefficients of `g`"): two families with the property `IsGrunskyCoeff g` agree, so
the predicate names the paper's coefficients. -/
theorem sec3_grunsky_unique (g : ℂ → ℂ) (hg : InS g) (γ γ' : ℕ → ℕ → ℂ) (h : IsGrunskyCoeff g γ)
    (h' : IsGrunskyCoeff g γ') : γ = γ' := Proofs.sec3_grunsky_unique_proved g hg γ γ' h h'

/-- sec_03_tools.tex:32-35 (eq:cauchy): "In particular, for all `x, y ∈ ℓ²`, `|xᵀ C(g) y| ≤ ‖x‖ ‖y‖`" (the bilinear form
as iterated sums, which converge). PROVED GIVEN the strong Grunsky inequality. -/
theorem sec3_cauchy (hG : FactGrunsky) (g : ℂ → ℂ) (hg : InS g) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff g γ)
    (x y : ℕ → ℂ) (hx : Summable fun n => ‖x n‖ ^ 2) (hy : Summable fun n => ‖y n‖ ^ 2) :
    (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
      ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2) := Proofs.sec3_cauchy_proved hG g hg γ hγ x y hx hy

open Classical in
/-- sec_03_tools.tex:36: "The same bound holds for every principal block of `C(g)` and for every compression `Vᵀ C(g) V`
by a matrix `V` with orthonormal columns" (a principal block: rows and columns in a set `S`; `k` columns in `ℓ²`).
PROVED GIVEN the strong Grunsky inequality. -/
theorem sec3_blocks_compressions (hG : FactGrunsky) (g : ℂ → ℂ) (hg : InS g) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff g γ) :
    (∀ (S : Set ℕ) (x y : ℕ → ℂ), Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
      ‖bilinf x (fun n m => if n ∈ S ∧ m ∈ S then Cmat γ n m else 0) y‖ ≤
        Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2)) ∧
    ∀ (k : ℕ) (V : ℕ → Fin k → ℂ),
      (∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) →
      ∀ x y : Fin k → ℂ, ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) * y j‖ ≤
        Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2) := Proofs.sec3_blocks_compressions_proved hG g hg γ hγ

/-- sec_03_tools.tex:39-43: for `f ∈ 𝒮` the odd square root `h(s) = √(f(s²))` exists. -/
theorem sec3_oddroot_exists (f : ℂ → ℂ) (hf : InS f) : ∃ h : ℂ → ℂ, IsOddRoot f h := Proofs.sec3_oddroot_exists_proved f hf

/-- sec_03_tools.tex:43: "`h ∈ 𝒮`". -/
theorem sec3_oddroot_mem_S (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) : InS h := Proofs.sec3_oddroot_mem_S_proved f h hf hh

/-- sec_03_tools.tex:43: "Because `h` is odd, `K_h(-s, -t) = K_h(s, t)`, so `γ_{nm}(h) = 0` unless `n + m` is even." -/
theorem sec3_oddroot_parity (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff h γ) :
    (∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → kser γ (-s) (-t) = kser γ s t) ∧
      ∀ n m : ℕ, (n + m) % 2 = 1 → γ n m = 0 := Proofs.sec3_oddroot_parity_proved f h hf hh γ hγ

/-- sec_03_tools.tex:43: "The Grunsky matrix of `h` therefore splits into the block `O` of odd indices and the block `E`
of even indices, and both are complex symmetric contractions" (contractions: every finite section).
PROVED GIVEN the strong Grunsky inequality. -/
theorem sec3_OE_contractions (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) :
    (∀ n m : ℕ, Oblock γ n m = Oblock γ m n) ∧ (∀ n m : ℕ, Eblock γ n m = Eblock γ m n) ∧
      (∀ n m : ℕ, Cmat γ n m = Oblock γ n m + Eblock γ n m) ∧
      ∀ (N : ℕ) (x y : ℕ → ℂ),
        ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Oblock γ n m * y m‖ ≤
            Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) ∧
          ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
            Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) := Proofs.sec3_OE_contractions_proved_from sec3_grunsky_unique hG f h hf hh γ hγ

/-- sec_03_tools.tex:45-47: "`∑_{n,m odd} γ_{nm}(h) sⁿ tᵐ = a(s)ᵀ O a(t)`, and similarly for the even indices". -/
theorem sec3_block_sums (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    HasSum (fun nm : ℕ × ℕ => if nm.1 % 2 = 1 ∧ nm.2 % 2 = 1 then γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 else 0)
        (bilinf (aOdd s) (Oblock γ) (aOdd t)) ∧
      HasSum (fun nm : ℕ × ℕ => if nm.1 % 2 = 0 ∧ nm.2 % 2 = 0 then γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 else 0)
        (bilinf (aEven s) (Eblock γ) (aEven t)) := Proofs.sec3_block_sums_proved f h hf hh γ hγ s t hs ht

/-- sec_03_tools.tex:49-51: for `f ∈ 𝒮`, `p(z) = z f'(z)/f(z)` is holomorphic on `𝔻`, "has no zero in `𝔻` and equals
`1` at `z = 0`". -/
theorem sec3_p_ne_zero (f : ℂ → ℂ) (hf : InS f) :
    DifferentiableOn ℂ (pfun f) (ball (0 : ℂ) 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, pfun f z ≠ 0) ∧ pfun f 0 = 1 := Proofs.sec3_p_ne_zero_proved f hf

/-- Lemma 3.1(i) (sec_03_tools.tex:56-57): `2 a(s)ᵀ O a(t) = K_h(s, t) - K_h(s, -t)`, and for `s ≠ ±t`,
`exp(2 a(s)ᵀ O a(t)) = ((h(s) - h(t))/(h(s) + h(t))) · ((s + t)/(s - t))`. -/
theorem lem_3_1_i (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
      (s ≠ t → s ≠ -t →
        exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))) := Proofs.lem_3_1_i_proved f h hf hh γ hγ s t hs ht

/-- Lemma 3.1(ii) (sec_03_tools.tex:58): `2 a_e(s)ᵀ E a_e(t) = K_h(s, t) + K_h(s, -t) = K_f(z, w)` (`z = s²`, `w = t²`;
`γf` the Grunsky coefficients of `f`). -/
theorem lem_3_1_ii (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (hγf : IsGrunskyCoeff f γf) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    2 * bilinf (aEven s) (Eblock γ) (aEven t) = kser γ s t + kser γ s (-t) ∧
      kser γ s t + kser γ s (-t) = kser γf (s ^ 2) (t ^ 2) := Proofs.lem_3_1_ii_proved f h hf hh γ γf hγ hγf s t hs ht

/-- Lemma 3.1(iii) (sec_03_tools.tex:59): `log p(z) = 2 a(s)ᵀ O a(s)` (`z = s²`), the logarithm vanishing at `0`: the
function `s ↦ 2 a(s)ᵀ O a(s)` is continuous on `𝔻`, vanishes at `0`, and its exponential is `p(s²)`. -/
theorem lem_3_1_iii (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) :
    ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
      2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
      ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2) := Proofs.lem_3_1_iii_proved f h hf hh γ hγ

/-- sec_03_tools.tex:67-70 (eq:Kf): "the even block is the Grunsky matrix of `f` itself: `E_{2n,2m} = √(nm) γ_{nm}(f)`",
and `K_f(z, w) = α(z)ᵀ C(f) α(w)` for `z, w ∈ 𝔻`. -/
theorem eq_Kf (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (hγf : IsGrunskyCoeff f γf) :
    (∀ n m : ℕ, Eblock γ (2 * n) (2 * m) = Cmat γf n m) ∧
      ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
        kser γf z w = bilinf (alphaV z) (Cmat γf) (alphaV w) := Proofs.eq_Kf_proved f h hf hh γ γf hγ hγf

/-- sec_03_tools.tex:72-79 (eq:gram): on `|s|² = ½` (`z = s²`): `‖a(s)‖² = artanh ½`, `a(s)ᵀ a(s) = artanh z`,
`‖a_e(s)‖² = -½ log ¾`, `a_e(s)ᵀ a_e(s) = -½ log(1 - z²)`. -/
theorem eq_gram (s : ℂ) (hs : ‖s‖ ^ 2 = 1 / 2) :
    HasSum (fun n => ‖aOdd s n‖ ^ 2) Ao ∧ HasSum (fun n => aOdd s n ^ 2) (cartanh (s ^ 2)) ∧
      HasSum (fun n => ‖aEven s n‖ ^ 2) Ae ∧
      HasSum (fun n => aEven s n ^ 2) (-(1 / 2 : ℂ) * log (1 - (s ^ 2) ^ 2)) := Proofs.eq_gram_proved s hs

/-! ## Section 4 (nearby pairs): the rows without power series -/

/-- sec_04_near.tex:36-48, the pair seen from its midpoint: for `θ ∈ (0, π]`, `τ = ½ cos(θ/2)`, `y = ½ sin(θ/2)`:
`z_θ = τ + iy`, `τ² + y² = ¼`, `g(z) = -f(-z)` (the rotation of Lemma 2.3 with `φ = π`),
`Q_f(z_θ, \overline{z_θ}) = Q_g(-τ - iy, -τ + iy)`,
`sin²(θ/2)/80 = y²/20`, and `θ ≤ θ₀ ⇔ y ≤ y₀`. -/
theorem sec4_midpoint (f : ℂ → ℂ) (hf : InS f) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    zθ θ = ((Real.cos (θ / 2) / 2 : ℝ) : ℂ) + ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I ∧
      (Real.cos (θ / 2) / 2) ^ 2 + (Real.sin (θ / 2) / 2) ^ 2 = 1 / 4 ∧
      (∀ z : ℂ, rotate Real.pi f z = -f (-z)) ∧
      Q f (zθ θ) (conj (zθ θ)) =
        Q (rotate Real.pi f) (-((Real.cos (θ / 2) / 2 : ℝ) : ℂ) - ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I)
          (-((Real.cos (θ / 2) / 2 : ℝ) : ℂ) + ((Real.sin (θ / 2) / 2 : ℝ) : ℂ) * I) ∧
      Real.sin (θ / 2) ^ 2 / 80 = (Real.sin (θ / 2) / 2) ^ 2 / 20 ∧ (θ ≤ θ₀ ↔ Real.sin (θ / 2) / 2 ≤ y0) := Proofs.sec4_midpoint_proved f hf θ h0 hπ

/-- sec_04_near.tex:40-47: Proposition 4.1 is equivalent to (sec4:goal): `Re Q_f(-τ + iy, -τ - iy) ≥ y²/20` for
`f ∈ 𝒮` and `0 < y ≤ y₀ = 17/80`, `τ = √(¼ - y²)` ("As `f ↦ g` is a bijection of `𝒮` and `Q` is symmetric",
sec_04_near.tex:44, with `g(z) = -f(-z)`). -/
theorem sec4_goal_equiv :
    (∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
        Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re) ↔
      ∀ f : ℂ → ℂ, InS f → ∀ y : ℝ, 0 < y → y ≤ y0 →
        y ^ 2 / 20 ≤ (Q f (-((Real.sqrt (1 / 4 - y ^ 2) : ℝ) : ℂ) + (y : ℂ) * I)
          (-((Real.sqrt (1 / 4 - y ^ 2) : ℝ) : ℂ) - (y : ℂ) * I)).re := Proofs.sec4_goal_equiv_proved

/-- sec_04_near.tex:48-51: for `0 < y ≤ y₀` and `τ = √(¼ - y²)`: `τ² ≥ 1311/6400 > (9/20)²`, so `9/20 < τ < ½`;
`Ψ = 1 - τ² ∈ [¾, 1]` and `τ₁ = τ/Ψ ≤ ⅔`. -/
theorem sec4_tau_bounds (y : ℝ) (hy : 0 < y) (hy0 : y ≤ y0) :
    1311 / 6400 ≤ Real.sqrt (1 / 4 - y ^ 2) ^ 2 ∧ (9 / 20 : ℝ) ^ 2 < 1311 / 6400 ∧
      9 / 20 < Real.sqrt (1 / 4 - y ^ 2) ∧ Real.sqrt (1 / 4 - y ^ 2) < 1 / 2 ∧
      3 / 4 ≤ vτ (Real.sqrt (1 / 4 - y ^ 2)) ∧ vτ (Real.sqrt (1 / 4 - y ^ 2)) ≤ 1 ∧
      βτ (Real.sqrt (1 / 4 - y ^ 2)) ≤ 2 / 3 := Proofs.sec4_tau_bounds_proved y hy hy0

/-- sec_04_near.tex:53-60: for `f ∈ 𝒮` and `9/20 < τ < ½`, the Koebe transform `f_{-τ}` belongs to `𝒮`; with
`A = a₂(f_{-τ})`, `|A| ≤ 2` (Bieberbach's inequality, the case `n = 2` of de Branges' theorem); `c = A/2` has `|c| ≤ 1`, `e ∈ [0, 4]`, `η ∈ [0, 1]`.
PROVED GIVEN de Branges' theorem. -/
theorem sec4_c_bounds (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 < τ) (h2 : τ < 1 / 2) :
    InS (koebeTransform f (-(τ : ℂ))) ∧ ‖coeff (koebeTransform f (-(τ : ℂ))) 2‖ ≤ 2 ∧
      ‖coeff (koebeTransform f (-(τ : ℂ))) 2 / 2‖ ≤ 1 ∧
      0 ≤ edef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ∧ edef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ≤ 4 ∧
      0 ≤ etadef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ∧
      etadef (coeff (koebeTransform f (-(τ : ℂ))) 2 / 2) ≤ 1 := Proofs.sec4_c_bounds_proved hDB f hf τ h1 h2

/-- sec_04_near.tex:69: "Since `Re c = 1 - ϰ/2` and `|c| ≥ |Re c|`, we have `η ≤ ϰ - ϰ²/4`. In particular `ϰ = 0` forces
`c = 1`, `η = 0`" (for `|c| ≤ 1`). -/
theorem sec4_eta_le (c : ℂ) (hc : ‖c‖ ≤ 1) :
    etadef c ≤ edef c - edef c ^ 2 / 4 ∧ (edef c = 0 → c = 1 ∧ etadef c = 0) := Proofs.sec4_eta_le_proved c hc

/-- sec_04_near.tex:70-73 (sec4:rho): for `|c| ≤ 1`, `c ≠ 1`: `e > 0`, `ρ = η/e ∈ [0, 1 - e/4]`, so `e ≤ 4(1 - ρ)`, and
`|c - ρ| = 1 - ρ`. -/
theorem sec4_rho_facts (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1) :
    0 < edef c ∧ 0 ≤ etadef c / edef c ∧ etadef c / edef c ≤ 1 - edef c / 4 ∧
      edef c ≤ 4 * (1 - etadef c / edef c) ∧ ‖c - ((etadef c / edef c : ℝ) : ℂ)‖ = 1 - etadef c / edef c := Proofs.sec4_rho_facts_proved c hc hc1

/-- sec_04_near.tex:108 and sec_01_intro.tex:73: for `|c| ≤ 1` the comparison function `u/(1 - cu)²` belongs to `𝒮`,
equals `k(cu)/c` for `c ≠ 0`, has second coefficient `2c`, and is the Koebe function when `c = 1`. -/
theorem sec4_model_mem_S (c : ℂ) (hc : ‖c‖ ≤ 1) :
    InS (fun u => u / (1 - c * u) ^ 2) ∧ (c ≠ 0 → ∀ u : ℂ, u / (1 - c * u) ^ 2 = koebe (c * u) / c) ∧
      coeff (fun u => u / (1 - c * u) ^ 2) 2 = 2 * c ∧ (c = 1 → (fun u => u / (1 - c * u) ^ 2) = koebe) := Proofs.sec4_model_mem_S_proved c hc

/-- sec_04_near.tex:112 and :120: `ν(ν + 2τ₁) = (c² - τ²)/Ψ²`; for `9/20 ≤ τ ≤ ½` and `|c| ≤ 1`: `|ν| ≤ 1/(1 - τ) ≤ 2`,
`|ν(ν + 2τ₁)| ≤ (1 + τ²)/Ψ² ≤ 20/9`, `y² = ¼ - τ² ≤ 19/400`; the denominators in (sec4:hat) stay away from `0` and `Q̂`,
`T̂` (and `Π̂_o(iy)`) are holomorphic in `c` on a neighbourhood of `|c| ≤ 1`. -/
theorem sec4_hat_bounds (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) :
    (∀ c : ℂ, nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) = (c ^ 2 - (τ : ℂ) ^ 2) / (vτ τ : ℂ) ^ 2) ∧
      (∀ c : ℂ, ‖c‖ ≤ 1 →
        ‖nuτ τ c‖ ≤ 1 / (1 - τ) ∧ ‖nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ))‖ ≤ (1 + τ ^ 2) / vτ τ ^ 2) ∧
      1 / (1 - τ) ≤ 2 ∧ (1 + τ ^ 2) / vτ τ ^ 2 ≤ 20 / 9 ∧ ysq τ ≤ 19 / 400 ∧
      ∃ R : ℝ, 1 < R ∧ DifferentiableOn ℂ (Qhat τ) (ball (0 : ℂ) R) ∧
        DifferentiableOn ℂ (That τ) (ball (0 : ℂ) R) ∧ DifferentiableOn ℂ (PihatO τ) (ball (0 : ℂ) R) ∧
        ∀ c ∈ ball (0 : ℂ) R,
          (1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) * (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)) ≠ 0 ∧
          1 - 2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) -
            (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ) ^ 2 ≠ 0 := Proofs.sec4_hat_bounds_proved τ h1 h2

/-- sec_04_near.tex:121-124 (eq:Qk): for `9/20 ≤ τ < ½`: `Q̂(τ, 1) = Q_k(τ) = y²/((½ + τ) · ¾ · (5/4 + 2τ)) ≥ (16/27) y²`,
and it is the quotient of the Koebe function itself at the pair `-τ ± iy`. -/
theorem eq_Qk (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    Qhat τ 1 = (Qk τ : ℂ) ∧ Qk τ = ysq τ / ((1 / 2 + τ) * (3 / 4) * (5 / 4 + 2 * τ)) ∧ 16 / 27 * ysq τ ≤ Qk τ ∧
      Q koebe (-(τ : ℂ) + (yτ τ : ℂ) * I) (-(τ : ℂ) - (yτ τ : ℂ) * I) = (Qk τ : ℂ) := Proofs.eq_Qk_proved τ h1 h2

/-- Lemma 4.3 (sec_04_near.tex:126-136): let `9/20 ≤ τ < ½`, `|c| ≤ 1`, `c ≠ 1`, `e = 2(1 - Re c)`, `η = 1 - |c|²`,
`ρ = η/e`. Then `Re Q̂(τ, c) ≥ Q_k(τ) + e m(ρ) ≥ (16/27) y² + e m(ρ)`, `m(ρ) = 22/25 + (21/100)ρ`. -/
theorem lem_4_3 (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1) :
    Qk τ + edef c * mρ (etadef c / edef c) ≤ (Qhat τ c).re ∧
      16 / 27 * ysq τ + edef c * mρ (etadef c / edef c) ≤ Qk τ + edef c * mρ (etadef c / edef c) := Proofs.lem_4_3_proved τ h1 h2 c hc hc1

/-- sec_04_near.tex:139-147 (sec4:circle), the boundary step of Lemma 4.3: for `9/20 ≤ τ < ½`, `|c| = 1`, `c₁ = Re c`,
`e = 2(1 - c₁)`: `Re Q̂ ≥ Q_k + (13/10)e - (21/200)e² = Q_k + (1 - c₁)(109/50 + (21/50)c₁)`. -/
theorem sec4_circle (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ = 1) :
    Qk τ + 13 / 10 * edef c - 21 / 200 * edef c ^ 2 ≤ (Qhat τ c).re ∧
      13 / 10 * edef c - 21 / 200 * edef c ^ 2 = (1 - c.re) * (109 / 50 + 21 / 50 * c.re) := Proofs.sec4_circle_proved τ h1 h2 c hc

/-- Lemma 4.4(iv) (sec_04_near.tex:181-185): for `9/20 ≤ τ ≤ ½` with `0 < y ≤ y₀`, `|c| ≤ 1`, and a cap
`|ν| ≤ ν⁺ ≤ 2` (as printed): `|T̂| ≤ T⁺` and `|Π̂_o(iy)| ≥ Π̂₋`. -/
theorem lem_4_4_iv (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy : 0 < yτ τ) (hy0 : yτ τ ≤ y0) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) :
    ‖That τ c‖ ≤ TPlusOf νp ∧ PihatLowOf νp ≤ ‖PihatO τ c‖ := Proofs.lem_4_4_iv_proved τ h1 h2 hy hy0 c hc νp hν hνp

/-- Proof of Lemma 4.4(iv) (sec_04_near.tex:208), first line of the display: the numerator of `T̂` satisfies
`|-4τν³ + (6 + 2τ²/Ψ)ν² + (4τ/Ψ²)ν - Q_0(ν⁴ + 2τ₁ν³)y²| ≤ 2(ν⁺)³ + (20/3)(ν⁺)² + (32/9)ν⁺ + (16/3)((ν⁺)⁴ + (4/3)(ν⁺)³)y₀²`
(Lean's `vτ`, `βτ`, `Dτ`, `ysq` are `Ψ`, `τ₁`, `Q_0`, `y²`). -/
theorem sec4_That_num (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) :
    ‖-4 * τ * nuτ τ c ^ 3 + (6 + 2 * τ ^ 2 / (vτ τ : ℂ)) * nuτ τ c ^ 2 + 4 * τ / (vτ τ : ℂ) ^ 2 * nuτ τ c -
        Dτ τ c * (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ)‖ ≤
      2 * νp ^ 3 + 20 / 3 * νp ^ 2 + 32 / 9 * νp + 16 / 3 * (νp ^ 4 + 4 / 3 * νp ^ 3) * y0 ^ 2 := Proofs.sec4_That_num_proved τ h1 h2 hy0 c hc νp hν

/-- Proof of Lemma 4.4(iv) (sec_04_near.tex:208), second line of the display and the last sentence: the denominator
of `T̂` satisfies `|1 - 2τ₁νy² - (ν⁴ + 2τ₁ν³)y⁴| ≥ 1 - (4/3)ν⁺y₀² - ((ν⁺)⁴ + (4/3)(ν⁺)³)y₀⁴`, and since `ν⁺ ≤ 2` this
is at least `1 - (8/3)y₀² - (80/3)y₀⁴ > 4/5`. -/
theorem sec4_That_den (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) (c : ℂ)
    (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) :
    1 - 4 / 3 * νp * y0 ^ 2 - (νp ^ 4 + 4 / 3 * νp ^ 3) * y0 ^ 4 ≤
        ‖1 - 2 * (βτ τ : ℂ) * nuτ τ c * (ysq τ : ℂ) - (nuτ τ c ^ 4 + 2 * (βτ τ : ℂ) * nuτ τ c ^ 3) * (ysq τ : ℂ) ^ 2‖ ∧
      1 - 8 / 3 * y0 ^ 2 - 80 / 3 * y0 ^ 4 ≤ 1 - 4 / 3 * νp * y0 ^ 2 - (νp ^ 4 + 4 / 3 * νp ^ 3) * y0 ^ 4 ∧
      (4 / 5 : ℝ) < 1 - 8 / 3 * y0 ^ 2 - 80 / 3 * y0 ^ 4 := Proofs.sec4_That_den_proved τ h1 h2 hy0 c νp hν hνp

/-- Proof of Lemma 4.4(iv) (sec_04_near.tex:208), the bounds used in (sec4:hat): with `|ν| ≤ ν⁺`, `2τ ≤ 1`:
`τ²/Ψ ≤ 1/3`, `τ/Ψ² ≤ 8/9`, `|Q_0| ≤ 16/3` and `|2τ₁ν| ≤ (4/3)ν⁺`. -/
theorem sec4_hat_elem_bounds (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) :
    τ ^ 2 / vτ τ ≤ 1 / 3 ∧ τ / vτ τ ^ 2 ≤ 8 / 9 ∧ ‖Dτ τ c‖ ≤ 16 / 3 ∧
      ‖2 * (βτ τ : ℂ) * nuτ τ c‖ ≤ 4 / 3 * νp := Proofs.sec4_hat_elem_bounds_proved τ h1 h2 c hc νp hν

/-- Proof of Lemma 4.4(iv) (sec_04_near.tex:208): "`T⁺` and `Π̂₋` are the quotients of the right-hand sides" of the
display. -/
theorem sec4_hat_quotients (νp : ℝ) :
    TPlusOf νp = (2 * νp ^ 3 + 20 / 3 * νp ^ 2 + 32 / 9 * νp + 16 / 3 * (νp ^ 4 + 4 / 3 * νp ^ 3) * y0 ^ 2) /
        (1 - 4 / 3 * νp * y0 ^ 2 - (νp ^ 4 + 4 / 3 * νp ^ 3) * y0 ^ 4) ∧
      PihatLowOf νp = (1 - min (20 / 9) (νp ^ 2 + 4 / 3 * νp) * y0 ^ 2) / (1 + νp ^ 2 * y0 ^ 2) ^ 2 := Proofs.sec4_hat_quotients_proved νp

/-- Proof of Lemma 4.4(iv) (sec_04_near.tex:208), third line of the display: the numerator of `Π̂_o(iy)` satisfies
`|1 - ν(ν + 2τ₁)y²| ≥ 1 - min(20/9, (ν⁺)² + (4/3)ν⁺)y₀²`, from `|ν(ν + 2τ₁)| ≤ min(20/9, (ν⁺)² + (4/3)ν⁺)`. -/
theorem sec4_PihatO_num (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) :
    ‖nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ))‖ ≤ min (20 / 9) (νp ^ 2 + 4 / 3 * νp) ∧
      1 - min (20 / 9) (νp ^ 2 + 4 / 3 * νp) * y0 ^ 2 ≤
        ‖1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ)‖ := Proofs.sec4_PihatO_num_proved τ h1 h2 hy0 c hc νp hν

/-- Proof of Lemma 4.4(iv) (sec_04_near.tex:208), fourth line of the display: the denominator of `Π̂_o(iy)` satisfies
`|1 + ν²y²|² ≤ (1 + (ν⁺)²y₀²)²`. -/
theorem sec4_PihatO_den (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (hy0 : yτ τ ≤ y0) (c : ℂ)
    (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) :
    ‖1 + nuτ τ c ^ 2 * (ysq τ : ℂ)‖ ^ 2 ≤ (1 + νp ^ 2 * y0 ^ 2) ^ 2 := Proofs.sec4_PihatO_den_proved τ h1 h2 hy0 c νp hν

/-- Lemma 4.5(i) (sec_04_near.tex:220-228): for `9/20 ≤ τ < ½` and `|c| ≤ 1`, with `T_j` the printed closed form
(`ξ = iy`), `∑_{j=2}^{5} |T_j|²/(2j - 1) ≤ 20 + 130e`. -/
theorem lem_4_5_i (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ∑ j ∈ Finset.Icc 2 5, ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) ≤ 20 + 130 * edef c := Proofs.lem_4_5_i_proved τ h1 h2 c hc

/-- sec_04_near.tex:143 and :239: "Let `𝒫(c)` and `𝒥(c)` be `Ψ⁴` times the numerator and the denominator of `Q̂`"
with "`𝒥(c) = (Ψ² + (c - τ)²y²)(Ψ² - (c² - τ²)y²)`" (:143, recalled at :239), "the factor
`4 - 7τ² = 4Ψ²(1 + τ₁²y²)`" and "Since `4 - 7τ² ≥ 9/4`": the denominator of `Q̂` is `(1 + ν²y²)(1 - ν(ν + 2τ₁)y²)`
(sec4_hat_bounds); the identity holds for every `c`. -/
theorem sec4_Qcal (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) :
    (vτ τ : ℂ) ^ 4 * ((1 + nuτ τ c ^ 2 * (ysq τ : ℂ)) *
        (1 - nuτ τ c * (nuτ τ c + 2 * (βτ τ : ℂ)) * (ysq τ : ℂ))) =
      ((vτ τ : ℂ) ^ 2 + (c - τ) ^ 2 * (ysq τ : ℂ)) * ((vτ τ : ℂ) ^ 2 - (c ^ 2 - (τ : ℂ) ^ 2) * (ysq τ : ℂ)) ∧
    4 - 7 * τ ^ 2 = 4 * vτ τ ^ 2 * (1 + βτ τ ^ 2 * ysq τ) ∧ (9 / 4 : ℝ) ≤ 4 - 7 * τ ^ 2 :=
  Proofs.sec4_Qcal_proved τ h1 h2 c

/-- sec_04_near.tex:239: "the `T_j` are holomorphic in `c` there", that is near the closed disc `|c| ≤ 1`: here on a
disc of radius `R > 1`, for every `j`. -/
theorem sec4_TJ_holo (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    ∃ R : ℝ, 1 < R ∧ ∀ j : ℕ, DifferentiableOn ℂ (fun c => TJ τ c j) (ball (0 : ℂ) R) :=
  Proofs.sec4_TJ_holo_proved τ h1 h2

/-- Lemma 4.7 (sec_04_near.tex:286-288): let `9/20 ≤ τ ≤ ½`, `|c| ≤ 1`, `e > 0` and `ρ ≥ ρ₋`. Then
`|ν| ≤ max(20/29, 2 - (8/3)ρ₋)` and `η ≤ 4ρ(1 - ρ)`. -/
theorem lem_4_7 (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (he : 0 < edef c) (ρm : ℝ)
    (hρ : ρm ≤ etadef c / edef c) :
    ‖nuτ τ c‖ ≤ max (20 / 29) (2 - 8 / 3 * ρm) ∧
      etadef c ≤ 4 * (etadef c / edef c) * (1 - etadef c / edef c) := Proofs.lem_4_7_proved τ h1 h2 c hc he ρm hρ

/-- sec_04_near.tex:330: "The numbers in Lemma 4.8 are the caps of Lemmas 4.5 and 4.6 for a cell ...; by Lemma 4.7 and
(sec4:rho), they are valid for every `f` whose `ρ` lies in the cell": for `9/20 ≤ τ ≤ ½`, `|c| ≤ 1`, `c ≠ 1` and
`ρ = η/e ∈ [i/256, (i+1)/256]`: `|ν| ≤ ν⁺ ≤ 2`, `η ≤ η⁺ ≤ 1`, `e ≤ e⁺`, `(M + 130e)^{1/2} ≤ n⁺`. -/
theorem sec4_caps_valid (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (hc1 : c ≠ 1) (i : ℕ)
    (hi : i ≤ 255) (hlo : (i : ℝ) / 256 ≤ etadef c / edef c) (hhi : etadef c / edef c ≤ ((i : ℝ) + 1) / 256) :
    ‖nuτ τ c‖ ≤ nuPlus ((i : ℝ) / 256) ∧ nuPlus ((i : ℝ) / 256) ≤ 2 ∧
      etadef c ≤ etaPlus ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ∧
      etaPlus ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ≤ 1 ∧ edef c ≤ ePlus ((i : ℝ) / 256) ∧
      Real.sqrt (Mcap ((i : ℝ) / 256) + 130 * edef c) ≤ nPlus ((i : ℝ) / 256) := Proofs.sec4_caps_valid_proved τ h1 h2 c hc hc1 i hi hlo hhi

/-- sec_04_near.tex:31: the Koebe quotient is of the exact order `sin²(θ/2)` for nearby points (for `k_π`, in the
normal position), so the bound of Proposition 4.1 cannot hold with a fixed positive constant in place of
`sin²(θ/2)/80`. -/
theorem sec4_no_constant :
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      C₁ * Real.sin (θ / 2) ^ 2 ≤ (Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))).re ∧
        (Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))).re ≤ C₂ * Real.sin (θ / 2) ^ 2) ∧
      ∀ κ : ℝ, 0 < κ → ∃ f : ℂ → ℂ, InS f ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ θ₀ ∧ (Q f (zθ θ) (conj (zθ θ))).re < κ := Proofs.sec4_no_constant_proved

/-! ## Section 4, the power-series layer [P]: `G_τ`, `Π`, Lemma 4.2, majorants, Lemmas 4.4 (i)-(iii),
4.5 (ii)-(iii), 4.6, and the printed proof of Proposition 4.1. `φ` with `IsSqrtQuot (fT f τ) φ` carries the
coefficients `b_{2j-1} = coeff φ j` (Robinson/Defs/NearP.lean). -/

/-- sec_04_near.tex:61-65: since `f_{-τ}(u)/u` has no zero in `𝔻`, `G_τ(ζ) = (f_{-τ}(ζ⁻²))^{-1/2} = ζ - cζ⁻¹ +
∑_{j ≥ 2} b_{2j-1} ζ^{1-2j}` (`|ζ| > 1`, the branch like `ζ` at infinity) is holomorphic and odd, and it is injective.
Typed with the unique square root `φ` of `u/f_{-τ}(u)` with `φ(0) = 1` and `G_τ(ζ) = ζ φ(ζ⁻²)`. -/
theorem sec4_Gtau (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    ∃ φ : ℂ → ℂ, IsSqrtQuot (fT f τ) φ ∧
      (∀ ψ : ℂ → ℂ, IsSqrtQuot (fT f τ) ψ → Set.EqOn ψ φ (ball (0 : ℂ) 1)) ∧
      coeff φ 1 = -cOf f τ ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ ζ ^ 2 * fT f τ ((ζ ^ 2)⁻¹) = 1) ∧
      DifferentiableOn ℂ (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → Gtau φ (-ζ) = -Gtau φ ζ) ∧
      Set.InjOn (Gtau φ) {ζ : ℂ | 1 < ‖ζ‖} ∧
      ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℕ => Glaurent (cOf f τ) φ n * (ζ ^ n)⁻¹) (Gtau φ ζ - ζ) := Proofs.sec4_Gtau_proved f hf τ h1 h2

/-- (sec4:area), sec_04_near.tex:65-68: the area theorem for `G_τ` reads `|c|² + ∑_{j ≥ 2} (2j - 1)|b_{2j-1}|² ≤ 1`,
that is, `∑_{j ≥ 2} (2j - 1)|b_{2j-1}|² ≤ η`. -/
theorem sec4_area (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    Summable (fun j : ℕ => if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) ∧
      ‖cOf f τ‖ ^ 2 + ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) ≤ 1 ∧
      ∑' j : ℕ, (if 2 ≤ j then (2 * (j : ℝ) - 1) * ‖coeff φ j‖ ^ 2 else 0) ≤ etadef (cOf f τ) := Proofs.sec4_area_proved hArea f hf τ h1 h2 φ hφ

/-- sec_04_near.tex:69-70: "`ϰ = 0` forces `c = 1`, `η = 0` and `b_{2j-1} = 0` for all `j`, that is, `f_{-τ} = k`". -/
theorem sec4_e_zero (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (he : edef (cOf f τ) = 0) :
    cOf f τ = 1 ∧ etadef (cOf f τ) = 0 ∧ (∀ j : ℕ, 2 ≤ j → coeff φ j = 0) ∧
      Set.EqOn (fT f τ) koebe (ball (0 : ℂ) 1) := Proofs.sec4_e_zero_proved hArea f hf τ h1 h2 φ hφ he

/-- (sec4:Pi), sec_04_near.tex:75-83: the automorphism `u ↦ (u - τ)/(1 - τu)` sends `u = ξ/(Ψ + τξ)` to `-τ + ξ`, so
`Π(ξ) = Ψ f_{-τ}(ξ/(Ψ + τξ))`; `Π = N/(1 - νξ + B)²` with `N = ξ(1 + τ₁ξ)`; `π₁ = 1`, `π₂ = (2c - τ)/Ψ`.
Typed on `|ξ| < 1/4` (the paper: "for small ξ"; `y ≤ y₀ < 1/4`), with `Π (1 - νξ + B)² = N`. -/
theorem sec4_Pi_formula (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    (∀ ξ ∈ ball (0 : ℂ) (1 / 4),
      (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ) - (τ : ℂ)) / (1 - (τ : ℂ) * (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) = -(τ : ℂ) + ξ) ∧
      (∀ ξ ∈ ball (0 : ℂ) (1 / 4), PiF f τ ξ = (vτ τ : ℂ) * fT f τ (ξ / ((vτ τ : ℂ) + (τ : ℂ) * ξ))) ∧
      (∀ ξ ∈ ball (0 : ℂ) (1 / 4), PiF f τ ξ * Lfun τ (cOf f τ) φ ξ ^ 2 = Nfun τ ξ) ∧
      coeff (PiF f τ) 1 = 1 ∧ coeff (PiF f τ) 2 = (2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ) := Proofs.sec4_Pi_formula_proved f hf τ h1 h2 φ hφ

/-- Lemma 4.2 (sec_04_near.tex:85-93): with `Π_o(ξ) = (Π(ξ) - Π(-ξ))/(2ξ)`, `D = 2(1 - 2τc)/Ψ` and `Υ`,
`Q_f(-τ + ξ, -τ - ξ) = D + ξ² Υ(ξ)/Π_o(ξ)`; at `ξ = iy`, (sec4:QDT) `Q_f(-τ + iy, -τ - iy) = D - y²T`. Typed for
`0 < |ξ| < 1/4` (the paper, sec_04_near.tex:75: "For small ξ"). -/
theorem lem_4_2 (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    (∀ ξ : ℂ, ξ ≠ 0 → ξ ∈ ball (0 : ℂ) (1 / 4) →
      PiOddSer (coeff (PiF f τ)) ξ = (PiF f τ ξ - PiF f τ (-ξ)) / (2 * ξ) ∧
        Q f (-(τ : ℂ) + ξ) (-(τ : ℂ) - ξ) =
          Dτ τ (cOf f τ) + ξ ^ 2 * UpsSer τ (coeff (PiF f τ)) ξ / PiOddSer (coeff (PiF f τ)) ξ) ∧
      Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) = Dτ τ (cOf f τ) - (ysq τ : ℂ) * Tser τ (coeff (PiF f τ)) := Proofs.lem_4_2_proved f hf τ h1 h2

/-- sec_04_near.tex:105: "The number `Q_0 = 2 + zf''(z)/f'(z)` at `z = -τ` is the diagonal value of `Q_f`. For fixed `τ`
it depends only on `c`, and so does `π₂`" (`Q_0 = 2 - 2τπ₂`). -/
theorem sec4_D_diagonal (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    Dτ τ (cOf f τ) = 2 + -(τ : ℂ) * deriv (deriv f) (-(τ : ℂ)) / deriv f (-(τ : ℂ)) ∧
      Dτ τ (cOf f τ) = 2 - 2 * (τ : ℂ) * coeff (PiF f τ) 2 ∧
      Tendsto (fun w => Q f (-(τ : ℂ)) w) (𝓝[≠] (-(τ : ℂ))) (𝓝 (Dτ τ (cOf f τ))) := Proofs.sec4_D_diagonal_proved f hf τ h1 h2

/-- sec_04_near.tex:107-119: for the comparison function (`b_{2j-1} = 0`, `Π̂ = N/(1 - νξ)²`): `π̂₁ = 1`, `π̂₂ = π₂`,
and `Π̂_o(iy)`, `T̂`, `Q̂ = D - y²T̂` have the closed forms (sec4:hat). -/
theorem sec4_hat_closed (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    coeff (Pihat τ c) 1 = 1 ∧ coeff (Pihat τ c) 2 = (2 * c - (τ : ℂ)) / (vτ τ : ℂ) ∧
      PiOddSer (coeff (Pihat τ c)) (xiτ τ) = PihatO τ c ∧
      Tser τ (coeff (Pihat τ c)) = That τ c ∧
      Dτ τ c - (ysq τ : ℂ) * That τ c = Qhat τ c := Proofs.sec4_hat_closed_proved τ h1 h2 c hc

/-- (sec4:diff), sec_04_near.tex:108-110: "As `Q_0` and `π₂` depend only on `c`, `Q_f(-τ + iy, -τ - iy) - Q̂ =
-y²(T - T̂)`." -/
theorem sec4_diff (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) - Qhat τ (cOf f τ) =
      -(ysq τ : ℂ) * (Tser τ (coeff (PiF f τ)) - That τ (cOf f τ)) := Proofs.sec4_diff_proved hDB f hf τ h1 h2

/-- sec_04_near.tex:153-156 (used in the proof of Proposition 4.1, sec_04_near.tex:337-341): "Split
`T - T̂ = Ṫ + (T - T̂ - Ṫ)` ...; then
`Re Q_f(-τ + iy, -τ - iy) ≥ Re Q̂ - y²|Ṫ| - y²|T - T̂ - Ṫ|`." -/
theorem sec4_majorant_split (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    (Qhat τ (cOf f τ)).re - ysq τ * ‖Tdot τ (cOf f τ) φ‖ -
        ysq τ * ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
      (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re := Proofs.sec4_majorant_split_proved hDB f hf τ h1 h2 φ hφ

/-- sec_04_near.tex:159: for `F ≪ Z`: `|F(ξ)| ≤ Z(|ξ|)` wherever `Z` converges; the relation is preserved by sums and
products; and `(1 - F)⁻¹ ≪ (1 - Z)⁻¹` if `F(0) = Z(0) = 0` (the inverses are the solutions of `g = 1 + F g`,
`G = 1 + Z G`). -/
theorem sec4_majorant_rules :
    (∀ (F : ℕ → ℂ) (Z : ℕ → ℝ) (ξ : ℂ), Majorizes F Z → Summable (fun n => Z n * ‖ξ‖ ^ n) →
      Summable (fun n => F n * ξ ^ n) ∧ ‖∑' n, F n * ξ ^ n‖ ≤ ∑' n, Z n * ‖ξ‖ ^ n) ∧
    (∀ (F G : ℕ → ℂ) (Z W : ℕ → ℝ), Majorizes F Z → Majorizes G W →
      Majorizes (fun n => F n + G n) (fun n => Z n + W n) ∧ Majorizes (cmul F G) (cmul Z W)) ∧
    (∀ (F g : ℕ → ℂ) (Z G : ℕ → ℝ), Majorizes F Z → F 0 = 0 → Z 0 = 0 →
      (∀ n, g n = (if n = 0 then 1 else 0) + cmul F g n) →
      (∀ n, G n = (if n = 0 then 1 else 0) + cmul Z G n) → Majorizes g G) := Proofs.sec4_majorant_rules_proved

/-- sec_04_near.tex:164-169: for a majorant `Z` with `Z₁ = Z₂ = 0`, in terms of coefficients `𝔥[Z] = ∑_{j ≥ 1} Z_{2j+1}
x^{2j}` and `𝔴[Z] = ∑_{j ≥ 1} [(2j + 10/3)Z_{2j+1} + (j+1)Z_{2j+2}] x^{2j-2}`; both increase with `x ≥ 0` (inside the
disc of convergence). -/
theorem sec4_hw_coeff (Z : ℕ → ℝ) (hZ : ∀ n, 0 ≤ Z n) (hZ1 : Z 1 = 0) (hZ2 : Z 2 = 0) (Zf : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r) (hsum : ∀ x : ℝ, |x| < r → HasSum (fun n => Z n * x ^ n) (Zf x)) :
    (∀ x : ℝ, 0 < x → x < r → frakHat Zf x = hCoef Z x ∧ frakWat Zf x = wCoef Z x) ∧
      MonotoneOn (hCoef Z) (Set.Ico 0 r) ∧ MonotoneOn (wCoef Z) (Set.Ico 0 r) := Proofs.sec4_hw_coeff_proved Z hZ hZ1 hZ2 Zf r hr hsum

/-- sec_04_near.tex:169: "The weights `2j + 10/3` and `j + 1` bound the factors `2j + 2τπ₂` and `2τ(j + 1)` in the
coefficients of `Υ` ..., because `2τ ≤ 1` and `|π₂| ≤ 10/3`", with `π₂ = (2c - τ)/Ψ` (sec_04_near.tex:83). -/
theorem sec4_weight_bounds (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖(2 * c - (τ : ℂ)) / (vτ τ : ℂ)‖ ≤ 10 / 3 ∧
      ∀ j : ℕ, ‖2 * (j : ℂ) + 2 * (τ : ℂ) * ((2 * c - (τ : ℂ)) / (vτ τ : ℂ))‖ ≤ 2 * j + 10 / 3 ∧
        ‖2 * (τ : ℂ) * ((j : ℂ) + 1)‖ ≤ (j : ℝ) + 1 :=
  Proofs.sec4_weight_bounds_proved τ h1 h2 c hc

/-- Lemma 4.4(i) (sec_04_near.tex:174): if `ΔΠ = ∑_{n ≥ 3} Δπ_n ξⁿ ≪ Z` and `ΔΠ_o`, `ΔΥ` are formed from the `Δπ_n` by the
linear rules of Lemma 4.2 with `π₂ = (2c - τ)/Ψ` kept fixed, then `|ΔΠ_o(iy)| ≤ 𝔥[Z](y)` and `|ΔΥ(iy)| ≤ 𝔴[Z](y)`
(`Z` converging at `y`, with the derivative-type weights). -/
theorem lem_4_4_i (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2) (y : ℝ) (hy : 0 < y) (hy0 : y ≤ y0) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (dp : ℕ → ℂ) (Z : ℕ → ℝ) (hdp : ∀ n, n ≤ 2 → dp n = 0) (hmaj : Majorizes dp Z)
    (hZs : Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * y ^ n)) :
    ‖PiOddSer dp (I * (y : ℂ))‖ ≤ hCoef Z y ∧
      ‖UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) dp (I * (y : ℂ))‖ ≤ wCoef Z y := Proofs.lem_4_4_i_proved τ h1 h2 y hy hy0 c hc dp Z hdp hmaj hZs

/-- Lemma 4.4(ii) (sec_04_near.tex:175): for every `f ∈ 𝒮`, `|Π_o(iy) - 1| ≤ ς(y)`. -/
theorem lem_4_4_ii (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2)
    (y : ℝ) (hy : 0 < y) (hy0 : y ≤ y0) :
    ‖PiOddSer (coeff (PiF f τ)) (I * (y : ℂ)) - 1‖ ≤ epsOf y := Proofs.lem_4_4_ii_proved hDB f hf τ h1 h2 y hy hy0

/-- Lemma 4.4(iii) (sec_04_near.tex:176-179): `B ≪ √η B₁` and `B² ≪ η B₂` (coefficients in `ξ`). -/
theorem lem_4_4_iii (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ ≤ 1 / 2)
    (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    Majorizes (coeff (Bser τ φ)) (fun n => Real.sqrt (etadef (cOf f τ)) * (coeff B1c n).re) ∧
      Majorizes (coeff (fun ξ => Bser τ φ ξ ^ 2)) (fun n => etadef (cOf f τ) * (coeff B2c n).re) := Proofs.lem_4_4_iii_proved hArea f hf τ h1 h2 φ hφ

/-- sec_04_near.tex:212-216 (the first variation): with `B` replaced by `λB`, `Π̇ = -2NB/(1 - νξ)³ = ∑_{j ≥ 2} b_{2j-1}
Π_j` and `Ṫ = ∑_{j ≥ 2} b_{2j-1} T_j` (the derivative at `λ = 0` of `T` computed from `N/(1 - νξ + λB)²`); at `λ = 1`
this is `Π`, at `λ = 0` the comparison function `Π̂`. Typed with complex `λ` (`T` is holomorphic in `λ`): stronger
than the printed real `0 ≤ λ ≤ 1`, and true. -/
theorem sec4_first_variation (hDB : FactDeBranges) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ < 1 / 2) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) :
    (∀ ξ ∈ ball (0 : ℂ) (1 / 4), PiLam τ (cOf f τ) φ 1 ξ = PiF f τ ξ ∧ PiLam τ (cOf f τ) φ 0 ξ = Pihat τ (cOf f τ) ξ ∧
      HasDerivAt (fun lam : ℂ => PiLam τ (cOf f τ) φ lam ξ)
        (-2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ (cOf f τ) * ξ) ^ 3) 0 ∧
      -2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ (cOf f τ) * ξ) ^ 3 =
        ∑' j : ℕ, if 2 ≤ j then coeff φ j * PiJ τ (cOf f τ) j ξ else 0) ∧
      HasDerivAt (fun lam : ℂ => Tser τ (coeff (PiLam τ (cOf f τ) φ lam))) (Tdot τ (cOf f τ) φ) 0 := Proofs.sec4_first_variation_proved hDB f hf τ h1 h2 φ hφ

/-- sec_04_near.tex:216: "where `T_j = (Υ_j - T̂ Π_{j,o})/Π̂_o`, with `Υ_j` and `Π_{j,o}` formed from `Π_j` by the linear
rules of Lemma 4.2 (`π₂` kept fixed)", and
differentiating the first formula of Lemma 4.2's proof "gives the closed form used in Lemma 4.5" (`Υ_j`, `Π_{j,o}` by the
linear rules with `π₂` fixed). -/
theorem sec4_Tj_closed (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (c : ℂ) (hc : ‖c‖ ≤ 1) (j : ℕ) (hj : 2 ≤ j) :
    (UpsLin τ ((2 * c - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiJ τ c j)) (xiτ τ) -
        That τ c * PiOddSer (coeff (PiJ τ c j)) (xiτ τ)) / PihatO τ c = TJ τ c j := Proofs.sec4_Tj_closed_proved τ h1 h2 c hc j hj

/-- Lemma 4.4(i), its last sentence (sec_04_near.tex:174) and its proof (:190): two functions of the form (sec4:Pi)
with the same `τ` and `c` have the same `π₀ = 0`, `π₁ = 1` and `π₂`, so their difference starts at `ξ³`; so does each
derivative `Π_j` with respect to `b_{2j-1}`. -/
theorem sec4_low_coeffs (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) :
    (∀ n : ℕ, n ≤ 2 → coeff (PiF f τ) n = coeff (Pihat τ (cOf f τ)) n) ∧
      ∀ c : ℂ, ∀ j : ℕ, 2 ≤ j → ∀ n : ℕ, n ≤ 2 → coeff (PiJ τ c j) n = 0 := Proofs.sec4_low_coeffs_proved f hf τ h1 h2

/-- sec_04_near.tex:159 and :267: the denominators of the majorants, `1 - ⅔x`, `1 - 2x`, `1 - ν⁺x` (`ν⁺ ≤ 2`) and
`𝒴 = 1 - ν⁺x - √η⁺ B₁` (`η⁺ ≤ 1`), stay positive for `|x| ≤ 1/4`, with `𝒴(1/4) ≥ 1/2 - 2/15`; `1 - 𝒴 = ν⁺x + √η⁺B₁` has
nonnegative coefficients (those of `B₁`), "so they converge for `|x| ≤ 1/4`". -/
theorem sec4_majorant_conv (νp ηp : ℝ) (hν0 : 0 ≤ νp) (hν : νp ≤ 2) (hη0 : 0 ≤ ηp) (hη : ηp ≤ 1) :
    1 / 2 - 2 / 15 ≤ fdOf νp ηp (1 / 4) ∧ (∀ n : ℕ, (coeff B1c n).im = 0 ∧ 0 ≤ (coeff B1c n).re) ∧
      ∀ x : ℝ, |x| ≤ 1 / 4 → 0 < 1 - 2 / 3 * x ∧ 0 < 1 - 2 * x ∧ 0 < faOf νp x ∧ 0 < fdOf νp ηp x := Proofs.sec4_majorant_conv_proved νp ηp hν0 hν hη0 hη

/-- Lemma 4.5(ii) (sec_04_near.tex:229-233; `𝔥`, `𝔴` as at sec_04_near.tex:159-163): if moreover `0 < y ≤ y₀` and
`|ν| ≤ ν⁺ ≤ 2` (as printed),
then `(∑_{j ≥ 6} |T_j|²/(2j - 1))^{1/2} ≤ N₆`. -/
theorem lem_4_5_ii (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) (hy0 : yτ τ ≤ y0) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (νp : ℝ) (hν : ‖nuτ τ c‖ ≤ νp) (hνp : νp ≤ 2) :
    Summable (fun j : ℕ => if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) ∧
      Real.sqrt (∑' j : ℕ, if 6 ≤ j then ‖TJ τ c j‖ ^ 2 / (2 * (j : ℝ) - 1) else 0) ≤ N6Of νp := Proofs.lem_4_5_ii_proved τ h1 h2 hy0 c hc νp hν hνp

/-- Lemma 4.5(iii) (sec_04_near.tex:234): under the hypotheses of (ii), `|Ṫ| ≤ √η √(M + 130e)`, `M = 20 + N₆²`. -/
theorem lem_4_5_iii (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2)
    (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ) (νp : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp)
    (hνp : νp ≤ 2) :
    ‖Tdot τ (cOf f τ) φ‖ ≤
      Real.sqrt (etadef (cOf f τ)) * Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)) := Proofs.lem_4_5_iii_proved_from lem_4_5_i lem_4_5_ii hArea f hf τ h1 h2 hy0 φ hφ νp hν hνp

/-- Lemma 4.6 (sec_04_near.tex:253-263): if `|ν| ≤ ν⁺ ≤ 2`, `η ≤ η⁺ ≤ 1` and `(M + 130e)^{1/2} ≤ n⁺`, then
`|Π_o(iy)| ≥ Π₋`, and if `Π₋ > 0`, `|T - T̂ - Ṫ| ≤ ηΛ`. -/
theorem lem_4_6 (hDB : FactDeBranges) (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) (hy : 0 < yτ τ) (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ)
    (νp ηp np : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp) (hνp : νp ≤ 2) (hη : etadef (cOf f τ) ≤ ηp) (hηp : ηp ≤ 1)
    (hn : Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)) ≤ np) :
    PiLowOf νp ηp ≤ ‖PiOddSer (coeff (PiF f τ)) (xiτ τ)‖ ∧
      (0 < PiLowOf νp ηp →
        ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤ etadef (cOf f τ) * LamOf νp ηp np) := Proofs.lem_4_6_proved_from lem_4_4_ii lem_4_4_iii lem_4_5_iii hDB hArea f hf τ h1 h2 hy hy0 φ hφ νp ηp np hν hνp hη hηp hn

/-- A step of the proof of Proposition 4.1 (sec_04_near.tex:342): `Λ ≥ 0` on every cell, so `ρ e Λ ≤ ρ₊ e Λ`. The
paper names it there: "`Λ ≥ 0` (the series in `Λ` have nonnegative coefficients, `T⁺, n⁺ ≥ 0` and `Π₋ > 0`)"; the
majorants have nonnegative coefficients by sec_04_near.tex:159. SUPPORT row (the paper's own step). -/
theorem sec4_Lam_nonneg : ∀ i : ℕ, i ≤ 255 → 0 ≤ Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) := Proofs.sec4_Lam_nonneg_proved

/-- The proof of Proposition 4.1 (sec_04_near.tex:336-346), as an implication: from the case `e = 0` (`Q_f = Q_k`) and
the per-cell bound `Re Q_f ≥ (16/27)y² + e m(ρ) - y²√(ρe(M + 130e)) - y²ρeΛ` (its first display, with the cell's
numbers), Lemma 4.8 gives (sec4:goal), hence Proposition 4.1. The proof uses `|c| ≤ 1` (de Branges for `n = 2`,
sec_04_near.tex:57) to place `ρ` in a cell and `e ≤ e⁺`, hence the binder `hDB`. -/
theorem prop_4_1_from_layer (hDB : FactDeBranges) (h48 : Check_4_8)
    (hzero : ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → edef (cOf f τ) = 0 →
      Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ) = (Qk τ : ℂ))
    (hcell : ∀ f : ℂ → ℂ, InS f → ∀ τ : ℝ, 9 / 20 ≤ τ → τ < 1 / 2 → yτ τ ≤ y0 → 0 < edef (cOf f τ) →
      ∀ i : ℕ, i ≤ 255 → (i : ℝ) / 256 ≤ etadef (cOf f τ) / edef (cOf f τ) →
        etadef (cOf f τ) / edef (cOf f τ) ≤ ((i : ℝ) + 1) / 256 →
        16 / 27 * ysq τ + edef (cOf f τ) * mρ (etadef (cOf f τ) / edef (cOf f τ)) -
            ysq τ * Real.sqrt (etadef (cOf f τ) * (Mcap ((i : ℝ) / 256) + 130 * edef (cOf f τ))) -
            ysq τ * etadef (cOf f τ) * Lam ((i : ℝ) / 256) (((i : ℝ) + 1) / 256) ≤
          (Q f (-(τ : ℂ) + xiτ τ) (-(τ : ℂ) - xiτ τ)).re) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re := Proofs.prop_4_1_from_layer_proved_from sec4_Lam_nonneg hDB h48 hzero hcell

/-! ## Section 5 (the quotient through the odd Grunsky block): the finite-dimensional rows -/

/-- sec_05_grunsky_q.tex:8-10: `s = 2^{-1/2} e^{iθ/4}`, `t = s̄`, "so that `s² = z` and `t² = w`". -/
theorem sec5_s_sq (θ : ℝ) : sθ θ ^ 2 = zθ θ ∧ conj (sθ θ) ^ 2 = conj (zθ θ) := Proofs.sec5_s_sq_proved θ

/-- sec_05_grunsky_q.tex:13-19, the coordinates: for `θ ∈ (0, π]`, `l₁₁ > 0`, `l₂₂ > 0` (`u`, `v` are linearly
independent), and `ũ, ṽ` have the Gram matrix of `u, v`: `l₁₁² = (A_o + Re Z_o)/2`, `l₁₁ l₂₁ = Im Z_o / 2`,
`l₂₁² + l₂₂² = (A_o - Re Z_o)/2`. -/
theorem sec5_coords (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    0 < l11 θ ∧ 0 < l22 θ ∧ l11 θ ^ 2 = (Ao + (Zo θ).re) / 2 ∧ l11 θ * l21 θ = (Zo θ).im / 2 ∧
      l21 θ ^ 2 + l22 θ ^ 2 = (Ao - (Zo θ).re) / 2 := Proofs.sec5_coords_proved θ h0 hπ

/-- sec_05_grunsky_q.tex:33: "Since `tan(θ/4) > 0`, `χ` never vanishes, and `Q_rel` is an entire function of the
three entries of `M`" (for `θ ∈ (0, π]`). -/
theorem sec5_chi_qrel_entire (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ, chi θ M ≠ 0) ∧ Differentiable ℂ (fun p : ℂ × ℂ × ℂ => Qrel θ (symMat p)) := Proofs.sec5_chi_qrel_entire_proved θ h0 hπ

/-- sec_05_grunsky_q.tex:40: "`(s - t)/(s + t) = i tan(θ/4)`" (for `θ ∈ (0, π]`). -/
theorem sec5_tan_identity (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (sθ θ - conj (sθ θ)) / (sθ θ + conj (sθ θ)) = I * (Real.tan (θ / 4) : ℂ) := Proofs.sec5_tan_identity_proved θ h0 hπ

/-- sec_05_grunsky_q.tex:44-46, the algebra of the proof of Proposition 5.1: with `ϱ = (1 + χ)/(1 - χ)` and
`f(z)/f(w) = ϱ²`, `1 + (p f(z) - q f(w))/(f(z) - f(w)) = 1 + (p ϱ² - q)/(ϱ² - 1)
= 1 + (p(1 + χ)² - q(1 - χ)²)/(4χ) = 1 + (p + q)/2 + (p - q)(χ + χ⁻¹)/4`. -/
theorem sec5_qrel_algebra (p q χ fz fw : ℂ) (hχ0 : χ ≠ 0) (hχ1 : χ ≠ 1) (hfw : fw ≠ 0) (hne : fz ≠ fw)
    (hratio : fz / fw = ((1 + χ) / (1 - χ)) ^ 2) :
    1 + (p * fz - q * fw) / (fz - fw) = 1 + (p * ((1 + χ) / (1 - χ)) ^ 2 - q) / (((1 + χ) / (1 - χ)) ^ 2 - 1) ∧
      1 + (p * ((1 + χ) / (1 - χ)) ^ 2 - q) / (((1 + χ) / (1 - χ)) ^ 2 - 1) =
        1 + (p * (1 + χ) ^ 2 - q * (1 - χ) ^ 2) / (4 * χ) ∧
      1 + (p * (1 + χ) ^ 2 - q * (1 - χ) ^ 2) / (4 * χ) = 1 + (p + q) / 2 + (p - q) * (χ + χ⁻¹) / 4 := Proofs.sec5_qrel_algebra_proved p q χ fz fw hχ0 hχ1 hfw hne hratio

/-- The Takagi factorization of a complex symmetric 2x2 matrix [Tak25], [HJ13, Corollary 4.4.4], as the proof of
Proposition 5.2 uses it (sec_05_grunsky_q.tex:64): `M = 𝒰 diag(σ₁, σ₂) 𝒰ᵀ` with `𝒰` unitary and
`0 ≤ σⱼ ≤ ‖M‖`. -/
theorem sec5_takagi_2x2 (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Mᵀ = M) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℂ, W * Wᴴ = 1 ∧ ∃ σ₁ σ₂ : ℝ, 0 ≤ σ₁ ∧ 0 ≤ σ₂ ∧ σ₁ ≤ opNorm M ∧
      σ₂ ≤ opNorm M ∧ M = W * Matrix.diagonal ![(σ₁ : ℂ), (σ₂ : ℂ)] * Wᵀ := Proofs.sec5_takagi_2x2_proved M hM

/-- Proposition 5.2 (sec_05_grunsky_q.tex:59-61): let `Φ` be holomorphic on a neighbourhood of `𝓑` in the space `ℂ³`
of complex symmetric 2x2 matrices. Then the minimum of `Re Φ` over `𝓑` is attained at a symmetric unitary
matrix. -/
theorem prop_5_2 (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (hΦ : HolomorphicNearBall Φ) :
    ∃ M₀ : Matrix (Fin 2) (Fin 2) ℂ, InBall M₀ ∧ IsSymmUnitary M₀ ∧
      ∀ M : Matrix (Fin 2) (Fin 2) ℂ, InBall M → (Φ M₀).re ≤ (Φ M).re := Proofs.prop_5_2_proved Φ hΦ

/-- Lemma 5.3 (sec_05_grunsky_q.tex:67-73): every symmetric unitary 2x2 matrix is `M(α, ψ, ω)` with `α ∈ [0, π/2]`
and `ψ, ω ∈ [-π, π]`; moreover `\overline{M(α, ψ, ω)} = M(α, π - ψ, π - ω)`. (Each `M(α, ψ, ω)` is symmetric and
unitary: sec_05_grunsky_q.tex:76.) -/
theorem lem_5_3 :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ, IsSymmUnitary M → ∃ α ψ ω : ℝ, 0 ≤ α ∧ α ≤ Real.pi / 2 ∧
      -Real.pi ≤ ψ ∧ ψ ≤ Real.pi ∧ -Real.pi ≤ ω ∧ ω ≤ Real.pi ∧ M = chart α ψ ω) ∧
      (∀ α ψ ω : ℝ, IsSymmUnitary (chart α ψ ω)) ∧
      ∀ α ψ ω : ℝ, mconj (chart α ψ ω) = chart α (Real.pi - ψ) (Real.pi - ω) := Proofs.lem_5_3_proved

/-- Lemma 5.4 (sec_05_grunsky_q.tex:82-88), first part: if `Φ(M̄) = \overline{Φ(M)}` on `𝓑`, then the values of
`Re Φ` on all symmetric unitary matrices are its values on the half chart
`𝓗 = {M(α, ψ, ω) : 0 ≤ α ≤ π/2, -π/2 ≤ ψ ≤ π/2, -π ≤ ω ≤ π}`. -/
theorem lem_5_4 (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (hΦ : ∀ M, InBall M → Φ (mconj M) = conj (Φ M)) :
    {x : ℝ | ∃ M : Matrix (Fin 2) (Fin 2) ℂ, IsSymmUnitary M ∧ x = (Φ M).re} =
      {x : ℝ | ∃ α ψ ω : ℝ, InX α ψ ω ∧ x = (Φ (chart α ψ ω)).re} := Proofs.lem_5_4_proved Φ hΦ

/-- Lemma 5.4 (sec_05_grunsky_q.tex:87), second part: "The function `Q_rel` has this symmetry for every
`θ ∈ (0, π]`" (for every matrix `M`). -/
theorem lem_5_4_qrel (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Qrel θ (mconj M) = conj (Qrel θ M) := Proofs.lem_5_4_qrel_proved θ h0 hπ M

/-- Corollary 5.5 (sec_05_grunsky_q.tex:94-96): let `Φ` be holomorphic on a neighbourhood of `𝓑` with
`Φ(M̄) = \overline{Φ(M)}`. If `Re Φ(M(α, ψ, ω)) > 0` for all `(α, ψ, ω) ∈ [0, π/2] x [-π/2, π/2] x [-π, π]`, then
`Re Φ > 0` on `𝓑`. -/
theorem cor_5_5 (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (hhol : HolomorphicNearBall Φ)
    (hsym : ∀ M, InBall M → Φ (mconj M) = conj (Φ M)) (hpos : ∀ α ψ ω : ℝ, InX α ψ ω → 0 < (Φ (chart α ψ ω)).re) :
    ∀ M : Matrix (Fin 2) (Fin 2) ℂ, InBall M → 0 < (Φ M).re := Proofs.cor_5_5_proved Φ hhol hsym hpos

/-- Remark 5.6 (sec_05_grunsky_q.tex:102-103): at `θ = 60°` the real symmetric unitary matrix
`M = [[-cos α, -sin α], [-sin α, cos α]]` with `α = 0.535` gives `Re Q_rel(M) ≈ -0.078`
(here: `-0.0785 < Re Q_rel(M) < -0.0775`). -/
theorem rem_5_6 :
    IsSymmUnitary (!![-(Real.cos 0.535 : ℂ), -(Real.sin 0.535 : ℂ); -(Real.sin 0.535 : ℂ), (Real.cos 0.535 : ℂ)]) ∧
      -0.0785 < (Qrel (deg 60)
        (!![-(Real.cos 0.535 : ℂ), -(Real.sin 0.535 : ℂ); -(Real.sin 0.535 : ℂ), (Real.cos 0.535 : ℂ)])).re ∧
      (Qrel (deg 60)
        (!![-(Real.cos 0.535 : ℂ), -(Real.sin 0.535 : ℂ); -(Real.sin 0.535 : ℂ), (Real.cos 0.535 : ℂ)])).re < -0.0775 := Proofs.rem_5_6_proved

/-! ## Section 6 (far pairs): the finite-dimensional rows -/

/-- sec_06_far.tex:11: for `θ ∈ [135°, 180°]`, `c = cos(θ/2)` satisfies `0 ≤ c ≤ sin(π/8) < 383/1000`. -/
theorem sec6_c_bound (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    0 ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ Real.sin (Real.pi / 8) ∧ Real.sin (Real.pi / 8) < 383 / 1000 := Proofs.sec6_c_bound_proved θ h1 h2

/-- sec_06_far.tex:11: "since `sin(π/8) = ½√(2 - √2) = 0.38268…`": the closed form, and `0.38268 < sin(π/8) < 0.38269`. -/
theorem sec6_sin_pi_8 :
    Real.sin (Real.pi / 8) = Real.sqrt (2 - Real.sqrt 2) / 2 ∧
      (38268 / 100000 : ℝ) < Real.sin (Real.pi / 8) ∧ Real.sin (Real.pi / 8) < 38269 / 100000 :=
  Proofs.sec6_sin_pi_8_proved

/-- sec_06_far.tex:11 and :97: "`277/400 - 173/250 = 1/2000`". -/
theorem sec6_margin_arith : (277 / 400 : ℝ) - 173 / 250 = 1 / 2000 := Proofs.sec6_margin_arith_proved

/-- sec_06_far.tex:16 and :34: "`L = 2A_o = log 3`" and "`L = log 3 < π/2`". -/
theorem sec6_L_log3 : 2 * Ao = Real.log 3 ∧ Llog3 = Real.log 3 ∧ Llog3 < Real.pi / 2 := Proofs.sec6_L_log3_proved

/-- sec_06_far.tex:48: "`u_o = Re Z_o` and `v_o = Im Z_o`" with `c = cos(θ/2)` (for `θ ∈ [0, π]`). -/
theorem sec6_ZO_re_im (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (Zo θ).re = uo (Real.cos (θ / 2)) ∧ (Zo θ).im = vo (Real.cos (θ / 2)) := Proofs.sec6_ZO_re_im_proved θ h0 hπ

/-- sec_06_far.tex:26: "The rows of `O'` have norm at most `1`, so `|O'₁₁|, |O'₂₂| ≤ √(1 - |O'₁₂|²)`; since
`2(σ₊ + σ₋) = L`, this gives `|ξ₁|² + |ξ₂|² ≤ 1`", with `ξ₁ = 2(σ₊O'₁₁ - σ₋O'₂₂)/L` and `ξ₂ = O'₁₂` (sec_06_far.tex:24;
`σ₊ + σ₋ = A_o`, `L = 2A_o`; Lean's matrix `N` is `O'`). Stronger than printed: for all `σ₊, σ₋ ≥ 0` with
`σ₊ + σ₋ > 0` and every `O' ∈ 𝓑`, not only the numbers and the compression of the pair. -/
theorem sec6_xi_ball (σp σm : ℝ) (hp : 0 ≤ σp) (hm : 0 ≤ σm) (hpos : 0 < σp + σm)
    (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : InBall N) :
    ‖2 * ((σp : ℂ) * N 0 0 - (σm : ℂ) * N 1 1) / (2 * ((σp + σm : ℝ) : ℂ))‖ ^ 2 + ‖N 0 1‖ ^ 2 ≤ 1 := Proofs.sec6_xi_ball_proved σp σm hp hm hpos N hN

/-- sec_06_far.tex:24-28: from `log p = e^{iφ}(Lξ₁ + idξ₂)` and `log q = e^{-iφ}(Lξ₁ - idξ₂)`,
`(p + q)/2 = e^{U*} cos V*` with `U* = L cos φ ξ₁ - d sin φ ξ₂` and `V* = L sin φ ξ₁ + d cos φ ξ₂` (Lean's `X, Y` are
`Lξ₁, dξ₂`). Stronger than printed: an identity for every real `φ` and all complex `X, Y`, not only `φ = arg Z_o`,
`X = Lξ₁` and `Y = dξ₂`. -/
theorem sec6_psum_cos (φ : ℝ) (X Y : ℂ) :
    (exp (exp ((φ : ℂ) * I) * (X + I * Y)) + exp (exp (-((φ : ℂ) * I)) * (X - I * Y))) / 2 =
      exp ((Real.cos φ : ℂ) * X - (Real.sin φ : ℂ) * Y) * Complex.cos ((Real.sin φ : ℂ) * X + (Real.cos φ : ℂ) * Y) := Proofs.sec6_psum_cos_proved φ X Y

/-- sec_06_far.tex:30-32: "The real orthogonal change of the complex variables `(ξ₁, ξ₂)` to
`ζ₁ = (L sin φ ξ₁ + d cos φ ξ₂)/b₁` and `ζ₂ = (d cos φ ξ₁ - L sin φ ξ₂)/b₁`, still with `|ζ₁|² + |ζ₂|² ≤ 1`, gives
`V* = b₁ζ₁` and `U* = b₂ζ₁ + b₃ζ₂`", with `b₁² = L² sin²φ + d² cos²φ`, `b₂ = (L² - d²) sin φ cos φ / b₁`,
`b₃ = Ld/b₁` (for `L, d > 0`). Stronger than printed: for all `L, d > 0`, real `φ` and all `ξ₁, ξ₂ ∈ ℂ`, with
`|ζ₁|² + |ζ₂|² = |ξ₁|² + |ξ₂|²` (not only `≤ 1`); this equality for all `ξ₁, ξ₂` says the change is real orthogonal. -/
theorem sec6_b_change (L d φ : ℝ) (hL : 0 < L) (hd : 0 < d) (ξ₁ ξ₂ : ℂ) :
    let b₁ : ℝ := Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2)
    let ζ₁ : ℂ := ((L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂) / b₁
    let ζ₂ : ℂ := ((d * Real.cos φ : ℂ) * ξ₁ - (L * Real.sin φ : ℂ) * ξ₂) / b₁
    ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 = ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 ∧
      (L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂ = (b₁ : ℂ) * ζ₁ ∧
      (L * Real.cos φ : ℂ) * ξ₁ - (d * Real.sin φ : ℂ) * ξ₂ =
        (((L ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / b₁ : ℝ) : ℂ) * ζ₁ + ((L * d / b₁ : ℝ) : ℂ) * ζ₂ :=
  Proofs.sec6_b_change_proved L d φ hL hd ξ₁ ξ₂

/-- sec_06_far.tex:16, :32-34 and :48: for `θ ∈ [135°, 180°]`, with `φ = arg Z_o`, `σ± = (A_o ± |Z_o|)/2`,
`d = 4√(σ₊σ₋)` and `L = log 3`, the numbers `b₁, b₂, b₃` of the orthogonal change are those of Lemma 6.2 at
`c = cos(θ/2)` ("since `d² = L² - 4|Z_o|²` and `|Z_o| cos φ = u_o`, `|Z_o| sin φ = v_o`"); they are nonnegative,
`b₁ > 0`, and `b₁ ≤ L = log 3 < π/2`. -/
theorem sec6_b_values (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    let φ := Complex.arg (Zo θ)
    let d := 4 * Real.sqrt ((Ao + ‖Zo θ‖) / 2 * ((Ao - ‖Zo θ‖) / 2))
    let c := Real.cos (θ / 2)
    0 < b1 c ∧ Real.sqrt (Llog3 ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2) = b1 c ∧
      (Llog3 ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / b1 c = b2 c ∧ Llog3 * d / b1 c = b3 c ∧
      0 ≤ b2 c ∧ 0 ≤ b3 c ∧ b1 c ≤ Llog3 ∧ Llog3 < Real.pi / 2 := Proofs.sec6_b_values_proved θ h1 h2

/-- sec_06_far.tex:34, after "`b₁ ≤ L = log 3 < π/2`": "Indeed, `d ≤ 2(σ₊ + σ₋) = L` (by the inequality between the
arithmetic and geometric means), which gives `b₁ ≤ L` and `L² - d² ≥ 0`; and `0 ≤ φ ≤ π/2` on our range of `θ` (the point
`z` lies in the closed first quadrant), so `b₂ ≥ 0`", for `θ ∈ [135°, 180°]`, with `z = z_θ`, `φ = arg Z_o`,
`σ± = (A_o ± |Z_o|)/2`, `d = 4√(σ₊σ₋)` and `L = log 3` as in `sec6_b_values` (which states `b₁ ≤ L` and `b₂ ≥ 0`). -/
theorem sec6_phi_d_range (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    let φ := Complex.arg (Zo θ)
    let σp := (Ao + ‖Zo θ‖) / 2
    let σm := (Ao - ‖Zo θ‖) / 2
    let d := 4 * Real.sqrt (σp * σm)
    0 ≤ (zθ θ).re ∧ 0 ≤ (zθ θ).im ∧ 0 ≤ φ ∧ φ ≤ Real.pi / 2 ∧
      d ≤ 2 * (σp + σm) ∧ 2 * (σp + σm) = Llog3 ∧ 0 ≤ Llog3 ^ 2 - d ^ 2 := Proofs.sec6_phi_d_range_proved θ h1 h2

/-- sec_06_far.tex:34: "The function `-log cos v` has a Taylor series with nonnegative coefficients ..., so
`|log cos v| ≤ -log cos |v|` for `|v| < π/2`" (principal logarithm; `cos v` is never real `≤ 0` there). -/
theorem sec6_logcos (v : ℂ) (hv : ‖v‖ < Real.pi / 2) :
    ‖log (Complex.cos v)‖ ≤ -Real.log (Real.cos ‖v‖) := Proofs.sec6_logcos_proved v hv

/-- sec_06_far.tex:34-36 (eq:Wbound), the finite-dimensional step: if `b₁, b₂, b₃ ≥ 0`, `b₁ < π/2` and
`|ζ₁|² + |ζ₂|² ≤ 1`, then `ℓ₊ = b₂ζ₁ + b₃ζ₂ + log cos(b₁ζ₁)` (`= U* + log cos V*`) satisfies
`|ℓ₊| ≤ b₂r₁ + b₃√(1 - r₁²) - log cos(b₁r₁)`, `r₁ = |ζ₁| ∈ [0, 1]`. Stronger than printed: for all `b₁, b₂, b₃ ≥ 0`
with `b₁ < π/2`, not only the numbers of our range of `θ`. -/
theorem sec6_Wbound_finite (b₁ b₂ b₃ : ℝ) (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃) (hb : b₁ < Real.pi / 2)
    (ζ₁ ζ₂ : ℂ) (hζ : ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 ≤ 1) :
    ‖ζ₁‖ ≤ 1 ∧
      ‖(b₂ : ℂ) * ζ₁ + (b₃ : ℂ) * ζ₂ + log (Complex.cos ((b₁ : ℂ) * ζ₁))‖ ≤
        b₂ * ‖ζ₁‖ + b₃ * Real.sqrt (1 - ‖ζ₁‖ ^ 2) - Real.log (Real.cos (b₁ * ‖ζ₁‖)) := Proofs.sec6_Wbound_finite_proved b₁ b₂ b₃ h1 h2 h3 hb ζ₁ ζ₂ hζ

/-- sec_06_far.tex:51-53 (eq:psum), the real-analysis step: on the disc `|ℓ₊| ≤ ϖ = 211/200`, `Re e^{ℓ₊} > 277/800`
(via `ϖ sin(57/100) < 57/100`, `cos(57/100) > 21/25`, `e^{21ϖ/25} < 672/277`, `e^ϖ < 800/277`; the proof's step
"Since `g` is even, it suffices to take `0 ≤ γ ≤ π`", sec_06_far.tex:51, with `g(γ) = e^{-ϖ cos γ} cos(ϖ sin γ)`). -/
theorem sec6_expW_bound (W : ℂ) (hW : ‖W‖ ≤ Tfar) : 277 / 800 < (exp W).re := Proofs.sec6_expW_bound_proved W hW

/-- sec_06_far.tex:51, with `ϖ = 211/200` (sec_06_far.tex:44): "the root `γ_* ∈ (0, π)` of `γ = ϖ sin γ` (there
is only one, since `γ - ϖ sin γ` is strictly convex on `[0, π]` and vanishes at `0`)". -/
theorem sec6_gamma_unique :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) Real.pi) (fun γ : ℝ => γ - Tfar * Real.sin γ) ∧
    (0 : ℝ) - Tfar * Real.sin 0 = 0 ∧
    ∃! γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) Real.pi ∧ γ = Tfar * Real.sin γ := Proofs.sec6_gamma_unique_proved

/-- sec_06_far.tex:74-82 with Lemma 6.4's parametrization (sec_06_far.tex:85-87): for `θ ∈ [135°, 180°]`,
`c = c_θ = cos(θ/2)`, `ε = π - θ` and `z = z_θ`: `e^{-iε} = 1 - 2c² - 2ic√(1 - c²)`
("`cos ε = 1 - 2c_θ²` and `sin ε = 2c_θ√(1 - c_θ²)`"), `z² = -¼e^{-iε}` (Lean's `xfar` is `¼`), and
`A_R = Re(e^{iε} z²/(1 - z²)²)`,
`B_R = Re(-e^{iε} log(1 - z²))`. -/
theorem sec6_A0B0_closed (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    emeps (Real.cos (θ / 2)) = exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) ∧
      zθ θ ^ 2 = -(xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) ∧
      A0 (Real.cos (θ / 2)) = (exp (((Real.pi - θ : ℝ) : ℂ) * I) * (zθ θ ^ 2 / (1 - zθ θ ^ 2) ^ 2)).re ∧
      B0 (Real.cos (θ / 2)) = (exp (((Real.pi - θ : ℝ) : ℂ) * I) * (-log (1 - zθ θ ^ 2))).re := Proofs.sec6_A0B0_closed_proved θ h1 h2

/-- sec_06_far.tex:80 and :87: "`A_R = Re(-4/(4 + e^{-iε})²)`", for every `c` (Lean's `A0` is
`Re(-x/(1 + x e^{-iε})²)` with `x = ¼`; `emeps c` is `e^{-iε}`). -/
theorem sec6_A0_printed (c : ℝ) : A0 c = (-4 / (4 + emeps c) ^ 2).re := Proofs.sec6_A0_printed_proved c

/-- sec_06_far.tex:100: "At `c_θ = 0` (`θ = 180°`) the left side in Lemma 6.4 is about `0.6912`, close to the bound
`173/250 = 0.692`": its value there is in `(0.69115, 0.69125)`. -/
theorem sec6_value_180 : 0.69115 < Rbound 0 ∧ Rbound 0 < 0.69125 := Proofs.sec6_value_180_proved

/-- sec_06_far.tex:93: each cell's upper bound is "below `173/250`", and "The largest of these upper bounds is
`3459999249/(5·10⁹) = 0.69199984…`, below `173/250 = 0.692`": `3459999249/(5·10⁹)` is below `173/250` (that it is
the largest bound is the program's, NOT COUNTED),
`0.69199984 < 3459999249/(5·10⁹) < 0.69199985` (the printed digits) and `173/250 = 0.692`. -/
theorem sec6_cover_bound_arith :
    (3459999249 : ℝ) / (5 * 10 ^ 9) < 173 / 250 ∧
      (0.69199984 : ℝ) < 3459999249 / (5 * 10 ^ 9) ∧ (3459999249 : ℝ) / (5 * 10 ^ 9) < 0.69199985 ∧
      (173 / 250 : ℝ) = 0.692 := Proofs.sec6_cover_bound_arith_proved

/-! ## Section 7 (middle angles): the finite-dimensional rows -/

/-- Lemma 7.2 (sec_07_middle.tex:23-25): for `θ ∈ (0, π]`, the functions `Δ`, `U` and `R` are holomorphic on the
neighbourhood `{‖M‖ < π/log 9}` of `𝓑` (an open set of `ℂ³` containing `𝓑`), and `iU(M̄) = \overline{iU(M)}`,
`R(M̄) = \overline{R(M)}` there (the proof uses that "`m_uu`, `m_vv` and `m_uv` are conjugated when `M` is",
sec_07_middle.tex:28). -/
theorem lem_7_2 (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    1 < Real.pi / Real.log 9 ∧ IsOpen {p : ℂ × ℂ × ℂ | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      DifferentiableOn ℂ (fun p => Delta θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      DifferentiableOn ℂ (fun p => Ufun θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      DifferentiableOn ℂ (fun p => Rfun θ (symMat p)) {p | opNorm (symMat p) < Real.pi / Real.log 9} ∧
      ∀ M : Matrix (Fin 2) (Fin 2) ℂ, Mᵀ = M → opNorm M < Real.pi / Real.log 9 →
        I * Ufun θ (mconj M) = conj (I * Ufun θ M) ∧ Rfun θ (mconj M) = conj (Rfun θ M) := Proofs.lem_7_2_proved θ h0 hπ

/-- The finite-dimensional core of Lemma 7.4 (sec_07_middle.tex:81-86): if `E` is a complex `N x N` matrix with
`|yᵀ E x| ≤ ‖x‖ ‖y‖` for all real `x, y`, `𝒲` is a real `N x 4` matrix, `J = λJ₁ + μJ₂` and `P` is real symmetric
positive definite, then `|tr(E 𝒲 J 𝒲ᵀ)| ≤ tr(𝒲ᵀ𝒲 K)` with `K = ½(P + J P⁻¹ J)`. Stronger than printed: for every
size `N`, every such `E`, every real `𝒲` and all real `λ, μ`, not only the even block, the columns `u_e, v_e, β₀, β₁`
and the fixed `λ = 4/5`, `μ = ½`. -/
theorem sec7_trace_bound (N : ℕ) (E : Matrix (Fin N) (Fin N) ℂ)
    (hE : ∀ x y : Fin N → ℝ, ‖(fun i => (y i : ℂ)) ⬝ᵥ (E *ᵥ (fun i => (x i : ℂ)))‖ ≤
      Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (W : Matrix (Fin N) (Fin 4) ℝ) (lam mu : ℝ) (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : P.PosDef) :
    ‖Matrix.trace (E * (W * Jmat lam mu * Wᵀ).map (↑))‖ ≤ Matrix.trace (Wᵀ * W * Kmat lam mu P) := Proofs.sec7_trace_bound_proved N E hE W lam mu P hP

/-- sec_07_middle.tex:93-97: the leading principal minors of `P` are `8473/5000`, `499588663/10⁸`,
`1317395036843/10¹²` and `125044355055249/(2·10¹⁵)`, all positive, so `P` is positive definite. -/
theorem sec7_P_minors :
    (Pmat.submatrix (Fin.castLE (by norm_num : 1 ≤ 4)) (Fin.castLE (by norm_num : 1 ≤ 4))).det = 8473 / 5000 ∧
      (Pmat.submatrix (Fin.castLE (by norm_num : 2 ≤ 4)) (Fin.castLE (by norm_num : 2 ≤ 4))).det =
        499588663 / 10 ^ 8 ∧
      (Pmat.submatrix (Fin.castLE (by norm_num : 3 ≤ 4)) (Fin.castLE (by norm_num : 3 ≤ 4))).det =
        1317395036843 / 10 ^ 12 ∧
      Pmat.det = 125044355055249 / (2 * 10 ^ 15) ∧ Pmat.PosDef := Proofs.sec7_P_minors_proved

/-- sec_07_middle.tex:97: "The matrix `K` is then an explicit rational matrix, and `C_P(θ)` is the following linear combination
with rational coefficients of the nine numbers `A_e, Re Z_e, Im Z_e, L_e, Re L_z, Im L_z, M_e, Re M_z, Im M_z`". -/
theorem sec7_CP_linear :
    (∃ Kq : Matrix (Fin 4) (Fin 4) ℚ, Kmat (4 / 5) (1 / 2) Pmat = Kq.map (↑)) ∧
      ∃ q : Fin 9 → ℚ, ∀ θ : ℝ, CP θ (4 / 5) (1 / 2) Pmat =
        q 0 * Ae + q 1 * (Ze θ).re + q 2 * (Ze θ).im + q 3 * Le + q 4 * (Lz θ).re + q 5 * (Lz θ).im +
          q 6 * Me + q 7 * (Mz θ).re + q 8 * (Mz θ).im := Proofs.sec7_CP_linear_proved

/-- sec_07_middle.tex:97: "`C_P(θ)` is the following linear combination with rational coefficients of the nine numbers
`A_e, Re Z_e, Im Z_e, L_e, Re L_z, Im L_z, M_e, Re M_z, Im M_z`": the nine printed rationals (`λ = 4/5`, `μ = ½`, the
printed `P`). -/
theorem sec7_CP_explicit (θ : ℝ) :
    CP θ (4 / 5) (1 / 2) Pmat =
      130963453301025393 / 55575268913444000 * Ae - 183920349380321459 / 277876344567220000 * (Ze θ).re +
        95947301639073811 / 277876344567220000 * (Ze θ).im - 917139083085913 / 8336290337016600 * Le -
        6145773526217781 / 69469086141805000 * (Lz θ).re + 282896396731486619 / 833629033701660000 * (Lz θ).im +
        225798938136139847 / 1250443550552490000 * Me + 3679103289741521 / 39696620652460000 * (Mz θ).re -
        10747725795500707 / 312610887638122500 * (Mz θ).im := Proofs.sec7_CP_explicit_proved θ

/-- Proposition 7.5(i) (sec_07_middle.tex:108): for `θ ∈ (0, π]`, `F` is holomorphic on a neighbourhood of `𝓑`, and
`F(M̄) = \overline{F(M)}` on `𝓑`. -/
theorem prop_7_5_i (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    HolomorphicNearBall (Ffun θ) ∧ ∀ M, InBall M → Ffun θ (mconj M) = conj (Ffun θ M) := Proofs.prop_7_5_i_proved θ h0 hπ

/-- Lemma 7.6(i) (sec_07_middle.tex:128): `Φ_F > 0` on `[50.3°, 90°] x 𝓧`. PROVED GIVEN the five band checks of
Table 3 rows 1-5 (the bands `[50.3, 55], [55, 60], [60, 70], [70, 80], [80, 90]` cover `[50.3, 90]`). -/
theorem lem_7_6_i (h1 : Check_7_6_band01) (h2 : Check_7_6_band02) (h3 : Check_7_6_band03) (h4 : Check_7_6_band04)
    (h5 : Check_7_6_band05) : ∀ θ : ℝ, 50.3 ≤ θ → θ ≤ 90 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω := Proofs.lem_7_6_i_proved h1 h2 h3 h4 h5

/-- Lemma 7.6(ii) (sec_07_middle.tex:129): `Φ_rel > 0` on `[90°, 135°] x 𝓧`. PROVED GIVEN the six band checks of
Table 3 rows 6-11 (the bands `[90, 95], ..., [125, 135]` cover `[90, 135]`). -/
theorem lem_7_6_ii (h6 : Check_7_6_band06) (h7 : Check_7_6_band07) (h8 : Check_7_6_band08)
    (h9 : Check_7_6_band09) (h10 : Check_7_6_band10) (h11 : Check_7_6_band11) :
    ∀ θ : ℝ, 90 ≤ θ → θ ≤ 135 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω := Proofs.lem_7_6_ii_proved h6 h7 h8 h9 h10 h11

/-- Table 3 (sec_07_middle.tex:147-159): the column total `311,506` (boxes checked). -/
theorem tab3_totals :
    36762 + 42121 + 43457 + 63128 + 63302 + 8986 + 8128 + 7562 + 13517 + 12519 + 12024 = 311506 := Proofs.tab3_totals_proved

/-! ## Sections 5-7: the Grunsky-layer rows -/

/-- sec_05_grunsky_q.tex:13: "The coefficients of `a(s)` have phases `nθ/4`, so `a(t) = \overline{a(s)}`"
(entrywise, every `s`; likewise `a_e`, `b_e`). -/
theorem sec5_a_conj (s : ℂ) (n : ℕ) :
    aOdd (conj s) n = conj (aOdd s n) ∧ aEven (conj s) n = conj (aEven s n) ∧ bEven (conj s) n = conj (bEven s n) := Proofs.sec5_a_conj_proved s n

/-- sec_05_grunsky_q.tex:17-19: by (eq:gram), with `u = Re a(s)`, `v = Im a(s)` (`s = s_θ`):
`uᵀu = (A_o + Re Z_o)/2`, `vᵀv = (A_o - Re Z_o)/2`, `uᵀv = Im Z_o / 2`. -/
theorem sec5_uv_gram (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    HasSum (fun n => uvec θ n ^ 2) ((Ao + (Zo θ).re) / 2) ∧ HasSum (fun n => vvec θ n ^ 2) ((Ao - (Zo θ).re) / 2) ∧
      HasSum (fun n => uvec θ n * vvec θ n) ((Zo θ).im / 2) := Proofs.sec5_uv_gram_proved θ h0 hπ

/-- sec_05_grunsky_q.tex:13-17: `V` has orthonormal columns, `u = V ũ`, `v = V ṽ`, and `O₂ = Vᵀ O V` is complex
symmetric with `‖O₂‖ ≤ ‖O‖ ≤ 1`. PROVED GIVEN the strong Grunsky inequality. -/
theorem sec5_O2_contraction (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (∀ i j : Fin 2, HasSum (fun n => Vcol θ i n * Vcol θ j n) (if i = j then 1 else 0)) ∧
      (∀ n, uvec θ n = l11 θ * Vcol θ 0 n) ∧ (∀ n, vvec θ n = l21 θ * Vcol θ 0 n + l22 θ * Vcol θ 1 n) ∧
      InBall (O2 γ θ) := Proofs.sec5_O2_contraction_proved_from sec3_grunsky_unique sec3_blocks_compressions sec5_uv_gram sec5_coords hG f h hf hh γ hγ θ h0 hπ

/-- sec_05_grunsky_q.tex:17: "and `uᵀOu = ũᵀO₂ũ`; similarly `vᵀOv = ṽᵀO₂ṽ` and `uᵀOv = ũᵀO₂ṽ`": `uᵀOu`, `vᵀOv`,
`uᵀOv` are `m_uu`, `m_vv`, `m_uv` of `M = O₂`. -/
theorem sec5_O2_entries (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ) ∧
      bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ) ∧
      bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ) := Proofs.sec5_O2_entries_proved_from sec5_coords f h hf hh γ hγ θ h0 hπ

/-- Proposition 5.1 (sec_05_grunsky_q.tex:35-37): for every `f ∈ 𝒮` and `θ ∈ (0, π]`,
`Q_f(z_θ, \overline{z_θ}) = Q_rel(O₂)` (`O₂` from the Grunsky coefficients `γ` of the odd root `h` of `f`). -/
theorem prop_5_1 (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
    (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ) := Proofs.prop_5_1_proved_from lem_3_1_i sec3_grunsky_unique sec5_coords f h hf hh γ hγ θ h0 hπ

/-- sec_05_grunsky_q.tex:54: "If, for a given `θ`, `Re Q_rel > 0` on `𝓑`, then `Re Q_f(z_θ, \overline{z_θ}) > 0` for
every `f ∈ 𝒮`." PROVED GIVEN the bidisc power series and the strong Grunsky inequality. -/
theorem sec5_relaxation (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi)
    (hpos : ∀ M, InBall M → 0 < (Qrel θ M).re) : ∀ f : ℂ → ℂ, InS f → 0 < (Q f (zθ θ) (conj (zθ θ))).re := Proofs.sec5_relaxation_proved_from sec3_oddroot_exists sec3_grunsky_exists lem_3_1_i sec3_blocks_compressions sec5_uv_gram sec5_coords hB hG θ h0 hπ hpos

/-- Lemma 6.3 (sec_06_far.tex:59-61): for `f ∈ 𝒮` and distinct `z, w ∈ 𝔻`,
`Q_f(z, w) - p(z) - p(w) = β(z)ᵀ C(f) α(w) + β(w)ᵀ C(f) α(z)`. -/
theorem lem_6_3 (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hzw : z ≠ w) :
    Q f z w - pfun f z - pfun f w =
      bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z) := Proofs.lem_6_3_proved f hf γ hγ z w hz hw hzw

/-- sec_06_far.tex:72 (an auxiliary remark; the proof does not use it): "Lemma 6.3 is Barnard's identity [Bar78, (5)],
written in terms of the Grunsky matrix: the right side of Lemma 6.3 is `∑_{n,m ≥ 1} (n + m) γ_{nm}(f) zⁿ wᵐ`"
(for `f ∈ 𝒮`, `z, w ∈ 𝔻`; `γ_{nm} = 0` when `n = 0` or
`m = 0`, so the sum over `ℕ × ℕ` is the printed one). -/
theorem sec6_barnard_series (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z) =
      ∑' nm : ℕ × ℕ, ((nm.1 : ℂ) + nm.2) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2 := Proofs.sec6_barnard_series_proved_from sec3_grunsky_unique f hf γ hγ z w hz hw

/-- sec_06_far.tex:74-82: for `|z| = ½`: `U_R = ‖β(z)‖² = 4/9`, `V_R = ‖α(z)‖² = log(4/3)`, `β(z)ᵀβ(z) = z²/(1 - z²)²`,
`α(z)ᵀα(z) = -log(1 - z²)`, and `α(z̄) = \overline{α(z)}`, `β(z̄) = \overline{β(z)}`. -/
theorem sec6_UV_values (z : ℂ) (hz : ‖z‖ = 1 / 2) :
    HasSum (fun n => ‖betaV z n‖ ^ 2) U0 ∧ HasSum (fun n => ‖alphaV z n‖ ^ 2) V0 ∧
      HasSum (fun n => betaV z n ^ 2) (z ^ 2 / (1 - z ^ 2) ^ 2) ∧ HasSum (fun n => alphaV z n ^ 2) (-log (1 - z ^ 2)) ∧
      ∀ n, alphaV (conj z) n = conj (alphaV z n) ∧ betaV (conj z) n = conj (betaV z n) := Proofs.sec6_UV_values_proved z hz

/-- sec_06_far.tex:74-82: for `f ∈ 𝒮` and `θ ∈ [135°, 180°]`, `c = cos(θ/2)`:
`|R_f| = |Q_f(z, w) - p(z) - p(w)| ≤ √((U_R + A_R)(V_R + B_R)) + √((U_R - A_R)(V_R - B_R))`.
PROVED GIVEN the bidisc power series and the strong Grunsky inequality. -/
theorem sec6_Rf_bound (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f : ℂ → ℂ) (hf : InS f) (θ : ℝ)
    (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    ‖Q f (zθ θ) (conj (zθ θ)) - pfun f (zθ θ) - pfun f (conj (zθ θ))‖ ≤ Rbound (Real.cos (θ / 2)) := Proofs.sec6_Rf_bound_proved_from sec3_grunsky_exists sec3_cauchy sec6_UV_values sec6_A0B0_closed hB hG f hf θ h1 h2

/-- sec_06_far.tex:18: "(both are nonzero, since `Re a(s)` and `Im a(s)` are linearly independent; see
Section 5)": `σ₊ > 0` and `σ₋ > 0` for `θ ∈ (0, π]` (stated as positive: slightly stronger than "nonzero", and true). -/
theorem sec6_sigma_pos : ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < sigM θ ∧ 0 < sigP θ := Proofs.sec6_sigma_pos_proved

/-- sec_06_far.tex:14-28: for `f ∈ 𝒮` and `θ ∈ [135°, 180°]`, in the rotated real orthonormal basis
(`a(s) = e^{iφ/2}(√σ₊, i√σ₋)`) the odd block compresses to a complex symmetric `O'` with `‖O'‖ ≤ 1`, and
`log p = e^{iφ}(Lξ₁ + idξ₂)`, `log q = e^{-iφ}(Lξ₁ - idξ₂)`, `ξ₁ = 2(σ₊O'₁₁ - σ₋O'₂₂)/L`, `ξ₂ = O'₁₂`; Lean states it
with `X = Lξ₁ = 2(σ₊O'₁₁ - σ₋O'₂₂)` and `Y = dξ₂ = dO'₁₂` (and for `p = exp(log p)`, `q = exp(log q)`). PROVED GIVEN the bidisc power series and the strong Grunsky inequality. -/
theorem sec6_logp_logq (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f : ℂ → ℂ) (hf : InS f) (θ : ℝ)
    (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    ∃ N : Matrix (Fin 2) (Fin 2) ℂ, InBall N ∧
      pfun f (zθ θ) = exp (exp ((phiFar θ : ℂ) * I) *
        (2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1) + I * ((dFar θ : ℂ) * N 0 1))) ∧
      pfun f (conj (zθ θ)) = exp (exp (-((phiFar θ : ℂ) * I)) *
        (2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1) - I * ((dFar θ : ℂ) * N 0 1))) := Proofs.sec6_logp_logq_proved_from sec3_oddroot_exists sec3_oddroot_mem_S sec3_grunsky_exists sec3_cauchy sec3_blocks_compressions lem_3_1_iii eq_gram hB hG f hf θ h1 h2

/-- sec_06_far.tex:51-53 (eq:psum): for `f ∈ 𝒮` and `θ ∈ [135°, 180°]`, `Re(p + q) = 2 Re e^{ℓ₊} > 277/400`.
PROVED GIVEN the bidisc power series, the strong Grunsky inequality and Lemma 6.2's check. -/
theorem eq_psum (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h62 : Check_6_2) (f : ℂ → ℂ) (hf : InS f)
    (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    277 / 400 < (pfun f (zθ θ) + pfun f (conj (zθ θ))).re := Proofs.eq_psum_proved_from sec3_oddroot_exists sec3_oddroot_mem_S sec3_grunsky_exists sec3_cauchy sec3_blocks_compressions lem_3_1_iii eq_gram sec6_psum_cos sec6_xi_ball sec6_b_change sec6_b_values sec6_Wbound_finite sec6_expW_bound hB hG h62 f hf θ h1 h2

/-- The proof of Proposition 6.1 (sec_06_far.tex:96-98): from (eq:psum) and `|R_f| < 173/250`,
`Re Q_f(z, w) ≥ Re(p + q) - |R_f| > 277/400 - 173/250 = 1/2000`. -/
theorem prop_6_1_from_layer
    (hpsum : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      277 / 400 < (pfun f (zθ θ) + pfun f (conj (zθ θ))).re)
    (hR : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      ‖Q f (zθ θ) (conj (zθ θ)) - pfun f (zθ θ) - pfun f (conj (zθ θ))‖ < 173 / 250) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 → 1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re := Proofs.prop_6_1_from_layer_proved hpsum hR

/-- sec_07_middle.tex:16: "`b_e(s) = (√n sⁿ)_{n even}`; it is `s (d/ds) a_e(s)`" (entrywise). -/
theorem sec7_be_deriv (s : ℂ) (n : ℕ) : bEven s n = s * deriv (fun x => aEven x n) s := Proofs.sec7_be_deriv_proved s n

/-- Lemma 7.3 (sec_07_middle.tex:31-37): for `f ∈ 𝒮`, `θ ∈ (0, π]`, `E` the even block of the Grunsky matrix of `h`:
`U(O₂) = (a_e(s) - a_e(t))ᵀ E (a_e(s) + a_e(t))` and `R(O₂) = b_e(s)ᵀ E a_e(t) + b_e(t)ᵀ E a_e(s)`.
PROVED GIVEN the bidisc power series (`E = C(f)`) and the strong Grunsky inequality (`‖O₂‖ ≤ 1`, eq:cauchy). -/
theorem lem_7_3 (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    Ufun θ (O2 γ θ) = bilinf (fun n => aEven (sθ θ) n - aEven (conj (sθ θ)) n) (Eblock γ)
        (fun n => aEven (sθ θ) n + aEven (conj (sθ θ)) n) ∧
      Rfun θ (O2 γ θ) = bilinf (bEven (sθ θ)) (Eblock γ) (aEven (conj (sθ θ))) +
        bilinf (bEven (conj (sθ θ))) (Eblock γ) (aEven (sθ θ)) := Proofs.lem_7_3_proved_from lem_3_1_i lem_3_1_ii lem_3_1_iii sec3_OE_contractions sec5_O2_entries sec3_grunsky_exists eq_Kf lem_6_3 prop_5_1 hB hG f h hf hh γ hγ θ h0 hπ

/-- sec_07_middle.tex:50-53 (eq:UR): with `a_e(s) = u_e + i v_e`, `b_e(s) = β₀ + iβ₁` (real sequences):
`iU(O₂) = -4 u_eᵀ E v_e` and `R(O₂) = 2(β₀ᵀ E u_e + β₁ᵀ E v_e)`. PROVED GIVEN the facts of Lemma 7.3. -/
theorem eq_UR (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    I * Ufun θ (O2 γ θ) =
        -4 * bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ)) ∧
      Rfun θ (O2 γ θ) = 2 * (bilinf (fun n => (wEven θ 2 n : ℂ)) (Eblock γ) (fun n => (wEven θ 0 n : ℂ)) +
        bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) := Proofs.eq_UR_proved_from lem_3_1_i lem_3_1_ii lem_3_1_iii sec3_OE_contractions sec5_O2_entries sec3_grunsky_exists eq_Kf lem_6_3 prop_5_1 hB hG f h hf hh γ hγ θ h0 hπ

/-- sec_07_middle.tex:54-67: the real 4x4 Gram matrix of `u_e, v_e, β₀, β₁` is `G(θ)` ("summing the geometric series";
e.g. `‖b_e(s)‖² = 8/9`, `b_e(s)ᵀ b_e(s) = 2z²/(1 - z²)²`). -/
theorem sec7_gram (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    ∀ i j : Fin 4, HasSum (fun n => wEven θ i n * wEven θ j n) (Gram θ i j) := Proofs.sec7_gram_proved θ h0 hπ

/-- Lemma 7.4 (sec_07_middle.tex:69-79): for real `λ, μ`, `P` real symmetric positive definite, `f ∈ 𝒮` and
`θ ∈ (0, π]`: `|λ iU(O₂) - μ R(O₂)| ≤ C_P(θ)`. PROVED GIVEN the bidisc power series and the strong Grunsky
inequality. -/
theorem lem_7_4 (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (lam mu : ℝ)
    (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : P.PosDef) :
    ‖(lam : ℂ) * (I * Ufun θ (O2 γ θ)) - (mu : ℂ) * Rfun θ (O2 γ θ)‖ ≤ CP θ lam mu P := Proofs.lem_7_4_proved_from lem_3_1_i lem_3_1_ii lem_3_1_iii sec3_OE_contractions sec5_O2_entries sec3_grunsky_exists eq_Kf lem_6_3 prop_5_1 sec7_gram hB hG f h hf hh γ hγ θ h0 hπ lam mu P hP

/-- Proposition 7.5(ii) (sec_07_middle.tex:109): for every `f ∈ 𝒮` and `θ ∈ (0, π]`,
`Re F(O₂) ≤ Re Q_f(z_θ, \overline{z_θ})`. PROVED GIVEN the bidisc power series and the strong Grunsky inequality. -/
theorem prop_7_5_ii (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (Ffun θ (O2 γ θ)).re ≤ (Q f (zθ θ) (conj (zθ θ))).re := Proofs.prop_7_5_ii_proved_from lem_3_1_i lem_3_1_ii lem_3_1_iii sec3_OE_contractions sec5_O2_entries sec3_grunsky_exists eq_Kf lem_6_3 prop_5_1 sec7_gram hB hG f h hf hh γ hγ θ h0 hπ

/-- sec_05_grunsky_q.tex:54: "not every `M ∈ 𝓑` comes from a univalent function": at `θ = 60°` some `M ∈ 𝓑` is `O₂`
of no `f ∈ 𝒮` (Remark 5.6's matrix, with Proposition 7.1 at `θ = 60°`). PROVED GIVEN the facts and the band check
used at `θ = 60°`. (Placed after Proposition 7.5(ii), which its proof uses.) -/
theorem sec5_not_all_from_S (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h2 : Check_7_6_band02) :
    ∃ M, InBall M ∧ ∀ f h : ℂ → ℂ, InS f → IsOddRoot f h → ∀ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff h γ →
      O2 γ (deg 60) ≠ M := Proofs.sec5_not_all_from_S_proved_from rem_5_6 prop_7_5_ii lem_3_1_i sec3_grunsky_unique sec5_coords hB hG h2

/-- The proof of Proposition 7.1 (sec_07_middle.tex:167-169): if every `Q_f(z_θ, \overline{z_θ})` (`f ∈ 𝒮`,
`θ ∈ (0, π]`) is `Q_rel(M)` for some `M ∈ 𝓑` with `Re F(M) ≤ Re Q_f(z_θ, \overline{z_θ})` (Propositions 5.1, 7.5),
`Φ_F > 0` on `[50.3°, 90°] x 𝓧` and `Φ_rel > 0` on `[90°, 135°] x 𝓧` (Lemma 7.6), then Proposition 7.1 holds (via
Corollary 5.5). -/
theorem prop_7_1_from_layer
    (hrep : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → ∃ M, InBall M ∧
      Q f (zθ θ) (conj (zθ θ)) = Qrel θ M ∧ (Ffun θ M).re ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hs : ∀ θ : ℝ, 50.3 ≤ θ → θ ≤ 90 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiS θ α ψ ω)
    (hp : ∀ θ : ℝ, 90 ≤ θ → θ ≤ 135 → ∀ α ψ ω : ℝ, InX α ψ ω → 0 < PhiP θ α ψ ω) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 → 0 < (Q f (zθ θ) (conj (zθ θ))).re := Proofs.prop_7_1_from_layer_proved hrep hs hp

/-! ## The three ranges of angles (printed statements; proofs in Sections 4, 6, 7) -/

/-- Proposition 4.1 (sec_04_near.tex:24-29): for every `f ∈ 𝒮` and every `θ ∈ (0, θ₀]`,
`Re Q_f(z_θ, \overline{z_θ}) ≥ sin²(θ/2)/80`. -/
theorem prop_4_1 (hDB : FactDeBranges) (hArea : FactArea) (h48 : Check_4_8) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
    Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re := Proofs.prop_4_1_proved_from prop_4_1_from_layer sec4_e_zero sec4_Gtau sec4_majorant_split lem_4_3 lem_4_5_iii lem_4_6 hDB hArea h48

/-- Proposition 6.1 (sec_06_far.tex:7-9): for every `f ∈ 𝒮` and every `θ ∈ [135°, 180°]`,
`Re Q_f(z_θ, \overline{z_θ}) > 1/2000`. -/
theorem prop_6_1 (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h62 : Check_6_2) (h64 : Check_6_4) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
    1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re :=
  prop_6_1_from_layer (fun f hf θ h1 h2 => eq_psum hB hG h62 f hf θ h1 h2)
    (fun f hf θ h1 h2 => lt_of_le_of_lt (sec6_Rf_bound hB hG f hf θ h1 h2)
      (h64 _ (sec6_c_bound θ h1 h2).1 ((sec6_c_bound θ h1 h2).2.1.trans (sec6_c_bound θ h1 h2).2.2.le)))

/-- Proposition 7.1 (sec_07_middle.tex:9-11): for every `f ∈ 𝒮` and every `θ ∈ [50.3°, 135°]`,
`Re Q_f(z_θ, \overline{z_θ}) > 0`. -/
theorem prop_7_1 (hB : FactBidiscPowerSeries) (hG : FactGrunsky)
    (h1 : Check_7_6_band01) (h2 : Check_7_6_band02) (h3 : Check_7_6_band03) (h4 : Check_7_6_band04)
    (h5 : Check_7_6_band05) (h6 : Check_7_6_band06) (h7 : Check_7_6_band07) (h8 : Check_7_6_band08)
    (h9 : Check_7_6_band09) (h10 : Check_7_6_band10) (h11 : Check_7_6_band11) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 →
    0 < (Q f (zθ θ) (conj (zθ θ))).re :=
  prop_7_1_from_layer
    (fun f hf θ h0 hπ => by
      obtain ⟨h, hh⟩ := sec3_oddroot_exists f hf
      obtain ⟨γ, hγ, -⟩ := sec3_grunsky_exists hB h (sec3_oddroot_mem_S f h hf hh)
      exact ⟨O2 γ θ, (sec5_O2_contraction hG f h hf hh γ hγ θ h0 hπ).2.2.2, prop_5_1 f h hf hh γ hγ θ h0 hπ,
        prop_7_5_ii hB hG f h hf hh γ hγ θ h0 hπ⟩)
    (lem_7_6_i h1 h2 h3 h4 h5) (lem_7_6_ii h6 h7 h8 h9 h10 h11)

/-! ## Section 8 (proof of the main theorems) -/

/-- Lemma 8.1 (sec_08_proof.tex:7-9): `θ₀ > 50.3°`, that is, `sin(503π/3600) < 17/40`. -/
theorem lem_8_1 : deg 50.3 < θ₀ ∧ Real.sin (503 * Real.pi / 3600) < 17 / 40 := Proofs.lem_8_1_proved

/-- sec_08_proof.tex:5 and :19: "The three ranges of angles overlap" and "these three ranges cover `(0°, 180°]`":
`(0, θ₀]`, `[50.3°, 135°]` and `[135°, 180°]` cover `(0, π]` (with `180° = π`). -/
theorem sec8_cover :
    deg 180 = Real.pi ∧ ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi →
      θ ≤ θ₀ ∨ (deg 50.3 ≤ θ ∧ θ ≤ deg 135) ∨ (deg 135 ≤ θ ∧ θ ≤ deg 180) := Proofs.sec8_cover_proved

/-- sec_08_proof.tex:18-20, the proof of Theorems 1.1 and 1.2: from Propositions 4.1, 7.1 and 6.1 (as hypotheses
here), Proposition 2.4 and Proposition 2.5, Theorem 1.1 and Theorem 1.2 follow.
PROVED GIVEN the facts of Lemma 2.2. -/
theorem sec8_assembly (hAP : FactArgumentPrinciple) (hJ : FactJordanCurve)
    (hnear : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hmiddle : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    (hfar : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re) :
    ((∀ f : ℂ → ℂ, InS f → Set.InjOn (Gam f) (closedBall (0 : ℂ) (1 / 2))) ∧
        ∀ r : ℝ, 1 / 2 < r → ∃ f : ℂ → ℂ, InS f ∧ ¬ Set.InjOn (Gam f) (ball (0 : ℂ) r)) ∧
      (∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r → z ≠ w →
        0 < (Q f z w).re) := Proofs.sec8_assembly_proved hAP hJ hnear hmiddle hfar

/-- Theorem 1.1 (sec_01_intro.tex:13-15): for every `f ∈ 𝒮`, the function `Γ f` is injective on the closed disc
`|z| ≤ ½`. The radius `½` is sharp, as Robinson observed [Rob47, p. 18]: for every `r > ½` some `f ∈ 𝒮` has `Γ f`
not injective on `|z| < r`.
Its proof uses Propositions 4.1, 6.1, 7.1 (with their checks and facts) and the facts of Lemma 2.2. -/
theorem thm_1_1 (hAP : FactArgumentPrinciple) (hJ : FactJordanCurve) (hDB : FactDeBranges) (hArea : FactArea) (h48 : Check_4_8)
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h62 : Check_6_2) (h64 : Check_6_4)
    (h1 : Check_7_6_band01) (h2 : Check_7_6_band02) (h3 : Check_7_6_band03) (h4 : Check_7_6_band04)
    (h5 : Check_7_6_band05) (h6 : Check_7_6_band06) (h7 : Check_7_6_band07) (h8 : Check_7_6_band08)
    (h9 : Check_7_6_band09) (h10 : Check_7_6_band10) (h11 : Check_7_6_band11) :
    (∀ f : ℂ → ℂ, InS f → Set.InjOn (Gam f) (closedBall (0 : ℂ) (1 / 2))) ∧
      ∀ r : ℝ, 1 / 2 < r → ∃ f : ℂ → ℂ, InS f ∧ ¬ Set.InjOn (Gam f) (ball (0 : ℂ) r) :=
  (sec8_assembly hAP hJ (prop_4_1 hDB hArea h48) (prop_7_1 hB hG h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
    (prop_6_1 hB hG h62 h64)).1

/-- Theorem 1.2 (sec_01_intro.tex:23-28): for every `f ∈ 𝒮`, every `r ∈ (0, ½]` and all distinct `z, w` with
`|z| = |w| = r`, `Re Q_f(z, w) > 0`. -/
theorem thm_1_2 (hDB : FactDeBranges) (hArea : FactArea) (h48 : Check_4_8)
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h62 : Check_6_2) (h64 : Check_6_4)
    (h1 : Check_7_6_band01) (h2 : Check_7_6_band02) (h3 : Check_7_6_band03) (h4 : Check_7_6_band04)
    (h5 : Check_7_6_band05) (h6 : Check_7_6_band06) (h7 : Check_7_6_band07) (h8 : Check_7_6_band08)
    (h9 : Check_7_6_band09) (h10 : Check_7_6_band10) (h11 : Check_7_6_band11) :
    ∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r → z ≠ w →
    0 < (Q f z w).re :=
  Proofs.thm_1_2_from (prop_4_1 hDB hArea h48) (prop_7_1 hB hG h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
    (prop_6_1 hB hG h62 h64)

/-- Remark 8.2 (sec_08_proof.tex:22-24; sec_01_intro.tex:46): for distinct `z, w` with `|z| = |w| = r ≤ ½` and
angular distance `θ` (`w = z e^{±iθ}`, `0 < θ ≤ π`): `Re Q_f(z, w) ≥ sin²(θ/2)/80` when `θ ≤ θ₀`, and
`Re Q_f(z, w) > 1/2000` when `θ ≥ 135°`. The remark's middle range, "the bound is `Re Q_f > 0` (Proposition 7.1)"
(sec_08_proof.tex:23), is `thm_1_2` (for every angle), through `prop_7_1`. -/
theorem rem_8_2 (hDB : FactDeBranges) (hArea : FactArea) (h48 : Check_4_8)
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h62 : Check_6_2) (h64 : Check_6_4) :
    ∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r →
    ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → (w = z * exp ((θ : ℂ) * I) ∨ w = z * exp (-((θ : ℂ) * I))) →
      (θ ≤ θ₀ → Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f z w).re) ∧ (deg 135 ≤ θ → 1 / 2000 < (Q f z w).re) :=
  Proofs.rem_8_2_from (prop_4_1 hDB hArea h48) (prop_6_1 hB hG h62 h64)

end Robinson.Paper
