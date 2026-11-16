/-
Robinson/Proofs/NearP_D.lean — the second-order remainder of Section 4 (Lemma 4.6).
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Proofs.NearP_C
import Robinson.Proofs.NearP_B
import Robinson.Proofs.TdotClosed

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Coefficients of sums, products and inverses -/

lemma coeff_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) (n : ℕ) : coeff f n = coeff g n := by
  unfold coeff
  rw [h.iteratedDeriv_eq n]

lemma coeff_mulC {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (fun x => f x * g x) n = cmul (coeff f) (coeff g) n := by
  unfold coeff cmul
  rw [show (fun x => f x * g x) = f * g from rfl, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h := Nat.choose_mul_factorial_mul_factorial hk'
  have hc0 : ((n.choose k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
  rw [← h]
  push_cast
  generalize iteratedDeriv k f 0 = A
  generalize iteratedDeriv (n - k) g 0 = B
  rw [div_mul_div_comm, mul_assoc, mul_assoc, mul_div_mul_left _ _ hc0]

lemma coeff_addC {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (fun x => f x + g x) n = coeff f n + coeff g n := by
  unfold coeff
  rw [show (fun x => f x + g x) = f + g from rfl, iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

lemma coeff_negC (f : ℂ → ℂ) (n : ℕ) : coeff (fun x => -f x) n = -coeff f n := by
  unfold coeff
  rw [iteratedDeriv_fun_neg, neg_div]

lemma coeff_smulC (r : ℂ) (f : ℂ → ℂ) (n : ℕ) : coeff (fun x => r * f x) n = r * coeff f n := by
  unfold coeff
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

lemma coeff_const_fun (a : ℂ) (n : ℕ) : coeff (fun _ => a) n = if n = 0 then a else 0 := by
  unfold coeff
  rw [iteratedDeriv_const]
  split_ifs with h
  · subst h
    simp
  · simp

lemma coeff_id_fun (n : ℕ) : coeff (fun x : ℂ => x) n = if n = 1 then 1 else 0 := by
  unfold coeff
  rw [iteratedDeriv_fun_id_zero]
  split_ifs with h
  · subst h
    simp
  · simp

lemma cmul_low {a b : ℕ → ℂ} {p q : ℕ} (ha : ∀ i, i < p → a i = 0) (hb : ∀ i, i < q → b i = 0) (n : ℕ)
    (hn : n < p + q) : cmul a b n = 0 := by
  unfold cmul
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  by_cases hkp : k < p
  · rw [ha k hkp, zero_mul]
  · rw [hb (n - k) (by omega), mul_zero]

lemma coeff_low_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) {p q : ℕ}
    (hf0 : ∀ i, i < p → coeff f i = 0) (hg0 : ∀ i, i < q → coeff g i = 0) (n : ℕ) (hn : n < p + q) :
    coeff (fun x => f x * g x) n = 0 := by
  rw [coeff_mulC hf hg]
  exact cmul_low hf0 hg0 n hn

lemma cmul_re_of_real {u w : ℕ → ℂ} (hu : ∀ n, (u n).im = 0) (hw : ∀ n, (w n).im = 0) (n : ℕ) :
    (cmul u w n).im = 0 ∧ (cmul u w n).re = cmul (fun k => (u k).re) (fun k => (w k).re) n := by
  refine ⟨?_, ?_⟩
  · simp [cmul, Complex.im_sum, Complex.mul_im, hu, hw]
  · simp [cmul, Complex.re_sum, Complex.mul_re, hu, hw]

lemma norm_eq_re_of {z : ℂ} (h : z.im = 0) (h' : 0 ≤ z.re) : ‖z‖ = z.re := by
  have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])
  conv_lhs => rw [e]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h']

/-! ### Majorants of functions -/

/-- The coefficients of `Z` at `0` are real and nonnegative. -/
def PosCoeff (Z : ℂ → ℂ) : Prop := ∀ n, (coeff Z n).im = 0 ∧ 0 ≤ (coeff Z n).re

/-- `f ≪ Z`: both analytic at `0`, the coefficients of `Z` are real, nonnegative and dominate those of `f`. -/
def MajF (f Z : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ Z 0 ∧ PosCoeff Z ∧ Majorizes (coeff f) (fun n => (coeff Z n).re)

lemma MajF.self {Z : ℂ → ℂ} (hZ : AnalyticAt ℂ Z 0) (hP : PosCoeff Z) : MajF Z Z :=
  ⟨hZ, hZ, hP, fun n => le_of_eq (norm_eq_re_of (hP n).1 (hP n).2)⟩

lemma MajF.mul {f g Z W : ℂ → ℂ} (hf : MajF f Z) (hg : MajF g W) :
    MajF (fun x => f x * g x) (fun x => Z x * W x) := by
  obtain ⟨hfa, hZa, hZp, hfm⟩ := hf
  obtain ⟨hga, hWa, hWp, hgm⟩ := hg
  have hre : ∀ n, (coeff (fun x => Z x * W x) n).im = 0 ∧
      (coeff (fun x => Z x * W x) n).re = cmul (fun k => (coeff Z k).re) (fun k => (coeff W k).re) n := by
    intro n
    rw [coeff_mulC hZa hWa]
    exact cmul_re_of_real (fun k => (hZp k).1) (fun k => (hWp k).1) n
  refine ⟨hfa.mul hga, hZa.mul hWa, fun n => ⟨(hre n).1, ?_⟩, fun n => ?_⟩
  · rw [(hre n).2]
    exact cmul_nonneg (fun k => (hZp k).2) (fun k => (hWp k).2) n
  · show ‖coeff (fun x => f x * g x) n‖ ≤ (coeff (fun x => Z x * W x) n).re
    rw [coeff_mulC hfa hga, (hre n).2]
    exact (sec4_majorant_rules_proved.2.1 _ _ _ _ hfm hgm).2 n

lemma MajF.add {f g Z W : ℂ → ℂ} (hf : MajF f Z) (hg : MajF g W) :
    MajF (fun x => f x + g x) (fun x => Z x + W x) := by
  obtain ⟨hfa, hZa, hZp, hfm⟩ := hf
  obtain ⟨hga, hWa, hWp, hgm⟩ := hg
  refine ⟨hfa.add hga, hZa.add hWa, fun n => ?_, fun n => ?_⟩
  · rw [coeff_addC hZa hWa, Complex.add_im, Complex.add_re, (hZp n).1, (hWp n).1, add_zero]
    exact ⟨rfl, add_nonneg (hZp n).2 (hWp n).2⟩
  · show ‖coeff (fun x => f x + g x) n‖ ≤ (coeff (fun x => Z x + W x) n).re
    rw [coeff_addC hfa hga, coeff_addC hZa hWa, Complex.add_re]
    exact (norm_add_le _ _).trans (add_le_add (hfm n) (hgm n))

lemma MajF.smul {f Z : ℂ → ℂ} (hf : MajF f Z) (r : ℂ) (s : ℝ) (hrs : ‖r‖ ≤ s) :
    MajF (fun x => r * f x) (fun x => (s : ℂ) * Z x) := by
  obtain ⟨hfa, hZa, hZp, hfm⟩ := hf
  have hs : 0 ≤ s := (norm_nonneg _).trans hrs
  refine ⟨analyticAt_const.mul hfa, analyticAt_const.mul hZa, fun n => ?_, fun n => ?_⟩
  · rw [coeff_smulC, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hZp n).1, mul_zero]
    exact ⟨rfl, mul_nonneg hs (hZp n).2⟩
  · show ‖coeff (fun x => r * f x) n‖ ≤ (coeff (fun x => (s : ℂ) * Z x) n).re
    rw [coeff_smulC, coeff_smulC, Complex.re_ofReal_mul, norm_mul]
    exact mul_le_mul hrs (hfm n) (norm_nonneg _) hs

lemma MajF.neg {f Z : ℂ → ℂ} (hf : MajF f Z) : MajF (fun x => -f x) Z := by
  obtain ⟨hfa, hZa, hZp, hfm⟩ := hf
  refine ⟨hfa.neg, hZa, hZp, fun n => ?_⟩
  show ‖coeff (fun x => -f x) n‖ ≤ (coeff Z n).re
  rw [coeff_negC, norm_neg]
  exact hfm n

lemma MajF.congr {f f' Z Z' : ℂ → ℂ} (hf : MajF f Z) (h1 : f =ᶠ[𝓝 0] f') (h2 : Z = Z') : MajF f' Z' := by
  subst h2
  obtain ⟨hfa, hZa, hZp, hfm⟩ := hf
  exact ⟨hfa.congr h1, hZa, hZp, fun n => by
    show ‖coeff f' n‖ ≤ (coeff Z n).re
    rw [← coeff_congr h1 n]
    exact hfm n⟩

lemma MajF.mono {f Z Z' : ℂ → ℂ} (hf : MajF f Z) (hZ' : AnalyticAt ℂ Z' 0) (hP : PosCoeff Z')
    (h : ∀ n, (coeff Z n).re ≤ (coeff Z' n).re) : MajF f Z' :=
  ⟨hf.1, hZ', hP, fun n => (hf.2.2.2 n).trans (h n)⟩

lemma posCoeff_one : PosCoeff (fun _ => (1 : ℂ)) := fun n => by
  rw [coeff_const_fun]
  split_ifs <;> simp

lemma posCoeff_id : PosCoeff (fun x : ℂ => x) := fun n => by
  rw [coeff_id_fun]
  split_ifs <;> simp

lemma MajF.one : MajF (fun _ => (1 : ℂ)) (fun _ => 1) := MajF.self analyticAt_const posCoeff_one

lemma MajF.ident : MajF (fun x : ℂ => x) (fun x => x) := MajF.self analyticAt_id posCoeff_id

/-- `1/L = 1 + (1 - L)(1/L)` gives the recursion for the coefficients of `1/L`. -/
lemma coeff_inv_rec {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 0) (hL0 : L 0 = 1) (n : ℕ) :
    coeff (fun x => 1 / L x) n =
      (if n = 0 then 1 else 0) + cmul (coeff (fun x => 1 - L x)) (coeff (fun x => 1 / L x)) n := by
  have hne : ∀ᶠ x in 𝓝 (0 : ℂ), L x ≠ 0 :=
    hL.continuousAt.eventually_ne (by rw [hL0]; exact one_ne_zero)
  have hinv : AnalyticAt ℂ (fun x => 1 / L x) 0 := analyticAt_const.div hL (by rw [hL0]; exact one_ne_zero)
  have hF : AnalyticAt ℂ (fun x => 1 - L x) 0 := analyticAt_const.sub hL
  have heq : (fun x => 1 / L x) =ᶠ[𝓝 0] fun x => 1 + (1 - L x) * (1 / L x) := by
    filter_upwards [hne] with x hx
    rw [sub_mul, one_mul, mul_one_div_cancel hx]
    ring
  have hFm : AnalyticAt ℂ (fun x => (1 - L x) * (1 / L x)) 0 := hF.mul hinv
  have h1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 0 := analyticAt_const
  rw [coeff_congr heq n, coeff_addC h1 hFm, coeff_const_fun, coeff_mulC hF hinv]

lemma posCoeff_inv {Lc : ℂ → ℂ} (hLc : AnalyticAt ℂ Lc 0) (hLc0 : Lc 0 = 1)
    (hP : PosCoeff (fun x => 1 - Lc x)) : PosCoeff (fun x => 1 / Lc x) := by
  have hF0 : coeff (fun x => 1 - Lc x) 0 = 0 := by
    rw [coeff_zero_eq]
    simp [hLc0]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [coeff_inv_rec hLc hLc0 n]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (coeff (fun x => 1 - Lc x) k * coeff (fun x => 1 / Lc x) (n - k)).im = 0 ∧
          0 ≤ (coeff (fun x => 1 - Lc x) k * coeff (fun x => 1 / Lc x) (n - k)).re := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        rw [hF0, zero_mul]
        simp
      · have hlt : n - k < n := by
          have := Finset.mem_range.mp hk
          omega
        obtain ⟨i1, r1⟩ := hP k
        obtain ⟨i2, r2⟩ := ih (n - k) hlt
        rw [Complex.mul_im, Complex.mul_re, i1, i2]
        refine ⟨by ring, ?_⟩
        nlinarith [mul_nonneg r1 r2]
    simp only [cmul, Complex.add_im, Complex.add_re, Complex.im_sum, Complex.re_sum]
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_eq_zero (fun k hk => (hterm k hk).1)]
      split_ifs <;> simp
    · refine add_nonneg ?_ (Finset.sum_nonneg (fun k hk => (hterm k hk).2))
      split_ifs <;> simp

/-- Rule (iii) of the majorant calculus, for functions: `1 - L ≪ 1 - L_c` gives `1/L ≪ 1/L_c`. -/
lemma MajF.inv {L Lc : ℂ → ℂ} (hL : AnalyticAt ℂ L 0) (hLc : AnalyticAt ℂ Lc 0) (hL0 : L 0 = 1)
    (hLc0 : Lc 0 = 1) (hF : MajF (fun x => 1 - L x) (fun x => 1 - Lc x)) :
    MajF (fun x => 1 / L x) (fun x => 1 / Lc x) := by
  have hP := posCoeff_inv hLc hLc0 hF.2.2.1
  refine ⟨analyticAt_const.div hL (by rw [hL0]; exact one_ne_zero),
    analyticAt_const.div hLc (by rw [hLc0]; exact one_ne_zero), hP, ?_⟩
  have hF0 : coeff (fun x => 1 - L x) 0 = 0 := by
    rw [coeff_zero_eq]
    simp [hL0]
  have hZ0 : (coeff (fun x => 1 - Lc x) 0).re = 0 := by
    rw [coeff_zero_eq]
    simp [hLc0]
  refine sec4_majorant_rules_proved.2.2 _ _ _ _ hF.2.2.2 hF0 hZ0 (coeff_inv_rec hL hL0) (fun n => ?_)
  rw [coeff_inv_rec hLc hLc0 n, Complex.add_re,
    (cmul_re_of_real (fun k => (hF.2.2.1 k).1) (fun k => (hP k).1) n).2]
  split_ifs <;> simp

lemma MajF.geom {ν : ℂ} {νp : ℝ} (hν : ‖ν‖ ≤ νp) :
    MajF (fun x => 1 / (1 - ν * x)) (fun x => 1 / (1 - (νp : ℂ) * x)) := by
  have h1 : MajF (fun x => 1 - (1 - ν * x)) (fun x => 1 - (1 - (νp : ℂ) * x)) :=
    (MajF.ident.smul ν νp hν).congr (Filter.Eventually.of_forall (fun x => by beta_reduce; ring))
      (funext (fun x => by ring))
  exact MajF.inv (L := fun x => 1 - ν * x) (Lc := fun x => 1 - (νp : ℂ) * x)
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp) (by simp) h1

/-! ### The comparison functions -/

/-- `1/(1 - ⅔z)`. -/
noncomputable def iEc (z : ℂ) : ℂ := 1 / (1 - ((2 / 3 : ℝ) : ℂ) * z)

/-- `1/(1 - 2z)`. -/
noncomputable def iFc (z : ℂ) : ℂ := 1 / (1 - ((2 : ℝ) : ℂ) * z)

/-- `1/𝔞 = 1/(1 - ν⁺z)`. -/
noncomputable def iAc (νp : ℝ) (z : ℂ) : ℂ := 1 / (1 - (νp : ℂ) * z)

/-- `1/𝔡 = 1/(1 - ν⁺z - s B₁(z))`, `s = √η⁺`. -/
noncomputable def iDc (νp sp : ℝ) (z : ℂ) : ℂ := 1 / (1 - (νp : ℂ) * z - (sp : ℂ) * B1c z)

/-- `N₊(z) = z(1 + ⅔z)`. -/
noncomputable def NPc (z : ℂ) : ℂ := z * (1 + ((2 / 3 : ℝ) : ℂ) * z)

/-- `Z₁ = N₊ B₁ [1/(𝔞𝔡²) + 1/(𝔞²𝔡)]`. -/
noncomputable def Z1c (νp sp : ℝ) (z : ℂ) : ℂ :=
  NPc z * (B1c z * (iAc νp z * (iDc νp sp z * iDc νp sp z) + iAc νp z * iAc νp z * iDc νp sp z))

/-- `Z₂ = N₊ B₂ [2/(𝔞³𝔡) + 1/(𝔞²𝔡²)]`. -/
noncomputable def Z2c (νp sp : ℝ) (z : ℂ) : ℂ :=
  NPc z * (B2c z * (2 * (iAc νp z * iAc νp z * iAc νp z) * iDc νp sp z +
    iAc νp z * iAc νp z * (iDc νp sp z * iDc νp sp z)))

lemma MajF_iE : MajF iEc iEc := (MajF.geom (ν := ((2 / 3 : ℝ) : ℂ)) (νp := 2 / 3) (by simp)).congr
  (Filter.Eventually.of_forall (fun x => rfl)) rfl

lemma MajF_iF : MajF iFc iFc := (MajF.geom (ν := ((2 : ℝ) : ℂ)) (νp := 2) (by simp)).congr
  (Filter.Eventually.of_forall (fun x => rfl)) rfl

lemma MajF_iA {νp : ℝ} (hν0 : 0 ≤ νp) : MajF (iAc νp) (iAc νp) :=
  (MajF.geom (ν := (νp : ℂ)) (νp := νp) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν0])).congr
    (Filter.Eventually.of_forall (fun x => rfl)) rfl

/-- `B₁(z) = z · z · (16/15)/(1 - 2z)`. -/
lemma B1c_eq : B1c = fun z => z * z * (((16 / 15 : ℝ) : ℂ) * iFc z) := by
  funext z
  simp only [B1c, iFc]
  push_cast
  ring

/-- `B₂(z) = z · z · K(z)`. -/
lemma B2c_eq : B2c = fun z => z * z * (((256 / 243 : ℝ) : ℂ) * (z * z * (iEc z * iEc z)) +
    ((4096 / 3645 : ℝ) : ℂ) * (z * z * z * (iEc z * iEc z * iFc z))) := by
  funext z
  simp only [B2c, iEc, iFc]
  push_cast
  generalize 1 - 2 / 3 * z = A
  generalize 1 - 2 * z = E
  ring

lemma MajF_B1c : MajF B1c B1c := by
  have h := MajF.mul (MajF.mul MajF.ident MajF.ident) (MajF_iF.smul (((16 / 15 : ℝ) : ℂ)) (16 / 15) (by simp))
  rw [← B1c_eq] at h
  exact h

lemma MajF_B2c : MajF B2c B2c := by
  have hE2 := MajF.mul MajF_iE MajF_iE
  have hz2 := MajF.mul MajF.ident MajF.ident
  have hz3 := MajF.mul hz2 MajF.ident
  have hK := MajF.add ((MajF.mul hz2 hE2).smul (((256 / 243 : ℝ) : ℂ)) (256 / 243) (by simp))
    ((MajF.mul hz3 (MajF.mul hE2 MajF_iF)).smul (((4096 / 3645 : ℝ) : ℂ)) (4096 / 3645) (by simp))
  have h := MajF.mul hz2 hK
  rw [← B2c_eq] at h
  exact h

lemma B1c_zero : B1c 0 = 0 := by simp [B1c]

lemma MajF_iD {νp sp : ℝ} (hν0 : 0 ≤ νp) (hs0 : 0 ≤ sp) : MajF (iDc νp sp) (iDc νp sp) := by
  have hL : AnalyticAt ℂ (fun z => 1 - (νp : ℂ) * z - (sp : ℂ) * B1c z) 0 :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).sub (analyticAt_const.mul MajF_B1c.1)
  have h1 : MajF (fun x => 1 - (1 - (νp : ℂ) * x - (sp : ℂ) * B1c x))
      (fun x => 1 - (1 - (νp : ℂ) * x - (sp : ℂ) * B1c x)) := by
    have h := MajF.add (MajF.ident.smul (νp : ℂ) νp
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν0]))
      (MajF_B1c.smul (sp : ℂ) sp (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]))
    exact h.congr (Filter.Eventually.of_forall (fun x => by beta_reduce; ring)) (funext (fun x => by ring))
  exact (MajF.inv hL hL (by simp [B1c_zero]) (by simp [B1c_zero]) h1).congr
    (Filter.Eventually.of_forall (fun x => rfl)) rfl

lemma MajF_NP : MajF NPc NPc :=
  (MajF.mul MajF.ident (MajF.add MajF.one (MajF.ident.smul (((2 / 3 : ℝ) : ℂ)) (2 / 3) (by simp)))).congr
    (Filter.Eventually.of_forall (fun x => rfl)) rfl

lemma MajF_Z1 {νp sp : ℝ} (hν0 : 0 ≤ νp) (hs0 : 0 ≤ sp) : MajF (Z1c νp sp) (Z1c νp sp) := by
  have hA := MajF_iA hν0
  have hD := MajF_iD hν0 hs0
  exact MajF.mul MajF_NP (MajF.mul MajF_B1c (MajF.add (MajF.mul hA (MajF.mul hD hD))
    (MajF.mul (MajF.mul hA hA) hD)))

lemma MajF_Z2 {νp sp : ℝ} (hν0 : 0 ≤ νp) (hs0 : 0 ≤ sp) : MajF (Z2c νp sp) (Z2c νp sp) := by
  have hA := MajF_iA hν0
  have hD := MajF_iD hν0 hs0
  have h2 : MajF (fun z => (2 : ℂ) * (iAc νp z * iAc νp z * iAc νp z))
      (fun z => ((2 : ℝ) : ℂ) * (iAc νp z * iAc νp z * iAc νp z)) :=
    (MajF.mul (MajF.mul hA hA) hA).smul 2 2 (by simp)
  have h2' : MajF (fun z => (2 : ℂ) * (iAc νp z * iAc νp z * iAc νp z))
      (fun z => (2 : ℂ) * (iAc νp z * iAc νp z * iAc νp z)) :=
    h2.congr (Filter.Eventually.of_forall (fun x => rfl)) (funext (fun x => by norm_num))
  exact MajF.mul MajF_NP (MajF.mul MajF_B2c (MajF.add (MajF.mul h2' hD) (MajF.mul (MajF.mul hA hA)
    (MajF.mul hD hD))))

/-! ### Low coefficients -/

lemma coeff_id_low (i : ℕ) (hi : i < 1) : coeff (fun x : ℂ => x) i = 0 := by
  rw [coeff_id_fun, if_neg (show ¬ (i = 1) by omega)]

lemma coeff_sq_low (i : ℕ) (hi : i < 2) : coeff (fun x : ℂ => x * x) i = 0 :=
  coeff_low_mul (f := fun x : ℂ => x) (g := fun x : ℂ => x) analyticAt_id analyticAt_id (p := 1) (q := 1)
    coeff_id_low coeff_id_low i hi

lemma coeff_sqmul_low {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (i : ℕ) (hi : i < 2) :
    coeff (fun x : ℂ => x * x * g x) i = 0 :=
  coeff_low_mul (f := fun x : ℂ => x * x) (g := g) (MajF.mul MajF.ident MajF.ident).1 hg (p := 2) (q := 0)
    coeff_sq_low (fun j hj => absurd hj (Nat.not_lt_zero j)) i (by omega)

lemma B1c_low (i : ℕ) (hi : i < 2) : coeff B1c i = 0 := by
  rw [B1c_eq]
  exact coeff_sqmul_low (analyticAt_const.mul MajF_iF.1) i hi

lemma B2c_low (i : ℕ) (hi : i < 2) : coeff B2c i = 0 := by
  rw [B2c_eq]
  exact coeff_sqmul_low (MajF.add ((MajF.mul (MajF.mul MajF.ident MajF.ident) (MajF.mul MajF_iE MajF_iE)).smul
    (((256 / 243 : ℝ) : ℂ)) (256 / 243) (by simp)) ((MajF.mul (MajF.mul (MajF.mul MajF.ident MajF.ident)
      MajF.ident) (MajF.mul (MajF.mul MajF_iE MajF_iE) MajF_iF)).smul (((4096 / 3645 : ℝ) : ℂ)) (4096 / 3645)
        (by simp))).1 i hi

lemma NPc_low (i : ℕ) (hi : i < 1) : coeff NPc i = 0 := by
  obtain rfl : i = 0 := by omega
  rw [coeff_zero_eq]
  simp [NPc]

/-- The coefficients of `Z₁` and `Z₂` vanish below `x³`. -/
lemma Z1c_low {νp sp : ℝ} (hν0 : 0 ≤ νp) (hs0 : 0 ≤ sp) (i : ℕ) (hi : i < 3) : coeff (Z1c νp sp) i = 0 := by
  have hA := MajF_iA hν0
  have hD := MajF_iD hν0 hs0
  have hS := MajF.add (MajF.mul hA (MajF.mul hD hD)) (MajF.mul (MajF.mul hA hA) hD)
  have hBS := MajF.mul MajF_B1c hS
  exact coeff_low_mul MajF_NP.1 hBS.1 (p := 1) (q := 2) NPc_low
    (fun j hj => coeff_low_mul MajF_B1c.1 hS.1 (p := 2) (q := 0) B1c_low
      (fun k hk => absurd hk (Nat.not_lt_zero k)) j (by omega)) i (by omega)

lemma Z2c_low {νp sp : ℝ} (hν0 : 0 ≤ νp) (hs0 : 0 ≤ sp) (i : ℕ) (hi : i < 3) : coeff (Z2c νp sp) i = 0 := by
  have hA := MajF_iA hν0
  have hD := MajF_iD hν0 hs0
  have h2 : MajF (fun z => (2 : ℂ) * (iAc νp z * iAc νp z * iAc νp z))
      (fun z => ((2 : ℝ) : ℂ) * (iAc νp z * iAc νp z * iAc νp z)) :=
    (MajF.mul (MajF.mul hA hA) hA).smul 2 2 (by simp)
  have hS := MajF.add (MajF.mul h2 hD) (MajF.mul (MajF.mul hA hA) (MajF.mul hD hD))
  have hBS := MajF.mul MajF_B2c hS
  exact coeff_low_mul MajF_NP.1 hBS.1 (p := 1) (q := 2) NPc_low
    (fun j hj => coeff_low_mul MajF_B2c.1 hS.1 (p := 2) (q := 0) B2c_low
      (fun k hk => absurd hk (Nat.not_lt_zero k)) j (by omega)) i (by omega)

lemma coeff_subC {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (fun x => f x - g x) n = coeff f n - coeff g n := by
  unfold coeff
  rw [show (fun x => f x - g x) = f - g from rfl, iteratedDeriv_sub hf.contDiffAt hg.contDiffAt, sub_div]

lemma coeff_zero_of_maj {F : ℕ → ℂ} {Z : ℕ → ℝ} (h : Majorizes F Z) {n : ℕ} (hz : Z n = 0) : F n = 0 :=
  norm_le_zero_iff.mp ((h n).trans (le_of_eq hz))

lemma MajF.of_smul_maj {f Z : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hZ : MajF Z Z) (s : ℝ) (hs : 0 ≤ s)
    (h : Majorizes (coeff f) (fun n => s * (coeff Z n).re)) : MajF f (fun z => (s : ℂ) * Z z) := by
  obtain ⟨-, hZa, hZp, -⟩ := hZ.smul (s : ℂ) s (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs])
  refine ⟨hf, hZa, hZp, fun n => ?_⟩
  show ‖coeff f n‖ ≤ (coeff (fun z => (s : ℂ) * Z z) n).re
  rw [coeff_smulC, Complex.re_ofReal_mul]
  exact h n

lemma MajF.to_maj {f Z : ℂ → ℂ} {s : ℝ} (h : MajF f (fun z => (s : ℂ) * Z z)) :
    Majorizes (coeff f) (fun n => s * (coeff Z n).re) := fun n => by
  have h3 : ‖coeff f n‖ ≤ (coeff (fun z => (s : ℂ) * Z z) n).re := h.2.2.2 n
  rw [coeff_smulC, Complex.re_ofReal_mul] at h3
  exact h3

/-! ### The functions of Lemma 4.6 -/

lemma Bser_eq' {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    Bser τ φ ξ = (1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ) - 1 + nuτ τ (cOf f τ) * ξ := by
  have h := Lfun_eq hf h1 h2 hφ hξ
  simp only [Lfun] at h
  linear_combination h

lemma Bser_differentiableOn {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) : DifferentiableOn ℂ (Bser τ φ) (ball (0 : ℂ) (1 / 4)) := by
  have hd : DifferentiableOn ℂ (fun ξ => (1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ) - 1 + nuτ τ (cOf f τ) * ξ)
      (ball (0 : ℂ) (1 / 4)) := by
    intro ξ hξ
    have hw : wmap τ ξ ∈ ball (0 : ℂ) 1 := w_mem_ball h1 h2 hξ
    have hφd : DifferentiableAt ℂ φ (wmap τ ξ) := hφ.1.differentiableAt (isOpen_ball.mem_nhds hw)
    have hwd : DifferentiableAt ℂ (wmap τ) ξ := (hasDerivAt_wmap h1 h2 hξ).differentiableAt
    have hcomp : DifferentiableAt ℂ (fun ξ => φ (wmap τ ξ)) ξ := hφd.comp ξ hwd
    have h : DifferentiableAt ℂ (fun ξ => (1 + (βτ τ : ℂ) * ξ) * φ (wmap τ ξ) - 1 + nuτ τ (cOf f τ) * ξ) ξ := by
      fun_prop
    exact h.differentiableWithinAt
  exact hd.congr (fun ξ hξ => Bser_eq' hf h1 h2 hφ hξ)

/-- `Π̇ = -2NB/(1 - νξ)³`. -/
noncomputable def Pdf (τ : ℝ) (c : ℂ) (φ : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  -2 * Nfun τ ξ * Bser τ φ ξ / (1 - nuτ τ c * ξ) ^ 3

/-- `Π - Π̂ = -NB(1/(aL²) + 1/(a²L))` on `|ξ| < 1/4`. -/
lemma D1_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) (hc : ‖cOf f τ‖ ≤ 1) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    PiF f τ ξ - Pihat τ (cOf f τ) ξ = -(Nfun τ ξ * (Bser τ φ ξ * (1 / (1 - nuτ τ (cOf f τ) * ξ) *
      (1 / Lfun τ (cOf f τ) φ ξ * (1 / Lfun τ (cOf f τ) φ ξ)) +
      1 / (1 - nuτ τ (cOf f τ) * ξ) * (1 / (1 - nuτ τ (cOf f τ) * ξ)) * (1 / Lfun τ (cOf f τ) φ ξ)))) := by
  have hPL := (sec4_Pi_formula_proved f hf τ h1 h2 φ hφ).2.2.1 ξ hξ
  have ha := one_sub_nu_ne h1 h2 hc (quarter_sub_half hξ)
  have hL := Lfun_ne_zero hf h1 h2 hφ hξ
  have hP : PiF f τ ξ = Nfun τ ξ / Lfun τ (cOf f τ) φ ξ ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hL)]
    exact hPL
  rw [hP]
  simp only [Pihat, Lfun] at hL ⊢
  rw [show ξ * (1 + (βτ τ : ℂ) * ξ) = Nfun τ ξ from rfl]
  generalize 1 - nuτ τ (cOf f τ) * ξ = a at ha hL ⊢
  generalize Bser τ φ ξ = B at hL ⊢
  generalize Nfun τ ξ = N
  field_simp
  ring

/-- `Π - Π̂ - Π̇ = NB²(2/(a³L) + 1/(a²L²))` on `|ξ| < 1/4`. -/
lemma D2_eq {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) (hc : ‖cOf f τ‖ ≤ 1) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) (1 / 4)) :
    PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ = Nfun τ ξ * (Bser τ φ ξ ^ 2 *
      (2 * (1 / (1 - nuτ τ (cOf f τ) * ξ) * (1 / (1 - nuτ τ (cOf f τ) * ξ)) * (1 / (1 - nuτ τ (cOf f τ) * ξ))) *
        (1 / Lfun τ (cOf f τ) φ ξ) +
      1 / (1 - nuτ τ (cOf f τ) * ξ) * (1 / (1 - nuτ τ (cOf f τ) * ξ)) *
        (1 / Lfun τ (cOf f τ) φ ξ * (1 / Lfun τ (cOf f τ) φ ξ)))) := by
  have hPL := (sec4_Pi_formula_proved f hf τ h1 h2 φ hφ).2.2.1 ξ hξ
  have ha := one_sub_nu_ne h1 h2 hc (quarter_sub_half hξ)
  have hL := Lfun_ne_zero hf h1 h2 hφ hξ
  have hP : PiF f τ ξ = Nfun τ ξ / Lfun τ (cOf f τ) φ ξ ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hL)]
    exact hPL
  rw [hP]
  simp only [Pihat, Pdf, Lfun] at hL ⊢
  rw [show ξ * (1 + (βτ τ : ℂ) * ξ) = Nfun τ ξ from rfl]
  generalize 1 - nuτ τ (cOf f τ) * ξ = a at ha hL ⊢
  generalize Bser τ φ ξ = B at hL ⊢
  generalize Nfun τ ξ = N
  field_simp
  ring

lemma MajF_N {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) : MajF (Nfun τ) NPc := by
  obtain ⟨hb0, hb1⟩ := beta_bounds h1 h2
  have h := MajF.mul MajF.ident (MajF.add MajF.one (MajF.ident.smul (βτ τ : ℂ) (2 / 3)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; exact hb1)))
  exact h.congr (Filter.Eventually.of_forall (fun x => rfl)) rfl

lemma MajF_ia {ν : ℂ} {νp : ℝ} (hν : ‖ν‖ ≤ νp) : MajF (fun ξ => 1 / (1 - ν * ξ)) (iAc νp) :=
  (MajF.geom hν).congr (Filter.Eventually.of_forall (fun x => rfl)) rfl

lemma MajF_iL {τ : ℝ} {c : ℂ} {φ : ℂ → ℂ} {νp sη sp : ℝ} (hBa : AnalyticAt ℂ (Bser τ φ) 0)
    (hB : MajF (Bser τ φ) (fun z => (sη : ℂ) * B1c z)) (hsη0 : 0 ≤ sη) (hsp : sη ≤ sp)
    (hν : ‖nuτ τ c‖ ≤ νp) (hB0 : Bser τ φ 0 = 0) : MajF (fun ξ => 1 / Lfun τ c φ ξ) (iDc νp sp) := by
  have hsp0 : 0 ≤ sp := hsη0.trans hsp
  obtain ⟨-, hZa, hZp, -⟩ := MajF_B1c.smul (sp : ℂ) sp
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsp0])
  have hBm : MajF (fun ξ => -Bser τ φ ξ) (fun z => (sp : ℂ) * B1c z) :=
    hB.neg.mono hZa hZp (fun n => by
      rw [coeff_smulC, coeff_smulC, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_right hsp (MajF_B1c.2.2.1 n).2)
  have hF : MajF (fun x => 1 - Lfun τ c φ x) (fun x => 1 - (1 - (νp : ℂ) * x - (sp : ℂ) * B1c x)) :=
    (MajF.add (MajF.ident.smul (nuτ τ c) νp hν) hBm).congr
      (Filter.Eventually.of_forall (fun x => by simp only [Lfun]; ring)) (funext (fun x => by ring))
  have hL : AnalyticAt ℂ (Lfun τ c φ) 0 := by
    have h : AnalyticAt ℂ (fun x => 1 - nuτ τ c * x + Bser τ φ x) 0 :=
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).add hBa
    exact h
  have hLc : AnalyticAt ℂ (fun z => 1 - (νp : ℂ) * z - (sp : ℂ) * B1c z) 0 :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).sub (analyticAt_const.mul MajF_B1c.1)
  exact (MajF.inv hL hLc (by simp [Lfun, hB0]) (by simp [B1c_zero]) hF).congr
    (Filter.Eventually.of_forall (fun x => rfl)) rfl

/-! ### Majorants of `Π - Π̂` and `Π - Π̂ - Π̇` -/

lemma MajF_D1 {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) (hc : ‖cOf f τ‖ ≤ 1) {νp sη sp : ℝ} (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp)
    (hB : MajF (Bser τ φ) (fun z => (sη : ℂ) * B1c z))
    (hiL : MajF (fun ξ => 1 / Lfun τ (cOf f τ) φ ξ) (iDc νp sp)) :
    MajF (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ) (fun z => (sη : ℂ) * Z1c νp sp z) := by
  have hN := MajF_N h1 h2
  have hia := MajF_ia hν
  have h := MajF.neg (MajF.mul hN (MajF.mul hB (MajF.add (MajF.mul hia (MajF.mul hiL hiL))
    (MajF.mul (MajF.mul hia hia) hiL))))
  refine h.congr ?_ ?_
  · exact Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4))
      (fun ξ hξ => (D1_eq hf h1 h2 hφ hc hξ).symm)
  · funext z
    simp only [Z1c]
    ring

lemma MajF_D2 {f : ℂ → ℂ} (hf : InS f) {τ : ℝ} (h1 : 9 / 20 ≤ τ) (h2 : τ < 1 / 2) {φ : ℂ → ℂ}
    (hφ : IsSqrtQuot (fT f τ) φ) (hc : ‖cOf f τ‖ ≤ 1) {νp η sp : ℝ} (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp)
    (hBB : MajF (fun ξ => Bser τ φ ξ ^ 2) (fun z => (η : ℂ) * B2c z))
    (hiL : MajF (fun ξ => 1 / Lfun τ (cOf f τ) φ ξ) (iDc νp sp)) :
    MajF (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ) (fun z => (η : ℂ) * Z2c νp sp z) := by
  have hN := MajF_N h1 h2
  have hia := MajF_ia hν
  have h2a := (MajF.mul (MajF.mul hia hia) hia).smul 2 2 (by simp)
  have h := MajF.mul hN (MajF.mul hBB (MajF.add (MajF.mul h2a hiL) (MajF.mul (MajF.mul hia hia)
    (MajF.mul hiL hiL))))
  refine h.congr ?_ ?_
  · exact Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4))
      (fun ξ hξ => (D2_eq hf h1 h2 hφ hc hξ).symm)
  · funext z
    simp only [Z2c]
    push_cast
    ring

/-! ### The comparison functions on the real line -/

lemma one_sub_ne_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hw
  exact lt_irrefl _ hw

lemma den_facts {νp sp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (hs0 : 0 ≤ sp) (hs1 : sp ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1 / 4) :
    1 - 2 * z ≠ 0 ∧ 1 - 2 / 3 * z ≠ 0 ∧ 1 - (νp : ℂ) * z ≠ 0 ∧ 1 - (νp : ℂ) * z - (sp : ℂ) * B1c z ≠ 0 := by
  have hz0 := norm_nonneg z
  have hE : 1 - 2 * z ≠ 0 := one_sub_ne_of_norm_lt (by rw [norm_mul]; norm_num; linarith)
  have hEn : 1 / 2 ≤ ‖1 - 2 * z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (2 * z)
    rw [norm_one, norm_mul] at this
    norm_num at this
    linarith
  have hB1 : ‖B1c z‖ ≤ 2 / 15 := by
    have e : ‖B1c z‖ = 16 / 15 * (‖z‖ ^ 2 / ‖1 - 2 * z‖) := by
      simp only [B1c]
      rw [norm_mul, norm_div (z ^ 2), norm_pow]
      norm_num
    rw [e]
    have hq : ‖z‖ ^ 2 / ‖1 - 2 * z‖ ≤ (1 / 16) / (1 / 2) :=
      div_le_div₀ (by norm_num) (by nlinarith) (by norm_num) hEn
    nlinarith
  refine ⟨hE, one_sub_ne_of_norm_lt (by rw [norm_mul]; norm_num; linarith),
    one_sub_ne_of_norm_lt (by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν0]; nlinarith), ?_⟩
  rw [show 1 - (νp : ℂ) * z - (sp : ℂ) * B1c z = 1 - ((νp : ℂ) * z + (sp : ℂ) * B1c z) by ring]
  apply one_sub_ne_of_norm_lt
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hν0, abs_of_nonneg hs0]
  nlinarith [norm_nonneg (B1c z)]

lemma B1c_dAt {z : ℂ} (hE : 1 - 2 * z ≠ 0) : DifferentiableAt ℂ B1c z := by
  unfold B1c
  fun_prop (disch := assumption)

lemma B2c_dAt {z : ℂ} (hE : 1 - 2 * z ≠ 0) (hF : 1 - 2 / 3 * z ≠ 0) : DifferentiableAt ℂ B2c z := by
  have hF2 : (1 - 2 / 3 * z) ^ 2 ≠ 0 := pow_ne_zero 2 hF
  have hFE : (1 - 2 / 3 * z) ^ 2 * (1 - 2 * z) ≠ 0 := mul_ne_zero hF2 hE
  unfold B2c
  fun_prop (disch := assumption)

lemma iAc_dAt {νp : ℝ} {z : ℂ} (hA : 1 - (νp : ℂ) * z ≠ 0) : DifferentiableAt ℂ (iAc νp) z := by
  unfold iAc
  fun_prop (disch := assumption)

lemma iDc_dAt {νp sp : ℝ} {z : ℂ} (hE : 1 - 2 * z ≠ 0) (hD : 1 - (νp : ℂ) * z - (sp : ℂ) * B1c z ≠ 0) :
    DifferentiableAt ℂ (iDc νp sp) z := by
  have hB := B1c_dAt hE
  unfold iDc
  fun_prop (disch := assumption)

lemma Z1c_diff {νp sp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (hs0 : 0 ≤ sp) (hs1 : sp ≤ 1) :
    DifferentiableOn ℂ (Z1c νp sp) (ball (0 : ℂ) (1 / 4)) := by
  intro z hz
  obtain ⟨hE, -, hA, hD⟩ := den_facts hν0 hν2 hs0 hs1 (mem_ball_zero_iff.mp hz)
  have h1 := B1c_dAt hE
  have h2 := iAc_dAt hA
  have h3 := iDc_dAt hE hD
  have h : DifferentiableAt ℂ (Z1c νp sp) z := by
    unfold Z1c NPc
    fun_prop
  exact h.differentiableWithinAt

lemma Z2c_diff {νp sp : ℝ} (hν0 : 0 ≤ νp) (hν2 : νp ≤ 2) (hs0 : 0 ≤ sp) (hs1 : sp ≤ 1) :
    DifferentiableOn ℂ (Z2c νp sp) (ball (0 : ℂ) (1 / 4)) := by
  intro z hz
  obtain ⟨hE, hF, hA, hD⟩ := den_facts hν0 hν2 hs0 hs1 (mem_ball_zero_iff.mp hz)
  have h1 := B2c_dAt hE hF
  have h2 := iAc_dAt hA
  have h3 := iDc_dAt hE hD
  have h : DifferentiableAt ℂ (Z2c νp sp) z := by
    unfold Z2c NPc
    fun_prop
  exact h.differentiableWithinAt

lemma Z1c_real (νp ηp x : ℝ) : Z1c νp (Real.sqrt ηp) (x : ℂ) = ((Z1Of νp ηp x : ℝ) : ℂ) := by
  simp only [Z1c, NPc, iAc, iDc, B1c, Z1Of, Nplus, B1, faOf, fdOf]
  push_cast
  generalize (1 - 2 * (x : ℂ)) = E
  generalize (1 - (νp : ℂ) * (x : ℂ)) = A
  generalize A - (Real.sqrt ηp : ℂ) * (16 / 15 * ((x : ℂ) ^ 2 / E)) = D
  ring

lemma Z2c_real (νp ηp x : ℝ) : Z2c νp (Real.sqrt ηp) (x : ℂ) = ((Z2Of νp ηp x : ℝ) : ℂ) := by
  simp only [Z2c, NPc, iAc, iDc, B1c, B2c, Z2Of, Nplus, B1, B2, faOf, fdOf]
  push_cast
  generalize (1 - 2 * (x : ℂ)) = E
  generalize (1 - 2 / 3 * (x : ℂ)) = F
  generalize (1 - (νp : ℂ) * (x : ℂ)) = A
  generalize A - (Real.sqrt ηp : ℂ) * (16 / 15 * ((x : ℂ) ^ 2 / E)) = D
  ring

lemma real_link {Zc : ℂ → ℂ} {Zr : ℝ → ℝ} (hd : DifferentiableOn ℂ Zc (ball (0 : ℂ) (1 / 4)))
    (hreal : ∀ x : ℝ, Zc (x : ℂ) = (Zr x : ℂ)) (x : ℝ) (hx : |x| < 1 / 4) :
    HasSum (fun n => (coeff Zc n).re * x ^ n) (Zr x) := by
  have hxb : (x : ℂ) ∈ ball (0 : ℂ) (1 / 4) := by
    rwa [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
  have h := Complex.hasSum_re (hasSum_coeff hd hxb)
  rw [hreal x, Complex.ofReal_re] at h
  refine h.congr_fun (fun n => ?_)
  rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]

lemma hCoef_smul (s : ℝ) (Z : ℕ → ℝ) (x : ℝ) : hCoef (fun n => s * Z n) x = s * hCoef Z x := by
  unfold hCoef
  rw [← tsum_mul_left]
  congr 1
  funext j
  split_ifs <;> ring

lemma wCoef_smul (s : ℝ) (Z : ℕ → ℝ) (x : ℝ) : wCoef (fun n => s * Z n) x = s * wCoef Z x := by
  unfold wCoef
  rw [← tsum_mul_left]
  congr 1
  funext j
  split_ifs <;> ring

/-- The two comparison series: nonnegative, vanishing below `x³`, summing to `Z₁`/`Z₂` on `|x| < 1/4`,
and their `𝔥`, `𝔴` at `y₀`. -/
lemma Zc_facts {Zc : ℂ → ℂ} {Zr : ℝ → ℝ} (hM : MajF Zc Zc) (hlow : ∀ i, i < 3 → coeff Zc i = 0)
    (hd : DifferentiableOn ℂ Zc (ball (0 : ℂ) (1 / 4))) (hreal : ∀ x : ℝ, Zc (x : ℂ) = (Zr x : ℂ)) :
    (∀ n, 0 ≤ (coeff Zc n).re) ∧ (∀ n, n ≤ 2 → (coeff Zc n).re = 0) ∧
      (∀ y : ℝ, 0 ≤ y → y < 6 / 25 → Summable (fun n : ℕ => ((n : ℝ) + 1) * (coeff Zc n).re * y ^ n)) ∧
      frakH Zr = hCoef (fun n => (coeff Zc n).re) y0 ∧ frakW Zr = wCoef (fun n => (coeff Zc n).re) y0 := by
  have h0 : ∀ n, 0 ≤ (coeff Zc n).re := fun n => (hM.2.2.1 n).2
  have hl : ∀ n, n ≤ 2 → (coeff Zc n).re = 0 := fun n hn => by rw [hlow n (by omega)]; simp
  have hs := (real_link hd hreal (6 / 25) (by norm_num)).summable
  obtain ⟨hlink, -, -⟩ := sec4_hw_coeff_proved (fun n => (coeff Zc n).re) h0 (hl 1 (by norm_num))
    (hl 2 le_rfl) Zr (1 / 4) (by norm_num) (fun x hx => real_link hd hreal x hx)
  obtain ⟨hH, hW⟩ := hlink y0 y0_pos (by norm_num [y0])
  exact ⟨h0, hl, fun y hy hy1 => summable_succ_mul h0 hy hy1 hs, hH, hW⟩

lemma epsOf_mono {y : ℝ} (hy : 0 < y) (hyy : y ≤ y0) : epsOf y ≤ epsOf y0 := by
  unfold epsOf
  have hy2 : y ^ 2 ≤ y0 ^ 2 := pow_le_pow_left₀ hy.le hyy 2
  have hy02 : y0 ^ 2 = 289 / 6400 := by norm_num [y0]
  have h1 : 0 < 1 - 4 * y0 ^ 2 := by rw [hy02]; norm_num
  have h2 : 1 - 4 * y0 ^ 2 ≤ 1 - 4 * y ^ 2 := by linarith
  have h3 := pow_le_pow_left₀ h1.le h2 2
  apply add_le_add
  · exact div_le_div₀ (by positivity) (by linarith) (mul_pos (by norm_num) (pow_pos h1 2)) (by linarith)
  · exact div_le_div₀ (by positivity) (by linarith) h1 h2

lemma hCoef_mono_y {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) {y : ℝ} (hy : 0 < y) (hyy : y ≤ y0)
    (hs : ∀ x : ℝ, 0 ≤ x → x < 6 / 25 → Summable (fun n : ℕ => ((n : ℝ) + 1) * Z n * x ^ n)) :
    hCoef Z y ≤ hCoef Z y0 ∧ wCoef Z y ≤ wCoef Z y0 := by
  have hy1 : y < 6 / 25 := lt_of_le_of_lt hyy (by norm_num [y0])
  have hy01 : y0 < 6 / 25 := by norm_num [y0]
  exact ⟨hasSum_le (fun i => hTerm_mono_x hZ hy.le hyy i) (summable_hTerm hZ hy (hs y hy.le hy1)).hasSum
      (summable_hTerm hZ y0_pos (hs y0 y0_pos.le hy01)).hasSum,
    hasSum_le (fun i => wTerm_mono_x hZ hy.le hyy i) (summable_wTerm hZ hy (hs y hy.le hy1)).hasSum
      (summable_wTerm hZ y0_pos (hs y0 y0_pos.le hy01)).hasSum⟩

lemma hCoef_nonneg {Z : ℕ → ℝ} (hZ : ∀ n, 0 ≤ Z n) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ hCoef Z x := by
  unfold hCoef
  refine tsum_nonneg (fun j => ?_)
  split_ifs
  · exact mul_nonneg (hZ _) (pow_nonneg hx _)
  · exact le_rfl

/-! ### Lemma 4.6 -/

theorem lem_4_6_proved_from
    (hII : ∀ (_ : FactDeBranges) (f : ℂ → ℂ) (_ : InS f) (τ : ℝ) (_ : 9 / 20 ≤ τ) (_ : τ ≤ 1 / 2) (y : ℝ)
      (_ : 0 < y) (_ : y ≤ y0), ‖PiOddSer (coeff (PiF f τ)) (I * (y : ℂ)) - 1‖ ≤ epsOf y)
    (hIII : ∀ (_ : FactArea) (f : ℂ → ℂ) (_ : InS f) (τ : ℝ) (_ : 9 / 20 ≤ τ) (_ : τ ≤ 1 / 2) (φ : ℂ → ℂ)
      (_ : IsSqrtQuot (fT f τ) φ),
      Majorizes (coeff (Bser τ φ)) (fun n => Real.sqrt (etadef (cOf f τ)) * (coeff B1c n).re) ∧
        Majorizes (coeff (fun ξ => Bser τ φ ξ ^ 2)) (fun n => etadef (cOf f τ) * (coeff B2c n).re))
    (hV : ∀ (_ : FactArea) (f : ℂ → ℂ) (_ : InS f) (τ : ℝ) (_ : 9 / 20 ≤ τ) (_ : τ < 1 / 2)
      (_ : yτ τ ≤ y0) (φ : ℂ → ℂ) (_ : IsSqrtQuot (fT f τ) φ) (νp : ℝ) (_ : ‖nuτ τ (cOf f τ)‖ ≤ νp)
      (_ : νp ≤ 2), ‖Tdot τ (cOf f τ) φ‖ ≤
        Real.sqrt (etadef (cOf f τ)) * Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)))
    (hDB : FactDeBranges) (hArea : FactArea) (f : ℂ → ℂ) (hf : InS f) (τ : ℝ) (h1 : 9 / 20 ≤ τ)
    (h2 : τ ≤ 1 / 2) (hy : 0 < yτ τ) (hy0 : yτ τ ≤ y0) (φ : ℂ → ℂ) (hφ : IsSqrtQuot (fT f τ) φ)
    (νp ηp np : ℝ) (hν : ‖nuτ τ (cOf f τ)‖ ≤ νp) (hνp : νp ≤ 2) (hη : etadef (cOf f τ) ≤ ηp) (hηp : ηp ≤ 1)
    (hn : Real.sqrt (20 + N6Of νp ^ 2 + 130 * edef (cOf f τ)) ≤ np) :
    PiLowOf νp ηp ≤ ‖PiOddSer (coeff (PiF f τ)) (xiτ τ)‖ ∧
      (0 < PiLowOf νp ηp →
        ‖Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ‖ ≤
          etadef (cOf f τ) * LamOf νp ηp np) := by
  /- basic facts -/
  have h2' : τ < 1 / 2 := by
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exfalso
      rw [h] at hy
      norm_num [yτ, ysq] at hy
  have hc := cOf_norm_le hDB hf h1 h2'
  have hν0 : 0 ≤ νp := (norm_nonneg _).trans hν
  have hη0 : 0 ≤ etadef (cOf f τ) := by
    unfold etadef
    nlinarith [norm_nonneg (cOf f τ)]
  have hsη0 : 0 ≤ Real.sqrt (etadef (cOf f τ)) := Real.sqrt_nonneg _
  have hsp : Real.sqrt (etadef (cOf f τ)) ≤ Real.sqrt ηp := Real.sqrt_le_sqrt hη
  have hsp0 : 0 ≤ Real.sqrt ηp := Real.sqrt_nonneg _
  have hsp1 : Real.sqrt ηp ≤ 1 := (Real.sqrt_le_sqrt hηp).trans_eq Real.sqrt_one
  have hsq : Real.sqrt (etadef (cOf f τ)) * Real.sqrt (etadef (cOf f τ)) = etadef (cOf f τ) :=
    Real.mul_self_sqrt hη0
  have hnp0 : 0 ≤ np := (Real.sqrt_nonneg _).trans hn
  obtain ⟨hTp, hPl⟩ := lem_4_4_iv_proved τ h1 h2 hy hy0 (cOf f τ) hc νp hν hνp
  have hT0 : 0 ≤ TPlusOf νp := (norm_nonneg _).trans hTp
  have hPho : PihatO τ (cOf f τ) ≠ 0 := norm_pos_iff.mp ((PihatLow_pos νp).trans_le hPl)
  /- the majorants of `Π - Π̂` and `Π - Π̂ - Π̇` -/
  obtain ⟨hB1, hB2⟩ := hIII hArea f hf τ h1 h2 φ hφ
  have hBd := Bser_differentiableOn hf h1 h2' hφ
  have hBa : AnalyticAt ℂ (Bser τ φ) 0 := hBd.analyticAt (ball_mem_nhds 0 (by norm_num))
  have hB := MajF.of_smul_maj hBa MajF_B1c _ hsη0 hB1
  have hBB := MajF.of_smul_maj (hBa.pow 2) MajF_B2c _ hη0 hB2
  have hB0 : Bser τ φ 0 = 0 := by
    rw [← coeff_zero_eq (Bser τ φ)]
    exact coeff_zero_of_maj hB1 (by beta_reduce; rw [coeff_zero_eq, B1c_zero]; simp)
  have hiL := MajF_iL hBa hB hsη0 hsp hν hB0
  have hM1 := (MajF_D1 hf h1 h2' hφ hc hν hB hiL).to_maj
  have hM2 := (MajF_D2 hf h1 h2' hφ hc hν hBB hiL).to_maj
  obtain ⟨hZ1n, hZ1l, hZ1s, hH1, -⟩ := Zc_facts (MajF_Z1 hν0 hsp0) (Z1c_low hν0 hsp0)
    (Z1c_diff hν0 hνp hsp0 hsp1) (Z1c_real νp ηp)
  obtain ⟨hZ2n, hZ2l, hZ2s, hH2, hW2⟩ := Zc_facts (MajF_Z2 hν0 hsp0) (Z2c_low hν0 hsp0)
    (Z2c_diff hν0 hνp hsp0 hsp1) (Z2c_real νp ηp)
  have hdp1 : ∀ n, n ≤ 2 → coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ) n = 0 := fun n hn =>
    coeff_zero_of_maj hM1 (by beta_reduce; rw [hZ1l n hn, mul_zero])
  have hdp2 : ∀ n, n ≤ 2 →
      coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ) n = 0 := fun n hn =>
    coeff_zero_of_maj hM2 (by beta_reduce; rw [hZ2l n hn, mul_zero])
  have hy1 : yτ τ < 6 / 25 := lt_of_le_of_lt hy0 (by norm_num [y0])
  have hZs1 : Summable (fun n : ℕ => ((n : ℝ) + 1) *
      (Real.sqrt (etadef (cOf f τ)) * (coeff (Z1c νp (Real.sqrt ηp)) n).re) * yτ τ ^ n) :=
    ((hZ1s (yτ τ) hy.le hy1).mul_left (Real.sqrt (etadef (cOf f τ)))).congr (fun n => by ring)
  have hZs2 : Summable (fun n : ℕ => ((n : ℝ) + 1) *
      (etadef (cOf f τ) * (coeff (Z2c νp (Real.sqrt ηp)) n).re) * yτ τ ^ n) :=
    ((hZ2s (yτ τ) hy.le hy1).mul_left (etadef (cOf f τ))).congr (fun n => by ring)
  obtain ⟨hP1, -⟩ := lem_4_4_i_proved τ h1 h2 (yτ τ) hy hy0 (cOf f τ) hc _ _ hdp1 hM1 hZs1
  obtain ⟨hP2, hU2⟩ := lem_4_4_i_proved τ h1 h2 (yτ τ) hy hy0 (cOf f τ) hc _ _ hdp2 hM2 hZs2
  obtain ⟨hm1h, -⟩ := hCoef_mono_y hZ1n hy hy0 hZ1s
  obtain ⟨hm2h, hm2w⟩ := hCoef_mono_y hZ2n hy hy0 hZ2s
  have hxi : xiτ τ = I * ((yτ τ : ℝ) : ℂ) := rfl
  have hR1n : ‖PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ)) (xiτ τ)‖ ≤
      Real.sqrt (etadef (cOf f τ)) * frakH (Z1Of νp ηp) := by
    rw [hxi, hH1]
    refine hP1.trans ?_
    rw [hCoef_smul]
    exact mul_le_mul_of_nonneg_left hm1h hsη0
  have hR2n : ‖PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ)‖ ≤
      etadef (cOf f τ) * frakH (Z2Of νp ηp) := by
    rw [hxi, hH2]
    refine hP2.trans ?_
    rw [hCoef_smul]
    exact mul_le_mul_of_nonneg_left hm2h hη0
  have hU2n : ‖UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ))
      (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ)‖ ≤
      etadef (cOf f τ) * frakW (Z2Of νp ηp) := by
    rw [hxi, hW2]
    refine hU2.trans ?_
    rw [wCoef_smul]
    exact mul_le_mul_of_nonneg_left hm2w hη0
  /- function values at `±ξ₀` -/
  obtain ⟨hξ0, hξ, -⟩ := xi_facts h1 h2'
  have hξm := neg_mem_ball_zero hξ
  have dF := PiF_differentiableOn hf h1 h2'
  have dH : DifferentiableOn ℂ (Pihat τ (cOf f τ)) (ball (0 : ℂ) (1 / 4)) :=
    (Pihat_differentiableOn h1 h2' hc).mono (ball_subset_ball (by norm_num))
  have dPd : DifferentiableOn ℂ (Pdf τ (cOf f τ) φ) (ball (0 : ℂ) (1 / 4)) := by
    intro ξ hξ'
    have hBdx := (hBd ξ hξ').differentiableAt (isOpen_ball.mem_nhds hξ')
    have ha := pow_ne_zero 3 (one_sub_nu_ne h1 h2' hc (quarter_sub_half hξ'))
    have h : DifferentiableAt ℂ (Pdf τ (cOf f τ) φ) ξ := by
      unfold Pdf Nfun
      fun_prop (disch := exact ha)
    exact h.differentiableWithinAt
  have d1 : DifferentiableOn ℂ (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ) (ball (0 : ℂ) (1 / 4)) := dF.sub dH
  have d2 : DifferentiableOn ℂ (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)
      (ball (0 : ℂ) (1 / 4)) := d1.sub dPd
  have eF := (PiOddSer_eq dF hξ hξ0).2
  have eH := (PiOddSer_eq dH hξ hξ0).2
  have eP := (PiOddSer_eq dPd hξ hξ0).2
  have e1 := (PiOddSer_eq d1 hξ hξ0).2
  have e2 := (PiOddSer_eq d2 hξ hξ0).2
  have hR1 : PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ)) (xiτ τ) =
      PiOddSer (coeff (PiF f τ)) (xiτ τ) - PiOddSer (coeff (Pihat τ (cOf f τ))) (xiτ τ) := by
    rw [e1, eF, eH]
    ring
  have hR2 : PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ) =
      PiOddSer (coeff (PiF f τ)) (xiτ τ) - PiOddSer (coeff (Pihat τ (cOf f τ))) (xiτ τ) -
        PiOddSer (coeff (Pdf τ (cOf f τ) φ)) (xiτ τ) := by
    rw [e2, eF, eH, eP]
    ring
  /- part (a): the lower bound for `|Π_o(iy)|` -/
  obtain ⟨-, -, hO, hTh, -⟩ := sec4_hat_closed_proved τ h1 h2' (cOf f τ) hc
  have hPiLow : PiLowOf νp ηp ≤ ‖PiOddSer (coeff (PiF f τ)) (xiτ τ)‖ := by
    unfold PiLowOf
    refine max_le ?_ ?_
    · have hII' := hII hDB f hf τ h1 h2 (yτ τ) hy hy0
      rw [← hxi] at hII'
      have hm := epsOf_mono hy hy0
      have h3 := norm_sub_norm_le (1 : ℂ) (PiOddSer (coeff (PiF f τ)) (xiτ τ))
      rw [norm_one, norm_sub_rev] at h3
      unfold epsY0
      linarith
    · have h3 := norm_sub_norm_le (PiOddSer (coeff (Pihat τ (cOf f τ))) (xiτ τ))
        (PiOddSer (coeff (PiF f τ)) (xiτ τ))
      rw [norm_sub_rev, ← hR1, hO] at h3
      have h4 : Real.sqrt (etadef (cOf f τ)) * frakH (Z1Of νp ηp) ≤ Real.sqrt ηp * frakH (Z1Of νp ηp) :=
        mul_le_mul_of_nonneg_right hsp (by rw [hH1]; exact hCoef_nonneg hZ1n y0 y0_pos.le)
      linarith
  refine ⟨hPiLow, fun hPL => ?_⟩
  /- part (b): `T - T̂ - Ṫ` -/
  have hPo0 : PiOddSer (coeff (PiF f τ)) (xiτ τ) ≠ 0 := norm_pos_iff.mp (hPL.trans_le hPiLow)
  obtain ⟨-, hp1, hp2⟩ := Pihat_low_coeffs h1 h2' (cOf f τ)
  have hF1 := PiF_coeff_one hf h1 h2'
  have hF2 := PiF_coeff_two hf h1 h2'
  have aF : AnalyticAt ℂ (PiF f τ) 0 := dF.analyticAt (ball_mem_nhds 0 (by norm_num))
  have aH : AnalyticAt ℂ (Pihat τ (cOf f τ)) 0 := dH.analyticAt (ball_mem_nhds 0 (by norm_num))
  have a1 : AnalyticAt ℂ (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ) 0 :=
    d1.analyticAt (ball_mem_nhds 0 (by norm_num))
  have a2 : AnalyticAt ℂ (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ) 0 :=
    d2.analyticAt (ball_mem_nhds 0 (by norm_num))
  have hPdeq : Pdf τ (cOf f τ) φ =ᶠ[𝓝 0] fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ -
      (PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ) :=
    Filter.Eventually.of_forall (fun ξ => by ring)
  have hPdc : ∀ n, coeff (Pdf τ (cOf f τ) φ) n =
      coeff (PiF f τ) n - coeff (Pihat τ (cOf f τ)) n -
        coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ) n := fun n => by
    rw [coeff_congr hPdeq, coeff_subC a1 a2, coeff_subC aF aH]
  have hPd1 : coeff (Pdf τ (cOf f τ) φ) 1 = 0 := by
    rw [hPdc, hdp2 1 (by norm_num), hF1, hp1]
    ring
  have hPd2 : coeff (Pdf τ (cOf f τ) φ) 2 = 0 := by
    rw [hPdc, hdp2 2 le_rfl, hF2, hp2]
    ring
  have nF := numerator_identity dF τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (by rw [hF1, hF2, mul_one]) hξ hξ0
  have nH := numerator_identity dH τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (by rw [hp1, hp2, mul_one]) hξ hξ0
  have nP := numerator_identity dPd τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ))
    (by rw [hPd1, hPd2, mul_zero]) hξ hξ0
  have n2 := numerator_identity d2 τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ))
    (by rw [hdp2 1 (by norm_num), hdp2 2 le_rfl, mul_zero]) hξ hξ0
  have dd : ∀ w ∈ ball (0 : ℂ) (1 / 4),
      deriv (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ) w =
        deriv (PiF f τ) w - deriv (Pihat τ (cOf f τ)) w - deriv (Pdf τ (cOf f τ) φ) w := fun w hw => by
    have hFw := (dF w hw).differentiableAt (isOpen_ball.mem_nhds hw)
    have hHw := (dH w hw).differentiableAt (isOpen_ball.mem_nhds hw)
    have hPw := (dPd w hw).differentiableAt (isOpen_ball.mem_nhds hw)
    have hFH : DifferentiableAt ℂ (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ) w := hFw.sub hHw
    rw [deriv_fun_sub hFH hPw, deriv_fun_sub hFw hHw]
  rw [dd _ hξ, dd _ hξm] at n2
  have hU : UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ))
      (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ) =
      UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiF f τ)) (xiτ τ) -
        UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (Pihat τ (cOf f τ))) (xiτ τ) -
          UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (Pdf τ (cOf f τ) φ)) (xiτ τ) := by
    apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) (pow_ne_zero 3 hξ0))
    linear_combination -n2 + nF - nH - nP
  have hT : Tser τ (coeff (PiF f τ)) =
      UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiF f τ)) (xiτ τ) /
        PiOddSer (coeff (PiF f τ)) (xiτ τ) := by
    simp only [Tser, UpsSer]
    rw [hF2]
  have hTh' : That τ (cOf f τ) * PihatO τ (cOf f τ) =
      UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (Pihat τ (cOf f τ))) (xiτ τ) := by
    rw [← hTh]
    simp only [Tser, UpsSer]
    rw [hp2, hO]
    exact div_mul_cancel₀ _ hPho
  have hTd : Tdot τ (cOf f τ) φ * PihatO τ (cOf f τ) =
      UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (Pdf τ (cOf f τ) φ)) (xiτ τ) -
        That τ (cOf f τ) * PiOddSer (coeff (Pdf τ (cOf f τ) φ)) (xiτ τ) :=
    Tdot_closed hDB f hf τ h1 h2' φ hφ
  have key : Tser τ (coeff (PiF f τ)) - That τ (cOf f τ) - Tdot τ (cOf f τ) φ =
      (UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ))
          (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ) -
        That τ (cOf f τ) *
          PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ) -
        Tdot τ (cOf f τ) φ * PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ)) (xiτ τ)) /
      PiOddSer (coeff (PiF f τ)) (xiτ τ) := by
    rw [eq_div_iff hPo0, hT, hU, hR2, hR1, hO]
    linear_combination (div_mul_cancel₀ (UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ)) (coeff (PiF f τ))
      (xiτ τ)) hPo0) - hTh' - hTd
  have hTdn : ‖Tdot τ (cOf f τ) φ‖ ≤ Real.sqrt (etadef (cOf f τ)) * np :=
    (hV hArea f hf τ h1 h2' hy0 φ hφ νp hν hνp).trans (mul_le_mul_of_nonneg_left hn hsη0)
  have hnum : ‖UpsLin τ ((2 * cOf f τ - (τ : ℂ)) / (vτ τ : ℂ))
          (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ) -
        That τ (cOf f τ) *
          PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ - Pdf τ (cOf f τ) φ ξ)) (xiτ τ) -
        Tdot τ (cOf f τ) φ * PiOddSer (coeff (fun ξ => PiF f τ ξ - Pihat τ (cOf f τ) ξ)) (xiτ τ)‖ ≤
      etadef (cOf f τ) * frakW (Z2Of νp ηp) + TPlusOf νp * (etadef (cOf f τ) * frakH (Z2Of νp ηp)) +
        Real.sqrt (etadef (cOf f τ)) * np * (Real.sqrt (etadef (cOf f τ)) * frakH (Z1Of νp ηp)) := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hU2n ?_)) ?_)
    · rw [norm_mul]
      exact mul_le_mul hTp hR2n (norm_nonneg _) hT0
    · rw [norm_mul]
      exact mul_le_mul hTdn hR1n (norm_nonneg _) (mul_nonneg hsη0 hnp0)
  rw [key, norm_div]
  calc _ ≤ (etadef (cOf f τ) * frakW (Z2Of νp ηp) + TPlusOf νp * (etadef (cOf f τ) * frakH (Z2Of νp ηp)) +
        Real.sqrt (etadef (cOf f τ)) * np * (Real.sqrt (etadef (cOf f τ)) * frakH (Z1Of νp ηp))) /
          PiLowOf νp ηp := div_le_div₀ ((norm_nonneg _).trans hnum) hnum hPL hPiLow
    _ = etadef (cOf f τ) * LamOf νp ηp np := by
        unfold LamOf
        rw [show Real.sqrt (etadef (cOf f τ)) * np * (Real.sqrt (etadef (cOf f τ)) * frakH (Z1Of νp ηp)) =
          Real.sqrt (etadef (cOf f τ)) * Real.sqrt (etadef (cOf f τ)) * np * frakH (Z1Of νp ηp) by ring, hsq]
        ring

end Robinson.Proofs
