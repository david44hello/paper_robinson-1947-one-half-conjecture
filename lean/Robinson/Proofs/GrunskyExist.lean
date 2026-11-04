/-
Robinson/Proofs/GrunskyExist.lean — proofs of sec3_grunsky_unique, sec3_grunsky_exists.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Grunsky
import Robinson.NotFormalized
import Robinson.Proofs.Sec3Local

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### Logarithms: uniqueness on connected sets, and holomorphy -/

/-- Two continuous logarithms of the same function on a preconnected set that agree at one point agree
everywhere: their difference takes values in the discrete group `2πiℤ`. -/
private lemma eqOn_of_exp_eq {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {f₁ f₂ : X → ℂ} (h₁ : ContinuousOn f₁ S) (h₂ : ContinuousOn f₂ S)
    (he : ∀ x ∈ S, exp (f₁ x) = exp (f₂ x)) {x₀ : X} (hx₀ : x₀ ∈ S) (h0 : f₁ x₀ = f₂ x₀) :
    ∀ x ∈ S, f₁ x = f₂ x := by
  intro x hx
  have hT : IsDiscrete ((AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * I) : AddSubgroup ℂ) : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (NormedSpace.discreteTopology_zmultiples _)
  have hmaps : Set.MapsTo (fun y => f₁ y - f₂ y) S
      ((AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * I) : AddSubgroup ℂ) : Set ℂ) := by
    intro y hy
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp (he y hy)
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
    show _ = f₁ y - f₂ y
    rw [zsmul_eq_mul, hn]
    ring
  have hconst : f₁ x - f₂ x = f₁ x₀ - f₂ x₀ := hS.constant_of_mapsTo hT (h₁.sub h₂) hmaps hx hx₀
  rw [h0, sub_self] at hconst
  exact sub_eq_zero.mp hconst

/-- An element of `2πiℤ` of modulus less than `2π` is `0`. -/
private lemma eq_zero_of_exp_eq_one {w : ℂ} (hw : exp w = 1) (hsmall : ‖w‖ < 2 * Real.pi) : w = 0 := by
  obtain ⟨n, rfl⟩ := exp_eq_one_iff.mp hw
  rcases eq_or_ne n 0 with h | h
  · simp [h]
  · exfalso
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h
    have hn : ‖(n : ℂ) * (2 * (Real.pi : ℂ) * I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
      simp [abs_of_pos Real.pi_pos]
    rw [hn] at hsmall
    nlinarith [Real.pi_pos]

/-- A continuous logarithm `φ` of a function `F` holomorphic at `z` is holomorphic at `z`: near `z`,
`φ(w) = φ(z) + Log(F(w)/F(z))` with the principal branch, since the difference is continuous, `0` at `z`, and
takes values in `2πiℤ`. -/
private lemma differentiableAt_of_exp_eq {φ F : ℂ → ℂ} {z : ℂ} (hφ : ContinuousAt φ z)
    (hF : DifferentiableAt ℂ F z) (hexp : ∀ᶠ w in 𝓝 z, exp (φ w) = F w) :
    DifferentiableAt ℂ φ z := by
  have hFz : F z = exp (φ z) := hexp.self_of_nhds.symm
  have hFz0 : F z ≠ 0 := hFz ▸ exp_ne_zero _
  have hslit : F z / F z ∈ slitPlane := by rw [div_self hFz0]; exact one_mem_slitPlane
  have hψd : DifferentiableAt ℂ (fun w => φ z + log (F w / F z)) z :=
    (differentiableAt_const _).add ((hF.div_const _).clog hslit)
  have hd : ContinuousAt (fun w => φ w - (φ z + log (F w / F z))) z := hφ.sub hψd.continuousAt
  have hsmall : ∀ᶠ w in 𝓝 z, ‖φ w - (φ z + log (F w / F z))‖ < 2 * Real.pi := by
    have h := hd.tendsto
    simp only [div_self hFz0, log_one, add_zero, sub_self] at h
    have := (Metric.tendsto_nhds.mp h) (2 * Real.pi) (by positivity)
    simpa [dist_zero_right] using this
  have heq : φ =ᶠ[𝓝 z] fun w => φ z + log (F w / F z) := by
    filter_upwards [hexp, hsmall] with w hw hws
    have hFw : F w ≠ 0 := hw ▸ exp_ne_zero _
    have h1 : exp (φ w - (φ z + log (F w / F z))) = 1 := by
      rw [exp_sub, exp_add, exp_log (div_ne_zero hFw hFz0), hw, ← hFz]
      field_simp
    exact sub_eq_zero.mp (eq_zero_of_exp_eq_one h1 hws)
  exact hψd.congr_of_eventuallyEq heq

/-! ### Double power series on the bidisc -/

private lemma kser_def (γ : ℕ → ℕ → ℂ) (s t : ℂ) :
    kser γ s t = ∑' nm : ℕ × ℕ, γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 := rfl

private lemma norm_term_le (γ : ℕ → ℕ → ℂ) (n m : ℕ) {s t : ℂ} {r : ℝ} (hs : ‖s‖ ≤ r) (ht : ‖t‖ ≤ r) :
    ‖γ n m * s ^ n * t ^ m‖ ≤ ‖γ n m * (r : ℂ) ^ n * (r : ℂ) ^ m‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hs
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  gcongr

/-- An absolutely convergent double power series on the bidisc has a continuous sum there (Weierstrass test on
each smaller bidisc). -/
private lemma continuousOn_kser {γ : ℕ → ℕ → ℂ}
    (hsum : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖)) :
    ContinuousOn (fun p : ℂ × ℂ => kser γ p.1 p.2) (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
  intro p hp
  have hp1 : ‖p.1‖ < 1 := mem_ball_zero_iff.mp hp.1
  have hp2 : ‖p.2‖ < 1 := mem_ball_zero_iff.mp hp.2
  have hm1 := le_max_left ‖p.1‖ ‖p.2‖
  have hm2 := le_max_right ‖p.1‖ ‖p.2‖
  have hmax : max ‖p.1‖ ‖p.2‖ < 1 := max_lt hp1 hp2
  set r : ℝ := (1 + max ‖p.1‖ ‖p.2‖) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by rw [hr]; linarith [norm_nonneg p.1]
  have h1r : ‖p.1‖ < r := by rw [hr]; linarith
  have h2r : ‖p.2‖ < r := by rw [hr]; linarith
  have hrball : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hV : ContinuousOn (fun q : ℂ × ℂ => kser γ q.1 q.2) (ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r) := by
    simp only [kser_def]
    refine continuousOn_tsum (f := fun nm (q : ℂ × ℂ) => γ nm.1 nm.2 * q.1 ^ nm.1 * q.2 ^ nm.2)
      (fun nm => ?_) (hsum _ _ hrball hrball) ?_
    · exact Continuous.continuousOn (by fun_prop)
    · intro nm q hq
      exact norm_term_le γ nm.1 nm.2 (le_of_lt (mem_ball_zero_iff.mp hq.1))
        (le_of_lt (mem_ball_zero_iff.mp hq.2))
  have hVo : IsOpen (ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r) := isOpen_ball.prod isOpen_ball
  have hpV : p ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r :=
    ⟨mem_ball_zero_iff.mpr h1r, mem_ball_zero_iff.mpr h2r⟩
  exact (hV.continuousAt (hVo.mem_nhds hpV)).continuousWithinAt

private lemma kser_zero_zero {γ : ℕ → ℕ → ℂ} (h0 : γ 0 0 = 0) : kser γ 0 0 = 0 := by
  have : (fun nm : ℕ × ℕ => γ nm.1 nm.2 * (0 : ℂ) ^ nm.1 * (0 : ℂ) ^ nm.2) = fun _ => 0 := by
    funext ⟨n, m⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [h0]
      · simp [zero_pow hm.ne']
    · simp [zero_pow hn.ne']
  rw [kser_def, this, tsum_zero]

private lemma tsum_mul_zero_pow (a : ℕ → ℂ) : ∑' m, a m * (0 : ℂ) ^ m = a 0 := by
  rw [tsum_eq_single 0 (fun m hm => by rw [zero_pow hm, mul_zero])]
  simp

/-- One variable: a power series that converges absolutely and sums to `0` on the unit disc has all
coefficients `0`. -/
private lemma coeff_eq_zero_of_tsum_eq_zero {a : ℕ → ℂ}
    (hsum : ∀ s ∈ ball (0 : ℂ) 1, Summable (fun n => ‖a n * s ^ n‖))
    (hzero : ∀ s ∈ ball (0 : ℂ) 1, ∑' n, a n * s ^ n = 0) : a = 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hhalf : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real]
    norm_num
  have hrad : ((2⁻¹ : NNReal) : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable
    refine (hsum _ hhalf).congr (fun n => ?_)
    rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real]
    norm_num
  have hpos : 0 < p.radius := lt_of_lt_of_le (ENNReal.coe_pos.mpr (by norm_num)) hrad
  have hps := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hev : p.sum =ᶠ[𝓝 0] 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with s hs
    change FormalMultilinearSeries.ofScalarsSum a s = 0
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simpa [smul_eq_mul] using hzero s hs
  have hp0 : p = 0 := hps.eq_zero_of_eventually hev
  funext n
  have hpn : p n = 0 := by rw [hp0]; rfl
  exact (FormalMultilinearSeries.ofScalars_eq_zero ℂ n).mp hpn

private lemma row_tsum_eq (c : ℕ → ℕ → ℂ) (s t : ℂ) (n : ℕ) :
    (∑' m, c n m * t ^ m) * s ^ n = ∑' m, c n m * s ^ n * t ^ m := by
  rw [← tsum_mul_right]
  congr 1
  funext m
  ring

/-- Summing a double series by rows: for fixed `t`, the rows give a power series in `s`. -/
private lemma row_series (c : ℕ → ℕ → ℂ) {s t : ℂ}
    (hs : Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖)) :
    Summable (fun n => ‖(∑' m, c n m * t ^ m) * s ^ n‖) ∧
      ∑' n, (∑' m, c n m * t ^ m) * s ^ n = kser c s t := by
  have hF : Summable (fun nm : ℕ × ℕ => c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2) := hs.of_norm
  constructor
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs.prod
    rw [row_tsum_eq]
    exact norm_tsum_le_tsum_norm (hs.prod_factor n)
  · simp_rw [row_tsum_eq]
    rw [kser_def]
    exact hF.tsum_prod.symm

private lemma row_summable {c : ℕ → ℕ → ℂ} {s t : ℂ} (hs0 : s ≠ 0)
    (h : Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖)) (n : ℕ) :
    Summable (fun m => ‖c n m * t ^ m‖) := by
  have hne : ‖s‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hs0)
  refine (summable_mul_left_iff hne).mp ((h.prod_factor n).congr fun m => ?_)
  simp only [norm_mul, norm_pow]
  ring

/-- Two variables: a double power series that converges absolutely and sums to `0` on the bidisc has all
coefficients `0`. -/
private lemma coeff_eq_zero_of_kser_eq_zero {c : ℕ → ℕ → ℂ}
    (hsum : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖))
    (hzero : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → kser c s t = 0) : c = 0 := by
  have hrow : ∀ t ∈ ball (0 : ℂ) 1, ∀ n, ∑' m, c n m * t ^ m = 0 := by
    intro t ht
    have h := coeff_eq_zero_of_tsum_eq_zero (a := fun n => ∑' m, c n m * t ^ m)
      (fun s hs => (row_series c (hsum s t hs ht)).1)
      (fun s hs => ((row_series c (hsum s t hs ht)).2).trans (hzero s t hs ht))
    exact fun n => congr_fun h n
  have hhalf : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real]
    norm_num
  have hhalf0 : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by norm_num
  funext n m
  have hn := coeff_eq_zero_of_tsum_eq_zero (a := fun m => c n m)
    (fun t ht => row_summable hhalf0 (hsum _ t hhalf ht) n) (fun t ht => hrow t ht n)
  exact congr_fun hn m

/-- If two absolutely convergent double power series have the same sum on the bidisc, their coefficients agree. -/
private lemma coeff_ext {c c' : ℕ → ℕ → ℂ}
    (hc : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖))
    (hc' : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖c' nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖))
    (heq : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → kser c s t = kser c' s t) : c = c' := by
  have hsplit : ∀ s t : ℂ, (fun nm : ℕ × ℕ => (c - c') nm.1 nm.2 * s ^ nm.1 * t ^ nm.2) =
      fun nm => c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 - c' nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 := by
    intro s t
    funext nm
    simp only [Pi.sub_apply]
    ring
  have hdiff := coeff_eq_zero_of_kser_eq_zero (c := c - c') ?_ ?_
  · funext n m
    have h := congr_fun (congr_fun hdiff n) m
    simpa [sub_eq_zero] using h
  · intro s t hs ht
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun nm => ?_)
      ((hc s t hs ht).add (hc' s t hs ht))
    rw [congr_fun (hsplit s t) nm]
    exact norm_sub_le _ _
  · intro s t hs ht
    rw [kser_def, hsplit s t, ((hc s t hs ht).of_norm).tsum_sub ((hc' s t hs ht).of_norm)]
    exact sub_eq_zero.mpr (heq s t hs ht)

/-- The transposed coefficients `cᵀ(n, m) = c(m, n)`. -/
private def ctr (c : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ := fun n m => c m n

/-- Transposing the coefficients swaps the two variables. -/
private lemma kser_swap (c : ℕ → ℕ → ℂ) (s t : ℂ) : kser (ctr c) s t = kser c t s := by
  rw [kser_def, kser_def]
  have h := (Equiv.prodComm ℕ ℕ).tsum_eq (fun nm : ℕ × ℕ => c nm.1 nm.2 * t ^ nm.1 * s ^ nm.2)
  rw [← h]
  congr 1
  funext nm
  simp only [ctr, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  ring

private lemma summable_swap {c : ℕ → ℕ → ℂ} {s t : ℂ}
    (h : Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * t ^ nm.1 * s ^ nm.2‖)) :
    Summable (fun nm : ℕ × ℕ => ‖ctr c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖) := by
  refine h.prod_symm.congr fun nm => ?_
  simp only [ctr, Prod.fst_swap, Prod.snd_swap]
  ring_nf

/-! ### The bidisc -/

private lemma convex_bidisc : Convex ℝ (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) :=
  (convex_ball _ _).prod (convex_ball _ _)

private lemma isOpen_bidisc : IsOpen (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := isOpen_ball.prod isOpen_ball

private lemma zero_mem_disc : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos

private lemma zero_mem_bidisc : ((0 : ℂ), (0 : ℂ)) ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1 :=
  ⟨zero_mem_disc, zero_mem_disc⟩

/-! ### Uniqueness -/

theorem sec3_grunsky_unique_proved (g : ℂ → ℂ) (hg : InS g) (γ γ' : ℕ → ℕ → ℂ) (h : IsGrunskyCoeff g γ)
    (h' : IsGrunskyCoeff g γ') : γ = γ' := by
  clear hg
  obtain ⟨h0, hk⟩ := h
  obtain ⟨h0', hk'⟩ := h'
  have hagree : ∀ p ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1, kser γ p.1 p.2 = kser γ' p.1 p.2 := by
    refine eqOn_of_exp_eq convex_bidisc.isPreconnected
      (continuousOn_kser fun s t hs ht => (hk s t hs ht).1)
      (continuousOn_kser fun s t hs ht => (hk' s t hs ht).1) (fun p hp => ?_) zero_mem_bidisc ?_
    · rw [(hk p.1 p.2 hp.1 hp.2).2, (hk' p.1 p.2 hp.1 hp.2).2]
    · rw [kser_zero_zero (h0 0 0 (Or.inl rfl)), kser_zero_zero (h0' 0 0 (Or.inl rfl))]
  exact coeff_ext (fun s t hs ht => (hk s t hs ht).1) (fun s t hs ht => (hk' s t hs ht).1)
    (fun s t hs ht => hagree (s, t) ⟨hs, ht⟩)

/-! ### The kernel quotient: continuity, holomorphy in each variable, zero-freeness -/

/-- The difference quotient of `g`, extended by `g'` on the diagonal, is the `dslope` of `g`. -/
private lemma dquot_eq_dslope_left (g : ℂ → ℂ) (s t : ℂ) :
    (if s = t then deriv g s else (g s - g t) / (s - t)) = dslope g t s := by
  by_cases h : s = t
  · subst h
    rw [ite_eq_left rfl, dslope_same]
  · rw [ite_eq_right h, dslope_of_ne _ h, slope_def_field]

private lemma dslope_comm (g : ℂ → ℂ) (s t : ℂ) : dslope g t s = dslope g s t := by
  by_cases h : s = t
  · rw [h]
  · rw [dslope_of_ne _ h, dslope_of_ne _ (Ne.symm h), slope_def_field, slope_def_field,
      show g t - g s = -(g s - g t) by ring, show t - s = -(s - t) by ring, neg_div_neg_eq]

/-- The factor `s/g(s)` (value `1` at `0`) is the reciprocal of the `dslope` of `g` at `0`. -/
private lemma recip_eq (g : ℂ → ℂ) (hg0 : g 0 = 0) (hd : deriv g 0 = 1) (s : ℂ) :
    (if s = 0 then 1 else s / g s) = (dslope g 0 s)⁻¹ := by
  by_cases h : s = 0
  · subst h
    rw [ite_eq_left rfl, dslope_same, hd, inv_one]
  · rw [ite_eq_right h, dslope_of_ne _ h, slope_def_field, hg0, sub_zero, sub_zero, inv_div]

private lemma kernelQuot_eq (g : ℂ → ℂ) (hg : InS g) (s t : ℂ) :
    kernelQuot g s t = dslope g t s * (dslope g 0 s)⁻¹ * (dslope g 0 t)⁻¹ := by
  unfold kernelQuot
  rw [dquot_eq_dslope_left, recip_eq g hg.map_zero hg.deriv_zero, recip_eq g hg.map_zero hg.deriv_zero]

private lemma dslope_zero_ne_zero (g : ℂ → ℂ) (hg : InS g) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    dslope g 0 s ≠ 0 := by
  have h := (sec3_kernel_nonvanishing_proved g hg).2.2 s hs
  by_cases h0 : s = 0
  · subst h0
    rw [dslope_same]
    simpa using h
  · rw [dslope_of_ne _ h0, slope_def_field, hg.map_zero, sub_zero, sub_zero]
    simpa [h0] using h

private lemma dslope_ne_zero (g : ℂ → ℂ) (hg : InS g) {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1)
    (ht : t ∈ ball (0 : ℂ) 1) : dslope g t s ≠ 0 := by
  rw [← dquot_eq_dslope_left]
  exact (sec3_kernel_nonvanishing_proved g hg).1 s t hs ht

private lemma dslope_differentiableOn (g : ℂ → ℂ) (hg : InS g) {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (dslope g a) (ball (0 : ℂ) 1) :=
  (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).mpr hg.differentiableOn

/-- Joint continuity of the difference quotient at a diagonal point: `g` is strictly differentiable there
and `g'` is continuous. -/
private lemma dslope_continuousAt_diag (g : ℂ → ℂ) (hg : InS g) {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ContinuousAt (fun p : ℂ × ℂ => dslope g p.2 p.1) (a, a) := by
  have han : AnalyticAt ℂ g a := hg.differentiableOn.analyticAt (isOpen_ball.mem_nhds ha)
  have hlo := hasDerivAtFilter_iff_isLittleO.mp han.hasStrictDerivAt
  have hdc : ContinuousAt (deriv g) a :=
    ((hg.differentiableOn.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds ha)).continuousAt
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h1 := hlo.def (half_pos hε)
  have h2 : ∀ᶠ q : ℂ × ℂ in 𝓝 (a, a), dist (deriv g q.1) (deriv g a) < ε :=
    (Metric.tendsto_nhds.mp (hdc.tendsto.comp (continuous_fst.tendsto (a, a)))) ε hε
  filter_upwards [h1, h2] with q hq1 hq2
  show dist (dslope g q.2 q.1) (dslope g a a) < ε
  rw [dslope_same]
  by_cases hq : q.1 = q.2
  · rw [← hq, dslope_same]
    exact hq2
  · have hne : q.1 - q.2 ≠ 0 := sub_ne_zero.mpr hq
    have hpos : 0 < ‖q.1 - q.2‖ := norm_pos_iff.mpr hne
    rw [dslope_of_ne _ hq, slope_def_field, dist_eq_norm]
    have hrw : (g q.1 - g q.2) / (q.1 - q.2) - deriv g a =
        (g q.1 - g q.2 - (q.1 - q.2) • deriv g a) / (q.1 - q.2) := by
      rw [smul_eq_mul, eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
      ring
    rw [hrw, norm_div, div_lt_iff₀ hpos]
    have hlt : ε / 2 * ‖q.1 - q.2‖ < ε * ‖q.1 - q.2‖ := by nlinarith
    exact lt_of_le_of_lt hq1 hlt

/-- Joint continuity of the difference quotient off the diagonal. -/
private lemma dslope_continuousAt_off (g : ℂ → ℂ) (hg : InS g) {p : ℂ × ℂ}
    (hp : p ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) (hne : p.1 ≠ p.2) :
    ContinuousAt (fun q : ℂ × ℂ => dslope g q.2 q.1) p := by
  have hg1 : ContinuousAt g p.1 :=
    (hg.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hp.1)).continuousAt
  have hg2 : ContinuousAt g p.2 :=
    (hg.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hp.2)).continuousAt
  have hc1 : ContinuousAt (fun q : ℂ × ℂ => g q.1) p := hg1.comp continuousAt_fst
  have hc2 : ContinuousAt (fun q : ℂ × ℂ => g q.2) p := hg2.comp continuousAt_snd
  have hc : ContinuousAt (fun q : ℂ × ℂ => (g q.1 - g q.2) / (q.1 - q.2)) p :=
    (hc1.sub hc2).div (continuousAt_fst.sub continuousAt_snd) (sub_ne_zero.mpr hne)
  refine hc.congr ?_
  filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hne] with q hq
  rw [dslope_of_ne _ hq, slope_def_field]

private lemma dslope_continuousOn (g : ℂ → ℂ) (hg : InS g) :
    ContinuousOn (fun p : ℂ × ℂ => dslope g p.2 p.1) (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hne : p.1 = p.2
  · have hpe : p = (p.1, p.1) := Prod.ext rfl hne.symm
    rw [hpe]
    exact dslope_continuousAt_diag g hg hp.1
  · exact dslope_continuousAt_off g hg hp hne

private lemma recip_continuousOn (g : ℂ → ℂ) (hg : InS g) :
    ContinuousOn (fun s => (dslope g 0 s)⁻¹) (ball (0 : ℂ) 1) :=
  (dslope_differentiableOn g hg zero_mem_disc).continuousOn.inv₀ (fun _ hs => dslope_zero_ne_zero g hg hs)

private lemma kernel_continuousOn (g : ℂ → ℂ) (hg : InS g) :
    ContinuousOn (fun p : ℂ × ℂ => kernelQuot g p.1 p.2) (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
  have h1 := dslope_continuousOn g hg
  have h2 : ContinuousOn (fun p : ℂ × ℂ => (dslope g 0 p.1)⁻¹) (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) :=
    (recip_continuousOn g hg).comp continuousOn_fst (fun _ hp => hp.1)
  have h3 : ContinuousOn (fun p : ℂ × ℂ => (dslope g 0 p.2)⁻¹) (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) :=
    (recip_continuousOn g hg).comp continuousOn_snd (fun _ hp => hp.2)
  refine ((h1.mul h2).mul h3).congr (fun p _ => ?_)
  exact kernelQuot_eq g hg p.1 p.2

private lemma kernel_ne_zero (g : ℂ → ℂ) (hg : InS g) {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1)
    (ht : t ∈ ball (0 : ℂ) 1) : kernelQuot g s t ≠ 0 := by
  rw [kernelQuot_eq g hg]
  exact mul_ne_zero (mul_ne_zero (dslope_ne_zero g hg hs ht) (inv_ne_zero (dslope_zero_ne_zero g hg hs)))
    (inv_ne_zero (dslope_zero_ne_zero g hg ht))

private lemma kernel_differentiableOn_left (g : ℂ → ℂ) (hg : InS g) {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (fun s => kernelQuot g s t) (ball (0 : ℂ) 1) := by
  have h := ((dslope_differentiableOn g hg ht).mul ((dslope_differentiableOn g hg zero_mem_disc).inv
    (fun _ hs => dslope_zero_ne_zero g hg hs))).mul_const (dslope g 0 t)⁻¹
  refine h.congr (fun s _ => ?_)
  exact kernelQuot_eq g hg s t

private lemma kernel_differentiableOn_right (g : ℂ → ℂ) (hg : InS g) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (fun t => kernelQuot g s t) (ball (0 : ℂ) 1) := by
  have h := ((dslope_differentiableOn g hg hs).mul_const (dslope g 0 s)⁻¹).mul
    ((dslope_differentiableOn g hg zero_mem_disc).inv (fun _ ht => dslope_zero_ne_zero g hg ht))
  refine h.congr (fun t _ => ?_)
  show kernelQuot g s t = dslope g s t * (dslope g 0 s)⁻¹ * (dslope g 0 t)⁻¹
  rw [kernelQuot_eq g hg, dslope_comm g s t]

private lemma kernel_symm (g : ℂ → ℂ) (hg : InS g) (s t : ℂ) : kernelQuot g s t = kernelQuot g t s := by
  rw [kernelQuot_eq g hg, kernelQuot_eq g hg, dslope_comm g s t]
  ring

private lemma kernel_axis_left (g : ℂ → ℂ) (hg : InS g) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    kernelQuot g s 0 = 1 := by
  rw [kernelQuot_eq g hg, dslope_same, hg.deriv_zero, inv_one, mul_one,
    mul_inv_cancel₀ (dslope_zero_ne_zero g hg hs)]

private lemma kernel_axis_right (g : ℂ → ℂ) (hg : InS g) {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    kernelQuot g 0 t = 1 := by
  rw [kernel_symm g hg, kernel_axis_left g hg ht]

/-! ### A logarithm of the kernel, holomorphic in each variable -/

/-- The bidisc is convex, hence simply connected, so the zero-free continuous kernel has a continuous
logarithm there; normalise it to be `0` at the origin, where the kernel is `1`. -/
private lemma exists_log_kernel (g : ℂ → ℂ) (hg : InS g) :
    ∃ L : ℂ × ℂ → ℂ, ContinuousOn L (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) ∧
      (∀ p ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1, exp (L p) = kernelQuot g p.1 p.2) ∧ L (0, 0) = 0 := by
  have hsc : IsSimplyConnected (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
    have : ContractibleSpace (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1 : Set (ℂ × ℂ)) :=
      convex_bidisc.contractibleSpace ⟨_, zero_mem_bidisc⟩
    unfold IsSimplyConnected
    infer_instance
  have hK0 : (0 : ℂ) ∉ (fun p : ℂ × ℂ => kernelQuot g p.1 p.2) '' (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
    rintro ⟨p, hp, hp0⟩
    exact kernel_ne_zero g hg hp.1 hp.2 hp0
  obtain ⟨L₁, hL₁c, hL₁e⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_bidisc
    (kernel_continuousOn g hg) hK0
  have h00 : exp (L₁ (0, 0)) = 1 := by
    have h := hL₁e zero_mem_bidisc
    simp only [Function.comp_apply] at h
    rw [h]
    exact kernel_axis_left g hg zero_mem_disc
  refine ⟨fun p => L₁ p - L₁ (0, 0), hL₁c.sub continuousOn_const, fun p hp => ?_, sub_self _⟩
  have h := hL₁e hp
  simp only [Function.comp_apply] at h
  show exp (L₁ p - L₁ (0, 0)) = _
  rw [exp_sub, h, h00, div_one]

private lemma log_differentiableOn_left {g : ℂ → ℂ} (hg : InS g) {L : ℂ × ℂ → ℂ}
    (hLc : ContinuousOn L (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1))
    (hLe : ∀ p ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1, exp (L p) = kernelQuot g p.1 p.2) :
    ∀ t ∈ ball (0 : ℂ) 1, DifferentiableOn ℂ (fun s => L (s, t)) (ball (0 : ℂ) 1) := by
  intro t ht s hs
  refine (differentiableAt_of_exp_eq (F := fun s => kernelQuot g s t) ?_ ?_ ?_).differentiableWithinAt
  · have hL : ContinuousAt L (s, t) := hLc.continuousAt (isOpen_bidisc.mem_nhds ⟨hs, ht⟩)
    exact hL.comp (f := fun w : ℂ => (w, t)) (by fun_prop)
  · exact (kernel_differentiableOn_left g hg ht).differentiableAt (isOpen_ball.mem_nhds hs)
  · filter_upwards [isOpen_ball.mem_nhds hs] with w hw
    exact hLe (w, t) ⟨hw, ht⟩

private lemma log_differentiableOn_right {g : ℂ → ℂ} (hg : InS g) {L : ℂ × ℂ → ℂ}
    (hLc : ContinuousOn L (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1))
    (hLe : ∀ p ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1, exp (L p) = kernelQuot g p.1 p.2) :
    ∀ s ∈ ball (0 : ℂ) 1, DifferentiableOn ℂ (fun t => L (s, t)) (ball (0 : ℂ) 1) := by
  intro s hs t ht
  refine (differentiableAt_of_exp_eq (F := fun t => kernelQuot g s t) ?_ ?_ ?_).differentiableWithinAt
  · have hL : ContinuousAt L (s, t) := hLc.continuousAt (isOpen_bidisc.mem_nhds ⟨hs, ht⟩)
    exact hL.comp (f := fun w : ℂ => (s, w)) (by fun_prop)
  · exact (kernel_differentiableOn_right g hg hs).differentiableAt (isOpen_ball.mem_nhds ht)
  · filter_upwards [isOpen_ball.mem_nhds ht] with w hw
    exact hLe (s, w) ⟨hs, hw⟩

/-! ### Existence and symmetry -/

theorem sec3_grunsky_exists_proved (hB : FactBidiscPowerSeries) (g : ℂ → ℂ) (hg : InS g) :
    ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n := by
  obtain ⟨L, hLc, hLe, hL0⟩ := exists_log_kernel g hg
  obtain ⟨c, hc⟩ := hB L hLc (log_differentiableOn_left hg hLc hLe) (log_differentiableOn_right hg hLc hLe)
  have hsum : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖) :=
    fun s t hs ht => (hc s t hs ht).1
  have hLk : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → L (s, t) = kser c s t :=
    fun s t hs ht => (hc s t hs ht).2
  -- `L` vanishes on both axes, where the kernel is `1`
  have hax : ∀ s ∈ ball (0 : ℂ) 1, L (s, 0) = 0 ∧ L (0, s) = 0 := by
    intro s hs
    constructor
    · refine eqOn_of_exp_eq (convex_ball (0 : ℂ) 1).isPreconnected (f₁ := fun w => L (w, 0))
        (f₂ := fun _ => 0) ?_ continuousOn_const ?_ zero_mem_disc hL0 s hs
      · exact hLc.comp (Continuous.continuousOn (by fun_prop)) (fun w hw => ⟨hw, zero_mem_disc⟩)
      · intro w hw
        show exp (L (w, 0)) = exp 0
        rw [hLe (w, 0) ⟨hw, zero_mem_disc⟩, exp_zero]
        exact kernel_axis_left g hg hw
    · refine eqOn_of_exp_eq (convex_ball (0 : ℂ) 1).isPreconnected (f₁ := fun w => L (0, w))
        (f₂ := fun _ => 0) ?_ continuousOn_const ?_ zero_mem_disc hL0 s hs
      · exact hLc.comp (Continuous.continuousOn (by fun_prop)) (fun w hw => ⟨zero_mem_disc, hw⟩)
      · intro w hw
        show exp (L (0, w)) = exp 0
        rw [hLe (0, w) ⟨zero_mem_disc, hw⟩, exp_zero]
        exact kernel_axis_right g hg hw
  -- hence the coefficients with `m = 0` vanish
  have hrow0 : ∀ n, c n 0 = 0 := by
    have h := coeff_eq_zero_of_tsum_eq_zero (a := fun n => ∑' m, c n m * (0 : ℂ) ^ m)
      (fun s hs => (row_series c (hsum s 0 hs zero_mem_disc)).1)
      (fun s hs => by
        rw [(row_series c (hsum s 0 hs zero_mem_disc)).2, ← hLk s 0 hs zero_mem_disc]
        exact (hax s hs).1)
    intro n
    have hn : ∑' m, c n m * (0 : ℂ) ^ m = 0 := congr_fun h n
    rwa [tsum_mul_zero_pow] at hn
  -- and, transposing, the coefficients with `n = 0` vanish
  have hsumT : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable (fun nm : ℕ × ℕ => ‖ctr c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖) :=
    fun s t hs ht => summable_swap (hsum t s ht hs)
  have hcol0 : ∀ m, c 0 m = 0 := by
    have h := coeff_eq_zero_of_tsum_eq_zero
      (a := fun n => ∑' m, ctr c n m * (0 : ℂ) ^ m)
      (fun s hs => (row_series (ctr c) (hsumT s 0 hs zero_mem_disc)).1)
      (fun s hs => by
        rw [(row_series (ctr c) (hsumT s 0 hs zero_mem_disc)).2, kser_swap, ← hLk 0 s zero_mem_disc hs]
        exact (hax s hs).2)
    intro m
    have hm : ∑' k, ctr c m k * (0 : ℂ) ^ k = 0 := congr_fun h m
    rw [tsum_mul_zero_pow] at hm
    exact hm
  have hzero : ∀ n m : ℕ, n = 0 ∨ m = 0 → c n m = 0 := by
    rintro n m (rfl | rfl)
    · exact hcol0 m
    · exact hrow0 n
  have hG : IsGrunskyCoeff g c := by
    refine ⟨hzero, fun s t hs ht => ⟨hsum s t hs ht, ?_⟩⟩
    rw [← hLk s t hs ht]
    exact hLe (s, t) ⟨hs, ht⟩
  -- symmetry: the transposed coefficients are Grunsky coefficients too, and these are unique
  have hGT : IsGrunskyCoeff g (ctr c) := by
    refine ⟨fun n m hnm => hzero m n hnm.symm, fun s t hs ht => ⟨hsumT s t hs ht, ?_⟩⟩
    rw [kser_swap, kernel_symm g hg s t]
    exact (hG.2 t s ht hs).2
  refine ⟨c, hG, fun n m => ?_⟩
  have h := sec3_grunsky_unique_proved g hg c (ctr c) hG hGT
  exact congr_fun (congr_fun h n) m

end Robinson.Proofs
