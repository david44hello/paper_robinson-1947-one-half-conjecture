/-
Robinson/Proofs/Lem31.lean — proofs of sec3_block_sums, lem_3_1_i, lem_3_1_ii, lem_3_1_iii, eq_Kf.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Grunsky

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

namespace Lem31

/-! ## Double series and the bilinear form -/

/-- An absolutely summable double series whose terms are `x n * (A n m * y m)` sums to `xᵀ A y`. -/
theorem bilinf_hasSum {F : ℕ × ℕ → ℂ} (hF : Summable fun p => ‖F p‖) {x : ℕ → ℂ} {A : ℕ → ℕ → ℂ}
    {y : ℕ → ℂ} (hterm : ∀ n m, x n * (A n m * y m) = F (n, m)) : HasSum F (bilinf x A y) := by
  have hs : Summable F := hF.of_norm
  have key : bilinf x A y = ∑' p, F p := by
    rw [hs.tsum_prod]
    unfold bilinf
    refine tsum_congr fun n => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun m => hterm n m
  rw [key]
  exact hs.hasSum

theorem sqrt_cast_ne_zero {n : ℕ} (hn : n ≠ 0) : (Real.sqrt n : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]
  exact (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'

/-- `(xⁿ/√n) (√(nm) c) (yᵐ/√m) = c xⁿ yᵐ` for `n, m ≥ 1`. -/
theorem sqrt_term_eq {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (c x y : ℂ) :
    x ^ n / (Real.sqrt n : ℂ) * ((Real.sqrt ((n : ℝ) * m) : ℂ) * c * (y ^ m / (Real.sqrt m : ℂ))) =
      c * x ^ n * y ^ m := by
  have hn' := sqrt_cast_ne_zero hn
  have hm' := sqrt_cast_ne_zero hm
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Complex.ofReal_mul]
  field_simp

/-- The double series vanishes at `s = 0` when the row `n = 0` of coefficients vanishes. -/
theorem kser_zero_fst {γ : ℕ → ℕ → ℂ} (h0 : ∀ m, γ 0 m = 0) (t : ℂ) : kser γ 0 t = 0 := by
  have hterm : ∀ nm : ℕ × ℕ, γ nm.1 nm.2 * (0 : ℂ) ^ nm.1 * t ^ nm.2 = 0 := by
    intro nm
    rcases Nat.eq_zero_or_pos nm.1 with hn | hn
    · rw [hn, h0]; ring
    · rw [zero_pow hn.ne']; ring
  unfold kser
  simp only [hterm, tsum_zero]

/-! ## Continuity of the double series on the bidisc -/

theorem kser_contOn {γ : ℕ → ℕ → ℂ}
    (hsum : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable fun nm : ℕ × ℕ => ‖γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖) :
    ContinuousOn (fun p : ℂ × ℂ => kser γ p.1 p.2) (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
  rintro ⟨s₀, t₀⟩ ⟨hs₀, ht₀⟩
  rw [mem_ball_zero_iff] at hs₀ ht₀
  have hmax := max_lt hs₀ ht₀
  have hl := le_max_left ‖s₀‖ ‖t₀‖
  have hr' := le_max_right ‖s₀‖ ‖t₀‖
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (max ‖s₀‖ ‖t₀‖ + 1) / 2 := ⟨_, rfl⟩
  have h1 : ‖s₀‖ < r := by rw [hr]; linarith
  have h2 : ‖t₀‖ < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 ≤ r := (norm_nonneg _).trans h1.le
  have hrb : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1
  have hU : ContinuousOn (fun p : ℂ × ℂ => kser γ p.1 p.2) (ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r) := by
    unfold kser
    refine continuousOn_tsum (fun nm => by fun_prop) (hsum _ _ hrb hrb) ?_
    rintro nm ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩
    rw [mem_ball_zero_iff] at hq₁ hq₂
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
    gcongr
  exact (hU.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds
    ⟨mem_ball_zero_iff.2 h1, mem_ball_zero_iff.2 h2⟩)).continuousWithinAt

theorem kser_comp_contOn {X : Type*} [TopologicalSpace X] {S : Set X} {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ}
    (hγ : IsGrunskyCoeff g γ) {u v : X → ℂ} (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (hmaps : ∀ p ∈ S, u p ∈ ball (0 : ℂ) 1 ∧ v p ∈ ball (0 : ℂ) 1) :
    ContinuousOn (fun p => kser γ (u p) (v p)) S := by
  have hc := (kser_contOn fun s t hs ht => (hγ.2 s t hs ht).1).comp (hu.prodMk hv)
    (fun p hp => Set.mk_mem_prod (hmaps p hp).1 (hmaps p hp).2)
  refine hc.congr fun p _ => ?_
  simp only [Function.comp_apply]

theorem bidisc_open : IsOpen (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := isOpen_ball.prod isOpen_ball

theorem bidisc_preconn : IsPreconnected (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) :=
  isPreconnected_ball.prod isPreconnected_ball

theorem origin_in_bidisc : ((0 : ℂ), (0 : ℂ)) ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1 :=
  ⟨mem_ball_self one_pos, mem_ball_self one_pos⟩

/-! ## A continuous function with exponential `1` on a connected open set, vanishing at one point, is `0` -/

theorem small_exp_one {z : ℂ} (hexp : exp z = 1) (hz : ‖z‖ < 1) : z = 0 := by
  obtain ⟨n, rfl⟩ := Complex.exp_eq_one_iff.1 hexp
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · exfalso
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have h3 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by simp [abs_of_pos Real.pi_pos]
    rw [norm_mul, Complex.norm_intCast, h3] at hz
    nlinarith [Real.pi_gt_three]

theorem exp_one_const {X : Type*} [TopologicalSpace X] {S : Set X} (hSo : IsOpen S)
    (hSc : IsPreconnected S) {D : X → ℂ} (hD : ContinuousOn D S) (hexp : ∀ x ∈ S, exp (D x) = 1)
    {x₀ : X} (hx₀ : x₀ ∈ S) (h0 : D x₀ = 0) : ∀ x ∈ S, D x = 0 := by
  have hu_open : IsOpen (S ∩ D ⁻¹' ball (0 : ℂ) 1) := hD.isOpen_inter_preimage hSo isOpen_ball
  have hx₀u : x₀ ∈ D ⁻¹' ball (0 : ℂ) 1 := by
    show D x₀ ∈ ball (0 : ℂ) 1
    rw [h0]; exact mem_ball_self one_pos
  have hsub : S ⊆ S ∩ D ⁻¹' ball (0 : ℂ) 1 := by
    refine hSc.subset_of_closure_inter_subset hu_open ⟨x₀, hx₀, hx₀, hx₀u⟩ ?_
    rintro x ⟨hxc, hxS⟩
    have hcont : ContinuousAt D x := hD.continuousAt (hSo.mem_nhds hxS)
    have hV : D ⁻¹' ball (D x) 1 ∈ 𝓝 x := hcont.preimage_mem_nhds (ball_mem_nhds _ one_pos)
    obtain ⟨y, hyV, hyS, hyu⟩ := mem_closure_iff_nhds.1 hxc _ hV
    have hy0 : D y = 0 := small_exp_one (hexp y hyS) (mem_ball_zero_iff.1 hyu)
    refine ⟨hxS, ?_⟩
    have hd : dist (D y) (D x) < 1 := hyV
    rw [hy0, dist_comm, dist_zero_right] at hd
    exact mem_ball_zero_iff.2 hd
  intro x hx
  exact small_exp_one (hexp x hx) (mem_ball_zero_iff.1 (hsub hx).2)

/-! ## Uniqueness of power-series coefficients (one and two variables) -/

theorem coeff1_zero {a : ℕ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsum : Summable fun n => ‖a n * (ρ : ℂ) ^ n‖)
    (hzero : ∀ x : ℂ, ‖x‖ < ρ → ∑' n, a n * x ^ n = 0) : ∀ n, a n = 0 := by
  lift ρ to NNReal using hρ.le with r
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hrad : (r : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable ?_
    refine hsum.congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (NNReal.coe_nonneg r)]
  have hpos : 0 < p.radius := lt_of_lt_of_le (ENNReal.coe_pos.2 (NNReal.coe_pos.1 hρ)) hrad
  have hps : HasFPowerSeriesAt p.sum p 0 := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hev : p.sum =ᶠ[𝓝 0] 0 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with x hx
    rw [mem_ball_zero_iff] at hx
    simp only [Pi.zero_apply, FormalMultilinearSeries.sum, hp, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact hzero x hx
  have hp0 : p = 0 := hps.eq_zero_of_eventually hev
  have ha : a = 0 := (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 (by rw [← hp]; exact hp0)
  intro n
  simp [ha]

theorem coeff2_zero {c : ℕ → ℕ → ℂ}
    (hsum : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable fun nm : ℕ × ℕ => ‖c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖)
    (hzero : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      ∑' nm : ℕ × ℕ, c nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 = 0) :
    ∀ n m, c n m = 0 := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]; norm_num
  have hsmall : ∀ x : ℂ, ‖x‖ < 1 / 2 → x ∈ ball (0 : ℂ) 1 := fun x hx => by
    rw [mem_ball_zero_iff]; linarith
  have hrow : ∀ t ∈ ball (0 : ℂ) 1, ∀ n, ∑' m, c n m * t ^ m = 0 := by
    intro t ht
    have hS := hsum _ _ hhalf ht
    refine coeff1_zero (a := fun n => ∑' m, c n m * t ^ m) (by norm_num : (0 : ℝ) < 1 / 2) ?_ ?_
    · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hS.prod
      have hfib : Summable fun m => ‖c n m * t ^ m * ((1 / 2 : ℝ) : ℂ) ^ n‖ :=
        (hS.prod_factor n).congr fun m => by dsimp only; congr 1; ring
      dsimp only
      calc ‖(∑' m, c n m * t ^ m) * ((1 / 2 : ℝ) : ℂ) ^ n‖
          = ‖∑' m, c n m * t ^ m * ((1 / 2 : ℝ) : ℂ) ^ n‖ := by rw [tsum_mul_right]
        _ ≤ ∑' m, ‖c n m * t ^ m * ((1 / 2 : ℝ) : ℂ) ^ n‖ := norm_tsum_le_tsum_norm hfib
        _ = ∑' m, ‖c n m * ((1 / 2 : ℝ) : ℂ) ^ n * t ^ m‖ :=
          tsum_congr fun m => by congr 1; ring
    · intro x hx
      have hxb := hsmall x hx
      have h0 := hzero x t hxb ht
      rw [(hsum x t hxb ht).of_norm.tsum_prod] at h0
      refine Eq.trans (tsum_congr fun n => ?_) h0
      dsimp only
      rw [← tsum_mul_right]
      exact tsum_congr fun m => by ring
  intro n m
  refine coeff1_zero (a := fun m => c n m) (by norm_num : (0 : ℝ) < 1 / 2) ?_ ?_ m
  · have h1 := (hsum _ _ hhalf hhalf).prod_factor n
    have hne : ‖((1 / 2 : ℝ) : ℂ) ^ n‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact pow_ne_zero _ (by norm_num)
    refine (summable_mul_left_iff hne).1 ?_
    refine h1.congr fun m => ?_
    dsimp only
    rw [← norm_mul]; congr 1; ring
  · intro x hx
    exact hrow x (hsmall x hx) n

/-! ## Facts about `f ∈ 𝒮` and its odd square root `h` -/

theorem neg_in_ball {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) : -s ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.1 hs

theorem sq_in_ball {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) : s ^ 2 ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_pow]
  have h1 := mem_ball_zero_iff.1 hs
  have h0 := norm_nonneg s
  nlinarith

theorem sqrt_in_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : ∃ s ∈ ball (0 : ℂ) 1, s ^ 2 = z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < 2)
  refine ⟨s, ?_, hs⟩
  rw [mem_ball_zero_iff] at hz ⊢
  rw [← hs, norm_pow] at hz
  by_contra hcon
  have h1 := not_lt.1 hcon
  nlinarith

theorem fS_ne_zero {f : ℂ → ℂ} (hf : InS f) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hz0 : z ≠ 0) : f z ≠ 0 :=
  fun hfz => hz0 (hf.injOn hz (mem_ball_self one_pos) (hfz.trans hf.map_zero.symm))

theorem root_ne_zero {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1)
    (hs0 : s ≠ 0) : h s ≠ 0 := by
  intro h0
  have h1 := hh.2.2.1 s hs
  rw [h0] at h1
  exact fS_ne_zero hf (sq_in_ball hs) (pow_ne_zero 2 hs0) (by rw [← h1]; ring)

/-- Differentiating `h(s)² = f(s²)`: `h(s) h'(s) = s f'(s²)`. -/
theorem root_mul_deriv {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    h s * deriv h s = s * deriv f (s ^ 2) := by
  have hdh : DifferentiableAt ℂ h s := hh.1.differentiableAt (isOpen_ball.mem_nhds hs)
  have hdf : DifferentiableAt ℂ f (s ^ 2) :=
    hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds (sq_in_ball hs))
  have h1 := hdh.hasDerivAt.fun_pow 2
  have h2 := hdf.hasDerivAt.comp s (hasDerivAt_pow 2 s)
  have heq : (fun x => f (x ^ 2)) =ᶠ[𝓝 s] (fun x => h x ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds hs] with x hx
    exact (hh.2.2.1 x hx).symm
  have h3 := (h1.congr_of_eventuallyEq heq).unique h2
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, pow_one] at h3
  push_cast at h3
  linear_combination h3 / 2

theorem root_deriv_neg {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    deriv h (-s) = deriv h s := by
  by_cases h0 : s = 0
  · rw [h0, neg_zero]
  · have h1 := root_mul_deriv hf hh (neg_in_ball hs)
    have h2 := root_mul_deriv hf hh hs
    rw [hh.2.1 s hs, neg_sq] at h1
    have h3 : h s * deriv h (-s) = h s * deriv h s := by linear_combination -h1 - h2
    exact mul_left_cancel₀ (root_ne_zero hf hh hs h0) h3

theorem quotA_neg {f h : ℂ → ℂ} (hh : IsOddRoot f h) {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    (if -t = 0 then 1 else -t / h (-t)) = (if t = 0 then 1 else t / h t) := by
  by_cases h0 : t = 0
  · simp [h0]
  · rw [ite_eq_right (neg_ne_zero.2 h0), ite_eq_right h0, hh.2.1 t ht, neg_div_neg_eq]

theorem quotA_ne_zero {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    (if s = 0 then 1 else s / h s) ≠ 0 := by
  by_cases h0 : s = 0
  · simp [h0]
  · rw [ite_eq_right h0]; exact div_ne_zero h0 (root_ne_zero hf hh hs h0)

theorem quotA_sq {f h : ℂ → ℂ} (hh : IsOddRoot f h) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    (if s = 0 then 1 else s / h s) ^ 2 = (if s ^ 2 = 0 then 1 else s ^ 2 / f (s ^ 2)) := by
  by_cases h0 : s = 0
  · simp [h0]
  · rw [ite_eq_right h0, ite_eq_right (pow_ne_zero 2 h0), div_pow, hh.2.2.1 s hs]

/-! ## Identities of the kernel quotient -/

/-- `h` odd: `K(-s, -t) = K(s, t)` at the level of the quotient under the logarithm. -/
theorem kq_neg {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1)
    (ht : t ∈ ball (0 : ℂ) 1) : kernelQuot h (-s) (-t) = kernelQuot h s t := by
  have hX : (if -s = -t then deriv h (-s) else (h (-s) - h (-t)) / (-s - -t)) =
      (if s = t then deriv h s else (h s - h t) / (s - t)) := by
    by_cases hst : s = t
    · subst hst
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact root_deriv_neg hf hh hs
    · rw [ite_eq_right (fun e => hst (neg_inj.1 e)), ite_eq_right hst, hh.2.1 s hs, hh.2.1 t ht,
        show -h s - -h t = -(h s - h t) by ring, show -s - -t = -(s - t) by ring, neg_div_neg_eq]
  unfold kernelQuot
  rw [quotA_neg hh hs, quotA_neg hh ht, hX]

/-- For `s ≠ ±t`: `K(s,t)/K(s,-t) = ((h(s) - h(t))/(h(s) + h(t))) ((s + t)/(s - t))`. -/
theorem kq_ratio {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1)
    (ht : t ∈ ball (0 : ℂ) 1) (hst : s ≠ t) (hst' : s ≠ -t) :
    kernelQuot h s t / kernelQuot h s (-t) = (h s - h t) / (h s + h t) * ((s + t) / (s - t)) := by
  unfold kernelQuot
  rw [ite_eq_right hst, ite_eq_right hst', quotA_neg hh ht, hh.2.1 t ht]
  have hA := quotA_ne_zero hf hh hs
  have hB := quotA_ne_zero hf hh ht
  rw [mul_div_mul_right _ _ hB, mul_div_mul_right _ _ hA, sub_neg_eq_add, sub_neg_eq_add, div_div_div_eq,
    div_mul_div_comm, mul_comm (s - t)]

/-- On the diagonal: `K(s,s) K(s,-s) = K_f(s², s²)`. -/
theorem kq_diag {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    kernelQuot h s s * kernelQuot h s (-s) = kernelQuot f (s ^ 2) (s ^ 2) := by
  by_cases h0 : s = 0
  · subst h0; simp [kernelQuot, hh.2.2.2, hf.deriv_zero]
  · have hhs := root_ne_zero hf hh hs h0
    have hdf : deriv f (s ^ 2) = h s * deriv h s / s := by
      rw [eq_div_iff h0, root_mul_deriv hf hh hs]; ring
    have hss : s ≠ -s := fun e => h0 (by linear_combination e / 2)
    have h2s : s + s ≠ 0 := by rw [← two_mul]; exact mul_ne_zero two_ne_zero h0
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 h0
    unfold kernelQuot
    rw [ite_eq_left (rfl : s = s), ite_eq_left (rfl : s ^ 2 = s ^ 2), ite_eq_right hss, ite_eq_right h0,
      ite_eq_right (neg_ne_zero.2 h0), ite_eq_right hs2, hh.2.1 s hs, hdf, ← hh.2.2.1 s hs, sub_neg_eq_add,
      sub_neg_eq_add, neg_div_neg_eq]
    field_simp

/-- `K_h(s,t) K_h(s,-t) = K_f(s², t²)` on the bidisc, the quotient version of Lemma 3.1(ii). -/
theorem kq_mul {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1)
    (ht : t ∈ ball (0 : ℂ) 1) : kernelQuot h s t * kernelQuot h s (-t) = kernelQuot f (s ^ 2) (t ^ 2) := by
  by_cases hst : s = t
  · subst hst; exact kq_diag hf hh hs
  by_cases hst' : s = -t
  · subst hst'
    have hd := kq_diag hf hh hs
    rw [neg_neg, neg_sq] at hd
    rw [neg_sq, mul_comm (kernelQuot h (-t) t)]
    exact hd
  have hsq : s ^ 2 ≠ t ^ 2 := by
    intro e
    have hp : (s - t) * (s + t) = 0 := by linear_combination e
    rcases mul_eq_zero.1 hp with h1 | h1
    · exact hst (sub_eq_zero.1 h1)
    · exact hst' (by linear_combination h1)
  have h1 : s - t ≠ 0 := sub_ne_zero.2 hst
  have h2 : s + t ≠ 0 := fun e => hst' (by linear_combination e)
  have h3 : s ^ 2 - t ^ 2 ≠ 0 := sub_ne_zero.2 hsq
  unfold kernelQuot
  rw [ite_eq_right hst, ite_eq_right hst', ite_eq_right hsq, quotA_neg hh ht, hh.2.1 t ht, ← quotA_sq hh hs, ← quotA_sq hh ht,
    ← hh.2.2.1 s hs, ← hh.2.2.1 t ht, sub_neg_eq_add, sub_neg_eq_add]
  generalize (if s = 0 then 1 else s / h s) = A
  generalize (if t = 0 then 1 else t / h t) = B
  field_simp
  ring

/-- `K_h(s,s)/K_h(s,-s) = p(s²)`, the quotient version of Lemma 3.1(iii). -/
theorem kq_diag_ratio {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {s : ℂ}
    (hs : s ∈ ball (0 : ℂ) 1) : kernelQuot h s s / kernelQuot h s (-s) = pfun f (s ^ 2) := by
  by_cases h0 : s = 0
  · subst h0; simp [kernelQuot, pfun, hh.2.2.2]
  · have hhs := root_ne_zero hf hh hs h0
    have hdf : deriv f (s ^ 2) = h s * deriv h s / s := by
      rw [eq_div_iff h0, root_mul_deriv hf hh hs]; ring
    have hss : s ≠ -s := fun e => h0 (by linear_combination e / 2)
    have h2s : s + s ≠ 0 := by rw [← two_mul]; exact mul_ne_zero two_ne_zero h0
    unfold kernelQuot pfun
    rw [ite_eq_left (rfl : s = s), ite_eq_right hss, ite_eq_right h0, ite_eq_right (neg_ne_zero.2 h0),
      ite_eq_right (pow_ne_zero 2 h0), hh.2.1 s hs, hdf, ← hh.2.2.1 s hs, sub_neg_eq_add, sub_neg_eq_add, neg_div_neg_eq]
    field_simp

/-! ## The parity of the Grunsky coefficients of the odd root -/

theorem kser_negneg {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ}
    (hγ : IsGrunskyCoeff h γ) :
    ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 → kser γ (-s) (-t) = kser γ s t := by
  have hD := exp_one_const bidisc_open bidisc_preconn
    (D := fun p : ℂ × ℂ => kser γ (-p.1) (-p.2) - kser γ p.1 p.2)
    ((kser_comp_contOn (S := ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) hγ (u := fun p => -p.1) (v := fun p => -p.2)
        (by fun_prop) (by fun_prop) fun p hp => ⟨neg_in_ball hp.1, neg_in_ball hp.2⟩).sub
      (kser_comp_contOn (S := ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) hγ (u := fun p => p.1) (v := fun p => p.2)
        (by fun_prop) (by fun_prop) fun p hp => ⟨hp.1, hp.2⟩))
    (fun p hp => by
      have e1 := (hγ.2 _ _ (neg_in_ball hp.1) (neg_in_ball hp.2)).2
      have e2 := (hγ.2 _ _ hp.1 hp.2).2
      have hne : kernelQuot h p.1 p.2 ≠ 0 := e2 ▸ exp_ne_zero _
      simp only [exp_sub, e1, e2, kq_neg hf hh hp.1 hp.2, div_self hne])
    origin_in_bidisc (by simp [kser_zero_fst (fun m => hγ.1 0 m (Or.inl rfl))])
  intro s t hs ht
  exact sub_eq_zero.1 (hD (s, t) ⟨hs, ht⟩)

/-- `γ_{nm}(h) = 0` unless `n + m` is even. -/
theorem root_parity {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ}
    (hγ : IsGrunskyCoeff h γ) : ∀ n m : ℕ, (n + m) % 2 = 1 → γ n m = 0 := by
  have hsum : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      Summable fun nm : ℕ × ℕ => ‖γ nm.1 nm.2 * ((-1) ^ (nm.1 + nm.2) - 1) * s ^ nm.1 * t ^ nm.2‖ := by
    intro s t hs ht
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun nm => ?_)
      ((hγ.2 s t hs ht).1.mul_left 2)
    have hb : ‖((-1 : ℂ)) ^ (nm.1 + nm.2) - 1‖ ≤ 2 := by
      calc _ ≤ ‖((-1 : ℂ)) ^ (nm.1 + nm.2)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, norm_neg, norm_one, one_pow]; norm_num
    calc ‖γ nm.1 nm.2 * ((-1) ^ (nm.1 + nm.2) - 1) * s ^ nm.1 * t ^ nm.2‖
        = ‖((-1 : ℂ)) ^ (nm.1 + nm.2) - 1‖ * ‖γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖ := by
          rw [← norm_mul]; congr 1; ring
      _ ≤ 2 * ‖γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2‖ := by gcongr
  have hzero : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      ∑' nm : ℕ × ℕ, γ nm.1 nm.2 * ((-1) ^ (nm.1 + nm.2) - 1) * s ^ nm.1 * t ^ nm.2 = 0 := by
    intro s t hs ht
    have e := kser_negneg hf hh hγ s t hs ht
    unfold kser at e
    rw [← sub_eq_zero, ← (hγ.2 _ _ (neg_in_ball hs) (neg_in_ball ht)).1.of_norm.tsum_sub
      (hγ.2 s t hs ht).1.of_norm] at e
    refine Eq.trans (tsum_congr fun nm => ?_) e
    rw [neg_pow s, neg_pow t, pow_add]; ring
  have hc := coeff2_zero (c := fun n m => γ n m * ((-1) ^ (n + m) - 1)) hsum hzero
  intro n m hnm
  have h1 := hc n m
  have h2 : ((-1 : ℂ)) ^ (n + m) = -1 := Odd.neg_one_pow (Nat.odd_iff.2 hnm)
  simp only [h2] at h1
  have h3 : (-1 - 1 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.1 h1).resolve_right h3

/-! ## The odd and even blocks -/

theorem oddTerm {γ : ℕ → ℕ → ℂ} (s t : ℂ) (n m : ℕ) :
    aOdd s n * (Oblock γ n m * aOdd t m) =
      if n % 2 = 1 ∧ m % 2 = 1 then γ n m * s ^ n * t ^ m else 0 := by
  unfold aOdd Oblock Cmat
  by_cases hn : n % 2 = 1
  · by_cases hm : m % 2 = 1
    · rw [ite_eq_left hn, ite_eq_left hm, ite_eq_left (And.intro hn hm), ite_eq_left (And.intro hn hm)]
      have hn0 : n ≠ 0 := by omega
      have hm0 : m ≠ 0 := by omega
      exact sqrt_term_eq hn0 hm0 _ _ _
    · simp [hm]
  · simp [hn]

theorem evenTerm {γ : ℕ → ℕ → ℂ} (h0 : ∀ n m : ℕ, n = 0 ∨ m = 0 → γ n m = 0) (s t : ℂ) (n m : ℕ) :
    aEven s n * (Eblock γ n m * aEven t m) =
      if n % 2 = 0 ∧ m % 2 = 0 then γ n m * s ^ n * t ^ m else 0 := by
  unfold aEven Eblock Cmat
  by_cases hn : n % 2 = 0
  · by_cases hm : m % 2 = 0
    · rw [ite_eq_left (And.intro hn hm)]
      by_cases hn0 : n = 0
      · simp [hn0, h0]
      by_cases hm0 : m = 0
      · simp [hm0, h0]
      rw [ite_eq_left (And.intro hn hn0), ite_eq_left (And.intro hm hm0),
        ite_eq_left (And.intro hn (And.intro hn0 (And.intro hm hm0)))]
      exact sqrt_term_eq hn0 hm0 _ _ _
    · simp [hm]
  · simp [hn]

theorem alphaTerm {γ : ℕ → ℕ → ℂ} (h0 : ∀ n m : ℕ, n = 0 ∨ m = 0 → γ n m = 0) (z w : ℂ) (n m : ℕ) :
    alphaV z n * (Cmat γ n m * alphaV w m) = γ n m * z ^ n * w ^ m := by
  unfold alphaV Cmat
  by_cases hn : n = 0
  · simp [hn, h0]
  by_cases hm : m = 0
  · simp [hm, h0]
  rw [ite_eq_right hn, ite_eq_right hm]
  exact sqrt_term_eq hn hm _ _ _

theorem blockSums {h : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ) {s t : ℂ}
    (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    HasSum (fun nm : ℕ × ℕ => if nm.1 % 2 = 1 ∧ nm.2 % 2 = 1 then γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 else 0)
        (bilinf (aOdd s) (Oblock γ) (aOdd t)) ∧
      HasSum (fun nm : ℕ × ℕ => if nm.1 % 2 = 0 ∧ nm.2 % 2 = 0 then γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 else 0)
        (bilinf (aEven s) (Eblock γ) (aEven t)) := by
  have hS := (hγ.2 s t hs ht).1
  constructor
  · refine bilinf_hasSum ?_ (fun n m => oddTerm s t n m)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun nm => ?_) hS
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  · refine bilinf_hasSum ?_ (fun n m => evenTerm hγ.1 s t n m)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun nm => ?_) hS
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _

theorem oddDiff {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ)
    {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) := by
  have hpar := root_parity hf hh hγ
  unfold kser
  rw [← (hγ.2 s t hs ht).1.of_norm.tsum_sub (hγ.2 s (-t) hs (neg_in_ball ht)).1.of_norm,
    ← (blockSums hγ hs ht).1.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun nm => ?_
  obtain ⟨n, m⟩ := nm
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · rw [Even.neg_pow (Nat.even_iff.2 hm), ite_eq_right (by omega)]; ring
  · rw [Odd.neg_pow (Nat.odd_iff.2 hm)]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [hpar n m (by omega), ite_eq_right (by omega)]; ring
    · rw [ite_eq_left (And.intro hn hm)]; ring

theorem evenSum {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ)
    {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    2 * bilinf (aEven s) (Eblock γ) (aEven t) = kser γ s t + kser γ s (-t) := by
  have hpar := root_parity hf hh hγ
  unfold kser
  rw [← (hγ.2 s t hs ht).1.of_norm.tsum_add (hγ.2 s (-t) hs (neg_in_ball ht)).1.of_norm,
    ← (blockSums hγ hs ht).2.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun nm => ?_
  obtain ⟨n, m⟩ := nm
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · rw [Even.neg_pow (Nat.even_iff.2 hm)]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [ite_eq_left (And.intro hn hm)]; ring
    · rw [hpar n m (by omega), ite_eq_right (by omega)]; ring
  · rw [Odd.neg_pow (Nat.odd_iff.2 hm), ite_eq_right (by omega)]; ring

/-- `K_h(s,t) + K_h(s,-t) = K_f(s², t²)`: both sides are continuous on the bidisc, vanish at the origin, and have
the same exponential. -/
theorem kserSumEq {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ γf : ℕ → ℕ → ℂ}
    (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) :
    ∀ s t : ℂ, s ∈ ball (0 : ℂ) 1 → t ∈ ball (0 : ℂ) 1 →
      kser γ s t + kser γ s (-t) = kser γf (s ^ 2) (t ^ 2) := by
  have hD := exp_one_const bidisc_open bidisc_preconn
    (D := fun p : ℂ × ℂ => kser γ p.1 p.2 + kser γ p.1 (-p.2) - kser γf (p.1 ^ 2) (p.2 ^ 2))
    (((kser_comp_contOn (S := ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) hγ (u := fun p => p.1) (v := fun p => p.2)
        (by fun_prop) (by fun_prop) fun p hp => ⟨hp.1, hp.2⟩).add
      (kser_comp_contOn (S := ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) hγ (u := fun p => p.1) (v := fun p => -p.2)
        (by fun_prop) (by fun_prop) fun p hp => ⟨hp.1, neg_in_ball hp.2⟩)).sub
      (kser_comp_contOn (S := ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) hγf (u := fun p => p.1 ^ 2)
        (v := fun p => p.2 ^ 2) (by fun_prop) (by fun_prop) fun p hp => ⟨sq_in_ball hp.1, sq_in_ball hp.2⟩))
    (fun p hp => by
      have e1 := (hγ.2 _ _ hp.1 hp.2).2
      have e2 := (hγ.2 _ _ hp.1 (neg_in_ball hp.2)).2
      have e3 := (hγf.2 _ _ (sq_in_ball hp.1) (sq_in_ball hp.2)).2
      have hne : kernelQuot f (p.1 ^ 2) (p.2 ^ 2) ≠ 0 := e3 ▸ exp_ne_zero _
      simp only [exp_sub, exp_add, e1, e2, e3, kq_mul hf hh hp.1 hp.2, div_self hne])
    origin_in_bidisc (by simp [kser_zero_fst (fun m => hγ.1 0 m (Or.inl rfl)),
      kser_zero_fst (fun m => hγf.1 0 m (Or.inl rfl))])
  intro s t hs ht
  exact sub_eq_zero.1 (hD (s, t) ⟨hs, ht⟩)

/-! ## The even block is the Grunsky matrix of `f` -/

theorem double_inj : Function.Injective (fun nm : ℕ × ℕ => (2 * nm.1, 2 * nm.2)) := by
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext (by omega) (by omega)

/-- `∑_{n,m} γ_{2n,2m}(h) zⁿ wᵐ = a_e(s)ᵀ E a_e(t)` for `z = s²`, `w = t²`. -/
theorem evenReindex {h : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ) {s t : ℂ}
    (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    HasSum (fun nm : ℕ × ℕ => γ (2 * nm.1) (2 * nm.2) * (s ^ 2) ^ nm.1 * (t ^ 2) ^ nm.2)
      (bilinf (aEven s) (Eblock γ) (aEven t)) := by
  have hsupp : ∀ x : ℕ × ℕ, x ∉ Set.range (fun nm : ℕ × ℕ => (2 * nm.1, 2 * nm.2)) →
      (fun nm : ℕ × ℕ => if nm.1 % 2 = 0 ∧ nm.2 % 2 = 0 then γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 else 0) x = 0 := by
    rintro ⟨n, m⟩ hnm
    dsimp only
    rw [ite_eq_right]
    rintro ⟨hn, hm⟩
    exact hnm ⟨(n / 2, m / 2), by simp only [Prod.mk.injEq]; omega⟩
  have key := (double_inj.hasSum_iff hsupp).2 (blockSums hγ hs ht).2
  convert key using 1
  funext nm
  simp only [Function.comp_apply]
  rw [ite_eq_left (show 2 * nm.1 % 2 = 0 ∧ 2 * nm.2 % 2 = 0 by omega), pow_mul, pow_mul]

/-- `2 γ_{2n,2m}(h) = γ_{nm}(f)`, by comparing the coefficients of Lemma 3.1(ii). -/
theorem coeffEven {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) {γ γf : ℕ → ℕ → ℂ}
    (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) : ∀ n m : ℕ, 2 * γ (2 * n) (2 * m) = γf n m := by
  have hsum : ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
      Summable fun nm : ℕ × ℕ => ‖(2 * γ (2 * nm.1) (2 * nm.2) - γf nm.1 nm.2) * z ^ nm.1 * w ^ nm.2‖ := by
    intro z w hz hw
    obtain ⟨s, hs, rfl⟩ := sqrt_in_ball hz
    obtain ⟨t, ht, rfl⟩ := sqrt_in_ball hw
    have hX : Summable fun nm : ℕ × ℕ => ‖γ (2 * nm.1) (2 * nm.2) * (s ^ 2) ^ nm.1 * (t ^ 2) ^ nm.2‖ :=
      ((hγ.2 s t hs ht).1.comp_injective double_inj).congr fun nm => by
        simp only [Function.comp_apply, pow_mul]
    have hG1 : Summable fun nm : ℕ × ℕ =>
        ‖2 * (γ (2 * nm.1) (2 * nm.2) * (s ^ 2) ^ nm.1 * (t ^ 2) ^ nm.2)‖ :=
      (hX.mul_left ‖(2 : ℂ)‖).congr fun nm => (norm_mul _ _).symm
    have h2 := (hγf.2 _ _ hz hw).1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun nm => ?_) (hG1.add h2)
    calc _ = ‖2 * (γ (2 * nm.1) (2 * nm.2) * (s ^ 2) ^ nm.1 * (t ^ 2) ^ nm.2) -
          γf nm.1 nm.2 * (s ^ 2) ^ nm.1 * (t ^ 2) ^ nm.2‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hzero : ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
      ∑' nm : ℕ × ℕ, (2 * γ (2 * nm.1) (2 * nm.2) - γf nm.1 nm.2) * z ^ nm.1 * w ^ nm.2 = 0 := by
    intro z w hz hw
    obtain ⟨s, hs, rfl⟩ := sqrt_in_ball hz
    obtain ⟨t, ht, rfl⟩ := sqrt_in_ball hw
    have hE := evenReindex hγ hs ht
    have hF := (hγf.2 _ _ hz hw).1.of_norm
    have e1 := (hE.mul_left 2).sub hF.hasSum
    have e2 := (evenSum hf hh hγ hs ht).trans (kserSumEq hf hh hγ hγf s t hs ht)
    unfold kser at e2
    rw [e2, sub_self] at e1
    exact (tsum_congr fun nm => by ring).trans e1.tsum_eq
  intro n m
  exact sub_eq_zero.1 (coeff2_zero (c := fun n m => 2 * γ (2 * n) (2 * m) - γf n m) hsum hzero n m)

end Lem31

open Lem31

/-! ## The rows -/

set_option linter.unusedVariables false in
theorem sec3_block_sums_proved (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff h γ) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    HasSum (fun nm : ℕ × ℕ => if nm.1 % 2 = 1 ∧ nm.2 % 2 = 1 then γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 else 0)
        (bilinf (aOdd s) (Oblock γ) (aOdd t)) ∧
      HasSum (fun nm : ℕ × ℕ => if nm.1 % 2 = 0 ∧ nm.2 % 2 = 0 then γ nm.1 nm.2 * s ^ nm.1 * t ^ nm.2 else 0)
        (bilinf (aEven s) (Eblock γ) (aEven t)) :=
  blockSums hγ hs ht

theorem lem_3_1_i_proved (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff h γ) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1) :
    2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
      (s ≠ t → s ≠ -t →
        exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))) := by
  have h1 := oddDiff hf hh hγ hs ht
  refine ⟨h1, fun hst hst' => ?_⟩
  rw [h1, exp_sub, (hγ.2 s t hs ht).2, (hγ.2 s (-t) hs (neg_in_ball ht)).2]
  exact kq_ratio hf hh hs ht hst hst'

theorem lem_3_1_ii_proved (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1)
    (ht : t ∈ ball (0 : ℂ) 1) :
    2 * bilinf (aEven s) (Eblock γ) (aEven t) = kser γ s t + kser γ s (-t) ∧
      kser γ s t + kser γ s (-t) = kser γf (s ^ 2) (t ^ 2) :=
  ⟨evenSum hf hh hγ hs ht, kserSumEq hf hh hγ hγf s t hs ht⟩

theorem lem_3_1_iii_proved (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff h γ) :
    ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
      2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
      ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2) := by
  have hcont : ContinuousOn (fun s : ℂ => kser γ s s - kser γ s (-s)) (ball (0 : ℂ) 1) :=
    (kser_comp_contOn (S := ball (0 : ℂ) 1) hγ (u := fun s => s) (v := fun s => s) (by fun_prop)
        (by fun_prop) fun s hs => ⟨hs, hs⟩).sub
      (kser_comp_contOn (S := ball (0 : ℂ) 1) hγ (u := fun s => s) (v := fun s => -s) (by fun_prop)
        (by fun_prop) fun s hs => ⟨hs, neg_in_ball hs⟩)
  refine ⟨hcont.congr fun s hs => oddDiff hf hh hγ hs hs, ?_, fun s hs => ?_⟩
  · rw [oddDiff hf hh hγ (mem_ball_self one_pos) (mem_ball_self one_pos), neg_zero, sub_self]
  · rw [oddDiff hf hh hγ hs hs, exp_sub, (hγ.2 s s hs hs).2, (hγ.2 s (-s) hs (neg_in_ball hs)).2]
    exact kq_diag_ratio hf hh hs

theorem eq_Kf_proved (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) :
    (∀ n m : ℕ, Eblock γ (2 * n) (2 * m) = Cmat γf n m) ∧
      ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
        kser γf z w = bilinf (alphaV z) (Cmat γf) (alphaV w) := by
  refine ⟨fun n m => ?_, fun z w hz hw => ?_⟩
  · have hc := coeffEven hf hh hγ hγf n m
    unfold Eblock Cmat
    by_cases hn : n = 0
    · subst hn; simp [hγf.1 0 m (Or.inl rfl)]
    by_cases hm : m = 0
    · subst hm; simp [hγf.1 n 0 (Or.inr rfl)]
    rw [ite_eq_left (And.intro (by omega) (And.intro (by omega) (And.intro (by omega) (by omega))))]
    have hsq : Real.sqrt (((2 * n : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ)) = 2 * Real.sqrt ((n : ℝ) * m) := by
      rw [show (((2 * n : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ)) = 2 ^ 2 * ((n : ℝ) * m) by push_cast; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [hsq, ← hc]
    push_cast
    ring
  · unfold kser
    exact (bilinf_hasSum (hγf.2 z w hz hw).1 fun n m => alphaTerm hγf.1 z w n m).tsum_eq

end Robinson.Proofs
