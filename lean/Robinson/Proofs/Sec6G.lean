/-
Robinson/Proofs/Sec6G.lean — proofs of lem_6_3, sec6_barnard_series, sec6_Rf_bound, sec6_logp_logq,
eq_psum.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Matrix2
import Robinson.Defs.Far
import Robinson.Defs.Grunsky
import Robinson.NotFormalized
import Robinson.ComputerChecked
import Robinson.Proofs.Arith

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## Weighted summability of the Grunsky series -/

/-- For `0 ≤ r < 1` the sequence `n rⁿ` is bounded. -/
private lemma nat_mul_pow_bdd {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, (n : ℝ) * r ^ n ≤ K := by
  have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖r‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
    simpa using this
  refine ⟨∑' n : ℕ, (n : ℝ) * r ^ n, tsum_nonneg (fun n => by positivity), fun n => ?_⟩
  exact hs.le_tsum n (fun m _ => by positivity)

/-- The series `∑ n |γ_{nm}| |z|ⁿ |w|ᵐ` converges on the bidisc. -/
private lemma weighted_summable {f : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff f γ) {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : w ∈ ball (0 : ℂ) 1) :
    Summable (fun nm : ℕ × ℕ => (nm.1 : ℝ) * ‖γ nm.1 nm.2‖ * ‖z‖ ^ nm.1 * ‖w‖ ^ nm.2) := by
  set ρ : ℝ := (‖z‖ + 1) / 2 with hρ
  have hρ0 : 0 < ρ := by have := norm_nonneg z; rw [hρ]; linarith
  have hzρ : ‖z‖ < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  obtain ⟨K, hK0, hK⟩ := nat_mul_pow_bdd (r := ‖z‖ / ρ) (by positivity) ((div_lt_one hρ0).2 hzρ)
  have hρb : (ρ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1
  have hs := ((hγ.2 (ρ : ℂ) w hρb hw).1).mul_left K
  refine Summable.of_nonneg_of_le (fun nm => by positivity) (fun nm => ?_) hs
  have hn : (nm.1 : ℝ) * ‖z‖ ^ nm.1 ≤ K * ρ ^ nm.1 := by
    have h := hK nm.1
    rw [div_pow, mul_div_assoc'] at h
    rwa [div_le_iff₀ (by positivity)] at h
  have e : ‖γ nm.1 nm.2 * (ρ : ℂ) ^ nm.1 * w ^ nm.2‖ = ‖γ nm.1 nm.2‖ * ρ ^ nm.1 * ‖w‖ ^ nm.2 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  rw [e]
  have h1 : 0 ≤ ‖γ nm.1 nm.2‖ * ‖w‖ ^ nm.2 := by positivity
  calc (nm.1 : ℝ) * ‖γ nm.1 nm.2‖ * ‖z‖ ^ nm.1 * ‖w‖ ^ nm.2
      = ((nm.1 : ℝ) * ‖z‖ ^ nm.1) * (‖γ nm.1 nm.2‖ * ‖w‖ ^ nm.2) := by ring
    _ ≤ (K * ρ ^ nm.1) * (‖γ nm.1 nm.2‖ * ‖w‖ ^ nm.2) := mul_le_mul_of_nonneg_right hn h1
    _ = K * (‖γ nm.1 nm.2‖ * ρ ^ nm.1 * ‖w‖ ^ nm.2) := by ring

/-! ## The derivative of the Grunsky series in the first variable -/

/-- Term by term differentiation of `s ↦ ∑ γ_{nm} sⁿ wᵐ`. -/
private lemma kser_hasDerivAt {f : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff f γ) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun y => kser γ y w)
      (∑' nm : ℕ × ℕ, γ nm.1 nm.2 * ((nm.1 : ℂ) * z ^ (nm.1 - 1)) * w ^ nm.2) z := by
  rw [mem_ball_zero_iff] at hz
  set ρ : ℝ := (‖z‖ + 1) / 2 with hρ
  have hρ0 : 0 < ρ := by have := norm_nonneg z; rw [hρ]; linarith
  have hzρ : ‖z‖ < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρn : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hu := (weighted_summable hγ (z := (ρ : ℂ)) (by rw [hρn]; exact hρ1) hw).mul_left ρ⁻¹
  refine hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball (0 : ℂ) ρ).isPreconnected
    (fun nm y _ => ((hasDerivAt_pow nm.1 y).const_mul (γ nm.1 nm.2)).mul_const (w ^ nm.2))
    (fun nm y hy => ?_) (mem_ball_zero_iff.2 hzρ) (hγ.2 z w (mem_ball_zero_iff.2 hz) hw).1.of_norm
    (mem_ball_zero_iff.2 hzρ)
  rw [mem_ball_zero_iff] at hy
  simp only [hρn]
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  rcases nm with ⟨_ | k, m⟩
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have hyk : ‖y‖ ^ k ≤ ρ ^ k := pow_le_pow_left₀ (norm_nonneg y) hy.le k
    have e : ρ⁻¹ * (((k : ℝ) + 1) * ‖γ (k + 1) m‖ * ρ ^ (k + 1) * ‖w‖ ^ m) =
        ‖γ (k + 1) m‖ * (((k : ℝ) + 1) * ρ ^ k) * ‖w‖ ^ m := by
      field_simp
      ring
    rw [e]
    have h1 : 0 ≤ ‖γ (k + 1) m‖ := norm_nonneg _
    have h2 : 0 ≤ ‖w‖ ^ m := by positivity
    have h3 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    gcongr

/-- `z ∂_z K(z, w) = ∑ n γ_{nm} zⁿ wᵐ` (the derivative of `kser` multiplied by `z`). -/
private lemma z_mul_deriv_series (γ : ℕ → ℕ → ℂ) (z w : ℂ) :
    z * ∑' nm : ℕ × ℕ, γ nm.1 nm.2 * ((nm.1 : ℂ) * z ^ (nm.1 - 1)) * w ^ nm.2 =
      ∑' nm : ℕ × ℕ, (nm.1 : ℂ) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2 := by
  rw [← tsum_mul_left]
  congr 1
  funext nm
  rcases nm with ⟨_ | k, m⟩
  · simp
  · simp only [Nat.add_sub_cancel]
    ring

/-! ## Lemma 6.3 -/

/-- The value of the derivative identity: for distinct nonzero `z, w ∈ 𝔻`,
`∑ n γ_{nm} zⁿ wᵐ = z f'(z)/(f(z) - f(w)) - z/(z - w) + 1 - z f'(z)/f(z)`. -/
private lemma z_dK_eq {f : ℂ → ℂ} (hf : InS f) {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff f γ) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hzw : z ≠ w) (hz0 : z ≠ 0) (hw0 : w ≠ 0) :
    ∑' nm : ℕ × ℕ, (nm.1 : ℂ) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2 =
      z * deriv f z / (f z - f w) - z / (z - w) + 1 - z * deriv f z / f z := by
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hfzw : f z - f w ≠ 0 := sub_ne_zero.2 (fun h => hzw (hf.injOn hz hw h))
  have hfz : f z ≠ 0 := fun h => hz0 (hf.injOn hz h0b (h.trans hf.map_zero.symm))
  have hfw : f w ≠ 0 := fun h => hw0 (hf.injOn hw h0b (h.trans hf.map_zero.symm))
  have hzw' : z - w ≠ 0 := sub_ne_zero.2 hzw
  have hfd : HasDerivAt f (deriv f z) z :=
    (hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  set D := ∑' nm : ℕ × ℕ, γ nm.1 nm.2 * ((nm.1 : ℂ) * z ^ (nm.1 - 1)) * w ^ nm.2 with hD
  have hK : HasDerivAt (fun y => exp (kser γ y w)) (exp (kser γ z w) * D) z :=
    (kser_hasDerivAt hγ hz hw).cexp
  set Kq : ℂ → ℂ := fun y => (f y - f w) / (y - w) * (y / f y) * (w / f w) with hKq
  have hKqd : HasDerivAt Kq
      (((deriv f z * (z - w) - (f z - f w) * 1) / (z - w) ^ 2 * (z / f z) +
        (f z - f w) / (z - w) * ((1 * f z - z * deriv f z) / f z ^ 2)) * (w / f w)) z := by
    have h1 := (hfd.sub_const (f w)).div ((hasDerivAt_id z).sub_const w) hzw'
    have h2 := (hasDerivAt_id z).div hfd hfz
    exact (h1.mul h2).mul_const (w / f w)
  have hev : Kq =ᶠ[𝓝 z] fun y => exp (kser γ y w) := by
    filter_upwards [isOpen_ball.mem_nhds hz, eventually_ne_nhds hzw, eventually_ne_nhds hz0] with y hy hyw hy0
    rw [(hγ.2 y w hy hw).2, kernelQuot, ite_eq_right hyw, ite_eq_right hy0, ite_eq_right hw0]
  have huniq := (hK.congr_of_eventuallyEq hev).unique hKqd
  have hKz : exp (kser γ z w) = Kq z := by
    rw [(hγ.2 z w hz hw).2, kernelQuot, ite_eq_right hzw, ite_eq_right hz0, ite_eq_right hw0]
  rw [hKz] at huniq
  have hKq0 : Kq z ≠ 0 := by
    simp only [hKq]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero hfzw hzw') (div_ne_zero hz0 hfz)) (div_ne_zero hw0 hfw)
  rw [← z_mul_deriv_series]
  apply mul_left_cancel₀ hKq0
  rw [show Kq z * (z * D) = z * (Kq z * D) by ring, huniq]
  simp only [hKq]
  field_simp
  ring

/-- `β(z)ᵀ C α(w) = ∑ n γ_{nm} zⁿ wᵐ`, termwise. -/
private lemma beta_C_alpha_term {f : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff f γ) (z w : ℂ) (n m : ℕ) :
    betaV z n * (Cmat γ n m * alphaV w m) = (n : ℂ) * γ n m * z ^ n * w ^ m := by
  unfold betaV Cmat alphaV
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm, hγ.1 n 0 (Or.inr rfl)]
  rw [ite_eq_right hn, ite_eq_right hm]
  have hsm : (Real.sqrt m : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hnn : (Real.sqrt n : ℂ) * (Real.sqrt n : ℂ) = n := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]; simp
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Complex.ofReal_mul]
  calc (Real.sqrt n : ℂ) * z ^ n * ((Real.sqrt n : ℂ) * (Real.sqrt m : ℂ) * γ n m * (w ^ m / (Real.sqrt m : ℂ)))
      = ((Real.sqrt n : ℂ) * (Real.sqrt n : ℂ)) * z ^ n * γ n m * w ^ m *
          ((Real.sqrt m : ℂ) / (Real.sqrt m : ℂ)) := by ring
    _ = (n : ℂ) * γ n m * z ^ n * w ^ m := by rw [hnn, div_self hsm]; ring

/-- The series `∑ n γ_{nm} zⁿ wᵐ` converges absolutely. -/
private lemma weighted_summable' {f : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff f γ) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    Summable (fun nm : ℕ × ℕ => (nm.1 : ℂ) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2) := by
  refine Summable.of_norm_bounded (weighted_summable hγ (mem_ball_zero_iff.1 hz) hw) (fun nm => ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]

/-- `β(z)ᵀ C(f) α(w) = ∑_{n,m} n γ_{nm} zⁿ wᵐ` on the bidisc. -/
private lemma bilinf_beta_alpha {f : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff f γ) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    bilinf (betaV z) (Cmat γ) (alphaV w) =
      ∑' nm : ℕ × ℕ, (nm.1 : ℂ) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2 := by
  rw [(weighted_summable' hγ hz hw).tsum_prod, bilinf]
  congr 1
  funext n
  rw [← tsum_mul_left]
  congr 1
  funext m
  exact beta_C_alpha_term hγ z w n m

/-- `β(0) = 0` and `α(0) = 0`. -/
private lemma betaV_zero (n : ℕ) : betaV 0 n = 0 := by
  unfold betaV; split_ifs with h
  · rfl
  · simp [h]

private lemma alphaV_zero (n : ℕ) : alphaV 0 n = 0 := by
  unfold alphaV; split_ifs with h
  · rfl
  · simp [h]

/-- The case `z = 0` of Lemma 6.3: both sides vanish. -/
private lemma lem_6_3_zero {f : ℂ → ℂ} (hf : InS f) (γ : ℕ → ℕ → ℂ) {w : ℂ} (hw0 : w ≠ 0) :
    Q f 0 w - pfun f 0 - pfun f w =
      bilinf (betaV 0) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV 0) := by
  have h1 : bilinf (betaV 0) (Cmat γ) (alphaV w) = 0 := by simp [bilinf, betaV_zero]
  have h2 : bilinf (betaV w) (Cmat γ) (alphaV 0) = 0 := by simp [bilinf, alphaV_zero]
  rw [h1, h2, Q, pfun, pfun, ite_eq_left rfl, ite_eq_right hw0, hf.map_zero]
  ring

theorem lem_6_3_proved (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hzw : z ≠ w) :
    Q f z w - pfun f z - pfun f w =
      bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z) := by
  by_cases hz0 : z = 0
  · subst hz0; exact lem_6_3_zero hf γ (Ne.symm hzw)
  by_cases hw0 : w = 0
  · subst hw0
    rw [add_comm, ← lem_6_3_zero hf γ hz0, Q, Q, pfun, pfun, ite_eq_left rfl, ite_eq_right hz0, hf.map_zero]
    ring
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hfzw : f z - f w ≠ 0 := sub_ne_zero.2 (fun h => hzw (hf.injOn hz hw h))
  have hfwz : f w - f z ≠ 0 := sub_ne_zero.2 (fun h => hzw (hf.injOn hw hz h).symm)
  have hzw' : z - w ≠ 0 := sub_ne_zero.2 hzw
  have hwz' : w - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzw)
  rw [bilinf_beta_alpha hγ hz hw, bilinf_beta_alpha hγ hw hz, z_dK_eq hf hγ hz hw hzw hz0 hw0,
    z_dK_eq hf hγ hw hz (Ne.symm hzw) hw0 hz0, Q, pfun, pfun, ite_eq_right hz0, ite_eq_right hw0]
  field_simp
  ring

/-! ## Barnard's series -/

/-- The kernel quotient is symmetric in its two variables. -/
private lemma kernelQuot_symm (g : ℂ → ℂ) (s t : ℂ) : kernelQuot g s t = kernelQuot g t s := by
  unfold kernelQuot
  by_cases h : s = t
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    have e : (g s - g t) / (s - t) = (g t - g s) / (t - s) := by
      rw [← neg_sub (g t), ← neg_sub t, neg_div_neg_eq]
    rw [e]; ring

/-- The transposed family `γ_{mn}` again has the property `IsGrunskyCoeff`. -/
private lemma isGrunskyCoeff_swap {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) :
    IsGrunskyCoeff g (fun n m => γ m n) := by
  refine ⟨fun n m h => hγ.1 m n h.symm, fun s t hs ht => ?_⟩
  obtain ⟨hsum, hexp⟩ := hγ.2 t s ht hs
  refine ⟨?_, ?_⟩
  · refine ((Equiv.prodComm ℕ ℕ).summable_iff.2 hsum).congr (fun nm => ?_)
    simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring_nf
  · have e : kser (fun n m => γ m n) s t = kser γ t s := by
      unfold kser
      rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
      congr 1
      funext nm
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      ring
    rw [e, hexp, kernelQuot_symm]

/-- `∑ m γ_{nm} zⁿ wᵐ` written through the swap of indices. -/
private lemma swap_series {γ : ℕ → ℕ → ℂ} (hsym : ∀ n m, γ n m = γ m n) (z w : ℂ) (nm : ℕ × ℕ) :
    (fun nm : ℕ × ℕ => (nm.1 : ℂ) * γ nm.1 nm.2 * w ^ nm.1 * z ^ nm.2) (Equiv.prodComm ℕ ℕ nm) =
      (nm.2 : ℂ) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2 := by
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [hsym nm.2 nm.1]
  ring

/-- Barnard's series, given that the Grunsky coefficients are unique (`sec3_grunsky_unique`). -/
theorem sec6_barnard_series_proved_from
    (hU : ∀ (g : ℂ → ℂ), InS g → ∀ (γ γ' : ℕ → ℕ → ℂ), IsGrunskyCoeff g γ → IsGrunskyCoeff g γ' →
      γ = γ')
    (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z) =
      ∑' nm : ℕ × ℕ, ((nm.1 : ℂ) + nm.2) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2 := by
  have hsym : ∀ n m, γ n m = γ m n := fun n m =>
    congrFun (congrFun (hU f hf γ _ hγ (isGrunskyCoeff_swap hγ)) n) m
  have h2 : ∑' nm : ℕ × ℕ, (nm.1 : ℂ) * γ nm.1 nm.2 * w ^ nm.1 * z ^ nm.2 =
      ∑' nm : ℕ × ℕ, (nm.2 : ℂ) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2 := by
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
    exact tsum_congr (swap_series hsym z w)
  have hs2 : Summable (fun nm : ℕ × ℕ => (nm.2 : ℂ) * γ nm.1 nm.2 * z ^ nm.1 * w ^ nm.2) :=
    ((Equiv.prodComm ℕ ℕ).summable_iff.2 (weighted_summable' hγ hw hz)).congr (swap_series hsym z w)
  rw [bilinf_beta_alpha hγ hz hw, bilinf_beta_alpha hγ hw hz, h2, ← (weighted_summable' hγ hz hw).tsum_add hs2]
  exact tsum_congr (fun nm => by ring)

/-! ## The points `z_θ` -/

private lemma norm_zθ (θ : ℝ) : ‖zθ θ‖ = 1 / 2 := by
  unfold zθ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, norm_one, Complex.norm_ofNat]

private lemma zθ_mem_ball (θ : ℝ) : zθ θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_zθ]; norm_num

private lemma conj_zθ_mem_ball (θ : ℝ) : conj (zθ θ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_conj, norm_zθ]; norm_num

private lemma im_zθ (θ : ℝ) : (zθ θ).im = Real.sin (θ / 2) / 2 := by
  unfold zθ
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp
  ring

private lemma im_zθ_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < (zθ θ).im := by
  rw [im_zθ]
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

private lemma zθ_ne_conj {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : zθ θ ≠ conj (zθ θ) := by
  intro h
  have him : (zθ θ).im = 0 := conj_eq_iff_im.mp h.symm
  linarith [im_zθ_pos h0 hπ]

private lemma far_range {θ : ℝ} (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) : 0 < θ ∧ θ ≤ Real.pi := by
  unfold deg at h1 h2
  constructor
  · nlinarith [Real.pi_pos]
  · linarith

/-! ## Bilinear algebra with `C(g)` on `ℓ²` -/

/-- Expansion of `xᵀ C y` for linear combinations, given the convergence statements of (eq:cauchy). -/
private lemma bilinf_expand {γ : ℕ → ℕ → ℂ}
    (hC : ∀ x y : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
      (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
        ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2))
    {x1 x2 y1 y2 : ℕ → ℂ} (hx1 : Summable (fun n => ‖x1 n‖ ^ 2)) (hx2 : Summable (fun n => ‖x2 n‖ ^ 2))
    (hy1 : Summable (fun n => ‖y1 n‖ ^ 2)) (hy2 : Summable (fun n => ‖y2 n‖ ^ 2)) (c1 c2 d1 d2 : ℂ) :
    bilinf (fun n => c1 * x1 n + c2 * x2 n) (Cmat γ) (fun n => d1 * y1 n + d2 * y2 n) =
      c1 * d1 * bilinf x1 (Cmat γ) y1 + c1 * d2 * bilinf x1 (Cmat γ) y2 +
        c2 * d1 * bilinf x2 (Cmat γ) y1 + c2 * d2 * bilinf x2 (Cmat γ) y2 := by
  obtain ⟨i11, o11, -⟩ := hC x1 y1 hx1 hy1
  obtain ⟨i12, o12, -⟩ := hC x1 y2 hx1 hy2
  obtain ⟨-, o21, -⟩ := hC x2 y1 hx2 hy1
  obtain ⟨-, o22, -⟩ := hC x2 y2 hx2 hy2
  have hin : ∀ n, ∑' m, Cmat γ n m * (d1 * y1 m + d2 * y2 m) =
      d1 * ∑' m, Cmat γ n m * y1 m + d2 * ∑' m, Cmat γ n m * y2 m := by
    intro n
    rw [← tsum_mul_left, ← tsum_mul_left, ← ((i11 n).mul_left d1).tsum_add ((i12 n).mul_left d2)]
    exact tsum_congr (fun m => by ring)
  have H := (((o11.hasSum.mul_left (c1 * d1)).add (o12.hasSum.mul_left (c1 * d2))).add
    (o21.hasSum.mul_left (c2 * d1))).add (o22.hasSum.mul_left (c2 * d2))
  simp only [bilinf]
  refine HasSum.tsum_eq ?_
  convert H using 1
  funext n
  rw [hin n]
  ring

/-! ## The phase trick for `R_f` -/

/-- `e^{iε/2}`. -/
private noncomputable def ph (ε : ℝ) : ℂ := exp (((ε / 2 : ℝ) : ℂ) * I)

/-- `e^{-iε/2}`. -/
private noncomputable def phc (ε : ℝ) : ℂ := exp (-(((ε / 2 : ℝ) : ℂ) * I))

private lemma ph_mul_phc (ε : ℝ) : ph ε * phc ε = 1 := by
  rw [ph, phc, ← exp_add, add_neg_cancel, exp_zero]

private lemma phc_mul_ph (ε : ℝ) : phc ε * ph ε = 1 := by rw [mul_comm, ph_mul_phc]

private lemma conj_phc (ε : ℝ) : conj (phc ε) = ph ε := by
  rw [ph, phc, ← exp_conj]
  congr 1
  rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma norm_ph (ε : ℝ) : ‖ph ε‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma ph_sq (ε : ℝ) : ph ε ^ 2 = exp ((ε : ℂ) * I) := by
  rw [ph, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `c = e^{-iε/2} (r + i q)` with `r + iq = e^{iε/2} c`. -/
private lemma phase_split (ε : ℝ) (c : ℂ) :
    c = phc ε * (((ph ε * c).re : ℝ) : ℂ) + (phc ε * I) * (((ph ε * c).im : ℝ) : ℂ) := by
  have h := Complex.re_add_im (ph ε * c)
  have h2 : phc ε * (ph ε * c) = c := by rw [← mul_assoc, phc_mul_ph, one_mul]
  calc c = phc ε * (ph ε * c) := h2.symm
    _ = phc ε * ((((ph ε * c).re : ℝ) : ℂ) + (((ph ε * c).im : ℝ) : ℂ) * I) := by rw [h]
    _ = _ := by ring

/-- `c̄ = e^{iε/2} (r - i q)` with `r + iq = e^{iε/2} c`. -/
private lemma phase_split_conj (ε : ℝ) (c : ℂ) :
    conj c = ph ε * (((ph ε * c).re : ℝ) : ℂ) + (-(ph ε * I)) * (((ph ε * c).im : ℝ) : ℂ) := by
  conv_lhs => rw [phase_split ε c]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, conj_phc]
  ring

private lemma re_sq_eq (c : ℂ) : c.re ^ 2 = (‖c‖ ^ 2 + (c ^ 2).re) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sq c, Complex.mul_re]; ring

private lemma im_sq_eq (c : ℂ) : c.im ^ 2 = (‖c‖ ^ 2 - (c ^ 2).re) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sq c, Complex.mul_re]; ring

/-- The squared norms of the real and imaginary parts of `e^{iε/2} u`:
`‖u_r‖² = (‖u‖² + Re(e^{iε} uᵀu))/2`, `‖u_i‖² = (‖u‖² - Re(e^{iε} uᵀu))/2`. -/
private lemma phase_hasSum (ε : ℝ) {u : ℕ → ℂ} {N : ℝ} {S : ℂ} (hN : HasSum (fun n => ‖u n‖ ^ 2) N)
    (hS : HasSum (fun n => u n ^ 2) S) :
    HasSum (fun n => ‖(((ph ε * u n).re : ℝ) : ℂ)‖ ^ 2) ((N + (exp ((ε : ℂ) * I) * S).re) / 2) ∧
      HasSum (fun n => ‖(((ph ε * u n).im : ℝ) : ℂ)‖ ^ 2) ((N - (exp ((ε : ℂ) * I) * S).re) / 2) := by
  have h1 : ∀ n, ‖ph ε * u n‖ ^ 2 = ‖u n‖ ^ 2 := by intro n; rw [norm_mul, norm_ph, one_mul]
  have h2 : ∀ n, (ph ε * u n) ^ 2 = exp ((ε : ℂ) * I) * u n ^ 2 := by intro n; rw [mul_pow, ph_sq]
  have hS' := Complex.hasSum_re (hS.mul_left (exp ((ε : ℂ) * I)))
  constructor
  · have e : (fun n => ‖(((ph ε * u n).re : ℝ) : ℂ)‖ ^ 2) =
        fun n => (‖u n‖ ^ 2 + (exp ((ε : ℂ) * I) * u n ^ 2).re) / 2 := by
      funext n; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, re_sq_eq, h1, h2]
    rw [e]; exact (hN.add hS').div_const 2
  · have e : (fun n => ‖(((ph ε * u n).im : ℝ) : ℂ)‖ ^ 2) =
        fun n => (‖u n‖ ^ 2 - (exp ((ε : ℂ) * I) * u n ^ 2).re) / 2 := by
      funext n; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, im_sq_eq, h1, h2]
    rw [e]; exact (hN.sub hS').div_const 2

/-- `2 √(P/2) √(Q/2) = √(PQ)` for `P ≥ 0`. -/
private lemma two_sqrt_half (P Q : ℝ) (hP : 0 ≤ P) :
    2 * (Real.sqrt (P / 2) * Real.sqrt (Q / 2)) = Real.sqrt (P * Q) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ P / 2), show P / 2 * (Q / 2) = P * Q / 2 ^ 2 by ring,
    Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The phases cancel: `β(z)ᵀ C α(w) + β(w)ᵀ C α(z) = 2(β_rᵀ C α_r + β_iᵀ C α_i)` when `w = z̄`. -/
private lemma phase_identity {γ : ℕ → ℕ → ℂ}
    (hC : ∀ x y : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
      (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
        ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2))
    {xr xi yr yi : ℕ → ℂ} (hxr : Summable (fun n => ‖xr n‖ ^ 2)) (hxi : Summable (fun n => ‖xi n‖ ^ 2))
    (hyr : Summable (fun n => ‖yr n‖ ^ 2)) (hyi : Summable (fun n => ‖yi n‖ ^ 2)) (e e' : ℂ) (hee : e * e' = 1) :
    bilinf (fun n => e' * xr n + (e' * I) * xi n) (Cmat γ) (fun n => e * yr n + (-(e * I)) * yi n) +
        bilinf (fun n => e * xr n + (-(e * I)) * xi n) (Cmat γ) (fun n => e' * yr n + (e' * I) * yi n) =
      2 * (bilinf xr (Cmat γ) yr + bilinf xi (Cmat γ) yi) := by
  rw [bilinf_expand hC hxr hxi hyr hyi, bilinf_expand hC hxr hxi hyr hyi]
  linear_combination (2 * bilinf xr (Cmat γ) yr + 2 * bilinf xi (Cmat γ) yi) * hee -
    2 * e * e' * bilinf xi (Cmat γ) yi * Complex.I_sq

/-- The bound `|R_f| ≤ √((U+A)(V+B)) + √((U-A)(V-B))` from (eq:cauchy) and the phase trick. -/
private lemma Rf_main {γ : ℕ → ℕ → ℂ}
    (hC : ∀ x y : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
      (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
        ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2))
    {b a b' a' : ℕ → ℂ} (hb' : ∀ n, b' n = conj (b n)) (ha' : ∀ n, a' n = conj (a n))
    {Nb Na : ℝ} {Sb Sa : ℂ} (hNb : HasSum (fun n => ‖b n‖ ^ 2) Nb) (hSb : HasSum (fun n => b n ^ 2) Sb)
    (hNa : HasSum (fun n => ‖a n‖ ^ 2) Na) (hSa : HasSum (fun n => a n ^ 2) Sa) (ε : ℝ) :
    ‖bilinf b (Cmat γ) a' + bilinf b' (Cmat γ) a‖ ≤
      Real.sqrt ((Nb + (exp ((ε : ℂ) * I) * Sb).re) * (Na + (exp ((ε : ℂ) * I) * Sa).re)) +
        Real.sqrt ((Nb - (exp ((ε : ℂ) * I) * Sb).re) * (Na - (exp ((ε : ℂ) * I) * Sa).re)) := by
  obtain ⟨hxr, hxi⟩ := phase_hasSum ε hNb hSb
  obtain ⟨hyr, hyi⟩ := phase_hasSum ε hNa hSa
  have eb : b = fun n => phc ε * (((ph ε * b n).re : ℝ) : ℂ) + (phc ε * I) * (((ph ε * b n).im : ℝ) : ℂ) :=
    funext fun n => phase_split ε (b n)
  have ea : a = fun n => phc ε * (((ph ε * a n).re : ℝ) : ℂ) + (phc ε * I) * (((ph ε * a n).im : ℝ) : ℂ) :=
    funext fun n => phase_split ε (a n)
  have eb' : b' = fun n => ph ε * (((ph ε * b n).re : ℝ) : ℂ) + (-(ph ε * I)) * (((ph ε * b n).im : ℝ) : ℂ) :=
    funext fun n => by rw [hb']; exact phase_split_conj ε (b n)
  have ea' : a' = fun n => ph ε * (((ph ε * a n).re : ℝ) : ℂ) + (-(ph ε * I)) * (((ph ε * a n).im : ℝ) : ℂ) :=
    funext fun n => by rw [ha']; exact phase_split_conj ε (a n)
  have hid := phase_identity hC hxr.summable hxi.summable hyr.summable hyi.summable (ph ε) (phc ε) (ph_mul_phc ε)
  rw [← eb, ← ea, ← eb', ← ea'] at hid
  rw [hid]
  obtain ⟨-, -, B1⟩ := hC _ _ hxr.summable hyr.summable
  obtain ⟨-, -, B2⟩ := hC _ _ hxi.summable hyi.summable
  rw [hxr.tsum_eq, hyr.tsum_eq] at B1
  rw [hxi.tsum_eq, hyi.tsum_eq] at B2
  have hP1 : 0 ≤ Nb + (exp ((ε : ℂ) * I) * Sb).re := by
    have := hxr.nonneg (fun n => by positivity); linarith
  have hP2 : 0 ≤ Nb - (exp ((ε : ℂ) * I) * Sb).re := by
    have := hxi.nonneg (fun n => by positivity); linarith
  rw [← two_sqrt_half _ _ hP1, ← two_sqrt_half _ _ hP2, norm_mul, Complex.norm_ofNat]
  have := norm_add_le (bilinf (fun n => (((ph ε * b n).re : ℝ) : ℂ)) (Cmat γ) (fun n => (((ph ε * a n).re : ℝ) : ℂ)))
    (bilinf (fun n => (((ph ε * b n).im : ℝ) : ℂ)) (Cmat γ) (fun n => (((ph ε * a n).im : ℝ) : ℂ)))
  linarith

/-- The bound on `R_f`, given the existence of Grunsky coefficients (`sec3_grunsky_exists`), (eq:cauchy)
(`sec3_cauchy`), the sums `U_R, V_R, βᵀβ, αᵀα` (`sec6_UV_values`) and the closed forms of `A_R, B_R`
(`sec6_A0B0_closed`). -/
theorem sec6_Rf_bound_proved_from
    (hExists : FactBidiscPowerSeries → ∀ (g : ℂ → ℂ), InS g →
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (hCauchy : FactGrunsky → ∀ (g : ℂ → ℂ), InS g → ∀ (γ : ℕ → ℕ → ℂ), IsGrunskyCoeff g γ →
      ∀ (x y : ℕ → ℂ), (Summable fun n => ‖x n‖ ^ 2) → (Summable fun n => ‖y n‖ ^ 2) →
      (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
        ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2))
    (hUV : ∀ (z : ℂ), ‖z‖ = 1 / 2 →
      HasSum (fun n => ‖betaV z n‖ ^ 2) U0 ∧ HasSum (fun n => ‖alphaV z n‖ ^ 2) V0 ∧
        HasSum (fun n => betaV z n ^ 2) (z ^ 2 / (1 - z ^ 2) ^ 2) ∧
        HasSum (fun n => alphaV z n ^ 2) (-log (1 - z ^ 2)) ∧
        ∀ n, alphaV (conj z) n = conj (alphaV z n) ∧ betaV (conj z) n = conj (betaV z n))
    (hA0B0 : ∀ (θ : ℝ), deg 135 ≤ θ → θ ≤ deg 180 →
      emeps (Real.cos (θ / 2)) = exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) ∧
        zθ θ ^ 2 = -(xfar : ℂ) * exp (-(((Real.pi - θ : ℝ) : ℂ) * I)) ∧
        A0 (Real.cos (θ / 2)) = (exp (((Real.pi - θ : ℝ) : ℂ) * I) * (zθ θ ^ 2 / (1 - zθ θ ^ 2) ^ 2)).re ∧
        B0 (Real.cos (θ / 2)) = (exp (((Real.pi - θ : ℝ) : ℂ) * I) * (-log (1 - zθ θ ^ 2))).re)
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f : ℂ → ℂ) (hf : InS f) (θ : ℝ)
    (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    ‖Q f (zθ θ) (conj (zθ θ)) - pfun f (zθ θ) - pfun f (conj (zθ θ))‖ ≤ Rbound (Real.cos (θ / 2)) := by
  obtain ⟨γ, hγ, -⟩ := hExists hB f hf
  obtain ⟨hθ0, hθπ⟩ := far_range h1 h2
  obtain ⟨hU0, hV0, hbb, haa, hconj⟩ := hUV (zθ θ) (norm_zθ θ)
  obtain ⟨-, -, hA, hB'⟩ := hA0B0 θ h1 h2
  rw [lem_6_3_proved f hf γ hγ _ _ (zθ_mem_ball θ) (conj_zθ_mem_ball θ) (zθ_ne_conj hθ0 hθπ), Rbound, hA, hB']
  exact Rf_main (hCauchy hG f hf γ hγ) (fun n => (hconj n).2) (fun n => (hconj n).1) hU0 hbb hV0 haa
    (Real.pi - θ)

/-! ## The odd block on odd vectors, and the point `s = s_θ` -/

/-- On vectors supported on odd indices, the odd block `O` and the full matrix `C` give the same form. -/
private lemma bilinf_Oblock_eq {γ : ℕ → ℕ → ℂ} {x y : ℕ → ℂ} (hx : ∀ n, n % 2 = 0 → x n = 0)
    (hy : ∀ n, n % 2 = 0 → y n = 0) : bilinf x (Oblock γ) y = bilinf x (Cmat γ) y := by
  unfold bilinf
  refine tsum_congr (fun n => ?_)
  by_cases hn : n % 2 = 0
  · rw [hx n hn, zero_mul, zero_mul]
  · have hn1 : n % 2 = 1 := by omega
    congr 1
    refine tsum_congr (fun m => ?_)
    by_cases hm : m % 2 = 0
    · rw [hy m hm, mul_zero, mul_zero]
    · have hm1 : m % 2 = 1 := by omega
      rw [Oblock, ite_eq_left ⟨hn1, hm1⟩]

private lemma aOdd_even {s : ℂ} {n : ℕ} (hn : n % 2 = 0) : aOdd s n = 0 := by
  unfold aOdd; rw [ite_eq_right (by omega)]

private lemma aOdd_conj (s : ℂ) (n : ℕ) : aOdd (conj s) n = conj (aOdd s n) := by
  unfold aOdd; split_ifs <;> simp [map_div₀, Complex.conj_ofReal]

private lemma norm_sθ_sq (θ : ℝ) : ‖sθ θ‖ ^ 2 = 1 / 2 := by
  unfold sθ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma sθ_mem_ball (θ : ℝ) : sθ θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  have h := norm_sθ_sq θ
  nlinarith [norm_nonneg (sθ θ)]

private lemma conj_sθ_mem_ball (θ : ℝ) : conj (sθ θ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_conj, ← mem_ball_zero_iff]; exact sθ_mem_ball θ

/-- `s² = z` (sec_05_grunsky_q.tex:8-10). -/
private lemma sθ_sq (θ : ℝ) : sθ θ ^ 2 = zθ θ := by
  have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  unfold sθ zθ
  rw [mul_pow, h2, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

private lemma Ao_pos : 0 < Ao := by
  have h := sec6_L_log3_proved.1
  have : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

/-- `e^{-iφ} Z_o = |Z_o|`, `φ = arg Z_o`. -/
private lemma rot_Zo (θ : ℝ) : exp ((((-phiFar θ) : ℝ) : ℂ) * I) * Zo θ = ((‖Zo θ‖ : ℝ) : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (Zo θ)]
  rw [phiFar, mul_left_comm, ← Complex.exp_add]
  push_cast
  rw [neg_mul, neg_add_cancel, exp_zero, mul_one]

/-- The real and imaginary parts `r + iq = e^{-iφ/2} a(s)`: `‖r‖² = σ₊`, `‖q‖² = σ₋`, `rᵀq = 0`. -/
private lemma rq_sums {θ : ℝ} {u : ℕ → ℂ} (hN : HasSum (fun n => ‖u n‖ ^ 2) Ao) (hS : HasSum (fun n => u n ^ 2) (Zo θ)) :
    HasSum (fun n => (ph (-phiFar θ) * u n).re ^ 2) (sigP θ) ∧
      HasSum (fun n => (ph (-phiFar θ) * u n).im ^ 2) (sigM θ) ∧
      HasSum (fun n => (ph (-phiFar θ) * u n).re * (ph (-phiFar θ) * u n).im) 0 := by
  obtain ⟨h1, h2⟩ := phase_hasSum (-phiFar θ) hN hS
  rw [rot_Zo, Complex.ofReal_re] at h1 h2
  have e1 : ∀ c : ℝ, ‖(c : ℂ)‖ ^ 2 = c ^ 2 := fun c => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [e1] at h1 h2
  refine ⟨h1, h2, ?_⟩
  have h3 := Complex.hasSum_im (hS.mul_left (exp ((((-phiFar θ) : ℝ) : ℂ) * I)))
  rw [rot_Zo, Complex.ofReal_im] at h3
  have h4 := h3.div_const 2
  rw [zero_div] at h4
  refine h4.congr_fun (fun n => ?_)
  have e : exp ((((-phiFar θ) : ℝ) : ℂ) * I) * u n ^ 2 = (ph (-phiFar θ) * u n) * (ph (-phiFar θ) * u n) := by
    rw [← ph_sq]; ring
  rw [e, Complex.mul_im (ph (-phiFar θ) * u n) (ph (-phiFar θ) * u n)]
  ring

private lemma sigP_pos (θ : ℝ) : 0 < sigP θ := by
  unfold sigP; have := Ao_pos; have := norm_nonneg (Zo θ); linarith

/-- `σ₋ > 0`: otherwise `e^{-iφ/2} s` and `e^{-iφ/2} s³` would both be real, and `z = s²` would be real. -/
private lemma sigM_pos
    (hGram : ∀ (s : ℂ), ‖s‖ ^ 2 = 1 / 2 →
      HasSum (fun n => ‖aOdd s n‖ ^ 2) Ao ∧ HasSum (fun n => aOdd s n ^ 2) (cartanh (s ^ 2)) ∧
        HasSum (fun n => ‖aEven s n‖ ^ 2) Ae ∧
        HasSum (fun n => aEven s n ^ 2) (-(1 / 2 : ℂ) * log (1 - (s ^ 2) ^ 2)))
    {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < sigM θ := by
  obtain ⟨hN, hS, -, -⟩ := hGram (sθ θ) (norm_sθ_sq θ)
  rw [sθ_sq] at hS
  obtain ⟨-, hq, -⟩ := rq_sums hN hS
  by_contra hneg
  rw [not_lt] at hneg
  set w := ph (-phiFar θ)
  have hq0 : ∀ n, (w * aOdd (sθ θ) n).im = 0 := by
    intro n
    have := le_hasSum hq n (fun j _ => sq_nonneg _)
    nlinarith [sq_nonneg (w * aOdd (sθ θ) n).im]
  have ha1 : aOdd (sθ θ) 1 = sθ θ := by simp [aOdd]
  have ha3 : aOdd (sθ θ) 3 = sθ θ ^ 3 / (Real.sqrt 3 : ℂ) := by simp [aOdd]
  have hq1 := hq0 1
  have hq3 := hq0 3
  rw [ha1] at hq1
  rw [ha3, ← mul_div_assoc, Complex.div_ofReal_im] at hq3
  have hs3 : (w * sθ θ ^ 3).im = 0 := by
    have hsq : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    rcases div_eq_zero_iff.1 hq3 with h | h
    · exact h
    · linarith
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hs0 : sθ θ ≠ 0 := by
    intro h; have := norm_sθ_sq θ; rw [h, norm_zero] at this; norm_num at this
  have hA : w * sθ θ = (((w * sθ θ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hq1])
  have hB : w * sθ θ ^ 3 = (((w * sθ θ ^ 3).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hs3])
  have hz : zθ θ = (w * sθ θ ^ 3) / (w * sθ θ) := by
    rw [← sθ_sq]; field_simp
  have him : (zθ θ).im = 0 := by
    rw [hz, hB, hA, ← Complex.ofReal_div, Complex.ofReal_im]
  linarith [im_zθ_pos h0 hπ]

/-! ## The bilinear bound gives the operator norm -/

/-- A `2 x 2` matrix with `|xᵀ M y| ≤ ‖x‖ ‖y‖` for all `x, y` has operator norm at most `1`. -/
private lemma opNorm_le_one_of_bil {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : ∀ x y : Fin 2 → ℂ, ‖∑ i, ∑ j, x i * M i j * y j‖ ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2)) : opNorm M ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
  set u : Fin 2 → ℂ := M *ᵥ WithLp.ofLp y with hu
  have hTy : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M y‖ = Real.sqrt (∑ i, ‖u i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; rfl
  have hy : ‖y‖ = Real.sqrt (∑ j, ‖WithLp.ofLp y j‖ ^ 2) := by rw [EuclideanSpace.norm_eq]
  have key := hM (fun i => conj (u i)) (WithLp.ofLp y)
  have hsum : ∑ i, ∑ j, conj (u i) * M i j * WithLp.ofLp y j = ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    calc ∑ j, conj (u i) * M i j * WithLp.ofLp y j = conj (u i) * ∑ j, M i j * WithLp.ofLp y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = conj (u i) * u i := rfl
      _ = (‖u i‖ : ℂ) ^ 2 := Complex.conj_mul' (u i)
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at key
  simp only [Complex.norm_conj] at key
  rw [hTy, hy, one_mul]
  have hA : 0 ≤ ∑ i, ‖u i‖ ^ 2 := by positivity
  have := Real.sq_sqrt hA
  nlinarith [Real.sqrt_nonneg (∑ i, ‖u i‖ ^ 2), Real.sqrt_nonneg (∑ j, ‖WithLp.ofLp y j‖ ^ 2)]

/-- The symmetrization `(N + Nᵀ)/2` of a `2 x 2` matrix with the bilinear bound lies in `𝓑`. -/
private lemma symm_inBall (Nm : Fin 2 → Fin 2 → ℂ)
    (hN : ∀ x y : Fin 2 → ℂ, ‖∑ i, ∑ j, x i * Nm i j * y j‖ ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2)) :
    InBall !![Nm 0 0, (Nm 0 1 + Nm 1 0) / 2; (Nm 0 1 + Nm 1 0) / 2, Nm 1 1] := by
  refine ⟨?_, opNorm_le_one_of_bil (fun x y => ?_)⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · have e : ∑ i, ∑ j, x i * (!![Nm 0 0, (Nm 0 1 + Nm 1 0) / 2; (Nm 0 1 + Nm 1 0) / 2, Nm 1 1] : Matrix _ _ ℂ) i j * y j =
        ((∑ i, ∑ j, x i * Nm i j * y j) + ∑ i, ∑ j, y i * Nm i j * x j) / 2 := by
      simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    rw [e, norm_div, Complex.norm_ofNat]
    have h1 := hN x y
    have h2 := hN y x
    have h3 := norm_add_le (∑ i, ∑ j, x i * Nm i j * y j) (∑ i, ∑ j, y i * Nm i j * x j)
    linarith

/-! ## `log p` and `log q` in the rotated basis -/

/-- `e^{iφ/2}` squared, written with `phc (-φ)`. -/
private lemma phc_neg_sq (φ : ℝ) : phc (-φ) ^ 2 = exp ((φ : ℂ) * I) := by
  rw [phc, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma ph_neg_sq (φ : ℝ) : ph (-φ) ^ 2 = exp (-((φ : ℂ) * I)) := by
  rw [ph_sq]
  congr 1
  push_cast
  ring

/-- The algebra of the compression: with `a = c₁ e₁ + c₂ e₂`, `2 aᵀ C a = e^{iφ}(X + iY)`. -/
private lemma compress_algebra (P E sp sm N00 N01 N10 N11 : ℂ) (hP : P ^ 2 = E) (σp σm : ℝ)
    (hsp : sp ^ 2 = σp) (hsm : sm ^ 2 = σm) (d : ℂ) (hd : d = 4 * sp * sm) :
    2 * ((P * sp) * (P * sp) * N00 + (P * sp) * (P * I * sm) * N01 + (P * I * sm) * (P * sp) * N10 +
        (P * I * sm) * (P * I * sm) * N11) =
      E * (2 * ((σp : ℂ) * N00 - (σm : ℂ) * N11) + I * (d * ((N01 + N10) / 2))) := by
  rw [← hP, ← hsp, ← hsm, hd]
  linear_combination (2 * P ^ 2 * sm ^ 2 * N11) * Complex.I_sq

/-- The same algebra for `ā = c̄₁ e₁ + c̄₂ e₂`: `2 āᵀ C ā = e^{-iφ}(X - iY)`. -/
private lemma compress_algebra_conj (P E sp sm N00 N01 N10 N11 : ℂ) (hP : P ^ 2 = E) (σp σm : ℝ)
    (hsp : sp ^ 2 = σp) (hsm : sm ^ 2 = σm) (d : ℂ) (hd : d = 4 * sp * sm) :
    2 * ((P * sp) * (P * sp) * N00 + (P * sp) * (-(P * I) * sm) * N01 + (-(P * I) * sm) * (P * sp) * N10 +
        (-(P * I) * sm) * (-(P * I) * sm) * N11) =
      E * (2 * ((σp : ℂ) * N00 - (σm : ℂ) * N11) - I * (d * ((N01 + N10) / 2))) := by
  rw [← hP, ← hsp, ← hsm, hd]
  linear_combination (2 * P ^ 2 * sm ^ 2 * N11) * Complex.I_sq

open Classical in
/-- `log p = e^{iφ}(X + iY)`, `log q = e^{-iφ}(X - iY)`, given the existence of the odd root
(`sec3_oddroot_exists`), `h ∈ 𝒮` (`sec3_oddroot_mem_S`), the Grunsky coefficients (`sec3_grunsky_exists`),
(eq:cauchy) (`sec3_cauchy`), the compressions (`sec3_blocks_compressions`), Lemma 3.1(iii) (`lem_3_1_iii`)
and (eq:gram) (`eq_gram`). -/
theorem sec6_logp_logq_proved_from
    (hOddEx : ∀ (f : ℂ → ℂ), InS f → ∃ h : ℂ → ℂ, IsOddRoot f h)
    (hOddS : ∀ (f h : ℂ → ℂ), InS f → IsOddRoot f h → InS h)
    (hExists : FactBidiscPowerSeries → ∀ (g : ℂ → ℂ), InS g →
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (hCauchy : FactGrunsky → ∀ (g : ℂ → ℂ), InS g → ∀ (γ : ℕ → ℕ → ℂ), IsGrunskyCoeff g γ →
      ∀ (x y : ℕ → ℂ), (Summable fun n => ‖x n‖ ^ 2) → (Summable fun n => ‖y n‖ ^ 2) →
      (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
        ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2))
    (hComp : FactGrunsky → ∀ (g : ℂ → ℂ), InS g → ∀ (γ : ℕ → ℕ → ℂ), IsGrunskyCoeff g γ →
      (∀ (S : Set ℕ) (x y : ℕ → ℂ), Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
        ‖bilinf x (fun n m => if n ∈ S ∧ m ∈ S then Cmat γ n m else 0) y‖ ≤
          Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2)) ∧
      ∀ (k : ℕ) (V : ℕ → Fin k → ℂ),
        (∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) →
        ∀ x y : Fin k → ℂ, ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) * y j‖ ≤
          Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2))
    (hL31 : ∀ (f h : ℂ → ℂ), InS f → IsOddRoot f h → ∀ (γ : ℕ → ℕ → ℂ), IsGrunskyCoeff h γ →
      ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
        2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
        ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2))
    (hGram : ∀ (s : ℂ), ‖s‖ ^ 2 = 1 / 2 →
      HasSum (fun n => ‖aOdd s n‖ ^ 2) Ao ∧ HasSum (fun n => aOdd s n ^ 2) (cartanh (s ^ 2)) ∧
        HasSum (fun n => ‖aEven s n‖ ^ 2) Ae ∧
        HasSum (fun n => aEven s n ^ 2) (-(1 / 2 : ℂ) * log (1 - (s ^ 2) ^ 2)))
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f : ℂ → ℂ) (hf : InS f) (θ : ℝ)
    (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    ∃ N : Matrix (Fin 2) (Fin 2) ℂ, InBall N ∧
      pfun f (zθ θ) = exp (exp ((phiFar θ : ℂ) * I) *
        (2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1) + I * ((dFar θ : ℂ) * N 0 1))) ∧
      pfun f (conj (zθ θ)) = exp (exp (-((phiFar θ : ℂ) * I)) *
        (2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1) - I * ((dFar θ : ℂ) * N 0 1))) := by
  obtain ⟨hθ0, hθπ⟩ := far_range h1 h2
  obtain ⟨h, hh⟩ := hOddEx f hf
  have hhS := hOddS f h hf hh
  obtain ⟨γ, hγ, -⟩ := hExists hB h hhS
  have hC := hCauchy hG h hhS γ hγ
  have hV2 := (hComp hG h hhS γ hγ).2 2
  have hp3 := (hL31 f h hf hh γ hγ).2.2
  obtain ⟨hN, hS, -, -⟩ := hGram (sθ θ) (norm_sθ_sq θ)
  rw [sθ_sq] at hS
  obtain ⟨hr, hq, hrq⟩ := rq_sums hN hS
  set φ := phiFar θ
  set σp := sigP θ
  set σm := sigM θ
  have hσp := sigP_pos θ
  have hσm : 0 < σm := sigM_pos hGram hθ0 hθπ
  have hsp0 : Real.sqrt σp ≠ 0 := (Real.sqrt_pos.2 hσp).ne'
  have hsm0 : Real.sqrt σm ≠ 0 := (Real.sqrt_pos.2 hσm).ne'
  set r : ℕ → ℝ := fun n => (ph (-φ) * aOdd (sθ θ) n).re with hr_def
  set q : ℕ → ℝ := fun n => (ph (-φ) * aOdd (sθ θ) n).im with hq_def
  set e1 : ℕ → ℂ := fun n => ((r n / Real.sqrt σp : ℝ) : ℂ) with he1
  set e2 : ℕ → ℂ := fun n => ((q n / Real.sqrt σm : ℝ) : ℂ) with he2
  -- the real sums of the unit vectors
  have hr11 : HasSum (fun n => (r n / Real.sqrt σp) * (r n / Real.sqrt σp)) 1 := by
    have := hr.div_const σp
    rw [div_self hσp.ne'] at this
    refine this.congr_fun (fun n => ?_)
    rw [div_mul_div_comm, Real.mul_self_sqrt hσp.le, sq]
  have hr22 : HasSum (fun n => (q n / Real.sqrt σm) * (q n / Real.sqrt σm)) 1 := by
    have := hq.div_const σm
    rw [div_self hσm.ne'] at this
    refine this.congr_fun (fun n => ?_)
    rw [div_mul_div_comm, Real.mul_self_sqrt hσm.le, sq]
  have hr12 : HasSum (fun n => (r n / Real.sqrt σp) * (q n / Real.sqrt σm)) 0 := by
    have := hrq.div_const (Real.sqrt σp * Real.sqrt σm)
    rw [zero_div] at this
    refine this.congr_fun (fun n => ?_)
    rw [div_mul_div_comm]
  have hr21 : HasSum (fun n => (q n / Real.sqrt σm) * (r n / Real.sqrt σp)) 0 :=
    hr12.congr_fun (fun n => mul_comm _ _)
  have cplx : ∀ (x y : ℕ → ℝ) (c : ℝ), HasSum (fun n => x n * y n) c →
      HasSum (fun n => conj ((x n : ℝ) : ℂ) * ((y n : ℝ) : ℂ)) (c : ℂ) := fun x y c hxy => by
    refine (Complex.hasSum_ofReal.2 hxy).congr_fun (fun n => ?_)
    rw [Complex.conj_ofReal, Complex.ofReal_mul]
  set V : ℕ → Fin 2 → ℂ := fun n => ![e1 n, e2 n] with hV_def
  have hV : ∀ i j : Fin 2, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [hV_def, he1] using cplx _ _ _ hr11
    · simpa [hV_def, he1, he2] using cplx _ _ _ hr12
    · simpa [hV_def, he1, he2] using cplx _ _ _ hr21
    · simpa [hV_def, he2] using cplx _ _ _ hr22
  have hbound := hV2 V hV
  set Nm : Fin 2 → Fin 2 → ℂ := fun i j => bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) with hNm
  have hInB := symm_inBall Nm hbound
  have hsp' : (Real.sqrt σp : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsp0
  have hsm' : (Real.sqrt σm : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsm0
  have hv0 : ∀ n, V n 0 = (((ph (-φ) * aOdd (sθ θ) n).re / Real.sqrt σp : ℝ) : ℂ) := fun n => rfl
  have hv1 : ∀ n, V n 1 = (((ph (-φ) * aOdd (sθ θ) n).im / Real.sqrt σm : ℝ) : ℂ) := fun n => rfl
  have ha : aOdd (sθ θ) = fun n => (phc (-φ) * (Real.sqrt σp : ℂ)) * V n 0 +
      (phc (-φ) * I * (Real.sqrt σm : ℂ)) * V n 1 := by
    funext n
    rw [hv0, hv1, Complex.ofReal_div, Complex.ofReal_div]
    conv_lhs => rw [phase_split (-φ) (aOdd (sθ θ) n)]
    field_simp
  have ha' : aOdd (conj (sθ θ)) = fun n => (ph (-φ) * (Real.sqrt σp : ℂ)) * V n 0 +
      (-(ph (-φ) * I) * (Real.sqrt σm : ℂ)) * V n 1 := by
    funext n
    rw [hv0, hv1, Complex.ofReal_div, Complex.ofReal_div, aOdd_conj]
    conv_lhs => rw [phase_split_conj (-φ) (aOdd (sθ θ) n)]
    field_simp
  have hl0 : Summable (fun n => ‖V n 0‖ ^ 2) := hr11.summable.congr (fun n => by
    rw [hv0, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq])
  have hl1 : Summable (fun n => ‖V n 1‖ ^ 2) := hr22.summable.congr (fun n => by
    rw [hv1, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq])
  have hsp2 : (Real.sqrt σp : ℂ) ^ 2 = (σp : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hσp.le]
  have hsm2 : (Real.sqrt σm : ℂ) ^ 2 = (σm : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hσm.le]
  have hd : (dFar θ : ℂ) = 4 * (Real.sqrt σp : ℂ) * (Real.sqrt σm : ℂ) := by
    rw [dFar, Real.sqrt_mul hσp.le]; push_cast; ring
  have hodd : ∀ n, n % 2 = 0 → aOdd (sθ θ) n = 0 := fun n hn => aOdd_even hn
  have hodd' : ∀ n, n % 2 = 0 → aOdd (conj (sθ θ)) n = 0 := fun n hn => aOdd_even hn
  refine ⟨_, hInB, ?_, ?_⟩
  · rw [← sθ_sq θ, ← hp3 _ (sθ_mem_ball θ), bilinf_Oblock_eq hodd hodd, ha, bilinf_expand hC hl0 hl1 hl0 hl1]
    congr 1
    exact compress_algebra _ _ _ _ _ _ _ _ (phc_neg_sq φ) σp σm hsp2 hsm2 _ hd
  · rw [← sθ_sq θ, map_pow, ← hp3 _ (conj_sθ_mem_ball θ), bilinf_Oblock_eq hodd' hodd', ha',
      bilinf_expand hC hl0 hl1 hl0 hl1]
    congr 1
    exact compress_algebra_conj _ _ _ _ _ _ _ _ (ph_neg_sq φ) σp σm hsp2 hsm2 _ hd

/-! ## (eq:psum) -/

/-- `cos v ≠ 0` for `|v| < π/2` (the zeros of `cos` are the real numbers `(2k + 1)π/2`). -/
private lemma ccos_ne_zero {v : ℂ} (hv : ‖v‖ < Real.pi / 2) : Complex.cos v ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 h
  have e : v = (((2 * (k : ℝ) + 1) * Real.pi / 2 : ℝ) : ℂ) := by rw [hk]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two] at hv
  have hk1 : (1 : ℝ) ≤ |2 * (k : ℝ) + 1| := by
    rcases le_or_gt 0 k with h0 | h0
    · have : (0 : ℝ) ≤ k := by exact_mod_cast h0
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h1 : k ≤ -1 := by omega
      have : (k : ℝ) ≤ -1 := by exact_mod_cast h1
      rw [abs_of_neg (by linarith)]; linarith
  nlinarith [Real.pi_pos]

/-- The change of variables of `sec6_b_change` (explicit `ζ₁`, `ζ₂`), in the form `∃ ζ₁ ζ₂` that `eq_psum_proved_from`
uses. -/
private lemma bchange_exists (hBchange : ∀ (L d φ : ℝ), 0 < L → 0 < d → ∀ (ξ₁ ξ₂ : ℂ),
      let b₁ : ℝ := Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2)
      let ζ₁ : ℂ := ((L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂) / b₁
      let ζ₂ : ℂ := ((d * Real.cos φ : ℂ) * ξ₁ - (L * Real.sin φ : ℂ) * ξ₂) / b₁
      ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 = ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 ∧
        (L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂ = (b₁ : ℂ) * ζ₁ ∧
        (L * Real.cos φ : ℂ) * ξ₁ - (d * Real.sin φ : ℂ) * ξ₂ =
          (((L ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / b₁ : ℝ) : ℂ) * ζ₁ + ((L * d / b₁ : ℝ) : ℂ) * ζ₂)
    (L d φ : ℝ) (hL : 0 < L) (hd : 0 < d) (ξ₁ ξ₂ : ℂ) :
    ∃ ζ₁ ζ₂ : ℂ, ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 = ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 ∧
      (L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂ =
        (Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2) : ℂ) * ζ₁ ∧
      (L * Real.cos φ : ℂ) * ξ₁ - (d * Real.sin φ : ℂ) * ξ₂ =
        (((L ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2) : ℝ) : ℂ)
            * ζ₁ +
          ((L * d / Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2) : ℝ) : ℂ) * ζ₂ :=
  ⟨_, _, hBchange L d φ hL hd ξ₁ ξ₂⟩

open Classical in
/-- (eq:psum), given Lemma 6.2's check and the rows used by `sec6_logp_logq_proved_from`, together with
`sec6_psum_cos`, `sec6_xi_ball`, `sec6_b_change`, `sec6_b_values`, `sec6_Wbound_finite` and `sec6_expW_bound`. -/
theorem eq_psum_proved_from
    (hOddEx : ∀ (f : ℂ → ℂ), InS f → ∃ h : ℂ → ℂ, IsOddRoot f h)
    (hOddS : ∀ (f h : ℂ → ℂ), InS f → IsOddRoot f h → InS h)
    (hExists : FactBidiscPowerSeries → ∀ (g : ℂ → ℂ), InS g →
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (hCauchy : FactGrunsky → ∀ (g : ℂ → ℂ), InS g → ∀ (γ : ℕ → ℕ → ℂ), IsGrunskyCoeff g γ →
      ∀ (x y : ℕ → ℂ), (Summable fun n => ‖x n‖ ^ 2) → (Summable fun n => ‖y n‖ ^ 2) →
      (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
        ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2))
    (hComp : FactGrunsky → ∀ (g : ℂ → ℂ), InS g → ∀ (γ : ℕ → ℕ → ℂ), IsGrunskyCoeff g γ →
      (∀ (S : Set ℕ) (x y : ℕ → ℂ), Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
        ‖bilinf x (fun n m => if n ∈ S ∧ m ∈ S then Cmat γ n m else 0) y‖ ≤
          Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2)) ∧
      ∀ (k : ℕ) (V : ℕ → Fin k → ℂ),
        (∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) →
        ∀ x y : Fin k → ℂ, ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) * y j‖ ≤
          Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2))
    (hL31 : ∀ (f h : ℂ → ℂ), InS f → IsOddRoot f h → ∀ (γ : ℕ → ℕ → ℂ), IsGrunskyCoeff h γ →
      ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
        2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
        ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2))
    (hGram : ∀ (s : ℂ), ‖s‖ ^ 2 = 1 / 2 →
      HasSum (fun n => ‖aOdd s n‖ ^ 2) Ao ∧ HasSum (fun n => aOdd s n ^ 2) (cartanh (s ^ 2)) ∧
        HasSum (fun n => ‖aEven s n‖ ^ 2) Ae ∧
        HasSum (fun n => aEven s n ^ 2) (-(1 / 2 : ℂ) * log (1 - (s ^ 2) ^ 2)))
    (hPsumCos : ∀ (φ : ℝ) (X Y : ℂ),
      (exp (exp ((φ : ℂ) * I) * (X + I * Y)) + exp (exp (-((φ : ℂ) * I)) * (X - I * Y))) / 2 =
        exp ((Real.cos φ : ℂ) * X - (Real.sin φ : ℂ) * Y) *
          Complex.cos ((Real.sin φ : ℂ) * X + (Real.cos φ : ℂ) * Y))
    (hXi : ∀ (σp σm : ℝ), 0 ≤ σp → 0 ≤ σm → 0 < σp + σm →
      ∀ (N : Matrix (Fin 2) (Fin 2) ℂ), InBall N →
        ‖2 * ((σp : ℂ) * N 0 0 - (σm : ℂ) * N 1 1) / (2 * ((σp + σm : ℝ) : ℂ))‖ ^ 2 + ‖N 0 1‖ ^ 2 ≤ 1)
    (hBchange : ∀ (L d φ : ℝ), 0 < L → 0 < d → ∀ (ξ₁ ξ₂ : ℂ),
      let b₁ : ℝ := Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2)
      let ζ₁ : ℂ := ((L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂) / b₁
      let ζ₂ : ℂ := ((d * Real.cos φ : ℂ) * ξ₁ - (L * Real.sin φ : ℂ) * ξ₂) / b₁
      ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 = ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 ∧
        (L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂ = (b₁ : ℂ) * ζ₁ ∧
        (L * Real.cos φ : ℂ) * ξ₁ - (d * Real.sin φ : ℂ) * ξ₂ =
          (((L ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / b₁ : ℝ) : ℂ) * ζ₁ + ((L * d / b₁ : ℝ) : ℂ) * ζ₂)
    (hBvalues : ∀ (θ : ℝ), deg 135 ≤ θ → θ ≤ deg 180 →
      let φ := Complex.arg (Zo θ)
      let d := 4 * Real.sqrt ((Ao + ‖Zo θ‖) / 2 * ((Ao - ‖Zo θ‖) / 2))
      let c := Real.cos (θ / 2)
      0 < b1 c ∧ Real.sqrt (Llog3 ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2) = b1 c ∧
        (Llog3 ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / b1 c = b2 c ∧ Llog3 * d / b1 c = b3 c ∧
        0 ≤ b2 c ∧ 0 ≤ b3 c ∧ b1 c ≤ Llog3 ∧ Llog3 < Real.pi / 2)
    (hWbound : ∀ (b₁ b₂ b₃ : ℝ), 0 ≤ b₁ → 0 ≤ b₂ → 0 ≤ b₃ → b₁ < Real.pi / 2 →
      ∀ (ζ₁ ζ₂ : ℂ), ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 ≤ 1 →
        ‖ζ₁‖ ≤ 1 ∧
          ‖(b₂ : ℂ) * ζ₁ + (b₃ : ℂ) * ζ₂ + log (Complex.cos ((b₁ : ℂ) * ζ₁))‖ ≤
            b₂ * ‖ζ₁‖ + b₃ * Real.sqrt (1 - ‖ζ₁‖ ^ 2) - Real.log (Real.cos (b₁ * ‖ζ₁‖)))
    (hExpW : ∀ (W : ℂ), ‖W‖ ≤ Tfar → 277 / 800 < (exp W).re)
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (h62 : Check_6_2) (f : ℂ → ℂ) (hf : InS f)
    (θ : ℝ) (h1 : deg 135 ≤ θ) (h2 : θ ≤ deg 180) :
    277 / 400 < (pfun f (zθ θ) + pfun f (conj (zθ θ))).re := by
  obtain ⟨hθ0, hθπ⟩ := far_range h1 h2
  obtain ⟨N, hN, hp, hq⟩ :=
    sec6_logp_logq_proved_from hOddEx hOddS hExists hCauchy hComp hL31 hGram hB hG f hf θ h1 h2
  have hpq := hPsumCos (phiFar θ) (2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1)) ((dFar θ : ℂ) * N 0 1)
  rw [← hp, ← hq] at hpq
  have hσp := sigP_pos θ
  have hσm := sigM_pos hGram hθ0 hθπ
  have hL : Llog3 = 2 * (sigP θ + sigM θ) := by
    have h3 := sec6_L_log3_proved
    unfold sigP sigM
    linarith [h3.1, h3.2.1]
  have hLpos : 0 < Llog3 := by rw [hL]; linarith
  have hdpos : 0 < dFar θ := by
    unfold dFar
    have := Real.sqrt_pos.2 (mul_pos hσp hσm)
    linarith
  have hξ := hXi (sigP θ) (sigM θ) hσp.le hσm.le (by linarith) N hN
  set ξ₁ : ℂ := 2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1) / (2 * ((sigP θ + sigM θ : ℝ) : ℂ)) with hξ₁
  have hX : 2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1) = (Llog3 : ℂ) * ξ₁ := by
    have hne : (2 * ((sigP θ + sigM θ : ℝ) : ℂ)) ≠ 0 := by
      have : (sigP θ + sigM θ : ℝ) ≠ 0 := by linarith
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 this)
    have hne' : (sigP θ : ℂ) + (sigM θ : ℂ) ≠ 0 := by
      have : (sigP θ + sigM θ : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    rw [hξ₁, hL]
    push_cast
    field_simp
  obtain ⟨ζ₁, ζ₂, hζn, hVs, hUs⟩ := bchange_exists hBchange Llog3 (dFar θ) (phiFar θ) hLpos hdpos ξ₁ (N 0 1)
  have hbv := hBvalues θ h1 h2
  dsimp only at hbv
  obtain ⟨hb1pos, hb1, hb2, hb3, hb2nn, hb3nn, hb1L, hLpi⟩ := hbv
  have hdd : dFar θ = 4 * Real.sqrt ((Ao + ‖Zo θ‖) / 2 * ((Ao - ‖Zo θ‖) / 2)) := rfl
  have hφφ : phiFar θ = Complex.arg (Zo θ) := rfl
  rw [← hdd] at hb1 hb2 hb3
  rw [← hφφ] at hb1 hb2
  rw [hb1] at hVs hUs
  have hV' : (Real.sin (phiFar θ) : ℂ) * (2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1)) +
      (Real.cos (phiFar θ) : ℂ) * ((dFar θ : ℂ) * N 0 1) = (b1 (Real.cos (θ / 2)) : ℂ) * ζ₁ := by
    rw [hX, ← hVs]; push_cast; ring
  have hU' : (Real.cos (phiFar θ) : ℂ) * (2 * ((sigP θ : ℂ) * N 0 0 - (sigM θ : ℂ) * N 1 1)) -
      (Real.sin (phiFar θ) : ℂ) * ((dFar θ : ℂ) * N 0 1) =
        (b2 (Real.cos (θ / 2)) : ℂ) * ζ₁ + (b3 (Real.cos (θ / 2)) : ℂ) * ζ₂ := by
    rw [hX, ← hb2, ← hb3, ← hUs]; push_cast; ring
  have hζ : ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 ≤ 1 := by rw [hζn]; exact hξ
  obtain ⟨hr1, hW⟩ := hWbound (b1 (Real.cos (θ / 2))) (b2 (Real.cos (θ / 2))) (b3 (Real.cos (θ / 2)))
    hb1pos.le hb2nn hb3nn (lt_of_le_of_lt hb1L hLpi) ζ₁ ζ₂ hζ
  have hcos : Complex.cos ((b1 (Real.cos (θ / 2)) : ℂ) * ζ₁) ≠ 0 := by
    apply ccos_ne_zero
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb1pos]
    have : b1 (Real.cos (θ / 2)) * ‖ζ₁‖ ≤ b1 (Real.cos (θ / 2)) := by
      nlinarith [norm_nonneg ζ₁]
    linarith
  rw [hU', hV', ← Complex.exp_log hcos, ← Complex.exp_add] at hpq
  have hc := sec6_c_bound_proved θ h1 h2
  have h62' := h62 (Real.cos (θ / 2)) hc.1 (hc.2.1.trans hc.2.2.le) ‖ζ₁‖ (norm_nonneg _) hr1
  have hE := hExpW _ (lt_of_le_of_lt hW h62').le
  have hsum : pfun f (zθ θ) + pfun f (conj (zθ θ)) =
      2 * exp ((b2 (Real.cos (θ / 2)) : ℂ) * ζ₁ + (b3 (Real.cos (θ / 2)) : ℂ) * ζ₂ +
        log (Complex.cos ((b1 (Real.cos (θ / 2)) : ℂ) * ζ₁))) := by
    rw [← hpq]; ring
  have h2re : ∀ w : ℂ, (2 * w).re = 2 * w.re := fun w => by simp [Complex.mul_re]
  rw [hsum, h2re]
  linarith

end Robinson.Proofs
