/-
Robinson/Proofs/Sec2Rest.lean — proofs of sec2_pair_normal_form, sec2_values_eq, sec2_koebe_limit,
lem_2_2, prop_2_4, sec8_assembly.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.NotFormalized
import Robinson.Proofs.Sec2Basic
import Robinson.Proofs.Normalize
import Robinson.Proofs.Koebe
import Robinson.Proofs.Connector

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ### The points `z_θ = ½ e^{iθ/2}` and `\overline{z_θ}` -/

/-- `|z_θ| = ½`. -/
private lemma norm_zθ (θ : ℝ) : ‖zθ θ‖ = 1 / 2 := by
  unfold zθ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, norm_one, Complex.norm_ofNat]

private lemma zθ_mem_ball (θ : ℝ) : zθ θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_zθ]; norm_num

private lemma conj_zθ_mem_ball (θ : ℝ) : conj (zθ θ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_conj, norm_zθ]; norm_num

/-- `\overline{z_θ} = ½ e^{-iθ/2}`. -/
private lemma conj_zθ (θ : ℝ) : conj (zθ θ) = (1 / 2 : ℂ) * exp (((-(θ / 2) : ℝ) : ℂ) * I) := by
  unfold zθ
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
    Complex.conj_ofNat]
  congr 2
  push_cast
  ring

/-- `Im z_θ = sin(θ/2)/2`. -/
private lemma im_zθ (θ : ℝ) : (zθ θ).im = Real.sin (θ / 2) / 2 := by
  unfold zθ
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp
  ring

/-- For `0 < θ ≤ π`, `z_θ ≠ \overline{z_θ}`, since `Im z_θ = sin(θ/2)/2 > 0`. -/
private lemma zθ_ne_conj {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : zθ θ ≠ conj (zθ θ) := by
  intro h
  have him : (zθ θ).im = 0 := conj_eq_iff_im.mp h.symm
  rw [im_zθ] at him
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

/-- `e^{iφ} · ½ e^{iψ} = ½ e^{i(φ + ψ)}`. -/
private lemma rot_half_exp (φ ψ : ℝ) :
    exp ((φ : ℂ) * I) * ((1 / 2 : ℂ) * exp ((ψ : ℂ) * I)) =
      (1 / 2 : ℂ) * exp (((φ + ψ : ℝ) : ℂ) * I) := by
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- By Lemma 2.3 (rotation): `Q_{f_φ}(z_θ, \overline{z_θ}) = Q_f(½ e^{i(φ+θ/2)}, ½ e^{i(φ-θ/2)})`. -/
private lemma Q_rotate_zθ {f : ℂ → ℂ} (hf : InS f) (φ θ : ℝ) :
    Q (rotate φ f) (zθ θ) (conj (zθ θ)) =
      Q f ((1 / 2 : ℂ) * exp (((φ + θ / 2 : ℝ) : ℂ) * I))
        ((1 / 2 : ℂ) * exp (((φ - θ / 2 : ℝ) : ℂ) * I)) := by
  rw [(lem_2_3_rot_proved f hf φ).2 _ _ (zθ_mem_ball θ) (conj_zθ_mem_ball θ), conj_zθ]
  unfold zθ
  rw [rot_half_exp, rot_half_exp, ← sub_eq_add_neg]

/-! ### The normal form of a pair of points on the circle `|z| = ½` -/

/-- A point of modulus `½` is `½ e^{iα}` for some real `α`. -/
private lemma exists_half_exp {z : ℂ} (hz : ‖z‖ = 1 / 2) :
    ∃ α : ℝ, z = (1 / 2 : ℂ) * exp ((α : ℂ) * I) := by
  refine ⟨arg z, ?_⟩
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [hz]
  push_cast
  ring

/-- Two distinct points `z, w` of modulus `½`: `w = z e^{iψ}` with `-π < ψ ≤ π` and `ψ ≠ 0`. -/
private lemma exists_ratio_angle {z w : ℂ} (hz : ‖z‖ = 1 / 2) (hw : ‖w‖ = 1 / 2) (hzw : z ≠ w) :
    ∃ ψ : ℝ, -Real.pi < ψ ∧ ψ ≤ Real.pi ∧ ψ ≠ 0 ∧ w = z * exp ((ψ : ℂ) * I) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hun : ‖w / z‖ = 1 := by
    rw [norm_div, hz, hw]; norm_num
  have hu_eq : w / z = exp ((arg (w / z) : ℂ) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I (w / z)]
    rw [hun, ofReal_one, one_mul]
  have hw_eq : w = z * exp ((arg (w / z) : ℂ) * I) := by
    rw [← hu_eq]; field_simp
  refine ⟨arg (w / z), neg_pi_lt_arg _, arg_le_pi _, ?_, hw_eq⟩
  intro h0
  apply hzw
  rw [hw_eq, h0]
  simp

/-- The angles of the normal form: `θ = |ψ| ∈ (0, π]` and `φ = α + ψ/2`. -/
private lemma exists_normal_form (z w : ℂ) (hz : ‖z‖ = 1 / 2) (hw : ‖w‖ = 1 / 2) (hzw : z ≠ w) :
    ∃ φ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi ∧
      ((z = (1 / 2 : ℂ) * exp (((φ + θ / 2 : ℝ) : ℂ) * I) ∧
          w = (1 / 2 : ℂ) * exp (((φ - θ / 2 : ℝ) : ℂ) * I)) ∨
        (w = (1 / 2 : ℂ) * exp (((φ + θ / 2 : ℝ) : ℂ) * I) ∧
          z = (1 / 2 : ℂ) * exp (((φ - θ / 2 : ℝ) : ℂ) * I))) := by
  obtain ⟨ψ, hψlo, hψhi, hψ0, rfl⟩ := exists_ratio_angle hz hw hzw
  obtain ⟨α, rfl⟩ := exists_half_exp hz
  have hw' : (1 / 2 : ℂ) * exp ((α : ℂ) * I) * exp ((ψ : ℂ) * I) =
      (1 / 2 : ℂ) * exp (((α + ψ : ℝ) : ℂ) * I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hw']
  rcases lt_or_gt_of_ne hψ0 with hneg | hpos
  · refine ⟨α + ψ / 2, -ψ, by linarith, by linarith, Or.inl ⟨?_, ?_⟩⟩
    · rw [show α + ψ / 2 + -ψ / 2 = α by ring]
    · rw [show α + ψ / 2 - -ψ / 2 = α + ψ by ring]
  · refine ⟨α + ψ / 2, ψ, hpos, hψhi, Or.inr ⟨?_, ?_⟩⟩
    · rw [show α + ψ / 2 + ψ / 2 = α + ψ by ring]
    · rw [show α + ψ / 2 - ψ / 2 = α by ring]

theorem sec2_pair_normal_form_proved (z w : ℂ) (hz : ‖z‖ = 1 / 2) (hw : ‖w‖ = 1 / 2) (hzw : z ≠ w) :
    ∃ φ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi ∧
      ((z = (1 / 2 : ℂ) * exp (((φ + θ / 2 : ℝ) : ℂ) * I) ∧ w = (1 / 2 : ℂ) * exp (((φ - θ / 2 : ℝ) : ℂ) * I)) ∨
        (w = (1 / 2 : ℂ) * exp (((φ + θ / 2 : ℝ) : ℂ) * I) ∧ z = (1 / 2 : ℂ) * exp (((φ - θ / 2 : ℝ) : ℂ) * I))) ∧
      ∀ f : ℂ → ℂ, InS f → Q f z w = Q (rotate φ f) (zθ θ) (conj (zθ θ)) := by
  obtain ⟨φ, θ, hθ0, hθπ, hpos⟩ := exists_normal_form z w hz hw hzw
  refine ⟨φ, θ, hθ0, hθπ, hpos, fun f hf => ?_⟩
  rw [Q_rotate_zθ hf]
  rcases hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact sec2_Q_symm_proved f _ _

theorem sec2_values_eq_proved :
    {v : ℂ | ∃ f : ℂ → ℂ, InS f ∧ ∃ z w : ℂ, ‖z‖ = 1 / 2 ∧ ‖w‖ = 1 / 2 ∧ z ≠ w ∧ v = Q f z w} =
      {v : ℂ | ∃ f : ℂ → ℂ, InS f ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi ∧ v = Q f (zθ θ) (conj (zθ θ))} := by
  ext v
  constructor
  · rintro ⟨f, hf, z, w, hz, hw, hzw, rfl⟩
    obtain ⟨φ, θ, hθ0, hθπ, -, hQ⟩ := sec2_pair_normal_form_proved z w hz hw hzw
    exact ⟨rotate φ f, (lem_2_3_rot_proved f hf φ).1, θ, hθ0, hθπ, hQ f hf⟩
  · rintro ⟨f, hf, θ, hθ0, hθπ, rfl⟩
    exact ⟨f, hf, zθ θ, conj (zθ θ), norm_zθ θ, by rw [Complex.norm_conj, norm_zθ],
      zθ_ne_conj hθ0 hθπ, rfl⟩

/-! ### The Koebe function near the diagonal -/

/-- The closed form `Q_k(z, w) = 2 (1 - 3zw + zw(z + w)) / ((1 - z)(1 - w)(1 - zw))`. -/
private noncomputable def Rk (p : ℂ × ℂ) : ℂ :=
  2 * (1 - 3 * (p.1 * p.2) + p.1 * p.2 * (p.1 + p.2)) / ((1 - p.1) * (1 - p.2) * (1 - p.1 * p.2))

/-- `Q_k(z, w) = R_k(z, w)` for distinct `z, w ≠ 1` with `zw ≠ 1`: here
`k(z) - k(w) = (z - w)(1 - zw)/((1-z)²(1-w)²)` and
`zk'(z) - wk'(w) = (z - w)(z²w² + zw² + z²w - 6zw + z + w + 1)/((1-z)³(1-w)³)`. -/
private lemma Q_koebe_eq {z w : ℂ} (hz : z ≠ 1) (hw : w ≠ 1) (hzw1 : 1 - z * w ≠ 0) (hzw : z ≠ w) :
    Q koebe z w = Rk (z, w) := by
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h1w : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hden : koebe z - koebe w = (z - w) * (1 - z * w) / ((1 - z) ^ 2 * (1 - w) ^ 2) := by
    unfold koebe
    field_simp
    ring
  have hnum : z * deriv koebe z - w * deriv koebe w =
      (z - w) * (z ^ 2 * w ^ 2 + z * w ^ 2 + z ^ 2 * w - 6 * z * w + z + w + 1) /
        ((1 - z) ^ 3 * (1 - w) ^ 3) := by
    rw [deriv_koebe hz, deriv_koebe hw]
    field_simp
    ring
  unfold Q Rk
  rw [hden, hnum]
  field_simp
  ring

private lemma Rk_continuousAt : ContinuousAt Rk ((-1 / 2 : ℂ), (-1 / 2 : ℂ)) := by
  unfold Rk
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · norm_num

private lemma Rk_val : Rk ((-1 / 2 : ℂ), (-1 / 2 : ℂ)) = 0 := by
  norm_num [Rk]

/-- `Q_k(z, w) → 0` as `z, w → -½` along the circle with `z ≠ w`. -/
private lemma koebe_tendsto :
    Tendsto (fun p : ℂ × ℂ => Q koebe p.1 p.2)
        (𝓝[{p : ℂ × ℂ | ‖p.1‖ = 1 / 2 ∧ ‖p.2‖ = 1 / 2 ∧ p.1 ≠ p.2}] ((-1 / 2 : ℂ), (-1 / 2 : ℂ)))
        (𝓝 0) := by
  have hR : Tendsto Rk
      (𝓝[{p : ℂ × ℂ | ‖p.1‖ = 1 / 2 ∧ ‖p.2‖ = 1 / 2 ∧ p.1 ≠ p.2}] ((-1 / 2 : ℂ), (-1 / 2 : ℂ)))
      (𝓝 0) := by
    have h := Rk_continuousAt.tendsto
    rw [Rk_val] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine Tendsto.congr' ?_ hR
  have h1 : ∀ᶠ p : ℂ × ℂ in 𝓝 ((-1 / 2 : ℂ), (-1 / 2 : ℂ)), p.1 ≠ 1 :=
    continuousAt_fst.eventually_ne (by norm_num)
  have h2 : ∀ᶠ p : ℂ × ℂ in 𝓝 ((-1 / 2 : ℂ), (-1 / 2 : ℂ)), p.2 ≠ 1 :=
    continuousAt_snd.eventually_ne (by norm_num)
  have h3 : ∀ᶠ p : ℂ × ℂ in 𝓝 ((-1 / 2 : ℂ), (-1 / 2 : ℂ)), 1 - p.1 * p.2 ≠ 0 :=
    (by fun_prop : ContinuousAt (fun p : ℂ × ℂ => 1 - p.1 * p.2) ((-1 / 2 : ℂ), (-1 / 2 : ℂ))).eventually_ne
      (by norm_num)
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3,
    self_mem_nhdsWithin] with p hp1 hp2 hp3 hS
  exact (Q_koebe_eq hp1 hp2 hp3 hS.2.2).symm

/-- `k_π(z) = e^{-iπ} k(e^{iπ} z) = -k(-z)`. -/
private lemma rotate_pi_koebe (z : ℂ) : rotate Real.pi koebe z = -koebe (-z) := by
  unfold rotate
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  simp

/-- `Q_{k_π}(z_θ, \overline{z_θ}) = Q_k(-z_θ, -\overline{z_θ})` (Lemma 2.3 with `e^{iπ} = -1`). -/
private lemma Q_koebe_rot (θ : ℝ) :
    Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ)) = Q koebe (-zθ θ) (-conj (zθ θ)) := by
  rw [(lem_2_3_rot_proved koebe koebe_mem_S_proved Real.pi).2 _ _ (zθ_mem_ball θ)
    (conj_zθ_mem_ball θ), Complex.exp_pi_mul_I, neg_one_mul, neg_one_mul]

private lemma zθ_zero : zθ 0 = 1 / 2 := by
  simp [zθ]

private lemma continuous_zθ : Continuous zθ := by
  unfold zθ
  fun_prop

/-- `(-z_θ, -\overline{z_θ}) → (-½, -½)` as `θ → 0`. -/
private lemma pair_tendsto :
    Tendsto (fun θ : ℝ => (-zθ θ, -conj (zθ θ))) (𝓝[>] 0) (𝓝 ((-1 / 2 : ℂ), (-1 / 2 : ℂ))) := by
  have hc : Continuous (fun θ : ℝ => (-zθ θ, -conj (zθ θ))) :=
    continuous_zθ.neg.prodMk (Complex.continuous_conj.comp continuous_zθ).neg
  have h0 : (-zθ 0, -conj (zθ 0)) = ((-1 / 2 : ℂ), (-1 / 2 : ℂ)) := by
    rw [zθ_zero, map_div₀, map_one, Complex.conj_ofNat, neg_div]
  have h := hc.tendsto 0
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- For `0 < θ ≤ π` the pair `(-z_θ, -\overline{z_θ})` consists of distinct points of the circle `|z| = ½`. -/
private lemma pair_mem_set {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (-zθ θ, -conj (zθ θ)) ∈ {p : ℂ × ℂ | ‖p.1‖ = 1 / 2 ∧ ‖p.2‖ = 1 / 2 ∧ p.1 ≠ p.2} := by
  refine ⟨?_, ?_, ?_⟩
  · show ‖-zθ θ‖ = 1 / 2
    rw [norm_neg, norm_zθ]
  · show ‖-conj (zθ θ)‖ = 1 / 2
    rw [norm_neg, Complex.norm_conj, norm_zθ]
  · show -zθ θ ≠ -conj (zθ θ)
    exact fun h => zθ_ne_conj h0 hπ (neg_injective h)

private lemma pair_tendsto_within :
    Tendsto (fun θ : ℝ => (-zθ θ, -conj (zθ θ))) (𝓝[>] 0)
      (𝓝[{p : ℂ × ℂ | ‖p.1‖ = 1 / 2 ∧ ‖p.2‖ = 1 / 2 ∧ p.1 ≠ p.2}] ((-1 / 2 : ℂ), (-1 / 2 : ℂ))) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨pair_tendsto, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
  exact pair_mem_set hθ.1 hθ.2.le

/-- `Q_{k_π}(z_θ, \overline{z_θ}) → 0` as `θ → 0⁺`. -/
private lemma koebe_rot_tendsto :
    Tendsto (fun θ : ℝ => Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))) (𝓝[>] 0) (𝓝 0) := by
  have h : (fun θ : ℝ => Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))) =
      (fun p : ℂ × ℂ => Q koebe p.1 p.2) ∘ (fun θ : ℝ => (-zθ θ, -conj (zθ θ))) := by
    funext θ
    exact Q_koebe_rot θ
  rw [h]
  exact koebe_tendsto.comp pair_tendsto_within

theorem sec2_koebe_limit_proved :
    Tendsto (fun p : ℂ × ℂ => Q koebe p.1 p.2)
        (𝓝[{p : ℂ × ℂ | ‖p.1‖ = 1 / 2 ∧ ‖p.2‖ = 1 / 2 ∧ p.1 ≠ p.2}] ((-1 / 2 : ℂ), (-1 / 2 : ℂ))) (𝓝 0) ∧
      (∀ z : ℂ, rotate Real.pi koebe z = -koebe (-z)) ∧
      Tendsto (fun θ : ℝ => Q (rotate Real.pi koebe) (zθ θ) (conj (zθ θ))) (𝓝[>] 0) (𝓝 0) :=
  ⟨koebe_tendsto, rotate_pi_koebe, koebe_rot_tendsto⟩

/-! ### Lemma 2.2: injective on the circle implies injective on the closed disc -/

/-- `G` is analytic at every point of the open disc `|z| < ρ`. -/
private lemma analyticOnNhd_ball {G : ℂ → ℂ} {ρ : ℝ} (hG : HolomorphicNearClosedDisc G ρ) :
    AnalyticOnNhd ℂ G (ball (0 : ℂ) ρ) := by
  obtain ⟨U, -, hsub, hdiff⟩ := hG
  exact (hdiff.mono (ball_subset_closedBall.trans hsub)).analyticOnNhd isOpen_ball

/-- `G` is continuous on the closed disc `|z| ≤ ρ`. -/
private lemma continuousOn_closedBall {G : ℂ → ℂ} {ρ : ℝ} (hG : HolomorphicNearClosedDisc G ρ) :
    ContinuousOn G (closedBall (0 : ℂ) ρ) := by
  obtain ⟨U, -, hsub, hdiff⟩ := hG
  exact hdiff.continuousOn.mono hsub

/-- `G` is not constant on the open disc: otherwise, by continuity, it is constant on the circle, which contains
the two distinct points `ρ` and `-ρ`. -/
private lemma not_const_ball {G : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hG : HolomorphicNearClosedDisc G ρ)
    (hinj : Set.InjOn G (sphere (0 : ℂ) ρ)) : ¬ ∃ c : ℂ, ∀ z ∈ ball (0 : ℂ) ρ, G z = c := by
  rintro ⟨c, hc⟩
  have heq : Set.EqOn G (fun _ => c) (closedBall (0 : ℂ) ρ) :=
    Set.EqOn.of_subset_closure hc (continuousOn_closedBall hG) continuousOn_const ball_subset_closedBall
      (closure_ball (0 : ℂ) hρ.ne').symm.subset
  have h1 : (ρ : ℂ) ∈ sphere (0 : ℂ) ρ := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have h2 : (-(ρ : ℂ)) ∈ sphere (0 : ℂ) ρ := by
    rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have hne : (ρ : ℂ) ≠ -(ρ : ℂ) := by
    intro h
    have h0 : (ρ : ℂ) = 0 := by linear_combination h / 2
    exact hρ.ne' (by exact_mod_cast h0)
  exact hne (hinj h1 h2 (by rw [heq (sphere_subset_closedBall h1), heq (sphere_subset_closedBall h2)]))

/-- Open mapping theorem: `G` maps open subsets of the open disc to open sets. -/
private lemma isOpen_image_ball {G : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hG : HolomorphicNearClosedDisc G ρ)
    (hinj : Set.InjOn G (sphere (0 : ℂ) ρ)) : IsOpen (G '' ball (0 : ℂ) ρ) :=
  ((analyticOnNhd_ball hG).is_constant_or_isOpen (convex_ball (0 : ℂ) ρ).isPreconnected).resolve_left
    (not_const_ball hρ hG hinj) _ subset_rfl isOpen_ball

/-- At a zero `z` of `G - c` where `G` is analytic, a finite order of vanishing is at least `1`. -/
private lemma one_le_order_toNat {G : ℂ → ℂ} {z c : ℂ} (han : AnalyticAt ℂ G z) (hzc : G z = c)
    (htop : analyticOrderAt (fun x => G x - c) z ≠ ⊤) :
    1 ≤ (analyticOrderAt (fun x => G x - c) z).toNat := by
  have h0 : analyticOrderAt (fun x => G x - c) z ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨han.sub analyticAt_const, by simp [hzc]⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at h0 ⊢
  rw [ENat.toNat_natCast]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp at h0
  · exact h

/-- The argument principle at a value `c` off the image `J` of the circle: the zero set `Z` of `G - c` in the open
disc is finite, and the winding number of `J` about `c` is a natural number `S ≥ |Z|` (each zero has order `≥ 1`). -/
private lemma count_zeros (hAP : FactArgumentPrinciple) {G : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hG : HolomorphicNearClosedDisc G ρ) {c : ℂ} (hc : c ∉ G '' sphere (0 : ℂ) ρ) :
    ∃ Z : Finset ℂ, (∀ x : ℂ, x ∈ Z ↔ x ∈ ball (0 : ℂ) ρ ∧ G x = c) ∧
      ∃ S : ℕ, Z.card ≤ S ∧ (S : ℂ) = windingImage G ρ c := by
  obtain ⟨Z, hZ, htop, hsum⟩ := hAP G ρ c hρ hG (fun z hz hzc => hc ⟨z, hz, hzc⟩)
  refine ⟨Z, hZ, _, ?_, hsum⟩
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨hxb, hxc⟩ := (hZ x).mp hx
  exact one_le_order_toNat (analyticOnNhd_ball hG x hxb) hxc (htop x hx)

/-- A value taken in the open disc and lying off `J` has nonzero winding number. -/
private lemma winding_ne_zero (hAP : FactArgumentPrinciple) {G : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hG : HolomorphicNearClosedDisc G ρ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ)
    (hc : G z ∉ G '' sphere (0 : ℂ) ρ) : windingImage G ρ (G z) ≠ 0 := by
  obtain ⟨Z, hZ, S, hcard, hS⟩ := count_zeros hAP hρ hG hc
  have hzZ : z ∈ Z := (hZ z).mpr ⟨hz, rfl⟩
  have hpos : 0 < S := lt_of_lt_of_le (Finset.card_pos.mpr ⟨z, hzZ⟩) hcard
  rw [← hS]
  exact_mod_cast hpos.ne'

theorem lem_2_2_proved (hAP : FactArgumentPrinciple) (hJ : FactJordanCurve) (G : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hG : HolomorphicNearClosedDisc G ρ) (hinj : Set.InjOn G (sphere (0 : ℂ) ρ)) :
    Set.InjOn G (closedBall (0 : ℂ) ρ) := by
  obtain ⟨Ω, Ω', -, -, -, -, -, hunion, -, -, hfront, hind0, ε, hε, hindε⟩ := hJ G ρ hρ hG hinj
  have hΩJ : ∀ c ∈ Ω, c ∉ G '' sphere (0 : ℂ) ρ := fun c hc =>
    (Set.mem_compl_iff _ _).mp (hunion ▸ Set.mem_union_left Ω' hc)
  have hΩ'J : ∀ c ∈ Ω', c ∉ G '' sphere (0 : ℂ) ρ := fun c hc =>
    (Set.mem_compl_iff _ _).mp (hunion ▸ Set.mem_union_right Ω hc)
  -- Step 1: `G` maps the open disc into the bounded component `Ω`.
  have hinΩ : ∀ z ∈ ball (0 : ℂ) ρ, G z ∈ Ω := by
    intro z hz
    by_contra hnot
    have hcl : G z ∈ closure Ω' := by
      by_cases hJz : G z ∈ G '' sphere (0 : ℂ) ρ
      · rw [← hfront] at hJz
        exact frontier_subset_closure hJz
      · have hu : G z ∈ Ω ∪ Ω' := hunion ▸ hJz
        exact subset_closure (hu.resolve_left hnot)
    obtain ⟨c', ⟨z', hz', rfl⟩, hc'Ω'⟩ :=
      mem_closure_iff.mp hcl _ (isOpen_image_ball hρ hG hinj) ⟨z, hz, rfl⟩
    exact winding_ne_zero hAP hρ hG hz' (hΩ'J _ hc'Ω') (hind0 _ hc'Ω')
  -- Step 2: `G` is injective on the open disc: each value in `G(𝔻_ρ)` is taken once.
  have hinj_ball : ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ, G z = G w → z = w := by
    intro z hz w hw hzw
    have hcΩ := hinΩ z hz
    obtain ⟨Z, hZ, S, hcard, hS⟩ := count_zeros hAP hρ hG (hΩJ _ hcΩ)
    have hzZ : z ∈ Z := (hZ z).mpr ⟨hz, rfl⟩
    have hwZ : w ∈ Z := (hZ w).mpr ⟨hw, hzw.symm⟩
    rw [hindε _ hcΩ] at hS
    have hS1 : S = 1 := by
      rcases hε with rfl | rfl
      · exact_mod_cast hS
      · exfalso
        have hre := congrArg Complex.re hS
        simp at hre
        linarith [(Nat.cast_nonneg S : (0 : ℝ) ≤ S)]
    rw [hS1] at hcard
    exact Finset.card_le_one.mp hcard z hzZ w hwZ
  -- Step 3: the closed disc is the open disc together with the circle.
  intro z hz w hw hzw
  rw [← ball_union_sphere] at hz hw
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · exact hinj_ball z hz w hw hzw
  · exact absurd ⟨w, hw, hzw.symm⟩ (hΩJ _ (hinΩ z hz))
  · exact absurd ⟨z, hz, hzw⟩ (hΩJ _ (hinΩ w hw))
  · exact hinj hz hw hzw

/-! ### Proposition 2.4 -/

/-- Under the hypothesis of Proposition 2.4: `Re Q_f(z, w) > 0` for distinct `z, w` on the circle `|z| = ½`
(normal form of the pair and Lemma 2.3, rotation). -/
private lemma re_Q_pos_half
    (h : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    {f : ℂ → ℂ} (hf : InS f) {z w : ℂ} (hz : ‖z‖ = 1 / 2) (hw : ‖w‖ = 1 / 2) (hzw : z ≠ w) :
    0 < (Q f z w).re := by
  obtain ⟨φ, θ, hθ0, hθπ, -, hQ⟩ := sec2_pair_normal_form_proved z w hz hw hzw
  rw [hQ f hf]
  exact h _ (lem_2_3_rot_proved f hf φ).1 θ hθ0 hθπ

/-- Under the same hypothesis: `Re Q_f(z, w) > 0` for distinct `z, w` with `|z| = |w| = r ≤ ½`, by the dilation
`F(u) = f(2ru)/(2r)` (Lemma 2.3) and the case `r = ½`. -/
private lemma re_Q_pos
    (h : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    {f : ℂ → ℂ} (hf : InS f) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) {z w : ℂ} (hz : ‖z‖ = r)
    (hw : ‖w‖ = r) (hzw : z ≠ w) : 0 < (Q f z w).re := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2r : (2 * (r : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hr0
  have hn2r : ‖(2 * (r : ℂ))‖ = 2 * r := by
    have h2 : (2 * (r : ℂ)) = ((2 * r : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.norm_of_nonneg (by linarith)]
  have hz' : ‖z / (2 * (r : ℂ))‖ = 1 / 2 := by
    rw [norm_div, hz, hn2r]; field_simp
  have hw' : ‖w / (2 * (r : ℂ))‖ = 1 / 2 := by
    rw [norm_div, hw, hn2r]; field_simp
  have hzw' : z / (2 * (r : ℂ)) ≠ w / (2 * (r : ℂ)) := fun h => hzw ((div_left_inj' h2r).mp h)
  have hzb : z / (2 * (r : ℂ)) ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hz']; norm_num
  have hwb : w / (2 * (r : ℂ)) ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hw']; norm_num
  have hQ := (lem_2_3_dil_proved f hf r hr hr').2 _ _ hzb hwb
  have hcz : 2 * (r : ℂ) * (z / (2 * (r : ℂ))) = z := by field_simp
  have hcw : 2 * (r : ℂ) * (w / (2 * (r : ℂ))) = w := by field_simp
  rw [hcz, hcw] at hQ
  rw [← hQ]
  exact re_Q_pos_half h (lem_2_3_dil_proved f hf r hr hr').1 hz' hw' hzw'

/-- `Γ f` is holomorphic on the unit disc, a neighbourhood of `|z| ≤ ½`. -/
private lemma gam_holomorphicNear {f : ℂ → ℂ} (hf : InS f) : HolomorphicNearClosedDisc (Gam f) (1 / 2) := by
  refine ⟨ball (0 : ℂ) 1, isOpen_ball, closedBall_subset_ball (by norm_num), ?_⟩
  have hd := hf.differentiableOn
  have hd' := hd.deriv isOpen_ball
  exact (hd.add (differentiableOn_id.mul hd')).div_const 2

/-- Under the hypothesis of Proposition 2.4, `Γ f` is injective on the circle `|z| = ½` (Lemma 2.1). -/
private lemma gam_injOn_sphere
    (h : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    {f : ℂ → ℂ} (hf : InS f) : Set.InjOn (Gam f) (sphere (0 : ℂ) (1 / 2)) := by
  intro z hz w hw hzw
  by_contra hne
  rw [mem_sphere_zero_iff_norm] at hz hw
  have hzb : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hz]; norm_num
  have hwb : w ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hw]; norm_num
  have hQ0 : Q f z w = 0 := (lem_2_1_proved f hf z w hzb hwb hne).2.mp hzw
  have hpos := re_Q_pos_half h hf hz hw hne
  rw [hQ0, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

theorem prop_2_4_proved (hAP : FactArgumentPrinciple) (hJ : FactJordanCurve)
    (h : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re) :
    (∀ f : ℂ → ℂ, InS f → Set.InjOn (Gam f) (closedBall (0 : ℂ) (1 / 2))) ∧
      (∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r → z ≠ w →
        0 < (Q f z w).re) :=
  ⟨fun f hf => lem_2_2_proved hAP hJ (Gam f) (1 / 2) (by norm_num) (gam_holomorphicNear hf)
      (gam_injOn_sphere h hf),
    fun f hf _ hr hr' _ _ hz hw hzw => re_Q_pos h hf hr hr' hz hw hzw⟩

/-! ### Section 8: the assembly -/

/-- The three ranges `(0, θ₀]`, `[50.3°, 135°]`, `[135°, 180°]` cover `(0, π]`, and on each the hypothesis gives
`Re Q_f(z_θ, \overline{z_θ}) > 0` (on the first, `sin²(θ/2)/80 > 0` since `0 < θ/2 ≤ π/2`). -/
private lemma re_Q_pos_all
    (hnear : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hmiddle : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    (hfar : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re) :
    ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi → 0 < (Q f (zθ θ) (conj (zθ θ))).re := by
  intro f hf θ hθ0 hθπ
  rcases sec8_cover_proved.2 θ hθ0 hθπ with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
  · have hs : 0 < Real.sin (θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hle := hnear f hf θ hθ0 h1
    have hpos : 0 < Real.sin (θ / 2) ^ 2 / 80 := div_pos (pow_pos hs 2) (by norm_num)
    linarith
  · exact hmiddle f hf θ h2a h2b
  · have hlt := hfar f hf θ h3a h3b
    linarith

theorem sec8_assembly_proved (hAP : FactArgumentPrinciple) (hJ : FactJordanCurve)
    (hnear : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      Real.sin (θ / 2) ^ 2 / 80 ≤ (Q f (zθ θ) (conj (zθ θ))).re)
    (hmiddle : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 50.3 ≤ θ → θ ≤ deg 135 → 0 < (Q f (zθ θ) (conj (zθ θ))).re)
    (hfar : ∀ f : ℂ → ℂ, InS f → ∀ θ : ℝ, deg 135 ≤ θ → θ ≤ deg 180 →
      1 / 2000 < (Q f (zθ θ) (conj (zθ θ))).re) :
    ((∀ f : ℂ → ℂ, InS f → Set.InjOn (Gam f) (closedBall (0 : ℂ) (1 / 2))) ∧
        ∀ r : ℝ, 1 / 2 < r → ∃ f : ℂ → ℂ, InS f ∧ ¬ Set.InjOn (Gam f) (ball (0 : ℂ) r)) ∧
      (∀ f : ℂ → ℂ, InS f → ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r → z ≠ w →
        0 < (Q f z w).re) := by
  obtain ⟨h11, h12⟩ := prop_2_4_proved hAP hJ (re_Q_pos_all hnear hmiddle hfar)
  exact ⟨⟨h11, fun r hr => ⟨koebe, koebe_mem_S_proved, Gam_koebe_not_injOn hr⟩⟩, h12⟩

end Robinson.Proofs
