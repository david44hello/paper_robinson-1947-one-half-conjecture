/-
Robinson/Proofs/Sec7G.lean — proofs of lem_7_3, eq_UR, lem_7_4, prop_7_5_ii.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Robinson.Defs.Grunsky
import Robinson.NotFormalized
import Robinson.Proofs.Sec7Lin

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

namespace Sec7G

/-! ## The point `s = s_θ = 2^{-1/2} e^{iθ/4}` and `t = s̄` -/

/-- `c = 1/√2`. -/
lemma c_pos : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr two_pos)

lemma c_sq : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

lemma norm_s (θ : ℝ) : ‖sθ θ‖ = (Real.sqrt 2)⁻¹ := by
  rw [sθ, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos c_pos, mul_one]

lemma norm_t (θ : ℝ) : ‖conj (sθ θ)‖ = (Real.sqrt 2)⁻¹ := by rw [Complex.norm_conj, norm_s]

lemma c_lt_one : (Real.sqrt 2)⁻¹ < 1 := by
  rw [inv_lt_one₀ (Real.sqrt_pos.mpr two_pos)]
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma s_mem (θ : ℝ) : sθ θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_s]; exact c_lt_one

lemma t_mem (θ : ℝ) : conj (sθ θ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_t]; exact c_lt_one

/-- `s = c (cos(θ/4) + i sin(θ/4))`. -/
lemma s_eq (θ : ℝ) : sθ θ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    ((Real.cos (θ / 4) : ℂ) + (Real.sin (θ / 4) : ℂ) * I) := by
  rw [sθ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `t = s̄ = c (cos(θ/4) - i sin(θ/4))`. -/
lemma t_eq (θ : ℝ) : conj (sθ θ) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    ((Real.cos (θ / 4) : ℂ) - (Real.sin (θ / 4) : ℂ) * I) := by
  rw [s_eq, map_mul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_I]
  ring

lemma s_sq (θ : ℝ) : sθ θ ^ 2 = zθ θ := by
  rw [sθ, zθ, mul_pow, ← Complex.exp_nat_mul]
  have h2 : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, c_sq]; push_cast; ring
  rw [h2]
  congr 2
  push_cast
  ring

lemma t_sq (θ : ℝ) : conj (sθ θ) ^ 2 = conj (zθ θ) := by rw [← map_pow, s_sq]

lemma sin_q_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < Real.sin (θ / 4) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

lemma cos_q_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : 0 < Real.cos (θ / 4) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

lemma s_ne_zero (θ : ℝ) : sθ θ ≠ 0 := by
  intro h; have := norm_s θ; rw [h, norm_zero] at this; exact c_pos.ne' this.symm

lemma t_ne_zero (θ : ℝ) : conj (sθ θ) ≠ 0 := by
  rw [map_ne_zero]; exact s_ne_zero θ

lemma s_sub_t (θ : ℝ) : sθ θ - conj (sθ θ) =
    2 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Real.sin (θ / 4) : ℂ) * I := by
  rw [t_eq, s_eq]; ring

lemma s_add_t (θ : ℝ) : sθ θ + conj (sθ θ) =
    2 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Real.cos (θ / 4) : ℂ) := by
  rw [t_eq, s_eq]; ring

lemma s_ne_t {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : sθ θ ≠ conj (sθ θ) := by
  intro h
  have h1 := s_sub_t θ
  rw [sub_eq_zero.mpr h] at h1
  have hc : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast c_pos.ne'
  have hs : (Real.sin (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast (sin_q_pos h0 hπ).ne'
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hs) I_ne_zero) h1.symm

lemma s_ne_neg_t {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : sθ θ ≠ -conj (sθ θ) := by
  intro h
  have h1 := s_add_t θ
  rw [eq_neg_iff_add_eq_zero.mp h] at h1
  have hc : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast c_pos.ne'
  have hs : (Real.cos (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast (cos_q_pos h0 hπ).ne'
  exact (mul_ne_zero (mul_ne_zero two_ne_zero hc) hs) h1.symm

/-- `i tan(θ/4) (s + t)/(s - t) = 1`. -/
lemma tan_ratio {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    I * (Real.tan (θ / 4) : ℂ) * ((sθ θ + conj (sθ θ)) / (sθ θ - conj (sθ θ))) = 1 := by
  rw [s_add_t, s_sub_t, Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  have hc : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast c_pos.ne'
  have hs : (Real.sin (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast (sin_q_pos h0 hπ).ne'
  have hco : (Real.cos (θ / 4) : ℂ) ≠ 0 := by exact_mod_cast (cos_q_pos h0 hπ).ne'
  have key : ∀ S Co c : ℂ, S ≠ 0 → Co ≠ 0 → c ≠ 0 →
      I * (S / Co) * ((2 * c * Co) / (2 * c * S * I)) = 1 := by
    intro S Co c hS hCo hc'
    have hI := I_ne_zero
    field_simp
  exact key _ _ _ hs hco hc

/-- `e^{iθ/2} = s / t`. -/
lemma exp_half (θ : ℝ) : exp (I * ((θ / 2 : ℝ) : ℂ)) = sθ θ / conj (sθ θ) := by
  have hc : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast c_pos.ne'
  have ht : conj (sθ θ) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * exp (-(((θ / 4 : ℝ) : ℂ) * I)) := by
    rw [sθ, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_neg]
  rw [ht, sθ, mul_div_mul_left _ _ hc, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

lemma norm_zθ (θ : ℝ) : ‖zθ θ‖ = 1 / 2 := by
  rw [zθ, norm_mul, Complex.norm_exp_ofReal_mul_I]; norm_num

lemma z_mem (θ : ℝ) : zθ θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_zθ]; norm_num

lemma w_mem (θ : ℝ) : conj (zθ θ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_conj, norm_zθ]; norm_num

lemma z_ne_w {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) : zθ θ ≠ conj (zθ θ) := by
  intro h
  have him : (zθ θ).im = 1 / 2 * Real.sin (θ / 2) := by
    rw [zθ, Complex.mul_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
    simp
  have hpos : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h2 := congrArg Complex.im h
  rw [Complex.conj_im, him] at h2
  linarith

/-! ## Conjugation and real/imaginary parts of the vectors -/

lemma aOdd_conj (s : ℂ) (n : ℕ) : aOdd (conj s) n = conj (aOdd s n) := by
  unfold aOdd; split_ifs <;> simp [map_div₀, map_pow, Complex.conj_ofReal]

lemma aEven_conj (s : ℂ) (n : ℕ) : aEven (conj s) n = conj (aEven s n) := by
  unfold aEven; split_ifs <;> simp [map_div₀, map_pow, Complex.conj_ofReal]

lemma bEven_conj (s : ℂ) (n : ℕ) : bEven (conj s) n = conj (bEven s n) := by
  unfold bEven; split_ifs <;> simp [map_pow, Complex.conj_ofReal]

lemma re_add_im' (z : ℂ) : z = (z.re : ℂ) + I * (z.im : ℂ) := by
  conv_lhs => rw [← Complex.re_add_im z]
  ring

lemma conj_re_im (z : ℂ) : conj z = (z.re : ℂ) + (-I) * (z.im : ℂ) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-! ## Domination of the vectors and absolute summability of the double series -/

/-- The radius `r = (5/4)/√2 < 1`. -/
noncomputable def rr : ℝ := 5 / 4 * (Real.sqrt 2)⁻¹

lemma rr_pos : 0 < rr := mul_pos (by norm_num) c_pos

lemma rr_lt_one : rr < 1 := by
  have h : rr ^ 2 = 25 / 32 := by rw [rr, mul_pow, c_sq]; norm_num
  nlinarith [rr_pos]

lemma c_le_rr : (Real.sqrt 2)⁻¹ ≤ rr := by
  rw [rr]; nlinarith [c_pos]

/-- A vector is dominated if `‖x n‖ √n ≤ 4 rⁿ`. -/
def Dom (x : ℕ → ℂ) : Prop := ∀ n : ℕ, ‖x n‖ * Real.sqrt n ≤ 4 * rr ^ n

lemma pow_c_le (n : ℕ) : ((Real.sqrt 2)⁻¹) ^ n ≤ 4 * rr ^ n := by
  have h1 : ((Real.sqrt 2)⁻¹) ^ n ≤ rr ^ n := pow_le_pow_left₀ c_pos.le c_le_rr n
  have h2 : 0 ≤ rr ^ n := pow_nonneg rr_pos.le n
  linarith

lemma sqrt_cast_pos {n : ℕ} (hn : n ≠ 0) : 0 < Real.sqrt n :=
  Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn)

lemma norm_pow_div_sqrt_mul {z : ℂ} {n : ℕ} (hn : n ≠ 0) :
    ‖z ^ n / (Real.sqrt n : ℂ)‖ * Real.sqrt n = ‖z‖ ^ n := by
  have hp := sqrt_cast_pos hn
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_mul_cancel₀ _ hp.ne']

lemma dom_aOdd {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) : Dom (aOdd z) := by
  intro n
  unfold aOdd
  split_ifs with h
  · have hn : n ≠ 0 := by omega
    rw [norm_pow_div_sqrt_mul hn, hz]; exact pow_c_le n
  · simp only [norm_zero, zero_mul]; exact mul_nonneg (by norm_num) (pow_nonneg rr_pos.le n)

lemma dom_aEven {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) : Dom (aEven z) := by
  intro n
  unfold aEven
  split_ifs with h
  · rw [norm_pow_div_sqrt_mul h.2, hz]; exact pow_c_le n
  · simp only [norm_zero, zero_mul]; exact mul_nonneg (by norm_num) (pow_nonneg rr_pos.le n)

/-- `n ≤ 4 (5/4)ⁿ` (Bernoulli). -/
lemma nat_le_four_pow (n : ℕ) : (n : ℝ) ≤ 4 * (5 / 4 : ℝ) ^ n := by
  have h := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1 / 4) n
  norm_num at h
  linarith

lemma dom_bEven {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) : Dom (bEven z) := by
  intro n
  unfold bEven
  split_ifs with h
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hz]
    have e : Real.sqrt n * ((Real.sqrt 2)⁻¹) ^ n * Real.sqrt n = (n : ℝ) * ((Real.sqrt 2)⁻¹) ^ n := by
      rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    rw [e, rr, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (nat_le_four_pow n) (pow_nonneg c_pos.le n)
  · simp only [norm_zero, zero_mul]; exact mul_nonneg (by norm_num) (pow_nonneg rr_pos.le n)

lemma dom_re {x : ℕ → ℂ} (hx : Dom x) : Dom (fun n => ((x n).re : ℂ)) := by
  intro n
  refine le_trans ?_ (hx n)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (Real.sqrt_nonneg _)

lemma dom_im {x : ℕ → ℂ} (hx : Dom x) : Dom (fun n => ((x n).im : ℂ)) := by
  intro n
  refine le_trans ?_ (hx n)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) (Real.sqrt_nonneg _)

lemma norm_Cmat_le (γ : ℕ → ℕ → ℂ) (n m : ℕ) :
    ‖Cmat γ n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖ := by
  rw [Cmat, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_mul (Nat.cast_nonneg n)]

lemma norm_Oblock_le (γ : ℕ → ℕ → ℂ) (n m : ℕ) :
    ‖Oblock γ n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖ := by
  unfold Oblock; split_ifs
  · exact norm_Cmat_le γ n m
  · rw [norm_zero]; positivity

lemma norm_Eblock_le (γ : ℕ → ℕ → ℂ) (n m : ℕ) :
    ‖Eblock γ n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖ := by
  unfold Eblock; split_ifs
  · exact norm_Cmat_le γ n m
  · rw [norm_zero]; positivity

/-- The coefficient series at radius `r`. -/
lemma gamma_summable {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) :
    Summable fun p : ℕ × ℕ => ‖γ p.1 p.2‖ * rr ^ p.1 * rr ^ p.2 := by
  have hm : ((rr : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rr_pos]; exact rr_lt_one
  refine ((hγ.2 _ _ hm hm).1).congr fun p => ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rr_pos]

lemma summable_dom {γ : ℕ → ℕ → ℂ} (hγ : Summable fun p : ℕ × ℕ => ‖γ p.1 p.2‖ * rr ^ p.1 * rr ^ p.2)
    {A : ℕ → ℕ → ℂ} (hA : ∀ n m, ‖A n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖)
    {x y : ℕ → ℂ} (hx : Dom x) (hy : Dom y) :
    Summable fun p : ℕ × ℕ => ‖x p.1 * A p.1 p.2 * y p.2‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (hγ.mul_left 16)
  obtain ⟨n, m⟩ := p
  have hxn := hx n
  have hym := hy m
  have hAnm := hA n m
  have e1 : ‖x n * A n m * y m‖ = ‖x n‖ * ‖A n m‖ * ‖y m‖ := by rw [norm_mul, norm_mul]
  rw [e1]
  have hg := norm_nonneg (γ n m)
  have h1 : ‖x n‖ * ‖A n m‖ * ‖y m‖ ≤ ‖x n‖ * (Real.sqrt n * Real.sqrt m * ‖γ n m‖) * ‖y m‖ := by
    gcongr
  refine h1.trans ?_
  have e2 : ‖x n‖ * (Real.sqrt n * Real.sqrt m * ‖γ n m‖) * ‖y m‖ =
      (‖x n‖ * Real.sqrt n) * (‖y m‖ * Real.sqrt m) * ‖γ n m‖ := by ring
  rw [e2]
  have h3 : (‖x n‖ * Real.sqrt n) * (‖y m‖ * Real.sqrt m) ≤ (4 * rr ^ n) * (4 * rr ^ m) :=
    mul_le_mul hxn hym (by positivity) (mul_nonneg (by norm_num) (pow_nonneg rr_pos.le n))
  calc (‖x n‖ * Real.sqrt n) * (‖y m‖ * Real.sqrt m) * ‖γ n m‖ ≤ (4 * rr ^ n) * (4 * rr ^ m) * ‖γ n m‖ :=
        mul_le_mul_of_nonneg_right h3 hg
    _ = 16 * (‖γ n m‖ * rr ^ n * rr ^ m) := by ring

/-! ## The double series `xᵀ A y` as a sum over `ℕ × ℕ` -/

lemma bilinf_eq_tsum {x y : ℕ → ℂ} {A : ℕ → ℕ → ℂ}
    (h : Summable fun p : ℕ × ℕ => ‖x p.1 * A p.1 p.2 * y p.2‖) :
    bilinf x A y = ∑' p : ℕ × ℕ, x p.1 * A p.1 p.2 * y p.2 := by
  rw [h.of_norm.tsum_prod]
  unfold bilinf
  refine tsum_congr fun n => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by show x n * (A n m * y m) = x n * A n m * y m; ring

lemma bilinf_expand {x1 x2 y1 y2 : ℕ → ℂ} {A : ℕ → ℕ → ℂ} (c d : ℂ)
    (h11 : Summable fun p : ℕ × ℕ => ‖x1 p.1 * A p.1 p.2 * y1 p.2‖)
    (h12 : Summable fun p : ℕ × ℕ => ‖x1 p.1 * A p.1 p.2 * y2 p.2‖)
    (h21 : Summable fun p : ℕ × ℕ => ‖x2 p.1 * A p.1 p.2 * y1 p.2‖)
    (h22 : Summable fun p : ℕ × ℕ => ‖x2 p.1 * A p.1 p.2 * y2 p.2‖) :
    bilinf (fun n => x1 n + c * x2 n) A (fun m => y1 m + d * y2 m) =
      bilinf x1 A y1 + d * bilinf x1 A y2 + c * bilinf x2 A y1 + c * d * bilinf x2 A y2 := by
  have e : ∀ p : ℕ × ℕ, (x1 p.1 + c * x2 p.1) * A p.1 p.2 * (y1 p.2 + d * y2 p.2) =
      x1 p.1 * A p.1 p.2 * y1 p.2 + d * (x1 p.1 * A p.1 p.2 * y2 p.2) +
        c * (x2 p.1 * A p.1 p.2 * y1 p.2) + (c * d) * (x2 p.1 * A p.1 p.2 * y2 p.2) := fun p => by ring
  have hsum : Summable fun p : ℕ × ℕ => ‖(x1 p.1 + c * x2 p.1) * A p.1 p.2 * (y1 p.2 + d * y2 p.2)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (((h11.add (h12.mul_left ‖d‖)).add (h21.mul_left ‖c‖)).add (h22.mul_left ‖c * d‖))
    rw [e p]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl (le_of_eq (norm_mul _ _)))) (le_of_eq (norm_mul _ _))))
      (le_of_eq (norm_mul _ _)))
  have H := bilinf_eq_tsum (x := fun n => x1 n + c * x2 n) (y := fun m => y1 m + d * y2 m) (A := A) hsum
  beta_reduce at H
  rw [H, tsum_congr e, bilinf_eq_tsum h11, bilinf_eq_tsum h12, bilinf_eq_tsum h21, bilinf_eq_tsum h22]
  have s11 := h11.of_norm
  have s12 := h12.of_norm.mul_left d
  have s21 := h21.of_norm.mul_left c
  have s22 := h22.of_norm.mul_left (c * d)
  rw [((s11.add s12).add s21).tsum_add s22, (s11.add s12).tsum_add s21, s11.tsum_add s12,
    tsum_mul_left, tsum_mul_left, tsum_mul_left]

lemma bilinf_swap {x y : ℕ → ℂ} {A : ℕ → ℕ → ℂ} (hA : ∀ n m, A n m = A m n)
    (h : Summable fun p : ℕ × ℕ => ‖x p.1 * A p.1 p.2 * y p.2‖)
    (h' : Summable fun p : ℕ × ℕ => ‖y p.1 * A p.1 p.2 * x p.2‖) :
    bilinf x A y = bilinf y A x := by
  rw [bilinf_eq_tsum h, bilinf_eq_tsum h',
    ← (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ => y p.1 * A p.1 p.2 * x p.2)]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [hA p.2 p.1]; ring

lemma bilinf_smul (x y : ℕ → ℂ) (A : ℕ → ℕ → ℂ) (c d : ℂ) :
    bilinf (fun n => c * x n) A (fun m => d * y m) = c * d * bilinf x A y := by
  unfold bilinf
  have hin : ∀ n, ∑' m, A n m * (d * y m) = d * ∑' m, A n m * y m := fun n => by
    rw [← tsum_mul_left]; exact tsum_congr fun m => by ring
  simp only [hin]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- Square partial sums of an (unconditionally) summable double series converge to its sum. -/
lemma tendsto_square {F : ℕ × ℕ → ℂ} {S : ℂ} (hF : HasSum F S) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, F (n, m)) atTop (𝓝 S) := by
  have hmono : Monotone (fun N : ℕ => Finset.range N ×ˢ Finset.range N) := fun a b hab =>
    Finset.product_subset_product (Finset.range_mono hab) (Finset.range_mono hab)
  have hcov : ∀ p : ℕ × ℕ, ∃ N, p ∈ Finset.range N ×ˢ Finset.range N := fun p =>
    ⟨max p.1 p.2 + 1, by simp only [Finset.mem_product, Finset.mem_range]; omega⟩
  have ht : Tendsto (fun s : Finset (ℕ × ℕ) => ∑ p ∈ s, F p) atTop (𝓝 S) := hF
  refine (ht.comp (Filter.tendsto_atTop_finset_of_monotone hmono hcov)).congr fun N => ?_
  simp only [Function.comp_apply, Finset.sum_product]

lemma tendsto_square_bilinf {x y : ℕ → ℂ} {A : ℕ → ℕ → ℂ}
    (h : Summable fun p : ℕ × ℕ => ‖x p.1 * A p.1 p.2 * y p.2‖) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * A n m * y m) atTop
      (𝓝 (bilinf x A y)) := by
  have hS : HasSum (fun p : ℕ × ℕ => x p.1 * A p.1 p.2 * y p.2) (bilinf x A y) := by
    rw [bilinf_eq_tsum h]; exact h.of_norm.hasSum
  have ht := tendsto_square hS
  exact ht

/-- The bound `|xᵀ A y| ≤ ‖x‖ ‖y‖` from the bound on every finite section. -/
lemma bilinf_norm_le {x y : ℕ → ℂ} {A : ℕ → ℕ → ℂ}
    (h : Summable fun p : ℕ × ℕ => ‖x p.1 * A p.1 p.2 * y p.2‖)
    (hx : Summable fun n => ‖x n‖ ^ 2) (hy : Summable fun n => ‖y n‖ ^ 2)
    (hfin : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * A n m * y m‖ ≤
      Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2)) :
    ‖bilinf x A y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2) := by
  refine le_of_tendsto' (tendsto_square_bilinf h).norm fun N => (hfin N).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt (hx.sum_le_tsum _ fun _ _ => sq_nonneg _))
    (Real.sqrt_le_sqrt (hy.sum_le_tsum _ fun _ _ => sq_nonneg _)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## The same statements for dominated vectors -/

lemma bilinf_expand_dom {γ : ℕ → ℕ → ℂ} (hg : Summable fun p : ℕ × ℕ => ‖γ p.1 p.2‖ * rr ^ p.1 * rr ^ p.2)
    {A : ℕ → ℕ → ℂ} (hA : ∀ n m, ‖A n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖)
    {x1 x2 y1 y2 : ℕ → ℂ} (c d : ℂ) (hx1 : Dom x1) (hx2 : Dom x2) (hy1 : Dom y1) (hy2 : Dom y2) :
    bilinf (fun n => x1 n + c * x2 n) A (fun m => y1 m + d * y2 m) =
      bilinf x1 A y1 + d * bilinf x1 A y2 + c * bilinf x2 A y1 + c * d * bilinf x2 A y2 :=
  bilinf_expand (x1 := x1) (x2 := x2) (y1 := y1) (y2 := y2) (A := A) c d (summable_dom hg hA hx1 hy1)
    (summable_dom hg hA hx1 hy2) (summable_dom hg hA hx2 hy1) (summable_dom hg hA hx2 hy2)

lemma bilinf_swap_dom {γ : ℕ → ℕ → ℂ} (hg : Summable fun p : ℕ × ℕ => ‖γ p.1 p.2‖ * rr ^ p.1 * rr ^ p.2)
    {A : ℕ → ℕ → ℂ} (hA : ∀ n m, ‖A n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖)
    (hsym : ∀ n m, A n m = A m n) {x y : ℕ → ℂ} (hx : Dom x) (hy : Dom y) :
    bilinf x A y = bilinf y A x :=
  bilinf_swap (x := x) (y := y) (A := A) hsym (summable_dom hg hA hx hy) (summable_dom hg hA hy hx)

lemma tendsto_square_dom {γ : ℕ → ℕ → ℂ} (hg : Summable fun p : ℕ × ℕ => ‖γ p.1 p.2‖ * rr ^ p.1 * rr ^ p.2)
    {A : ℕ → ℕ → ℂ} (hA : ∀ n m, ‖A n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖)
    {x y : ℕ → ℂ} (hx : Dom x) (hy : Dom y) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * A n m * y m) atTop
      (𝓝 (bilinf x A y)) :=
  tendsto_square_bilinf (x := x) (y := y) (A := A) (summable_dom hg hA hx hy)

/-! ## The norms `‖a(s)‖² + ‖a_e(s)‖² = log 2` on `|s|² = ½` -/

lemma norm_sq_term {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) {n : ℕ} (_hn : n ≠ 0) :
    ‖z ^ n / (Real.sqrt n : ℂ)‖ ^ 2 = (1 / 2 : ℝ) ^ n / n := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), ← pow_mul, mul_comm, pow_mul, hz, c_sq]

/-- The termwise value `(1/2)ⁿ/n` (`0` at `n = 0`). -/
noncomputable def tT (n : ℕ) : ℝ := if n = 0 then 0 else (1 / 2 : ℝ) ^ n / n

lemma tT_nonneg (n : ℕ) : 0 ≤ tT n := by
  unfold tT; split_ifs
  · exact le_rfl
  · positivity

lemma sq_aOdd_add_aEven {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) (n : ℕ) :
    ‖aOdd z n‖ ^ 2 + ‖aEven z n‖ ^ 2 = tT n := by
  unfold aOdd aEven tT
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases hodd : n % 2 = 1
    · have he : ¬ (n % 2 = 0 ∧ n ≠ 0) := by omega
      rw [if_pos hodd, if_neg he, if_neg h0, norm_sq_term hz h0]; simp
    · have he : n % 2 = 0 ∧ n ≠ 0 := ⟨by omega, h0⟩
      rw [if_neg hodd, if_pos he, if_neg h0, norm_sq_term hz h0]; simp

lemma hasSum_tT : HasSum tT (Real.log 2) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / 2) (by rw [abs_of_pos (by norm_num)]; norm_num)
  have e : -Real.log (1 - 1 / 2) = Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [e] at h
  have h' : HasSum (fun n => tT (n + 1)) (Real.log 2) := by
    refine h.congr_fun fun n => ?_
    unfold tT; rw [if_neg (Nat.succ_ne_zero n)]; push_cast; ring
  have := (hasSum_nat_add_iff (f := tT) 1).mp h'
  simpa [tT] using this

lemma summable_sq_aOdd {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) : Summable fun n => ‖aOdd z n‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun n => by rw [← sq_aOdd_add_aEven hz n]; nlinarith [sq_nonneg ‖aEven z n‖]) hasSum_tT.summable

lemma summable_sq_aEven {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) : Summable fun n => ‖aEven z n‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun n => by rw [← sq_aOdd_add_aEven hz n]; nlinarith [sq_nonneg ‖aOdd z n‖]) hasSum_tT.summable

lemma tsum_sq_add {z : ℂ} (hz : ‖z‖ = (Real.sqrt 2)⁻¹) :
    ∑' n, ‖aOdd z n‖ ^ 2 + ∑' n, ‖aEven z n‖ ^ 2 = Real.log 2 := by
  rw [← (summable_sq_aOdd hz).tsum_add (summable_sq_aEven hz)]
  rw [tsum_congr (sq_aOdd_add_aEven hz)]
  exact hasSum_tT.tsum_eq

lemma log_two_lt_quarter_pi : Real.log 2 < Real.pi / 4 := by
  have := Real.log_two_lt_d9; have := Real.pi_gt_d2; linarith

/-! ## The kernel of the odd root at `(s, -s)`: `exp K_h(s, -s) = s / h(s)` -/

lemma kernelQuot_neg {h : ℂ → ℂ} {s : ℂ} (hs : s ≠ 0) (hodd : h (-s) = -h s) :
    kernelQuot h s (-s) = s / h s := by
  have hss : s ≠ -s := fun e => hs (by linear_combination e / 2)
  have hns : -s ≠ 0 := neg_ne_zero.mpr hs
  unfold kernelQuot
  rw [if_neg hss, if_neg hs, if_neg hns, hodd]
  by_cases h0 : h s = 0
  · simp [h0]
  · have h2 : s - -s ≠ 0 := sub_ne_zero.mpr hss
    field_simp

/-! ## The branch of `Δ` -/

lemma log_ratio {χ : ℂ} (hχ : 0 < χ.im) :
    -log (1 + χ) + log (1 - χ) = log ((1 - χ) / (1 + χ)) ∧
      -Real.pi < arg ((1 - χ) / (1 + χ)) ∧ arg ((1 - χ) / (1 + χ)) < 0 := by
  have h1 : 1 + χ ≠ 0 := fun e => by
    have := congrArg Complex.im e; simp at this; linarith
  have h2 : 1 - χ ≠ 0 := fun e => by
    have := congrArg Complex.im e; simp at this; linarith
  have hρ0 : (1 - χ) / (1 + χ) ≠ 0 := div_ne_zero h2 h1
  have hn : 0 < Complex.normSq (1 + χ) := Complex.normSq_pos.mpr h1
  have hρim : ((1 - χ) / (1 + χ)).im = -2 * χ.im / Complex.normSq (1 + χ) := by
    rw [Complex.div_im]
    simp only [Complex.sub_im, Complex.one_im, Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im]
    field_simp
    ring
  have hneg : ((1 - χ) / (1 + χ)).im < 0 := by
    rw [hρim]; exact div_neg_of_neg_of_pos (by linarith) hn
  have ha1 : arg ((1 - χ) / (1 + χ)) < 0 := Complex.arg_neg_iff.mpr hneg
  have ha2 := Complex.neg_pi_lt_arg ((1 - χ) / (1 + χ))
  have hb1 : 0 ≤ arg (1 + χ) := Complex.arg_nonneg_iff.mpr (by simp; linarith)
  have hb2 := Complex.arg_le_pi (1 + χ)
  have hmul : log ((1 - χ) / (1 + χ) * (1 + χ)) = log ((1 - χ) / (1 + χ)) + log (1 + χ) :=
    (Complex.log_mul_eq_add_log_iff hρ0 h1).mpr ⟨by linarith, by linarith⟩
  rw [div_mul_cancel₀ _ h1] at hmul
  refine ⟨?_, ha2, ha1⟩
  rw [hmul]; ring

/-- Two numbers with the same exponential: `iθ/2 - Log(1 + χ) + Log(1 - χ)` has imaginary part in
`(θ/2 - π, θ/2)` when `Im χ > 0`, and `|K_s - K_t| < π`, so they are equal. -/
lemma delta_eq {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) {χ Ks Kt : ℂ} (hχ : 0 < χ.im)
    (hexp : exp (I * ((θ / 2 : ℝ) : ℂ) - log (1 + χ) + log (1 - χ)) = exp (Ks - Kt))
    (hK : ‖Ks - Kt‖ < Real.pi) :
    I * ((θ / 2 : ℝ) : ℂ) - log (1 + χ) + log (1 - χ) = Ks - Kt := by
  obtain ⟨hlog, ha2, ha1⟩ := log_ratio hχ
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg Complex.im hk
  have e1 : (I * ((θ / 2 : ℝ) : ℂ) - log (1 + χ) + log (1 - χ)).im =
      θ / 2 + arg ((1 - χ) / (1 + χ)) := by
    rw [show I * ((θ / 2 : ℝ) : ℂ) - log (1 + χ) + log (1 - χ) =
      I * ((θ / 2 : ℝ) : ℂ) + (-log (1 + χ) + log (1 - χ)) by ring, hlog, Complex.add_im, Complex.log_im]
    simp
  have e2 : (Ks - Kt + (k : ℂ) * (2 * Real.pi * I)).im = (Ks - Kt).im + 2 * Real.pi * k := by
    simp [Complex.mul_im]
    ring
  rw [e1, e2] at him
  have hb := abs_le.mp ((Complex.abs_im_le_norm (Ks - Kt)).trans hK.le)
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc0
    have hc := not_lt.mp hc0
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hc0
    have hc := not_lt.mp hc0
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have hlt : (Ks - Kt).im < Real.pi := lt_of_le_of_lt (le_abs_self _)
      (lt_of_le_of_lt (Complex.abs_im_le_norm _) hK)
    linarith
  have hk0 : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk, hk0]; simp

/-- `Im(i tan(θ/4) e^{2κ}) > 0` when `|κ| < π/4`. -/
lemma chi_im_pos_of {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi) {κ : ℂ} (hκ : ‖κ‖ < Real.pi / 4) :
    0 < (I * (Real.tan (θ / 4) : ℂ) * exp (2 * κ)).im := by
  have ht : 0 < Real.tan (θ / 4) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [Real.pi_pos])
  have him : |(2 * κ).im| < Real.pi / 2 := by
    calc |(2 * κ).im| ≤ ‖2 * κ‖ := Complex.abs_im_le_norm _
      _ = 2 * ‖κ‖ := by rw [norm_mul]; norm_num
      _ < Real.pi / 2 := by linarith
  have hcos : 0 < Real.cos ((2 * κ).im) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp him).1], (abs_lt.mp him).2⟩
  have hre : 0 < (exp (2 * κ)).re := by
    rw [Complex.exp_re]; exact mul_pos (Real.exp_pos _) hcos
  have e : (I * (Real.tan (θ / 4) : ℂ) * exp (2 * κ)).im = Real.tan (θ / 4) * (exp (2 * κ)).re := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [e]
  exact mul_pos ht hre

/-! ## `a(s) = u + i v`, `a_e(s) = u_e + i v_e`, `b_e(s) = β₀ + i β₁` -/

lemma aOdd_s_eq (θ : ℝ) : aOdd (sθ θ) = fun n => (uvec θ n : ℂ) + I * (vvec θ n : ℂ) :=
  funext fun _ => re_add_im' _

lemma aOdd_t_eq (θ : ℝ) : aOdd (conj (sθ θ)) = fun n => (uvec θ n : ℂ) + (-I) * (vvec θ n : ℂ) :=
  funext fun _ => by rw [aOdd_conj, conj_re_im]; rfl

lemma dom_u (θ : ℝ) : Dom (fun n => (uvec θ n : ℂ)) := dom_re (dom_aOdd (norm_s θ))

lemma dom_v (θ : ℝ) : Dom (fun n => (vvec θ n : ℂ)) := dom_im (dom_aOdd (norm_s θ))

lemma w_fun (θ : ℝ) :
    aEven (sθ θ) = (fun n => (wEven θ 0 n : ℂ) + I * (wEven θ 1 n : ℂ)) ∧
    aEven (conj (sθ θ)) = (fun n => (wEven θ 0 n : ℂ) + (-I) * (wEven θ 1 n : ℂ)) ∧
    bEven (sθ θ) = (fun n => (wEven θ 2 n : ℂ) + I * (wEven θ 3 n : ℂ)) ∧
    bEven (conj (sθ θ)) = (fun n => (wEven θ 2 n : ℂ) + (-I) * (wEven θ 3 n : ℂ)) := by
  refine ⟨funext fun n => ?_, funext fun n => ?_, funext fun n => ?_, funext fun n => ?_⟩
  · simp only [wEven]; exact re_add_im' _
  · rw [aEven_conj, conj_re_im]; simp [wEven]
  · simp only [wEven]; exact re_add_im' _
  · rw [bEven_conj, conj_re_im]; simp [wEven]

lemma dom_w (θ : ℝ) (j : Fin 4) : Dom (fun n => (wEven θ j n : ℂ)) := by
  fin_cases j
  · exact dom_re (dom_aEven (norm_s θ))
  · exact dom_im (dom_aEven (norm_s θ))
  · exact dom_re (dom_bEven (norm_s θ))
  · exact dom_im (dom_bEven (norm_s θ))

/-! ## The odd block in the real vectors `u, v` -/

lemma odd_forms {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ)
    (hOsym : ∀ n m, Oblock γ n m = Oblock γ m n) (θ : ℝ) :
    bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (conj (sθ θ))) =
        bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) +
          bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) ∧
      bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ)) =
        bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) -
          bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) +
            2 * I * bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) ∧
      bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ))) =
        bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) -
          bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) -
            2 * I * bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) := by
  have hg := gamma_summable hγ
  have hO := norm_Oblock_le γ
  have hswap := bilinf_swap_dom hg hO hOsym (dom_v θ) (dom_u θ)
  rw [aOdd_s_eq, aOdd_t_eq, bilinf_expand_dom hg hO I (-I) (dom_u θ) (dom_v θ) (dom_u θ) (dom_v θ),
    bilinf_expand_dom hg hO I I (dom_u θ) (dom_v θ) (dom_u θ) (dom_v θ),
    bilinf_expand_dom hg hO (-I) (-I) (dom_u θ) (dom_v θ) (dom_u θ) (dom_v θ), hswap]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ))) * Complex.I_sq
  · linear_combination (bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ))) * Complex.I_sq
  · linear_combination (bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ))) * Complex.I_sq

/-- `(a_e(s) - a_e(t))ᵀ E (a_e(s) + a_e(t)) = a_e(s)ᵀ E a_e(s) - a_e(t)ᵀ E a_e(t)` (`E` symmetric). -/
lemma even_U {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ)
    (hEsym : ∀ n m, Eblock γ n m = Eblock γ m n) (θ : ℝ) :
    bilinf (fun n => aEven (sθ θ) n - aEven (conj (sθ θ)) n) (Eblock γ)
        (fun n => aEven (sθ θ) n + aEven (conj (sθ θ)) n) =
      bilinf (aEven (sθ θ)) (Eblock γ) (aEven (sθ θ)) -
        bilinf (aEven (conj (sθ θ))) (Eblock γ) (aEven (conj (sθ θ))) := by
  have hg := gamma_summable hγ
  have ds := dom_aEven (norm_s θ)
  have dt := dom_aEven (norm_t θ)
  have e1 : (fun n => aEven (sθ θ) n - aEven (conj (sθ θ)) n) =
      fun n => aEven (sθ θ) n + (-1) * aEven (conj (sθ θ)) n := funext fun n => by ring
  have e2 : (fun n => aEven (sθ θ) n + aEven (conj (sθ θ)) n) =
      fun n => aEven (sθ θ) n + 1 * aEven (conj (sθ θ)) n := funext fun n => by ring
  rw [e1, e2, bilinf_expand_dom hg (norm_Eblock_le γ) (-1) 1 ds dt ds dt,
    bilinf_swap_dom hg (norm_Eblock_le γ) hEsym dt ds]
  ring

/-- `|xᵀ B y| ≤ ‖x‖²`-type bound for the vectors `a(s), a(t), a_e(s), a_e(t)` (all of norm `‖a(s)‖`). -/
lemma norm_bil_le {γ : ℕ → ℕ → ℂ} {B : ℕ → ℕ → ℂ} (v : ℂ → ℕ → ℂ)
    (hg : Summable fun p : ℕ × ℕ => ‖γ p.1 p.2‖ * rr ^ p.1 * rr ^ p.2)
    (hB : ∀ n m, ‖B n m‖ ≤ Real.sqrt n * Real.sqrt m * ‖γ n m‖)
    (hdom : ∀ z : ℂ, ‖z‖ = (Real.sqrt 2)⁻¹ → Dom (v z))
    (hsq : ∀ z : ℂ, ‖z‖ = (Real.sqrt 2)⁻¹ → Summable fun n => ‖v z n‖ ^ 2)
    (hconj : ∀ z n, ‖v (conj z) n‖ = ‖v z n‖)
    (hfin : ∀ (N : ℕ) (x y : ℕ → ℂ), ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * B n m * y m‖ ≤
      Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2))
    (θ : ℝ) (z1 z2 : ℂ) (h1 : z1 = sθ θ ∨ z1 = conj (sθ θ)) (h2 : z2 = sθ θ ∨ z2 = conj (sθ θ)) :
    ‖bilinf (v z1) B (v z2)‖ ≤ ∑' n, ‖v (sθ θ) n‖ ^ 2 := by
  have hn : ∀ z, (z = sθ θ ∨ z = conj (sθ θ)) → ‖z‖ = (Real.sqrt 2)⁻¹ := by
    rintro z (rfl | rfl)
    · exact norm_s θ
    · exact norm_t θ
  have ht : ∀ z, (z = sθ θ ∨ z = conj (sθ θ)) → ∑' n, ‖v z n‖ ^ 2 = ∑' n, ‖v (sθ θ) n‖ ^ 2 := by
    rintro z (rfl | rfl)
    · rfl
    · exact tsum_congr fun n => by rw [hconj]
  have hb := bilinf_norm_le (x := v z1) (y := v z2) (A := B) (summable_dom hg hB (hdom _ (hn _ h1)) (hdom _ (hn _ h2)))
    (hsq _ (hn _ h1)) (hsq _ (hn _ h2)) (fun N => hfin N _ _)
  rw [ht _ h1, ht _ h2, Real.mul_self_sqrt (tsum_nonneg fun _ => sq_nonneg _)] at hb
  exact hb

/-! ## Lemma 7.3, the `U` part -/

lemma U_part {f h : ℂ → ℂ} (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ)
    {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ Real.pi)
    (hOsym : ∀ n m, Oblock γ n m = Oblock γ m n) (hEsym : ∀ n m, Eblock γ n m = Eblock γ m n)
    (hfin : ∀ (N : ℕ) (x y : ℕ → ℂ),
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Oblock γ n m * y m‖ ≤
          Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) ∧
        ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
          Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2))
    (hA : bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ))
    (hB : bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ))
    (hC : bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ))
    (hOss : 2 * bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ)) =
      kser γ (sθ θ) (sθ θ) - kser γ (sθ θ) (-sθ θ))
    (hOtt : 2 * bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ))) =
      kser γ (conj (sθ θ)) (conj (sθ θ)) - kser γ (conj (sθ θ)) (-conj (sθ θ)))
    (hOst : exp (2 * bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (conj (sθ θ)))) =
      (h (sθ θ) - h (conj (sθ θ))) / (h (sθ θ) + h (conj (sθ θ))) *
        ((sθ θ + conj (sθ θ)) / (sθ θ - conj (sθ θ))))
    (hEss : 2 * bilinf (aEven (sθ θ)) (Eblock γ) (aEven (sθ θ)) =
      kser γ (sθ θ) (sθ θ) + kser γ (sθ θ) (-sθ θ))
    (hEtt : 2 * bilinf (aEven (conj (sθ θ))) (Eblock γ) (aEven (conj (sθ θ))) =
      kser γ (conj (sθ θ)) (conj (sθ θ)) + kser γ (conj (sθ θ)) (-conj (sθ θ))) :
    Ufun θ (O2 γ θ) = bilinf (fun n => aEven (sθ θ) n - aEven (conj (sθ θ)) n) (Eblock γ)
        (fun n => aEven (sθ θ) n + aEven (conj (sθ θ)) n) := by
  obtain ⟨hκ, hss, htt⟩ := odd_forms hγ hOsym θ
  have hg := gamma_summable hγ
  have hsm := s_mem θ
  have htm := t_mem θ
  have hs0' := s_ne_zero θ
  have ht0' := t_ne_zero θ
  -- `K_s = a_e(s)ᵀ E a_e(s) - a(s)ᵀ O a(s) = K_h(s, -s)`
  have hKs : bilinf (aEven (sθ θ)) (Eblock γ) (aEven (sθ θ)) - bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ)) =
      kser γ (sθ θ) (-sθ θ) := by linear_combination (hEss - hOss) / 2
  have hKt : bilinf (aEven (conj (sθ θ))) (Eblock γ) (aEven (conj (sθ θ))) -
      bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ))) =
      kser γ (conj (sθ θ)) (-conj (sθ θ)) := by linear_combination (hEtt - hOtt) / 2
  have hnsm : -sθ θ ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.mp hsm
  have hntm : -conj (sθ θ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.mp htm
  have hexpKs : exp (kser γ (sθ θ) (-sθ θ)) = sθ θ / h (sθ θ) := by
    rw [(hγ.2 _ _ hsm hnsm).2, kernelQuot_neg hs0' (hh.2.1 _ hsm)]
  have hexpKt : exp (kser γ (conj (sθ θ)) (-conj (sθ θ))) = conj (sθ θ) / h (conj (sθ θ)) := by
    rw [(hγ.2 _ _ htm hntm).2, kernelQuot_neg ht0' (hh.2.1 _ htm)]
  have hs0 : h (sθ θ) ≠ 0 := fun e => by
    rw [e, div_zero] at hexpKs; exact Complex.exp_ne_zero _ hexpKs
  have ht0 : h (conj (sθ θ)) ≠ 0 := fun e => by
    rw [e, div_zero] at hexpKt; exact Complex.exp_ne_zero _ hexpKt
  have hsum : h (sθ θ) + h (conj (sθ θ)) ≠ 0 := fun e => by
    rw [e, div_zero, zero_mul] at hOst; exact Complex.exp_ne_zero _ hOst
  -- `κ = a(s)ᵀ O a(t)` and `χ = (h(s) - h(t))/(h(s) + h(t))`
  have hkappa : kappa θ (O2 γ θ) = bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (conj (sθ θ))) := by
    rw [kappa, ← hA, ← hB, hκ]
  have hchi : chi θ (O2 γ θ) = (h (sθ θ) - h (conj (sθ θ))) / (h (sθ θ) + h (conj (sθ θ))) := by
    rw [chi, hkappa, hOst]
    calc I * (Real.tan (θ / 4) : ℂ) * ((h (sθ θ) - h (conj (sθ θ))) / (h (sθ θ) + h (conj (sθ θ))) *
          ((sθ θ + conj (sθ θ)) / (sθ θ - conj (sθ θ))))
        = (h (sθ θ) - h (conj (sθ θ))) / (h (sθ θ) + h (conj (sθ θ))) *
          (I * (Real.tan (θ / 4) : ℂ) * ((sθ θ + conj (sθ θ)) / (sθ θ - conj (sθ θ)))) := by ring
      _ = _ := by rw [tan_ratio h0 hπ, mul_one]
  -- the Grunsky bounds
  have hOfin := fun N x y => (hfin N x y).1
  have hEfin := fun N x y => (hfin N x y).2
  have bO := norm_bil_le aOdd hg (norm_Oblock_le γ) (fun z hz => dom_aOdd hz) (fun z hz => summable_sq_aOdd hz)
    (fun z _ => by rw [aOdd_conj, Complex.norm_conj]) hOfin θ
  have bE := norm_bil_le aEven hg (norm_Eblock_le γ) (fun z hz => dom_aEven hz)
    (fun z hz => summable_sq_aEven hz) (fun z n => by rw [aEven_conj, Complex.norm_conj]) hEfin θ
  have hsq := tsum_sq_add (norm_s θ)
  have hnnO : 0 ≤ ∑' n, ‖aOdd (sθ θ) n‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hnnE : 0 ≤ ∑' n, ‖aEven (sθ θ) n‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hχim : 0 < (chi θ (O2 γ θ)).im := by
    have hk : ‖kappa θ (O2 γ θ)‖ < Real.pi / 4 := by
      rw [hkappa]
      have := bO _ _ (Or.inl rfl) (Or.inr rfl)
      linarith [log_two_lt_quarter_pi]
    exact chi_im_pos_of h0 hπ hk
  have hKbound : ‖kser γ (sθ θ) (-sθ θ) - kser γ (conj (sθ θ)) (-conj (sθ θ))‖ < Real.pi := by
    rw [← hKs, ← hKt]
    have b1 := bE _ _ (Or.inl rfl) (Or.inl rfl)
    have b2 := bO _ _ (Or.inl rfl) (Or.inl rfl)
    have b3 := bE _ _ (Or.inr rfl) (Or.inr rfl)
    have b4 := bO _ _ (Or.inr rfl) (Or.inr rfl)
    have tri : ‖bilinf (aEven (sθ θ)) (Eblock γ) (aEven (sθ θ)) - bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ)) -
        (bilinf (aEven (conj (sθ θ))) (Eblock γ) (aEven (conj (sθ θ))) -
          bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ))))‖ ≤
        ‖bilinf (aEven (sθ θ)) (Eblock γ) (aEven (sθ θ))‖ + ‖bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ))‖ +
          (‖bilinf (aEven (conj (sθ θ))) (Eblock γ) (aEven (conj (sθ θ)))‖ +
            ‖bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ)))‖) :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
    have := Real.log_two_lt_d9
    have := Real.pi_gt_three
    linarith
  -- the exponentials agree
  have h1c : 1 + chi θ (O2 γ θ) = 2 * h (sθ θ) / (h (sθ θ) + h (conj (sθ θ))) := by
    rw [hchi, one_add_div hsum]; congr 1; ring
  have h2c : 1 - chi θ (O2 γ θ) = 2 * h (conj (sθ θ)) / (h (sθ θ) + h (conj (sθ θ))) := by
    rw [hchi, one_sub_div hsum]; congr 1; ring
  have h1ne : 1 + chi θ (O2 γ θ) ≠ 0 := by
    rw [h1c]; exact div_ne_zero (mul_ne_zero two_ne_zero hs0) hsum
  have h2ne : 1 - chi θ (O2 γ θ) ≠ 0 := by
    rw [h2c]; exact div_ne_zero (mul_ne_zero two_ne_zero ht0) hsum
  have hexp : exp (I * ((θ / 2 : ℝ) : ℂ) - log (1 + chi θ (O2 γ θ)) + log (1 - chi θ (O2 γ θ))) =
      exp (kser γ (sθ θ) (-sθ θ) - kser γ (conj (sθ θ)) (-conj (sθ θ))) := by
    rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log h1ne, Complex.exp_log h2ne, Complex.exp_sub,
      hexpKs, hexpKt, exp_half, h1c, h2c]
    field_simp
  have hΔ : Delta θ (O2 γ θ) = kser γ (sθ θ) (-sθ θ) - kser γ (conj (sθ θ)) (-conj (sθ θ)) :=
    delta_eq h0 hπ hχim hexp hKbound
  rw [Ufun, hΔ, even_U hγ hEsym θ, ← hC]
  linear_combination -hKs + hKt - hss + htt

/-! ## Lemma 7.3, the `R` part -/

lemma tsum_even {F : ℕ → ℂ} (hF : ∀ n, n % 2 = 1 → F n = 0) : ∑' n, F n = ∑' k, F (2 * k) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b e => by
    have e' : 2 * a = 2 * b := e
    omega
  refine (hinj.tsum_eq (f := F) ?_).symm
  intro n hn
  rw [Function.mem_support] at hn
  have h2 : n % 2 = 0 := by
    by_contra hc
    exact hn (hF n (by omega))
  exact ⟨n / 2, by show 2 * (n / 2) = n; omega⟩

lemma sqrt_two_mul (k : ℕ) : Real.sqrt ((2 * k : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt k := by
  push_cast; exact Real.sqrt_mul (by norm_num) _

lemma bEven_two_mul (s : ℂ) (k : ℕ) : bEven s (2 * k) = (Real.sqrt 2 : ℂ) * betaV (s ^ 2) k := by
  by_cases hk : k = 0
  · subst hk; simp [bEven, betaV]
  · unfold bEven betaV
    rw [if_pos ⟨by omega, by omega⟩, if_neg hk, sqrt_two_mul, pow_mul]
    push_cast; ring

lemma aEven_two_mul (t : ℂ) (j : ℕ) : aEven t (2 * j) = ((Real.sqrt 2 : ℂ))⁻¹ * alphaV (t ^ 2) j := by
  by_cases hj : j = 0
  · subst hj; simp [aEven, alphaV]
  · unfold aEven alphaV
    rw [if_pos ⟨by omega, by omega⟩, if_neg hj, sqrt_two_mul, pow_mul]
    push_cast; ring

/-- The even coordinates `2k`: `b_e(s)ᵀ A a_e(t) = β(s²)ᵀ (A_{2k,2j}) α(t²)`. -/
lemma bE_aE_reindex (A : ℕ → ℕ → ℂ) (s t : ℂ) :
    bilinf (bEven s) A (aEven t) =
      bilinf (betaV (s ^ 2)) (fun k j => A (2 * k) (2 * j)) (alphaV (t ^ 2)) := by
  have hsq : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  unfold bilinf
  rw [tsum_even (F := fun n => bEven s n * ∑' m, A n m * aEven t m) (fun n hn => by
    show bEven s n * _ = 0
    rw [show bEven s n = 0 by unfold bEven; rw [if_neg (by omega)], zero_mul])]
  refine tsum_congr fun k => ?_
  beta_reduce
  have hin : ∑' m, A (2 * k) m * aEven t m = ((Real.sqrt 2 : ℂ))⁻¹ * ∑' j, A (2 * k) (2 * j) * alphaV (t ^ 2) j := by
    rw [tsum_even (F := fun m => A (2 * k) m * aEven t m) (fun m hm => by
      show A (2 * k) m * aEven t m = 0
      rw [show aEven t m = 0 by unfold aEven; rw [if_neg (by omega)], mul_zero])]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [aEven_two_mul]; ring
  rw [hin, bEven_two_mul]
  field_simp

lemma R_part {f h : ℂ → ℂ} {γ γf : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff h γ) {θ : ℝ}
    (hOsym : ∀ n m, Oblock γ n m = Oblock γ m n)
    (hA : bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ))
    (hB : bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ))
    (hC : bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ))
    (hps : exp (2 * bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ))) = pfun f (sθ θ ^ 2))
    (hpt : exp (2 * bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ)))) =
      pfun f (conj (sθ θ) ^ 2))
    (hQ : Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ))
    (hBar : Q f (zθ θ) (conj (zθ θ)) - pfun f (zθ θ) - pfun f (conj (zθ θ)) =
      bilinf (betaV (zθ θ)) (Cmat γf) (alphaV (conj (zθ θ))) +
        bilinf (betaV (conj (zθ θ))) (Cmat γf) (alphaV (zθ θ)))
    (hKf : ∀ n m, Eblock γ (2 * n) (2 * m) = Cmat γf n m) :
    Rfun θ (O2 γ θ) = bilinf (bEven (sθ θ)) (Eblock γ) (aEven (conj (sθ θ))) +
      bilinf (bEven (conj (sθ θ))) (Eblock γ) (aEven (sθ θ)) := by
  obtain ⟨-, hss, htt⟩ := odd_forms hγ hOsym θ
  have hl1 : ell1 θ (O2 γ θ) = 2 * bilinf (aOdd (sθ θ)) (Oblock γ) (aOdd (sθ θ)) := by
    rw [ell1, hss, ← hA, ← hB, ← hC]; ring
  have hl2 : ell2 θ (O2 γ θ) = 2 * bilinf (aOdd (conj (sθ θ))) (Oblock γ) (aOdd (conj (sθ θ))) := by
    rw [ell2, htt, ← hA, ← hB, ← hC]; ring
  have hE' : (fun k j => Eblock γ (2 * k) (2 * j)) = Cmat γf := funext fun k => funext fun j => hKf k j
  rw [Rfun, hl1, hl2, hps, hpt, s_sq, t_sq, ← hQ, hBar, bE_aE_reindex, bE_aE_reindex, hE', s_sq, t_sq]

/-! ## (eq:UR): the real form -/

lemma UR_real {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ)
    (hEsym : ∀ n m, Eblock γ n m = Eblock γ m n) (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Ufun θ M = bilinf (fun n => aEven (sθ θ) n - aEven (conj (sθ θ)) n) (Eblock γ)
        (fun n => aEven (sθ θ) n + aEven (conj (sθ θ)) n))
    (hR : Rfun θ M = bilinf (bEven (sθ θ)) (Eblock γ) (aEven (conj (sθ θ))) +
        bilinf (bEven (conj (sθ θ))) (Eblock γ) (aEven (sθ θ))) :
    I * Ufun θ M = -4 * bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ)) ∧
      Rfun θ M = 2 * (bilinf (fun n => (wEven θ 2 n : ℂ)) (Eblock γ) (fun n => (wEven θ 0 n : ℂ)) +
        bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) := by
  obtain ⟨ha, hat, hb, hbt⟩ := w_fun θ
  have hg := gamma_summable hγ
  have hE := norm_Eblock_le γ
  constructor
  · have e1 : (fun n => aEven (sθ θ) n - aEven (conj (sθ θ)) n) = fun n => (2 * I) * (wEven θ 1 n : ℂ) :=
      funext fun n => by simp only [ha, hat]; ring
    have e2 : (fun n => aEven (sθ θ) n + aEven (conj (sθ θ)) n) = fun n => 2 * (wEven θ 0 n : ℂ) :=
      funext fun n => by simp only [ha, hat]; ring
    rw [hU, e1, e2, bilinf_smul, bilinf_swap_dom hg hE hEsym (dom_w θ 1) (dom_w θ 0)]
    linear_combination (4 * bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) *
      Complex.I_sq
  · rw [hR, hb, hat, hbt, ha, bilinf_expand_dom hg hE I (-I) (dom_w θ 2) (dom_w θ 3) (dom_w θ 0) (dom_w θ 1),
      bilinf_expand_dom hg hE (-I) I (dom_w θ 2) (dom_w θ 3) (dom_w θ 0) (dom_w θ 1)]
    linear_combination (-2 * bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) *
      Complex.I_sq

/-! ## Lemma 7.4: finite sections and the limit -/

/-- The finite section `(E_{nm})_{n, m < N}`. -/
noncomputable def Esec (γ : ℕ → ℕ → ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => Eblock γ i j

/-- The first `N` rows of `𝒲 = (u_e, v_e, β₀, β₁)`. -/
noncomputable def Wsec (θ : ℝ) (N : ℕ) : Matrix (Fin N) (Fin 4) ℝ := Matrix.of fun i j => wEven θ j i

lemma fin_sum_sum (N : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ i : Fin N, ∑ l : Fin N, g i l = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, g n m := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ m ∈ Finset.range N, g n m) N]
  exact Finset.sum_congr rfl fun i _ => (Fin.sum_univ_eq_sum_range (fun m => g i m) N)

lemma trace_E_aux {N : ℕ} (E : Matrix (Fin N) (Fin N) ℂ) (W : Matrix (Fin N) (Fin 4) ℝ)
    (J : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.trace (E * (W * J * Wᵀ).map (↑)) =
      ∑ k : Fin 4, ∑ j : Fin 4, (∑ i : Fin N, ∑ l : Fin N, (W i k : ℂ) * E i l * (W l j : ℂ)) * (J j k : ℂ) := by
  have lhs : Matrix.trace (E * (W * J * Wᵀ).map (↑)) =
      ∑ i : Fin N, ∑ l : Fin N, ∑ k : Fin 4, ∑ j : Fin 4, (W i k : ℂ) * E i l * (W l j : ℂ) * (J j k : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [lhs]
  simp only [Finset.sum_mul]
  calc _ = ∑ i : Fin N, ∑ k : Fin 4, ∑ l : Fin N, ∑ j : Fin 4,
        (W i k : ℂ) * E i l * (W l j : ℂ) * (J j k : ℂ) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k : Fin 4, ∑ i : Fin N, ∑ l : Fin N, ∑ j : Fin 4,
        (W i k : ℂ) * E i l * (W l j : ℂ) * (J j k : ℂ) := Finset.sum_comm
    _ = ∑ k : Fin 4, ∑ i : Fin N, ∑ j : Fin 4, ∑ l : Fin N,
        (W i k : ℂ) * E i l * (W l j : ℂ) * (J j k : ℂ) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k : Fin 4, ∑ j : Fin 4, ∑ i : Fin N, ∑ l : Fin N,
        (W i k : ℂ) * E i l * (W l j : ℂ) * (J j k : ℂ) := Finset.sum_congr rfl fun k _ => Finset.sum_comm

lemma trace_E (γ : ℕ → ℕ → ℂ) (θ : ℝ) (N : ℕ) (J : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.trace (Esec γ N * (Wsec θ N * J * (Wsec θ N)ᵀ).map (↑)) =
      ∑ k : Fin 4, ∑ j : Fin 4, (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        (wEven θ k n : ℂ) * Eblock γ n m * (wEven θ j m : ℂ)) * (J j k : ℂ) := by
  rw [trace_E_aux]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact fin_sum_sum N (fun n m => (wEven θ k n : ℂ) * Eblock γ n m * (wEven θ j m : ℂ))

lemma trace_G (θ : ℝ) (N : ℕ) (K : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.trace ((Wsec θ N)ᵀ * Wsec θ N * K) =
      ∑ j : Fin 4, ∑ k : Fin 4, (∑ n ∈ Finset.range N, wEven θ j n * wEven θ k n) * K k j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Wsec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun n => wEven θ j n * wEven θ k n) N

lemma trace_GK (G K : Matrix (Fin 4) (Fin 4) ℝ) : Matrix.trace (G * K) = ∑ j, ∑ k, G j k * K k j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- The finite sections of `E` satisfy the hypothesis of `sec7_trace_bound`. -/
lemma hE_sec {γ : ℕ → ℕ → ℂ}
    (hEfin : ∀ (N : ℕ) (x y : ℕ → ℂ), ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
      Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2)) (N : ℕ) :
    ∀ x y : Fin N → ℝ, ‖(fun i => (y i : ℂ)) ⬝ᵥ (Esec γ N *ᵥ (fun i => (x i : ℂ)))‖ ≤
      Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
  intro x y
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℂ, ∀ i : Fin N, X i = (x i : ℂ) :=
    ⟨fun n => if h : n < N then (x ⟨n, h⟩ : ℂ) else 0, fun i => by simp [i.isLt]⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℂ, ∀ i : Fin N, Y i = (y i : ℂ) :=
    ⟨fun n => if h : n < N then (y ⟨n, h⟩ : ℂ) else 0, fun i => by simp [i.isLt]⟩
  have e1 : (fun i => (y i : ℂ)) ⬝ᵥ (Esec γ N *ᵥ (fun i => (x i : ℂ))) =
      ∑ i : Fin N, ∑ l : Fin N, Y i * Eblock γ i l * X l := by
    simp only [dotProduct, Matrix.mulVec, Esec, Matrix.of_apply, Finset.mul_sum, hX, hY]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have e1' := fin_sum_sum N (fun n m => Y n * Eblock γ n m * X m)
  beta_reduce at e1'
  have e2 := Fin.sum_univ_eq_sum_range (fun n => ‖Y n‖ ^ 2) N
  have e3 := Fin.sum_univ_eq_sum_range (fun n => ‖X n‖ ^ 2) N
  beta_reduce at e2 e3
  have e2' : ∑ n ∈ Finset.range N, ‖Y n‖ ^ 2 = ∑ i, y i ^ 2 := by
    rw [← e2]
    exact Finset.sum_congr rfl fun i _ => by rw [hY, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e3' : ∑ n ∈ Finset.range N, ‖X n‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [← e3]
    exact Finset.sum_congr rfl fun i _ => by rw [hX, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e1, e1']
  refine (hEfin N Y X).trans (le_of_eq ?_)
  rw [e2', e3', mul_comm]

lemma J_sum (B : Fin 4 → Fin 4 → ℂ) (lam mu : ℝ) :
    ∑ k : Fin 4, ∑ j : Fin 4, B k j * (Jmat lam mu j k : ℂ) =
      -2 * (lam : ℂ) * (B 1 0 + B 0 1) - (mu : ℂ) * (B 2 0 + B 0 2 + B 3 1 + B 1 3) := by
  simp [Fin.sum_univ_four, Jmat, J1, J2]
  ring

lemma lem74_core {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ)
    (hEsym : ∀ n m, Eblock γ n m = Eblock γ m n)
    (hEfin : ∀ (N : ℕ) (x y : ℕ → ℂ), ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
      Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2))
    (θ : ℝ) (hgram : ∀ i j : Fin 4, HasSum (fun n => wEven θ i n * wEven θ j n) (Gram θ i j))
    (lam mu : ℝ) (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : P.PosDef) :
    ‖(lam : ℂ) * (-4 * bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) -
        (mu : ℂ) * (2 * (bilinf (fun n => (wEven θ 2 n : ℂ)) (Eblock γ) (fun n => (wEven θ 0 n : ℂ)) +
          bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))))‖ ≤ CP θ lam mu P := by
  have hg := gamma_summable hγ
  have hE := norm_Eblock_le γ
  have hT : Tendsto (fun N => Matrix.trace (Esec γ N * (Wsec θ N * Jmat lam mu * (Wsec θ N)ᵀ).map (↑)))
      atTop (𝓝 (∑ k : Fin 4, ∑ j : Fin 4, bilinf (fun n => (wEven θ k n : ℂ)) (Eblock γ)
        (fun n => (wEven θ j n : ℂ)) * (Jmat lam mu j k : ℂ))) := by
    refine (tendsto_congr fun N => trace_E γ θ N (Jmat lam mu)).mpr ?_
    exact tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun j _ =>
      (tendsto_square_dom hg hE (dom_w θ k) (dom_w θ j)).mul_const _
  have hG : Tendsto (fun N => Matrix.trace ((Wsec θ N)ᵀ * Wsec θ N * Kmat lam mu P)) atTop
      (𝓝 (Matrix.trace (Gram θ * Kmat lam mu P))) := by
    refine (tendsto_congr fun N => trace_G θ N (Kmat lam mu P)).mpr ?_
    rw [trace_GK]
    exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ =>
      ((hgram j k).tendsto_sum_nat).mul_const _
  have hlim := le_of_tendsto_of_tendsto' hT.norm hG
    (fun N => sec7_trace_bound_proved N (Esec γ N) (hE_sec hEfin N) (Wsec θ N) lam mu P hP)
  rw [J_sum] at hlim
  rw [bilinf_swap_dom hg hE hEsym (dom_w θ 1) (dom_w θ 0), bilinf_swap_dom hg hE hEsym (dom_w θ 0) (dom_w θ 2),
    bilinf_swap_dom hg hE hEsym (dom_w θ 1) (dom_w θ 3)] at hlim
  unfold CP
  have e : (lam : ℂ) * (-4 * bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) -
      (mu : ℂ) * (2 * (bilinf (fun n => (wEven θ 2 n : ℂ)) (Eblock γ) (fun n => (wEven θ 0 n : ℂ)) +
        bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ)))) =
      -2 * (lam : ℂ) * (bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ)) +
        bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) -
      (mu : ℂ) * (bilinf (fun n => (wEven θ 2 n : ℂ)) (Eblock γ) (fun n => (wEven θ 0 n : ℂ)) +
        bilinf (fun n => (wEven θ 2 n : ℂ)) (Eblock γ) (fun n => (wEven θ 0 n : ℂ)) +
        bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ)) +
        bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) := by ring
  rw [e]
  exact hlim

end Sec7G

open Sec7G

/-! ## The four rows -/

set_option linter.unusedVariables false in
/-- Lemma 7.3, conditional on the rows lem_3_1_i, lem_3_1_ii, lem_3_1_iii, sec3_OE_contractions,
sec5_O2_entries, sec3_grunsky_exists, eq_Kf, lem_6_3, prop_5_1 (in this order). -/
theorem lem_7_3_proved_from
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    (h31ii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ)
      (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1)
      (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aEven s) (Eblock γ) (aEven t) = kser γ s t + kser γ s (-t) ∧
        kser γ s t + kser γ s (-t) = kser γf (s ^ 2) (t ^ 2))
    (h31iii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
        2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
        ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2))
    (hOE : ∀ (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
      (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      (∀ n m : ℕ, Oblock γ n m = Oblock γ m n) ∧ (∀ n m : ℕ, Eblock γ n m = Eblock γ m n) ∧
        (∀ n m : ℕ, Cmat γ n m = Oblock γ n m + Eblock γ n m) ∧
        ∀ (N : ℕ) (x y : ℕ → ℂ),
          ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Oblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) ∧
            ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2))
    (hO2e : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi),
      bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ) ∧
        bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ) ∧
        bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ))
    (hgex : ∀ (hB : FactBidiscPowerSeries) (g : ℂ → ℂ) (hg : InS g),
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (hKf : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (hγf : IsGrunskyCoeff f γf),
      (∀ n m : ℕ, Eblock γ (2 * n) (2 * m) = Cmat γf n m) ∧
        ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
          kser γf z w = bilinf (alphaV z) (Cmat γf) (alphaV w))
    (h63 : ∀ (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
      (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hzw : z ≠ w),
      Q f z w - pfun f z - pfun f w =
        bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z))
    (h51 : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi), Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ))
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    Ufun θ (O2 γ θ) = bilinf (fun n => aEven (sθ θ) n - aEven (conj (sθ θ)) n) (Eblock γ)
        (fun n => aEven (sθ θ) n + aEven (conj (sθ θ)) n) ∧
      Rfun θ (O2 γ θ) = bilinf (bEven (sθ θ)) (Eblock γ) (aEven (conj (sθ θ))) +
        bilinf (bEven (conj (sθ θ))) (Eblock γ) (aEven (sθ θ)) := by
  obtain ⟨γf, hγf, -⟩ := hgex hB f hf
  obtain ⟨hOsym, hEsym, -, hfin⟩ := hOE hG f h hf hh γ hγ
  obtain ⟨hA, hBB, hC⟩ := hO2e f h hf hh γ hγ θ h0 hπ
  have hs := s_mem θ
  have ht := t_mem θ
  refine ⟨U_part hh hγ h0 hπ hOsym hEsym hfin hA hBB hC (h31i f h hf hh γ hγ _ _ hs hs).1
    (h31i f h hf hh γ hγ _ _ ht ht).1 ((h31i f h hf hh γ hγ _ _ hs ht).2 (s_ne_t h0 hπ) (s_ne_neg_t h0 hπ))
    (h31ii f h hf hh γ γf hγ hγf _ _ hs hs).1 (h31ii f h hf hh γ γf hγ hγf _ _ ht ht).1, ?_⟩
  exact R_part hγ hOsym hA hBB hC ((h31iii f h hf hh γ hγ).2.2 _ hs) ((h31iii f h hf hh γ hγ).2.2 _ ht)
    (h51 f h hf hh γ hγ θ h0 hπ) (h63 f hf γf hγf _ _ (z_mem θ) (w_mem θ) (z_ne_w h0 hπ))
    (hKf f h hf hh γ γf hγ hγf).1


set_option linter.unusedVariables false in
/-- (eq:UR), conditional on the same rows as `lem_7_3_proved_from`. -/
theorem eq_UR_proved_from
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    (h31ii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ)
      (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1)
      (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aEven s) (Eblock γ) (aEven t) = kser γ s t + kser γ s (-t) ∧
        kser γ s t + kser γ s (-t) = kser γf (s ^ 2) (t ^ 2))
    (h31iii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
        2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
        ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2))
    (hOE : ∀ (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
      (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      (∀ n m : ℕ, Oblock γ n m = Oblock γ m n) ∧ (∀ n m : ℕ, Eblock γ n m = Eblock γ m n) ∧
        (∀ n m : ℕ, Cmat γ n m = Oblock γ n m + Eblock γ n m) ∧
        ∀ (N : ℕ) (x y : ℕ → ℂ),
          ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Oblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) ∧
            ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2))
    (hO2e : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi),
      bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ) ∧
        bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ) ∧
        bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ))
    (hgex : ∀ (hB : FactBidiscPowerSeries) (g : ℂ → ℂ) (hg : InS g),
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (hKf : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (hγf : IsGrunskyCoeff f γf),
      (∀ n m : ℕ, Eblock γ (2 * n) (2 * m) = Cmat γf n m) ∧
        ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
          kser γf z w = bilinf (alphaV z) (Cmat γf) (alphaV w))
    (h63 : ∀ (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
      (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hzw : z ≠ w),
      Q f z w - pfun f z - pfun f w =
        bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z))
    (h51 : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi), Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ))
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    I * Ufun θ (O2 γ θ) =
        -4 * bilinf (fun n => (wEven θ 0 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ)) ∧
      Rfun θ (O2 γ θ) = 2 * (bilinf (fun n => (wEven θ 2 n : ℂ)) (Eblock γ) (fun n => (wEven θ 0 n : ℂ)) +
        bilinf (fun n => (wEven θ 3 n : ℂ)) (Eblock γ) (fun n => (wEven θ 1 n : ℂ))) := by
  obtain ⟨hU, hR⟩ := lem_7_3_proved_from h31i h31ii h31iii hOE hO2e hgex hKf h63 h51 hB hG f h hf hh γ hγ θ h0 hπ
  obtain ⟨-, hEsym, -, -⟩ := hOE hG f h hf hh γ hγ
  exact UR_real hγ hEsym θ (O2 γ θ) hU hR

set_option linter.unusedVariables false in
/-- Lemma 7.4, conditional on the rows of `lem_7_3_proved_from` and sec7_gram (last). -/
theorem lem_7_4_proved_from
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    (h31ii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ)
      (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1)
      (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aEven s) (Eblock γ) (aEven t) = kser γ s t + kser γ s (-t) ∧
        kser γ s t + kser γ s (-t) = kser γf (s ^ 2) (t ^ 2))
    (h31iii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
        2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
        ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2))
    (hOE : ∀ (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
      (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      (∀ n m : ℕ, Oblock γ n m = Oblock γ m n) ∧ (∀ n m : ℕ, Eblock γ n m = Eblock γ m n) ∧
        (∀ n m : ℕ, Cmat γ n m = Oblock γ n m + Eblock γ n m) ∧
        ∀ (N : ℕ) (x y : ℕ → ℂ),
          ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Oblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) ∧
            ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2))
    (hO2e : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi),
      bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ) ∧
        bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ) ∧
        bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ))
    (hgex : ∀ (hB : FactBidiscPowerSeries) (g : ℂ → ℂ) (hg : InS g),
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (hKf : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (hγf : IsGrunskyCoeff f γf),
      (∀ n m : ℕ, Eblock γ (2 * n) (2 * m) = Cmat γf n m) ∧
        ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
          kser γf z w = bilinf (alphaV z) (Cmat γf) (alphaV w))
    (h63 : ∀ (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
      (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hzw : z ≠ w),
      Q f z w - pfun f z - pfun f w =
        bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z))
    (h51 : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi), Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ))
    (hgram : ∀ (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi),
      ∀ i j : Fin 4, HasSum (fun n => wEven θ i n * wEven θ j n) (Gram θ i j))
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) (lam mu : ℝ)
    (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : P.PosDef) :
    ‖(lam : ℂ) * (I * Ufun θ (O2 γ θ)) - (mu : ℂ) * Rfun θ (O2 γ θ)‖ ≤ CP θ lam mu P := by
  obtain ⟨hIU, hR⟩ := eq_UR_proved_from h31i h31ii h31iii hOE hO2e hgex hKf h63 h51 hB hG f h hf hh γ hγ θ h0 hπ
  obtain ⟨-, hEsym, -, hfin⟩ := hOE hG f h hf hh γ hγ
  rw [hIU, hR]
  exact lem74_core hγ hEsym (fun N x y => (hfin N x y).2) θ (hgram θ h0 hπ) lam mu P hP

set_option linter.unusedVariables false in
/-- Proposition 7.5(ii), conditional on the rows of `lem_7_4_proved_from`. -/
theorem prop_7_5_ii_proved_from
    (h31i : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1) (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aOdd s) (Oblock γ) (aOdd t) = kser γ s t - kser γ s (-t) ∧
        (s ≠ t → s ≠ -t →
          exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd t)) = (h s - h t) / (h s + h t) * ((s + t) / (s - t))))
    (h31ii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ)
      (hγ : IsGrunskyCoeff h γ) (hγf : IsGrunskyCoeff f γf) (s t : ℂ) (hs : s ∈ ball (0 : ℂ) 1)
      (ht : t ∈ ball (0 : ℂ) 1),
      2 * bilinf (aEven s) (Eblock γ) (aEven t) = kser γ s t + kser γ s (-t) ∧
        kser γ s t + kser γ s (-t) = kser γf (s ^ 2) (t ^ 2))
    (h31iii : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      ContinuousOn (fun s => 2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) (ball (0 : ℂ) 1) ∧
        2 * bilinf (aOdd 0) (Oblock γ) (aOdd 0) = 0 ∧
        ∀ s ∈ ball (0 : ℂ) 1, exp (2 * bilinf (aOdd s) (Oblock γ) (aOdd s)) = pfun f (s ^ 2))
    (hOE : ∀ (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
      (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ),
      (∀ n m : ℕ, Oblock γ n m = Oblock γ m n) ∧ (∀ n m : ℕ, Eblock γ n m = Eblock γ m n) ∧
        (∀ n m : ℕ, Cmat γ n m = Oblock γ n m + Eblock γ n m) ∧
        ∀ (N : ℕ) (x y : ℕ → ℂ),
          ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Oblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) ∧
            ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
              Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2))
    (hO2e : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi),
      bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (uvec θ n : ℂ)) = cA θ (O2 γ θ) ∧
        bilinf (fun n => (vvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cB θ (O2 γ θ) ∧
        bilinf (fun n => (uvec θ n : ℂ)) (Oblock γ) (fun n => (vvec θ n : ℂ)) = cC θ (O2 γ θ))
    (hgex : ∀ (hB : FactBidiscPowerSeries) (g : ℂ → ℂ) (hg : InS g),
      ∃ γ : ℕ → ℕ → ℂ, IsGrunskyCoeff g γ ∧ ∀ n m : ℕ, γ n m = γ m n)
    (hKf : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ γf : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (hγf : IsGrunskyCoeff f γf),
      (∀ n m : ℕ, Eblock γ (2 * n) (2 * m) = Cmat γf n m) ∧
        ∀ z w : ℂ, z ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 →
          kser γf z w = bilinf (alphaV z) (Cmat γf) (alphaV w))
    (h63 : ∀ (f : ℂ → ℂ) (hf : InS f) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff f γ) (z w : ℂ)
      (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hzw : z ≠ w),
      Q f z w - pfun f z - pfun f w =
        bilinf (betaV z) (Cmat γ) (alphaV w) + bilinf (betaV w) (Cmat γ) (alphaV z))
    (h51 : ∀ (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h) (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ)
      (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi), Q f (zθ θ) (conj (zθ θ)) = Qrel θ (O2 γ θ))
    (hgram : ∀ (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi),
      ∀ i j : Fin 4, HasSum (fun n => wEven θ i n * wEven θ j n) (Gram θ i j))
    (hB : FactBidiscPowerSeries) (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    (Ffun θ (O2 γ θ)).re ≤ (Q f (zθ θ) (conj (zθ θ))).re := by
  have h74 := lem_7_4_proved_from h31i h31ii h31iii hOE hO2e hgex hKf h63 h51 hgram hB hG f h hf hh γ hγ θ h0 hπ (4 / 5) (1 / 2) Pmat
    Pmat_posDef
  have hQ := h51 f h hf hh γ hγ θ h0 hπ
  set X := ((4 / 5 : ℝ) : ℂ) * (I * Ufun θ (O2 γ θ)) - ((1 / 2 : ℝ) : ℂ) * Rfun θ (O2 γ θ) with hX
  have e : Ffun θ (O2 γ θ) = Qrel θ (O2 γ θ) + X - (CP θ (4 / 5) (1 / 2) Pmat : ℂ) := by
    rw [hX, Ffun]; push_cast; ring
  rw [e, Complex.sub_re, Complex.add_re, Complex.ofReal_re, hQ]
  linarith [Complex.re_le_norm X]

end Robinson.Proofs
