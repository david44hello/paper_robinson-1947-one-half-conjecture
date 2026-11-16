/-
Robinson/Proofs/Sec6Bounds.lean — proofs of sec6_xi_ball, sec6_psum_cos, sec6_b_change,
sec6_Wbound_finite, sec6_expW_bound, sec6_logcos.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Matrix2
import Robinson.Defs.Far

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## The ball bound for `ξ₁, ξ₂` -/

/-- A column of a matrix of operator norm at most `1` has Euclidean norm at most `1`. -/
private lemma col_sq_le (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : opNorm M ≤ 1) (j : Fin 2) :
    ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 ≤ 1 := by
  set T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M with hT
  have h1 : ‖T (WithLp.toLp 2 (Pi.single j (1 : ℂ)))‖ ≤ 1 := by
    calc _ ≤ ‖T‖ * ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin 2))‖ := T.le_opNorm _
      _ ≤ 1 := by
        have hT1 : ‖T‖ ≤ 1 := hM
        simpa using hT1
  have h2 : ‖T (WithLp.toLp 2 (Pi.single j (1 : ℂ)))‖ ^ 2 = ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [T, Matrix.mulVec_single, Fin.sum_univ_two]
  nlinarith [norm_nonneg (T (WithLp.toLp 2 (Pi.single j (1 : ℂ))))]

theorem sec6_xi_ball_proved (σp σm : ℝ) (hp : 0 ≤ σp) (hm : 0 ≤ σm) (hpos : 0 < σp + σm)
    (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : InBall N) :
    ‖2 * ((σp : ℂ) * N 0 0 - (σm : ℂ) * N 1 1) / (2 * ((σp + σm : ℝ) : ℂ))‖ ^ 2 + ‖N 0 1‖ ^ 2 ≤ 1 := by
  have hsym : N 1 0 = N 0 1 := by
    have := congrFun (congrFun hN.1 0) 1
    simpa [Matrix.transpose_apply] using this
  have c0 := col_sq_le N hN.2 0
  have c1 := col_sq_le N hN.2 1
  rw [hsym] at c0
  set x := ‖N 0 0‖
  set y := ‖N 1 1‖
  set z := ‖N 0 1‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hD : (2 * ((σp + σm : ℝ) : ℂ)) ≠ 0 := by
    have : ((σp + σm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    exact mul_ne_zero two_ne_zero this
  have hnorm : ‖2 * ((σp : ℂ) * N 0 0 - (σm : ℂ) * N 1 1) / (2 * ((σp + σm : ℝ) : ℂ))‖ ≤
      (σp * x + σm * y) / (σp + σm) := by
    rw [norm_div]
    have hden : ‖2 * ((σp + σm : ℝ) : ℂ)‖ = 2 * (σp + σm) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]; simp
    rw [hden]
    have hnum : ‖2 * ((σp : ℂ) * N 0 0 - (σm : ℂ) * N 1 1)‖ ≤ 2 * (σp * x + σm * y) := by
      rw [norm_mul]
      have : ‖(σp : ℂ) * N 0 0 - (σm : ℂ) * N 1 1‖ ≤ σp * x + σm * y := by
        calc _ ≤ ‖(σp : ℂ) * N 0 0‖ + ‖(σm : ℂ) * N 1 1‖ := norm_sub_le _ _
          _ = σp * x + σm * y := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hm]
      simpa using mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
    calc _ ≤ 2 * (σp * x + σm * y) / (2 * (σp + σm)) := by gcongr
      _ = (σp * x + σm * y) / (σp + σm) := by field_simp
  have hq : 0 ≤ (σp * x + σm * y) / (σp + σm) := by positivity
  have key : ((σp * x + σm * y) / (σp + σm)) ^ 2 ≤ 1 - z ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ σp * σm * (x - y) ^ 2 := mul_nonneg (mul_nonneg hp hm) (sq_nonneg (x - y))
    have h2 : 0 ≤ (σp + σm) * (σp * (1 - z ^ 2 - x ^ 2) + σm * (1 - z ^ 2 - y ^ 2)) :=
      mul_nonneg hpos.le (add_nonneg (mul_nonneg hp (by linarith)) (mul_nonneg hm (by linarith)))
    nlinarith [h1, h2]
  have := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  linarith

/-! ## Half the sum of the two exponentials -/

theorem sec6_psum_cos_proved (φ : ℝ) (X Y : ℂ) :
    (exp (exp ((φ : ℂ) * I) * (X + I * Y)) + exp (exp (-((φ : ℂ) * I)) * (X - I * Y))) / 2 =
      exp ((Real.cos φ : ℂ) * X - (Real.sin φ : ℂ) * Y) * Complex.cos ((Real.sin φ : ℂ) * X + (Real.cos φ : ℂ) * Y) := by
  have e1 : exp ((φ : ℂ) * I) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * I := by
    rw [exp_mul_I, ofReal_cos, ofReal_sin]
  have e2 : exp (-((φ : ℂ) * I)) = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * I := by
    have : -((φ : ℂ) * I) = ((-φ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  set c : ℂ := (Real.cos φ : ℂ)
  set s : ℂ := (Real.sin φ : ℂ)
  have a1 : (c + s * I) * (X + I * Y) = (c * X - s * Y) + (s * X + c * Y) * I := by
    ring_nf; rw [I_sq]; ring
  have a2 : (c - s * I) * (X - I * Y) = (c * X - s * Y) + -(s * X + c * Y) * I := by
    ring_nf; rw [I_sq]; ring
  rw [e1, e2, a1, a2, exp_add, exp_add, Complex.cos]
  ring

/-! ## The real orthogonal change of variables -/

/-- A real rotation-reflection `(ξ₁, ξ₂) ↦ (αξ₁ + βξ₂, βξ₁ - αξ₂)` with `α² + β² = 1` preserves `|ξ₁|² + |ξ₂|²`. -/
private lemma orth_norm (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) (ξ₁ ξ₂ : ℂ) :
    ‖(α : ℂ) * ξ₁ + (β : ℂ) * ξ₂‖ ^ 2 + ‖(β : ℂ) * ξ₁ - (α : ℂ) * ξ₂‖ ^ 2 = ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  linear_combination (ξ₁.re ^ 2 + ξ₁.im ^ 2 + ξ₂.re ^ 2 + ξ₂.im ^ 2) * h

/-- The change of `sec6_b_change` with `ζ₁ = (L sin φ / B) ξ₁ + (d cos φ / B) ξ₂`,
`ζ₂ = (d cos φ / B) ξ₁ - (L sin φ / B) ξ₂`, where `B = √(L² sin²φ + d² cos²φ)`. -/
private lemma b_change_aux (L d φ : ℝ) (hL : 0 < L) (hd : 0 < d) (ξ₁ ξ₂ : ℂ) (B : ℝ)
    (hBdef : B = Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2)) :
    ‖((L * Real.sin φ / B : ℝ) : ℂ) * ξ₁ + ((d * Real.cos φ / B : ℝ) : ℂ) * ξ₂‖ ^ 2 +
        ‖((d * Real.cos φ / B : ℝ) : ℂ) * ξ₁ - ((L * Real.sin φ / B : ℝ) : ℂ) * ξ₂‖ ^ 2 = ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 ∧
      (L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂ =
        (B : ℂ) * (((L * Real.sin φ / B : ℝ) : ℂ) * ξ₁ + ((d * Real.cos φ / B : ℝ) : ℂ) * ξ₂) ∧
      (L * Real.cos φ : ℂ) * ξ₁ - (d * Real.sin φ : ℂ) * ξ₂ =
        (((L ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / B : ℝ) : ℂ) *
            (((L * Real.sin φ / B : ℝ) : ℂ) * ξ₁ + ((d * Real.cos φ / B : ℝ) : ℂ) * ξ₂) +
          ((L * d / B : ℝ) : ℂ) * (((d * Real.cos φ / B : ℝ) : ℂ) * ξ₁ - ((L * Real.sin φ / B : ℝ) : ℂ) * ξ₂) := by
  have hsc : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have hB2pos : 0 < L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2 := by
    rcases eq_or_ne (Real.sin φ) 0 with h0 | h0
    · have : Real.cos φ ^ 2 = 1 := by rw [h0] at hsc; linarith
      rw [h0, this]; positivity
    · have : 0 < Real.sin φ ^ 2 := by positivity
      positivity
  have hB : 0 < B := by rw [hBdef]; exact Real.sqrt_pos.mpr hB2pos
  have hBB : B ^ 2 = L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2 := by rw [hBdef]; exact Real.sq_sqrt hB2pos.le
  clear hBdef
  generalize Real.sin φ = s at hsc hBB ⊢
  generalize Real.cos φ = c at hsc hBB ⊢
  have hB0 : B ≠ 0 := hB.ne'
  have hαβ : (L * s / B) ^ 2 + (d * c / B) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity), hBB]
    ring
  refine ⟨orth_norm _ _ hαβ ξ₁ ξ₂, ?_, ?_⟩
  · have hα : (B : ℂ) * ((L * s / B : ℝ) : ℂ) = (L : ℂ) * (s : ℂ) := by
      rw [← ofReal_mul, ← ofReal_mul, mul_div_cancel₀ _ hB0]
    have hβ : (B : ℂ) * ((d * c / B : ℝ) : ℂ) = (d : ℂ) * (c : ℂ) := by
      rw [← ofReal_mul, ← ofReal_mul, mul_div_cancel₀ _ hB0]
    linear_combination (-ξ₁) * hα - ξ₂ * hβ
  · have r1 : (L ^ 2 - d ^ 2) * s * c / B * (L * s / B) + L * d / B * (d * c / B) = L * c := by
      rw [div_mul_div_comm, div_mul_div_comm, ← add_div, div_eq_iff (by positivity)]
      linear_combination (-(L * c * d ^ 2)) * hsc - (L * c) * hBB
    have r2 : (L ^ 2 - d ^ 2) * s * c / B * (d * c / B) - L * d / B * (L * s / B) = -(d * s) := by
      rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, div_eq_iff (by positivity)]
      linear_combination (d * s * L ^ 2) * hsc + (d * s) * hBB
    have r1c : (((L ^ 2 - d ^ 2) * s * c / B : ℝ) : ℂ) * ((L * s / B : ℝ) : ℂ) +
        ((L * d / B : ℝ) : ℂ) * ((d * c / B : ℝ) : ℂ) = (L : ℂ) * c := by exact_mod_cast r1
    have r2c : (((L ^ 2 - d ^ 2) * s * c / B : ℝ) : ℂ) * ((d * c / B : ℝ) : ℂ) -
        ((L * d / B : ℝ) : ℂ) * ((L * s / B : ℝ) : ℂ) = -((d : ℂ) * s) := by exact_mod_cast r2
    linear_combination (-ξ₁) * r1c - ξ₂ * r2c

theorem sec6_b_change_proved (L d φ : ℝ) (hL : 0 < L) (hd : 0 < d) (ξ₁ ξ₂ : ℂ) :
    let b₁ : ℝ := Real.sqrt (L ^ 2 * Real.sin φ ^ 2 + d ^ 2 * Real.cos φ ^ 2)
    let ζ₁ : ℂ := ((L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂) / b₁
    let ζ₂ : ℂ := ((d * Real.cos φ : ℂ) * ξ₁ - (L * Real.sin φ : ℂ) * ξ₂) / b₁
    ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 = ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 ∧
      (L * Real.sin φ : ℂ) * ξ₁ + (d * Real.cos φ : ℂ) * ξ₂ = (b₁ : ℂ) * ζ₁ ∧
      (L * Real.cos φ : ℂ) * ξ₁ - (d * Real.sin φ : ℂ) * ξ₂ =
        (((L ^ 2 - d ^ 2) * Real.sin φ * Real.cos φ / b₁ : ℝ) : ℂ) * ζ₁ + ((L * d / b₁ : ℝ) : ℂ) * ζ₂ := by
  intro b₁ ζ₁ ζ₂
  have e₁ : ζ₁ = ((L * Real.sin φ / b₁ : ℝ) : ℂ) * ξ₁ + ((d * Real.cos φ / b₁ : ℝ) : ℂ) * ξ₂ := by
    simp only [ζ₁]
    push_cast
    ring
  have e₂ : ζ₂ = ((d * Real.cos φ / b₁ : ℝ) : ℂ) * ξ₁ - ((L * Real.sin φ / b₁ : ℝ) : ℂ) * ξ₂ := by
    simp only [ζ₂]
    push_cast
    ring
  rw [e₁, e₂]
  exact b_change_aux L d φ hL hd ξ₁ ξ₂ b₁ rfl

/-! ## `|log cos v| ≤ -log cos |v|` on the disc `|v| < π/2` -/

/-- `Re cos v = cos (Re v) cosh (Im v)`. -/
private lemma cos_re_eq (v : ℂ) : (Complex.cos v).re = Real.cos v.re * Real.cosh v.im := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]

/-- On the disc `|v| < π/2`, `Re cos v > 0`, so `cos v` lies in the slit plane. -/
private lemma cos_mem_slitPlane {v : ℂ} (hv : ‖v‖ < Real.pi / 2) : Complex.cos v ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  rw [cos_re_eq]
  have hre : |v.re| < Real.pi / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm v) hv
  have h1 : 0 < Real.cos v.re := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [abs_lt.mp hre]
  exact mul_pos h1 (Real.cosh_pos _)

/-- The polynomials `P₀ = X`, `P_{n+1} = P_n' · (1 + X²)`, with natural coefficients; `tan⁽ⁿ⁾ = P_n ∘ tan`. -/
private noncomputable def tanPoly : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n + 1 => Polynomial.derivative (tanPoly n) * (1 + Polynomial.X ^ 2)

/-- `P_n` with complex coefficients. -/
private noncomputable def tanPolyC (n : ℕ) : Polynomial ℂ := (tanPoly n).map (Nat.castRingHom ℂ)

private lemma tanPolyC_succ (n : ℕ) :
    tanPolyC (n + 1) = Polynomial.derivative (tanPolyC n) * (1 + Polynomial.X ^ 2) := by
  simp [tanPolyC, tanPoly, Polynomial.map_mul, Polynomial.derivative_map]

/-- `tan' = 1 + tan²` where `cos ≠ 0`. -/
private lemma one_div_cos_sq {v : ℂ} (hv : Complex.cos v ≠ 0) :
    1 / Complex.cos v ^ 2 = 1 + Complex.tan v ^ 2 := by
  rw [Complex.tan_eq_sin_div_cos]
  field_simp
  linear_combination -(Complex.sin_sq_add_cos_sq v)

/-- `tan⁽ⁿ⁾(v) = P_n(tan v)` wherever `cos v ≠ 0`. -/
private lemma iteratedDeriv_tan (n : ℕ) :
    ∀ v : ℂ, Complex.cos v ≠ 0 → iteratedDeriv n Complex.tan v = (tanPolyC n).eval (Complex.tan v) := by
  induction n with
  | zero => intro v _; simp [tanPolyC, tanPoly]
  | succ n ih =>
    intro v hv
    rw [iteratedDeriv_succ]
    have hU : IsOpen {w : ℂ | Complex.cos w ≠ 0} :=
      isOpen_ne_fun Complex.continuous_cos continuous_const
    have heq : iteratedDeriv n Complex.tan =ᶠ[𝓝 v] fun w => (tanPolyC n).eval (Complex.tan w) := by
      filter_upwards [hU.mem_nhds hv] with w hw using ih w hw
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun w => (tanPolyC n).eval (Complex.tan w))
        ((Polynomial.derivative (tanPolyC n)).eval (Complex.tan v) * (1 / Complex.cos v ^ 2)) v :=
      ((tanPolyC n).hasDerivAt (Complex.tan v)).comp v (Complex.hasDerivAt_tan hv)
    rw [hd.deriv, tanPolyC_succ, Polynomial.eval_mul, one_div_cos_sq hv]
    simp

/-- The Taylor coefficients (times `n!`) of `-log cos` at `0`: `0` and then `P_n(0)`. -/
private noncomputable def gcoef : ℕ → ℕ
  | 0 => 0
  | n + 1 => (tanPoly n).coeff 0

/-- The function `g(v) = -log cos v`. -/
private noncomputable def gfun (v : ℂ) : ℂ := -Complex.log (Complex.cos v)

private lemma gfun_hasDerivAt {v : ℂ} (hv : ‖v‖ < Real.pi / 2) : HasDerivAt gfun (Complex.tan v) v := by
  have h := ((Complex.hasDerivAt_cos v).clog (cos_mem_slitPlane hv)).neg
  rw [Complex.tan_eq_sin_div_cos]
  convert h using 1
  · funext t
    simp [gfun]
  · ring

private lemma gfun_differentiableOn : DifferentiableOn ℂ gfun (Metric.ball 0 (Real.pi / 2)) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact (gfun_hasDerivAt hv).differentiableAt.differentiableWithinAt

private lemma iteratedDeriv_gfun (n : ℕ) : iteratedDeriv n gfun 0 = (gcoef n : ℂ) := by
  cases n with
  | zero => simp [gfun, gcoef]
  | succ n =>
    rw [iteratedDeriv_succ']
    have heq : deriv gfun =ᶠ[𝓝 0] Complex.tan := by
      have hball : Metric.ball (0 : ℂ) (Real.pi / 2) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds 0 (by positivity)
      filter_upwards [hball] with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact (gfun_hasDerivAt hw).deriv
    rw [heq.iteratedDeriv_eq, iteratedDeriv_tan n 0 (by simp), Complex.tan_zero,
      ← Polynomial.coeff_zero_eq_eval_zero, tanPolyC, Polynomial.coeff_map]
    simp [gcoef]

/-- The Taylor series of `g = -log cos` at `0`, on the disc `|v| < π/2`. -/
private lemma gfun_hasSum {z : ℂ} (hz : ‖z‖ < Real.pi / 2) :
    HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹ * (gcoef n : ℝ) : ℝ) : ℂ) * z ^ n) (gfun z) := by
  have hzb : z ∈ Metric.ball (0 : ℂ) (Real.pi / 2) := by rwa [Metric.mem_ball, dist_zero_right]
  have h := Complex.hasSum_taylorSeries_on_ball gfun_differentiableOn hzb
  convert h using 1
  funext n
  rw [iteratedDeriv_gfun, sub_zero, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem sec6_logcos_proved (v : ℂ) (hv : ‖v‖ < Real.pi / 2) :
    ‖log (Complex.cos v)‖ ≤ -Real.log (Real.cos ‖v‖) := by
  have h1 := gfun_hasSum hv
  have hv' : ‖((‖v‖ : ℝ) : ℂ)‖ < Real.pi / 2 := by simpa using hv
  have h2 := gfun_hasSum hv'
  have hcos : 0 < Real.cos ‖v‖ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [norm_nonneg v]
  have hg : gfun ((‖v‖ : ℝ) : ℂ) = ((-Real.log (Real.cos ‖v‖) : ℝ) : ℂ) := by
    rw [gfun, ← Complex.ofReal_cos, ← Complex.ofReal_log hcos.le]
    push_cast; ring
  rw [hg] at h2
  have h2' : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (gcoef n : ℝ) * ‖v‖ ^ n)
      (-Real.log (Real.cos ‖v‖)) := by
    rw [← Complex.hasSum_ofReal]
    convert h2 using 1
    funext n
    push_cast
    ring
  have hle := h1.norm_le_of_bounded h2' (fun n => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)])
  rw [gfun, norm_neg] at hle
  exact hle


/-! ## The finite-dimensional bound on `W` -/

theorem sec6_Wbound_finite_proved (b₁ b₂ b₃ : ℝ) (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃) (hb : b₁ < Real.pi / 2)
    (ζ₁ ζ₂ : ℂ) (hζ : ‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2 ≤ 1) :
    ‖ζ₁‖ ≤ 1 ∧
      ‖(b₂ : ℂ) * ζ₁ + (b₃ : ℂ) * ζ₂ + log (Complex.cos ((b₁ : ℂ) * ζ₁))‖ ≤
        b₂ * ‖ζ₁‖ + b₃ * Real.sqrt (1 - ‖ζ₁‖ ^ 2) - Real.log (Real.cos (b₁ * ‖ζ₁‖)) := by
  have hz1 : ‖ζ₁‖ ≤ 1 := by nlinarith [norm_nonneg ζ₁, sq_nonneg ‖ζ₂‖]
  have hz2 : ‖ζ₂‖ ≤ Real.sqrt (1 - ‖ζ₁‖ ^ 2) := by
    have := Real.abs_le_sqrt (x := ‖ζ₂‖) (y := 1 - ‖ζ₁‖ ^ 2) (by linarith)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hv : ‖(b₁ : ℂ) * ζ₁‖ = b₁ * ‖ζ₁‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
  have hvlt : ‖(b₁ : ℂ) * ζ₁‖ < Real.pi / 2 := by
    rw [hv]
    calc b₁ * ‖ζ₁‖ ≤ b₁ * 1 := mul_le_mul_of_nonneg_left hz1 h1
      _ < Real.pi / 2 := by linarith
  have hlog := sec6_logcos_proved _ hvlt
  rw [hv] at hlog
  have e2 : ‖(b₂ : ℂ) * ζ₁‖ = b₂ * ‖ζ₁‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
  have e3 : ‖(b₃ : ℂ) * ζ₂‖ = b₃ * ‖ζ₂‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h3]
  have t1 := norm_add_le ((b₂ : ℂ) * ζ₁ + (b₃ : ℂ) * ζ₂) (log (Complex.cos ((b₁ : ℂ) * ζ₁)))
  have t2 := norm_add_le ((b₂ : ℂ) * ζ₁) ((b₃ : ℂ) * ζ₂)
  have t3 := mul_le_mul_of_nonneg_left hz2 h3
  exact ⟨hz1, by linarith⟩

/-! ## `Re e^W > 277/800` on the disc `|W| ≤ 211/200`

For `|W| ≤ T`, `Re e^W = e^{Re W} cos(Im W) ≥ F(|Im W|)` with `F(y) = e^{-√(T² - y²)} cos y` on `[0, T]`.
The minimum of `F` on `[0, T]` is attained. At `y = 0` it is `e^{-T}`, at `y = T` it is `cos T`. At an interior
minimum `m`, `F'(m) = 0` gives `√(T² - m²) = T cos m` and `m = T sin m`; then `m < 283/500`, so
`cos m > 1687/2000`, and `T cos m < 1` (from `tan m > m`); the function `c ↦ c e^{-Tc}` increases on
`[1687/2000, 1/T]`, and its value at `1687/2000` exceeds `277/800`. -/

private lemma T_lt_pi_div_two : (211 / 200 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]

/-- `F(y) = e^{-√(T² - y²)} cos y` with `T = 211/200`. -/
private noncomputable def Fd (y : ℝ) : ℝ := Real.exp (-Real.sqrt ((211 / 200 : ℝ) ^ 2 - y ^ 2)) * Real.cos y

private lemma Fd_continuous : Continuous Fd := by
  unfold Fd
  fun_prop

private lemma Fd_hasDerivAt {y : ℝ} (hy : y ^ 2 < (211 / 200 : ℝ) ^ 2) :
    HasDerivAt Fd (Real.exp (-Real.sqrt ((211 / 200 : ℝ) ^ 2 - y ^ 2)) *
      (y * Real.cos y / Real.sqrt ((211 / 200 : ℝ) ^ 2 - y ^ 2) - Real.sin y)) y := by
  have hne : (211 / 200 : ℝ) ^ 2 - y ^ 2 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t : ℝ => (211 / 200 : ℝ) ^ 2 - t ^ 2) (-(2 * y)) y := by
    simpa using (hasDerivAt_pow 2 y).const_sub ((211 / 200 : ℝ) ^ 2)
  have h2 := ((h1.sqrt hne).neg.exp).mul (Real.hasDerivAt_cos y)
  have h3 : HasDerivAt Fd
      (Real.exp (-Real.sqrt ((211 / 200 : ℝ) ^ 2 - y ^ 2)) *
          -(-(2 * y) / (2 * Real.sqrt ((211 / 200 : ℝ) ^ 2 - y ^ 2))) * Real.cos y +
        Real.exp (-Real.sqrt ((211 / 200 : ℝ) ^ 2 - y ^ 2)) * -Real.sin y) y := h2
  refine h3.congr_deriv ?_
  ring

/-- `sin(283/500) ≤ x - x³/6 + x⁵/100` at `x = 283/500`. -/
private lemma sin_a_upper :
    Real.sin (283 / 500) ≤ 283 / 500 - (283 / 500 : ℝ) ^ 3 / 6 + (283 / 500 : ℝ) ^ 5 / 100 := by
  have h := Real.sin_bound (x := 283 / 500) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 283 / 500)] at h
  linarith [(abs_le.mp h).2]

private lemma cos_a_upper :
    Real.cos (283 / 500) ≤ 1 - (283 / 500 : ℝ) ^ 2 / 2 + (283 / 500 : ℝ) ^ 4 * (5 / 96) := by
  have h := Real.cos_bound (x := 283 / 500) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 283 / 500)] at h
  linarith [(abs_le.mp h).2]

/-- `cos(283/500) = 1 - 2 sin²(283/1000) ≥ 1687/2000`. -/
private lemma cos_a_lower : (1687 / 2000 : ℝ) ≤ Real.cos (283 / 500) := by
  have hs := Real.sin_bound (x := 283 / 1000) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 283 / 1000)] at hs
  have hs2 := (abs_le.mp hs).2
  have hpos : 0 ≤ Real.sin (283 / 1000) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three])
  have hhalf := Real.sin_sq_eq_half_sub (x := (283 / 1000 : ℝ))
  rw [show (2 : ℝ) * (283 / 1000) = 283 / 500 by norm_num] at hhalf
  have hsq : Real.sin (283 / 1000) ^ 2 ≤
      (283 / 1000 - (283 / 1000 : ℝ) ^ 3 / 6 + (283 / 1000 : ℝ) ^ 5 / 100) ^ 2 :=
    pow_le_pow_left₀ hpos (by linarith) 2
  nlinarith

private lemma T_sin_a : (211 / 200 : ℝ) * Real.sin (283 / 500) < 283 / 500 := by
  have := sin_a_upper
  linarith

private lemma T_cos_a : (211 / 200 : ℝ) * Real.cos (283 / 500) ≤ 1 := by
  have := cos_a_upper
  linarith

/-- A positive solution of `m = T sin m` satisfies `m < 283/500`: for `m ≥ a = 283/500`,
`T sin m ≤ T sin a + T cos a (m - a) < a + (m - a) = m`. -/
private lemma crit_lt {m : ℝ} (hm : m = 211 / 200 * Real.sin m) : m < 283 / 500 := by
  by_contra h
  push Not at h
  have hsa : 0 ≤ Real.sin (283 / 500) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three])
  have hca : 0 ≤ Real.cos (283 / 500) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hexp := Real.sin_add (283 / 500) (m - 283 / 500)
  rw [show (283 / 500 : ℝ) + (m - 283 / 500) = m by ring] at hexp
  have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (m - 283 / 500)) hsa
  have h2 := mul_le_mul_of_nonneg_left (Real.sin_le (x := m - 283 / 500) (by linarith)) hca
  have h3 : Real.sin m ≤ Real.sin (283 / 500) + Real.cos (283 / 500) * (m - 283 / 500) := by
    rw [hexp]; linarith
  have h4 := T_sin_a
  have h6 := mul_le_of_le_one_left (sub_nonneg.mpr h) T_cos_a
  nlinarith

/-- `e^{T · 1687/2000} < (1687/2000)/(277/800)`. -/
private lemma exp_Tca : Real.exp (211 / 200 * (1687 / 2000)) < (1687 / 2000) / (277 / 800) := by
  have h := Real.exp_bound' (x := 211 / 200 * (1687 / 2000)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  refine lt_of_le_of_lt h ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `e^T < 800/277`, from `e^T = (e^{T/2})²`. -/
private lemma exp_T_bound : Real.exp (211 / 200) < 800 / 277 := by
  have h := Real.exp_bound' (x := 211 / 400) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  have hpos := Real.exp_pos (211 / 400)
  have hsq : Real.exp (211 / 200) = Real.exp (211 / 400) * Real.exp (211 / 400) := by
    rw [← Real.exp_add]; norm_num
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hm := mul_le_mul h h hpos.le (by linarith)
  rw [hsq]
  linarith

/-- For `1687/2000 ≤ c ≤ 1/T`: `c e^{-Tc} ≥ (1687/2000) e^{-T·1687/2000} > 277/800`. -/
private lemma crit_value_aux {c : ℝ} (hc : 1687 / 2000 ≤ c) (hTc : 211 / 200 * c ≤ 1) :
    277 / 800 < Real.exp (-(211 / 200 * c)) * c := by
  have hcpos : 0 < c := by linarith
  have key1 : 1687 / 2000 / c ≤ Real.exp (-(211 / 200 * (c - 1687 / 2000))) := by
    have h1 := Real.add_one_le_exp (-(1 - 1687 / 2000 / c))
    have h2 : -(1 - 1687 / 2000 / c) ≤ -(211 / 200 * (c - 1687 / 2000)) := by
      have : 211 / 200 * (c - 1687 / 2000) ≤ 1 - 1687 / 2000 / c := by
        rw [show 1 - 1687 / 2000 / c = (c - 1687 / 2000) / c by field_simp]
        rw [le_div_iff₀ hcpos]
        nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hTc)]
      linarith
    have h3 := Real.exp_le_exp.mpr h2
    linarith
  have key2 : Real.exp (-(211 / 200 * c)) =
      Real.exp (-(211 / 200 * (1687 / 2000))) * Real.exp (-(211 / 200 * (c - 1687 / 2000))) := by
    rw [← Real.exp_add]; congr 1; ring
  have key3 : 277 / 800 < Real.exp (-(211 / 200 * (1687 / 2000))) * (1687 / 2000) := by
    have hE := exp_Tca
    have hprod : Real.exp (-(211 / 200 * (1687 / 2000))) * Real.exp (211 / 200 * (1687 / 2000)) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-(211 / 200 * (1687 / 2000)))
    rw [lt_div_iff₀ (by norm_num)] at hE
    nlinarith
  have hE0 := Real.exp_pos (-(211 / 200 * (1687 / 2000)))
  rw [key2]
  calc (277 / 800 : ℝ) < Real.exp (-(211 / 200 * (1687 / 2000))) * (1687 / 2000) := key3
    _ = Real.exp (-(211 / 200 * (1687 / 2000))) * (1687 / 2000 / c) * c := by field_simp
    _ ≤ Real.exp (-(211 / 200 * (1687 / 2000))) * Real.exp (-(211 / 200 * (c - 1687 / 2000))) * c := by
        gcongr

/-- At an interior critical point `m` of `F`: `√(T² - m²) = T cos m` and `m = T sin m`. -/
private lemma crit_point {m : ℝ} (h0 : 0 < m) (hT : m < 211 / 200)
    (hd : Real.exp (-Real.sqrt ((211 / 200 : ℝ) ^ 2 - m ^ 2)) *
      (m * Real.cos m / Real.sqrt ((211 / 200 : ℝ) ^ 2 - m ^ 2) - Real.sin m) = 0) :
    Real.sqrt ((211 / 200 : ℝ) ^ 2 - m ^ 2) = 211 / 200 * Real.cos m ∧ m = 211 / 200 * Real.sin m := by
  have hpos : 0 < (211 / 200 : ℝ) ^ 2 - m ^ 2 := by nlinarith
  have hu : 0 < Real.sqrt ((211 / 200 : ℝ) ^ 2 - m ^ 2) := Real.sqrt_pos.mpr hpos
  have huu : Real.sqrt ((211 / 200 : ℝ) ^ 2 - m ^ 2) ^ 2 = (211 / 200 : ℝ) ^ 2 - m ^ 2 := Real.sq_sqrt hpos.le
  generalize Real.sqrt ((211 / 200 : ℝ) ^ 2 - m ^ 2) = u at hu huu hd ⊢
  have hcos : 0 < Real.cos m :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [T_lt_pi_div_two], by linarith [T_lt_pi_div_two]⟩
  have hsc := Real.sin_sq_add_cos_sq m
  have hd' : m * Real.cos m = u * Real.sin m := by
    have h1 : m * Real.cos m / u - Real.sin m = 0 := by
      rcases mul_eq_zero.mp hd with h | h
      · exact absurd h (Real.exp_pos _).ne'
      · exact h
    have h2 : m * Real.cos m / u = Real.sin m := by linarith
    rw [div_eq_iff hu.ne'] at h2
    rw [h2]; ring
  have hsq : u ^ 2 = (211 / 200 * Real.cos m) ^ 2 := by
    have h1 : (m * Real.cos m) ^ 2 = (u * Real.sin m) ^ 2 := by rw [hd']
    linear_combination (-1 : ℝ) * h1 - u ^ 2 * hsc + Real.cos m ^ 2 * huu
  have hTc : u = 211 / 200 * Real.cos m :=
    (pow_left_inj₀ hu.le (by positivity) two_ne_zero).mp hsq
  refine ⟨hTc, ?_⟩
  rw [hTc] at hd'
  have h3 : (m - 211 / 200 * Real.sin m) * Real.cos m = 0 := by linear_combination hd'
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · exact absurd h hcos.ne'

/-- At an interior critical point the value of `F` exceeds `277/800`. -/
private lemma crit_value {m : ℝ} (h0 : 0 < m) (hm : m = 211 / 200 * Real.sin m) :
    277 / 800 < Real.exp (-(211 / 200 * Real.cos m)) * Real.cos m := by
  have hma := crit_lt hm
  have hc_lo : 1687 / 2000 < Real.cos m := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_gt_three]) hma
    linarith [cos_a_lower]
  have hcpos : 0 < Real.cos m := by linarith
  have hc_hi : 211 / 200 * Real.cos m ≤ 1 := by
    have htan := Real.lt_tan h0 (by linarith [Real.pi_gt_three])
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcpos] at htan
    nlinarith
  exact crit_value_aux hc_lo.le hc_hi

/-- `F(y) > 277/800` for all `y ∈ [0, T]`. -/
private lemma Fd_bound : ∀ y ∈ Set.Icc (0 : ℝ) (211 / 200), 277 / 800 < Fd y := by
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 211 / 200)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by norm_num)) Fd_continuous.continuousOn
  have hFm : 277 / 800 < Fd m := by
    obtain ⟨hm0, hmT⟩ := hm
    rcases hm0.eq_or_lt with h | h
    · rw [← h]
      unfold Fd
      rw [show (211 / 200 : ℝ) ^ 2 - (0 : ℝ) ^ 2 = (211 / 200) ^ 2 by ring, Real.sqrt_sq (by norm_num),
        Real.cos_zero, mul_one]
      have hE := exp_T_bound
      have hprod : Real.exp (-(211 / 200)) * Real.exp (211 / 200) = 1 := by
        rw [← Real.exp_add]; simp
      have hpos := Real.exp_pos (-(211 / 200 : ℝ))
      nlinarith
    rcases hmT.eq_or_lt with h' | h'
    · rw [h']
      unfold Fd
      rw [sub_self, Real.sqrt_zero, neg_zero, Real.exp_zero, one_mul]
      have := Real.one_sub_sq_div_two_le_cos (x := (211 / 200 : ℝ))
      linarith
    · have hloc : IsLocalMin Fd m := hmin.isLocalMin (Icc_mem_nhds h h')
      have hd := hloc.hasDerivAt_eq_zero (Fd_hasDerivAt (by nlinarith))
      obtain ⟨hu, hs⟩ := crit_point h h' hd
      unfold Fd
      rw [hu]
      exact crit_value h hs
  intro y hy
  exact lt_of_lt_of_le hFm (isMinOn_iff.mp hmin y hy)

theorem sec6_expW_bound_proved (W : ℂ) (hW : ‖W‖ ≤ Tfar) : 277 / 800 < (exp W).re := by
  have hT : ‖W‖ ≤ 211 / 200 := hW
  rw [Complex.exp_re]
  have hnorm : W.re ^ 2 + W.im ^ 2 ≤ (211 / 200) ^ 2 := by
    have h1 : ‖W‖ ^ 2 = W.re ^ 2 + W.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h2 : ‖W‖ ^ 2 ≤ (211 / 200) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
    linarith
  have hya : |W.im| ≤ 211 / 200 := by nlinarith [sq_abs W.im, abs_nonneg W.im, sq_nonneg W.re]
  have hF := Fd_bound |W.im| ⟨abs_nonneg _, hya⟩
  have hcos : 0 < Real.cos W.im := by
    rw [← Real.cos_abs]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg W.im, Real.pi_gt_three], by
      linarith [T_lt_pi_div_two]⟩
  have hx : -Real.sqrt ((211 / 200 : ℝ) ^ 2 - |W.im| ^ 2) ≤ W.re := by
    have := Real.abs_le_sqrt (x := W.re) (y := (211 / 200 : ℝ) ^ 2 - |W.im| ^ 2) (by rw [sq_abs]; linarith)
    linarith [neg_abs_le W.re]
  unfold Fd at hF
  rw [Real.cos_abs] at hF
  calc (277 / 800 : ℝ) < _ := hF
    _ ≤ Real.exp W.re * Real.cos W.im :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) hcos.le

end Robinson.Proofs
