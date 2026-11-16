/-
Robinson/Proofs/GrunskyIneq.lean — proofs of sec3_cauchy, sec3_blocks_compressions,
sec3_OE_contractions.
Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Robinson.Defs.Basic
import Robinson.Defs.Grunsky
import Robinson.NotFormalized

namespace Robinson.Proofs

open Robinson Complex Metric Filter Topology
open ComplexConjugate
open scoped Matrix

/-! ## The finite-section bound and its consequences on `ℓ²` -/

/-- The bilinear finite-section bound `|∑_{n,m<N} xₙ Aₙₘ yₘ| ≤ ‖x‖_N ‖y‖_N` for every `N`. -/
def FinSecBound (A : ℕ → ℕ → ℂ) : Prop :=
  ∀ (N : ℕ) (x y : ℕ → ℂ),
    ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * A n m * y m‖ ≤
      Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2)

/-- A sum over `range K` of terms vanishing from `N ≤ K` on is the sum over `range N`. -/
private lemma sum_range_trunc {β : Type*} [AddCommMonoid β] (g : ℕ → β) {N K : ℕ} (h : N ≤ K)
    (hg : ∀ n, N ≤ n → g n = 0) : ∑ n ∈ Finset.range K, g n = ∑ n ∈ Finset.range N, g n := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr h)
  intro n _ hN
  simp only [Finset.mem_range, not_lt] at hN
  exact hg n hN

/-- Norms of a truncated sequence. -/
private lemma sum_sq_trunc (x : ℕ → ℂ) {N K : ℕ} (h : N ≤ K) :
    ∑ n ∈ Finset.range K, ‖(if n < N then x n else 0)‖ ^ 2 = ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 := by
  rw [sum_range_trunc _ h]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [hn]
  · intro n hn
    simp [not_lt.mpr hn]

/-- The rectangular form of the finite-section bound: rows `n < N`, columns `m < M`. -/
private lemma rect_bound {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) (N M : ℕ) (x y : ℕ → ℂ) :
    ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range M, x n * A n m * y m‖ ≤
      Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range M, ‖y m‖ ^ 2) := by
  have hN : N ≤ max N M := le_max_left _ _
  have hM : M ≤ max N M := le_max_right _ _
  have key := hA (max N M) (fun n => if n < N then x n else 0) (fun m => if m < M then y m else 0)
  rw [sum_sq_trunc x hN, sum_sq_trunc y hM] at key
  have h1 : ∑ n ∈ Finset.range (max N M), ∑ m ∈ Finset.range (max N M),
      (if n < N then x n else 0) * A n m * (if m < M then y m else 0) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range M, x n * A n m * y m := by
    rw [sum_range_trunc _ hN]
    · apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_range] at hn
      rw [sum_range_trunc _ hM]
      · apply Finset.sum_congr rfl
        intro m hm
        simp only [Finset.mem_range] at hm
        simp [hn, hm]
      · intro m hm
        simp [not_lt.mpr hm]
    · intro n hn
      apply Finset.sum_eq_zero
      intro m _
      simp [not_lt.mpr hn]
  rw [h1] at key
  exact key

/-- Each row of `A` has `∑_{m<M} |Aₙₘ|² ≤ 1`. -/
private lemma row_sq_le_one {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) (n M : ℕ) :
    ∑ m ∈ Finset.range M, ‖A n m‖ ^ 2 ≤ 1 := by
  have h := rect_bound hA (n + 1) M (fun k => if k = n then 1 else 0) (fun m => conj (A n m))
  have e1 : ∑ k ∈ Finset.range (n + 1), ∑ m ∈ Finset.range M,
      (if k = n then (1 : ℂ) else 0) * A k m * conj (A n m) =
      ((∑ m ∈ Finset.range M, ‖A n m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single n]
    · push_cast
      apply Finset.sum_congr rfl
      intro m _
      rw [ite_eq_left rfl, one_mul, mul_conj']
    · intro k _ hk
      simp [hk]
    · intro hn
      simp at hn
  have e2 : ∑ k ∈ Finset.range (n + 1), ‖(if k = n then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hn
      simp at hn
  have e3 : ∑ m ∈ Finset.range M, ‖conj (A n m)‖ ^ 2 = ∑ m ∈ Finset.range M, ‖A n m‖ ^ 2 := by
    simp
  have hS : 0 ≤ ∑ m ∈ Finset.range M, ‖A n m‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [e1, e2, e3, Complex.norm_real, Real.norm_of_nonneg hS, Real.sqrt_one, one_mul] at h
  nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg (∑ m ∈ Finset.range M, ‖A n m‖ ^ 2),
    sq_nonneg (Real.sqrt (∑ m ∈ Finset.range M, ‖A n m‖ ^ 2) - 1)]

/-- Each row of `A` is in `ℓ²`. -/
private lemma row_summable {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) (n : ℕ) :
    Summable fun m => ‖A n m‖ ^ 2 :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) (row_sq_le_one hA n)

/-- The product of two `ℓ²` sequences is summable. -/
private lemma summable_mul_of_sq {u v : ℕ → ℂ} (hu : Summable fun n => ‖u n‖ ^ 2)
    (hv : Summable fun n => ‖v n‖ ^ 2) : Summable fun n => u n * v n := by
  refine Summable.of_norm_bounded (hu.add hv) (fun n => ?_)
  rw [norm_mul]
  nlinarith [sq_nonneg (‖u n‖ - ‖v n‖), norm_nonneg (u n), norm_nonneg (v n)]

/-- The pairing of a finite vector with `A y`: `|∑_{n<N} xₙ (A y)ₙ| ≤ ‖x‖_N ‖y‖`. -/
private lemma key_bound {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) {y : ℕ → ℂ}
    (hy : Summable fun m => ‖y m‖ ^ 2) (N : ℕ) (x : ℕ → ℂ) :
    ‖∑ n ∈ Finset.range N, x n * ∑' m, A n m * y m‖ ≤
      Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑' m, ‖y m‖ ^ 2) := by
  have hrow : ∀ n, Summable fun m => A n m * y m := fun n => summable_mul_of_sq (row_summable hA n) hy
  have hlim : Tendsto (fun M => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range M, x n * A n m * y m) atTop
      (𝓝 (∑ n ∈ Finset.range N, x n * ∑' m, A n m * y m)) := by
    apply tendsto_finsetSum
    intro n _
    have := ((hrow n).hasSum.tendsto_sum_nat).const_mul (x n)
    convert this using 1
    funext M
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  refine le_of_tendsto' hlim.norm (fun M => (rect_bound hA N M x y).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (hy.sum_le_tsum _ (fun _ _ => sq_nonneg _))

/-- `A y` is in `ℓ²` with `∑_{n<N} |(A y)ₙ|² ≤ ‖y‖²`. -/
private lemma img_sq_le {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) {y : ℕ → ℂ}
    (hy : Summable fun m => ‖y m‖ ^ 2) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖∑' m, A n m * y m‖ ^ 2 ≤ ∑' m, ‖y m‖ ^ 2 := by
  have h := key_bound hA hy N (fun n => conj (∑' m, A n m * y m))
  have e1 : ∑ n ∈ Finset.range N, conj (∑' m, A n m * y m) * ∑' m, A n m * y m =
      ((∑ n ∈ Finset.range N, ‖∑' m, A n m * y m‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [conj_mul']
  have hS : 0 ≤ ∑ n ∈ Finset.range N, ‖∑' m, A n m * y m‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT : 0 ≤ ∑' m, ‖y m‖ ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
  simp only [RCLike.norm_conj] at h
  rw [e1, Complex.norm_real, Real.norm_of_nonneg hS] at h
  nlinarith [Real.sq_sqrt hS, Real.sq_sqrt hT, Real.sqrt_nonneg (∑' m, ‖y m‖ ^ 2),
    Real.sqrt_nonneg (∑ n ∈ Finset.range N, ‖∑' m, A n m * y m‖ ^ 2),
    sq_nonneg (Real.sqrt (∑ n ∈ Finset.range N, ‖∑' m, A n m * y m‖ ^ 2) -
      Real.sqrt (∑' m, ‖y m‖ ^ 2))]

/-- The bilinear form of a matrix with the finite-section bound, on `ℓ²`: the inner and outer series converge and
`|xᵀ A y| ≤ ‖x‖ ‖y‖`. -/
theorem bilinf_of_finSecBound {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) (x y : ℕ → ℂ)
    (hx : Summable fun n => ‖x n‖ ^ 2) (hy : Summable fun n => ‖y n‖ ^ 2) :
    (∀ n, Summable fun m => A n m * y m) ∧ Summable (fun n => x n * ∑' m, A n m * y m) ∧
      ‖bilinf x A y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2) := by
  have hrow : ∀ n, Summable fun m => A n m * y m := fun n => summable_mul_of_sq (row_summable hA n) hy
  have hz : Summable fun n => ‖∑' m, A n m * y m‖ ^ 2 :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) (img_sq_le hA hy)
  have hxz := summable_mul_of_sq hx hz
  refine ⟨hrow, hxz, ?_⟩
  unfold bilinf
  refine le_of_tendsto' hxz.hasSum.tendsto_sum_nat.norm (fun N => (key_bound hA hy N x).trans ?_)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (hx.sum_le_tsum _ (fun _ _ => sq_nonneg _))

/-! ## Principal blocks -/

/-- A principal block of a matrix with the finite-section bound has the finite-section bound. -/
theorem finSecBound_block {C B : ℕ → ℕ → ℂ} (hC : FinSecBound C) (p : ℕ → Prop) [DecidablePred p]
    (hB : ∀ n m, B n m = if p n ∧ p m then C n m else 0) : FinSecBound B := by
  intro N x y
  have e : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * B n m * y m =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        (if p n then x n else 0) * C n m * (if p m then y m else 0) := by
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    rw [hB n m]
    by_cases h1 : p n <;> by_cases h2 : p m <;> simp [h1, h2]
  have hxS : ∀ n, ‖(if p n then x n else 0)‖ ^ 2 ≤ ‖x n‖ ^ 2 := by
    intro n
    by_cases h1 : p n <;> simp [h1]
  have hyS : ∀ m, ‖(if p m then y m else 0)‖ ^ 2 ≤ ‖y m‖ ^ 2 := by
    intro m
    by_cases h1 : p m <;> simp [h1]
  rw [e]
  refine (hC N _ _).trans ?_
  apply mul_le_mul (Real.sqrt_le_sqrt (Finset.sum_le_sum (fun n _ => hxS n)))
    (Real.sqrt_le_sqrt (Finset.sum_le_sum (fun m _ => hyS m))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## Compressions by orthonormal columns -/

/-- For orthonormal columns `V`, the vector `V x = ∑ᵢ xᵢ V·ᵢ` has `∑ₙ |(V x)ₙ|² = ∑ᵢ |xᵢ|²`. -/
private lemma hasSum_norm_sq_comb {k : ℕ} (V : ℕ → Fin k → ℂ)
    (hV : ∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) (x : Fin k → ℂ) :
    HasSum (fun n => ‖∑ i, x i * V n i‖ ^ 2) (∑ i, ‖x i‖ ^ 2) := by
  rw [← Complex.hasSum_ofReal]
  have h : HasSum (fun n => ∑ i, ∑ j, conj (x i) * x j * (conj (V n i) * V n j))
      (∑ i, ∑ j, conj (x i) * x j * (if i = j then 1 else 0)) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => (hV i j).mul_left (conj (x i) * x j)))
  convert h using 1
  · funext n
    rw [Complex.ofReal_pow, ← conj_mul', map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    ring
  · push_cast
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [conj_mul']

/-- The bilinear form of two combinations of columns is the combination of the bilinear forms of the columns. -/
private lemma bilinf_comb {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) {k : ℕ} (V : ℕ → Fin k → ℂ)
    (hcol : ∀ i : Fin k, Summable fun n => ‖V n i‖ ^ 2) (x y : Fin k → ℂ) :
    bilinf (fun n => ∑ i, x i * V n i) A (fun n => ∑ j, y j * V n j) =
      ∑ i, ∑ j, x i * bilinf (fun n => V n i) A (fun n => V n j) * y j := by
  have hrow : ∀ (j : Fin k) (n : ℕ), Summable fun m => A n m * V m j :=
    fun j => (bilinf_of_finSecBound hA (fun n => V n j) (fun n => V n j) (hcol j) (hcol j)).1
  have hout : ∀ i j : Fin k, Summable fun n => V n i * ∑' m, A n m * V m j :=
    fun i j => (bilinf_of_finSecBound hA (fun n => V n i) (fun n => V n j) (hcol i) (hcol j)).2.1
  have hin : ∀ n, ∑' m, A n m * ∑ j, y j * V m j = ∑ j, y j * ∑' m, A n m * V m j := by
    intro n
    have h : HasSum (fun m => ∑ j, y j * (A n m * V m j)) (∑ j, y j * ∑' m, A n m * V m j) :=
      hasSum_sum (fun j _ => (hrow j n).hasSum.mul_left (y j))
    rw [← h.tsum_eq]
    congr 1
    funext m
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h : HasSum (fun n => ∑ i, ∑ j, x i * y j * (V n i * ∑' m, A n m * V m j))
      (∑ i, ∑ j, x i * y j * ∑' n, V n i * ∑' m, A n m * V m j) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => (hout i j).hasSum.mul_left (x i * y j)))
  have hL : bilinf (fun n => ∑ i, x i * V n i) A (fun n => ∑ j, y j * V n j) =
      ∑' n, (∑ i, x i * V n i) * ∑ j, y j * ∑' m, A n m * V m j := by
    simp only [bilinf, hin]
  have hterm : ∀ n, (∑ i, x i * V n i) * ∑ j, y j * ∑' m, A n m * V m j =
      ∑ i, ∑ j, x i * y j * (V n i * ∑' m, A n m * V m j) := by
    intro n
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hL, tsum_congr hterm, h.tsum_eq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [bilinf]
  ring

/-- The compression `Vᵀ A V` by orthonormal columns satisfies `|xᵀ (Vᵀ A V) y| ≤ ‖x‖ ‖y‖`. -/
theorem compression_bound {A : ℕ → ℕ → ℂ} (hA : FinSecBound A) {k : ℕ} (V : ℕ → Fin k → ℂ)
    (hV : ∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0))
    (x y : Fin k → ℂ) :
    ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) A (fun n => V n j) * y j‖ ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2) := by
  have hcol : ∀ i : Fin k, Summable fun n => ‖V n i‖ ^ 2 := by
    intro i
    have h := (hasSum_norm_sq_comb V hV (fun j => if j = i then 1 else 0)).summable
    simpa using h
  have hu := hasSum_norm_sq_comb V hV x
  have hw := hasSum_norm_sq_comb V hV y
  rw [← bilinf_comb hA V hcol x y, ← hu.tsum_eq, ← hw.tsum_eq]
  exact (bilinf_of_finSecBound hA _ _ hu.summable hw.summable).2.2

/-! ## The three rows -/

/-- sec_03_tools.tex:32-35 (eq:cauchy), given the strong Grunsky inequality. -/
theorem sec3_cauchy_proved (hG : FactGrunsky) (g : ℂ → ℂ) (hg : InS g) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff g γ)
    (x y : ℕ → ℂ) (hx : Summable fun n => ‖x n‖ ^ 2) (hy : Summable fun n => ‖y n‖ ^ 2) :
    (∀ n, Summable fun m => Cmat γ n m * y m) ∧ Summable (fun n => x n * ∑' m, Cmat γ n m * y m) ∧
      ‖bilinf x (Cmat γ) y‖ ≤ Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2) :=
  bilinf_of_finSecBound (hG g γ hg hγ) x y hx hy

open Classical in
/-- sec_03_tools.tex:36: principal blocks and compressions, given the strong Grunsky inequality. -/
theorem sec3_blocks_compressions_proved (hG : FactGrunsky) (g : ℂ → ℂ) (hg : InS g) (γ : ℕ → ℕ → ℂ)
    (hγ : IsGrunskyCoeff g γ) :
    (∀ (S : Set ℕ) (x y : ℕ → ℂ), Summable (fun n => ‖x n‖ ^ 2) → Summable (fun n => ‖y n‖ ^ 2) →
      ‖bilinf x (fun n m => if n ∈ S ∧ m ∈ S then Cmat γ n m else 0) y‖ ≤
        Real.sqrt (∑' n, ‖x n‖ ^ 2) * Real.sqrt (∑' n, ‖y n‖ ^ 2)) ∧
    ∀ (k : ℕ) (V : ℕ → Fin k → ℂ),
      (∀ i j : Fin k, HasSum (fun n => conj (V n i) * V n j) (if i = j then 1 else 0)) →
      ∀ x y : Fin k → ℂ, ‖∑ i, ∑ j, x i * bilinf (fun n => V n i) (Cmat γ) (fun n => V n j) * y j‖ ≤
        Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2) := by
  have hC : FinSecBound (Cmat γ) := hG g γ hg hγ
  refine ⟨fun S x y hx hy => ?_, fun k V hV x y => compression_bound hC V hV x y⟩
  have hB : FinSecBound (fun n m => if n ∈ S ∧ m ∈ S then Cmat γ n m else 0) :=
    finSecBound_block hC (fun n => n ∈ S) (fun n m => rfl)
  exact (bilinf_of_finSecBound hB x y hx hy).2.2

/-! ## The odd root and its Grunsky coefficients -/

/-- The odd square root of `f ∈ 𝒮` is in `𝒮`. -/
private lemma oddRoot_inS {f h : ℂ → ℂ} (hf : InS f) (hh : IsOddRoot f h) : InS h := by
  obtain ⟨hdiff, hodd, hsq, hder⟩ := hh
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hmap0 : h 0 = 0 := by
    have := hodd 0 h0
    rw [neg_zero] at this
    linear_combination this / 2
  have hsqball : ∀ s ∈ ball (0 : ℂ) 1, s ^ 2 ∈ ball (0 : ℂ) 1 := by
    intro s hs
    rw [mem_ball_zero_iff] at hs ⊢
    rw [norm_pow]
    nlinarith [norm_nonneg s]
  refine ⟨hdiff, ?_, hmap0, hder⟩
  intro s hs t ht hst
  have hsq' : s ^ 2 = t ^ 2 := by
    apply hf.injOn (hsqball s hs) (hsqball t ht)
    rw [← hsq s hs, ← hsq t ht, hst]
  have hfac : (s - t) * (s + t) = 0 := by linear_combination hsq'
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact sub_eq_zero.mp h1
  · have hts : s = -t := eq_neg_of_add_eq_zero_left h1
    have hzero : h s = 0 := by
      have e := hodd t ht
      rw [← hts, ← hst] at e
      linear_combination e / 2
    have hs0 : s ^ 2 = (0 : ℂ) ^ 2 := by
      apply hf.injOn (hsqball s hs) (hsqball 0 h0)
      rw [← hsq s hs, hzero, ← hsq 0 h0, hmap0]
    have hs00 : s = 0 := by
      have hs0' : s ^ 2 = 0 := by rw [hs0]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs0'
    have ht0 : t = 0 := by linear_combination hts - hs00
    rw [hs00, ht0]

/-- The kernel quotient is symmetric in `(s, t)`. -/
private lemma kernelQuot_symm (g : ℂ → ℂ) (s t : ℂ) : kernelQuot g s t = kernelQuot g t s := by
  unfold kernelQuot
  by_cases hst : s = t
  · subst hst
    ring
  · rw [ite_eq_right hst, ite_eq_right (Ne.symm hst)]
    rw [show (g t - g s) / (t - s) = (g s - g t) / (s - t) by
      rw [← neg_sub (g s), ← neg_sub s, neg_div_neg_eq]]
    ring

/-- For the odd root `h`, the kernel quotient is even in `(s, t)` jointly. -/
private lemma kernelQuot_neg {f h : ℂ → ℂ} (hh : IsOddRoot f h) {s t : ℂ} (hs : s ∈ ball (0 : ℂ) 1)
    (ht : t ∈ ball (0 : ℂ) 1) : kernelQuot h (-s) (-t) = kernelQuot h s t := by
  have hodd := hh.2.1
  have hderiv : deriv h (-s) = deriv h s := by
    have hev : h =ᶠ[𝓝 s] fun z => -h (-z) := by
      filter_upwards [isOpen_ball.mem_nhds hs] with z hz
      rw [hodd z hz, neg_neg]
    rw [hev.deriv_eq, deriv.fun_neg, deriv_comp_neg, neg_neg]
  have e1 : (if -s = -t then deriv h (-s) else (h (-s) - h (-t)) / (-s - -t)) =
      (if s = t then deriv h s else (h s - h t) / (s - t)) := by
    by_cases hst : s = t
    · rw [ite_eq_left (by rw [hst]), ite_eq_left hst, hderiv]
    · rw [ite_eq_right (fun e => hst (neg_inj.mp e)), ite_eq_right hst, hodd s hs, hodd t ht,
        show -h s - -h t = -(h s - h t) by ring, show -s - -t = -(s - t) by ring, neg_div_neg_eq]
  have e2 : ∀ u ∈ ball (0 : ℂ) 1, (if -u = 0 then 1 else -u / h (-u)) = (if u = 0 then 1 else u / h u) := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · rw [ite_eq_right (neg_ne_zero.mpr hu0), ite_eq_right hu0, hodd u hu, neg_div_neg_eq]
  unfold kernelQuot
  rw [e1, e2 s hs, e2 t ht]

/-- The transposed coefficients are again Grunsky coefficients. -/
private lemma isGrunskyCoeff_transpose {g : ℂ → ℂ} {γ : ℕ → ℕ → ℂ} (hγ : IsGrunskyCoeff g γ) :
    IsGrunskyCoeff g (fun n m => γ m n) := by
  refine ⟨fun n m hnm => hγ.1 m n hnm.symm, fun s t hs ht => ?_⟩
  obtain ⟨hsum, hexp⟩ := hγ.2 t s ht hs
  have hfun : (fun nm : ℕ × ℕ => ‖γ nm.2 nm.1 * s ^ nm.1 * t ^ nm.2‖) =
      (fun nm : ℕ × ℕ => ‖γ nm.1 nm.2 * t ^ nm.1 * s ^ nm.2‖) ∘ Equiv.prodComm ℕ ℕ := by
    funext nm
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring_nf
  have hk : kser (fun n m => γ m n) s t = kser γ t s := by
    unfold kser
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
    congr 1
    funext nm
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hsum
  · rw [hk, hexp, kernelQuot_symm]

/-- For the odd root `h`, the coefficients twisted by `(-1)^(n+m)` are again Grunsky coefficients. -/
private lemma isGrunskyCoeff_sign {f h : ℂ → ℂ} (hh : IsOddRoot f h) {γ : ℕ → ℕ → ℂ}
    (hγ : IsGrunskyCoeff h γ) : IsGrunskyCoeff h (fun n m => (-1) ^ (n + m) * γ n m) := by
  refine ⟨fun n m hnm => by simp only [hγ.1 n m hnm, mul_zero], fun s t hs ht => ?_⟩
  have hs' : -s ∈ ball (0 : ℂ) 1 := by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
  have ht' : -t ∈ ball (0 : ℂ) 1 := by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
  obtain ⟨hsum, _⟩ := hγ.2 s t hs ht
  obtain ⟨_, hexp⟩ := hγ.2 (-s) (-t) hs' ht'
  have hk : kser (fun n m => (-1) ^ (n + m) * γ n m) s t = kser γ (-s) (-t) := by
    unfold kser
    congr 1
    funext nm
    dsimp only
    rw [neg_pow s, neg_pow t, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · convert hsum using 1
    funext nm
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · rw [hk, hexp, kernelQuot_neg hh hs ht]

set_option linter.unusedVariables false in
/-- sec_03_tools.tex:43, given the strong Grunsky inequality and the uniqueness of Grunsky coefficients
(row `sec3_grunsky_unique`, the hypothesis `hX`). -/
theorem sec3_OE_contractions_proved_from
    (hX : ∀ (g : ℂ → ℂ) (hg : InS g) (γ γ' : ℕ → ℕ → ℂ) (h : IsGrunskyCoeff g γ)
      (h' : IsGrunskyCoeff g γ'), γ = γ')
    (hG : FactGrunsky) (f h : ℂ → ℂ) (hf : InS f) (hh : IsOddRoot f h)
    (γ : ℕ → ℕ → ℂ) (hγ : IsGrunskyCoeff h γ) :
    (∀ n m : ℕ, Oblock γ n m = Oblock γ m n) ∧ (∀ n m : ℕ, Eblock γ n m = Eblock γ m n) ∧
      (∀ n m : ℕ, Cmat γ n m = Oblock γ n m + Eblock γ n m) ∧
      ∀ (N : ℕ) (x y : ℕ → ℂ),
        ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Oblock γ n m * y m‖ ≤
            Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) ∧
          ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, x n * Eblock γ n m * y m‖ ≤
            Real.sqrt (∑ n ∈ Finset.range N, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Finset.range N, ‖y m‖ ^ 2) := by
  have hS : InS h := oddRoot_inS hf hh
  have hsym : ∀ n m, γ n m = γ m n := fun n m =>
    congrFun (congrFun (hX h hS γ _ hγ (isGrunskyCoeff_transpose hγ)) n) m
  have hpar : ∀ n m, (n + m) % 2 = 1 → γ n m = 0 := by
    intro n m hnm
    have e := congrFun (congrFun (hX h hS γ _ hγ (isGrunskyCoeff_sign hh hγ)) n) m
    simp only [(Nat.odd_iff.mpr hnm).neg_one_pow] at e
    linear_combination e / 2
  have hCsym : ∀ n m, Cmat γ n m = Cmat γ m n := by
    intro n m
    unfold Cmat
    rw [hsym n m, mul_comm (n : ℝ)]
  have hC : FinSecBound (Cmat γ) := hG h γ hS hγ
  have hO : FinSecBound (Oblock γ) :=
    finSecBound_block hC (fun n => n % 2 = 1) (fun n m => rfl)
  have hE : FinSecBound (Eblock γ) :=
    finSecBound_block hC (fun n => n % 2 = 0 ∧ n ≠ 0) (fun n m => by simp only [Eblock, and_assoc])
  refine ⟨fun n m => ?_, fun n m => ?_, fun n m => ?_, fun N x y => ⟨hO N x y, hE N x y⟩⟩
  · unfold Oblock
    rw [hCsym n m]
    by_cases h1 : n % 2 = 1 <;> by_cases h2 : m % 2 = 1 <;> simp [h1, h2]
  · unfold Eblock
    split_ifs <;> first | exact hCsym n m | rfl | (exfalso; omega)
  · unfold Oblock Eblock
    by_cases h1 : n % 2 = 1 ∧ m % 2 = 1
    · have h2 : ¬(n % 2 = 0 ∧ n ≠ 0 ∧ m % 2 = 0 ∧ m ≠ 0) := fun hc => by omega
      rw [ite_eq_left h1, ite_eq_right h2, add_zero]
    · by_cases h2 : n % 2 = 0 ∧ n ≠ 0 ∧ m % 2 = 0 ∧ m ≠ 0
      · rw [ite_eq_right h1, ite_eq_left h2, zero_add]
      · rw [ite_eq_right h1, ite_eq_right h2, add_zero]
        have hz : γ n m = 0 := by
          by_cases hp : (n + m) % 2 = 1
          · exact hpar n m hp
          · exact hγ.1 n m (by omega)
        simp [Cmat, hz]

end Robinson.Proofs
