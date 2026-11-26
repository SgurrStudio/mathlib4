/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Normal.Borel
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Moments.SubGaussian

import Mathlib.Algebra.Order.Floor.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Copeland–Erdős theorem

Let `a₀ < a₁ < a₂ < …` be positive integers such that for every `θ < 1` the number of terms
`≤ N` is at least `N ^ θ` for all large `N`. **Copeland and Erdős** (1946) proved that the real
number `0.a₀ a₁ a₂ …` obtained by concatenating the base-`b` expansions of the `aᵢ` is normal in
base `b`. Applied to the primes this shows that the *Copeland–Erdős constant*
`0.2357111317192329…` is normal in base ten. The special case `aₙ = n + 1` is Champernowne's
theorem (`Mathlib.NumberTheory.Normal.Champernowne`).

## Main definitions

* `Real.IsNormalSeq b d`: the digit sequence `d : ℕ → ℕ` is normal in base `b`.
* `Real.concatStart b a t`, `Real.concatDigit b a n`: positions and digits of the concatenation
  of the base-`b` expansions of `a 0, a 1, …`.
* `Real.concatenation b a`: the real number `0.a₀ a₁ a₂ …` in base `b`.
* `Real.copelandErdos b`: the base-`b` Copeland–Erdős constant (concatenated primes).

## Main statements

* `Real.val_digits_eq_digit`, `Real.digit_ofDigits`: `Real.digit` agrees with Mathlib's
  `Real.digits`, and recovers the digits of `Real.ofDigits` not ending in `b - 1`s.
* `Real.measureReal_le_abs_blockCount_sub`: a large deviation (Hoeffding) bound for the number of
  occurrences of a block among the first `n` digits of a uniform random `x ∈ [0, 1)`.
* `Real.isNormalIn_ofDigits`: a real number whose digit sequence is normal is normal.
* `Real.isNormalSeq_concatDigit`: the Copeland–Erdős theorem for digit sequences.
* `Real.isNormalIn_concatenation`: the Copeland–Erdős theorem.
* `Real.isNormalIn_copelandErdos`: the concatenation of the primes is normal in every base.

## Proof sketch

By Hoeffding's inequality applied to the independent base-`b` digits of a uniform random
`x ∈ [0, 1)`, all but `b ^ ((1 - δ) ℓ)` of the `ℓ`-digit integers contain the block `w` with
frequency within `ε` of `b⁻ᵏ`. The density hypothesis provides at least `b ^ (θ ℓ)` terms below
`b ^ ℓ` with `θ > 1 - δ`, so the exceptional terms contribute a negligible proportion of digits.

## References

* [A. H. Copeland, P. Erdős, *Note on normal numbers*][CopelandErdos1946]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- A digit sequence `d : ℕ → ℕ` is *normal in base `b`* if every block `w` of `k` base-`b`
digits occurs in it with asymptotic frequency `b⁻ᵏ`. -/
def IsNormalSeq (b : ℕ) (d : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Fin b), Tendsto (fun N : ℕ ↦
    (((Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j) = w j).card : ℝ) / N) atTop
      (𝓝 ((b : ℝ) ^ k)⁻¹)

/-- `Real.digit` agrees with Mathlib's `Real.digits` on `[0, 1)`. -/
theorem val_digits_eq_digit [NeZero b] {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    (digits x b n : ℕ) = digit b x n := by
  rw [digit_eq_floor_mod hx.1, digits, Fin.val_ofNat]

theorem ofDigits_lt_one {b : ℕ} (hb : 1 < b) (c : ℕ → Fin b) {m : ℕ} (hm : (c m : ℕ) + 1 < b) :
    ofDigits c < 1 := by
  rw [← ofDigits_const_last_eq_one' hb]
  refine Summable.tsum_lt_tsum_of_nonneg (i := m) (fun _ ↦ ofDigitsTerm_nonneg) (fun i ↦ ?_) ?_
    summable_ofDigitsTerm
  · exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by simp; omega)) (by positivity)
  · exact mul_lt_mul_of_pos_right (Nat.cast_lt.2 (by simp; omega)) (by positivity)

/-- If a digit sequence does not end in an infinite string of `b - 1`s, then it is the
base-`b` expansion of the real number it represents. -/
theorem digit_ofDigits {b : ℕ} (hb : 1 < b) (a : ℕ → Fin b)
    (ha : ∀ n, ∃ m, n < m ∧ (a m : ℕ) + 1 < b) (n : ℕ) : digit b (ofDigits a) n = a n := by
  set S : ℕ := ∑ i ∈ Finset.range (n + 1), (a i : ℕ) * b ^ (n - i) with hS_def
  have hS : (∑ i ∈ Finset.range (n + 1), ofDigitsTerm a i) * (b : ℝ) ^ (n + 1) = S := by
    rw [Finset.sum_mul, hS_def, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    rw [ofDigitsTerm, Nat.cast_mul, Nat.cast_pow,
      show (b : ℝ) ^ (n + 1) = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (n - i) by
        rw [← pow_add]; congr 1; omega]
    field_simp
  set y := ofDigits fun i ↦ a (i + (n + 1))
  have hy0 : 0 ≤ y := ofDigits_nonneg _
  have hy1 : y < 1 := by
    obtain ⟨m, hm, hm'⟩ := ha n
    exact ofDigits_lt_one hb _ (m := m - (n + 1)) (by rwa [Nat.sub_add_cancel hm])
  have hx : ofDigits a * (b : ℝ) ^ (n + 1) = S + y := by
    rw [ofDigits_eq_sum_add_ofDigits a (n + 1), add_mul, hS, mul_comm _ y, mul_assoc,
      inv_mul_cancel₀ (by positivity), mul_one]
  have hfl : ⌊ofDigits a * (b : ℝ) ^ (n + 1)⌋ = S := by
    rw [hx, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hmod : S % b = a n := by
    rw [hS_def, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    obtain ⟨q, hq⟩ : b ∣ ∑ i ∈ Finset.range n, (a i : ℕ) * b ^ (n - i) :=
      Finset.dvd_sum fun i hi ↦
        (dvd_pow_self b (by have := Finset.mem_range.1 hi; omega)).mul_left _
    rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt (a n).isLt]
  rw [digit, hfl, ← Int.natCast_mod, Int.toNat_natCast, hmod]

theorem isNormalIn_iff_isNormalSeq : IsNormalIn b x ↔ IsNormalSeq b (digit b x) := by
  simp only [IsNormalIn, IsNormalSeq, blockCount]

/-- A real number whose digit sequence is normal in base `b ≥ 2` is normal in base `b`. -/
theorem isNormalIn_ofDigits (hb : 2 ≤ b) {d : ℕ → Fin b} (h : IsNormalSeq b fun n ↦ d n) :
    IsNormalIn b (ofDigits d) := by
  -- the digit `0` occurs infinitely often, so `d` is the digit sequence of `ofDigits d`
  have hd : ∀ n, ∃ m, n < m ∧ (d m : ℕ) + 1 < b := by
    by_contra! hcon
    obtain ⟨n, hn⟩ := hcon
    have h0 := h 1 fun _ ↦ ⟨0, by omega⟩
    have hle : ∀ N, (((Finset.range N).filter fun i ↦
        ∀ j : Fin 1, (d (i + j) : ℕ) = ((fun _ ↦ (⟨0, by omega⟩ : Fin b)) j : ℕ)).card : ℝ) ≤
        n + 1 := fun N ↦ by
      have : ((Finset.range N).filter fun i ↦
          ∀ j : Fin 1, (d (i + j) : ℕ) = ((fun _ ↦ (⟨0, by omega⟩ : Fin b)) j : ℕ)) ⊆
          Finset.range (n + 1) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range, Fin.forall_fin_one, Fin.val_zero,
          add_zero] at hi
        by_contra hin
        have := hn i (by simp at hin; omega)
        omega
      exact_mod_cast (Finset.card_le_card this).trans (Finset.card_range _).le
    have h1 : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun i ↦
        ∀ j : Fin 1, (d (i + j) : ℕ) = ((fun _ ↦ (⟨0, by omega⟩ : Fin b)) j : ℕ)).card : ℝ) / N)
        atTop (𝓝 0) :=
      squeeze_zero (fun N ↦ by positivity) (fun N ↦ div_le_div_of_nonneg_right (hle N)
        (Nat.cast_nonneg N)) (tendsto_const_div_atTop_nhds_zero_nat _)
    have := tendsto_nhds_unique h0 h1
    simp at this
    omega
  rw [isNormalIn_iff_isNormalSeq]
  convert h using 2
  exact digit_ofDigits (by omega) d hd _

section LargeDeviation

/-! ### A large deviation estimate for the digits of a random real number -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {k : ℕ}

/-- The number of occurrences of the block `w` in the `ℓ`-digit base-`b` expansion of `m`
(with leading zeros), indexed by the position `s` of the block counted from the right. -/
def natBlockCount (b ℓ m : ℕ) (w : Fin k → Fin b) : ℕ :=
  ((Finset.range (ℓ + 1 - k)).filter fun s ↦ m / b ^ s % b ^ k = blockCode w).card

theorem natBlockCount_le (b ℓ m : ℕ) (w : Fin k → Fin b) : natBlockCount b ℓ m w ≤ ℓ + 1 - k :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- The occurrences of `w` among the first `ℓ` digits of `x ∈ [0, 1)` are the occurrences of `w`
in the base-`b` expansion of `⌊x * b ^ ℓ⌋₊`. -/
theorem blockCount_eq_natBlockCount (hb : 0 < b) (hx : x ∈ Ico (0 : ℝ) 1)
    (w : Fin k → Fin b) {ℓ : ℕ} (hkℓ : k ≤ ℓ) :
    blockCount b x w (ℓ + 1 - k) = natBlockCount b ℓ ⌊x * (b : ℝ) ^ ℓ⌋₊ w := by
  classical
  rw [blockCount, natBlockCount]
  refine Finset.card_bij' (fun i _ ↦ ℓ - k - i) (fun s _ ↦ ℓ - k - s) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨by omega, ?_⟩
    rw [← forall_div_pow_mod_eq_iff hb]
    intro j
    have := hi.2 j
    rw [digit_eq_floor_div_mod hb hx (n := ℓ) (by omega)] at this
    rw [Nat.div_div_eq_div_mul, ← pow_add, ← this,
      show ℓ - k - i + (k - 1 - j) = ℓ - 1 - (i + j) by omega]
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
    refine ⟨by omega, fun j ↦ ?_⟩
    have := (forall_div_pow_mod_eq_iff hb _ w).2 hs.2 j
    rw [digit_eq_floor_div_mod hb hx (n := ℓ) (by omega), ← this, Nat.div_div_eq_div_mul,
      ← pow_add, show s + (k - 1 - j) = ℓ - 1 - (ℓ - k - s + j) by omega]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    omega
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    omega

theorem measurableSet_block (w : Fin k → Fin b) (p : ℕ) :
    MeasurableSet {x : ℝ | ∀ q : Fin k, digit b x (p + q) = w q} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun q ↦ measurable_digit b _ (measurableSet_singleton _)

/-- Under the uniform measure on `[0, 1)`, the probability that the blocks of `k` digits starting
at the positions `r + j * k` (`j ∈ S`) all equal `w` is `b ^ (-k * #S)`. -/
theorem volume_restrict_biInter_block_eq (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b)
    (r : ℕ) (S : Finset ℕ) :
    volume.restrict (Ico (0 : ℝ) 1)
        (⋂ j ∈ S, {x | ∀ q : Fin k, digit b x (r + j * k + q) = w q}) =
      (((b : ℝ≥0∞) ^ k) ^ S.card)⁻¹ := by
  classical
  set f : ℕ × ℕ → ℕ := fun p ↦ r + p.1 * k + p.2
  set Q := (S ×ˢ Finset.range k).image f
  have hdiv : ∀ j q, q < k → (j * k + q) / k = j ∧ (j * k + q) % k = q := fun j q hq ↦ by
    rw [add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hq, zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
    exact ⟨rfl, rfl⟩
  have hinj : Set.InjOn f (S ×ˢ Finset.range k : Finset (ℕ × ℕ)) := by
    rintro ⟨j, q⟩ h ⟨j', q'⟩ h' e
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at h h'
    simp only [f] at e
    have e' : j * k + q = j' * k + q' := by omega
    obtain ⟨h1, h2⟩ := hdiv j q h.2
    obtain ⟨h1', h2'⟩ := hdiv j' q' h'.2
    rw [e'] at h1 h2
    simp only [Prod.mk.injEq]
    exact ⟨h1.symm.trans h1', h2.symm.trans h2'⟩
  set v : ℕ → ℕ := fun p ↦ w ⟨(p - r) % k, Nat.mod_lt _ hk⟩
  have hv : ∀ j (q : Fin k), v (r + j * k + q) = w q := fun j q ↦ by
    simp only [v]
    congr 2
    ext
    simp only
    rw [show r + j * k + q - r = j * k + q by omega, (hdiv j q q.isLt).2]
  have hset : (⋂ j ∈ S, {x : ℝ | ∀ q : Fin k, digit b x (r + j * k + q) = w q}) =
      ⋂ p ∈ Q, {x | digit b x p = v p} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, Q, Finset.mem_image, Finset.mem_product,
      Finset.mem_range, Prod.exists, f]
    constructor
    · rintro h p ⟨j, q, ⟨hj, hq⟩, rfl⟩
      have := h j hj ⟨q, hq⟩
      rw [this, ← hv j ⟨q, hq⟩]
    · intro h j hj q
      rw [h _ ⟨j, q, ⟨hj, q.isLt⟩, rfl⟩, hv]
  have hQ : Q.card = S.card * k := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range]
  rw [hset, volume_restrict_biInter_digit_eq hb Q fun p _ ↦ (w _).isLt, hQ, ← pow_mul,
    mul_comm]

/-- Under the uniform measure on `[0, 1)`, the events "the block of `k` digits at position
`r + j * k` is `w`" (`j : ℕ`) are mutually independent. -/
theorem iIndepSet_block (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b) (r : ℕ) :
    iIndepSet (fun j ↦ {x : ℝ | ∀ q : Fin k, digit b x (r + j * k + q) = w q})
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  rw [iIndepSet_iff_meas_biInter fun j ↦ measurableSet_block w _]
  intro S
  rw [volume_restrict_biInter_block_eq hb hk w r S, Finset.prod_congr rfl fun j _ ↦ by
    simpa using volume_restrict_biInter_block_eq hb hk w r {j}, Finset.prod_const,
    ENNReal.inv_pow]

theorem volume_restrict_block_eq (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b) (r j : ℕ) :
    volume.restrict (Ico (0 : ℝ) 1) {x : ℝ | ∀ q : Fin k, digit b x (r + j * k + q) = w q} =
      ((b : ℝ≥0∞) ^ k)⁻¹ := by
  simpa using volume_restrict_biInter_block_eq hb hk w r {j}

/-- **Hoeffding's inequality** for the number of occurrences of the block `w` at the positions
`r, r + k, …, r + (J - 1) k` of a uniform random `x ∈ [0, 1)`, both tails. -/
theorem measureReal_le_sum_block_sub (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b) (r J : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (volume.restrict (Ico (0 : ℝ) 1)).real {x | t ≤ σ * ∑ j ∈ Finset.range J,
      (({x : ℝ | ∀ q : Fin k, digit b x (r + j * k + q) = w q}.indicator (fun _ ↦ 1) x : ℝ) -
        ((b : ℝ) ^ k)⁻¹)} ≤ exp (-2 * t ^ 2 / J) := by
  set μ := volume.restrict (Ico (0 : ℝ) 1)
  set E : ℕ → Set ℝ := fun j ↦ {x : ℝ | ∀ q : Fin k, digit b x (r + j * k + q) = w q}
  set X : ℕ → ℝ → ℝ := fun j ↦ (E j).indicator fun _ ↦ 1
  have hE : ∀ j, MeasurableSet (E j) := fun j ↦ measurableSet_block w _
  have hX : ∀ j, Measurable (X j) := fun j ↦ measurable_const.indicator (hE j)
  have hmean : ∀ j, μ[X j] = ((b : ℝ) ^ k)⁻¹ := fun j ↦ by
    rw [show X j = (E j).indicator 1 from rfl, integral_indicator_one (hE j), measureReal_def,
      volume_restrict_block_eq hb hk w r j, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_natCast]
  have hind : iIndepFun X μ := (iIndepSet_block hb hk w r).iIndepFun_indicator
  have hIcc : ∀ j, ∀ᵐ x ∂μ, X j x ∈ Icc (0 : ℝ) 1 := fun j ↦ Eventually.of_forall fun x ↦ by
    simp only [X, Set.indicator]
    split_ifs <;> simp
  set Z : ℕ → ℝ → ℝ := fun j x ↦ σ * (X j x - μ[X j])
  have hZind : iIndepFun Z μ := by
    have := hind.comp (fun j (y : ℝ) ↦ σ * (y - μ[X j]))
      (fun j ↦ (measurable_id.sub_const _).const_mul σ)
    exact this
  have hsub : ∀ j, HasSubgaussianMGF (Z j) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := fun j ↦ by
    have h := hasSubgaussianMGF_of_mem_Icc (hX j).aemeasurable (hIcc j)
    rcases hσ with rfl | rfl
    · convert h using 1
      ext x
      simp [Z]
    · convert h.neg using 1
      ext x
      simp [Z]
  have key := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hZind (n := J)
    (fun j _ ↦ hsub j) ht
  have hc : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    simp only [sub_zero, nnNorm_one, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one]
    norm_num
  rw [hc] at key
  calc _ = μ.real {ω | t ≤ ∑ i ∈ Finset.range J, Z i ω} := by
        congr 1
        ext x
        simp only [Z, hmean, Finset.mul_sum]
        rfl
    _ ≤ _ := key
    _ = _ := by congr 1; ring

/-- **Large deviations for block counts**: under the uniform measure on `[0, 1)`, the number of
occurrences of a block `w` of length `k` among the first `n` digits deviates from `n / b ^ k` by
at least `t` with probability at most `2 k exp (-2 t² / (k² n))`. -/
theorem measureReal_le_abs_blockCount_sub (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b)
    {n : ℕ} (hn : k ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (volume.restrict (Ico (0 : ℝ) 1)).real
        {x | t ≤ |(blockCount b x w n : ℝ) - n / (b : ℝ) ^ k|} ≤
      2 * k * exp (-2 * t ^ 2 / (k ^ 2 * n)) := by
  classical
  set μ := volume.restrict (Ico (0 : ℝ) 1)
  set E : ℕ → ℕ → Set ℝ := fun r j ↦ {x : ℝ | ∀ q : Fin k, digit b x (r + j * k + q) = w q}
  set J : ℕ → ℕ := fun r ↦ (n + (k - 1 - r)) / k
  set c : ℝ := ((b : ℝ) ^ k)⁻¹
  set W : ℕ → ℝ → ℝ := fun r x ↦ ∑ j ∈ Finset.range (J r), ((E r j).indicator (fun _ ↦ 1) x - c)
  -- Hermite's identity: the residue classes partition the positions
  have hJ : ∑ r ∈ Finset.range k, J r = n := by
    have h := Int.sum_range_add_ediv (n : ℤ) hk
    rw [← Finset.sum_range_reflect] at h
    have : ∀ r ∈ Finset.range k, ((n : ℤ) + ((k - 1 - r : ℕ) : ℤ)) / (k : ℤ) = ((J r : ℕ) : ℤ) :=
      fun r _ ↦ by simp only [J, Int.natCast_div, Nat.cast_add]
    rw [Finset.sum_congr rfl this] at h
    exact_mod_cast h
  have hdec : ∀ x, (blockCount b x w n : ℝ) - n / (b : ℝ) ^ k = ∑ r ∈ Finset.range k, W r x := by
    intro x
    have hBC : blockCount b x w n = ∑ r ∈ Finset.range k,
        ((Finset.range (J r)).filter fun j ↦ x ∈ E r j).card := by
      rw [blockCount_eq_sum hk hb w n]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      simp only [blockCount, Fin.forall_fin_one, Fin.val_zero, add_zero]
      exact congrArg Finset.card (Finset.filter_congr fun j _ ↦
        (forall_digit_eq_iff_digit_pow hb w r j).symm)
    have hind : ∀ r, ∑ j ∈ Finset.range (J r), (E r j).indicator (fun _ ↦ (1 : ℝ)) x =
        (((Finset.range (J r)).filter fun j ↦ x ∈ E r j).card : ℝ) := fun r ↦ by
      rw [Finset.natCast_card_filter]
      exact Finset.sum_congr rfl fun j _ ↦ by simp [Set.indicator_apply]
    simp only [W, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hind]
    rw [hBC, ← Finset.sum_mul, ← Nat.cast_sum (s := Finset.range k) (f := J), hJ, div_eq_mul_inv,
      Nat.cast_sum]
  -- each residue class has between `1` and `n` positions
  have hJbd : ∀ r ∈ Finset.range k, 0 < J r ∧ J r ≤ n := fun r hr ↦ by
    have hr := Finset.mem_range.1 hr
    refine ⟨Nat.div_pos (by omega) hk, Nat.div_le_of_le_mul ?_⟩
    have h1 : k - 1 ≤ (k - 1) * n := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : k * n = n + (k - 1) * n := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      ring
    omega
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsub : {x | t ≤ |(blockCount b x w n : ℝ) - n / (b : ℝ) ^ k|} ⊆
      ⋃ r ∈ Finset.range k, ({x | t / k ≤ 1 * W r x} ∪ {x | t / k ≤ -1 * W r x}) := by
    intro x hx
    simp only [mem_ofPred_eq, hdec x] at hx
    by_contra hcon
    simp only [mem_iUnion, mem_union, mem_ofPred_eq, not_exists, not_or, not_le, one_mul,
      neg_one_mul] at hcon
    have : |∑ r ∈ Finset.range k, W r x| < t := by
      calc |∑ r ∈ Finset.range k, W r x| ≤ ∑ r ∈ Finset.range k, |W r x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ < ∑ _r ∈ Finset.range k, t / k :=
            Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 hk⟩ fun r hr ↦
              abs_lt.2 ⟨by linarith [(hcon r hr).2], (hcon r hr).1⟩
        _ = t := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    linarith
  have hexp : ∀ r ∈ Finset.range k, exp (-2 * (t / k) ^ 2 / J r) ≤
      exp (-2 * t ^ 2 / (k ^ 2 * n)) := fun r hr ↦ by
    obtain ⟨h0, hle⟩ := hJbd r hr
    have h0' : (0 : ℝ) < J r := by exact_mod_cast h0
    have hle' : (J r : ℝ) ≤ n := by exact_mod_cast hle
    refine exp_le_exp.2 ?_
    rw [div_pow, show -2 * (t ^ 2 / (k : ℝ) ^ 2) / J r = -(2 * t ^ 2 / ((k : ℝ) ^ 2 * J r)) by
      field_simp, show -2 * t ^ 2 / ((k : ℝ) ^ 2 * n) = -(2 * t ^ 2 / ((k : ℝ) ^ 2 * n)) by ring]
    exact neg_le_neg (div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr))
  calc μ.real {x | t ≤ |(blockCount b x w n : ℝ) - n / (b : ℝ) ^ k|}
      ≤ μ.real (⋃ r ∈ Finset.range k, ({x | t / k ≤ 1 * W r x} ∪ {x | t / k ≤ -1 * W r x})) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ r ∈ Finset.range k, μ.real ({x | t / k ≤ 1 * W r x} ∪ {x | t / k ≤ -1 * W r x}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Finset.range k, 2 * exp (-2 * t ^ 2 / (k ^ 2 * n)) := by
        refine Finset.sum_le_sum fun r hr ↦ (measureReal_union_le _ _).trans ?_
        have h1 := measureReal_le_sum_block_sub hb hk w r (J r) (t := t / k) (by positivity) 1
          (Or.inl rfl)
        have h2 := measureReal_le_sum_block_sub hb hk w r (J r) (t := t / k) (by positivity) (-1)
          (Or.inr rfl)
        have := hexp r hr
        exact (add_le_add h1 h2).trans (by linarith)
    _ = 2 * k * exp (-2 * t ^ 2 / (k ^ 2 * n)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Large deviations for digit blocks of integers**: at most a proportion
`2 k exp (-2 t² / (k² n))` of the integers `m < b ^ ℓ` contain the block `w` a number of times
deviating from `n / b ^ k` by at least `t`, where `n = ℓ + 1 - k` is the number of positions. -/
theorem card_filter_le_abs_sub_le (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b) {ℓ : ℕ}
    (hkℓ : k ≤ ℓ + 1 - k) {t : ℝ} (ht : 0 ≤ t) :
    (((Finset.range (b ^ ℓ)).filter fun m ↦
        t ≤ |(natBlockCount b ℓ m w : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|).card : ℝ) ≤
      (b : ℝ) ^ ℓ * (2 * k * exp (-2 * t ^ 2 / (k ^ 2 * (ℓ + 1 - k : ℕ)))) := by
  set G := (Finset.range (b ^ ℓ)).filter fun m ↦
    t ≤ |(natBlockCount b ℓ m w : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|
  set μ := volume.restrict (Ico (0 : ℝ) 1)
  have hbpos : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have h1 : μ.real {x | ⌊x * (b : ℝ) ^ ℓ⌋₊ ∈ G} = G.card * ((b : ℝ) ^ ℓ)⁻¹ := by
    rw [measureReal_def, volume_restrict_floor_mul_pow_mem hb ℓ G fun c hc ↦
      Finset.mem_range.1 (Finset.mem_filter.1 hc).1]
    simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
  have h2 : μ.real {x | ⌊x * (b : ℝ) ^ ℓ⌋₊ ∈ G} ≤
      μ.real {x | t ≤ |(blockCount b x w (ℓ + 1 - k) : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|} := by
    have e : μ.real {x | ⌊x * (b : ℝ) ^ ℓ⌋₊ ∈ G} =
        μ.real ({x | ⌊x * (b : ℝ) ^ ℓ⌋₊ ∈ G} ∩ Ico 0 1) := by
      simp only [measureReal_def, μ, Measure.restrict_apply' measurableSet_Ico, Set.inter_assoc,
        Set.inter_self]
    rw [e]
    refine measureReal_mono (fun x ⟨hx, hx'⟩ ↦ ?_) (measure_ne_top μ _)
    simp only [mem_ofPred_eq, G, Finset.mem_filter] at hx ⊢
    rw [blockCount_eq_natBlockCount hb hx' w (by omega)]
    exact hx.2
  have h3 := measureReal_le_abs_blockCount_sub hb hk w hkℓ ht
  rw [h1] at h2
  calc (G.card : ℝ) = G.card * ((b : ℝ) ^ ℓ)⁻¹ * (b : ℝ) ^ ℓ := by field_simp
    _ ≤ (2 * k * exp (-2 * t ^ 2 / (k ^ 2 * (ℓ + 1 - k : ℕ)))) * (b : ℝ) ^ ℓ :=
        mul_le_mul_of_nonneg_right (h2.trans h3) hbpos.le
    _ = _ := mul_comm _ _

end LargeDeviation

/-- The position (counted from `0`) at which the base-`b` expansion of `a t` starts in the
concatenation `a 0, a 1, …`. -/
def concatStart (b : ℕ) (a : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (Nat.log b (a i) + 1)

@[simp]
theorem concatStart_zero (b : ℕ) (a : ℕ → ℕ) : concatStart b a 0 = 0 := rfl

theorem concatStart_succ (b : ℕ) (a : ℕ → ℕ) (t : ℕ) :
    concatStart b a (t + 1) = concatStart b a t + (Nat.log b (a t) + 1) :=
  Finset.sum_range_succ _ _

theorem le_concatStart (b : ℕ) (a : ℕ → ℕ) (t : ℕ) : t ≤ concatStart b a t := by
  induction t with
  | zero => simp
  | succ t ih => rw [concatStart_succ]; omega

theorem concatStart_mono (b : ℕ) (a : ℕ → ℕ) : Monotone (concatStart b a) :=
  monotone_nat_of_le_succ fun t ↦ by rw [concatStart_succ]; omega

theorem exists_lt_concatStart_succ (b : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    ∃ t, n < concatStart b a (t + 1) :=
  ⟨n, Nat.lt_of_lt_of_le n.lt_succ_self (le_concatStart b a (n + 1))⟩

/-- The `n`-th digit (counted from `0`) of the concatenation of the base-`b` expansions of
`a 0, a 1, a 2, …`. -/
noncomputable def concatDigit (b : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  open Classical in
  let t := Nat.find (exists_lt_concatStart_succ b a n)
  a t / b ^ (concatStart b a (t + 1) - 1 - n) % b

/-- The real number `0.a₀ a₁ a₂ …` obtained by concatenating base-`b` expansions. -/
noncomputable def concatenation (b : ℕ) [NeZero b] (a : ℕ → ℕ) : ℝ :=
  ofDigits fun n ↦ Fin.ofNat b (concatDigit b a n)

section Concat

variable {a : ℕ → ℕ} {k : ℕ}

theorem concatDigit_lt (hb : 0 < b) (a : ℕ → ℕ) (n : ℕ) : concatDigit b a n < b :=
  Nat.mod_lt _ hb

theorem concatStart_find_le (b : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    concatStart b a (Nat.find (exists_lt_concatStart_succ b a n)) ≤ n := by
  rcases h : Nat.find (exists_lt_concatStart_succ b a n) with _ | t
  · simp
  · have := Nat.find_min (exists_lt_concatStart_succ b a n) (m := t) (by omega)
    omega

/-- Every position lies in the expansion of exactly one term. -/
theorem exists_concatStart_le_lt (b : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    ∃ t, concatStart b a t ≤ n ∧ n < concatStart b a (t + 1) :=
  ⟨_, concatStart_find_le b a n, Nat.find_spec (exists_lt_concatStart_succ b a n)⟩

/-- The digits of the concatenation at the positions occupied by the term `a t`. -/
theorem concatDigit_eq {n t : ℕ} (ht : concatStart b a t ≤ n) (hn : n < concatStart b a (t + 1)) :
    concatDigit b a n = a t / b ^ (concatStart b a (t + 1) - 1 - n) % b := by
  classical
  have h : Nat.find (exists_lt_concatStart_succ b a n) = t := by
    rw [Nat.find_eq_iff]
    refine ⟨hn, fun t' ht' ↦ ?_⟩
    have := concatStart_mono b a (show t' + 1 ≤ t by omega)
    omega
  simp only [concatDigit]
  rw [h]

/-- A block of `k` digits lying inside the expansion of the term `a t`, ending `s` digits
before its end, is the word `w` iff `⌊a t / b ^ s⌋ ≡ blockCode w [MOD b ^ k]`. -/
theorem forall_concatDigit_eq_iff (hb : 0 < b) (w : Fin k → Fin b) {t s : ℕ}
    (hs : s + k ≤ Nat.log b (a t) + 1) :
    (∀ j : Fin k, concatDigit b a (concatStart b a (t + 1) - k - s + j) = w j) ↔
      a t / b ^ s % b ^ k = blockCode w := by
  rw [← forall_div_pow_mod_eq_iff hb]
  have h := concatStart_succ b a t
  refine forall_congr' fun j ↦ ?_
  rw [concatDigit_eq (t := t) (by omega) (by omega),
    show concatStart b a (t + 1) - 1 - (concatStart b a (t + 1) - k - s + j) =
      s + (k - 1 - j) by omega, pow_add, Nat.div_div_eq_div_mul]

/-- The number of occurrences of the block `w` among the first `N` positions of the
concatenation. -/
noncomputable def concatOcc (b : ℕ) (a : ℕ → ℕ) (w : Fin k → Fin b) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun i ↦ ∀ j : Fin k, concatDigit b a (i + j) = w j).card

/-- The number of occurrences of `w` lying inside the expansion of a single term `a t`,
`t < T`. -/
def concatInternal (b : ℕ) (a : ℕ → ℕ) (w : Fin k → Fin b) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, natBlockCount b (Nat.log b (a t) + 1) (a t) w

theorem concatOcc_mono (w : Fin k → Fin b) : Monotone (concatOcc b a w) := fun _ _ h ↦
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem concatInternal_le_concatOcc (hk : 0 < k) (hb : 0 < b) (w : Fin k → Fin b) (T : ℕ) :
    concatInternal b a w T ≤ concatOcc b a w (concatStart b a T) := by
  rw [concatInternal]
  simp only [natBlockCount]
  rw [← Finset.card_sigma, concatOcc]
  refine Finset.card_le_card_of_injOn (fun p ↦ concatStart b a (p.1 + 1) - k - p.2) ?_ ?_
  · rintro ⟨t, s⟩ hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨ht, hs, hQ⟩ := hp
    have h1 := concatStart_mono b a (show t + 1 ≤ T by omega)
    have h2 := concatStart_succ b a t
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨by omega, (forall_concatDigit_eq_iff hb w (by omega)).2 hQ⟩
  · rintro ⟨t, s⟩ hp ⟨t', s'⟩ hp' heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hp hp' heq
    have h1 := concatStart_succ b a t
    have h2 := concatStart_succ b a t'
    have htt : t = t' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := concatStart_mono b a (show t + 1 ≤ t' by omega); omega
      · have := concatStart_mono b a (show t' + 1 ≤ t by omega); omega
    subst htt
    have : s = s' := by omega
    subst this
    rfl

theorem concatOcc_le (hk : 0 < k) (hb : 0 < b) (w : Fin k → Fin b) (T : ℕ) :
    concatOcc b a w (concatStart b a T) ≤ concatInternal b a w T + (k - 1) * T := by
  classical
  set σ := (Finset.range T).sigma fun t ↦
    (Finset.range (Nat.log b (a t) + 1 + 1 - k)).filter fun s ↦ a t / b ^ s % b ^ k = blockCode w
  set g : (Σ _ : ℕ, ℕ) → ℕ := fun p ↦ concatStart b a (p.1 + 1) - k - p.2
  set C := (Finset.range T).biUnion fun t ↦
    Finset.Ico (concatStart b a (t + 1) + 1 - k) (concatStart b a (t + 1))
  have hsub : ((Finset.range (concatStart b a T)).filter fun i ↦
      ∀ j : Fin k, concatDigit b a (i + j) = w j) ⊆ σ.image g ∪ C := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨t, ht1, ht2⟩ := exists_concatStart_le_lt b a i
    have htT : t < T := by
      by_contra h
      have := concatStart_mono b a (show T ≤ t by omega)
      omega
    have h1 := concatStart_succ b a t
    rw [Finset.mem_union]
    by_cases hik : i + k ≤ concatStart b a (t + 1)
    · left
      refine Finset.mem_image.2 ⟨⟨t, concatStart b a (t + 1) - k - i⟩, ?_, ?_⟩
      · simp only [σ, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
        refine ⟨htT, by omega, (forall_concatDigit_eq_iff hb w (by omega)).1 ?_⟩
        rw [show concatStart b a (t + 1) - k - (concatStart b a (t + 1) - k - i) = i by omega]
        exact hi.2
      · simp only [g]
        omega
    · right
      simp only [C, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico]
      exact ⟨t, htT, by omega, ht2⟩
  rw [concatOcc]
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (add_le_add ?_ ?_))
  · rw [concatInternal]
    simp only [natBlockCount]
    rw [← Finset.card_sigma]
    exact Finset.card_image_le
  · refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun t _ ↦
      (show _ ≤ k - 1 by rw [Nat.card_Ico]; omega)).trans ?_)
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

end Concat

/-- If `f` is monotone and `f (S T) / S T → c` along a sequence `S` of positions with
`S (T + 1) / S T → 1`, then `f N / N → c`. -/
theorem tendsto_div_of_tendsto_comp_div {f S : ℕ → ℕ} {c : ℝ} (hf : Monotone f) (hS : Monotone S)
    (hS0 : S 0 = 0) (hpos : ∀ T, 1 ≤ T → 0 < S T) (hunb : ∀ N, ∃ T, N < S (T + 1))
    (h1 : Tendsto (fun T ↦ (f (S T) : ℝ) / S T) atTop (𝓝 c))
    (h2 : Tendsto (fun T ↦ (S (T + 1) : ℝ) / S T) atTop (𝓝 1)) :
    Tendsto (fun N ↦ (f N : ℝ) / N) atTop (𝓝 c) := by
  classical
  set T : ℕ → ℕ := fun N ↦ Nat.find (hunb N)
  have hT1 : ∀ N, S (T N) ≤ N := fun N ↦ by
    rcases h : T N with _ | t
    · simp [hS0]
    · have := Nat.find_min (hunb N) (m := t) (by simp only [T] at h; omega)
      omega
  have hT2 : ∀ N, N < S (T N + 1) := fun N ↦ Nat.find_spec (hunb N)
  have hT : Tendsto T atTop atTop := by
    refine tendsto_atTop_atTop.2 fun M ↦ ⟨S (M + 1), fun N hN ↦ ?_⟩
    by_contra h
    have := hS (show T N + 1 ≤ M + 1 by omega)
    have := hT2 N
    omega
  have hup : Tendsto (fun N ↦ (f (S (T N + 1)) : ℝ) / S (T N + 1) * ((S (T N + 1) : ℝ) / S (T N)))
      atTop (𝓝 (c * 1)) :=
    (h1.comp ((tendsto_add_atTop_nat 1).comp hT)).mul (h2.comp hT)
  have hlow : Tendsto (fun N ↦ (f (S (T N)) : ℝ) / S (T N) / ((S (T N + 1) : ℝ) / S (T N)))
      atTop (𝓝 (c / 1)) :=
    (h1.comp hT).div (h2.comp hT) one_ne_zero
  rw [mul_one] at hup
  rw [div_one] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_ <;>
    filter_upwards [eventually_ge_atTop 1, hT.eventually (eventually_ge_atTop 1)] with N hN hTN
  · have hS0' : (0 : ℝ) < S (T N) := by exact_mod_cast hpos _ hTN
    have hS1 : (0 : ℝ) < S (T N + 1) := by exact_mod_cast hpos _ (Nat.le_add_left 1 _)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_div_div_cancel_right₀ hS0'.ne']
    exact div_le_div₀ (Nat.cast_nonneg _) (by exact_mod_cast hf (hT1 N)) hN0
      (by exact_mod_cast (hT2 N).le)
  · have hS0' : (0 : ℝ) < S (T N) := by exact_mod_cast hpos _ hTN
    have hS1 : (0 : ℝ) < S (T N + 1) := by exact_mod_cast hpos _ (Nat.le_add_left 1 _)
    rw [div_mul_div_cancel₀ hS1.ne']
    exact div_le_div₀ (Nat.cast_nonneg _) (by exact_mod_cast hf (hT2 N).le) hS0'
      (by exact_mod_cast hT1 N)

section Main

variable {a : ℕ → ℕ} {k : ℕ}

/-- The large deviation bound in the form used for the Copeland–Erdős theorem: for some
`ρ < log b`, the `ℓ`-digit integers in which the frequency of `w` is off by `ε` number at most
`C * exp (ρ * ℓ)`. -/
theorem exists_card_filter_le_exp (hb : 1 < b) (hk : 0 < k) (w : Fin k → Fin b) {ε : ℝ}
    (hε : 0 < ε) : ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < Real.log b ∧ ∀ ℓ : ℕ,
      (((Finset.range (b ^ ℓ)).filter fun m ↦ ε * (ℓ + 1 - k : ℕ) ≤
        |(natBlockCount b ℓ m w : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|).card : ℝ) ≤
        C * exp (ρ * ℓ) := by
  have hγ : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  set β : ℝ := 2 * ε ^ 2 / k ^ 2
  have hβ : 0 < β := by positivity
  set ρ := Real.log b - min β (Real.log b) / 2 with hρdef
  have hρ0 : 0 ≤ ρ := by have := min_le_right β (Real.log b); linarith
  have hρ : Real.log b - β ≤ ρ := by have := min_le_left β (Real.log b); linarith
  set C := 2 * k * exp (β * k) + (b : ℝ) ^ (2 * k)
  have hC : 0 ≤ C := by positivity
  refine ⟨C, ρ, hC, hρ0, by have := lt_min hβ hγ; linarith, fun ℓ ↦ ?_⟩
  have hbℓ : (b : ℝ) ^ ℓ = exp (Real.log b * ℓ) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
  have hexp1 : 1 ≤ exp (ρ * ℓ) := Real.one_le_exp (by positivity)
  by_cases hkℓ : k ≤ ℓ + 1 - k
  · have h := card_filter_le_abs_sub_le (b := b) (by omega) hk w hkℓ
      (t := ε * (ℓ + 1 - k : ℕ)) (by positivity)
    refine h.trans ?_
    set n : ℝ := ((ℓ + 1 - k : ℕ) : ℝ)
    have hn : (ℓ : ℝ) - k ≤ n := by
      simp only [n]
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    have hn0 : 0 < n := by simp only [n]; exact_mod_cast (show 0 < ℓ + 1 - k by omega)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have e1 : -2 * (ε * n) ^ 2 / (k ^ 2 * n) = -(β * n) := by
      simp only [β]
      field_simp
    rw [e1]
    have e2 : exp (Real.log b * ℓ) * (2 * k * exp (β * k - β * ℓ)) =
        2 * k * exp (β * k) * exp ((Real.log b - β) * ℓ) := by
      rw [show β * k - β * ℓ = β * k + -(β * ℓ) by ring, exp_add,
        show (Real.log b - β) * ℓ = Real.log b * ℓ + -(β * ℓ) by ring, exp_add]
      ring
    calc (b : ℝ) ^ ℓ * (2 * k * exp (-(β * n)))
        ≤ exp (Real.log b * ℓ) * (2 * k * exp (β * k - β * ℓ)) := by
          rw [hbℓ]
          gcongr
          nlinarith
      _ = 2 * k * exp (β * k) * exp ((Real.log b - β) * ℓ) := e2
      _ ≤ 2 * k * exp (β * k) * exp (ρ * ℓ) := by gcongr
      _ ≤ C * exp (ρ * ℓ) := by
          gcongr
          simp only [C]
          linarith [pow_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) (2 * k)]
  · have h1 : (((Finset.range (b ^ ℓ)).filter fun m ↦ ε * (ℓ + 1 - k : ℕ) ≤
        |(natBlockCount b ℓ m w : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|).card : ℝ) ≤
        (b : ℝ) ^ ℓ := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have h2 : (b : ℝ) ^ ℓ ≤ (b : ℝ) ^ (2 * k) :=
      pow_le_pow_right₀ (by exact_mod_cast hb.le) (by omega)
    have h3 : (b : ℝ) ^ (2 * k) ≤ C := by simp only [C]; linarith [exp_pos (β * k),
      (by positivity : (0 : ℝ) ≤ 2 * k * exp (β * k))]
    exact h1.trans (h2.trans (h3.trans (le_mul_of_one_le_right hC hexp1)))

theorem succ_le_of_strictMono (ha : StrictMono a) (ha0 : 0 < a 0) (t : ℕ) : t + 1 ≤ a t := by
  induction t with
  | zero => exact ha0
  | succ t ih => have := ha (show t < t + 1 by omega); omega

/-- Terms `a t` with `t ≥ b ^ L` have at least `L + 1` digits. -/
theorem mul_le_concatStart (hb : 1 < b) (ha : StrictMono a) (ha0 : 0 < a 0) (L T : ℕ) :
    (T - b ^ L) * (L + 1) ≤ concatStart b a T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [concatStart_succ]
    by_cases h : b ^ L ≤ T
    · have hL : L ≤ Nat.log b (a T) :=
        (Nat.le_log_iff_pow_le hb (by have := succ_le_of_strictMono ha ha0 T; omega)).2
          (by have := succ_le_of_strictMono ha ha0 T; omega)
      rw [show T + 1 - b ^ L = (T - b ^ L) + 1 by omega, add_mul, one_mul]
      omega
    · rw [show T + 1 - b ^ L = 0 by omega, zero_mul]
      exact Nat.zero_le _

/-- The number of digits of `a 0, …, a (T - 1)` grows faster than `T`. -/
theorem tendsto_succ_div_concatStart (hb : 1 < b) (ha : StrictMono a) (ha0 : 0 < a 0) :
    Tendsto (fun T : ℕ ↦ ((T : ℝ) + 1) / concatStart b a T) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun c hc ↦ Eventually.of_forall fun T ↦ hc.trans_le (by positivity), fun c hc ↦ ?_⟩
  obtain ⟨L, hL⟩ := exists_nat_gt (4 / c)
  have hL' : 4 / ((L : ℝ) + 1) < c := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at hL
    nlinarith
  filter_upwards [eventually_ge_atTop (2 * b ^ L + 1)] with T hT
  have h3 : ((T : ℝ) + 1) / 4 * (L + 1) ≤ concatStart b a T := by
    have : (((T - b ^ L) * (L + 1) : ℕ) : ℝ) ≤ concatStart b a T := by
      exact_mod_cast mul_le_concatStart hb ha ha0 L T
    push_cast at this
    rw [Nat.cast_sub (by omega)] at this
    have hT' : (2 : ℝ) * (b : ℝ) ^ L + 1 ≤ T := by exact_mod_cast hT
    push_cast at this
    nlinarith
  have hS : (0 : ℝ) < concatStart b a T := by
    refine lt_of_lt_of_le ?_ h3
    have : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
    positivity
  refine lt_of_le_of_lt ?_ hL'
  rw [div_le_div_iff₀ hS (by positivity)]
  nlinarith

/-- The density hypothesis of the Copeland–Erdős theorem implies `a T ^ θ ≤ T + 1`. -/
theorem eventually_rpow_le_succ (ha : StrictMono a)
    (hdens : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ ≤ ((Finset.range (N + 1)).filter fun i ↦ a i ≤ N).card) {θ : ℝ} (hθ : θ < 1) :
    ∀ᶠ T : ℕ in atTop, (a T : ℝ) ^ θ ≤ T + 1 := by
  filter_upwards [ha.tendsto_atTop.eventually (hdens θ hθ)] with T hT
  refine hT.trans ?_
  have : ((Finset.range (a T + 1)).filter fun i ↦ a i ≤ a T) ⊆ Finset.range (T + 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (ha.le_iff_le.1 hi.2)
  exact_mod_cast (Finset.card_le_card this).trans (Finset.card_range _).le

theorem tendsto_natLog_comp_atTop (hb : 1 < b) (ha : StrictMono a) :
    Tendsto (fun T ↦ Nat.log b (a T)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun M ↦ ⟨b ^ M, fun T hT ↦ Nat.le_log_of_pow_le hb ?_⟩
  exact hT.trans (ha.id_le T)

/-- `(x + 1) (x + 2) e^{-δ x} → 0`. -/
theorem tendsto_succ_mul_succ_mul_exp {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ ↦ (x + 1) * (x + 2) * exp (-(δ * x))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 δ hδ).const_mul 6
  rw [mul_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop 0] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Real.rpow_two, neg_mul, ← mul_assoc]
    have : (x + 1) * (x + 2) ≤ 6 * x ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (exp_pos _).le

/-- The terms `a t`, `t ≤ T`, in which the frequency of `w` is off by at least `ε`. -/
noncomputable def concatBad (b : ℕ) (a : ℕ → ℕ) (w : Fin k → Fin b) (ε : ℝ) (T : ℕ) :
    Finset ℕ :=
  (Finset.range (T + 1)).filter fun t ↦
    ε * (Nat.log b (a t) + 1 + 1 - k : ℕ) ≤ |(natBlockCount b (Nat.log b (a t) + 1) (a t) w : ℝ) -
      (Nat.log b (a t) + 1 + 1 - k : ℕ) / (b : ℝ) ^ k|

/-- **The few-bad-terms criterion** (Copeland–Erdős; Pollack–Vandehey): the internal occurrences
of `w` have frequency `b⁻ᵏ` as soon as, for every `ε > 0`, the terms in which the frequency of `w`
is off by `ε` are negligible. -/
theorem tendsto_concatInternal_div_of_concatBad (hb : 1 < b) (hk : 0 < k) (w : Fin k → Fin b)
    (ha : StrictMono a) (ha0 : 0 < a 0) (hbad : ∀ ε : ℝ, 0 < ε → Tendsto (fun T ↦
      ((Nat.log b (a T) : ℝ) + 1) * (concatBad b a w ε T).card / concatStart b a (T + 1)) atTop
        (𝓝 0)) :
    Tendsto (fun T ↦ (concatInternal b a w T : ℝ) / concatStart b a T) atTop
      (𝓝 ((b : ℝ) ^ k)⁻¹) := by
  classical
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  rw [Metric.tendsto_nhds]
  intro η hη
  set ε := η / 4 with hε_def
  have hε : 0 < ε := by positivity
  set c : ℝ := ((b : ℝ) ^ k)⁻¹
  have hbk : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hb.le)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ hbk
  have E2 : ∀ᶠ T : ℕ in atTop, k * ((T : ℝ) + 1) / concatStart b a (T + 1) < ε := by
    have h := ((tendsto_succ_div_concatStart hb ha ha0).comp (tendsto_add_atTop_nat 1)).const_mul
      (k : ℝ)
    rw [mul_zero] at h
    filter_upwards [h.eventually (gt_mem_nhds hε)] with T hT
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hT
    refine lt_of_le_of_lt ?_ hT
    rw [mul_div_assoc]
    gcongr
    linarith
  filter_upwards [E2, (hbad ε hε).eventually (gt_mem_nhds hε)] with T h2 h3
  -- notation
  set S := concatStart b a (T + 1)
  set m := Nat.log b (a T)
  set L := m + 1
  set len : ℕ → ℕ := fun t ↦ Nat.log b (a t) + 1
  set I : ℕ → ℕ := fun t ↦ natBlockCount b (len t) (a t) w
  set n : ℕ → ℕ := fun t ↦ len t + 1 - k
  set P : ℕ → Prop := fun t ↦ ε * (n t : ℝ) ≤ |(I t : ℝ) - (n t : ℝ) / (b : ℝ) ^ k|
  set B := (Finset.range (T + 1)).filter P
  have hBdef : B = concatBad b a w ε T := rfl
  have hlenL : ∀ t ∈ Finset.range (T + 1), len t ≤ L := fun t ht ↦ by
    have := Nat.log_mono_right (b := b) (ha.monotone (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)))
    simp only [len, L, m]; omega
  have hS : (S : ℝ) = ∑ t ∈ Finset.range (T + 1), (len t : ℝ) := by
    simp only [S, concatStart, len]; push_cast; rfl
  have hInt : (concatInternal b a w (T + 1) : ℝ) = ∑ t ∈ Finset.range (T + 1), (I t : ℝ) := by
    simp only [concatInternal, I, len]; push_cast; rfl
  have hSpos : (0 : ℝ) < S := by
    have := le_concatStart b a (T + 1)
    exact_mod_cast (show 0 < S by omega)
  -- the main inequality
  have hmain : |(concatInternal b a w (T + 1) : ℝ) - S * c| ≤
      ε * S + L * B.card + k * ((T : ℝ) + 1) := by
    have hterm : ∀ t ∈ Finset.range (T + 1), |(I t : ℝ) - (n t : ℝ) * c| ≤
        ε * n t + (if P t then (L : ℝ) else 0) := fun t ht ↦ by
      have hI : (I t : ℝ) ≤ n t := by exact_mod_cast natBlockCount_le b (len t) (a t) w
      have hnL : (n t : ℝ) ≤ L := by
        have := hlenL t ht
        exact_mod_cast (show n t ≤ L by simp only [n]; omega)
      have hn0 : (0 : ℝ) ≤ n t := Nat.cast_nonneg _
      have hI0 : (0 : ℝ) ≤ I t := Nat.cast_nonneg _
      have hnc : (n t : ℝ) * c ≤ n t := mul_le_of_le_one_right hn0 hc1
      have hnc0 : (0 : ℝ) ≤ n t * c := by positivity
      by_cases hP : P t
      · simp only [hP, ↓reduceIte]
        have : |(I t : ℝ) - (n t : ℝ) * c| ≤ n t := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
        nlinarith
      · simp only [hP, ↓reduceIte, add_zero]
        simp only [P, not_le, div_eq_mul_inv] at hP
        exact hP.le
    have hsum1 : |∑ t ∈ Finset.range (T + 1), ((I t : ℝ) - (n t : ℝ) * c)| ≤
        ε * S + L * B.card := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm (B.card : ℝ)]
      gcongr
      rw [hS]
      exact Finset.sum_le_sum fun t _ ↦ by exact_mod_cast (show n t ≤ len t by simp only [n]; omega)
    have hsum2 : |∑ t ∈ Finset.range (T + 1), ((n t : ℝ) - len t) * c| ≤ k * ((T : ℝ) + 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ t ∈ Finset.range (T + 1), |((n t : ℝ) - len t) * c|
          ≤ ∑ _t ∈ Finset.range (T + 1), (k : ℝ) := Finset.sum_le_sum fun t _ ↦ by
            rw [abs_mul, abs_of_pos hc0]
            have h1 : (len t : ℝ) ≤ n t + k := by
              exact_mod_cast (show len t ≤ n t + k by simp only [n]; omega)
            have h2 : (n t : ℝ) ≤ len t + k := by
              exact_mod_cast (show n t ≤ len t + k by simp only [n]; omega)
            have : |(n t : ℝ) - len t| ≤ k := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
            nlinarith [abs_nonneg ((n t : ℝ) - len t)]
        _ = k * ((T : ℝ) + 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have : (concatInternal b a w (T + 1) : ℝ) - S * c =
        ∑ t ∈ Finset.range (T + 1), ((I t : ℝ) - (n t : ℝ) * c) +
          ∑ t ∈ Finset.range (T + 1), ((n t : ℝ) - len t) * c := by
      rw [hInt, hS, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    rw [this]
    exact (abs_add_le _ _).trans (by linarith)
  have hbadS : L * B.card / S ≤ ε := by
    rw [hBdef]
    have : (L : ℝ) = (m : ℝ) + 1 := by simp only [L]; push_cast; ring
    rw [this]
    exact h3.le
  -- conclusion
  rw [Real.dist_eq]
  change |(concatInternal b a w (T + 1) : ℝ) / S - c| < η
  have e : (concatInternal b a w (T + 1) : ℝ) / S - c =
      ((concatInternal b a w (T + 1) : ℝ) - S * c) / S := by field_simp
  rw [e]
  have : |(concatInternal b a w (T + 1) : ℝ) - S * c| / S ≤ ε + L * B.card / S +
      k * ((T : ℝ) + 1) / S := by
    rw [div_le_iff₀ hSpos]
    calc _ ≤ ε * S + L * B.card + k * ((T : ℝ) + 1) := hmain
      _ = _ := by field_simp
  calc |((concatInternal b a w (T + 1) : ℝ) - S * c) / S|
      = |(concatInternal b a w (T + 1) : ℝ) - S * c| / S := by rw [abs_div, abs_of_pos hSpos]
    _ ≤ ε + L * B.card / S + k * ((T : ℝ) + 1) / S := this
    _ < ε + ε + ε + ε := by linarith
    _ = η := by simp only [ε]; ring

/-- Under the density hypothesis of the Copeland–Erdős theorem, the terms in which the frequency
of `w` is off by `ε` are negligible: by the large deviation bound there are at most
`C exp (ρ ℓ)`, `ρ < log b`, of them with `ℓ` digits. -/
theorem tendsto_concatBad_of_dens (hb : 1 < b) (hk : 0 < k) (w : Fin k → Fin b)
    (ha : StrictMono a) (ha0 : 0 < a 0) (hdens : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ ≤ ((Finset.range (N + 1)).filter fun i ↦ a i ≤ N).card) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T ↦ ((Nat.log b (a T) : ℝ) + 1) * (concatBad b a w ε T).card /
      concatStart b a (T + 1)) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro η' hη'
  obtain ⟨C, ρ, hC, hρ0, hργ, hbad⟩ := exists_card_filter_le_exp hb hk w hε
  set γ := Real.log b
  have hγ : 0 < γ := Real.log_pos (by exact_mod_cast hb)
  set θ := (ρ / γ + 1) / 2
  have hθ1 : θ < 1 := by
    have : ρ / γ < 1 := (div_lt_one hγ).2 hργ
    simp only [θ]; linarith
  have hθ0 : 0 ≤ θ := by simp only [θ]; positivity
  set δ := θ * γ - ρ
  have hδ : 0 < δ := by
    have : θ * γ = (ρ + γ) / 2 := by simp only [θ]; field_simp
    simp only [δ]; linarith
  have hη : 0 < η' / 2 := by positivity
  have E1 := eventually_rpow_le_succ ha hdens hθ1
  have E3 : ∀ᶠ T : ℕ in atTop, ((Nat.log b (a T) : ℝ) + 1) * ((Nat.log b (a T) : ℝ) + 2) *
      exp (-(δ * Nat.log b (a T))) < (η' / 2) / (C * exp ρ + 1) :=
    ((tendsto_succ_mul_succ_mul_exp hδ).comp (tendsto_natCast_atTop_atTop.comp
      (tendsto_natLog_comp_atTop hb ha))).eventually (gt_mem_nhds (by positivity))
  filter_upwards [E1, E3] with T h1 h3
  set S := concatStart b a (T + 1)
  set m := Nat.log b (a T)
  set L := m + 1
  set len : ℕ → ℕ := fun t ↦ Nat.log b (a t) + 1
  set B := concatBad b a w ε T
  have hlenL : ∀ t ∈ Finset.range (T + 1), len t ≤ L := fun t ht ↦ by
    have := Nat.log_mono_right (b := b) (ha.monotone (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)))
    simp only [len, L, m]; omega
  have hSpos : (0 : ℝ) < S := by
    have := le_concatStart b a (T + 1)
    exact_mod_cast (show 0 < S by omega)
  -- the number of exceptional terms
  have hB : (B.card : ℝ) ≤ (L + 1) * (C * exp (ρ * L)) := by
    have hinj : (B.card : ℝ) ≤ ∑ ℓ ∈ Finset.range (L + 1),
        (((Finset.range (b ^ ℓ)).filter fun m ↦ ε * (ℓ + 1 - k : ℕ) ≤
          |(natBlockCount b ℓ m w : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|).card : ℝ) := by
      rw [← Nat.cast_sum, ← Finset.card_sigma]
      refine Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun t ↦ ⟨len t, a t⟩) ?_ ?_)
      · intro t ht
        simp only [B, concatBad, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht
        simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
          Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
        refine ⟨Nat.lt_succ_of_le (hlenL t (Finset.mem_range.2 ht.1)),
          Nat.lt_pow_succ_log_self hb _, ht.2⟩
      · intro t _ t' _ e
        simp only [Sigma.mk.injEq] at e
        exact ha.injective (eq_of_heq e.2)
    refine hinj.trans ((Finset.sum_le_sum fun ℓ _ ↦ hbad ℓ).trans ?_)
    calc ∑ ℓ ∈ Finset.range (L + 1), C * exp (ρ * ℓ)
        ≤ ∑ _ℓ ∈ Finset.range (L + 1), C * exp (ρ * L) := by
          refine Finset.sum_le_sum fun ℓ hℓ ↦ ?_
          have : (ℓ : ℝ) ≤ L := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
          gcongr
      _ = (L + 1) * (C * exp (ρ * L)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hexpS : exp (θ * γ * m) ≤ S := by
    have hbm : ((b : ℝ) ^ m) ≤ a T := by
      have := ha0.trans_le (ha.monotone (Nat.zero_le T))
      exact_mod_cast Nat.pow_log_le_self b (by omega)
    have e : ((b : ℝ) ^ m) ^ θ = exp (θ * γ * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        Real.rpow_def_of_pos (by exact_mod_cast (show 0 < b by omega))]
      change exp (γ * ((m : ℝ) * θ)) = exp (θ * γ * m)
      ring_nf
    rw [← e]
    refine (Real.rpow_le_rpow (by positivity) hbm hθ0).trans (h1.trans ?_)
    have := le_concatStart b a (T + 1)
    exact_mod_cast this
  have hL : (L : ℝ) = m + 1 := by simp only [L]; push_cast; ring
  have hX : (L : ℝ) * B.card ≤ C * exp ρ * (((m : ℝ) + 1) * ((m : ℝ) + 2) * exp (-(δ * m))) *
      exp (θ * γ * m) := by
    calc (L : ℝ) * B.card ≤ L * ((L + 1) * (C * exp (ρ * L))) := by gcongr
      _ = C * exp ρ * (((m : ℝ) + 1) * ((m : ℝ) + 2) * exp (-(δ * m))) * exp (θ * γ * m) := by
        rw [hL, show ρ * ((m : ℝ) + 1) = ρ + -(δ * m) + θ * γ * m by simp only [δ]; ring,
          exp_add, exp_add]
        ring
  have hg : C * exp ρ * (((m : ℝ) + 1) * ((m : ℝ) + 2) * exp (-(δ * m))) ≤ η' / 2 := by
    have hpos : 0 < C * exp ρ + 1 := by positivity
    have := (lt_div_iff₀ hpos).1 h3
    nlinarith [exp_pos (-(δ * m)), (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) *
      exp (-(δ * m)))]
  have hle : (L : ℝ) * B.card / S ≤ η' / 2 := by
    rw [div_le_iff₀ hSpos]
    exact hX.trans (mul_le_mul hg hexpS (by positivity) hη.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), ← hL]
  linarith

end Main

/-- **The few-bad-terms criterion** for concatenations (Copeland–Erdős, Pollack–Vandehey): the
concatenation of an increasing sequence `a` with `log a T = O(T)` is normal as soon as, for every
block `w` and every `ε > 0`, the terms `a t` in which the frequency of `w` is off by `ε` are
negligible. -/
theorem isNormalSeq_concatDigit_of_concatBad (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (ha0 : 0 < a 0) {c : ℕ} (hlog : ∀ᶠ T in atTop, Nat.log b (a T) ≤ c * (T + 1))
    (hbad : ∀ k, 0 < k → ∀ (w : Fin k → Fin b) (ε : ℝ), 0 < ε → Tendsto (fun T ↦
      ((Nat.log b (a T) : ℝ) + 1) * (concatBad b a w ε T).card / concatStart b a (T + 1)) atTop
        (𝓝 0)) :
    IsNormalSeq b (concatDigit b a) := by
  intro k w
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : ∀ N, ((Finset.range N).filter fun i ↦
        ∀ j : Fin 0, concatDigit b a (i + j) = w j).card = N := fun N ↦ by simp
    simp only [this, pow_zero, inv_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [div_self (Nat.cast_ne_zero.2 hN.ne')]
  have hb1 : 1 < b := by omega
  change Tendsto (fun N : ℕ ↦ (concatOcc b a w N : ℝ) / N) atTop (𝓝 ((b : ℝ) ^ k)⁻¹)
  refine tendsto_div_of_tendsto_comp_div (concatOcc_mono w) (concatStart_mono b a)
    (concatStart_zero b a) (fun T hT ↦ (show 0 < T by omega).trans_le (le_concatStart b a T))
    (exists_lt_concatStart_succ b a) ?_ ?_
  · -- occurrences straddling two terms are negligible
    have hI := tendsto_concatInternal_div_of_concatBad hb1 hk w ha ha0 (hbad k hk w)
    have hT := (tendsto_succ_div_concatStart hb1 ha ha0).const_mul (k : ℝ)
    rw [mul_zero] at hT
    have hup := hI.add hT
    rw [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hI hup ?_ ?_ <;>
      filter_upwards [eventually_ge_atTop 1] with T hT1
    · have hS : (0 : ℝ) < concatStart b a T := by
        exact_mod_cast (show 0 < T by omega).trans_le (le_concatStart b a T)
      have hle := concatInternal_le_concatOcc (a := a) hk (by omega) w T
      exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hS.le
    · have hS : (0 : ℝ) < concatStart b a T := by
        exact_mod_cast (show 0 < T by omega).trans_le (le_concatStart b a T)
      rw [mul_div_assoc', ← add_div]
      refine div_le_div_of_nonneg_right ?_ hS.le
      have h := concatOcc_le hk (by omega) w (a := a) T
      have : (((k - 1) * T : ℕ) : ℝ) ≤ k * ((T : ℝ) + 1) := by
        push_cast
        rw [Nat.cast_sub (by omega)]
        push_cast
        nlinarith
      calc (concatOcc b a w (concatStart b a T) : ℝ)
          ≤ (concatInternal b a w T + (k - 1) * T : ℕ) := by exact_mod_cast h
        _ ≤ _ := by push_cast at this ⊢; linarith
  · -- the length of a single term is negligible
    have hT := (tendsto_succ_div_concatStart hb1 ha ha0).const_mul ((c : ℝ) + 1)
    rw [mul_zero] at hT
    have hup := hT.const_add 1
    rw [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with T hT1
      have hS : (0 : ℝ) < concatStart b a T := by
        exact_mod_cast (show 0 < T by omega).trans_le (le_concatStart b a T)
      rw [le_div_iff₀ hS, one_mul]
      exact_mod_cast concatStart_mono b a (Nat.le_succ T)
    · filter_upwards [eventually_ge_atTop 1, hlog] with T hT1 hD
      have hS : (0 : ℝ) < concatStart b a T := by
        exact_mod_cast (show 0 < T by omega).trans_le (le_concatStart b a T)
      have hS1 : (concatStart b a (T + 1) : ℝ) ≤ concatStart b a T + (c + 1) * ((T : ℝ) + 1) := by
        have := concatStart_succ b a T
        have : concatStart b a (T + 1) ≤ concatStart b a T + (c + 1) * (T + 1) := by
          rw [add_mul, one_mul]; omega
        exact_mod_cast this
      rw [div_le_iff₀ hS, add_mul, one_mul, mul_div_assoc', div_mul_cancel₀ _ hS.ne']
      exact hS1

/-- **Copeland–Erdős theorem** for digit sequences. -/
theorem isNormalSeq_concatDigit (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a) (ha0 : 0 < a 0)
    (hdens : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ ≤ ((Finset.range (N + 1)).filter fun i ↦ a i ≤ N).card) :
    IsNormalSeq b (concatDigit b a) := by
  have hb1 : 1 < b := by omega
  refine isNormalSeq_concatDigit_of_concatBad hb ha ha0 (c := 2) ?_ fun k hk w ε hε ↦
    tendsto_concatBad_of_dens hb1 hk w ha ha0 hdens hε
  have hθ : ((2 : ℕ) : ℝ)⁻¹ < 1 := by norm_num
  filter_upwards [eventually_rpow_le_succ ha hdens hθ] with T hD
  -- `a T ≤ (T + 1) ^ 2`, so `a T` has at most `2 (T + 1)` digits
  have hsq : a T ≤ (T + 1) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hD 2
    rw [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) two_ne_zero] at this
    exact_mod_cast this
  have hlog : Nat.log b (a T) < 2 * (T + 1) := by
    refine Nat.log_lt_of_lt_pow (by have := ha0.trans_le (ha.monotone (Nat.zero_le T)); omega)
      (hsq.trans_lt ?_)
    rw [pow_mul']
    exact Nat.pow_lt_pow_left (Nat.lt_pow_self hb1) two_ne_zero
  omega

/-- **Copeland–Erdős theorem**: if `a` is an increasing sequence of positive integers having at
least `N ^ θ` terms below `N` for every `θ < 1` and all large `N`, then `0.a₀ a₁ a₂ …` is normal
in base `b`. -/
theorem isNormalIn_concatenation [NeZero b] (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (ha0 : 0 < a 0) (hdens : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ ≤ ((Finset.range (N + 1)).filter fun i ↦ a i ≤ N).card) :
    IsNormalIn b (concatenation b a) := by
  refine isNormalIn_ofDigits hb ?_
  convert isNormalSeq_concatDigit hb ha ha0 hdens using 2 with n
  simp [Nat.mod_eq_of_lt (concatDigit_lt (b := b) (by omega) a n)]

/-- For every `θ < 1`, there are at least `N ^ θ` primes `≤ N` for all large `N`. -/
theorem eventually_rpow_le_primeCounting {θ : ℝ} (hθ : θ < 1) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ θ ≤ Nat.primeCounting N := by
  -- Chebyshev's bound `π N ≥ N log 2 / log N`, and `log N = o(N ^ (1 - θ))`
  have hlog := (isLittleO_log_rpow_atTop (show 0 < 1 - θ by linarith)).bound
    (show (0 : ℝ) < Real.log 2 by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlog, eventually_ge_atTop 4]
    with N hN h4
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  refine le_trans ?_ (Chebyshev.pi_ge_of_four_le h4)
  rw [le_div_iff₀ hlogN]
  simp only [Real.norm_eq_abs, abs_of_pos hlogN, abs_of_pos (Real.rpow_pos_of_pos hN0 _)] at hN
  calc (N : ℝ) ^ θ * Real.log N ≤ (N : ℝ) ^ θ * (Real.log 2 * (N : ℝ) ^ (1 - θ)) := by gcongr
    _ = N * Real.log 2 := by
        rw [mul_left_comm, ← Real.rpow_add hN0, add_sub_cancel, Real.rpow_one, mul_comm]

/-- The base-`b` *Copeland–Erdős constant* `0.2 3 5 7 11 13 …`, concatenating the primes. -/
noncomputable def copelandErdos (b : ℕ) [NeZero b] : ℝ :=
  concatenation b (Nat.nth Nat.Prime)

/-- **Copeland–Erdős**: the concatenation of the primes is normal in every base `b ≥ 2`. -/
theorem isNormalIn_copelandErdos [NeZero b] (hb : 2 ≤ b) : IsNormalIn b (copelandErdos b) := by
  refine isNormalIn_concatenation hb (Nat.nth_strictMono Nat.infinite_setOfPred_prime)
    (by rw [Nat.nth_prime_zero_eq_two]; norm_num) fun θ hθ ↦ ?_
  filter_upwards [eventually_rpow_le_primeCounting hθ] with N hN
  refine hN.trans (le_of_eq ?_)
  -- the primes `≤ N` are the `nth Prime i` with `i < π N`
  have : ((Finset.range (N + 1)).filter fun i ↦ Nat.nth Nat.Prime i ≤ N) =
      Finset.range (Nat.primeCounting N) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Nat.primeCounting, Nat.primeCounting']
    rw [Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime]
    have hid : i ≤ Nat.nth (fun p ↦ Nat.Prime p) i :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le i
    have he : Nat.nth Nat.Prime i = Nat.nth (fun p ↦ Nat.Prime p) i := rfl
    omega
  rw [this, Finset.card_range]

/-- The decimal Copeland–Erdős constant `0.235711131719…` is normal in base ten. -/
theorem isNormalIn_ten_copelandErdos : IsNormalIn 10 (copelandErdos 10) :=
  isNormalIn_copelandErdos (by norm_num)

end Real
