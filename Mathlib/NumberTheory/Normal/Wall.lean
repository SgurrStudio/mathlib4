/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Borel

/-!
# Wall's theorem: normality and equidistribution

A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every interval `[a, c) ⊆ [0, 1]`
the proportion of `n < N` with `Int.fract (u n) ∈ [a, c)` tends to `c - a`.

We prove **Wall's theorem** (D. D. Wall, 1949): a real number `x` is normal in base `b ≥ 2` if and
only if the sequence `(x * b ^ n)` is equidistributed modulo one. Combined with Borel's normal
number theorem this shows that for almost every `x` the sequence `(x * b ^ n)` is equidistributed
modulo one.

## Main definitions

* `IsEquidistributedModOne u`: the sequence `u` is equidistributed modulo one.

## Main statements

* `Real.blockCount_eq_card_floor_fract`: the block `w` occurs at position `i` of the base-`b`
  expansion of `x` iff `Int.fract (x * b ^ i)` lies in the `b`-adic interval coded by `w`.
* `Real.isNormalIn_iff_isEquidistributedModOne`: Wall's theorem.
* `Real.ae_isEquidistributedModOne_mul_pow`: for almost every `x`, `(x * b ^ n)` is
  equidistributed modulo one.

## References

* [D. D. Wall, *Normal numbers*, PhD thesis, UC Berkeley, 1949][Wall1949]
* [L. Kuipers, H. Niederreiter, *Uniform distribution of sequences*][KuipersNiederreiter1974]
-/

@[expose] public section

open Filter Topology MeasureTheory Set

/-- A real sequence `u` is *equidistributed modulo one* if for every `0 ≤ a ≤ c ≤ 1` the
proportion of indices `n < N` such that `Int.fract (u n) ∈ [a, c)` tends to `c - a`. -/
def IsEquidistributedModOne (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 →
    Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c).card : ℝ) / N)
      atTop (𝓝 (c - a))

namespace Real

variable {b k : ℕ} {x : ℝ}

/-- The block `w` occurs at position `i` of the base-`b` expansion of `x` iff
`⌊Int.fract (x * b ^ i) * b ^ k⌋₊` is the integer whose base-`b` digits are `w`. -/
theorem blockCount_eq_card_floor_fract (hb : 0 < b) (w : Fin k → Fin b) (N : ℕ) :
    blockCount b x w N = ((Finset.range N).filter fun i ↦
      ⌊Int.fract (x * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ = blockCode w).card := by
  classical
  rw [blockCount]
  congr 1
  refine Finset.filter_congr fun i _ ↦ ?_
  have h := forall_digit_eq_iff_digit_pow (x := x) hb w i 0
  simp only [zero_mul, add_zero] at h
  have hlt : ⌊Int.fract (x * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ < b ^ k := by
    rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) (by positivity))]
    push_cast
    exact mul_lt_of_lt_one_left (by positivity) (Int.fract_lt_one _)
  rw [h, ← digit_fract, digit_eq_floor_mod (Int.fract_nonneg _), zero_add, pow_one, Nat.cast_pow,
    Nat.mod_eq_of_lt hlt]

theorem exists_blockCode_eq (j : Fin (b ^ k)) : ∃ w : Fin k → Fin b, blockCode w = j :=
  ⟨finFunctionFinEquiv.symm j ∘ Fin.rev, by
    simp [blockCode, Function.comp_assoc, Fin.rev_involutive.comp_self]⟩

theorem floor_mul_eq_iff_mem_Ico {y B : ℝ} (hy : 0 ≤ y) (hB : 0 < B) (j : ℕ) :
    ⌊y * B⌋₊ = j ↔ y ∈ Ico ((j : ℝ) / B) (((j : ℝ) + 1) / B) := by
  rw [Nat.floor_eq_iff (mul_nonneg hy hB.le), mem_Ico, div_le_iff₀ hB, lt_div_iff₀ hB]

/-- `x` is normal in base `b` iff each `b`-adic interval of length `b⁻ᵏ` is visited by
`Int.fract (x * b ^ n)` with frequency `b⁻ᵏ`. -/
theorem isNormalIn_iff_tendsto_card_floor (hb : 0 < b) :
    IsNormalIn b x ↔ ∀ k j, j < b ^ k → Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun n ↦
      ⌊Int.fract (x * (b : ℝ) ^ n) * (b : ℝ) ^ k⌋₊ = j).card : ℝ) / N) atTop
        (𝓝 ((b : ℝ) ^ k)⁻¹) := by
  constructor
  · intro h k j hj
    obtain ⟨w, hw⟩ := exists_blockCode_eq (b := b) (k := k) ⟨j, hj⟩
    have := h k w
    simp_rw [blockCount_eq_card_floor_fract hb, hw] at this
    exact this
  · intro h k w
    simp_rw [blockCount_eq_card_floor_fract hb]
    exact h k _ (blockCode w).isLt

/-- **Wall's theorem**: `x` is normal in base `b ≥ 2` iff `(x * b ^ n)` is equidistributed modulo
one. -/
theorem isNormalIn_iff_isEquidistributedModOne (hb : 2 ≤ b) :
    IsNormalIn b x ↔ IsEquidistributedModOne fun n ↦ x * (b : ℝ) ^ n := by
  have hb0 : 0 < b := by omega
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  rw [isNormalIn_iff_tendsto_card_floor hb0]
  set y : ℕ → ℝ := fun n ↦ Int.fract (x * (b : ℝ) ^ n)
  have hy0 : ∀ n, 0 ≤ y n := fun n ↦ Int.fract_nonneg _
  constructor
  · intro h a c ha hac hc1
    -- the number of `n < N` whose `b`-adic interval of level `k` has index in `t`
    have hsum : ∀ (k : ℕ) (t : Finset ℕ), (∀ j ∈ t, j < b ^ k) →
        Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun n ↦
          ⌊y n * (b : ℝ) ^ k⌋₊ ∈ t).card : ℝ) / N) atTop
          (𝓝 ((t.card : ℝ) * ((b : ℝ) ^ k)⁻¹)) := by
      intro k t ht
      have := tendsto_finsetSum t fun j hj ↦ h k j (ht j hj)
      rw [Finset.sum_const, nsmul_eq_mul] at this
      refine this.congr fun N ↦ ?_
      rw [← Finset.sum_div, ← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]
    have hlB : ∀ ε > 0, ∃ k : ℕ, 2 / ((b : ℝ) ^ k) < ε := by
      intro ε hε
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 / ε) hb1
      exact ⟨k, by rwa [div_lt_iff₀ (by positivity), mul_comm, ← div_lt_iff₀ hε]⟩
    rw [tendsto_order]
    constructor
    · intro ℓ hℓ
      obtain ⟨k, hk⟩ := hlB (c - a - ℓ) (by linarith)
      set B : ℝ := (b : ℝ) ^ k with hB_def
      have hB : 0 < B := by positivity
      set lo := ⌈a * B⌉₊
      set hi := ⌊c * B⌋₊
      have hhi : hi ≤ b ^ k := by
        refine Nat.le_of_lt_succ ((Nat.floor_lt (mul_nonneg (ha.trans hac) hB.le)).2 ?_)
        push_cast
        nlinarith
      have hlim := hsum k (Finset.Ico lo hi) fun j hj ↦ (Finset.mem_Ico.1 hj).2.trans_le hhi
      have hval : ℓ < ((Finset.Ico lo hi).card : ℝ) * B⁻¹ := by
        rw [Nat.card_Ico]
        have h1 : c * B - 1 < hi := Nat.sub_one_lt_floor _
        have h2 : (lo : ℝ) < a * B + 1 := Nat.ceil_lt_add_one (mul_nonneg ha hB.le)
        have hsub : (hi : ℝ) - lo ≤ ((hi - lo : ℕ) : ℝ) := by
          rcases le_total lo hi with h | h
          · rw [Nat.cast_sub h]
          · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_nonpos]
            exact_mod_cast h
        have : c - a - 2 / B ≤ ((hi - lo : ℕ) : ℝ) * B⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hB, sub_mul, sub_mul, div_mul_cancel₀ _ hB.ne']
          linarith
        linarith
      filter_upwards [hlim.eventually (lt_mem_nhds hval)] with N hN
      refine hN.trans_le (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N))
      refine Nat.cast_le.2 (Finset.card_le_card fun n hn ↦ ?_)
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
      refine ⟨hn.1, ?_, ?_⟩
      · have h1 : (lo : ℝ) ≤ (⌊y n * B⌋₊ : ℝ) := Nat.cast_le.2 hn.2.1
        have h2 : a * B ≤ lo := Nat.le_ceil _
        have h3 : (⌊y n * B⌋₊ : ℝ) ≤ y n * B := Nat.floor_le (mul_nonneg (hy0 n) hB.le)
        exact le_of_mul_le_mul_right (by linarith) hB
      · have h1 : ((⌊y n * B⌋₊ + 1 : ℕ) : ℝ) ≤ hi := Nat.cast_le.2 hn.2.2
        push_cast at h1
        have h2 : (hi : ℝ) ≤ c * B := Nat.floor_le (mul_nonneg (ha.trans hac) hB.le)
        have h3 : y n * B < ⌊y n * B⌋₊ + 1 := Nat.lt_floor_add_one _
        exact lt_of_mul_lt_mul_right (by linarith) hB.le
    · intro u hu
      obtain ⟨k, hk⟩ := hlB (u - (c - a)) (by linarith)
      set B : ℝ := (b : ℝ) ^ k with hB_def
      have hB : 0 < B := by positivity
      set lo := ⌊a * B⌋₊
      set hi := ⌈c * B⌉₊
      have hhi : hi ≤ b ^ k := by
        rw [Nat.ceil_le]
        push_cast
        nlinarith
      have hlohi : lo ≤ hi := (Nat.floor_le_floor (by nlinarith)).trans (Nat.floor_le_ceil _)
      have hlim := hsum k (Finset.Ico lo hi) fun j hj ↦ (Finset.mem_Ico.1 hj).2.trans_le hhi
      have hval : ((Finset.Ico lo hi).card : ℝ) * B⁻¹ < u := by
        rw [Nat.card_Ico, Nat.cast_sub hlohi]
        have h1 : (hi : ℝ) < c * B + 1 := Nat.ceil_lt_add_one (mul_nonneg (ha.trans hac) hB.le)
        have h2 : a * B - 1 < lo := Nat.sub_one_lt_floor _
        have : ((hi : ℝ) - lo) * B⁻¹ ≤ c - a + 2 / B := by
          rw [← div_eq_mul_inv, div_le_iff₀ hB, add_mul, sub_mul, div_mul_cancel₀ _ hB.ne']
          linarith
        linarith
      filter_upwards [hlim.eventually (gt_mem_nhds hval)] with N hN
      refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)) hN
      refine Nat.cast_le.2 (Finset.card_le_card fun n hn ↦ ?_)
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
      refine ⟨hn.1, ?_, ?_⟩
      · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hn.2.1 hB.le)
      · rw [Nat.lt_ceil]
        exact (Nat.floor_le (mul_nonneg (hy0 n) hB.le)).trans_lt
          (mul_lt_mul_of_pos_right hn.2.2 hB)
  · intro h k j hj
    have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hj' : ((j : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 := by
      rw [div_le_one hB]
      exact_mod_cast hj
    have := h ((j : ℝ) / (b : ℝ) ^ k) (((j : ℝ) + 1) / (b : ℝ) ^ k) (by positivity)
      (div_le_div_of_nonneg_right (by linarith) hB.le) hj'
    rw [← sub_div, add_sub_cancel_left, one_div] at this
    refine this.congr fun N ↦ ?_
    congr 3
    ext n
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ ↦ (floor_mul_eq_iff_mem_Ico (hy0 n) hB j).symm

/-- For almost every `x`, the sequence `(x * b ^ n)` is equidistributed modulo one. -/
theorem ae_isEquidistributedModOne_mul_pow (hb : 2 ≤ b) :
    ∀ᵐ x : ℝ, IsEquidistributedModOne fun n ↦ x * (b : ℝ) ^ n := by
  filter_upwards [ae_isNormalIn (b := b) (by omega)] with x hx
  exact (isNormalIn_iff_isEquidistributedModOne hb).1 hx

end Real
