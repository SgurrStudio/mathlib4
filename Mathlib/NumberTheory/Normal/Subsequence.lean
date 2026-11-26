/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.CopelandErdos

import Mathlib.NumberTheory.Normal.BasePow

/-!
# Normality of digits along an arithmetic progression

If `x` is normal in base `b ≥ 2`, then for every offset `a` and step `m ≥ 1`, the digit subsequence
`n ↦ Real.digit b x (a + m * n)` is normal in base `b`, and the real number formed from these
digits via `Real.ofDigits` is normal in base `b`.

## Main statements

* `Real.IsNormalIn.isNormalSeq_arithmeticProgression`: if `IsNormalIn b x` (`2 ≤ b`) and `0 < m`,
  then `IsNormalSeq b (fun n ↦ digit b x (a + m * n))`.
* `Real.IsNormalIn.ofDigits_arithmeticProgression`: the real number with base-`b` digits
  `n ↦ digit b x (a + m * n)` is normal in base `b`.

## References

* D. D. Wall, *Normal numbers*, PhD thesis, University of California, Berkeley, 1949.
* L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Ch. 1 §8.
-/

@[expose] public section

open Filter Topology

namespace Real

private theorem digit_pow_mod_eq_digit {b m : ℕ} (hb : 0 < b) (hm : 0 < m) (z : ℝ) (n : ℕ) :
    digit (b ^ m) z n % b = digit b z (m - 1 + m * n) := by
  have hdvd : (b : ℤ) ∣ ((b ^ m : ℕ) : ℤ) := by
    exact_mod_cast dvd_pow_self b hm.ne'
  have hpow : (((b ^ m : ℕ) : ℝ) ^ (n + 1)) = (b : ℝ) ^ (m - 1 + m * n + 1) := by
    rw [Nat.cast_pow, ← pow_mul]
    congr 1
    rw [Nat.mul_add, mul_one]
    omega
  rw [digit, digit, hpow]
  have hnn : 0 ≤ ⌊z * (b : ℝ) ^ (m - 1 + m * n + 1)⌋ % ((b ^ m : ℕ) : ℤ) :=
    Int.emod_nonneg _ (by positivity)
  have hmod := Int.toNat_emod hnn (Int.natCast_nonneg b)
  rw [Int.toNat_natCast, Int.emod_emod_of_dvd _ hdvd] at hmod
  exact hmod.symm

private theorem card_filter_mod_eq {b m k : ℕ} (hb : 0 < b) (hm : 0 < m) (w : Fin k → Fin b) :
    (Finset.univ.filter fun u : Fin k → Fin (b ^ m) ↦ ∀ j : Fin k, (u j : ℕ) % b = w j).card =
      (b ^ (m - 1)) ^ k := by
  have hbm : b ^ (m - 1) * b = b ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hcard : Fintype.card (Fin k → Fin (b ^ (m - 1))) = (b ^ (m - 1)) ^ k := by
    simp
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_bij'
    (fun (u : Fin k → Fin (b ^ m)) _ j ↦
      ⟨(u j : ℕ) / b, Nat.div_lt_of_lt_mul (by rw [mul_comm, hbm]; exact (u j).isLt)⟩)
    (fun (q : Fin k → Fin (b ^ (m - 1))) _ j ↦
      ⟨(q j : ℕ) * b + w j, by
        have hq : (q j : ℕ) + 1 ≤ b ^ (m - 1) := (q j).isLt
        have hw : (w j : ℕ) < b := (w j).isLt
        nlinarith⟩)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun q _ ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (w j).isLt])
    (fun u hu ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      ext j
      simp only [← hu j, Nat.div_add_mod'])
    (fun q _ ↦ by
      ext j
      simp only
      rw [mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt (w j).isLt, add_zero])

/-- **Wall (1949)**: the base-`b` digits of a base-`b` normal number sampled along any arithmetic
progression `a + m * n` (`m ≥ 1`) form a base-`b` normal sequence. -/
theorem IsNormalIn.isNormalSeq_arithmeticProgression {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : IsNormalIn b x) (a : ℕ) {m : ℕ} (hm : 0 < m) :
    IsNormalSeq b (fun n ↦ digit b x (a + m * n)) := by
  have hb0 : 0 < b := by omega
  have hbr : (b : ℝ) ≠ 0 := by positivity
  set z : ℝ := x * (b : ℝ) ^ a * ((b : ℝ) ^ (m - 1))⁻¹
  have hz_mul : z * (b : ℝ) ^ (m - 1) = x * (b : ℝ) ^ a := by
    simp only [z]
    field_simp [hbr]
  have hz : IsNormalIn b z := by
    rw [← isNormalIn_mul_pow_iff (m - 1), hz_mul, isNormalIn_mul_pow_iff a]
    exact hx
  have hz_pow : IsNormalIn (b ^ m) z := hz.pow hb hm
  have hdig : ∀ n : ℕ, digit b x (a + m * n) = digit (b ^ m) z n % b := fun n ↦ by
    rw [digit_pow_mod_eq_digit hb0 hm, digit_add b z, hz_mul, ← digit_add]
  intro k w
  set S : Finset (Fin k → Fin (b ^ m)) :=
    Finset.univ.filter fun u ↦ ∀ j : Fin k, (u j : ℕ) % b = w j
  have hcount : ∀ N : ℕ,
      (((Finset.range N).filter fun i ↦ ∀ j : Fin k, digit b x (a + m * (i + j)) = w j).card : ℝ) /
          N =
        ∑ u ∈ S, (blockCount (b ^ m) z u N : ℝ) / N := by
    intro N
    rw [← Finset.sum_div, ← Nat.cast_sum]
    congr 2
    have hdisj : (S : Set (Fin k → Fin (b ^ m))).PairwiseDisjoint fun u ↦
        (Finset.range N).filter fun i ↦ ∀ j : Fin k, digit (b ^ m) z (i + j) = u j := by
      intro u₁ _ u₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro i hi₁ hi₂
      simp only [Finset.mem_filter] at hi₁ hi₂
      apply hne
      ext j
      exact (hi₁.2 j).symm.trans (hi₂.2 j)
    simp only [blockCount]
    rw [← Finset.card_biUnion hdisj]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, S, Finset.mem_univ,
      true_and, hdig]
    constructor
    · intro ⟨hiN, hi⟩
      refine ⟨fun j ↦ ⟨digit (b ^ m) z (i + j), digit_lt (by positivity) z _⟩, ?_, hiN, ?_⟩
      · intro j; exact hi j
      · intro j; rfl
    · rintro ⟨u, hu, hiN, hi⟩
      refine ⟨hiN, fun j ↦ ?_⟩
      rw [hi j, hu j]
  simp_rw [hcount]
  have hlim : Tendsto (fun N : ℕ ↦ ∑ u ∈ S, (blockCount (b ^ m) z u N : ℝ) / N) atTop
      (𝓝 (∑ _u ∈ S, (((b ^ m : ℕ) : ℝ) ^ k)⁻¹)) := by
    classical
    induction S using Finset.induction with
    | empty => simp
    | insert u T hu ih =>
      simp only [Finset.sum_insert hu]
      exact (hz_pow k u).add ih
  have htarget : ∑ _u ∈ S, (((b ^ m : ℕ) : ℝ) ^ k)⁻¹ = ((b : ℝ) ^ k)⁻¹ := by
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_mod_eq hb0 hm w]
    have hbm : (b : ℝ) ^ (m - 1) * (b : ℝ) = (b : ℝ) ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    push_cast
    have hmul : ((b : ℝ) ^ (m - 1)) ^ k * (b : ℝ) ^ k = ((b : ℝ) ^ m) ^ k := by
      rw [← mul_pow, hbm]
    have hbm0 : ((b : ℝ) ^ m) ^ k ≠ 0 := by positivity
    have hbk0 : (b : ℝ) ^ k ≠ 0 := by positivity
    field_simp [hbm0, hbk0]
    exact hmul
  rwa [htarget] at hlim

/-- The real number whose base-`b` digits are `n ↦ Real.digit b x (a + m * n)` is normal in
base `b` whenever `x` is normal in base `b` (`2 ≤ b`) and `0 < m`. -/
theorem IsNormalIn.ofDigits_arithmeticProgression {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : IsNormalIn b x) (a : ℕ) {m : ℕ} (hm : 0 < m) :
    IsNormalIn b (ofDigits fun n ↦ ⟨digit b x (a + m * n), digit_lt (by omega) x _⟩) :=
  isNormalIn_ofDigits hb (hx.isNormalSeq_arithmeticProgression hb a hm)

end Real
