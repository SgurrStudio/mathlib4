/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Digits of algebraic numbers: Liouville-type gap bounds

Borel's conjecture (see `Wanted/NumberTheory/Normal/Basic.lean`) predicts that the base-`b`
expansion of an irrational algebraic number looks random. Very little is known in this direction.
The most elementary result is a consequence of Liouville's inequality: if `x` is a root of a
nonzero integer polynomial of degree `d`, then a run of zeros in the base-`b` expansion of `x`
starting at position `n` has length at most `(d - 1) * n + C`, for a constant `C` depending only on
`x` and `b`. Equivalently, every window `[n, d * n + C)` of positions contains a nonzero digit.

The idea is that a run of `m` zeros after position `n` gives a rational approximation
`⌊x * b ^ n⌋ / b ^ n` of `x` with error less than `b ^ (-(n + m))`, while Liouville's inequality
bounds the error from below by a constant times `b ^ (-(n * d))`.

## Main statements

* `Real.mul_pow_lt_one_of_digit_eq_zero`: if the first `m` digits of `y ∈ [0, 1)` vanish, then
  `y < b ^ (-m)`.
* `Real.exists_zero_run_le`: zero runs in the expansion of an irrational root of a nonzero
  integer polynomial of degree `d` starting at position `n` have length at most
  `(d - 1) * n + C`.
* `Real.exists_digit_ne_zero_of_isAlgebraic`: for an irrational algebraic number, some
  `d ≥ 1` and `C` are such that every window `[n, d * n + C)` contains a nonzero digit.

## References

* [D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance,
  *On the binary expansions of algebraic numbers*][baileyborweincrandallpomerance2004]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

open Polynomial

namespace Real

variable {b : ℕ} {x : ℝ}

/-- If the first `m` base-`b` digits of `y ∈ [0, 1)` all vanish, then `y < b ^ (-m)`, i.e.
`y * b ^ m < 1`. -/
theorem mul_pow_lt_one_of_digit_eq_zero (hb : 0 < b) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) {m : ℕ}
    (h : ∀ j < m, digit b y j = 0) : y * (b : ℝ) ^ m < 1 := by
  induction m with
  | zero => simpa using hy1
  | succ m ih =>
    have ih' := ih fun j hj ↦ h j (by omega)
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hlt : y * (b : ℝ) ^ (m + 1) < b := by
      rw [pow_succ, ← mul_assoc]
      exact (mul_lt_mul_of_pos_right ih' hb').trans_eq (one_mul _)
    have hnn : 0 ≤ y * (b : ℝ) ^ (m + 1) := by positivity
    have hz0 : 0 ≤ ⌊y * (b : ℝ) ^ (m + 1)⌋ := Int.floor_nonneg.2 hnn
    have hzb : ⌊y * (b : ℝ) ^ (m + 1)⌋ < b := Int.floor_lt.2 (by exact_mod_cast hlt)
    have hd := h m (by omega)
    rw [digit, Int.emod_eq_of_lt hz0 hzb] at hd
    have hz : ⌊y * (b : ℝ) ^ (m + 1)⌋ = 0 := by omega
    exact (Int.floor_eq_zero_iff.1 hz).2

/-- If the base-`b` digits of `x` at positions `n, n + 1, …, n + m - 1` all vanish, then
`x` is within `b ^ (-(n + m))` of the rational number `⌊x * b ^ n⌋ / b ^ n`. -/
theorem abs_sub_floor_div_lt_of_digit_eq_zero (hb : 0 < b) {n m : ℕ}
    (h : ∀ j < m, digit b x (n + j) = 0) :
    |x - ⌊x * (b : ℝ) ^ n⌋ / (b : ℝ) ^ n| < ((b : ℝ) ^ (n + m))⁻¹ := by
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hy := mul_pow_lt_one_of_digit_eq_zero hb (Int.fract_nonneg (x * (b : ℝ) ^ n))
    (Int.fract_lt_one _) (m := m) fun j hj ↦ by rw [← digit_add_eq_digit_fract]; exact h j hj
  have heq : x - ⌊x * (b : ℝ) ^ n⌋ / (b : ℝ) ^ n = Int.fract (x * (b : ℝ) ^ n) / (b : ℝ) ^ n := by
    rw [Int.fract]
    field_simp
  rw [heq, abs_of_nonneg (div_nonneg (Int.fract_nonneg _) hbn.le), div_lt_iff₀ hbn, pow_add,
    mul_inv, mul_comm ((b : ℝ) ^ n)⁻¹, mul_assoc, inv_mul_cancel₀ hbn.ne', mul_one, ← one_div,
    lt_div_iff₀ (by positivity)]
  exact hy

/-- **Liouville bound on zero runs.** Let `x` be an irrational root of a nonzero integer
polynomial `f`. Then there is a constant `C` such that any run of zero digits in the base-`b`
expansion of `x` starting at position `n` has length at most `(f.natDegree - 1) * n + C`. -/
theorem exists_zero_run_le (hb : 2 ≤ b) (hx : Irrational x) {f : ℤ[X]} (f0 : f ≠ 0)
    (fx : aeval x f = 0) :
    ∃ C : ℕ, ∀ n m : ℕ, (∀ j < m, digit b x (n + j) = 0) → m ≤ (f.natDegree - 1) * n + C := by
  have hb0 : 0 < b := by omega
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have fx' : eval x (map (algebraMap ℤ ℝ) f) = 0 := by rwa [eval_map, ← aeval_def]
  obtain ⟨A, hA, hL⟩ := Liouville.exists_pos_real_of_irrational_root hx f0 fx'
  obtain ⟨C, hC⟩ := pow_unbounded_of_one_lt A hb1
  have hd : 0 < f.natDegree := natDegree_pos_of_aeval_root f0 fx
    fun c hc ↦ by simpa using hc
  refine ⟨C, fun n m hrun ↦ ?_⟩
  set d := f.natDegree with hd_def
  have hap := abs_sub_floor_div_lt_of_digit_eq_zero hb0 hrun
  have hq : (((b ^ n - 1 : ℕ) : ℝ) + 1) = (b : ℝ) ^ n := by
    have : 1 ≤ b ^ n := Nat.one_le_pow _ _ hb0
    rw [Nat.cast_sub this]
    push_cast
    ring
  have h1 := hL ⌊x * (b : ℝ) ^ n⌋ (b ^ n - 1)
  rw [hq, ← pow_mul] at h1
  have hpos : (0 : ℝ) < (b : ℝ) ^ (n + m) := by positivity
  have h2 : (b : ℝ) ^ (n * d) * (|x - ⌊x * (b : ℝ) ^ n⌋ / (b : ℝ) ^ n| * A) <
      (b : ℝ) ^ (n * d) * (((b : ℝ) ^ (n + m))⁻¹ * (b : ℝ) ^ C) := by
    gcongr
  have h4 : (b : ℝ) ^ (n + m) < (b : ℝ) ^ (n * d + C) := by
    calc (b : ℝ) ^ (n + m) = (b : ℝ) ^ (n + m) * 1 := (mul_one _).symm
      _ < (b : ℝ) ^ (n + m) *
          ((b : ℝ) ^ (n * d) * (((b : ℝ) ^ (n + m))⁻¹ * (b : ℝ) ^ C)) := by
        gcongr
        exact h1.trans_lt h2
      _ = (b : ℝ) ^ (n * d + C) := by
        field_simp
        rw [pow_add]
  have h5 := (pow_lt_pow_iff_right₀ hb1).1 h4
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [he] at h5 ⊢
  simp only [add_tsub_cancel_right]
  have : n * (e + 1) = e * n + n := by ring
  rw [this] at h5
  generalize e * n = t at h5 ⊢
  omega

/-- For an irrational algebraic number `x` and a base `b ≥ 2`, there are `d ≥ 1` and `C` such that
every window of positions `[n, d * n + C)` contains a nonzero base-`b` digit of `x`. In particular
the gaps between consecutive nonzero digits grow at most geometrically. -/
theorem exists_digit_ne_zero_of_isAlgebraic (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x)
    (hx : Irrational x) :
    ∃ d C : ℕ, 1 ≤ d ∧ ∀ n : ℕ, ∃ i, n ≤ i ∧ i < d * n + C ∧ digit b x i ≠ 0 := by
  obtain ⟨f, f0, fx⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).2 halg
  obtain ⟨C, hC⟩ := exists_zero_run_le hb hx f0 fx
  have hd : 0 < f.natDegree := natDegree_pos_of_aeval_root f0 fx
    fun c hc ↦ by simpa using hc
  refine ⟨f.natDegree, C + 1, hd, fun n ↦ ?_⟩
  obtain ⟨e, he⟩ : ∃ e, f.natDegree = e + 1 := ⟨f.natDegree - 1, by omega⟩
  rw [he] at hC ⊢
  simp only [add_tsub_cancel_right] at hC
  have hmul : (e + 1) * n = e * n + n := by ring
  rw [hmul]
  by_contra! hall
  have := hC n (e * n + C + 1) fun j hj ↦ hall (n + j) (by omega) (by omega)
  omega

end Real
