/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Normal numbers

A real number `x` is *normal in base `b`* if, in its base-`b` expansion, every block of `k` digits
occurs with asymptotic frequency `b⁻ᵏ`. It is *absolutely normal* if it is normal in every base
`b ≥ 2`. These notions were introduced by É. Borel in 1909.

## Main definitions

* `Real.digit b x n`: the `n`-th digit (counted from `0`) after the radix point of the base-`b`
  expansion of `x`, i.e. `⌊x * b ^ (n + 1)⌋ mod b`. This is the expansion of the fractional part
  of `x` that does not end in an infinite string of `b - 1`s.
* `Real.blockCount b x w N`: the number of positions `i < N` at which the block `w` of digits
  occurs in the base-`b` expansion of `x`.
* `Real.IsSimplyNormalIn b x`: every digit occurs with frequency `1 / b`.
* `Real.IsNormalIn b x`: every block of `k` digits occurs with frequency `b⁻ᵏ`.
* `Real.IsAbsolutelyNormal x`: `x` is normal in every base `b ≥ 2`.
* `Real.IsDisjunctiveIn b x`: every block of digits occurs in the base-`b` expansion of `x`.

## Main statements

* `Real.IsNormalIn.isSimplyNormalIn`: normal numbers are simply normal.
* `Real.IsNormalIn.isDisjunctiveIn`: normal numbers are disjunctive.
* `Real.isNormalIn_add_intCast_iff`: normality only depends on the fractional part.
* `Real.IsNormalIn.irrational`: a number normal in some base `b ≥ 2` is irrational.
* `Real.isNormalIn_mul_pow_iff`: normality in base `b` is invariant under multiplication by
  powers of `b`.

Borel's conjecture, that every irrational algebraic number is absolutely normal, is stated in
`Wanted/NumberTheory/Normal/Basic.lean`.

## References

* [É. Borel, *Les probabilités dénombrables et leurs applications arithmétiques*][Borel1909]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The `n`-th digit (counted from `0`) after the radix point of the base-`b` expansion of `x`,
namely `⌊x * b ^ (n + 1)⌋ mod b`. For `x ∈ [0, 1)` this agrees with `Real.digits x b n`
(`Real.val_digits_eq_digit`). -/
noncomputable def digit (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  (⌊x * (b : ℝ) ^ (n + 1)⌋ % (b : ℤ)).toNat

/-- The number of positions `i < N` such that the block of digits of `x` (in base `b`) starting at
position `i` is the word `w`. -/
noncomputable def blockCount (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range N).filter fun i ↦ ∀ j : Fin k, digit b x (i + j) = w j).card

/-- A real number `x` is *simply normal in base `b`* if each of the `b` digits occurs in the
base-`b` expansion of `x` with asymptotic frequency `1 / b`. -/
def IsSimplyNormalIn (b : ℕ) (x : ℝ) : Prop :=
  ∀ d : Fin b, Tendsto (fun N : ℕ ↦ (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N) atTop
    (𝓝 (b : ℝ)⁻¹)

/-- A real number `x` is *normal in base `b`* if every block `w` of `k` digits occurs in the
base-`b` expansion of `x` with asymptotic frequency `b⁻ᵏ`.

The notion is only meaningful for `b ≥ 2`: in base `1` every digit is `0` and in base `0` there
are no nonempty blocks, so every real number is normal in bases `0` and `1`. This is why
`Real.IsAbsolutelyNormal` quantifies over `b ≥ 2`. -/
def IsNormalIn (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Fin b), Tendsto (fun N : ℕ ↦ (blockCount b x w N : ℝ) / N) atTop
    (𝓝 ((b : ℝ) ^ k)⁻¹)

/-- A real number is *absolutely normal* if it is normal in every base `b ≥ 2`. -/
def IsAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalIn b x

/-- A real number `x` is *disjunctive* (or *rich*) *in base `b`* if every finite block of digits
occurs (at least once) in the base-`b` expansion of `x`. Normal numbers are disjunctive. -/
def IsDisjunctiveIn (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Fin b), ∃ i : ℕ, ∀ j : Fin k, digit b x (i + j) = w j

variable {b : ℕ} {x : ℝ}

theorem digit_lt (hb : 0 < b) (x : ℝ) (n : ℕ) : digit b x n < b := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  rw [digit, Int.toNat_lt (Int.emod_nonneg _ hb'.ne')]
  exact Int.emod_lt_of_pos _ hb'

@[simp]
theorem digit_add_intCast (b : ℕ) (x : ℝ) (m : ℤ) (n : ℕ) :
    digit b (x + m) n = digit b x n := by
  have : (x + m) * (b : ℝ) ^ (n + 1) =
      x * (b : ℝ) ^ (n + 1) + ((m * (b : ℤ) ^ (n + 1) : ℤ) : ℝ) := by
    push_cast; ring
  have hd : (b : ℤ) ∣ m * (b : ℤ) ^ (n + 1) := (dvd_pow_self _ n.succ_ne_zero).mul_left _
  rw [digit, digit, this, Int.floor_add_intCast, Int.add_emod, Int.emod_eq_zero_of_dvd hd,
    add_zero, Int.emod_emod]

/-- The digits of `x` from position `i` on are the digits of `x * b ^ i`. -/
theorem digit_add (b : ℕ) (x : ℝ) (i j : ℕ) : digit b x (i + j) = digit b (x * (b : ℝ) ^ i) j := by
  rw [digit, digit, mul_assoc, ← pow_add, add_assoc]

@[simp]
theorem digit_fract (b : ℕ) (x : ℝ) (n : ℕ) : digit b (Int.fract x) n = digit b x n := by
  rw [Int.fract, sub_eq_add_neg, ← Int.cast_neg, digit_add_intCast]

/-- The digits of `x` from position `i` on only depend on the fractional part of `x * b ^ i`. -/
theorem digit_add_eq_digit_fract (b : ℕ) (x : ℝ) (i j : ℕ) :
    digit b x (i + j) = digit b (Int.fract (x * (b : ℝ) ^ i)) j := by
  rw [digit_fract, digit_add]

@[simp]
theorem blockCount_add_intCast (b : ℕ) (x : ℝ) (m : ℤ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockCount b (x + m) w N = blockCount b x w N := by
  simp [blockCount]

theorem blockCount_le (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockCount b x w N ≤ N :=
  (Finset.card_filter_le _ _).trans (Finset.card_range N).le

theorem IsNormalIn.isSimplyNormalIn (h : IsNormalIn b x) : IsSimplyNormalIn b x := fun d ↦ by
  simpa using h 1 (fun _ ↦ d)

/-- Normal numbers are disjunctive: every block of digits occurs. -/
theorem IsNormalIn.isDisjunctiveIn (h : IsNormalIn b x) : IsDisjunctiveIn b x := by
  intro k w
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, fun j ↦ j.elim0⟩
  have hb : 0 < b := Fin.pos (w ⟨0, hk⟩)
  obtain ⟨N, hN⟩ := ((h k w).eventually
    (lt_mem_nhds (inv_pos.2 (pow_pos (Nat.cast_pos.2 hb) k)))).exists
  have hpos : 0 < blockCount b x w N := by
    rcases Nat.eq_zero_or_pos (blockCount b x w N) with h0 | h0
    · simp [h0] at hN
    · exact h0
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
  exact ⟨i, (Finset.mem_filter.1 hi).2⟩

@[simp]
theorem isNormalIn_add_intCast_iff (m : ℤ) : IsNormalIn b (x + m) ↔ IsNormalIn b x := by
  simp [IsNormalIn]

@[simp]
theorem isAbsolutelyNormal_add_intCast_iff (m : ℤ) :
    IsAbsolutelyNormal (x + m) ↔ IsAbsolutelyNormal x := by
  simp [IsAbsolutelyNormal]

/-- If the block `w` never occurs in the expansion of `x`, then `x` is not normal. -/
theorem not_isNormalIn_of_forall_ne {k : ℕ} (w : Fin k → Fin b)
    (hw : ∀ i, ∃ j : Fin k, digit b x (i + j) ≠ w j) : ¬ IsNormalIn b x := by
  intro h
  have h0 : ∀ N, blockCount b x w N = 0 := fun N ↦ by
    rw [blockCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    obtain ⟨j, hj⟩ := hw i
    exact hj (hi j)
  have := h k w
  simp only [h0, Nat.cast_zero, zero_div] at this
  have hbk : ((b : ℝ) ^ k)⁻¹ ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fin.pos (w ⟨0, hk⟩)).ne'))
  exact hbk (tendsto_nhds_unique tendsto_const_nhds this).symm

/-- A rational number is not normal in any base `b ≥ 2`: its expansion only contains finitely
many distinct blocks of each length, so long enough blocks are missing. -/
theorem IsNormalIn.irrational (hb : 2 ≤ b) (h : IsNormalIn b x) : Irrational x := by
  rintro ⟨r, rfl⟩
  have hb0 : 0 < b := by omega
  set q := r.den with hq
  -- the block of length `q` starting at position `i`
  let blk : ℝ → Fin q → Fin b := fun y j ↦ ⟨digit b y j, digit_lt hb0 y j⟩
  -- the fractional parts of `r * b ^ i` lie in `{t / q | t < q}`
  have key : ∀ i, ∃ t ∈ Finset.range q, ∀ j : Fin q,
      digit b r (i + j) = (blk ((t : ℝ) / q) j : ℕ) := by
    intro i
    refine ⟨((r.num * (b : ℤ) ^ i) % (q : ℤ)).toNat, ?_, fun j ↦ ?_⟩
    · have hq0 : (0 : ℤ) < q := by exact_mod_cast r.pos
      rw [Finset.mem_range, ← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ hq0.ne')]
      exact Int.emod_lt_of_pos _ hq0
    · have hq0 : (0 : ℤ) ≤ (r.num * (b : ℤ) ^ i) % (q : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast r.pos.ne')
      have hfr : Int.fract ((r : ℝ) * (b : ℝ) ^ i) =
          (((r.num * (b : ℤ) ^ i) % (q : ℤ)).toNat : ℝ) / q := by
        have : (r : ℝ) * (b : ℝ) ^ i = ((r.num * (b : ℤ) ^ i : ℤ) : ℝ) / (q : ℕ) := by
          rw [hq]; push_cast
          rw [Rat.cast_def]; ring
        rw [this, Int.fract_div_intCast_eq_div_intCast_mod]
        congr 1
        exact_mod_cast (Int.toNat_of_nonneg hq0).symm
      simp only [blk]
      rw [digit_add_eq_digit_fract, hfr]
  classical
  have hcard : ((Finset.range q).image fun t : ℕ ↦ blk ((t : ℝ) / q)).card <
      Fintype.card (Fin q → Fin b) := by
    refine Finset.card_image_le.trans_lt ?_
    rw [Finset.card_range, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    calc q < 2 ^ q := Nat.lt_two_pow_self
      _ ≤ b ^ q := Nat.pow_le_pow_left hb q
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := Finset.univ) (s := (Finset.range q).image fun t : ℕ ↦ blk ((t : ℝ) / q))
    (by simpa using hcard)
  refine not_isNormalIn_of_forall_ne w (fun i ↦ ?_) h
  obtain ⟨t, ht, hblk⟩ := key i
  by_contra! hall
  exact hw (Finset.mem_image.2 ⟨t, ht, funext fun j ↦ Fin.ext ((hblk j).symm.trans (hall j))⟩)

theorem IsAbsolutelyNormal.irrational (h : IsAbsolutelyNormal x) : Irrational x :=
  (h 2 le_rfl).irrational le_rfl

theorem blockCount_succ {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockCount b x w (N + 1) =
      blockCount b x w N + if ∀ j : Fin k, digit b x (N + j) = w j then 1 else 0 := by
  classical
  simp only [blockCount, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- Shifting the expansion by `r` digits: the blocks of `x * b ^ r` before position `N` are the
blocks of `x` at positions `r, …, N + r - 1`. -/
theorem blockCount_add {k : ℕ} (w : Fin k → Fin b) (N r : ℕ) :
    blockCount b x w (N + r) = blockCount b x w r + blockCount b (x * (b : ℝ) ^ r) w N := by
  induction N with
  | zero => simp [blockCount]
  | succ N ih =>
    have hd : ∀ j : Fin k, digit b x (N + r + j) = digit b (x * (b : ℝ) ^ r) (N + j) := by
      intro j
      rw [← digit_add, show r + (N + j) = N + r + j by ring]
    rw [show N + 1 + r = N + r + 1 by ring, blockCount_succ, ih, blockCount_succ, add_assoc]
    simp_rw [hd]

/-- Normality in base `b` is invariant under multiplication by powers of `b`. -/
@[simp]
theorem isNormalIn_mul_pow_iff (r : ℕ) : IsNormalIn b (x * (b : ℝ) ^ r) ↔ IsNormalIn b x := by
  have h1 : Tendsto (fun N : ℕ ↦ (N : ℝ) / (N + r)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (r : ℝ)
  have h2 : Tendsto (fun N : ℕ ↦ ((N : ℝ) + r) / N) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)).const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [add_div, div_self (by exact_mod_cast hN.ne')]
  have hc : ∀ c : ℝ, Tendsto (fun N : ℕ ↦ c / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat
  refine forall_congr' fun k ↦ forall_congr' fun w ↦ ?_
  set f : ℕ → ℝ := fun N ↦ (blockCount b x w N : ℝ)
  set L : ℝ := ((b : ℝ) ^ k)⁻¹
  have key : ∀ N, (blockCount b (x * (b : ℝ) ^ r) w N : ℝ) = f (N + r) - f r := by
    intro N
    simp only [f, blockCount_add w N r, Nat.cast_add]
    ring
  simp_rw [key]
  rw [← tendsto_add_atTop_iff_nat r (f := fun N ↦ f N / N)]
  push_cast
  constructor
  · intro h
    have h3 := (h.add (hc (f r))).mul h1
    rw [add_zero, mul_one] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℝ) + r ≠ 0 := by positivity
    field_simp
    ring
  · intro h
    have h3 := (h.mul h2).sub (hc (f r))
    rw [mul_one, sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℝ) + r ≠ 0 := by positivity
    field_simp

end Real
