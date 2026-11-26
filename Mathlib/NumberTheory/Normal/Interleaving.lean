/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.Normal.CopelandErdos

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Normal.BasePow
import Mathlib.NumberTheory.Normal.DigitOperations
import Mathlib.NumberTheory.Normal.Rational
import Mathlib.NumberTheory.Normal.Subsequence

/-!
# Digit interleaving and jointly normal numbers

Two real numbers `x` and `y` are *jointly normal in base `b`* if every pair `(u, v)` of length-`k`
blocks of base-`b` digits occurs simultaneously at the same position in `x` and `y` with asymptotic
frequency `b ^ (-2k)`. Equivalently, the base-`b` digit interleaving `Real.interleave b x y` is
normal in base `b`.

## Main definitions

* `Real.interleaveDigits b x y n`: the `n`-th interleaved base-`b` digit of `x` and `y`, taking
  `digit b x (n / 2)` at even indices and `digit b y (n / 2)` at odd indices.
* `Real.interleave b x y`: the real number in `[0, 1)` formed by interleaving the base-`b` digits
  of `x` and `y`.
* `Real.jointBlockCount b x y u v N`: the number of positions `i < N` where the base-`b` digit
  blocks of `x` and `y` simultaneously match `u` and `v`.
* `Real.IsJointlyNormalIn b x y`: `x` and `y` are jointly normal in base `b`.
* `Real.IsJointlyAbsolutelyNormal x y`: `x` and `y` are jointly normal in every base `b ≥ 2`.

## Main statements

* `Real.interleave_eq_ofDigits_sq`: `interleave b x y` equals the base-`b ^ 2` expansion with
  digits `m ↦ b * digit b x m + digit b y m`.
* `Real.isJointlyNormalIn_iff_isNormalIn_interleave`: `x` and `y` are jointly normal in base `b`
  if and only if `interleave b x y` is normal in base `b`.
* `Real.IsJointlyNormalIn.left`, `Real.IsJointlyNormalIn.right`, `Real.IsJointlyNormalIn.symm`:
  marginals and symmetry of joint normality.
* `Real.isJointlyNormalIn_even_odd`, `Real.exists_isJointlyNormalIn`: splitting a base-`b` normal
  number into its even and odd digits produces a jointly normal pair.
* `Real.ae_isJointlyNormalIn`, `Real.ae_isJointlyAbsolutelyNormal`: Lebesgue-almost every pair
  `(x, y) ∈ ℝ × ℝ` is jointly normal in base `b` (and jointly absolutely normal).
* `Real.isSimplyNormalIn_interleave_of_isSimplyNormalIn`: interleaving any two simply normal
  numbers preserves simple normality.
* `Real.not_isJointlyNormalIn_self`, `Real.not_isJointlyNormalIn_comp_equiv`,
  `Real.not_isJointlyNormalIn_neg`, `Real.not_isJointlyNormalIn_mul_pow`: correlated pairs
  `(x, x)`, `(x, σ(x))`, `(x, -x)`, and `(x, b ^ m * x)` are never jointly normal (so their
  interleavings are simply normal but not normal).
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Real

variable {b : ℕ} {x y : ℝ}

/-! ### Core definitions and digit identities -/

/-- The `n`-th digit obtained by interleaving the base-`b` digits of `x` (at even indices) and `y`
(at odd indices). -/
noncomputable def interleaveDigits (b : ℕ) (x y : ℝ) (n : ℕ) : ℕ :=
  if n % 2 = 0 then digit b x (n / 2) else digit b y (n / 2)

theorem interleaveDigits_lt (hb : 0 < b) (x y : ℝ) (n : ℕ) :
    interleaveDigits b x y n < b := by
  unfold interleaveDigits
  split_ifs <;> exact digit_lt hb _ _

@[simp]
theorem interleaveDigits_two_mul (b : ℕ) (x y : ℝ) (m : ℕ) :
    interleaveDigits b x y (2 * m) = digit b x m := by
  simp [interleaveDigits]

@[simp]
theorem interleaveDigits_two_mul_add_one (b : ℕ) (x y : ℝ) (m : ℕ) :
    interleaveDigits b x y (2 * m + 1) = digit b y m := by
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp [interleaveDigits, hmod, hdiv]

@[simp]
theorem interleaveDigits_add_intCast_left (b : ℕ) (x y : ℝ) (m : ℤ) (n : ℕ) :
    interleaveDigits b (x + m) y n = interleaveDigits b x y n := by
  simp [interleaveDigits]

@[simp]
theorem interleaveDigits_add_intCast_right (b : ℕ) (x y : ℝ) (m : ℤ) (n : ℕ) :
    interleaveDigits b x (y + m) n = interleaveDigits b x y n := by
  simp [interleaveDigits]

/-- The real number formed by interleaving the base-`b` digits of `x` and `y`. -/
noncomputable def interleave (b : ℕ) (x y : ℝ) : ℝ :=
  if hb : 0 < b then
    ofDigits fun n ↦ (⟨interleaveDigits b x y n, interleaveDigits_lt hb x y n⟩ : Fin b)
  else 0

@[simp]
theorem interleave_add_intCast_left (b : ℕ) (x y : ℝ) (m : ℤ) :
    interleave b (x + m) y = interleave b x y := by
  unfold interleave
  split_ifs with hb
  · congr 1
    ext n
    exact interleaveDigits_add_intCast_left b x y m n
  · rfl

@[simp]
theorem interleave_add_intCast_right (b : ℕ) (x y : ℝ) (m : ℤ) :
    interleave b x (y + m) = interleave b x y := by
  unfold interleave
  split_ifs with hb
  · congr 1
    ext n
    exact interleaveDigits_add_intCast_right b x y m n
  · rfl

/-- The number of positions `i < N` at which the base-`b` digit blocks of `x` and `y`
simultaneously equal `u` and `v`. -/
noncomputable def jointBlockCount (b : ℕ) (x y : ℝ) {k : ℕ} (u v : Fin k → Fin b) (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range N).filter fun i ↦
    (∀ j : Fin k, digit b x (i + j) = u j) ∧ (∀ j : Fin k, digit b y (i + j) = v j)).card

@[simp]
theorem jointBlockCount_add_intCast_left (b : ℕ) (x y : ℝ) (m : ℤ) {k : ℕ}
    (u v : Fin k → Fin b) (N : ℕ) :
    jointBlockCount b (x + m) y u v N = jointBlockCount b x y u v N := by
  simp [jointBlockCount]

@[simp]
theorem jointBlockCount_add_intCast_right (b : ℕ) (x y : ℝ) (m : ℤ) {k : ℕ}
    (u v : Fin k → Fin b) (N : ℕ) :
    jointBlockCount b x (y + m) u v N = jointBlockCount b x y u v N := by
  simp [jointBlockCount]

/-- Two real numbers `x` and `y` are *jointly normal in base `b`* if every pair `(u, v)` of
length-`k` base-`b` digit blocks occurs simultaneously in `x` and `y` with asymptotic frequency
`b ^ (-2k)`. -/
def IsJointlyNormalIn (b : ℕ) (x y : ℝ) : Prop :=
  ∀ (k : ℕ) (u v : Fin k → Fin b),
    Tendsto (fun N : ℕ ↦ (jointBlockCount b x y u v N : ℝ) / N) atTop (𝓝 ((b : ℝ) ^ (2 * k))⁻¹)

/-- Two real numbers `x` and `y` are *jointly absolutely normal* if they are jointly normal in
every base `b ≥ 2`. -/
def IsJointlyAbsolutelyNormal (x y : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsJointlyNormalIn b x y

@[simp]
theorem isJointlyNormalIn_add_intCast_left_iff (m : ℤ) :
    IsJointlyNormalIn b (x + m) y ↔ IsJointlyNormalIn b x y := by
  simp [IsJointlyNormalIn]

@[simp]
theorem isJointlyNormalIn_add_intCast_right_iff (m : ℤ) :
    IsJointlyNormalIn b x (y + m) ↔ IsJointlyNormalIn b x y := by
  simp [IsJointlyNormalIn]

/-- The canonical base-`b` expansion of any real number has infinitely many digits `< b - 1`. -/
theorem exists_gt_digit_lt_sub_one (hb : 2 ≤ b) (x : ℝ) (m : ℕ) :
    ∃ n, m < n ∧ digit b x n + 1 < b := by
  have hb0 : 0 < b := by omega
  have : NeZero b := ⟨by omega⟩
  by_contra! hcon
  set z : ℝ := Int.fract (x * (b : ℝ) ^ (m + 1))
  have hz : z ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hdig : digits z b = fun _ ↦ (⟨b - 1, by omega⟩ : Fin b) := by
    funext k
    apply Fin.ext
    rw [val_digits_eq_digit hz k]
    have h1 : digit b z k = digit b x (m + 1 + k) := by
      rw [digit_fract, ← digit_add]
    have hlt := digit_lt hb0 x (m + 1 + k)
    have hge := hcon (m + 1 + k) (by omega)
    dsimp only
    omega
  have hz1 : z = 1 := by
    rw [← ofDigits_digits (b := b) (by omega) hz, hdig, ofDigits_const_last_eq_one' (by omega)]
  linarith [hz.2]

theorem interleave_mem_Ico (hb : 2 ≤ b) (x y : ℝ) : interleave b x y ∈ Ico (0 : ℝ) 1 := by
  have hb0 : 0 < b := by omega
  simp only [interleave, hb0, ↓reduceDIte]
  refine ⟨ofDigits_nonneg _, ?_⟩
  obtain ⟨r, -, hr⟩ := exists_gt_digit_lt_sub_one hb x 0
  exact ofDigits_lt_one (by omega) _ (m := 2 * r) (by simpa using hr)

/-- The base-`b` digits of `interleave b x y` are unconditionally `interleaveDigits b x y`. -/
theorem digit_interleave (hb : 2 ≤ b) (x y : ℝ) (n : ℕ) :
    digit b (interleave b x y) n = interleaveDigits b x y n := by
  have hb0 : 0 < b := by omega
  simp only [interleave, hb0, ↓reduceDIte]
  refine digit_ofDigits (by omega) _ (fun m ↦ ?_) n
  obtain ⟨r, hr, hrlt⟩ := exists_gt_digit_lt_sub_one hb x m
  refine ⟨2 * r, by omega, ?_⟩
  simpa using hrlt

/-- Interleaving the base-`b` digits of `x` and `y` equals the base-`b ^ 2` real number with
digits `m ↦ b * digit b x m + digit b y m`. -/
theorem interleave_eq_ofDigits_sq (hb : 0 < b) (x y : ℝ) :
    interleave b x y = ofDigits (b := b ^ 2) fun m ↦
      ⟨b * digit b x m + digit b y m, by
        have hx := digit_lt hb x m
        have hy := digit_lt hb y m
        nlinarith⟩ := by
  simp only [interleave, hb, ↓reduceDIte]
  set d : ℕ → Fin b := fun n ↦ ⟨interleaveDigits b x y n, interleaveDigits_lt hb x y n⟩
  set d₂ : ℕ → Fin (b ^ 2) := fun m ↦
    ⟨b * digit b x m + digit b y m, by
      have hx := digit_lt hb x m
      have hy := digit_lt hb y m
      nlinarith⟩
  have hpair : ∀ m, ofDigitsTerm d (2 * m) + ofDigitsTerm d (2 * m + 1) = ofDigitsTerm d₂ m := by
    intro m
    simp only [ofDigitsTerm, d, d₂, interleaveDigits_two_mul, interleaveDigits_two_mul_add_one]
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    have hpow1 : (b : ℝ) ^ (2 * m + 2) = (b : ℝ) ^ (2 * m + 1) * (b : ℝ) := by
      rw [← pow_succ]
    have hpow2 : (((b ^ 2 : ℕ) : ℝ) ^ (m + 1)) = (b : ℝ) ^ (2 * m + 2) := by
      push_cast
      rw [← pow_mul]
      congr 1
    rw [hpow2, hpow1]
    push_cast
    field_simp [hb0]
  have hsum : ∀ M, ∑ n ∈ Finset.range (2 * M), ofDigitsTerm d n =
      ∑ m ∈ Finset.range M, ofDigitsTerm d₂ m := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, add_assoc, hpair M]
  have ht1 : Tendsto (fun M ↦ ∑ n ∈ Finset.range (2 * M), ofDigitsTerm d n) atTop
      (𝓝 (ofDigits d)) :=
    (summable_ofDigitsTerm.hasSum.tendsto_sum_nat).comp
      (tendsto_id.const_mul_atTop' (by omega : 0 < 2))
  have ht2 : Tendsto (fun M ↦ ∑ m ∈ Finset.range M, ofDigitsTerm d₂ m) atTop (𝓝 (ofDigits d₂)) :=
    summable_ofDigitsTerm.hasSum.tendsto_sum_nat
  simp_rw [hsum] at ht1
  exact tendsto_nhds_unique ht1 ht2

/-- The base-`b ^ 2` digits of `interleave b x y` are `m ↦ b * digit b x m + digit b y m`. -/
theorem digit_sq_interleave (hb : 2 ≤ b) (x y : ℝ) (m : ℕ) :
    digit (b ^ 2) (interleave b x y) m = b * digit b x m + digit b y m := by
  have hb0 : 0 < b := by omega
  rw [interleave_eq_ofDigits_sq hb0 x y]
  refine digit_ofDigits (by nlinarith) _ (fun n ↦ ?_) m
  obtain ⟨r, hr, hrlt⟩ := exists_gt_digit_lt_sub_one hb x n
  refine ⟨r, hr, ?_⟩
  have hy := digit_lt hb0 y r
  dsimp only
  nlinarith

/-! ### Fundamental equivalence, marginals, and symmetry -/

private theorem mul_add_eq_mul_add_iff {a₁ a₂ c₁ c₂ : ℕ}
    (ha₂ : a₂ < b) (hc₂ : c₂ < b) :
    b * a₁ + a₂ = b * c₁ + c₂ ↔ a₁ = c₁ ∧ a₂ = c₂ := by
  constructor
  · intro h
    have hb0 : 0 < b := by omega
    have hq : (b * a₁ + a₂) / b = (b * c₁ + c₂) / b := congrArg (· / b) h
    have hr : (b * a₁ + a₂) % b = (b * c₁ + c₂) % b := congrArg (· % b) h
    rw [Nat.mul_add_div hb0, Nat.mul_add_div hb0, Nat.div_eq_of_lt ha₂, Nat.div_eq_of_lt hc₂,
      add_zero, add_zero] at hq
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt ha₂, Nat.mod_eq_of_lt hc₂] at hr
    exact ⟨hq, hr⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Two real numbers `x` and `y` are jointly normal in base `b ≥ 2` if and only if their base-`b`
interleaving is normal in base `b`. -/
theorem isJointlyNormalIn_iff_isNormalIn_interleave (hb : 2 ≤ b) :
    IsJointlyNormalIn b x y ↔ IsNormalIn b (interleave b x y) := by
  have hb0 : 0 < b := by omega
  rw [← isNormalIn_pow_iff hb (r := 2) (by omega)]
  have hpow : ∀ k : ℕ, ((b : ℝ) ^ (2 * k))⁻¹ = (((b ^ 2 : ℕ) : ℝ) ^ k)⁻¹ := fun k ↦ by
    push_cast
    rw [← pow_mul]
  constructor
  · intro h k w
    let u : Fin k → Fin b := fun j ↦
      ⟨(w j : ℕ) / b, Nat.div_lt_of_lt_mul (by rw [← sq]; exact (w j).isLt)⟩
    let v : Fin k → Fin b := fun j ↦ ⟨(w j : ℕ) % b, Nat.mod_lt _ hb0⟩
    have hcnt : ∀ N, blockCount (b ^ 2) (interleave b x y) w N = jointBlockCount b x y u v N := by
      classical
      intro N
      simp only [blockCount, jointBlockCount]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      refine and_congr_right fun _ ↦ ?_
      rw [← forall_and]
      refine forall_congr' fun j ↦ ?_
      rw [digit_sq_interleave hb x y (i + j)]
      have hw : (w j : ℕ) = b * u j + v j := (Nat.div_add_mod (w j : ℕ) b).symm
      rw [hw, mul_add_eq_mul_add_iff (digit_lt hb0 y _) (v j).isLt]
    simp_rw [hcnt, ← hpow k]
    exact h k u v
  · intro h k u v
    let w : Fin k → Fin (b ^ 2) := fun j ↦
      ⟨b * u j + v j, by nlinarith [(u j).isLt, (v j).isLt]⟩
    have hcnt : ∀ N, jointBlockCount b x y u v N = blockCount (b ^ 2) (interleave b x y) w N := by
      classical
      intro N
      simp only [blockCount, jointBlockCount]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      refine and_congr_right fun _ ↦ ?_
      rw [← forall_and]
      refine forall_congr' fun j ↦ ?_
      rw [digit_sq_interleave hb x y (i + j)]
      exact (mul_add_eq_mul_add_iff (digit_lt hb0 y _) (v j).isLt).symm
    simp_rw [hcnt, hpow k]
    exact h k w

/-- If `(x, y)` is jointly normal in base `b ≥ 2`, then `x` is normal in base `b`. -/
theorem IsJointlyNormalIn.left (hb : 2 ≤ b) (h : IsJointlyNormalIn b x y) : IsNormalIn b x := by
  have hz := (isJointlyNormalIn_iff_isNormalIn_interleave hb).1 h
  have hseq := hz.isNormalSeq_arithmeticProgression hb 0 (by omega : 0 < 2)
  rw [isNormalIn_iff_isNormalSeq]
  convert hseq using 1
  ext n
  simp [digit_interleave hb]

/-- If `(x, y)` is jointly normal in base `b ≥ 2`, then `y` is normal in base `b`. -/
theorem IsJointlyNormalIn.right (hb : 2 ≤ b) (h : IsJointlyNormalIn b x y) : IsNormalIn b y := by
  have hz := (isJointlyNormalIn_iff_isNormalIn_interleave hb).1 h
  have hseq := hz.isNormalSeq_arithmeticProgression hb 1 (by omega : 0 < 2)
  rw [isNormalIn_iff_isNormalSeq]
  convert hseq using 1
  ext n
  rw [digit_interleave hb, show 1 + 2 * n = 2 * n + 1 by omega, interleaveDigits_two_mul_add_one]

/-- Joint normality is symmetric. -/
theorem IsJointlyNormalIn.symm (_hb : 2 ≤ b) (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b y x := by
  intro k u v
  have hcnt : ∀ N, jointBlockCount b y x u v N = jointBlockCount b x y v u N := fun N ↦ by
    classical
    simp only [jointBlockCount]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ ↦ and_comm
  simp_rw [hcnt]
  exact h k v u

theorem IsJointlyAbsolutelyNormal.left (h : IsJointlyAbsolutelyNormal x y) :
    IsAbsolutelyNormal x :=
  fun b hb ↦ (h b hb).left hb

theorem IsJointlyAbsolutelyNormal.right (h : IsJointlyAbsolutelyNormal x y) :
    IsAbsolutelyNormal y :=
  fun b hb ↦ (h b hb).right hb

theorem IsJointlyAbsolutelyNormal.symm (h : IsJointlyAbsolutelyNormal x y) :
    IsJointlyAbsolutelyNormal y x :=
  fun b hb ↦ (h b hb).symm hb

/-! ### Constructive existence via even/odd digit splitting -/

/-- Splitting a base-`b` normal number `z` into its even-index and odd-index base-`b` digits yields
a pair that is jointly normal in base `b`. -/
theorem isJointlyNormalIn_even_odd (hb : 2 ≤ b) {z : ℝ} (hz : IsNormalIn b z) :
    IsJointlyNormalIn b
      (ofDigits fun n ↦ (⟨digit b z (2 * n), digit_lt (by omega) z (2 * n)⟩ : Fin b))
      (ofDigits fun n ↦ (⟨digit b z (2 * n + 1), digit_lt (by omega) z (2 * n + 1)⟩ : Fin b)) := by
  have hb0 : 0 < b := by omega
  have hb2 : 2 ≤ b ^ 2 := hb.trans (Nat.le_self_pow (by omega) b)
  have hz2 : IsNormalIn (b ^ 2) z := (isNormalIn_pow_iff hb (by omega)).2 hz
  have hzero : ∀ m, ∃ n, m < n ∧ digit b z (2 * n) = 0 ∧ digit b z (2 * n + 1) = 0 := by
    intro m
    have hz2' : IsNormalIn (b ^ 2) (z * ((b ^ 2 : ℕ) : ℝ) ^ (m + 1)) :=
      (isNormalIn_mul_pow_iff (m + 1)).2 hz2
    obtain ⟨i, hi⟩ := hz2'.isDisjunctiveIn 1 (fun _ ↦ ⟨0, by positivity⟩)
    have h0 : digit (b ^ 2) z (m + 1 + i) = 0 := by
      have := hi 0
      rw [Fin.val_zero, add_zero, ← digit_add] at this
      exact this
    have hblk := (forall_digit_eq_iff_digit_pow (x := z) hb0 (fun _ : Fin 2 ↦ ⟨0, hb0⟩) 0
      (m + 1 + i)).2 (by simpa [blockCode] using h0)
    refine ⟨m + 1 + i, by omega, ?_, ?_⟩
    · simpa [mul_comm] using hblk 0
    · simpa [mul_comm] using hblk 1
  have hx₀_dig : ∀ n, digit b
      (ofDigits fun k ↦ (⟨digit b z (2 * k), digit_lt (by omega) z (2 * k)⟩ : Fin b)) n =
      digit b z (2 * n) :=
    digit_ofDigits (by omega) _ fun m ↦ by
      obtain ⟨n, hn, h0, -⟩ := hzero m
      exact ⟨n, hn, by simp [h0]; omega⟩
  have hy₀_dig : ∀ n, digit b
      (ofDigits fun k ↦ (⟨digit b z (2 * k + 1), digit_lt (by omega) z (2 * k + 1)⟩ : Fin b)) n =
      digit b z (2 * n + 1) :=
    digit_ofDigits (by omega) _ fun m ↦ by
      obtain ⟨n, hn, -, h1⟩ := hzero m
      exact ⟨n, hn, by simp [h1]; omega⟩
  rw [isJointlyNormalIn_iff_isNormalIn_interleave hb, isNormalIn_iff_isNormalSeq]
  have heq : digit b (interleave b
      (ofDigits fun n ↦ (⟨digit b z (2 * n), digit_lt (by omega) z (2 * n)⟩ : Fin b))
      (ofDigits fun n ↦ (⟨digit b z (2 * n + 1), digit_lt (by omega) z (2 * n + 1)⟩ : Fin b))) =
      digit b z := by
    funext n
    rw [digit_interleave hb, interleaveDigits]
    split_ifs with hmod
    · rw [hx₀_dig, show 2 * (n / 2) = n by omega]
    · rw [hy₀_dig, show 2 * (n / 2) + 1 = n by omega]
  rw [heq]
  exact isNormalIn_iff_isNormalSeq.1 hz

/-- For every base `b ≥ 2`, there exists a pair of real numbers that are jointly normal in
base `b`. -/
theorem exists_isJointlyNormalIn (hb : 2 ≤ b) : ∃ x y : ℝ, IsJointlyNormalIn b x y := by
  have : NeZero b := ⟨by omega⟩
  exact ⟨_, _, isJointlyNormalIn_even_odd hb (isNormalIn_copelandErdos hb)⟩

/-! ### Metric ubiquity on `ℝ × ℝ` -/

private theorem exists_nat_div_pow_mod_eq {B : ℕ} (hB : 0 < B) (m : ℕ) {d : ℕ → ℕ}
    (hd : ∀ j < m, d j < B) :
    ∃ u < B ^ m, ∀ j < m, u / B ^ j % B = d j := by
  induction m generalizing d with
  | zero => exact ⟨0, by simp, fun j hj ↦ by omega⟩
  | succ m ih =>
    obtain ⟨u', hu', hdig⟩ := ih (d := fun j ↦ d (j + 1)) fun j hj ↦ hd (j + 1) (by omega)
    refine ⟨d 0 + B * u', ?_, fun j hj ↦ ?_⟩
    · have hd0 : d 0 < B := hd 0 (by omega)
      calc d 0 + B * u' < B + B * u' := by omega
        _ = B * (u' + 1) := by ring
        _ ≤ B * B ^ m := Nat.mul_le_mul_left B hu'
        _ = B ^ (m + 1) := (pow_succ' B m).symm
    · rcases j with _ | j
      · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0 (by omega))]
      · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
          Nat.div_eq_of_lt (hd 0 (by omega)), zero_add]
        exact hdig j (by omega)

private theorem nat_eq_of_forall_div_pow_mod_eq {B : ℕ} (_hB : 0 < B) {m u v : ℕ}
    (hu : u < B ^ m) (hv : v < B ^ m) (h : ∀ j < m, u / B ^ j % B = v / B ^ j % B) :
    u = v := by
  induction m generalizing u v with
  | zero =>
    simp only [pow_zero] at hu hv
    omega
  | succ m ih =>
    have h0 : u % B = v % B := by simpa using h 0 (by omega)
    have hdiv : u / B = v / B := by
      refine ih (Nat.div_lt_of_lt_mul (by rwa [← pow_succ']))
        (Nat.div_lt_of_lt_mul (by rwa [← pow_succ'])) fun j hj ↦ ?_
      have := h (j + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    rw [← Nat.div_add_mod u B, ← Nat.div_add_mod v B, hdiv, h0]

private theorem measurable_interleave (b : ℕ) :
    Measurable fun p : ℝ × ℝ ↦ interleave b p.1 p.2 := by
  by_cases hb : 0 < b
  · have hterm : ∀ n, Measurable fun p : ℝ × ℝ ↦
        ofDigitsTerm (fun k ↦ (⟨interleaveDigits b p.1 p.2 k,
          interleaveDigits_lt hb p.1 p.2 k⟩ : Fin b)) n := by
      intro n
      simp only [ofDigitsTerm, interleaveDigits]
      split_ifs
      · exact ((measurable_from_top.comp ((measurable_digit b (n / 2)).comp measurable_fst)).mul
          measurable_const)
      · exact ((measurable_from_top.comp ((measurable_digit b (n / 2)).comp measurable_snd)).mul
          measurable_const)
    refine measurable_of_tendsto_metrizable
      (f := fun N (p : ℝ × ℝ) ↦ ∑ n ∈ Finset.range N,
        ofDigitsTerm (fun k ↦ (⟨interleaveDigits b p.1 p.2 k,
          interleaveDigits_lt hb p.1 p.2 k⟩ : Fin b)) n)
      (fun N ↦ Finset.measurable_sum _ fun n _ ↦ hterm n)
      (tendsto_pi_nhds.2 fun p ↦ ?_)
    simp only [interleave, hb, ↓reduceDIte]
    exact summable_ofDigitsTerm.hasSum.tendsto_sum_nat
  · have : (fun p : ℝ × ℝ ↦ interleave b p.1 p.2) = fun _ ↦ 0 := by
      funext p
      simp [interleave, hb]
    rw [this]
    exact measurable_const

private theorem floor_mul_pow_eq_iff_mem_Ico {B : ℕ} (hB : 0 < B) (m c : ℕ) (_hc : c < B ^ m)
    {z : ℝ} (hz : z ∈ Ico (0 : ℝ) 1) :
    ⌊z * (B : ℝ) ^ m⌋₊ = c ↔ z ∈ Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m) := by
  have hBm : (0 : ℝ) < (B : ℝ) ^ m := by positivity
  simp only [mem_Ico]
  constructor
  · intro h
    rw [Nat.floor_eq_iff (mul_nonneg hz.1 hBm.le)] at h
    exact ⟨(div_le_iff₀ hBm).2 h.1, (lt_div_iff₀ hBm).2 h.2⟩
  · rintro ⟨h0, h1⟩
    rw [div_le_iff₀ hBm] at h0
    rw [lt_div_iff₀ hBm] at h1
    exact (Nat.floor_eq_iff (mul_nonneg hz.1 hBm.le)).2 ⟨h0, h1⟩

private theorem measurePreserving_interleave (hb : 2 ≤ b) :
    MeasurePreserving (fun p : ℝ × ℝ ↦ interleave b p.1 p.2)
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  have hb0 : 0 < b := by omega
  set μ₀ : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)
  set f : ℝ × ℝ → ℝ := fun p ↦ interleave b p.1 p.2
  have hf : Measurable f := measurable_interleave b
  refine ⟨hf, ?_⟩
  set B : ℕ := b ^ 2
  have hB : 0 < B := pow_pos hb0 2
  have hB1 : (1 : ℝ) < B := by
    have : 1 < B := by dsimp only [B]; nlinarith
    exact_mod_cast this
  -- Step 1: equality on `b ^ 2`-adic intervals `[c / B ^ m, (c + 1) / B ^ m)`
  have hadic : ∀ (m c : ℕ), c < B ^ m →
      Measure.map f (μ₀.prod μ₀) (Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m)) =
        μ₀ (Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m)) := by
    intro m c hc
    obtain ⟨c₁, hc₁, hdig₁⟩ := exists_nat_div_pow_mod_eq hb0 m
      (d := fun j ↦ (c / B ^ j % B) / b) fun j _ ↦
        Nat.div_lt_of_lt_mul (by rw [← sq]; exact Nat.mod_lt _ hB)
    obtain ⟨c₂, hc₂, hdig₂⟩ := exists_nat_div_pow_mod_eq hb0 m
      (d := fun j ↦ (c / B ^ j % B) % b) fun j _ ↦ Nat.mod_lt _ hb0
    have hpre : f ⁻¹' Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m) ∩
        (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) =
        ({x : ℝ | ⌊x * (b : ℝ) ^ m⌋₊ = c₁} ×ˢ {y : ℝ | ⌊y * (b : ℝ) ^ m⌋₊ = c₂}) ∩
          (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := by
      ext ⟨x, y⟩
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq]
      refine and_congr_left fun ⟨hx, hy⟩ ↦ ?_
      have hfz : f (x, y) ∈ Ico (0 : ℝ) 1 := interleave_mem_Ico hb x y
      rw [← floor_mul_pow_eq_iff_mem_Ico hB m c hc hfz]
      have hflz_lt : ⌊f (x, y) * (B : ℝ) ^ m⌋₊ < B ^ m := by
        rw [Nat.floor_lt (mul_nonneg hfz.1 (by positivity))]
        push_cast
        exact mul_lt_of_lt_one_left (by positivity) hfz.2
      have hflx_lt : ⌊x * (b : ℝ) ^ m⌋₊ < b ^ m := by
        rw [Nat.floor_lt (mul_nonneg hx.1 (by positivity))]
        push_cast
        exact mul_lt_of_lt_one_left (by positivity) hx.2
      have hfly_lt : ⌊y * (b : ℝ) ^ m⌋₊ < b ^ m := by
        rw [Nat.floor_lt (mul_nonneg hy.1 (by positivity))]
        push_cast
        exact mul_lt_of_lt_one_left (by positivity) hy.2
      constructor
      · intro hfl
        have hxy : ∀ i < m, digit b x i = c₁ / b ^ (m - 1 - i) % b ∧
            digit b y i = c₂ / b ^ (m - 1 - i) % b := by
          intro i hi
          have h1 : digit B (f (x, y)) i = c / B ^ (m - 1 - i) % B := by
            rw [digit_eq_floor_div_mod hB hfz hi, hfl]
          rw [digit_sq_interleave hb x y i] at h1
          have h2 : c / B ^ (m - 1 - i) % B =
              b * (c₁ / b ^ (m - 1 - i) % b) + c₂ / b ^ (m - 1 - i) % b := by
            rw [hdig₁ (m - 1 - i) (by omega), hdig₂ (m - 1 - i) (by omega), Nat.div_add_mod]
          rw [h2] at h1
          exact (mul_add_eq_mul_add_iff (digit_lt hb0 y i) (Nat.mod_lt _ hb0)).1 h1
        constructor
        · refine nat_eq_of_forall_div_pow_mod_eq hb0 hflx_lt hc₁ fun j hj ↦ ?_
          have := (hxy (m - 1 - j) (by omega)).1
          rw [digit_eq_floor_div_mod (n := m) hb0 hx (by omega),
            show m - 1 - (m - 1 - j) = j by omega] at this
          exact this
        · refine nat_eq_of_forall_div_pow_mod_eq hb0 hfly_lt hc₂ fun j hj ↦ ?_
          have := (hxy (m - 1 - j) (by omega)).2
          rw [digit_eq_floor_div_mod (n := m) hb0 hy (by omega),
            show m - 1 - (m - 1 - j) = j by omega] at this
          exact this
      · rintro ⟨hxfl, hyfl⟩
        refine nat_eq_of_forall_div_pow_mod_eq hB hflz_lt hc fun j hj ↦ ?_
        have hdig_z := digit_eq_floor_div_mod (n := m) hB hfz (i := m - 1 - j) (by omega)
        rw [show m - 1 - (m - 1 - j) = j by omega] at hdig_z
        rw [← hdig_z, digit_sq_interleave hb x y (m - 1 - j),
          digit_eq_floor_div_mod (n := m) hb0 hx (by omega),
          digit_eq_floor_div_mod (n := m) hb0 hy (by omega),
          show m - 1 - (m - 1 - j) = j by omega, hxfl, hyfl, hdig₁ j hj, hdig₂ j hj,
          Nat.div_add_mod]
    have hIco : Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m) =
        {z : ℝ | ⌊z * (B : ℝ) ^ m⌋₊ = c} ∩ Ico (0 : ℝ) 1 := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro hz
        have hzIco : z ∈ Ico (0 : ℝ) 1 := by
          have hc1 : (c : ℝ) + 1 ≤ (B : ℝ) ^ m := by exact_mod_cast hc
          have hBm : (0 : ℝ) < (B : ℝ) ^ m := by positivity
          exact ⟨le_trans (by positivity) hz.1, lt_of_lt_of_le hz.2 ((div_le_one hBm).2 hc1)⟩
        exact ⟨(floor_mul_pow_eq_iff_mem_Ico hB m c hc hzIco).2 hz, hzIco⟩
      · rintro ⟨hfl, hzIco⟩
        exact (floor_mul_pow_eq_iff_mem_Ico hB m c hc hzIco).1 hfl
    have hprod_eq : (μ₀.prod μ₀)
        (f ⁻¹' Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m)) =
        (μ₀.prod μ₀) ({x : ℝ | ⌊x * (b : ℝ) ^ m⌋₊ = c₁} ×ˢ {y : ℝ | ⌊y * (b : ℝ) ^ m⌋₊ = c₂}) := by
      rw [Measure.prod_restrict, Measure.restrict_apply' (measurableSet_Ico.prod measurableSet_Ico),
        hpre, ← Measure.restrict_apply' (measurableSet_Ico.prod measurableSet_Ico)]
    rw [Measure.map_apply hf measurableSet_Ico, hprod_eq, Measure.prod_prod,
      volume_restrict_floor_mul_pow_eq hb0 m hc₁, volume_restrict_floor_mul_pow_eq hb0 m hc₂,
      ← ENNReal.mul_inv (Or.inl (pow_ne_zero _ (by exact_mod_cast hb0.ne')))
        (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top b))),
      ← mul_pow, ← sq, ← Nat.cast_pow, show B = b ^ 2 from rfl,
      ← volume_restrict_floor_mul_pow_eq hB m hc, Measure.restrict_apply' measurableSet_Ico,
      ← hIco, Measure.restrict_apply' measurableSet_Ico,
      inter_eq_left.2 (by
        intro z hz
        rw [hIco] at hz
        exact hz.2)]
  -- Step 2: equality on `[0, k / B ^ m)` for `k ≤ B ^ m`
  have hprefix : ∀ (m k : ℕ), k ≤ B ^ m →
      Measure.map f (μ₀.prod μ₀) (Ico (0 : ℝ) ((k : ℝ) / (B : ℝ) ^ m)) =
        μ₀ (Ico (0 : ℝ) ((k : ℝ) / (B : ℝ) ^ m)) := by
    intro m k hk
    have hunion : Ico (0 : ℝ) ((k : ℝ) / (B : ℝ) ^ m) =
        ⋃ c ∈ Finset.range k, Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m) := by
      have hBm : (0 : ℝ) < (B : ℝ) ^ m := by positivity
      ext z
      simp only [mem_Ico, mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨hz0, hzk⟩
        refine ⟨⌊z * (B : ℝ) ^ m⌋₊, ?_, ?_, ?_⟩
        · rw [Nat.floor_lt (mul_nonneg hz0 hBm.le)]
          exact (lt_div_iff₀ hBm).1 hzk
        · exact (div_le_iff₀ hBm).2 (Nat.floor_le (mul_nonneg hz0 hBm.le))
        · exact (lt_div_iff₀ hBm).2 (Nat.lt_floor_add_one _)
      · rintro ⟨c, hck, h0, h1⟩
        refine ⟨le_trans (by positivity) h0, lt_of_lt_of_le h1 ?_⟩
        gcongr
        exact_mod_cast hck
    have hdisj : Set.PairwiseDisjoint (Finset.range k : Set ℕ) fun c ↦
        Ico ((c : ℝ) / (B : ℝ) ^ m) (((c : ℝ) + 1) / (B : ℝ) ^ m) := by
      intro c₁ _ c₂ _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro z hz1 hz2
      have hBm : (0 : ℝ) < (B : ℝ) ^ m := by positivity
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hle : ((c₁ : ℝ) + 1) / (B : ℝ) ^ m ≤ (c₂ : ℝ) / (B : ℝ) ^ m := by
          gcongr
          exact_mod_cast hlt
        linarith [hz1.2, hz2.1]
      · have hle : ((c₂ : ℝ) + 1) / (B : ℝ) ^ m ≤ (c₁ : ℝ) / (B : ℝ) ^ m := by
          gcongr
          exact_mod_cast hlt
        linarith [hz2.2, hz1.1]
    rw [hunion, measure_biUnion_finset hdisj (fun _ _ ↦ measurableSet_Ico),
      measure_biUnion_finset hdisj (fun _ _ ↦ measurableSet_Ico)]
    refine Finset.sum_congr rfl fun c hc ↦ hadic m c (lt_of_lt_of_le (Finset.mem_range.1 hc) hk)
  -- Step 3: equality on `[0, a)` for all `a ∈ [0, 1]`
  have hIco_zero : ∀ a ∈ Icc (0 : ℝ) 1,
      Measure.map f (μ₀.prod μ₀) (Ico (0 : ℝ) a) = μ₀ (Ico (0 : ℝ) a) := by
    intro a ha
    let q : ℕ → ℝ := fun m ↦ (⌊a * (B : ℝ) ^ m⌋₊ : ℝ) / (B : ℝ) ^ m
    have hmono : Monotone fun m ↦ Ico (0 : ℝ) (q m) := by
      refine monotone_nat_of_le_succ fun m ↦ Ico_subset_Ico_right ?_
      have hBm : (0 : ℝ) < (B : ℝ) ^ m := by positivity
      have hle : ⌊a * (B : ℝ) ^ m⌋₊ * B ≤ ⌊a * (B : ℝ) ^ (m + 1)⌋₊ := by
        refine Nat.le_floor ?_
        push_cast
        rw [pow_succ]
        have := Nat.floor_le (mul_nonneg ha.1 hBm.le)
        nlinarith [show (0 : ℝ) ≤ B by positivity]
      simp only [q]
      rw [div_le_div_iff₀ hBm (by positivity), pow_succ]
      have hle' : (⌊a * (B : ℝ) ^ m⌋₊ : ℝ) * B ≤ (⌊a * ((B : ℝ) ^ m * B)⌋₊ : ℝ) := by
        rw [← pow_succ]
        exact_mod_cast hle
      nlinarith
    have hunion : Ico (0 : ℝ) a = ⋃ m : ℕ, Ico (0 : ℝ) (q m) := by
      ext z
      simp only [mem_Ico, mem_iUnion]
      constructor
      · rintro ⟨hz0, hza⟩
        obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hza) (inv_lt_one_of_one_lt₀ hB1)
        refine ⟨m, hz0, ?_⟩
        have hBm : (0 : ℝ) < (B : ℝ) ^ m := by positivity
        rw [inv_pow] at hm
        have h1 : 1 < (a - z) * (B : ℝ) ^ m := by
          have := mul_lt_mul_of_pos_right hm hBm
          rwa [inv_mul_cancel₀ hBm.ne'] at this
        have h2 : a * (B : ℝ) ^ m < (⌊a * (B : ℝ) ^ m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        exact (lt_div_iff₀ hBm).2 (by linarith)
      · rintro ⟨m, hz0, hzq⟩
        have hBm : (0 : ℝ) < (B : ℝ) ^ m := by positivity
        have hle : q m ≤ a := (div_le_iff₀ hBm).2 (Nat.floor_le (mul_nonneg ha.1 hBm.le))
        exact ⟨hz0, lt_of_lt_of_le hzq hle⟩
    rw [hunion, hmono.measure_iUnion, hmono.measure_iUnion]
    refine iSup_congr fun m ↦ hprefix m ⌊a * (B : ℝ) ^ m⌋₊ ?_
    calc ⌊a * (B : ℝ) ^ m⌋₊ ≤ ⌊((B ^ m : ℕ) : ℝ)⌋₊ :=
          Nat.floor_mono (by push_cast; nlinarith [ha.2, show (0 : ℝ) ≤ (B : ℝ) ^ m by positivity])
      _ = B ^ m := Nat.floor_natCast _
  -- Step 4: apply `Measure.ext_of_Ico`
  have : IsProbabilityMeasure (Measure.map f (μ₀.prod μ₀)) :=
    ⟨by rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ, measure_univ]⟩
  refine Measure.ext_of_Ico _ _ fun u v huv ↦ ?_
  have hsupp : ∀ (s : Set ℝ), MeasurableSet s →
      Measure.map f (μ₀.prod μ₀) s = Measure.map f (μ₀.prod μ₀) (s ∩ Ico 0 1) := by
    intro s hs
    rw [Measure.map_apply hf hs, Measure.map_apply hf (hs.inter measurableSet_Ico)]
    congr 1
    ext p
    exact ⟨fun hp ↦ ⟨hp, interleave_mem_Ico hb p.1 p.2⟩, fun hp ↦ hp.1⟩
  rw [hsupp _ measurableSet_Ico, Measure.restrict_apply' measurableSet_Ico]
  rw [show volume (Ico u v ∩ Ico 0 1) = μ₀ (Ico u v ∩ Ico 0 1) from by
    rw [Measure.restrict_apply' measurableSet_Ico, inter_assoc, inter_self]]
  rw [Ico_inter_Ico]
  by_cases hlt : max u 0 < min v 1
  · have h0 : 0 ≤ max u 0 := le_max_right _ _
    have h1 : min v 1 ≤ 1 := min_le_right _ _
    have ha : max u 0 ∈ Icc (0 : ℝ) 1 := ⟨h0, le_trans hlt.le h1⟩
    have hb_mem : min v 1 ∈ Icc (0 : ℝ) 1 := ⟨le_trans h0 hlt.le, h1⟩
    have hdiff : Ico (max u 0) (min v 1) = Ico (0 : ℝ) (min v 1) \ Ico (0 : ℝ) (max u 0) := by
      ext z
      simp only [mem_Ico, Set.mem_sdiff, not_and, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨le_trans h0 h1, h2⟩, fun _ ↦ h1⟩
      · rintro ⟨⟨hz0, hz2⟩, hz1⟩
        exact ⟨hz1 hz0, hz2⟩
    have hsub : Ico (0 : ℝ) (max u 0) ⊆ Ico (0 : ℝ) (min v 1) := Ico_subset_Ico_right hlt.le
    rw [hdiff,
      measure_sdiff hsub nullMeasurableSet_Ico (measure_ne_top _ _),
      measure_sdiff hsub nullMeasurableSet_Ico (measure_ne_top _ _),
      hIco_zero _ hb_mem, hIco_zero _ ha]
  · rw [Ico_eq_empty hlt, measure_empty, measure_empty]

private theorem ae_prod_of_ae_restrict_Ico {p : ℝ × ℝ → Prop}
    (hp : ∀ x y (m n : ℤ), p (x + m, y + n) ↔ p (x, y))
    (h : ∀ᵐ q : ℝ × ℝ ∂((volume.restrict (Ico (0 : ℝ) 1)).prod
      (volume.restrict (Ico (0 : ℝ) 1))), p q) :
    ∀ᵐ q : ℝ × ℝ ∂(volume.prod volume), p q := by
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ico.prod measurableSet_Ico),
    ae_iff] at h
  rw [ae_iff]
  have hnull : ∀ m n : ℤ,
      (volume.prod volume)
        ((fun q : ℝ × ℝ ↦ (q.1 + (-m : ℝ), q.2 + (-n : ℝ))) ⁻¹'
          {q : ℝ × ℝ | ¬(q ∈ Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1 → p q)}) = 0 := by
    intro m n
    have hmp : MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1 + (-m : ℝ), q.2 + (-n : ℝ)))
        (volume.prod volume) (volume.prod volume) :=
      (measurePreserving_add_right volume (-m : ℝ)).prod
        (measurePreserving_add_right volume (-n : ℝ))
    exact hmp.quasiMeasurePreserving.preimage_null h
  refine measure_mono_null
    (t := ⋃ m : ℤ, ⋃ n : ℤ,
      (fun q : ℝ × ℝ ↦ (q.1 + (-m : ℝ), q.2 + (-n : ℝ))) ⁻¹'
        {q : ℝ × ℝ | ¬(q ∈ Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1 → p q)})
    ?_ (measure_iUnion_null fun m ↦ measure_iUnion_null fun n ↦ hnull m n)
  rintro ⟨x, y⟩ hxy
  simp only [mem_iUnion, mem_preimage, mem_ofPred_eq, not_imp, mem_prod]
  refine ⟨⌊x⌋, ⌊y⌋, ⟨?_, ?_⟩, fun hp' ↦ hxy ?_⟩
  · rw [← sub_eq_add_neg]
    exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  · rw [← sub_eq_add_neg]
    exact ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  · have := (hp (x + -⌊x⌋) (y + -⌊y⌋) ⌊x⌋ ⌊y⌋).2 hp'
    simpa using this

/-- Almost every pair `(x, y) ∈ ℝ × ℝ` (with respect to two-dimensional Lebesgue measure) is
jointly normal in base `b ≥ 2`. -/
theorem ae_isJointlyNormalIn (hb : 2 ≤ b) :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), IsJointlyNormalIn b p.1 p.2 := by
  have hae : ∀ᵐ z : ℝ ∂(volume.restrict (Ico (0 : ℝ) 1)), IsNormalIn b z :=
    ae_restrict_of_ae (ae_isNormalIn (by omega))
  have hae_inter : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ico (0 : ℝ) 1)).prod
      (volume.restrict (Ico (0 : ℝ) 1))), IsJointlyNormalIn b p.1 p.2 :=
    ((measurePreserving_interleave hb).quasiMeasurePreserving.ae hae).mono fun p hp ↦
      (isJointlyNormalIn_iff_isNormalIn_interleave hb).2 hp
  refine ae_prod_of_ae_restrict_Ico (fun x y m n ↦ ?_) hae_inter
  rw [isJointlyNormalIn_add_intCast_left_iff, isJointlyNormalIn_add_intCast_right_iff]

/-- Almost every pair `(x, y) ∈ ℝ × ℝ` (with respect to two-dimensional Lebesgue measure) is
jointly absolutely normal. -/
theorem ae_isJointlyAbsolutelyNormal :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), IsJointlyAbsolutelyNormal p.1 p.2 := by
  simp only [IsJointlyAbsolutelyNormal]
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · exact (ae_isJointlyNormalIn hb).mono fun p hp _ ↦ hp
  · exact Eventually.of_forall fun p h ↦ absurd h hb

/-- Jointly absolutely normal pairs exist. -/
theorem exists_isJointlyAbsolutelyNormal : ∃ x y : ℝ, IsJointlyAbsolutelyNormal x y :=
  let ⟨⟨x, y⟩, h⟩ := ae_isJointlyAbsolutelyNormal.exists
  ⟨x, y, h⟩

/-! ### Correlated interleaving: simple normality preserved, joint normality destroyed -/

/-- Interleaving the base-`b` digits of any two simply normal numbers preserves simple normality
in base `b`. -/
theorem isSimplyNormalIn_interleave_of_isSimplyNormalIn (hb : 2 ≤ b)
    (hx : IsSimplyNormalIn b x) (hy : IsSimplyNormalIn b y) :
    IsSimplyNormalIn b (interleave b x y) := by
  classical
  set z : ℝ := interleave b x y
  intro c
  have hcard_even : ∀ M,
      ((Finset.range (2 * M)).filter fun i ↦ interleaveDigits b x y i = c).card =
        blockCount b x (fun _ : Fin 1 ↦ c) M + blockCount b y (fun _ : Fin 1 ↦ c) M := by
    intro M
    set A := (Finset.range M).filter fun j ↦ digit b x j = c
    set B := (Finset.range M).filter fun j ↦ digit b y j = c
    have hA : blockCount b x (fun _ : Fin 1 ↦ c) M = A.card := by simp [blockCount, A]
    have hB : blockCount b y (fun _ : Fin 1 ↦ c) M = B.card := by simp [blockCount, B]
    rw [hA, hB]
    have hunion : ((Finset.range (2 * M)).filter fun i ↦ interleaveDigits b x y i = c) =
        A.image (fun j ↦ 2 * j) ∪ B.image (fun j ↦ 2 * j + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image, A, B]
      constructor
      · rintro ⟨hi, hdig⟩
        rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
        · left
          refine ⟨j, ⟨by omega, ?_⟩, rfl⟩
          simpa using hdig
        · right
          refine ⟨j, ⟨by omega, ?_⟩, rfl⟩
          simpa using hdig
      · rintro (⟨j, ⟨hj, hdig⟩, rfl⟩ | ⟨j, ⟨hj, hdig⟩, rfl⟩)
        · exact ⟨by omega, by simpa using hdig⟩
        · exact ⟨by omega, by simpa using hdig⟩
    have hdisj : Disjoint (A.image fun j ↦ 2 * j) (B.image fun j ↦ 2 * j + 1) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [Finset.mem_image] at hi1 hi2
      obtain ⟨j₁, _, rfl⟩ := hi1
      obtain ⟨j₂, _, h⟩ := hi2
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h ↦ by omega),
      Finset.card_image_of_injective _ (fun _ _ h ↦ by omega)]
  have hbounds : ∀ N,
      blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) + blockCount b y (fun _ : Fin 1 ↦ c) (N / 2) ≤
        blockCount b z (fun _ : Fin 1 ↦ c) N ∧
      blockCount b z (fun _ : Fin 1 ↦ c) N ≤
        blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) +
          blockCount b y (fun _ : Fin 1 ↦ c) (N / 2) + 1 := by
    intro N
    have hbz : blockCount b z (fun _ : Fin 1 ↦ c) N =
        ((Finset.range N).filter fun i ↦ interleaveDigits b x y i = c).card := by
      simp [blockCount, z, digit_interleave hb]
    rw [hbz, ← hcard_even (N / 2)]
    constructor
    · exact Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.range_subset_range.2 (by omega)))
    · have hsub : ((Finset.range N).filter fun i ↦ interleaveDigits b x y i = c) ⊆
          ((Finset.range (2 * (N / 2))).filter fun i ↦ interleaveDigits b x y i = c) ∪
            {2 * (N / 2)} := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
          Finset.mem_singleton] at hi ⊢
        by_cases hlt : i < 2 * (N / 2)
        · exact Or.inl ⟨hlt, hi.2⟩
        · exact Or.inr (by omega)
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by simp))
  have hratio : Tendsto (fun N : ℕ ↦ ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (2 : ℝ)⁻¹) := by
    simpa using tendsto_div_natCast_div (k := 2) (by omega) 0
  have hmain : Tendsto (fun N : ℕ ↦
      ((blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) : ℝ) +
        (blockCount b y (fun _ : Fin 1 ↦ c) (N / 2) : ℝ)) / N) atTop (𝓝 (b : ℝ)⁻¹) := by
    have h1 := ((hx c).add (hy c)).comp (Nat.tendsto_div_const_atTop (by omega : 2 ≠ 0))
    have h2 := h1.mul hratio
    have hlim : ((b : ℝ)⁻¹ + (b : ℝ)⁻¹) * (2 : ℝ)⁻¹ = (b : ℝ)⁻¹ := by ring
    rw [hlim] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hdiv : ((N / 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 0 < N / 2 by omega).ne'
    simp only [Function.comp_apply]
    field_simp
  have hup : Tendsto (fun N : ℕ ↦
      ((blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) : ℝ) +
        (blockCount b y (fun _ : Fin 1 ↦ c) (N / 2) : ℝ) + 1) / N) atTop (𝓝 (b : ℝ)⁻¹) := by
    have h := hmain.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    rw [add_zero] at h
    exact h.congr fun N ↦ (add_div _ _ _).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hup ?_ ?_ <;>
    refine Eventually.of_forall fun N ↦ div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  · exact_mod_cast (hbounds N).1
  · exact_mod_cast (hbounds N).2

/-- If a pair of blocks `(u, v)` never occurs simultaneously in `x` and `y`, then `(x, y)` is not
jointly normal in base `b`. -/
theorem not_isJointlyNormalIn_of_forall_not {k : ℕ} (hb : 0 < b) (u v : Fin k → Fin b)
    (huv : ∀ i, ¬((∀ j : Fin k, digit b x (i + j) = u j) ∧
      (∀ j : Fin k, digit b y (i + j) = v j))) :
    ¬ IsJointlyNormalIn b x y := by
  intro h
  have h0 : ∀ N, jointBlockCount b x y u v N = 0 := fun N ↦ by
    classical
    rw [jointBlockCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ hi ↦ huv i hi
  have ht := h k u v
  simp only [h0, Nat.cast_zero, zero_div] at ht
  have hbk : ((b : ℝ) ^ (2 * k))⁻¹ ≠ 0 := by positivity
  exact hbk (tendsto_nhds_unique tendsto_const_nhds ht).symm

/-- No number is jointly normal with itself in base `b ≥ 2`. -/
theorem not_isJointlyNormalIn_self (hb : 2 ≤ b) (_hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x x := by
  refine not_isJointlyNormalIn_of_forall_not (by omega)
    (fun _ : Fin 1 ↦ ⟨0, by omega⟩) (fun _ : Fin 1 ↦ ⟨1, by omega⟩) fun i hi ↦ ?_
  have h0 := hi.1 0
  have h1 := hi.2 0
  simp only [Fin.val_zero, add_zero] at h0 h1
  omega

/-- Self-interleaving a base-`b` normal number destroys normality in base `b`. -/
theorem not_isNormalIn_interleave_self (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x x) :=
  (isJointlyNormalIn_iff_isNormalIn_interleave hb).not.1 (not_isJointlyNormalIn_self hb hx)

/-- A base-`b` normal number is never jointly normal with any digit-permuted version of itself. -/
theorem not_isJointlyNormalIn_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x
      (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩) := by
  have hb0 : 0 < b := by omega
  set d₀ : Fin b := ⟨0, hb0⟩
  set v₀ : Fin b := if (σ d₀ : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, hb0⟩
  have hv₀ : (v₀ : ℕ) ≠ (σ d₀ : ℕ) := by
    simp only [v₀]
    split_ifs with h
    · simp [h]
    · exact Ne.symm h
  refine not_isJointlyNormalIn_of_forall_not hb0 (fun _ : Fin 1 ↦ d₀) (fun _ : Fin 1 ↦ v₀)
    fun i hi ↦ ?_
  have h1 := hi.1 0
  have h2 := hi.2 0
  simp only [Fin.val_zero, add_zero] at h1 h2
  rw [digit_ofDigits_of_isNormalSeq hb (isNormalSeq_comp_equiv hb σ hx) i] at h2
  have hfin : (⟨digit b x i, digit_lt hb0 x i⟩ : Fin b) = d₀ := Fin.ext h1
  rw [hfin] at h2
  exact hv₀ h2.symm

/-- Interleaving a base-`b` normal number with a digit-permuted copy of itself destroys normality
in base `b`. -/
theorem not_isNormalIn_interleave_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩)) :=
  (isJointlyNormalIn_iff_isNormalIn_interleave hb).not.1
    (not_isJointlyNormalIn_comp_equiv hb σ hx)

/-- Interleaving a base-`b` normal number with a digit-permuted copy of itself preserves simple
normality in base `b`. -/
theorem isSimplyNormalIn_interleave_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    IsSimplyNormalIn b
      (interleave b x (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩)) :=
  isSimplyNormalIn_interleave_of_isSimplyNormalIn hb hx.isSimplyNormalIn
    (isNormalIn_ofDigits_comp_equiv hb σ hx).isSimplyNormalIn

/-- A base-`b` normal number `x` is never jointly normal with `-x`. -/
theorem not_isJointlyNormalIn_neg (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x (-x) := by
  have hb0 : 0 < b := by omega
  have hirr := hx.irrational hb
  refine not_isJointlyNormalIn_of_forall_not hb0
    (fun _ : Fin 1 ↦ ⟨0, hb0⟩) (fun _ : Fin 1 ↦ ⟨0, hb0⟩) fun i hi ↦ ?_
  have h1 := hi.1 0
  have h2 := hi.2 0
  simp only [Fin.val_zero, add_zero] at h1 h2
  rw [digit_neg hb0 hirr i, h1] at h2
  omega

/-- Interleaving a base-`b` normal number `x` with `-x` destroys normality in base `b`. -/
theorem not_isNormalIn_interleave_neg (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x (-x)) :=
  (isJointlyNormalIn_iff_isNormalIn_interleave hb).not.1 (not_isJointlyNormalIn_neg hb hx)

/-- Interleaving a base-`b` normal number `x` with `-x` preserves simple normality in base `b`. -/
theorem isSimplyNormalIn_interleave_neg (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsSimplyNormalIn b (interleave b x (-x)) :=
  isSimplyNormalIn_interleave_of_isSimplyNormalIn hb hx.isSimplyNormalIn
    (hx.neg hb).isSimplyNormalIn

/-- A base-`b` normal number `x` is never jointly normal with `b ^ m * x`. -/
theorem not_isJointlyNormalIn_mul_pow (hb : 2 ≤ b) (m : ℕ) (_hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x ((b : ℝ) ^ m * x) := by
  have hb0 : 0 < b := by omega
  refine not_isJointlyNormalIn_of_forall_not hb0
    (fun _ : Fin (m + 1) ↦ ⟨0, hb0⟩) (fun _ : Fin (m + 1) ↦ ⟨1, by omega⟩) fun i hi ↦ ?_
  have h1 := hi.1 ⟨m, Nat.lt_succ_self m⟩
  have h2 := hi.2 ⟨0, Nat.zero_lt_succ m⟩
  simp only [add_zero] at h1 h2
  rw [mul_comm, ← digit_add, add_comm m i] at h2
  omega

/-- Interleaving a base-`b` normal number `x` with `b ^ m * x` destroys normality in base `b`. -/
theorem not_isNormalIn_interleave_mul_pow (hb : 2 ≤ b) (m : ℕ) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x ((b : ℝ) ^ m * x)) :=
  (isJointlyNormalIn_iff_isNormalIn_interleave hb).not.1 (not_isJointlyNormalIn_mul_pow hb m hx)

/-- Interleaving a base-`b` normal number `x` with `b ^ m * x` preserves simple normality in
base `b`. -/
theorem isSimplyNormalIn_interleave_mul_pow (hb : 2 ≤ b) (m : ℕ) (hx : IsNormalIn b x) :
    IsSimplyNormalIn b (interleave b x ((b : ℝ) ^ m * x)) := by
  have hmx : IsNormalIn b ((b : ℝ) ^ m * x) := by
    rw [mul_comm]
    exact (isNormalIn_mul_pow_iff m).2 hx
  exact isSimplyNormalIn_interleave_of_isSimplyNormalIn hb hx.isSimplyNormalIn
    hmx.isSimplyNormalIn

end Real
