/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.Normal.CopelandErdos

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
  sorry

@[simp]
theorem interleaveDigits_two_mul (b : ℕ) (x y : ℝ) (m : ℕ) :
    interleaveDigits b x y (2 * m) = digit b x m := by
  sorry

@[simp]
theorem interleaveDigits_two_mul_add_one (b : ℕ) (x y : ℝ) (m : ℕ) :
    interleaveDigits b x y (2 * m + 1) = digit b y m := by
  sorry

@[simp]
theorem interleaveDigits_add_intCast_left (b : ℕ) (x y : ℝ) (m : ℤ) (n : ℕ) :
    interleaveDigits b (x + m) y n = interleaveDigits b x y n := by
  sorry

@[simp]
theorem interleaveDigits_add_intCast_right (b : ℕ) (x y : ℝ) (m : ℤ) (n : ℕ) :
    interleaveDigits b x (y + m) n = interleaveDigits b x y n := by
  sorry

/-- The real number formed by interleaving the base-`b` digits of `x` and `y`. -/
noncomputable def interleave (b : ℕ) (x y : ℝ) : ℝ :=
  if hb : 0 < b then
    ofDigits fun n ↦ (⟨interleaveDigits b x y n, interleaveDigits_lt hb x y n⟩ : Fin b)
  else 0

@[simp]
theorem interleave_add_intCast_left (b : ℕ) (x y : ℝ) (m : ℤ) :
    interleave b (x + m) y = interleave b x y := by
  sorry

@[simp]
theorem interleave_add_intCast_right (b : ℕ) (x y : ℝ) (m : ℤ) :
    interleave b x (y + m) = interleave b x y := by
  sorry

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
  sorry

@[simp]
theorem jointBlockCount_add_intCast_right (b : ℕ) (x y : ℝ) (m : ℤ) {k : ℕ}
    (u v : Fin k → Fin b) (N : ℕ) :
    jointBlockCount b x (y + m) u v N = jointBlockCount b x y u v N := by
  sorry

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
  sorry

@[simp]
theorem isJointlyNormalIn_add_intCast_right_iff (m : ℤ) :
    IsJointlyNormalIn b x (y + m) ↔ IsJointlyNormalIn b x y := by
  sorry

/-- The canonical base-`b` expansion of any real number has infinitely many digits `< b - 1`. -/
theorem exists_gt_digit_lt_sub_one (hb : 2 ≤ b) (x : ℝ) (m : ℕ) :
    ∃ n, m < n ∧ digit b x n + 1 < b := by
  sorry

theorem interleave_mem_Ico (hb : 2 ≤ b) (x y : ℝ) : interleave b x y ∈ Ico (0 : ℝ) 1 := by
  sorry

/-- The base-`b` digits of `interleave b x y` are unconditionally `interleaveDigits b x y`. -/
theorem digit_interleave (hb : 2 ≤ b) (x y : ℝ) (n : ℕ) :
    digit b (interleave b x y) n = interleaveDigits b x y n := by
  sorry

/-- Interleaving the base-`b` digits of `x` and `y` equals the base-`b ^ 2` real number with
digits `m ↦ b * digit b x m + digit b y m`. -/
theorem interleave_eq_ofDigits_sq (hb : 0 < b) (x y : ℝ) :
    interleave b x y = ofDigits (b := b ^ 2) fun m ↦
      ⟨b * digit b x m + digit b y m, by
        have hx := digit_lt hb x m
        have hy := digit_lt hb y m
        nlinarith⟩ := by
  sorry

/-- The base-`b ^ 2` digits of `interleave b x y` are `m ↦ b * digit b x m + digit b y m`. -/
theorem digit_sq_interleave (hb : 2 ≤ b) (x y : ℝ) (m : ℕ) :
    digit (b ^ 2) (interleave b x y) m = b * digit b x m + digit b y m := by
  sorry

/-! ### Fundamental equivalence, marginals, and symmetry -/

/-- Two real numbers `x` and `y` are jointly normal in base `b ≥ 2` if and only if their base-`b`
interleaving is normal in base `b`. -/
theorem isJointlyNormalIn_iff_isNormalIn_interleave (hb : 2 ≤ b) :
    IsJointlyNormalIn b x y ↔ IsNormalIn b (interleave b x y) := by
  sorry

/-- If `(x, y)` is jointly normal in base `b ≥ 2`, then `x` is normal in base `b`. -/
theorem IsJointlyNormalIn.left (hb : 2 ≤ b) (h : IsJointlyNormalIn b x y) : IsNormalIn b x := by
  sorry

/-- If `(x, y)` is jointly normal in base `b ≥ 2`, then `y` is normal in base `b`. -/
theorem IsJointlyNormalIn.right (hb : 2 ≤ b) (h : IsJointlyNormalIn b x y) : IsNormalIn b y := by
  sorry

/-- Joint normality is symmetric. -/
theorem IsJointlyNormalIn.symm (_hb : 2 ≤ b) (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b y x := by
  sorry

theorem IsJointlyAbsolutelyNormal.left (h : IsJointlyAbsolutelyNormal x y) :
    IsAbsolutelyNormal x := by
  sorry

theorem IsJointlyAbsolutelyNormal.right (h : IsJointlyAbsolutelyNormal x y) :
    IsAbsolutelyNormal y := by
  sorry

theorem IsJointlyAbsolutelyNormal.symm (h : IsJointlyAbsolutelyNormal x y) :
    IsJointlyAbsolutelyNormal y x := by
  sorry

/-! ### Constructive existence via even/odd digit splitting -/

/-- Splitting a base-`b` normal number `z` into its even-index and odd-index base-`b` digits yields
a pair that is jointly normal in base `b`. -/
theorem isJointlyNormalIn_even_odd (hb : 2 ≤ b) {z : ℝ} (hz : IsNormalIn b z) :
    IsJointlyNormalIn b
      (ofDigits fun n ↦ (⟨digit b z (2 * n), digit_lt (by omega) z (2 * n)⟩ : Fin b))
      (ofDigits fun n ↦ (⟨digit b z (2 * n + 1), digit_lt (by omega) z (2 * n + 1)⟩ : Fin b)) := by
  sorry

/-- For every base `b ≥ 2`, there exists a pair of real numbers that are jointly normal in
base `b`. -/
theorem exists_isJointlyNormalIn (hb : 2 ≤ b) : ∃ x y : ℝ, IsJointlyNormalIn b x y := by
  sorry

/-! ### Metric ubiquity on `ℝ × ℝ` -/

/-- Almost every pair `(x, y) ∈ ℝ × ℝ` (with respect to two-dimensional Lebesgue measure) is
jointly normal in base `b ≥ 2`. -/
theorem ae_isJointlyNormalIn (hb : 2 ≤ b) :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), IsJointlyNormalIn b p.1 p.2 := by
  sorry

/-- Almost every pair `(x, y) ∈ ℝ × ℝ` (with respect to two-dimensional Lebesgue measure) is
jointly absolutely normal. -/
theorem ae_isJointlyAbsolutelyNormal :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), IsJointlyAbsolutelyNormal p.1 p.2 := by
  sorry

/-- Jointly absolutely normal pairs exist. -/
theorem exists_isJointlyAbsolutelyNormal : ∃ x y : ℝ, IsJointlyAbsolutelyNormal x y := by
  sorry

/-! ### Correlated interleaving: simple normality preserved, joint normality destroyed -/

/-- Interleaving the base-`b` digits of any two simply normal numbers preserves simple normality
in base `b`. -/
theorem isSimplyNormalIn_interleave_of_isSimplyNormalIn (hb : 2 ≤ b)
    (hx : IsSimplyNormalIn b x) (hy : IsSimplyNormalIn b y) :
    IsSimplyNormalIn b (interleave b x y) := by
  sorry

/-- If a pair of blocks `(u, v)` never occurs simultaneously in `x` and `y`, then `(x, y)` is not
jointly normal in base `b`. -/
theorem not_isJointlyNormalIn_of_forall_not {k : ℕ} (hb : 0 < b) (u v : Fin k → Fin b)
    (huv : ∀ i, ¬((∀ j : Fin k, digit b x (i + j) = u j) ∧
      (∀ j : Fin k, digit b y (i + j) = v j))) :
    ¬ IsJointlyNormalIn b x y := by
  sorry

/-- No number is jointly normal with itself in base `b ≥ 2`. -/
theorem not_isJointlyNormalIn_self (hb : 2 ≤ b) (_hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x x := by
  sorry

/-- Self-interleaving a base-`b` normal number destroys normality in base `b`. -/
theorem not_isNormalIn_interleave_self (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x x) := by
  sorry

/-- A base-`b` normal number is never jointly normal with any digit-permuted version of itself. -/
theorem not_isJointlyNormalIn_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x
      (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩) := by
  sorry

/-- Interleaving a base-`b` normal number with a digit-permuted copy of itself destroys normality
in base `b`. -/
theorem not_isNormalIn_interleave_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩)) :=
  by sorry

/-- Interleaving a base-`b` normal number with a digit-permuted copy of itself preserves simple
normality in base `b`. -/
theorem isSimplyNormalIn_interleave_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    IsSimplyNormalIn b
      (interleave b x (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩)) := by
  sorry

/-- A base-`b` normal number `x` is never jointly normal with `-x`. -/
theorem not_isJointlyNormalIn_neg (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x (-x) := by
  sorry

/-- Interleaving a base-`b` normal number `x` with `-x` destroys normality in base `b`. -/
theorem not_isNormalIn_interleave_neg (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x (-x)) := by
  sorry

/-- Interleaving a base-`b` normal number `x` with `-x` preserves simple normality in base `b`. -/
theorem isSimplyNormalIn_interleave_neg (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsSimplyNormalIn b (interleave b x (-x)) := by
  sorry

/-- A base-`b` normal number `x` is never jointly normal with `b ^ m * x`. -/
theorem not_isJointlyNormalIn_mul_pow (hb : 2 ≤ b) (m : ℕ) (_hx : IsNormalIn b x) :
    ¬ IsJointlyNormalIn b x ((b : ℝ) ^ m * x) := by
  sorry

/-- Interleaving a base-`b` normal number `x` with `b ^ m * x` destroys normality in base `b`. -/
theorem not_isNormalIn_interleave_mul_pow (hb : 2 ≤ b) (m : ℕ) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (interleave b x ((b : ℝ) ^ m * x)) := by
  sorry

/-- Interleaving a base-`b` normal number `x` with `b ^ m * x` preserves simple normality in
base `b`. -/
theorem isSimplyNormalIn_interleave_mul_pow (hb : 2 ≤ b) (m : ℕ) (hx : IsNormalIn b x) :
    IsSimplyNormalIn b (interleave b x ((b : ℝ) ^ m * x)) := by
  sorry

end Real
