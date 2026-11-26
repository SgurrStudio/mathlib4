/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.DigitOperations

/-!
# Block-cipher and periodic-mask invariance vs. digit-doubling separation

We establish invariance of normality in base `b ≥ 2` under aligned block-level bijections,
periodic digit-wise modular shifts, and fixed-width block-coordinate permutations, and contrast
these with digit-doubling (self-interleaving), which preserves simple normality while destroying
full normality.

## Main statements

* `Real.isNormalIn_ofDigits_blockPerm`: permuting aligned `L`-digit blocks via any
  `σ : Equiv.Perm (Fin (b ^ L))` preserves normality in base `b`.
* `Real.isNormalSeq_add_periodic_mod`, `Real.isNormalIn_ofDigits_add_periodic_mod`: adding a
  periodic mask modulo `b` to the base-`b` digits of a normal number preserves normality.
* `Real.isNormalSeq_blockCoordPerm`, `Real.isNormalIn_ofDigits_blockCoordPerm`: permuting
  coordinates within each aligned `L`-digit block preserves normality in base `b`.
* `Real.isSimplyNormalIn_digitDouble`, `Real.not_isNormalIn_digitDouble`: repeating each digit
  of a base-`b` normal number twice produces a number that is simply normal in base `b` but not
  normal in base `b`.
* `Real.exists_isSimplyNormalIn_not_isNormalIn`: for every base `b ≥ 2`, there exists a real
  number that is simply normal in base `b` but not normal in base `b`.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b L : ℕ} {x : ℝ}

/-- **Block-cipher invariance**: permuting aligned `L`-digit blocks of a base-`b` normal number
via any permutation `σ : Equiv.Perm (Fin (b ^ L))` preserves normality in base `b`. -/
theorem isNormalIn_ofDigits_blockPerm (hb : 2 ≤ b) (hL : 1 ≤ L)
    (σ : Equiv.Perm (Fin (b ^ L))) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits (b := b ^ L) fun n ↦
      σ ⟨digit (b ^ L) x n, digit_lt (by positivity) x n⟩) := by
  sorry

/-- Applying any bijection `f : Equiv.Perm (Fin L → Fin b)` to each aligned `L`-digit block of a
base-`b` normal number yields a base-`b` normal digit sequence. -/
theorem isNormalSeq_blockEquiv (hb : 2 ≤ b) (hL : 1 ≤ L)
    (f : Equiv.Perm (Fin L → Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦
      (f (fun j ↦ ⟨digit b x ((n / L) * L + j), digit_lt (by omega) x _⟩)
        ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ) := by
  sorry

/-- **Periodic modular shift invariance (digit sequences)**: adding a periodic mask `p` modulo `b`
to the base-`b` digits of a normal number yields a normal digit sequence. -/
theorem isNormalSeq_add_periodic_mod (hb : 2 ≤ b) (hL : 1 ≤ L) {p : ℕ → ℕ}
    (hp : ∀ n, p (n + L) = p n) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + p n) % b := by
  sorry

/-- **Periodic modular shift invariance**: adding a periodic mask `p` modulo `b` to the base-`b`
digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_add_periodic_mod (hb : 2 ≤ b) (hL : 1 ≤ L) {p : ℕ → ℕ}
    (hp : ∀ n, p (n + L) = p n) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨(digit b x n + p n) % b, Nat.mod_lt _ (by omega)⟩ : Fin b)) := by
  sorry

/-- **Block-coordinate permutation invariance (digit sequences)**: permuting the coordinates
within each aligned `L`-digit block of a base-`b` normal number yields a normal digit sequence. -/
theorem isNormalSeq_blockCoordPerm (hb : 2 ≤ b) (hL : 1 ≤ L) (τ : Equiv.Perm (Fin L))
    (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦
      digit b x ((n / L) * L + (τ ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ)) := by
  sorry

/-- **Block-coordinate permutation invariance**: permuting the coordinates within each aligned
`L`-digit block of a base-`b` normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_blockCoordPerm (hb : 2 ≤ b) (hL : 1 ≤ L) (τ : Equiv.Perm (Fin L))
    (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨digit b x ((n / L) * L + (τ ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ)),
        digit_lt (by omega) x _⟩ : Fin b)) := by
  sorry

/-- The digits of the digit-doubled expansion of a base-`b` normal number `x` are indeed
`n ↦ digit b x (n / 2)`. -/
theorem digit_ofDigits_digitDouble (hb : 2 ≤ b) (hx : IsNormalIn b x) (n : ℕ) :
    digit b (ofDigits fun k ↦ (⟨digit b x (k / 2), digit_lt (by omega) x (k / 2)⟩ : Fin b)) n =
      digit b x (n / 2) := by
  sorry

/-- Repeating each base-`b` digit of a normal number `x` twice preserves simple normality in
base `b`. -/
theorem isSimplyNormalIn_digitDouble (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsSimplyNormalIn b (ofDigits fun n ↦
      (⟨digit b x (n / 2), digit_lt (by omega) x (n / 2)⟩ : Fin b)) := by
  sorry

/-- Repeating each base-`b` digit of a normal number `x` twice destroys normality in base `b`:
the length-`2` block `(0, 1)` cannot occur at even positions, so its asymptotic frequency is
`1 / (2 b ^ 2)` instead of `1 / b ^ 2`. -/
theorem not_isNormalIn_digitDouble (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (ofDigits fun n ↦
      (⟨digit b x (n / 2), digit_lt (by omega) x (n / 2)⟩ : Fin b)) := by
  sorry

/-- For every base `b ≥ 2`, there exists a real number that is simply normal in base `b`
but not normal in base `b`. -/
theorem exists_isSimplyNormalIn_not_isNormalIn (hb : 2 ≤ b) :
    ∃ z : ℝ, IsSimplyNormalIn b z ∧ ¬ IsNormalIn b z := by
  sorry

end Real
