/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.DigitOperations

/-!
# Sliding-window codes and cellular automata on normal numbers

We establish invariance of normality in base `b ≥ 2` under left-permutative and right-permutative
sliding-block codes of arbitrary radius `r`, deduce invariance for additive cellular automata,
linear shift-register codes, and differential coding modulo `b`, and contrast these with
non-balanced local rules (`min` and `max` of adjacent digits), which destroy even simple normality.

## Main statements

* `Real.isNormalSeq_leftPermutativeSliding`, `Real.isNormalIn_ofDigits_leftPermutativeSliding`:
  a left-permutative sliding-block code of radius `r` preserves normality in base `b`.
* `Real.isNormalSeq_rightPermutativeSliding`, `Real.isNormalIn_ofDigits_rightPermutativeSliding`:
  a right-permutative sliding-block code of radius `r` preserves normality in base `b`.
* `Real.isNormalSeq_add_shift_mod`, `Real.isNormalIn_ofDigits_add_shift_mod`:
  the additive cellular automaton `d_n ↦ (d_n + d_{n + 1}) % b` preserves normality in base `b`.
* `Real.isNormalSeq_linearSliding_mod`, `Real.isNormalIn_ofDigits_linearSliding_mod`:
  any linear shift-register code `d_n ↦ (d_n + ∑ j, c j * d_{n + 1 + j}) % b` preserves normality.
* `Real.isNormalSeq_sub_shift_mod`, `Real.isNormalIn_ofDigits_sub_shift_mod`:
  differential coding `d_n ↦ (d_n + b - d_{n + 1}) % b` preserves normality in base `b`.
* `Real.not_isSimplyNormalIn_ofDigits_min_shift`, `Real.not_isSimplyNormalIn_ofDigits_max_shift`:
  taking the adjacent minimum or maximum of digits destroys simple normality in base `b`.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- **Left-permutative sliding-block code invariance (digit sequences)**: applying any
radius-`r` family of digit permutations `σ : (Fin r → Fin b) → Equiv.Perm (Fin b)` to the current
digit `digit b x n` conditioned on the next `r` digits `digit b x (n + 1 + j)` preserves
normality in base `b ≥ 2`. -/
theorem isNormalSeq_leftPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦
      (σ (fun j ↦ ⟨digit b x (n + 1 + j), digit_lt (by omega) x _⟩)
        ⟨digit b x n, digit_lt (by omega) x n⟩ : ℕ) := by
  sorry

/-- **Left-permutative sliding-block code invariance**: applying any radius-`r` left-permutative
sliding-block code to the base-`b` digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_leftPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      σ (fun j ↦ ⟨digit b x (n + 1 + j), digit_lt (by omega) x _⟩)
        ⟨digit b x n, digit_lt (by omega) x n⟩) := by
  sorry

/-- **Right-permutative sliding-block code invariance (digit sequences)**: applying any
radius-`r` family of digit permutations `σ : (Fin r → Fin b) → Equiv.Perm (Fin b)` to the digit
`digit b x (n + r)` conditioned on the preceding `r` digits `digit b x (n + j)` preserves
normality in base `b ≥ 2`. -/
theorem isNormalSeq_rightPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦
      (σ (fun j ↦ ⟨digit b x (n + j), digit_lt (by omega) x _⟩)
        ⟨digit b x (n + r), digit_lt (by omega) x _⟩ : ℕ) := by
  sorry

/-- **Right-permutative sliding-block code invariance**: applying any radius-`r` right-permutative
sliding-block code to the base-`b` digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_rightPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      σ (fun j ↦ ⟨digit b x (n + j), digit_lt (by omega) x _⟩)
        ⟨digit b x (n + r), digit_lt (by omega) x _⟩) := by
  sorry

/-- **Linear shift-register invariance (digit sequences)**: for any coefficients `c : Fin r → ℕ`,
the linear sliding-window code `n ↦ (digit b x n + ∑ j, c j * digit b x (n + 1 + j)) % b`
preserves normality in base `b ≥ 2`. -/
theorem isNormalSeq_linearSliding_mod (hb : 2 ≤ b) {r : ℕ} (c : Fin r → ℕ) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + ∑ j : Fin r, c j * digit b x (n + 1 + j)) % b := by
  sorry

/-- **Linear shift-register invariance**: for any coefficients `c : Fin r → ℕ`, the linear
sliding-window code `n ↦ (digit b x n + ∑ j, c j * digit b x (n + 1 + j)) % b` maps a base-`b`
normal number to a base-`b` normal real number. -/
theorem isNormalIn_ofDigits_linearSliding_mod (hb : 2 ≤ b) {r : ℕ} (c : Fin r → ℕ)
    (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨(digit b x n + ∑ j : Fin r, c j * digit b x (n + 1 + j)) % b,
        Nat.mod_lt _ (by omega)⟩ : Fin b)) := by
  sorry

/-- **Additive cellular automaton invariance (digit sequences)**: replacing each digit by
`(digit b x n + digit b x (n + 1)) % b` preserves normality in base `b ≥ 2`. -/
theorem isNormalSeq_add_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + digit b x (n + 1)) % b := by
  sorry

/-- **Additive cellular automaton invariance**: replacing each digit by
`(digit b x n + digit b x (n + 1)) % b` maps a base-`b` normal number to a base-`b` normal real
number. -/
theorem isNormalIn_ofDigits_add_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨(digit b x n + digit b x (n + 1)) % b, Nat.mod_lt _ (by omega)⟩ : Fin b)) := by
  sorry

/-- **Differential coding invariance (digit sequences)**: replacing each digit by
`(digit b x n + b - digit b x (n + 1)) % b` preserves normality in base `b ≥ 2`. -/
theorem isNormalSeq_sub_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + b - digit b x (n + 1)) % b := by
  sorry

/-- **Differential coding invariance**: replacing each digit by
`(digit b x n + b - digit b x (n + 1)) % b` maps a base-`b` normal number to a base-`b` normal
real number. -/
theorem isNormalIn_ofDigits_sub_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨(digit b x n + b - digit b x (n + 1)) % b, Nat.mod_lt _ (by omega)⟩ : Fin b)) := by
  sorry

/-- Taking the adjacent minimum of base-`b` digits of a normal number destroys even simple
normality: digit `0` occurs with asymptotic frequency `(2 b - 1) / b ^ 2 ≠ 1 / b`. -/
theorem not_isSimplyNormalIn_ofDigits_min_shift (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsSimplyNormalIn b (ofDigits fun n ↦
      (⟨min (digit b x n) (digit b x (n + 1)),
        lt_of_le_of_lt (min_le_left _ _) (digit_lt (by omega) x n)⟩ : Fin b)) := by
  sorry

/-- Taking the adjacent maximum of base-`b` digits of a normal number destroys even simple
normality: digit `0` occurs with asymptotic frequency `1 / b ^ 2 ≠ 1 / b`. -/
theorem not_isSimplyNormalIn_ofDigits_max_shift (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsSimplyNormalIn b (ofDigits fun n ↦
      (⟨max (digit b x n) (digit b x (n + 1)),
        max_lt (digit_lt (by omega) x n) (digit_lt (by omega) x (n + 1))⟩ : Fin b)) := by
  sorry

end Real
