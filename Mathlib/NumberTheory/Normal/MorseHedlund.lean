/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.FactorComplexity
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.NumberTheory.Normal.Exp

/-!
# Morse–Hedlund digit complexity lower bounds for irrationals, `π`, and `e`

A normal number in base `b` has maximal block complexity `p(n) = b ^ n`. For transcendental
constants such as `π` and `e = exp 1` (unlike algebraic irrationals, where Adamczewski–Bugeaud
gives `p(n) / n → ∞`, see `Mathlib/NumberTheory/Normal/Complexity.lean`), the strongest general
unconditional lower bound on block complexity comes from **Morse–Hedlund's theorem** (1938): every
irrational real number has at least `n + 1` distinct base-`b` blocks of length `n`.

## Main statements

* `Real.not_isEventuallyPeriodic_digit`: the base-`b` digit sequence of an irrational real number
  is not eventually periodic.
* `Real.succ_le_complexity_digit`: for every irrational `x` and base `b ≥ 2`,
  `n + 1 ≤ Function.complexity (digit b x) n`.
* `Real.succ_le_complexity_digit_pi`: Morse–Hedlund lower bound for `π`.
* `Real.succ_le_complexity_digit_exp_one`: Morse–Hedlund lower bound for `e = exp 1`.

## References

* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

namespace Real

/-- The base-`b` digit sequence of an irrational number is not eventually periodic. -/
theorem not_isEventuallyPeriodic_digit {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : Irrational x) :
    ¬ Function.IsEventuallyPeriodic (digit b x) := by
  sorry

/-- **Morse–Hedlund theorem for `Real.digit`**: in any base `b ≥ 2`, an irrational real number has
at least `n + 1` distinct blocks of `n` consecutive digits. -/
theorem succ_le_complexity_digit {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : Irrational x) (n : ℕ) :
    n + 1 ≤ Function.complexity (digit b x) n := by
  sorry

/-- In every base `b ≥ 2`, `π` has at least `n + 1` distinct blocks of `n` consecutive digits. -/
theorem succ_le_complexity_digit_pi {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    n + 1 ≤ Function.complexity (digit b π) n := by
  sorry

/-- In every base `b ≥ 2`, `e = exp 1` has at least `n + 1` distinct blocks of `n` consecutive
digits. -/
theorem succ_le_complexity_digit_exp_one {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    n + 1 ≤ Function.complexity (digit b (Real.exp 1)) n := by
  sorry

end Real
