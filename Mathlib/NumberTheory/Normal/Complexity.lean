/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.ComplexityTranscendence
public import Mathlib.NumberTheory.Normal.CopelandErdos

/-!
# The digit complexity of algebraic irrationals

Borel's conjecture says that the digits of an algebraic irrational `x` contain every block with
the expected frequency. A normal number in particular contains every block of length `n`, so its
complexity, the number of distinct blocks of length `n`, is `b ^ n`. The strongest unconditional
result in this direction is by **Adamczewski and Bugeaud**: the complexity `p n` of `x` satisfies
`p n / n → ∞`. Here we transfer their theorem, proved via Schmidt's Subspace Theorem in
`Mathlib/Imported/SubspaceTheorems`, to `Real.digit`.

## Main statements

* `Real.tendsto_complexity_digit_div_atTop`: the Adamczewski–Bugeaud theorem for `Real.digit`.

## References

* [B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
  bases*][AdamczewskiBugeaud2007]
-/

@[expose] public section

open Filter

namespace Real

/-- **Adamczewski–Bugeaud**: the number of distinct blocks of length `n` in the base-`b` digits of
an algebraic irrational number grows faster than `n`. -/
theorem tendsto_complexity_digit_div_atTop {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hirr : Irrational x)
    (halg : IsAlgebraic ℚ x) :
    Tendsto (fun n ↦ (Function.complexity (digit b x) n : ℝ) / n) atTop atTop := by
  sorry

end Real
