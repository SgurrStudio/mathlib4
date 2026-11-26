/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Bridge
public import Mathlib.NumberTheory.Normal.Cassels
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic

/-!
# Schmidt's theorem: normality in one base need not imply normality in another

Normality in base `b` implies normality in base `c` when `b` and `c` are multiplicatively
dependent (`Real.isNormalIn_iff_of_pow_eq_pow`). **Schmidt** (1960) proved the converse: if
`bᵐ ≠ cⁿ` for all `m, n ≥ 1`, some real number is normal in base `b` and not in base `c`.

## Main statements

* `Real.exists_liouville_isNormalIn_iff_not_three_dvd`: a Liouville number in the middle-third
  Cantor set that is normal exactly in the bases not divisible by `3` (Trevor Morris's
  `CantorLiouvilleAll`).
* `Real.exists_isNormalIn_two_not_isNormalIn_three`: normality in base `2` does not imply
  normality in base `3`.
-/

@[expose] public section

namespace Real

/-- A Liouville number in the middle-third Cantor set that is normal in base `b` exactly when
`3 ∤ b` (Trevor Morris's `CantorLiouvilleAll`). -/
theorem exists_liouville_isNormalIn_iff_not_three_dvd :
    ∃ x : ℝ, x ∈ cantorSet ∧ Liouville x ∧ ∀ b : ℕ, 2 ≤ b → (IsNormalIn b x ↔ ¬ 3 ∣ b) := by
  sorry

/-- Normality in base `2` does not imply normality in base `3`. -/
theorem exists_isNormalIn_two_not_isNormalIn_three :
    ∃ x : ℝ, IsNormalIn 2 x ∧ ¬ IsNormalIn 3 x := by
  sorry

end Real
