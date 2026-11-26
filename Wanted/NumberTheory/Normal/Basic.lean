/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.RingTheory.Algebraic.Defs

namespace Real

/-- **Borel's conjecture** (É. Borel, 1950): every irrational algebraic real number is
absolutely normal, i.e. normal in every integer base `b ≥ 2`.

This is wide open: it is not even known whether `√2` is simply normal in base `2`, or whether
every digit occurs infinitely often in the expansion of every irrational algebraic number in
every base. The weaker forms below are open as well. -/
proof_wanted isAbsolutelyNormal_of_isAlgebraic {x : ℝ} (halg : IsAlgebraic ℚ x)
    (hirr : Irrational x) : IsAbsolutelyNormal x

/-- A weak form of **Borel's conjecture**: every irrational algebraic real number is normal in
*some* base `b ≥ 2`. -/
proof_wanted exists_isNormalIn_of_isAlgebraic {x : ℝ} (halg : IsAlgebraic ℚ x)
    (hirr : Irrational x) : ∃ b : ℕ, 2 ≤ b ∧ IsNormalIn b x

/-- A weak form of **Borel's conjecture**: every irrational algebraic real number is simply
normal in every base `b ≥ 2`. -/
proof_wanted isSimplyNormalIn_of_isAlgebraic {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (halg : IsAlgebraic ℚ x) (hirr : Irrational x) : IsSimplyNormalIn b x

/-- A weak form of **Borel's conjecture**: in every base `b ≥ 2`, every finite block of digits
occurs in the expansion of every irrational algebraic real number. -/
proof_wanted isDisjunctiveIn_of_isAlgebraic {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (halg : IsAlgebraic ℚ x) (hirr : Irrational x) : IsDisjunctiveIn b x

/-- **Borel's conjecture for `√2`**: the square root of two is normal in base `10`. -/
proof_wanted isNormalIn_ten_sqrt_two : IsNormalIn 10 (√2)

end Real
