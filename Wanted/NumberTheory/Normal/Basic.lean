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
some digit occurs infinitely often in the expansion of every irrational algebraic number in
every base. -/
proof_wanted isAbsolutelyNormal_of_isAlgebraic {x : ℝ} (halg : IsAlgebraic ℚ x)
    (hirr : Irrational x) : IsAbsolutelyNormal x

/-- The base-specific form of **Borel's conjecture**: every irrational algebraic real number is
normal in base `b` for every `b ≥ 2`. -/
proof_wanted isNormalIn_of_isAlgebraic {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (halg : IsAlgebraic ℚ x)
    (hirr : Irrational x) : IsNormalIn b x

/-- **Borel's conjecture for `√2`**: the square root of two is normal in base `10`. -/
proof_wanted isNormalIn_ten_sqrt_two : IsNormalIn 10 (√2)

end Real
