/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.DavenportErdos

/-!
# The Nakai–Shiokawa theorem

Let `f` be a non-constant polynomial with real coefficients taking positive values at the
positive integers. **Nakai and Shiokawa** proved that the number `0.⌊f(1)⌋ ⌊f(2)⌋ ⌊f(3)⌋ …`,
obtained by concatenating the base-`b` expansions of the integer parts `⌊f(n)⌋`, is normal in
base `b`. For integer polynomials this is the Davenport–Erdős theorem
(`Real.isNormalIn_concatenation_polynomial`).

## Main statements

* `Real.isNormalIn_concatenation_floor_polynomial`: the Nakai–Shiokawa theorem.

## Proof

We reuse the Davenport–Erdős assembly `Real.isNormalIn_concatenation_of_growth`. The only new
point is the Weyl sum of `⌊f(t)⌋ / b ^ (s + k)`: it differs from that of `f(t) / b ^ (s + k)`
by at most `2 π h T / b ^ (s + k)`, which is `o(T)` at the positions `s` that matter, and the
latter is `o(T)` by the `d`-th difference test (`Polynomial.eventually_norm_polyExpSum_le`),
which already allows a real leading coefficient.

## References

* [Y. Nakai, I. Shiokawa, *Discrepancy estimates for a class of normal numbers*][NakaiShiokawa1992]
-/

@[expose] public section

open Polynomial Filter Topology Finset

namespace Real

/-- **The Nakai–Shiokawa theorem**: if `f` is a non-constant real polynomial with `f(n) > 0` for
all `n ≥ 1`, then `0.⌊f(1)⌋ ⌊f(2)⌋ ⌊f(3)⌋ …` is normal in every base `b ≥ 2`. -/
theorem isNormalIn_concatenation_floor_polynomial {b : ℕ} [NeZero b] (hb : 2 ≤ b) {f : ℝ[X]}
    (hf : 0 < f.natDegree) (hpos : ∀ n : ℕ, 0 < f.eval ((n : ℝ) + 1)) :
    IsNormalIn b (concatenation b fun n ↦ ⌊f.eval ((n : ℝ) + 1)⌋₊) := by
  sorry

end Real
