/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Basic

/-!
# Piatetski-Shapiro's normality criterion

**Piatetski-Shapiro** (1951) proved that a real number `x` is normal in base `b` as soon as there
is a constant `C` such that every block `w` of `k` digits has upper asymptotic frequency at most
`C * b⁻ᵏ` in the base-`b` expansion of `x`. This is the basic tool for proving normality of numbers
obtained from normal numbers by simple transformations (such as rational multiples) and of
the Stoneham numbers.

## Main statements

* `Real.isNormalIn_of_eventually_le`: Piatetski-Shapiro's normality criterion.

## Proof sketch

Along a subsequence of `N`, all block frequencies converge to a family `p(w)` which is consistent
under extending a word on the left or on the right, and satisfies `p(w) ≤ C * b^(-|w|)`. The
quantity `Q(L) = b ^ L * ∑_{|w| = L} p(w) ^ 2` is nondecreasing and bounded by `C`. Viewing
`ρ_L(w) = b ^ L * p(w)` as a function on words with the uniform measure, both `ρ_L(v)` and
`ρ_L(w)` are conditional expectations of `ρ_{2L}(v w)`, so
`2 * (Q(L) - 1) = ‖ρ_L(v) - ρ_L(w)‖² ≤ 4 * (Q(2L) - Q(L)) → 0`.
Hence `Q(L) = 1` for every `L`, which by Cauchy–Schwarz forces `p(w) = b^(-|w|)`.

## References

* [I. I. Piatetski-Shapiro, *On the laws of distribution of the fractional parts of an
  exponential function*][PiatetskiShapiro1951]
* [N. G. Moshchevitin, I. D. Shkredov, *On the Pyatetskii-Shapiro criterion of
  normality*][MoshchevitinShkredov2003]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- **Piatetski-Shapiro's normality criterion**: if there is a constant `C` such that every block
`w` of `k` digits eventually has frequency at most `C * b⁻ᵏ + ε` in the base-`b` expansion of `x`,
then `x` is normal in base `b`. -/
theorem isNormalIn_of_eventually_le (hb : 2 ≤ b) {C : ℝ}
    (h : ∀ (k : ℕ) (w : Fin k → Fin b) (ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop,
      (blockCount b x w N : ℝ) / N ≤ C * ((b : ℝ) ^ k)⁻¹ + ε) :
    IsNormalIn b x := by
  sorry

end Real
