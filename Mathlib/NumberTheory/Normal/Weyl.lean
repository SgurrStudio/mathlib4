/-
Copyright (c) 2026 Trevor Morris, Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris, Rob
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.NumberTheory.Normal.Wall

/-!
# Weyl's criterion

A real sequence `u` is equidistributed modulo one as soon as its *Weyl sums* are small: for every
nonzero integer `h`, `(1 / N) ∑_{n < N} e(h u n) → 0`, where `e(t) = exp(2 π i t)`. Combined with
Wall's theorem this gives the *exponential-sum criterion for normality*: `x` is normal in base `b`
as soon as `(1 / N) ∑_{n < N} e(h b ^ n x) → 0` for every `h ≠ 0`. This is the entry point of the
analytic proofs of normality (Davenport–Erdős, Besicovitch, Schmidt).

## Main statements

* `Real.isEquidistributedModOne_of_tendsto_weylSum`: **Weyl's criterion**.
* `Real.isNormalIn_of_tendsto_weylSum`: the exponential-sum criterion for normality.

## Proof

Squeeze the indicator of `[a, c)` between two continuous trapezoid functions on the circle whose
integrals are within `2 δ` of `c - a`, approximate continuous circle functions uniformly by
trigonometric polynomials (`span_fourier_closure_eq_top`), and use that the Cesàro means of
every nonconstant character vanish by hypothesis.

The proof is ported from Trevor Morris's `normal-numbers` repository
(`NormalNumbers/WeylCriterion.lean`, Apache 2.0), adapted to `Real.IsEquidistributedModOne`.

## References

* [L. Kuipers, H. Niederreiter, *Uniform distribution of sequences*][KuipersNiederreiter1974]
-/

@[expose] public section

open Filter Topology Complex MeasureTheory intervalIntegral

namespace Real

/-- **Weyl's criterion**: if every nonzero Weyl mean of `u` tends to `0`, then `u` is
equidistributed modulo one. -/
theorem isEquidistributedModOne_of_tendsto_weylSum (u : ℕ → ℝ)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * u n)) / N) atTop (𝓝 0)) :
    IsEquidistributedModOne u := by
  sorry

/-- **Exponential-sum criterion for normality**: if `(1 / N) ∑_{n < N} e(h b ^ n x) → 0` for
every integer `h ≠ 0`, then `x` is normal in base `b`. -/
theorem isNormalIn_of_tendsto_weylSum {b : ℕ} {x : ℝ} (hb : 2 ≤ b)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n))) / N) atTop (𝓝 0)) :
    IsNormalIn b x := by
  sorry

end Real
