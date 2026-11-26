/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Discrepancy
public import Mathlib.NumberTheory.Normal.Weyl

/-!
# The Erdős–Turán inequality

We prove the **Erdős–Turán inequality** (P. Erdős and P. Turán, 1948): for any real sequence
`u : ℕ → ℝ`, `N ≥ 1`, and integer `M ≥ 0`,
`starDiscrepancy u N ≤ 16 / (M + 1) + (4 / π) * ∑ h ∈ Icc 1 M, (1 / h) * ‖W_N(h)‖`,
where `W_N(h) = (1 / N) ∑_{n < N} exp(2 π i h u_n)` is the `h`-th Weyl mean.

Combined with quantitative Wall's theorem (`Real.abs_blockCount_div_sub_le_discrepancy`), this
yields an explicit exponential-sum bound on digit-block frequency errors in any base `b ≥ 2`.

## References

* P. Erdős and P. Turán, *On a problem in the theory of uniform distribution*, Indag. Math. 10
  (1948), 370–378, 406–413.
* L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974, Ch. 2 §2.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Real

/-- **Erdős–Turán inequality**: the star discrepancy `D_N^*(u)` is bounded in terms of the first
`M` Weyl exponential sums `W_N(h) = (1 / N) ∑_{n < N} exp(2 π i h u_n)`. -/
theorem erdos_turan (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    starDiscrepancy u N ≤
      16 / (M + 1 : ℝ) +
        (4 / π) * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) *
            ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) / N‖ := by
  sorry

/-- **Erdős–Turán inequality** for the extreme discrepancy `D_N(u)`. -/
theorem erdos_turan_discrepancy (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    discrepancy u N ≤
      32 / (M + 1 : ℝ) +
        (8 / π) * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) *
            ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) / N‖ := by
  sorry

/-- Quantitative exponential-sum bound for base-`b` digit-block frequencies, combining quantitative
Wall's theorem with the Erdős–Turán inequality. -/
theorem abs_blockCount_div_sub_le_erdos_turan {b k : ℕ} (hb : 0 < b) (x : ℝ)
    (w : Fin k → Fin b) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    |(blockCount b x w N : ℝ) / N - ((b : ℝ) ^ k)⁻¹| ≤
      32 / (M + 1 : ℝ) +
        (8 / π) * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) *
            ‖(∑ n ∈ Finset.range N,
              Complex.exp (2 * π * Complex.I * (h : ℂ) * (x * (b : ℝ) ^ n))) / N‖ := by
  sorry

end Real
