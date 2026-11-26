/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.DifferenceTest
public import Mathlib.Imported.TauCeti.NumberTheory.CircleMethod.TypeISum
public import Mathlib.Imported.TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds

/-!
# Weyl's inequality

For a real polynomial `φ` of degree at most `k ≥ 1` whose `k`-th coefficient `α` satisfies
`|α - a / q| ≤ 1 / q²` with `gcd(a, q) = 1` and `q ≥ 1`, and for every `ε > 0`,

`‖∑_{n < N} e(φ(n))‖ ≤ C(k, ε) · N ^ (1 + ε) · (1 / q + 1 / N + q / N ^ k) ^ (2 ^ (1 - k))`.

The proof is Vaughan's (Lemma 2.4):

* Weyl differencing (`Polynomial.polyExpSum_sq_le`, from van der Corput's inequality) `k - 1`
  times, with `H = N`, lowers the phase to a linear one with frequency `k! α h₁ ⋯ h_{k-1}`; its
  geometric series is at most `min(N, 1 / ‖k! α h₁ ⋯ h_{k-1}‖)`
  (`Polynomial.norm_polyExpSum_pow_le_weylSum`).
* Regrouping by `m = h₁ ⋯ h_{k-1}` costs a factor `N ^ ε` by the divisor bound
  (`TauCeti.exists_pos_card_divisors_le_rpow`), see `Polynomial.weylSum_le`.
* The type I bound (`TauCeti.sum_min_inv_distInt_le`) sums the resulting
  `∑_{m ≤ k! N ^ (k-1)} min(N, 1 / ‖α m‖)`.

## Main statements

* `Polynomial.norm_polyExpSum_le_weyl`: **Weyl's inequality**.

## References

* R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Lemma 2.4.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §8.2.
-/

@[expose] public section

open Complex Finset TauCeti

namespace Polynomial

/-- The geometric-series weight `min(N, 1 / ‖β‖)`, taking the value `N` when `β` is an integer. -/
noncomputable def weylMin (N : ℕ) (β : ℝ) : ℝ :=
  if distInt β = 0 then N else min (N : ℝ) (distInt β)⁻¹

/-- The iterated sum `∑_{h₁, …, h_j ∈ [1, N)} min(N, 1 / ‖β h₁ ⋯ h_j‖)` left after `j` Weyl
differencings. -/
noncomputable def weylSum (N : ℕ) : ℕ → ℝ → ℝ
  | 0, β => weylMin N β
  | j + 1, β => ∑ h ∈ Ico 1 N, weylSum N j (β * h)

theorem weylMin_nonneg (N : ℕ) (β : ℝ) : 0 ≤ weylMin N β := by
  sorry

theorem weylSum_nonneg (N j : ℕ) (β : ℝ) : 0 ≤ weylSum N j β := by
  sorry

/-- A linear phase: its exponential sum over `n < L ≤ N` is at most `min(N, 1 / ‖α‖)`. -/
theorem norm_polyExpSum_le_weylMin {φ : ℝ[X]} (hφ : φ.natDegree ≤ 1) {L N : ℕ} (hLN : L ≤ N) :
    ‖polyExpSum φ L‖ ≤ weylMin N (φ.coeff 1) := by
  sorry

/-- **Weyl differencing**, iterated `j` times with `H = N`. -/
theorem norm_polyExpSum_pow_le_weylSum (j : ℕ) : ∃ K : ℝ, 0 < K ∧
    ∀ (N L : ℕ) (φ : ℝ[X]), 1 ≤ N → L ≤ N → φ.natDegree ≤ j + 1 →
      (‖polyExpSum φ L‖ / N) ^ 2 ^ j ≤
        K * (1 / N + weylSum N j ((j + 1).factorial * φ.coeff (j + 1)) / (N : ℝ) ^ (j + 1)) := by
  sorry

/-- Regrouping a double sum by the product `n = h m`: each `n` occurs at most `d(n)` times. -/
theorem sum_Ico_sum_Icc_mul_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N M : ℕ) :
    ∑ h ∈ Ico 1 N, ∑ m ∈ Icc 1 M, f (h * m) ≤
      ∑ n ∈ Icc 1 (N * M), (n.divisors.card : ℝ) * f n := by
  sorry

/-- The divisor bound turns the iterated sum into a single sum, at the cost of `N ^ δ`. -/
theorem weylSum_le (j : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ A : ℝ, 0 < A ∧
    ∀ (N : ℕ) (β : ℝ), 1 ≤ N →
      weylSum N j β ≤ A * (N : ℝ) ^ δ * ∑ m ∈ Icc 1 (N ^ j), weylMin N (β * m) := by
  sorry

/-- The type I bound for `∑_{m ≤ M} min(N, 1 / ‖c α m‖)` with an integer factor `c ≥ 1`. -/
theorem sum_weylMin_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (ha : Int.gcd a q = 1)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N M c : ℕ) (hc : 1 ≤ c) :
    ∑ m ∈ Icc 1 M, weylMin N (c * α * m) ≤
      16 * (N * c * M / q + c * M + q) * Real.log (2 * (c * M) * q) := by
  sorry

/-- **Weyl's inequality.** If the `k`-th coefficient `α` of a real polynomial `φ` of degree at
most `k ≥ 1` satisfies `|α - a / q| ≤ 1 / q²` with `q ≥ 1` and `gcd(a, q) = 1`, then
`‖∑_{n < N} e(φ(n))‖ ≤ C N ^ (1 + ε) (1 / q + 1 / N + q / N ^ k) ^ (2 ^ (1 - k))`. -/
theorem norm_polyExpSum_le_weyl {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (φ : ℝ[X]) (a : ℤ) (q : ℕ), φ.natDegree ≤ k → 0 < q → Int.gcd a q = 1 →
      |φ.coeff k - a / q| ≤ 1 / (q : ℝ) ^ 2 →
        ‖polyExpSum φ N‖ ≤ C * (N : ℝ) ^ (1 + ε) *
          (1 / q + 1 / N + q / (N : ℝ) ^ k) ^ ((2 : ℝ) ^ (k - 1))⁻¹ := by
  sorry

end Polynomial
