/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Bridge
public import Mathlib.Imported.NormalNumbers.CantorLiouvilleAll

/-!
# Cassels' theorem: almost every point of the Cantor set is normal in other bases

Let `μ` be the Cantor measure, the law of `∑ᵢ 2 εᵢ 3⁻ⁱ⁻¹` for independent fair coins `εᵢ`.
**Cassels** (1959) proved that `μ`-almost every point is normal in every base `b ≥ 2` that is not
a power of `3`. Such points lie in the middle-third Cantor set, so they are not normal in base `3`.

## Main statements

* `NormalNumbers.CantorLiouvilleAll.cassels1959`: Morris's statement
  `NormalNumbers.CantorLiouvilleAll.Literature.Cassels1959`.
* `Real.ae_isNormalIn_cantor`: the same statement with `Real.IsNormalIn`.

## Proof

By the Davenport–Erdős–LeVeque criterion (`CantorLiouvilleAll.ae_isNormal_of_secondMoment`) it is
enough to bound `∫ ‖∑_{k<N} e(h bᵏ x)‖² dμ(x)` by `N²` times a quantity summable along a
schedule with ratio tending to `1`. Expanding the square gives `μ̂(h(bⁿ − bᵐ))`, and
`|μ̂(ξ)| = ∏ₚ |cos(2πξ/3ᵖ⁺¹)|`.

* If `3 ∤ b`, this is Morris's `CantorLiouvilleAll.secondMoment_le_b` with every ternary position
  free.
* If `b = 3ᵃ m` with `a ≥ 1`, `m ≥ 2` and `3 ∤ m`, the frequency of the pair `(l + d, l)` is
  `3^{e + al} · c mᴸ` with `c = |h'| (bᵈ − 1)` prime to `3` (`h = 3ᵉ h'`). The factor `3^{e+al}`
  only removes the leading cosine factors, which are `1`, so the sum over `l` is the orbit sum
  `∑_l Hf (c mˡ)` that `CantorLiouvilleAll.sum_Hf_le_b` bounds for the base `m` prime to `3`.
  No `d` is exceptional, since `bᵈ − 1 ≡ 2 mod 3`.
-/

@[expose] public section

open MeasureTheory

namespace NormalNumbers.CantorLiouvilleAll

open CantorLiouville ExplicitSquare

/-- **Cassels' theorem** (1959), in Morris's terms: for fair coins `ω`, almost surely the point
`∑ᵢ 2 ωᵢ 3⁻ⁱ⁻¹` of the Cantor set is normal in every base that is not a power of `3`. -/
theorem cassels1959 : Literature.Cassels1959 := by
  sorry

end NormalNumbers.CantorLiouvilleAll

namespace Real

open NormalNumbers.CantorLiouville NormalNumbers.ExplicitSquare

/-- **Cassels' theorem** (1959): almost every point of the middle-third Cantor set, for the
Cantor measure, is normal in every base `b ≥ 2` that is not a power of `3`. The Cantor measure is
the law of `pt (fun _ ↦ true)` under fair coins. -/
theorem ae_isNormalIn_cantor :
    ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (∀ k : ℕ, b ≠ 3 ^ k) →
      IsNormalIn b (pt (fun _ ↦ true) ω) := by
  sorry

end Real
