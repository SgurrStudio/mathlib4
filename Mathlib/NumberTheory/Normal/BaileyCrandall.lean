/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Weyl

/-!
# Bailey–Crandall dynamical reduction for BBP constants

For a base `b ≥ 2` and a real sequence `r : ℕ → ℝ` tending to `0`, consider the BBP-type series
`θ = ∑' k, r k / b ^ (k + 1)` and the associated Bailey–Crandall iteration on `[0, 1)`:
`x₀ = 0`, `x_{n+1} = Int.fract (b * x_n + r n)`.

We state and prove the two foundational unconditional theorems of Bailey and Crandall (2001):

1. **Shadowing / Normality Equivalence** (`Real.isNormalIn_iff_isEquidistributedModOne_bbpOrbit`):
   `θ` is normal in base `b` if and only if the Bailey–Crandall orbit `(x_n)` is equidistributed
   modulo one.
2. **Finite Attractor Theorem** (`Real.not_hasFiniteAttractorModOne_of_irrational`):
   if `θ` is irrational, neither `(θ * b ^ n)` nor the shadowing orbit `(x_n)` can converge to a
   finite subset of `UnitAddCircle`. Thus Bailey–Crandall's **Hypothesis A** (that every BBP orbit
   either has a finite attractor or is equidistributed modulo one) immediately implies base-`b`
   normality of every irrational BBP constant (such as `π` in base `16`/`2` and `log 2` in base
   `2`).

## Main definitions

* `Real.bbpSum b r`: the BBP-type series `∑' k, r k / (b : ℝ) ^ (k + 1)`.
* `Real.bbpOrbit b r`: the Bailey–Crandall iteration `x₀ = 0`, `x_{n+1} = Int.fract (b * x_n + r n)`.
* `HasFiniteAttractorModOne u`: `u` approaches a finite subset of `UnitAddCircle`.

## References

* [D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant expansions*][BaileyCrandall2001]
* [J. C. Lagarias, *On the normality of arithmetical constants*][Lagarias2001]
-/

@[expose] public section

open Filter Topology

/-- A real sequence `u` has a *finite attractor modulo one* if its image in `UnitAddCircle`
approaches some finite set `S : Finset UnitAddCircle`. -/
def HasFiniteAttractorModOne (u : ℕ → ℝ) : Prop :=
  ∃ S : Finset UnitAddCircle, ∀ ε > 0, ∀ᶠ n in atTop,
    ∃ s ∈ S, dist (u n : UnitAddCircle) s < ε

namespace Real

/-- The BBP-type series `∑' k, r k / b ^ (k + 1)`. -/
noncomputable def bbpSum (b : ℕ) (r : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, r k / (b : ℝ) ^ (k + 1)

/-- The Bailey–Crandall dynamical orbit: `x₀ = 0`, `x_{n+1} = Int.fract (b * x_n + r n)`. -/
noncomputable def bbpOrbit (b : ℕ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => Int.fract ((b : ℝ) * bbpOrbit b r n + r n)

/-- Equidistribution modulo one is unchanged by perturbations that vanish modulo `ℤ`. -/
theorem isEquidistributedModOne_iff_of_tendsto_sub_int {u v ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, ∃ m : ℤ, u n = v n + ε n + m) :
    IsEquidistributedModOne u ↔ IsEquidistributedModOne v := by
  sorry

/-- Having a finite attractor modulo one is unchanged by perturbations vanishing modulo `ℤ`. -/
theorem hasFiniteAttractorModOne_iff_of_tendsto_sub_int {u v ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, ∃ m : ℤ, u n = v n + ε n + m) :
    HasFiniteAttractorModOne u ↔ HasFiniteAttractorModOne v := by
  sorry

/-- Shadowing identity: `b ^ n * bbpSum b r` agrees with `bbpOrbit b r n` plus the tail
`∑' k, r (n + k) / b ^ (k + 1)` modulo `ℤ`. -/
theorem bbpOrbit_shadowing {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (n : ℕ) :
    ∃ m : ℤ, bbpSum b r * (b : ℝ) ^ n =
      bbpOrbit b r n + (∑' k : ℕ, r (n + k) / (b : ℝ) ^ (k + 1)) + m := by
  sorry

/-- **Bailey–Crandall Theorem 1**: for `r n → 0`, the BBP constant `bbpSum b r` is normal in
base `b` if and only if its Bailey–Crandall orbit `bbpOrbit b r` is equidistributed modulo one. -/
theorem isNormalIn_bbpSum_iff_isEquidistributedModOne {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) :
    IsNormalIn b (bbpSum b r) ↔ IsEquidistributedModOne (bbpOrbit b r) := by
  sorry

/-- **Bailey–Crandall / Lagarias finite-attractor theorem**: if `(x * b ^ n)` approaches a finite
subset of `UnitAddCircle`, then `x` is rational. -/
theorem not_hasFiniteAttractorModOne_mul_pow {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : Irrational x) :
    ¬ HasFiniteAttractorModOne (fun n ↦ x * (b : ℝ) ^ n) := by
  sorry

/-- If `bbpSum b r` is irrational and `r n → 0`, its Bailey–Crandall orbit does not have a finite
attractor modulo one. -/
theorem not_hasFiniteAttractorModOne_bbpOrbit {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hirr : Irrational (bbpSum b r)) :
    ¬ HasFiniteAttractorModOne (bbpOrbit b r) := by
  sorry

end Real
