/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.BoxMonomial
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.MvHasseDerivHeight
public import Mathlib.Imported.TauCeti.NumberTheory.Height.MvPolynomial
public import Mathlib.Imported.TauCeti.NumberTheory.Height.Basic

/-!
# The height of a row of the index conditions

A condition "`∂_μ P` vanishes at `α`" is a linear form in the coefficients of `P`, and Siegel's
lemma charges for it through the height of that form. This file computes the charge. The entry
of the row at the monomial `X ^ I` is

`(∏ j, (I j).choose (μ j)) * ∏ j, α j ^ (I j - μ j)`,

a **multiplication table** over the variables, so `Height.mulHeight_fun_prod_eq` turns its height
into a product of one-variable heights, and each of those splits — by
`Height.mulHeight_mul_le` — into a binomial part and a monomial part. The binomial part is a
tuple of natural numbers at most `2 ^ d j`, the monomial part is the tuple of powers
`α j ^ k, k ≤ d j`, whose height is exactly `H(α j) ^ d j`. The answer is Bombieri–Gubler's
`∏ j, (2 H(α j)) ^ d j`.

## Main results

* `Height.mulHeight_le_pow_totalWeight`: **the transport**, from a bound on the local factors to
  a bound on the height, for a single tuple.
* `Height.mulHeight_natCast_le`: the height of a tuple of natural numbers at most `N` is at most
  `N ^ totalWeight K`.
* `Height.mulHeight_pow_range`: the height of the tuple of powers `α ^ k`, `k ≤ d`, is
  `H(α) ^ d` — *exactly*, and with no hypothesis on `α`.
* `MvPolynomial.hasseDerivRow`: the row, and `MvPolynomial.hasseDerivRow_eq_prod`, which is the
  observation that it is a multiplication table.
* `MvPolynomial.mulHeight_hasseDerivRow_le`: **the estimate**,
  `H(row) ≤ (2 ^ ∑ j, d j) ^ totalWeight K * ∏ j, H(α j) ^ d j`.

## Implementation notes

⚠ **The transport lemma the roadmap records as missing is the one-input, one-sided one, and it
is three lines.** `ArithmeticHeights/GaussLemma.lean` has
`Finsupp.mulHeight_le_of_forall_iSup_le`, which compares the local factor of one object with the
*product* of those of two others and demands **equality** at the nonarchimedean absolute values —
what Gauss's lemma supplies and what a row of binomial coefficients does not. What is needed here
is the inequality at both kinds of place with a single tuple on each side, and it follows from
`Multiset.prod_map_le_prod_map₀` at the archimedean places and `finprod_le_finprod₀` at the
others. Only the constant form (the second tuple being `1`) is stated, because that is the only
form used: the rest of the estimate is carried by the Segre relation, which is an equality.

⚠ **The whole estimate is one equality and two comparisons, and none of them is an induction on
the number of variables.** `Height.mulHeight_fun_prod_eq` is Mathlib's Segre relation for an
arbitrary finite family, so the passage from `m` variables to one is free; and
`Height.mulHeight_pow_range` is an equality rather than an estimate, so the only loss in the
whole file is the binomial factor `2 ^ ∑ j, d j` — which is exactly the `log 2` that Lemma 6.3.4
carries in its bound.

⚠ **`Height.mulHeight_pow_range` compares the tuple of powers with the pair `![α ^ d, 1]`.** The
supremum of `v (α ^ k)` over `k ≤ d` is `max (v α) 1 ^ d` whichever side of `1` the value `v α`
falls on, and that is the local factor of the pair; so the two tuples have the same height at
every absolute value at once, and `Height.mulHeight_eq_of_forall_iSup_eq` turns that into an
equality of heights. Computing the product over the places directly would need the product
formula and would not be shorter.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.4.

This is part of Layer 2.6 of the `DiophantineApproximation` roadmap.
-/

-- Ported from rwst/Subspace-Theorems, which does not run Mathlib's numeric-projection linter.
set_option linter.style.numericProjections false

@[expose] public section

open Height Height.AdmissibleAbsValues Real

noncomputable section

namespace Height

/-! ### Transport from local factors to the height -/

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*} [Finite ι] [Finite ι']

/-! ### Two tuples whose height is known -/

end Height

/-! ### The row of a condition, and its height -/

namespace MvPolynomial

open Height

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] [Height.AdmissibleAbsValues F]

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: the tuple of powers `α ^ k`, `k ≤ d`, has height exactly `H(α) ^ d`.** -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] (α : K) :
    Height.mulHeight (fun k : Fin 4 ↦ α ^ (k : ℕ)) = Height.mulHeight₁ α ^ 3 :=
  Height.mulHeight_pow_range α 3

/-- **Acceptance test: the transport at `C = 1`.** A tuple whose local factor is at most `1` at
every absolute value has height exactly `1`, since the height is always at least `1`. -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι] {x : ι → K}
    (h : ∀ v : AbsoluteValue K ℝ, (⨆ i, v (x i)) ≤ 1) : Height.mulHeight x = 1 :=
  le_antisymm
    (by simpa using
      Height.mulHeight_le_pow_totalWeight le_rfl (fun v _ ↦ h v) fun v _ ↦ h v)
    (Height.one_le_mulHeight x)

end Acceptance

end MvPolynomial

end
