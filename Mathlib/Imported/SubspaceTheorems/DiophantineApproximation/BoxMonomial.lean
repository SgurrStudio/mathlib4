/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Imported.SubspaceTheorems.ArithmeticHeights.Absolute
public import Mathlib.Imported.SubspaceTheorems.ArithmeticHeights.Polynomial
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.MvHasseDeriv
public import Mathlib.Imported.TauCeti.RingTheory.MvPolynomial.Box

/-!
# Polynomials of bounded partial degrees

Roth's auxiliary polynomial is bounded **one variable at a time**: `degreeOf j P ≤ d j`, not
`totalDegree P ≤ D`. Its coefficients therefore sit on the box `∏ j, {0, …, d j}` rather than on
the simplex of monomials of bounded total degree, and this file is the dictionary between the
two descriptions — the box analogue of `ArithmeticHeights/MonomialIndex.lean`, which does the
same work for the simplex.

The index type is `∀ j, Fin (d j + 1)`, so that its cardinality is `∏ j, (d j + 1)` by
`Fintype.card_pi` and no separate counting lemma is needed, and so that a vector indexed by it is
literally a multiplication table — which is what makes the height of a row of the condition
matrix a product of one-variable heights in
`DiophantineApproximation/MonomialHeight.lean`.

## Main results

* `MvPolynomial.boxMonomial`: the exponent named by a point of the box, and
  `MvPolynomial.boxMonomial_injective` and `MvPolynomial.exists_boxMonomial_eq`, which say it
  names each exponent of the box exactly once.
* `MvPolynomial.ofBox`: the polynomial named by a coefficient vector, with
  `MvPolynomial.coeff_ofBox`, `MvPolynomial.degreeOf_ofBox_le`, `MvPolynomial.ofBox_coeff` and
  `MvPolynomial.ofBox_injective`.
* `MvPolynomial.mulHeight_eq_mulHeight_coeff_box` and
  `MvPolynomial.absMulHeight_coeff_box`: the height of such a polynomial is the height of its
  coefficient vector on the box.
* `MvPolynomial.hasseDeriv_eq_zero_of_lt`: a Hasse derivative of an order that leaves the box in
  some variable vanishes — the reason the conditions imposed outside the box are free.

## Implementation notes

⚠ **The index type is a `Pi` type and not a subtype, and that is the whole point.** The obvious
choice, `{ν : σ →₀ ℕ // ∀ j, ν j ≤ d j}`, needs a separate `Fintype` instance, a separate
cardinality computation, and then an equivalence with `∀ j, Fin (d j + 1)` anyway before the
Segre relation `Height.mulHeight_fun_prod_eq` can be applied to a row. Naming the box by
`∀ j, Fin (d j + 1)` from the start removes all three, at the cost of one injection
`MvPolynomial.boxMonomial` into the exponents, which is what every statement here is about.

⚠ **`Fintype (∀ j, Fin (d j + 1))` needs `DecidableEq σ`**, so the variables carry it from
`MvPolynomial.ofBox` on; the statements about `MvPolynomial.boxMonomial` alone do not.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.4.

This is part of Layer 2.6 of the `DiophantineApproximation` roadmap.
-/

-- Ported from rwst/Subspace-Theorems, which does not run Mathlib's numeric-projection linter.
set_option linter.style.numericProjections false

@[expose] public section

open Finsupp

noncomputable section

namespace MvPolynomial

/-! ### The exponents of the box -/

section Monomials

variable {σ : Type*} [Fintype σ] {d : σ → ℕ}

/-- The support of a polynomial with the partial degrees of the box is named by the box. -/
theorem mem_range_boxMonomial_of_mem_support {R : Type*} [CommSemiring R] {P : MvPolynomial σ R}
    (hP : ∀ j, P.degreeOf j ≤ d j) {ν : σ →₀ ℕ} (hν : ν ∈ P.support) :
    ν ∈ Set.range (boxMonomial d) :=
  exists_boxMonomial_eq fun j ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j)

omit [Fintype σ] in
/-- **A Hasse derivative of an order that leaves the box vanishes** on a polynomial of bounded
partial degrees: the binomial factor `(m j).choose (μ j)` of `MvPolynomial.hasseDeriv_monomial`
is zero at every monomial `m` that occurs. -/
theorem hasseDeriv_eq_zero_of_lt {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {j : σ}
    {μ : σ →₀ ℕ} (h : P.degreeOf j < μ j) : hasseDeriv μ P = 0 := by
  classical
  rw [hasseDeriv_apply]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  have hmj : m j < μ j := lt_of_le_of_lt (degreeOf_le_iff.mp le_rfl m hm) h
  rw [prod_choose_eq_zero (fun hle ↦ absurd (hle j) (by omega))]
  simp

end Monomials

/-! ### The coefficient vector of a polynomial with bounded partial degrees -/

section OfBox

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] {d : σ → ℕ}

end OfBox

/-! ### The row of a condition -/

section Row

variable {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]

/-- **The row is a multiplication table** over the variables: both the binomial factor and the
monomial factor are products over `σ`. -/
theorem hasseDerivRow_eq_prod (d : σ → ℕ) (α : σ → R) (μ : σ →₀ ℕ) (I : ∀ j, Fin (d j + 1)) :
    hasseDerivRow d α μ I
      = ∏ j, (((I j : ℕ).choose (μ j) : ℕ) : R) * α j ^ ((I j : ℕ) - μ j) := by
  classical
  rw [hasseDerivRow_def]

/-- The row as the binomial factor `∏ j, (I j).choose (μ j)`, written as a `Finsupp.prod` over
`μ.support`, times the monomial `α ^ (I - μ)`. (This was the definition in the source; Tau Ceti's
`MvPolynomial.hasseDerivRow` is defined as the product over `σ`.) -/
theorem hasseDerivRow_eq_prod_mul (d : σ → ℕ) (α : σ → R) (μ : σ →₀ ℕ) (I : ∀ j, Fin (d j + 1)) :
    hasseDerivRow d α μ I
      = ((μ.prod fun j k ↦ (I j : ℕ).choose k : ℕ) : R) * ∏ j, α j ^ ((I j : ℕ) - μ j) := by
  classical
  rw [hasseDerivRow_def, Finset.prod_mul_distrib]
  congr 1
  rw [← Nat.cast_prod]
  congr 1
  exact (Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)).symm

end Row

/-! ### The height of a polynomial with bounded partial degrees -/

section Height

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
  {d : σ → ℕ}

/-- **The height of a polynomial with the partial degrees of the box is the height of its
coefficient vector** on the box. -/
theorem mulHeight_eq_mulHeight_coeff_box (P : MvPolynomial σ K) (hP : ∀ j, P.degreeOf j ≤ d j) :
    P.mulHeight = Height.mulHeight fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I) :=
  (MvPolynomial.mulHeight_eq_finsupp P).trans <|
    Finsupp.mulHeight_eq_mulHeight_comp _ (boxMonomial d) boxMonomial_injective
    fun _ ha ↦ mem_range_boxMonomial_of_mem_support hP ha

end Height

section Absolute

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K] [NumberField K] {d : σ → ℕ}

/-- The absolute form of `MvPolynomial.mulHeight_eq_mulHeight_coeff_box`: the translation Layer
2.6 makes between the vector Siegel's lemma produces and the polynomial the milestone is
about. -/
theorem absMulHeight_coeff_box (P : MvPolynomial σ K) (hP : ∀ j, P.degreeOf j ≤ d j) :
    NumberField.absMulHeight (fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I))
      = P.mulHeight ^ ((Module.finrank ℚ K : ℝ))⁻¹ := by
  rw [NumberField.absMulHeight_eq, mulHeight_eq_mulHeight_coeff_box P hP]

end Absolute

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: the box has `∏ j, (d j + 1)` monomials**, which is what makes the
coefficient count of Lemma 6.3.4 a product and not a binomial coefficient. -/
example {σ : Type*} [Fintype σ] [DecidableEq σ] (d : σ → ℕ) :
    Fintype.card (∀ j, Fin (d j + 1)) = ∏ j, (d j + 1) := by simp

/-- **Acceptance test: at order `0` the row is the tuple of monomials at `α`**, so that the
condition of order `0` is the vanishing of `P` at `α` itself. -/
example {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R] (d : σ → ℕ) (α : σ → R)
    (I : ∀ j, Fin (d j + 1)) : hasseDerivRow d α 0 I = ∏ j, α j ^ (I j : ℕ) := by
  simp [hasseDerivRow_def]

/-- **Rejection test: `MvPolynomial.hasseDeriv_eq_zero_of_lt` needs the strict inequality.** At
`μ j = degreeOf j P` the derivative survives: `∂_(X 0) (X 0) = 1`. -/
example : hasseDeriv (Finsupp.single (0 : Fin 1) 1) (X 0 : MvPolynomial (Fin 1) ℚ) = 1 := by
  rw [X, hasseDeriv_monomial]
  simp

end Acceptance

end MvPolynomial

end
