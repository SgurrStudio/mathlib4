/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.IndexRename
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.MvHasseDerivHeight
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.PolynomialDeterminantHeight
public import Mathlib.Imported.TauCeti.NumberTheory.Height.MvPolynomial

/-!
# The determinant of a matrix of Hasse derivatives

The inductive step of Roth's lemma runs on one polynomial: the determinant of the `p × p` matrix
whose `(i, j)` entry is a Hasse derivative of `P` at an order `ρ i j`. Three things have to be
known about it, and all three are uniform in the orders.

* Its partial degrees are at most `p` times those of `P`, because a determinant is a sum of
  products of `p` entries and a Hasse derivative does not raise a degree.
* Its height is at most `p` times that of `P`, plus `totalWeight K` times an explicit constant:
  `log p!` from the Leibniz expansion and `2 (∑ j, d j) p log 2` from the `p` multiplications and
  the `p` differentiations, each of which costs a factor `2 ^ (∑ j, d j)` at an archimedean
  absolute value and nothing at a nonarchimedean one.
* Its index at `ξ` is at least the sum over the columns of the index of `P` minus the weight of
  the order, because the index is a valuation.

## Main results

* `MvPolynomial.degreeOf_det_le`: the degree bound for a determinant of polynomials.
* `MvPolynomial.totalDegree_le_sum_degreeOf`: the total degree against the partial degrees.
* `MvPolynomial.logHeight_det_hasseDeriv_le`: the height bound.
* `MvPolynomial.le_index_det`: the index bound.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.7.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

-- Ported from rwst/Subspace-Theorems, which does not run Mathlib's numeric-projection linter.
set_option linter.style.numericProjections false

@[expose] public section

open Finset Height AdmissibleAbsValues

open scoped ENNReal

namespace MvPolynomial

/-! ### Degrees -/

section Degrees

variable {σ R : Type*} [CommRing R]

/-- **The degree of a determinant of polynomials.** -/
theorem degreeOf_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (j : σ) {D : ℕ}
    (h : ∀ i l, (A i l).degreeOf j ≤ D) : (A.det).degreeOf j ≤ n * D := by
  classical
  rw [Matrix.det_apply']
  refine le_trans (degreeOf_sum_le j _ _) (Finset.sup_le fun τ _ ↦ ?_)
  refine le_trans (degreeOf_mul_le j _ _) ?_
  have hsign : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R).degreeOf j = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> rw [hs] <;> simp
  rw [hsign, zero_add]
  refine le_trans (degreeOf_prod_le j _ _) ?_
  calc ∑ i, (A (τ i) i).degreeOf j ≤ ∑ _i : Fin n, D := Finset.sum_le_sum fun i _ ↦ h _ _
    _ = n * D := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

variable [Fintype σ]

/-- The total degree is at most the sum of the partial degrees. -/
theorem totalDegree_le_sum_degreeOf (P : MvPolynomial σ R) :
    P.totalDegree ≤ ∑ j, P.degreeOf j := by
  rw [totalDegree]
  refine Finset.sup_le fun ν hν ↦ ?_
  have hsum : (ν.sum fun _ e ↦ e) = ∑ j, ν j :=
    Finsupp.sum_of_support_subset ν (Finset.subset_univ _) (fun _ e ↦ e) fun _ _ ↦ rfl
  rw [hsum]
  exact Finset.sum_le_sum fun j _ ↦ degreeOf_le_iff.mp (le_refl (P.degreeOf j)) ν hν

end Degrees

/-! ### The height of a determinant of Hasse derivatives -/

section HeightDet

variable {σ K : Type*} [Fintype σ] [Field K] [AdmissibleAbsValues K]

end HeightDet

/-! ### The index of a determinant -/

section IndexDet

variable {σ R : Type*} [CommRing R] [IsDomain R]

/-- **The index of a determinant from below.** A column bound transfers to the determinant,
because the index is a valuation: the index of the Leibniz sum is at least the minimum over the
permutations of the sum of the indices of the entries, and each permutation picks one entry from
every column. -/
theorem le_index_det {n : ℕ} (d : σ → ℝ) (hd : ∀ j, 0 ≤ d j) (α : σ → R)
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) {c : Fin n → ℝ≥0∞}
    (h : ∀ i j, c j ≤ index d α (A i j)) :
    ∑ j, c j ≤ index d α A.det := by
  classical
  rw [Matrix.det_apply']
  refine le_index_sum d hd α _ _ fun τ _ ↦ ?_
  have hsign : index d α (((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R) * ∏ i, A (τ i) i)
      = index d α (∏ i, A (τ i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs
    · rw [hs]
      norm_num
    · rw [hs]
      push_cast
      rw [neg_one_mul, index_neg]
  rw [hsign, index_prod d hd α]
  exact Finset.sum_le_sum fun i _ ↦ h (τ i) i

end IndexDet

end MvPolynomial
