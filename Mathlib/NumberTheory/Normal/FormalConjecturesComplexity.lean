/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.FormalConjectures.Dynamics.SymbolicDynamics.BlockComplexity
public import Mathlib.NumberTheory.Normal.Complexity
public import Mathlib.NumberTheory.Normal.FormalConjectures

/-!
# Formal Conjectures' block complexity and the Adamczewski–Bugeaud theorem

Formal Conjectures (`Mathlib/Imported/FormalConjectures`) measures the complexity of a sequence by
`SymbolicDynamics.blockComplexity`, the extended cardinality of its set of blocks `Fin n → α`.
Subspace-Theorems (`Mathlib/Imported/SubspaceTheorems`) uses `Function.complexity`, the
cardinality of its set of factors, as lists. We show that the two agree for sequences with finitely
many values, and restate the Adamczewski–Bugeaud theorem with Formal Conjectures' definitions.

## Main statements

* `SymbolicDynamics.blockComplexity_eq_complexity`: the two complexities agree.
* `Real.tendsto_blockComplexity_digitSeq_div_atTop`: **Adamczewski–Bugeaud** for
  `NormalNumber.digitSeq` and `SymbolicDynamics.blockComplexity`.

## References

* [B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
  bases*][AdamczewskiBugeaud2007]
-/

@[expose] public section

open Filter Set

namespace SymbolicDynamics

theorem blockComplexity_eq_complexity {α : Type*} {a : ℕ → α} (ha : (range a).Finite) (n : ℕ) :
    blockComplexity a n = Function.complexity a n := by
  set g : ℕ → Fin n → α := fun k i ↦ a (k + i)
  have hb : {w : Fin n → α | ∃ k, ∀ i, w i = a (k + i)} = range g := by
    ext w; simp [g, funext_iff, eq_comm]
  have hf : Function.factors a n = List.ofFn '' range g := by
    rw [← range_comp]; rfl
  have hfin : (range g).Finite :=
    (Finite.pi (t := fun _ : Fin n ↦ range a) fun _ ↦ ha).subset
      (range_subset_iff.2 fun k ↦ by simp [g])
  rw [blockComplexity, hb, Function.complexity, hf,
    ncard_image_of_injective _ List.ofFn_injective, ← hfin.cast_ncard_eq]
  simp

end SymbolicDynamics

namespace Real

/-- **Adamczewski–Bugeaud** in Formal Conjectures' terms: the block complexity of the base-`b`
digits of an algebraic irrational number grows faster than `n`. -/
theorem tendsto_blockComplexity_digitSeq_div_atTop {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hirr : Irrational x) (halg : IsAlgebraic ℚ x) :
    Tendsto (fun n ↦ (SymbolicDynamics.blockComplexity (NormalNumber.digitSeq b x) n).toReal / n)
      atTop atTop := by
  have hfin : (range (digit b x)).Finite :=
    (finite_lt_nat b).subset (range_subset_iff.2 fun n ↦ digit_lt (by omega) x n)
  have hd : NormalNumber.digitSeq b x = digit b x := funext (digitSeq_eq_digit b x)
  simpa [hd, SymbolicDynamics.blockComplexity_eq_complexity hfin] using
    tendsto_complexity_digit_div_atTop hb hirr halg

end Real
