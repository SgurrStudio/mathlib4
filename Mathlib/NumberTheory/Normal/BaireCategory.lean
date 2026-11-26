/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Borel
public import Mathlib.Topology.GDelta.Basic

/-!
# Baire category of normal and disjunctive numbers

While Borel's normal number theorem (`Real.ae_isAbsolutelyNormal`) shows that almost every real
number (in the sense of Lebesgue measure) is absolutely normal, from the standpoint of Baire
category the situation is completely reversed:

* The set of numbers whose digit frequency converges for even a single digit in a single base
  `b ≥ 2` is meagre (`Real.isMeagre_setOf_tendsto_digitFreq`). Consequently, the sets of simply
  normal, normal, and absolutely normal numbers—and even the union of simply normal numbers across
  all bases `b ≥ 2`—are meagre in `ℝ` (Šalát 1966).
* By contrast, the set of disjunctive numbers in base `b ≥ 2` (`Real.IsDisjunctiveIn b`), as well
  as the set of *absolutely disjunctive* numbers (disjunctive in every base `b ≥ 2`), is a dense
  `Gδ` set, hence residual (comeagre) in `ℝ`.
* Combining these gives a sharp measure-versus-category dichotomy and a strong separation between
  disjunctivity and normality: a residual (hence dense and uncountable) Lebesgue-null set of real
  numbers is disjunctive in *every* base `b ≥ 2` yet simply normal in *no* base `b ≥ 2`.
* Moreover, every real number can be written as the sum of two absolutely disjunctive numbers that
  are not simply normal in any base `b ≥ 2`.

## Main statements

* `Real.isGδ_setOf_isDisjunctiveIn`, `Real.residual_setOf_isDisjunctiveIn`: for `2 ≤ b`,
  `{x : ℝ | IsDisjunctiveIn b x}` is a dense `Gδ` (hence residual) set.
* `Real.isGδ_setOf_forall_isDisjunctiveIn`, `Real.residual_setOf_forall_isDisjunctiveIn`: the set
  of absolutely disjunctive reals is a dense `Gδ` (hence residual) set.
* `Real.isMeagre_setOf_tendsto_digitFreq`: for `2 ≤ b` and any digit `d : Fin b`, the set of reals
  whose frequency of digit `d` converges is meagre.
* `Real.isMeagre_setOf_isSimplyNormalIn`, `Real.isMeagre_setOf_isNormalIn`,
  `Real.isMeagre_setOf_isAbsolutelyNormal`, `Real.isMeagre_setOf_exists_isSimplyNormalIn`:
  normality (even simple normality in some base `b ≥ 2`) is meagre.
* `Real.residual_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn`: generic reals are
  absolutely disjunctive yet simply normal in no base `b ≥ 2`.
* `Real.volume_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn`: this residual set has
  Lebesgue measure zero.
* `Real.exists_add_eq_forall_isDisjunctiveIn_and_not_isSimplyNormalIn`: every real is a sum of two
  such numbers.

## References

* T. Šalát, *A remark on normal numbers*, Rev. Roumaine Math. Pures Appl. 11 (1966), 53–56.
* J. C. Oxtoby, *Measure and Category*, Springer GTM 2, 2nd ed., 1980.
* C. S. Calude and T. Zamfirescu, *Most numbers obey no probability laws*, Publ. Math. Debrecen
  54 (1999), 619–623.
-/

@[expose] public section

open Filter Topology Set MeasureTheory

namespace Real

/-- For `2 ≤ b`, the set of base-`b` disjunctive real numbers is a `Gδ` set. -/
theorem isGδ_setOf_isDisjunctiveIn {b : ℕ} (hb : 2 ≤ b) :
    IsGδ {x : ℝ | IsDisjunctiveIn b x} := by sorry

/-- For `2 ≤ b`, the set of base-`b` disjunctive real numbers is residual (comeagre) in `ℝ`. -/
theorem residual_setOf_isDisjunctiveIn {b : ℕ} (hb : 2 ≤ b) :
    {x : ℝ | IsDisjunctiveIn b x} ∈ residual ℝ := by sorry

/-- For `2 ≤ b`, the set of base-`b` disjunctive real numbers is dense in `ℝ`. -/
theorem dense_setOf_isDisjunctiveIn {b : ℕ} (hb : 2 ≤ b) :
    Dense {x : ℝ | IsDisjunctiveIn b x} := by sorry

/-- The set of *absolutely disjunctive* real numbers (disjunctive in every base `b ≥ 2`) is a
`Gδ` set in `ℝ`. -/
theorem isGδ_setOf_forall_isDisjunctiveIn :
    IsGδ {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} := by sorry

/-- The set of *absolutely disjunctive* real numbers is residual (comeagre) in `ℝ`. -/
theorem residual_setOf_forall_isDisjunctiveIn :
    {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} ∈ residual ℝ := by sorry

/-- The set of *absolutely disjunctive* real numbers is dense in `ℝ`. -/
theorem dense_setOf_forall_isDisjunctiveIn :
    Dense {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} := by sorry

/-- On a residual set of reals, the frequency of digit `d` in base `b ≥ 2` drops below `ε`
infinitely often. -/
theorem residual_setOf_frequently_digitFreq_lt {b : ℕ} (hb : 2 ≤ b) (d : Fin b)
    {ε : ℝ} (hε : 0 < ε) :
    {x : ℝ | ∃ᶠ N in atTop, (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N < ε} ∈
      residual ℝ := by sorry

/-- On a residual set of reals, the frequency of digit `d` in base `b ≥ 2` exceeds `1 - ε`
infinitely often. -/
theorem residual_setOf_frequently_digitFreq_gt {b : ℕ} (hb : 2 ≤ b) (d : Fin b)
    {ε : ℝ} (hε : 0 < ε) :
    {x : ℝ | ∃ᶠ N in atTop,
      1 - ε < (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N} ∈ residual ℝ := by sorry

/-- For any base `b ≥ 2` and digit `d : Fin b`, the set of real numbers for which the asymptotic
frequency of digit `d` converges is meagre in `ℝ` (Šalát 1966). -/
theorem isMeagre_setOf_tendsto_digitFreq {b : ℕ} (hb : 2 ≤ b) (d : Fin b) :
    IsMeagre {x : ℝ | ∃ L : ℝ,
      Tendsto (fun N : ℕ ↦ (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N) atTop (𝓝 L)} := by
  sorry

/-- For `2 ≤ b`, the set of base-`b` simply normal numbers is meagre in `ℝ`. -/
theorem isMeagre_setOf_isSimplyNormalIn {b : ℕ} (hb : 2 ≤ b) :
    IsMeagre {x : ℝ | IsSimplyNormalIn b x} := by sorry

/-- For `2 ≤ b`, the set of base-`b` normal numbers is meagre in `ℝ`. -/
theorem isMeagre_setOf_isNormalIn {b : ℕ} (hb : 2 ≤ b) :
    IsMeagre {x : ℝ | IsNormalIn b x} := by sorry

/-- The set of real numbers that are simply normal in *at least one* base `b ≥ 2` is meagre in
`ℝ`. -/
theorem isMeagre_setOf_exists_isSimplyNormalIn :
    IsMeagre {x : ℝ | ∃ b : ℕ, 2 ≤ b ∧ IsSimplyNormalIn b x} := by sorry

/-- The set of real numbers that are normal in *at least one* base `b ≥ 2` is meagre in `ℝ`. -/
theorem isMeagre_setOf_exists_isNormalIn :
    IsMeagre {x : ℝ | ∃ b : ℕ, 2 ≤ b ∧ IsNormalIn b x} := by sorry

/-- The set of absolutely normal numbers is meagre in `ℝ`, in sharp contrast to Borel's theorem
(`Real.ae_isAbsolutelyNormal`) which states that it has full Lebesgue measure. -/
theorem isMeagre_setOf_isAbsolutelyNormal :
    IsMeagre {x : ℝ | IsAbsolutelyNormal x} := by sorry

/-- The generic real number (in the sense of Baire category) is disjunctive in *every* base
`b ≥ 2` yet simply normal in *no* base `b ≥ 2` (Calude–Zamfirescu 1999). -/
theorem residual_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x} ∈ residual ℝ := by
  sorry

/-- The set of absolutely disjunctive, nowhere simply normal reals is dense in `ℝ`. -/
theorem dense_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    Dense {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x} := by sorry

/-- The set of absolutely disjunctive, nowhere simply normal reals is uncountable. -/
theorem not_countable_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    ¬ {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x}.Countable := by
  sorry

/-- There exists a real number that is disjunctive in every base `b ≥ 2` yet not simply normal in
any base `b ≥ 2`. -/
theorem exists_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    ∃ x : ℝ, ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x := by sorry

/-- Measure-versus-category dichotomy: although the set of absolutely disjunctive, nowhere simply
normal numbers is residual (comeagre) in `ℝ`, it has Lebesgue measure zero. -/
theorem volume_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    volume {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x} = 0 := by
  sorry

/-- Every real number `y` can be written as a sum `x₁ + x₂ = y` of two real numbers that are both
disjunctive in every base `b ≥ 2` yet simply normal in no base `b ≥ 2`. -/
theorem exists_add_eq_forall_isDisjunctiveIn_and_not_isSimplyNormalIn (y : ℝ) :
    ∃ x₁ x₂ : ℝ, x₁ + x₂ = y ∧
      (∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x₁ ∧ ¬ IsSimplyNormalIn b x₁) ∧
      (∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x₂ ∧ ¬ IsSimplyNormalIn b x₂) := by sorry

end Real
