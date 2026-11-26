/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.ComplexityTranscendence
public import Mathlib.NumberTheory.Normal.CopelandErdos

/-!
# The digit complexity of algebraic irrationals

Borel's conjecture says that the digits of an algebraic irrational `x` contain every block with
the expected frequency. A normal number in particular contains every block of length `n`, so its
complexity, the number of distinct blocks of length `n`, is `b ^ n`. The strongest unconditional
result in this direction is by **Adamczewski and Bugeaud**: the complexity `p n` of `x` satisfies
`p n / n → ∞`. Here we transfer their theorem, proved via Schmidt's Subspace Theorem in
`Mathlib/Imported/SubspaceTheorems`, to `Real.digit`.

## Main statements

* `Real.tendsto_complexity_digit_div_atTop`: the Adamczewski–Bugeaud theorem for `Real.digit`.

## References

* [B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
  bases*][AdamczewskiBugeaud2007]
-/

@[expose] public section

open Filter

namespace Real

/-- **Adamczewski–Bugeaud**: the number of distinct blocks of length `n` in the base-`b` digits of
an algebraic irrational number grows faster than `n`. -/
theorem tendsto_complexity_digit_div_atTop {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hirr : Irrational x)
    (halg : IsAlgebraic ℚ x) :
    Tendsto (fun n ↦ (Function.complexity (digit b x) n : ℝ) / n) atTop atTop := by
  have : NeZero b := ⟨by omega⟩
  obtain ⟨y, hyx⟩ : ∃ y, y = Int.fract x := ⟨_, rfl⟩
  have hy : y ∈ Set.Ico (0 : ℝ) 1 := hyx ▸ ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hya : ofDigits (digits y b) = y := ofDigits_digits (by omega) hy
  have hyirr : Irrational y := by
    rw [hyx, Int.fract]; exact hirr.sub_intCast ⌊x⌋
  have hyalg : IsAlgebraic ℚ y := by
    rw [hyx, Int.fract]; exact halg.sub (isAlgebraic_intCast (R := ℚ) ⌊x⌋)
  have h := tendsto_complexity_div_atTop hb (a := digits y b) (by rw [hya]; exact hyirr)
    (by rw [hya]; exact hyalg)
  have hd : digit b x = Fin.val ∘ digits y b := by
    funext n; rw [Function.comp_apply, val_digits_eq_digit hy, hyx, digit_fract]
  have hc : ∀ n, Function.complexity (Fin.val ∘ digits y b) n =
      Function.complexity (digits y b) n := fun n ↦ by
    unfold Function.complexity Function.factors
    rw [show (Set.range fun i ↦ Function.factor (Fin.val ∘ digits y b) i n) =
      List.map Fin.val '' Set.range fun i ↦ Function.factor (digits y b) i n by
        rw [← Set.range_comp]; congr 1; funext i
        simp [Function.factor, List.map_ofFn]; rfl]
    exact Set.ncard_image_of_injective _ (List.map_injective_iff.2 Fin.val_injective)
  simpa only [hd, hc] using h

end Real
