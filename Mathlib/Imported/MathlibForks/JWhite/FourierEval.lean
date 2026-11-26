/-
Copyright (c) 2026 j-white. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: j-white
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Evaluation lemmas for the Fourier characters on `AddCircle`

Imported from the mathlib4 fork
[j-white/mathlib4](https://github.com/j-white/mathlib4/tree/136285cf266c8572f929751d4d7ddb05064d17e5),
branch `fourier-eval-add` (Apache 2.0), where they are added to
`Mathlib/Analysis/Fourier/AddCircle.lean`. The branch also adds `fourier_sub`, which is upstream
now, so only the evaluation lemmas are imported: `fourier n` is an additive character,
`fourier n (x + y) = fourier n x * fourier n y`, and the `neg`/`sub` versions.
-/

@[expose] public section

noncomputable section

open ComplexConjugate

namespace AddCircle

variable {T : ℝ}

/-- `fourier n` is multiplicative in its argument: it is an additive character. -/
theorem fourier_eval_add {n : ℤ} {x y : AddCircle T} :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp_rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

theorem fourier_eval_neg {n : ℤ} {x : AddCircle T} :
    fourier n (-x) = conj (fourier n x) := by
  rw [fourier_apply, smul_neg, fourier_neg']

theorem fourier_eval_sub {n : ℤ} {x y : AddCircle T} :
    fourier n (x - y) = fourier n x * conj (fourier n y) := by
  rw [sub_eq_add_neg, fourier_eval_add, fourier_eval_neg]

end AddCircle
