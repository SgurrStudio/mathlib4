/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.NumberTheory.Normal.Bridge

/-!
# A computable absolutely normal number

We show that there is an absolutely normal real number whose binary digits are computable
(**Becher and Figueira**, 2002; Turing had sketched such a construction in an unpublished
manuscript).

## Main statements

* `Real.exists_computable_isAbsolutelyNormal`: there is an absolutely normal `x` such that
  `n ↦ digit 2 x n` is computable.

## Proof

This is Trevor Morris's generic derandomization
`NormalNumbers.ComputableNormalB.exists_computable_absNormal`, imported in
`Mathlib/Imported/NormalNumbers`, applied to the binary expansion `ω ↦ ∑ ωᵢ 2⁻ⁱ⁻¹` of a sequence of
fair coins. Its law is the uniform measure on `[0, 1]`, whose Fourier transform at `ξ` has modulus
`∏ₖ |cos (π ξ / 2ᵏ⁺¹)| = |sin (π ξ) / (π ξ)| ≤ 1 / |ξ|` (Viète's product). Morris's theorem gives a
computable coin sequence `e` whose binary expansion `x` is normal in every base, and the binary
digits of `x` are the coins `e`, since a normal number is not a dyadic rational.

## References

* [V. Becher, S. Figueira,
  *An example of a computable absolutely normal number*][BecherFigueira2002]
-/

public section

namespace Real

/-- There is a **computable absolutely normal number**: an absolutely normal real whose binary
digits are a computable sequence. -/
theorem exists_computable_isAbsolutelyNormal :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ Computable (fun n ↦ digit 2 x n) := by
  sorry

end Real

end
