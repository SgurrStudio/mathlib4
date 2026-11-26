/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.SchmidtPrimePower

/-!
# Schmidt's theorem for arbitrary bases

Let `b, c ≥ 2` be multiplicatively independent (`bᵐ ≠ cⁿ` for all `m, n ≥ 1`). We show that some
real number is normal in base `b` but in no base `cʲ`, `j ≥ 1` (Schmidt 1960).

## Proof

Let `q = c²` and `X = ∑ᵢ εᵢ q⁻ⁱ⁻¹` for independent fair coins `εᵢ`, as in
`Real.SchmidtPrimePower`: `X` is never normal in base `q`, and we show it is almost surely normal
in base `b` by the Davenport–Erdős–LeVeque criterion.

Choose a prime `p ∣ q` minimising `v_p(b) / v_p(q)` and put `s = v_p(q)`, `r = v_p(b)`, so that
`bˢ = qʳ B` with `p ∤ B ≥ 2` (`exists_reduction`). Write `q = p^γ q'` with `p ∤ q'`. Writing
`l = s m + ε`, the frequency of the pair `(l + d, l)` is `q^{rm} · pᵉ Y Bᵐ` with `p ∤ Y`, and its
Fourier coefficient is at most `Ψ_K(pᵉ Y Bᵐ)`.

* By the Chinese remainder theorem, `1/q^{i+1}` splits into a `p`-part with a unit numerator and a
  `q'`-part (`exists_Psi_le_Phi`). Once `m ≥ K q'`, the `q'`-part is periodic in `m` with period
  `φ(q'ᴷ)` (`dvd_pow_mul_pow_totient_sub_one`), so on each residue class it is a fixed phase.
* Along the class, `Bᵐ` runs through a residue class modulo `pᵗ` with `t` bounded independently of
  `K` (lifting the exponent, `tg_pow_totient`), and averaging the `p`-part over such a class gains a
  factor `1/√2` for each further digit (`sum_Phi_class_le`).
* The pairs where `v_p(bᵈ − 1)` is large are few (`card_bad_le`).

Together these give the second moment bound `secondMoment_le` and `ae_isNormal`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Real.SchmidtGeneral

open NormalNumbers NormalNumbers.CantorLiouville NormalNumbers.CantorLiouvilleAll
  NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare NormalNumbers.CantorSelfSimilar
  Real.SchmidtPrimePower

/-- **Schmidt's theorem.** If `b, c ≥ 2` are multiplicatively independent, some real number is
normal in base `b` and in no base `cʲ`, `j ≥ 1`. -/
theorem exists_isNormalIn_forall_not_isNormalIn_pow {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → b ^ m ≠ c ^ n) :
    ∃ x : ℝ, IsNormalIn b x ∧ ∀ j, 1 ≤ j → ¬ IsNormalIn (c ^ j) x := by
  sorry

end Real.SchmidtGeneral
