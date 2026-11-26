/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Cassels
public import Mathlib.NumberTheory.Normal.CopelandErdos
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Schmidt's theorem when one base is a prime power

Let `p` be a prime and `b ≥ 2` an integer that is not a power of `p`. We show that some real
number is normal in base `b` but not in base `p` (hence in no base `pʲ`).

## Proof

Fix `q = pᵏ ≥ 3` and let `X = ∑ᵢ εᵢ q⁻ⁱ⁻¹` for independent fair coins `εᵢ`. Every base-`q` digit of
`X` is `0` or `1`, so `X` is never normal in base `q`. Its Fourier transform satisfies
`|𝔼 e(ξX)| ≤ ∏_{i<K} |cos(πξ/qⁱ⁺¹)|` for every `K` (`charFun_le`), and we show that `X` is almost
surely normal in base `b` by the Davenport–Erdős–LeVeque criterion.

Write `b = pᵃ m` with `p ∤ m` and `m ≥ 2`. The frequency of a pair `(l + d, l)` in the second
moment is `h (bᵈ − 1) bˡ = p^v · w mˡ` with `p ∤ w`. Dropping the leading cosine factors, its
coefficient is at most `Ψ_K(pʳ w mˡ)` with `r = v mod k` (`charFun_le_Psi`). For `g = m^{2(p−1)}`
and `t = v_p(g − 1)`, lifting the exponent shows that `l ↦ w gˡ` runs once through the residues
`≡ w mod pᵗ` modulo `p^{t+n}` as `l < pⁿ`. Averaging `Ψ_K` over a residue class modulo `pᵗ` gains a
factor `1/√2` for each further base-`q` digit, because
`∑_{r<q} |cos(θ + πr/q)| ≤ q/√2` (`sum_abs_cos_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Real.SchmidtPrimePower

open NormalNumbers NormalNumbers.CantorLiouville NormalNumbers.CantorLiouvilleAll
  NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare NormalNumbers.CantorSelfSimilar

/-- **Schmidt's theorem for a prime-power base.** If `b ≥ 2` is not a power of the prime `p`,
some real number is normal in base `b` and in no base `pʲ`, `j ≥ 1`. -/
theorem exists_isNormalIn_forall_not_isNormalIn_pow {p : ℕ} (hp : p.Prime) {b : ℕ} (hb : 2 ≤ b)
    (hpow : ∀ i, b ≠ p ^ i) :
    ∃ x : ℝ, IsNormalIn b x ∧ ∀ j, 1 ≤ j → ¬ IsNormalIn (p ^ j) x := by
  sorry

end Real.SchmidtPrimePower
