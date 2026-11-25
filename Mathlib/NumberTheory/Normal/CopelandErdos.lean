/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Champernowne
public import Mathlib.NumberTheory.PrimeCounting

/-!
# The Copeland–Erdős theorem

Let `a₀ < a₁ < a₂ < …` be positive integers such that for every `θ < 1` the number of terms
`≤ N` is at least `N ^ θ` for all large `N`. **Copeland and Erdős** (1946) proved that the real
number `0.a₀ a₁ a₂ …` obtained by concatenating the base-`b` expansions of the `aᵢ` is normal in
base `b`. Applied to the primes this shows that the *Copeland–Erdős constant*
`0.2357111317192329…` is normal in base ten.

## Main definitions

* `Real.IsNormalSeq b d`: the digit sequence `d : ℕ → ℕ` is normal in base `b`.
* `Real.concatStart b a t`, `Real.concatDigit b a n`: positions and digits of the concatenation
  of the base-`b` expansions of `a 0, a 1, …`.
* `Real.concatenation b a`: the real number `0.a₀ a₁ a₂ …` in base `b`.
* `Real.copelandErdos b`: the base-`b` Copeland–Erdős constant (concatenated primes).

## Main statements

* `Real.isNormalIn_ofDigits`: a real number whose digit sequence is normal is normal.
* `Real.isNormalSeq_concatDigit`: the Copeland–Erdős theorem for digit sequences.
* `Real.isNormalIn_concatenation`: the Copeland–Erdős theorem.
* `Real.isNormalIn_copelandErdos`: the concatenation of the primes is normal in every base.

## Proof sketch

By Hoeffding's inequality applied to the independent base-`b` digits of a uniform random
`x ∈ [0, 1)`, all but `b ^ ((1 - δ) ℓ)` of the `ℓ`-digit integers contain the block `w` with
frequency within `ε` of `b⁻ᵏ`. The density hypothesis provides at least `b ^ (θ ℓ)` terms below
`b ^ ℓ` with `θ > 1 - δ`, so the exceptional terms contribute a negligible proportion of digits.

## References

* [A. H. Copeland, P. Erdős, *Note on normal numbers*][CopelandErdos1946]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- A digit sequence `d : ℕ → ℕ` is *normal in base `b`* if every block `w` of `k` base-`b`
digits occurs in it with asymptotic frequency `b⁻ᵏ`. -/
def IsNormalSeq (b : ℕ) (d : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Fin b), Tendsto (fun N : ℕ ↦
    (((Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j) = w j).card : ℝ) / N) atTop
      (𝓝 ((b : ℝ) ^ k)⁻¹)

theorem isNormalIn_iff_isNormalSeq : IsNormalIn b x ↔ IsNormalSeq b (digit b x) := by
  sorry

/-- A real number whose digit sequence is normal in base `b ≥ 2` is normal in base `b`. -/
theorem isNormalIn_ofDigits (hb : 2 ≤ b) {d : ℕ → Fin b} (h : IsNormalSeq b fun n ↦ d n) :
    IsNormalIn b (ofDigits d) := by
  sorry

/-- The position (counted from `0`) at which the base-`b` expansion of `a t` starts in the
concatenation `a 0, a 1, …`. -/
def concatStart (b : ℕ) (a : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (Nat.log b (a i) + 1)

theorem exists_lt_concatStart_succ (b : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    ∃ t, n < concatStart b a (t + 1) := by
  sorry

/-- The `n`-th digit (counted from `0`) of the concatenation of the base-`b` expansions of
`a 0, a 1, a 2, …`. -/
noncomputable def concatDigit (b : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  open Classical in
  let t := Nat.find (exists_lt_concatStart_succ b a n)
  a t / b ^ (concatStart b a (t + 1) - 1 - n) % b

/-- The real number `0.a₀ a₁ a₂ …` obtained by concatenating base-`b` expansions. -/
noncomputable def concatenation (b : ℕ) [NeZero b] (a : ℕ → ℕ) : ℝ :=
  ofDigits fun n ↦ Fin.ofNat b (concatDigit b a n)

/-- **Copeland–Erdős theorem** for digit sequences. -/
theorem isNormalSeq_concatDigit (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a) (ha0 : 0 < a 0)
    (hdens : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ ≤ ((Finset.range (N + 1)).filter fun i ↦ a i ≤ N).card) :
    IsNormalSeq b (concatDigit b a) := by
  sorry

/-- **Copeland–Erdős theorem**: if `a` is an increasing sequence of positive integers having at
least `N ^ θ` terms below `N` for every `θ < 1` and all large `N`, then `0.a₀ a₁ a₂ …` is normal
in base `b`. -/
theorem isNormalIn_concatenation [NeZero b] (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (ha0 : 0 < a 0) (hdens : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ ≤ ((Finset.range (N + 1)).filter fun i ↦ a i ≤ N).card) :
    IsNormalIn b (concatenation b a) := by
  sorry

/-- For every `θ < 1`, there are at least `N ^ θ` primes `≤ N` for all large `N`. -/
theorem eventually_rpow_le_primeCounting {θ : ℝ} (hθ : θ < 1) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ θ ≤ Nat.primeCounting N := by
  sorry

/-- The base-`b` *Copeland–Erdős constant* `0.2 3 5 7 11 13 …`, concatenating the primes. -/
noncomputable def copelandErdos (b : ℕ) [NeZero b] : ℝ :=
  concatenation b (Nat.nth Nat.Prime)

/-- **Copeland–Erdős**: the concatenation of the primes is normal in every base `b ≥ 2`. -/
theorem isNormalIn_copelandErdos [NeZero b] (hb : 2 ≤ b) : IsNormalIn b (copelandErdos b) := by
  sorry

/-- The decimal Copeland–Erdős constant `0.235711131719…` is normal in base ten. -/
theorem isNormalIn_ten_copelandErdos : IsNormalIn 10 (copelandErdos 10) :=
  isNormalIn_copelandErdos (by norm_num)

end Real
