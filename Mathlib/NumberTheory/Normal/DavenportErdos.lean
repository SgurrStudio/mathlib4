/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Normal.CopelandErdos
public import Mathlib.NumberTheory.Normal.DifferenceTest
public import Mathlib.NumberTheory.Normal.FejerCount

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Imported.TauCeti.Analysis.Polynomial.L1Norm
import Mathlib.NumberTheory.Normal.PiatetskiShapiro
import Mathlib.Topology.Algebra.Order.Polynomial

/-!
# The Davenport–Erdős theorem

Let `f` be a non-constant polynomial with integer coefficients taking positive values at the
positive integers. **Davenport and Erdős** (1952) proved that the number
`0.f(1) f(2) f(3) …`, obtained by concatenating the base-`b` expansions of `f(1), f(2), …`, is
normal in base `b`. For `f = X` this is Champernowne's theorem
(`Mathlib.NumberTheory.Normal.Champernowne`); for `f = X ^ 2` it says `0.1 4 9 16 25 …` is normal.

Copeland–Erdős (`Real.isNormalIn_concatenation`) does not apply: the values of a polynomial of
degree `d ≥ 2` have density `N ^ (1 / d - 1)` in `[1, N]`, below the `N ^ (θ - 1)` it needs
for every `θ < 1`.

## Main statements

* `Real.isNormalIn_concatenation_polynomial`: the Davenport–Erdős theorem.
* `Real.isNormalIn_concatenation_sq`: Besicovitch's theorem, the case `f = X ^ 2`.
* `Real.isNormalIn_concatenation_of_growth`: normality of `0.a₀ a₁ a₂ …` for sequences of size
  `≍ t ^ d` whose scaled Weyl sums are uniformly small.

## Proof

Following Davenport and Erdős, it suffices by Piatetski-Shapiro's hot-spot criterion
(`Real.isNormalIn_of_eventually_le`, with `C = 8`) to bound how often a block `w` of length `k`
occurs inside the terms `f(1), …, f(T)`
(`Real.isNormalIn_concatenation_of_concatInternal_le`). Sort the occurrences by their distance
`s` from the end of the term. The block at distance `s` in `f(t)` is `w` exactly when
`f(t) / b ^ (s + k)` lies in an interval of length `b ^ (-k)` modulo one, and these are counted
by Fejér squares (`Complex.card_fract_sub_lt_le`), giving `8 T / b ^ k` plus Weyl sums. For
the positions `s` away from the `δ log T` lowest and highest ones, the leading coefficient
of `h f(t) / b ^ (s + k)` lies in `[T ^ (δ - d), T ^ (-δ)]`, and the `d`-th difference test
(`Polynomial.eventually_norm_polyExpSum_le`, by van der Corput differencing with Tau Ceti's
`vanDerCorput_inequality`) makes the Weyl sums `o(T)`. The remaining `2 δ log T` positions cost
a fraction `O(δ)` of the `≈ d T log T` digits (`Real.isNormalIn_concatenation_of_growth`).

For squares there is an elementary proof by **Pollack and Vandehey**, which we follow for
`Real.isNormalIn_concatenation_sq`: by the few-bad-terms criterion
(`Real.isNormalSeq_concatDigit_of_concatBad`) it is enough that few `n ^ 2` have a bad block
frequency. Cut `n ^ 2 = u * b ^ ℓ + v` with `b ^ ℓ ≈ n`. The upper half `u` takes each value at
most `b ^ ℓ / n` times, and the lower half `v = n ^ 2 mod b ^ ℓ` takes each value rarely on average
since `x ^ 2 ≡ y ^ 2 [MOD b ^ ℓ]` has few solutions; so few `n` have a bad half.

## References

* [H. Davenport, P. Erdős, *Note on normal decimals*][DavenportErdos1952]
* [A. S. Besicovitch, *The asymptotic distribution of the numerals in the decimal representation
  of the squares of the natural numbers*][Besicovitch1935]
* [P. Pollack, J. Vandehey, *Besicovitch, bisection, and the normality of
  0.(1)(4)(9)(16)(25)…*][PollackVandehey2015]
* [Y. Nakai, I. Shiokawa, *Discrepancy estimates for a class of normal numbers*][NakaiShiokawa1992]
-/

@[expose] public section

open Polynomial Filter Topology Finset

/-- `τ(b ^ ℓ)` grows polynomially in `ℓ`. -/
theorem _root_.Nat.card_divisors_pow_le {b : ℕ} (hb : 0 < b) (ℓ : ℕ) :
    (b ^ ℓ).divisors.card ≤ (ℓ + 1) ^ b.primeFactors.card * b.divisors.card := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp [hb.ne']
  rw [Nat.card_divisors (pow_ne_zero _ hb.ne'), Nat.card_divisors hb.ne',
    Nat.primeFactors_pow _ hℓ.ne', Nat.factorization_pow, ← prod_const, ← prod_mul_distrib]
  refine prod_le_prod fun p _ ↦ ?_
  simp only [Finsupp.smul_apply, smul_eq_mul]
  nlinarith

namespace Real

variable {b k : ℕ}

section Squares

/-- Cutting the expansion of `x * b ^ ℓ + y` into its top and its last `ℓ` digits. -/
theorem natBlockCount_mul_pow_add (hb : 0 < b) (w : Fin k → Fin b) {ℓ y : ℕ} (hy : y < b ^ ℓ)
    (hk : 0 < k) (hkℓ : k ≤ ℓ) (m₁ x : ℕ) :
    natBlockCount b m₁ x w + natBlockCount b ℓ y w ≤ natBlockCount b (m₁ + ℓ) (x * b ^ ℓ + y) w ∧
    natBlockCount b (m₁ + ℓ) (x * b ^ ℓ + y) w ≤
      natBlockCount b m₁ x w + natBlockCount b ℓ y w + k := by
  classical
  set c := blockCode w
  have hlow : ∀ s, s + k ≤ ℓ → (x * b ^ ℓ + y) / b ^ s % b ^ k = y / b ^ s % b ^ k := fun s hs ↦ by
    obtain ⟨r, rfl⟩ : ∃ r, ℓ = s + k + r := ⟨ℓ - (s + k), by omega⟩
    have : x * b ^ (s + k + r) + y = y + b ^ s * (b ^ k * (x * b ^ r)) := by
      rw [pow_add, pow_add]; ring
    rw [this, Nat.add_mul_div_left _ _ (pow_pos hb s), Nat.add_mul_mod_self_left]
  have hhigh : ∀ s, (x * b ^ ℓ + y) / b ^ (s + ℓ) % b ^ k = x / b ^ s % b ^ k := fun s ↦ by
    rw [show b ^ (s + ℓ) = b ^ ℓ * b ^ s by rw [pow_add, mul_comm], ← Nat.div_div_eq_div_mul,
      add_comm,
      Nat.add_mul_div_right _ _ (pow_pos hb ℓ), Nat.div_eq_of_lt hy, zero_add]
  set F := (Finset.range (m₁ + ℓ + 1 - k)).filter fun s ↦ (x * b ^ ℓ + y) / b ^ s % b ^ k = c
  set Lo := (Finset.range (ℓ + 1 - k)).filter fun s ↦ y / b ^ s % b ^ k = c
  set Hi := ((Finset.range (m₁ + 1 - k)).filter fun s ↦ x / b ^ s % b ^ k = c).map
    (addRightEmbedding ℓ)
  have hHi : Hi.card = natBlockCount b m₁ x w := by simp [Hi, natBlockCount, c]
  have hdisj : Disjoint Lo Hi := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Lo, Hi, Finset.mem_filter, Finset.mem_range, Finset.mem_map,
      addRightEmbedding_apply] at hs hs'
    obtain ⟨t, _, rfl⟩ := hs'
    omega
  constructor
  · rw [← hHi]
    change Hi.card + Lo.card ≤ F.card
    rw [add_comm, ← Finset.card_union_of_disjoint hdisj]
    refine Finset.card_le_card fun s hs ↦ ?_
    simp only [Finset.mem_union, Lo, Hi, Finset.mem_filter, Finset.mem_range, Finset.mem_map,
      addRightEmbedding_apply] at hs
    simp only [F, Finset.mem_filter, Finset.mem_range]
    rcases hs with ⟨h1, h2⟩ | ⟨t, ⟨h1, h2⟩, rfl⟩
    · exact ⟨by omega, by rw [hlow s (by omega)]; exact h2⟩
    · exact ⟨by omega, by rw [hhigh]; exact h2⟩
  · have hsub : F ⊆ (Lo ∪ Hi) ∪ Finset.Ico (ℓ + 1 - k) ℓ := by
      intro s hs
      simp only [F, Finset.mem_filter, Finset.mem_range] at hs
      simp only [Finset.mem_union, Lo, Hi, Finset.mem_filter, Finset.mem_range, Finset.mem_map,
        addRightEmbedding_apply, Finset.mem_Ico]
      by_cases h1 : s + k ≤ ℓ
      · exact Or.inl (Or.inl ⟨by omega, by rw [← hlow s h1]; exact hs.2⟩)
      by_cases h2 : ℓ ≤ s
      · refine Or.inl (Or.inr ⟨s - ℓ, ⟨by omega, ?_⟩, by omega⟩)
        rw [← hhigh, Nat.sub_add_cancel h2]; exact hs.2
      · exact Or.inr ⟨by omega, by omega⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_union_of_disjoint hdisj, hHi, Nat.card_Ico]
    change natBlockCount b ℓ y w + _ + _ ≤ _
    omega

/-- `a y + c ≡ 0 [MOD Q]` has at most `gcd(Q, a)` solutions modulo `Q`. -/
theorem card_filter_dvd_mul_add_le {Q : ℕ} (hQ : 0 < Q) (a c : ℕ) :
    ((range Q).filter fun y ↦ Q ∣ a * y + c).card ≤ Nat.gcd Q a := by
  set D := Q / Nat.gcd Q a
  have hg : 0 < Nat.gcd Q a := Nat.gcd_pos_of_pos_left _ hQ
  have hQD : Q = D * Nat.gcd Q a := (Nat.div_mul_cancel (Nat.gcd_dvd_left Q a)).symm
  have hD : 0 < D := Nat.div_pos (Nat.gcd_le_left _ hQ) hg
  calc _ ≤ (range (Nat.gcd Q a)).card := by
        refine card_le_card_of_injOn (fun y ↦ y / D) (fun y hy ↦ ?_) fun y hy y' hy' h ↦ ?_
        · simp only [coe_filter, mem_range, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hy ⊢
          exact Nat.div_lt_of_lt_mul (hQD ▸ hy.1)
        · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hy hy'
          have h1 : a * y + c ≡ a * y' + c [MOD Q] :=
            (Nat.modEq_zero_iff_dvd.2 hy.2).trans (Nat.modEq_zero_iff_dvd.2 hy'.2).symm
          have h2 : y % D = y' % D :=
            Nat.ModEq.cancel_left_div_gcd hQ (Nat.ModEq.add_right_cancel' c h1)
          simp only at h
          rw [← Nat.div_add_mod y D, ← Nat.div_add_mod y' D, h, h2]
    _ = _ := card_range _

/-- The congruence `x ^ 2 ≡ y ^ 2 [MOD Q]` has at most `2 Q τ(Q)` solutions modulo `Q`. -/
theorem card_filter_sq_modEq_le {Q : ℕ} (hQ : 0 < Q) :
    ((range Q ×ˢ range Q).filter fun p : ℕ × ℕ ↦ p.1 ^ 2 ≡ p.2 ^ 2 [MOD Q]).card ≤
      2 * Q * Q.divisors.card := by
  classical
  -- substitute `x ≡ y + u`
  have h1 : ((range Q ×ˢ range Q).filter fun p : ℕ × ℕ ↦ p.1 ^ 2 ≡ p.2 ^ 2 [MOD Q]).card ≤
      ((range Q).sigma fun u ↦ (range Q).filter fun y ↦ Q ∣ (2 * u) * y + u ^ 2).card := by
    refine card_le_card_of_injOn (fun p ↦ ⟨(p.1 + (Q - p.2)) % Q, p.2⟩) (fun p hp ↦ ?_)
      fun p hp p' hp' h ↦ ?_
    · simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
      simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio, coe_filter, mem_range,
        Set.mem_ofPred_eq]
      refine ⟨Nat.mod_lt _ hQ, hp.1.2, ?_⟩
      set u := (p.1 + (Q - p.2)) % Q
      have hx : p.1 ≡ p.2 + u [MOD Q] := by
        simp only [u, Nat.ModEq]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← add_assoc, add_comm p.2,
          add_assoc, Nat.add_sub_cancel' hp.1.2.le, Nat.add_mod_right]
      have := (hx.pow 2).symm.trans hp.2
      rw [show (p.2 + u) ^ 2 = 2 * u * p.2 + u ^ 2 + p.2 ^ 2 by ring] at this
      exact (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_right_cancel' (p.2 ^ 2)
        (by simpa using this))
    · simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp hp'
      simp only [Sigma.mk.injEq, heq_eq_eq] at h
      obtain ⟨hu, hy⟩ := h
      have e1 : p.1 % Q = p'.1 % Q := by
        have := congrArg (· + p.2) hu
        have k1 : ((p.1 + (Q - p.2)) % Q + p.2) % Q = p.1 % Q := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc, Nat.sub_add_cancel hp.1.2.le,
            Nat.add_mod_right]
        have k2 : ((p'.1 + (Q - p'.2)) % Q + p'.2) % Q = p'.1 % Q := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc, Nat.sub_add_cancel hp'.1.2.le,
            Nat.add_mod_right]
        rw [← k1, ← k2, this, hy]
      rw [Nat.mod_eq_of_lt hp.1.1, Nat.mod_eq_of_lt hp'.1.1] at e1
      exact Prod.ext e1 hy
  refine h1.trans ?_
  rw [card_sigma]
  -- `Σ_u gcd(Q, 2u) ≤ 2 Σ_u gcd(Q, u) ≤ 2 Q τ(Q)`
  have h2 : ∀ u, Nat.gcd Q (2 * u) ≤ 2 * Nat.gcd Q u := fun u ↦ by
    refine Nat.le_of_dvd (by positivity) ?_
    rw [← Nat.gcd_mul_left]
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (dvd_mul_left _ _)) (Nat.gcd_dvd_right _ _)
  have h3 : ∀ u, Nat.gcd Q u ≤ ∑ d ∈ Q.divisors.filter (· ∣ u), d := fun u ↦
    single_le_sum (f := id) (fun _ _ ↦ Nat.zero_le _)
      (mem_filter.2 ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hQ.ne'⟩, Nat.gcd_dvd_right _ _⟩)
  have h4 : ∀ d ∈ Q.divisors, ((range Q).filter (d ∣ ·)).card * d ≤ Q := fun d hd ↦ by
    have hdQ := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have : ((range Q).filter (d ∣ ·)).card ≤ Q / d := by
      calc _ ≤ (range (Q / d)).card := by
            refine card_le_card_of_injOn (· / d) (fun u hu ↦ ?_) fun u hu u' hu' h ↦ ?_
            · simp only [coe_filter, mem_range, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hu ⊢
              exact Nat.div_lt_div_of_lt_of_dvd hdQ hu.1
            · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hu hu'
              simp only at h
              rw [← Nat.div_mul_cancel hu.2, ← Nat.div_mul_cancel hu'.2, h]
        _ = _ := card_range _
    calc _ ≤ Q / d * d := Nat.mul_le_mul_right _ this
      _ = Q := Nat.div_mul_cancel hdQ
  calc ∑ u ∈ range Q, ((range Q).filter fun y ↦ Q ∣ 2 * u * y + u ^ 2).card
      ≤ ∑ u ∈ range Q, 2 * ∑ d ∈ Q.divisors.filter (· ∣ u), d :=
        sum_le_sum fun u _ ↦ (card_filter_dvd_mul_add_le hQ _ _).trans ((h2 u).trans
          (Nat.mul_le_mul_left _ (h3 u)))
    _ = 2 * ∑ d ∈ Q.divisors, ((range Q).filter (d ∣ ·)).card * d := by
        rw [← mul_sum, sum_comm' (t' := Q.divisors) (s' := fun d ↦ (range Q).filter (d ∣ ·))]
        · simp [sum_const, smul_eq_mul]
        · intro u d; simp only [mem_filter, Nat.mem_divisors, mem_range]; tauto
    _ ≤ 2 * ∑ _d ∈ Q.divisors, Q := Nat.mul_le_mul_left _ (sum_le_sum h4)
    _ = 2 * Q * Q.divisors.card := by rw [sum_const, smul_eq_mul]; ring

/-- Solutions of `x ^ 2 ≡ y ^ 2 [MOD Q]` below `M` come from solutions modulo `Q`. -/
theorem card_filter_sq_modEq_range_le {Q : ℕ} (hQ : 0 < Q) (M : ℕ) :
    ((range M ×ˢ range M).filter fun p : ℕ × ℕ ↦ p.1 ^ 2 ≡ p.2 ^ 2 [MOD Q]).card ≤
      (M / Q + 1) ^ 2 *
        ((range Q ×ˢ range Q).filter fun p : ℕ × ℕ ↦ p.1 ^ 2 ≡ p.2 ^ 2 [MOD Q]).card := by
  calc _ ≤ ((range (M / Q + 1) ×ˢ range (M / Q + 1)) ×ˢ
        ((range Q ×ˢ range Q).filter fun p : ℕ × ℕ ↦ p.1 ^ 2 ≡ p.2 ^ 2 [MOD Q])).card := by
        refine card_le_card_of_injOn (fun p ↦ ((p.1 / Q, p.2 / Q), (p.1 % Q, p.2 % Q)))
          (fun p hp ↦ ?_) fun p _ p' _ h ↦ ?_
        · simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
          simp only [coe_product, coe_range, coe_filter, mem_product, mem_range, Set.mem_prod,
            Set.mem_Iio, Set.mem_ofPred_eq]
          refine ⟨⟨Nat.lt_succ_of_le (Nat.div_le_div_right hp.1.1.le),
            Nat.lt_succ_of_le (Nat.div_le_div_right hp.1.2.le)⟩,
            ⟨Nat.mod_lt _ hQ, Nat.mod_lt _ hQ⟩, ?_⟩
          exact ((Nat.mod_modEq _ _).pow 2).trans (hp.2.trans ((Nat.mod_modEq _ _).pow 2).symm)
        · simp only [Prod.mk.injEq] at h
          exact Prod.ext (by rw [← Nat.div_add_mod p.1 Q, ← Nat.div_add_mod p'.1 Q, h.1.1, h.2.1])
            (by rw [← Nat.div_add_mod p.2 Q, ← Nat.div_add_mod p'.2 Q, h.1.2, h.2.2])
    _ = _ := by rw [card_product, card_product, card_range, sq]

/-- **Cauchy–Schwarz**: few `n < M` have `n ^ 2 mod Q` in a small set `B`. -/
theorem card_filter_sq_mod_mem_sq_le (Q M : ℕ) (B : Finset ℕ) :
    ((range M).filter fun n ↦ n ^ 2 % Q ∈ B).card ^ 2 ≤ B.card *
      ((range M ×ˢ range M).filter fun p : ℕ × ℕ ↦ p.1 ^ 2 ≡ p.2 ^ 2 [MOD Q]).card := by
  set c : ℕ → ℕ := fun r ↦ ((range M).filter fun n ↦ n ^ 2 % Q = r).card
  have h1 : ((range M).filter fun n ↦ n ^ 2 % Q ∈ B).card = ∑ r ∈ B, c r := by
    rw [card_eq_sum_card_fiberwise (f := fun n ↦ n ^ 2 % Q) (t := B)
      (s := (range M).filter fun n ↦ n ^ 2 % Q ∈ B) fun n hn ↦ (mem_filter.1 hn).2]
    refine sum_congr rfl fun r hr ↦ congrArg card ?_
    ext n; simp only [mem_filter, mem_range]; constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hr⟩, h2⟩
  set P := (range M ×ˢ range M).filter fun p : ℕ × ℕ ↦ p.1 ^ 2 ≡ p.2 ^ 2 [MOD Q]
  set P' := P.filter fun p ↦ p.1 ^ 2 % Q ∈ B
  have h2 : ∑ r ∈ B, c r ^ 2 ≤ P.card := by
    calc ∑ r ∈ B, c r ^ 2 ≤ ∑ r ∈ B, (P'.filter fun p ↦ p.1 ^ 2 % Q = r).card := by
          refine sum_le_sum fun r hr ↦ ?_
          rw [sq, ← card_product]
          refine card_le_card fun p hp ↦ ?_
          simp only [mem_product, mem_filter, mem_range] at hp
          have hPp : p ∈ P := mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 hp.1.1, mem_range.2 hp.2.1⟩,
            show p.1 ^ 2 % Q = p.2 ^ 2 % Q from hp.1.2.trans hp.2.2.symm⟩
          have hP'p : p ∈ P' := mem_filter.2 ⟨hPp, hp.1.2 ▸ hr⟩
          exact mem_filter.2 ⟨hP'p, hp.1.2⟩
      _ = P'.card := by
          have hmaps : ∀ p ∈ P', p.1 ^ 2 % Q ∈ B := fun p hp ↦ (mem_filter.1 hp).2
          exact (card_eq_sum_card_fiberwise hmaps).symm
      _ ≤ P.card := card_filter_le _ _
  rw [h1]
  exact (sq_sum_le_card_mul_sum_sq).trans (Nat.mul_le_mul_left _ h2)

/-- The top halves `⌊n ^ 2 / Q⌋`, `n ≥ m`, of squares take each value at most
`2 ⌊Q / 2m⌋ + 1` times. -/
theorem card_filter_sq_div_mem_le {Q m : ℕ} (hQ : 0 < Q) (hm : 0 < m) (M : ℕ) (V : Finset ℕ) :
    ((Ico m M).filter fun n ↦ n ^ 2 / Q ∈ V).card ≤ (2 * (Q / (2 * m)) + 1) * V.card := by
  classical
  refine card_le_mul_card_image_of_maps_to (fun n hn ↦ (mem_filter.1 hn).2) _ fun v _ ↦ ?_
  set F := ((Ico m M).filter fun n ↦ n ^ 2 / Q ∈ V).filter fun n ↦ n ^ 2 / Q = v
  rcases F.eq_empty_or_nonempty with h | ⟨n₁, hn₁⟩
  · rw [h]; exact Nat.zero_le _
  have key : ∀ n ∈ F, ∀ n' ∈ F, n ≤ n' → n' - n ≤ Q / (2 * m) := by
    intro n hn n' hn' hle
    simp only [F, mem_filter, mem_Ico] at hn hn'
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have h1 : n' ^ 2 < (v + 1) * Q := by
      rw [← hn'.2]; exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hQ
    have h2 : v * Q ≤ n ^ 2 := by rw [← hn.2]; exact Nat.div_mul_le_self _ _
    have h3 : (n' - n) * (2 * m) ≤ n' ^ 2 - n ^ 2 := by
      have : n' ^ 2 - n ^ 2 = (n' - n) * (n' + n) := by
        rw [sq, sq, Nat.mul_self_sub_mul_self_eq, mul_comm]
      rw [this]; exact Nat.mul_le_mul_left _ (by omega)
    have : n' ^ 2 - n ^ 2 < Q := by
      have := Nat.pow_le_pow_left hle 2
      rw [add_mul, one_mul] at h1; omega
    omega
  have hsub : F ⊆ Icc (n₁ - Q / (2 * m)) (n₁ + Q / (2 * m)) := fun n hn ↦ by
    rw [mem_Icc]
    rcases le_total n n₁ with h | h
    · have := key n hn n₁ hn₁ h; omega
    · have := key n₁ hn₁ n hn h; omega
  refine (card_le_card hsub).trans ?_
  rw [Nat.card_Icc]
  omega

/-- If both halves of `x * b ^ ℓ + y` have block frequencies within `ε` then so does the whole. -/
theorem dev_or_dev_of_dev (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b) {ℓ m₁ x y : ℕ}
    (hy : y < b ^ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m₁) {ε : ℝ}
    (hlen : 2 * k ≤ ε * (m₁ + ℓ + 1 - k : ℕ))
    (h : 2 * ε * (m₁ + ℓ + 1 - k : ℕ) ≤ |(natBlockCount b (m₁ + ℓ) (x * b ^ ℓ + y) w : ℝ) -
      (m₁ + ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|) :
    ε * (m₁ + 1 - k : ℕ) ≤ |(natBlockCount b m₁ x w : ℝ) - (m₁ + 1 - k : ℕ) / (b : ℝ) ^ k| ∨
    ε * (ℓ + 1 - k : ℕ) ≤ |(natBlockCount b ℓ y w : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k| := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨s1, s2⟩ := natBlockCount_mul_pow_add hb w hy hk hkℓ m₁ x
  have hbk : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hb)
  set c := ((b : ℝ) ^ k)⁻¹
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ hbk
  have e : ((m₁ + ℓ + 1 - k : ℕ) : ℝ) = (m₁ + 1 - k : ℕ) + (ℓ + 1 - k : ℕ) + (k - 1 : ℕ) := by
    norm_cast; omega
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have r1 : (((m₁ + 1 - k : ℕ) : ℝ) + (ℓ + 1 - k : ℕ)) ≤ (m₁ + ℓ + 1 - k : ℕ) := by
    rw [e]; linarith [(Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ _)]
  have s1' : ((natBlockCount b m₁ x w : ℝ) + natBlockCount b ℓ y w) ≤
      natBlockCount b (m₁ + ℓ) (x * b ^ ℓ + y) w := by exact_mod_cast s1
  have s2' : (natBlockCount b (m₁ + ℓ) (x * b ^ ℓ + y) w : ℝ) ≤
      natBlockCount b m₁ x w + natBlockCount b ℓ y w + k := by exact_mod_cast s2
  simp only [div_eq_mul_inv] at h h1 h2
  rw [abs_lt] at h1 h2
  have hε : 0 ≤ ε := by
    by_contra hn; push Not at hn
    have : (0 : ℝ) ≤ |(natBlockCount b m₁ x w : ℝ) - (m₁ + 1 - k : ℕ) * c| := abs_nonneg _
    nlinarith [(Nat.cast_nonneg (m₁ + 1 - k) : (0 : ℝ) ≤ _), h1.1, h1.2]
  have hkc : ((k - 1 : ℕ) : ℝ) * c ≤ k := by nlinarith [(Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ _)]
  have hkc0 : 0 ≤ ((k - 1 : ℕ) : ℝ) * c := by positivity
  have : |(natBlockCount b (m₁ + ℓ) (x * b ^ ℓ + y) w : ℝ) - (m₁ + ℓ + 1 - k : ℕ) * c| <
      ε * (m₁ + ℓ + 1 - k : ℕ) + 2 * k := by
    rw [abs_lt, e]
    constructor <;> nlinarith
  linarith

/-- The numbers `v < b ^ (ℓ + 2)` in whose expansion the frequency of `w` is off by `ε`. -/
noncomputable def sqTopBad (b : ℕ) (w : Fin k → Fin b) (ε : ℝ) (ℓ : ℕ) : Finset ℕ :=
  (range (b ^ (ℓ + 2))).filter fun v ↦ ε * (Nat.log b v + 1 + 1 - k : ℕ) ≤
    |(natBlockCount b (Nat.log b v + 1) v w : ℝ) - (Nat.log b v + 1 + 1 - k : ℕ) / (b : ℝ) ^ k|

/-- The `ℓ`-digit strings in which the frequency of `w` is off by `ε`. -/
noncomputable def sqBotBad (b : ℕ) (w : Fin k → Fin b) (ε : ℝ) (ℓ : ℕ) : Finset ℕ :=
  (range (b ^ ℓ)).filter fun r ↦ ε * (ℓ + 1 - k : ℕ) ≤
    |(natBlockCount b ℓ r w : ℝ) - (ℓ + 1 - k : ℕ) / (b : ℝ) ^ k|

/-- **Bisection**: a square `n ^ 2`, `n ≥ m`, with a bad block frequency has a bad top half
`n ^ 2 / b ^ ℓ` or a bad bottom half `n ^ 2 % b ^ ℓ`. -/
theorem card_concatBad_sq_le (hb : 2 ≤ b) (hk : 0 < k) (w : Fin k → Fin b) {ε : ℝ} {T m : ℕ}
    (hm : 0 < m) (hkℓ : k ≤ Nat.log b (T + 2)) (hm2 : b ^ (Nat.log b (T + 2) + k) ≤ m ^ 2)
    (hlen : 2 * k ≤ ε / 2 * (Nat.log b (T + 2) + 1 - k : ℕ)) :
    (concatBad b (fun n ↦ (n + 1) ^ 2) w ε T).card ≤ m +
      (2 * (b ^ Nat.log b (T + 2) / (2 * m)) + 1) *
        (sqTopBad b w (ε / 2) (Nat.log b (T + 2))).card +
      ((range (T + 2)).filter fun n ↦
        n ^ 2 % b ^ Nat.log b (T + 2) ∈ sqBotBad b w (ε / 2) (Nat.log b (T + 2))).card := by
  classical
  set ℓ := Nat.log b (T + 2)
  set Q := b ^ ℓ
  have hb0 : 0 < b := by omega
  have hb1 : 1 < b := by omega
  have hQ : 0 < Q := pow_pos hb0 ℓ
  set Top := (Ico m (T + 2)).filter fun n ↦ n ^ 2 / Q ∈ sqTopBad b w (ε / 2) ℓ
  set Bot := (range (T + 2)).filter fun n ↦ n ^ 2 % Q ∈ sqBotBad b w (ε / 2) ℓ
  have hsub : (concatBad b (fun n ↦ (n + 1) ^ 2) w ε T).image (· + 1) ⊆ range m ∪ Top ∪ Bot := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hn
    simp only [concatBad, mem_filter, mem_range] at ht
    obtain ⟨htT, hbad⟩ := ht
    simp only [mem_union, mem_range]
    by_cases hnm : t + 1 < m
    · exact Or.inl (Or.inl hnm)
    push Not at hnm
    set v := (t + 1) ^ 2 / Q
    set r := (t + 1) ^ 2 % Q
    have hr : r < Q := Nat.mod_lt _ hQ
    have hvr : v * Q + r = (t + 1) ^ 2 := Nat.div_add_mod' _ _
    have hnT : t + 1 < b ^ (ℓ + 1) := (show t + 1 < T + 2 by omega).trans
      (Nat.lt_pow_succ_log_self hb1 _)
    have hv : v < b ^ (ℓ + 2) := by
      refine (Nat.div_lt_iff_lt_mul hQ).2 ?_
      calc (t + 1) ^ 2 < (b ^ (ℓ + 1)) ^ 2 := Nat.pow_lt_pow_left hnT two_ne_zero
        _ = b ^ (ℓ + 2) * Q := by rw [← pow_mul, ← pow_add]; congr 1; omega
    have hvk : b ^ k ≤ v := by
      refine (Nat.le_div_iff_mul_le hQ).2 ?_
      calc b ^ k * Q = b ^ (ℓ + k) := by rw [← pow_add, add_comm]
        _ ≤ m ^ 2 := hm2
        _ ≤ (t + 1) ^ 2 := Nat.pow_le_pow_left hnm 2
    have hlogv : k ≤ Nat.log b v := Nat.le_log_of_pow_le hb1 hvk
    have hv0 : v ≠ 0 := by have := Nat.one_le_pow k b hb0; omega
    have hlog : Nat.log b ((t + 1) ^ 2) = Nat.log b v + ℓ := by
      rw [← hvr]
      refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
      · calc b ^ (Nat.log b v + ℓ) = b ^ Nat.log b v * Q := pow_add _ _ _
          _ ≤ v * Q := Nat.mul_le_mul_right _ (Nat.pow_log_le_self b hv0)
          _ ≤ v * Q + r := Nat.le_add_right _ _
      · calc v * Q + r < (v + 1) * Q := by rw [add_mul, one_mul]; omega
          _ ≤ b ^ (Nat.log b v + 1) * Q :=
            Nat.mul_le_mul_right _ (Nat.lt_pow_succ_log_self hb1 v)
          _ = b ^ (Nat.log b v + ℓ + 1) := by rw [← pow_add]; congr 1; omega
    rw [hlog, show Nat.log b v + ℓ + 1 = (Nat.log b v + 1) + ℓ by omega, ← hvr] at hbad
    have hlen' : 2 * k ≤ ε / 2 * (Nat.log b v + 1 + ℓ + 1 - k : ℕ) := by
      refine hlen.trans ?_
      have hε : 0 ≤ ε := by
        by_contra hn; push Not at hn
        have : (0 : ℝ) < 2 * k := by positivity
        have : ε / 2 * ((ℓ + 1 - k : ℕ) : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
        linarith
      gcongr; omega
    rcases dev_or_dev_of_dev hb0 hk w hr hkℓ (by omega) hlen'
      (by rw [show 2 * (ε / 2) = ε by ring]; exact hbad) with h | h
    · refine Or.inl (Or.inr (mem_filter.2 ⟨mem_Ico.2 ⟨hnm, by omega⟩, ?_⟩))
      exact mem_filter.2 ⟨mem_range.2 hv, h⟩
    · exact Or.inr (mem_filter.2 ⟨mem_range.2 (by omega), mem_filter.2 ⟨mem_range.2 hr, h⟩⟩)
  rw [← card_image_of_injective _ (add_left_injective 1)]
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right
    ((card_union_le _ _).trans (add_le_add (card_range m).le
      (card_filter_sq_div_mem_le hQ hm _ _))) _))


/-- Polynomial growth loses to geometric decay. -/
theorem tendsto_add_three_pow_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (j : ℕ) :
    Tendsto (fun ℓ : ℕ ↦ ((ℓ : ℝ) + 3) ^ j * r ^ ℓ) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one j (r := r)
    (by rw [abs_of_nonneg hr0]; exact hr)).const_mul (4 ^ j)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun ℓ ↦ by positivity) ?_ h
  filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rw [← mul_assoc, ← mul_pow]
  gcongr
  linarith

/-- Few squares have a bad block frequency. -/
theorem tendsto_concatBad_sq (hb : 2 ≤ b) (hk : 0 < k) (w : Fin k → Fin b) {ε : ℝ}
    (hε : 0 < ε) : Tendsto (fun T ↦ ((Nat.log b ((T + 1) ^ 2) : ℝ) + 1) *
      (concatBad b (fun n ↦ (n + 1) ^ 2) w ε T).card /
        concatStart b (fun n ↦ (n + 1) ^ 2) (T + 1)) atTop (𝓝 0) := by
  have hb0 : 0 < b := by omega
  have hb1 : 1 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb1
  obtain ⟨C, ρ, hC, hρ0, hρ, hbad⟩ := exists_card_filter_le_exp hb1 hk w (ε := ε / 2)
    (by positivity)
  set β := exp ρ
  have hβ1 : 1 ≤ β := one_le_exp hρ0
  have hβb : β < b := by
    rw [← exp_log (show (0 : ℝ) < b by positivity)]; exact exp_lt_exp.2 hρ
  have hsb : √(b : ℝ) < b := by
    rw [sqrt_lt' (by positivity)]; nlinarith
  set β' := (max β √(b : ℝ) + b) / 2
  have hβ'b : β' < b := by have := max_lt hβb hsb; simp only [β']; linarith
  have hββ' : β < β' := by have := le_max_left β √(b : ℝ); simp only [β']; linarith
  have hsβ' : √(b : ℝ) < β' := by have := le_max_right β √(b : ℝ); simp only [β']; linarith
  have hβ'0 : 0 < β' := by linarith
  have hbβ' : (b : ℝ) < β' ^ 2 := by
    have := sq_sqrt (show (0 : ℝ) ≤ b by positivity)
    nlinarith [sqrt_nonneg (b : ℝ)]
  set ω := b.primeFactors.card
  set τb : ℝ := (b.divisors.card : ℝ)
  set G : ℕ → ℝ := fun ℓ ↦
    4 * (((ℓ : ℝ) + 3) ^ 1 * (β' / b) ^ ℓ + ((ℓ : ℝ) + 3) ^ 1 * (1 / b) ^ ℓ) +
    4 * C * β ^ 2 * (((ℓ : ℝ) + 3) ^ 2 * (β / β') ^ ℓ + ((ℓ : ℝ) + 3) ^ 2 * (β / b) ^ ℓ) +
    √(32 * C * b ^ 2 * τb * (((ℓ : ℝ) + 3) ^ (ω + 2) * (β / b) ^ ℓ))
  have hG : Tendsto G atTop (𝓝 0) := by
    have t1 := tendsto_add_three_pow_mul_pow (r := β' / b) (by positivity)
      ((div_lt_one (by positivity)).2 hβ'b) 1
    have t2 := tendsto_add_three_pow_mul_pow (r := 1 / b) (by positivity)
      ((div_lt_one (by positivity)).2 hbR) 1
    have t3 := tendsto_add_three_pow_mul_pow (r := β / β') (by positivity)
      ((div_lt_one hβ'0).2 hββ') 2
    have t4 := tendsto_add_three_pow_mul_pow (r := β / b) (by positivity)
      ((div_lt_one (by positivity)).2 hβb) 2
    have t5 := tendsto_add_three_pow_mul_pow (r := β / b) (by positivity)
      ((div_lt_one (by positivity)).2 hβb) (ω + 2)
    have t6 := t5.const_mul (32 * C * b ^ 2 * τb)
    rw [mul_zero] at t6
    have := (((t1.add t2).const_mul 4).add ((t3.add t4).const_mul (4 * C * β ^ 2))).add
      ((continuous_sqrt.tendsto 0).comp t6)
    simpa [G] using this
  -- conditions on `ℓ`
  have hE : ∀ᶠ ℓ : ℕ in atTop, k ≤ ℓ ∧ 1 ≤ ℓ ∧ (b : ℝ) ^ k * (b : ℝ) ^ ℓ ≤ β' ^ (2 * ℓ) ∧
      (2 * k : ℝ) ≤ ε / 2 * ((ℓ + 1 - k : ℕ) : ℝ) := by
    have hpow := tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ) < β' ^ 2 / b by rw [one_lt_div (by positivity)]; exact hbβ')
    filter_upwards [eventually_ge_atTop (k + ⌈4 * k / ε⌉₊), eventually_ge_atTop 1,
      hpow.eventually (eventually_ge_atTop ((b : ℝ) ^ k))] with ℓ h1 h2 h3
    refine ⟨by omega, h2, ?_, ?_⟩
    · rw [pow_mul, show (β' ^ 2) ^ ℓ = (β' ^ 2 / b) ^ ℓ * (b : ℝ) ^ ℓ by
        rw [← mul_pow, div_mul_cancel₀ _ (by positivity)]]
      gcongr
    · have : (4 * k / ε : ℝ) ≤ ((ℓ + 1 - k : ℕ) : ℝ) := by
        refine (Nat.le_ceil _).trans ?_
        exact_mod_cast (show ⌈4 * k / ε⌉₊ ≤ ℓ + 1 - k by omega)
      rw [div_le_iff₀ hε] at this
      linarith
  have hℓT : Tendsto (fun T : ℕ ↦ Nat.log b (T + 2)) atTop atTop :=
    tendsto_atTop_atTop.2 fun L ↦ ⟨b ^ L, fun T hT ↦ Nat.le_log_of_pow_le hb1 (by omega)⟩
  refine squeeze_zero' (Eventually.of_forall fun T ↦ by positivity) ?_ (hG.comp hℓT)
  filter_upwards [hℓT.eventually hE] with T ⟨h1, h2, h3, h4⟩
  simp only [Function.comp_apply]
  set ℓ := Nat.log b (T + 2)
  set Q := b ^ ℓ
  set q : ℝ := (b : ℝ) ^ ℓ
  have hqQ : (Q : ℝ) = q := by simp [Q, q]
  have hq0 : 0 < q := by positivity
  set m := ⌈β' ^ ℓ⌉₊
  have hP0 : 0 < β' ^ ℓ := by positivity
  have hm0 : 0 < m := Nat.ceil_pos.2 hP0
  have hmR : β' ^ ℓ ≤ m := Nat.le_ceil _
  have hmR' : (m : ℝ) < β' ^ ℓ + 1 := Nat.ceil_lt_add_one hP0.le
  have hm2 : b ^ (ℓ + k) ≤ m ^ 2 := by
    have : ((b ^ (ℓ + k) : ℕ) : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by
      push_cast
      calc (b : ℝ) ^ (ℓ + k) = (b : ℝ) ^ k * (b : ℝ) ^ ℓ := by rw [pow_add, mul_comm]
        _ ≤ β' ^ (2 * ℓ) := h3
        _ = (β' ^ ℓ) ^ 2 := by rw [← pow_mul, mul_comm]
        _ ≤ (m : ℝ) ^ 2 := by gcongr
    exact_mod_cast this
  have hcard := card_concatBad_sq_le hb hk w hm0 h1 hm2 h4
  set A := (sqTopBad b w (ε / 2) ℓ).card
  set Bb := (sqBotBad b w (ε / 2) ℓ).card
  set Bc := ((range (T + 2)).filter fun n ↦ n ^ 2 % Q ∈ sqBotBad b w (ε / 2) ℓ).card
  -- the bad top halves
  have hA : (A : ℝ) ≤ ((ℓ : ℝ) + 3) * (C * (β ^ ℓ * β ^ 2)) := by
    have hinj : (A : ℝ) ≤ ∑ j ∈ range (ℓ + 3),
        (((range (b ^ j)).filter fun v ↦ ε / 2 * (j + 1 - k : ℕ) ≤
          |(natBlockCount b j v w : ℝ) - (j + 1 - k : ℕ) / (b : ℝ) ^ k|).card : ℝ) := by
      rw [← Nat.cast_sum, ← card_sigma]
      refine Nat.cast_le.2 (card_le_card_of_injOn (fun v ↦ ⟨Nat.log b v + 1, v⟩) ?_ ?_)
      · intro v hv
        simp only [sqTopBad, coe_filter, mem_range, Set.mem_ofPred_eq] at hv
        simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio, coe_filter, mem_range,
          Set.mem_ofPred_eq]
        refine ⟨?_, Nat.lt_pow_succ_log_self hb1 _, hv.2⟩
        have : Nat.log b v < ℓ + 2 := Nat.log_lt_of_lt_pow' (by omega) hv.1
        omega
      · intro v _ v' _ e
        simp only [Sigma.mk.injEq] at e
        exact eq_of_heq e.2
    refine hinj.trans ((sum_le_sum fun j _ ↦ hbad j).trans ?_)
    calc ∑ j ∈ range (ℓ + 3), C * exp (ρ * j)
        ≤ ∑ _j ∈ range (ℓ + 3), C * exp (ρ * (ℓ + 2 : ℕ)) := by
          refine sum_le_sum fun j hj ↦ ?_
          have : (j : ℝ) ≤ (ℓ + 2 : ℕ) := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hj)
          gcongr
      _ = ((ℓ : ℝ) + 3) * (C * (β ^ ℓ * β ^ 2)) := by
          rw [sum_const, card_range, nsmul_eq_mul, mul_comm ρ, exp_natCast_mul, ← pow_add]
          push_cast; ring
  have hBb : (Bb : ℝ) ≤ C * β ^ ℓ := by
    have := hbad ℓ
    rwa [mul_comm ρ, exp_natCast_mul] at this
  -- the bad bottom halves
  have hBc : (Bc : ℝ) ^ 2 ≤ Bb * ((b : ℝ) ^ 2 * (2 * q * (((ℓ : ℝ) + 1) ^ ω * τb))) := by
    have hQ0 : 0 < Q := pow_pos hb0 ℓ
    have hMQ : (T + 2) / Q + 1 ≤ b := by
      have : T + 2 < Q * b := by
        rw [← pow_succ]; exact Nat.lt_pow_succ_log_self hb1 _
      have := (Nat.div_lt_iff_lt_mul hQ0).2 (by rw [mul_comm]; exact this)
      omega
    have hN : Bc ^ 2 ≤ Bb * (b ^ 2 * (2 * Q * ((ℓ + 1) ^ ω * b.divisors.card))) := by
      refine (card_filter_sq_mod_mem_sq_le Q (T + 2) _).trans (Nat.mul_le_mul_left _ ?_)
      refine (card_filter_sq_modEq_range_le hQ0 _).trans (Nat.mul_le_mul
        (Nat.pow_le_pow_left hMQ 2) ((card_filter_sq_modEq_le hQ0).trans ?_))
      exact Nat.mul_le_mul_left _ (Nat.card_divisors_pow_le hb0 ℓ)
    have : ((Bc ^ 2 : ℕ) : ℝ) ≤
        ((Bb * (b ^ 2 * (2 * Q * ((ℓ + 1) ^ ω * b.divisors.card))) : ℕ) : ℝ) := by
      exact_mod_cast hN
    push_cast at this
    rw [hqQ] at this
    exact this
  -- the length of the sequence
  have hqT : q ≤ T + 2 := by
    have := Nat.pow_log_le_self b (show T + 2 ≠ 0 by omega)
    simp only [q]; exact_mod_cast this
  have hq2 : 2 ≤ q := by
    have : (b : ℝ) ^ 1 ≤ q := pow_le_pow_right₀ hbR.le h2
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith [pow_one (b : ℝ)]
  have hS : q / 2 ≤ concatStart b (fun n ↦ (n + 1) ^ 2) (T + 1) := by
    have := le_concatStart b (fun n ↦ (n + 1) ^ 2) (T + 1)
    have : ((T + 1 : ℕ) : ℝ) ≤ concatStart b (fun n ↦ (n + 1) ^ 2) (T + 1) := by exact_mod_cast this
    push_cast at this
    linarith
  have hlog : (Nat.log b ((T + 1) ^ 2) : ℝ) + 1 ≤ 2 * ((ℓ : ℝ) + 3) := by
    have : Nat.log b ((T + 1) ^ 2) < 2 * ℓ + 2 := by
      refine Nat.log_lt_of_lt_pow' (by omega) ?_
      calc (T + 1) ^ 2 < (b ^ (ℓ + 1)) ^ 2 :=
            Nat.pow_lt_pow_left ((Nat.lt_succ_self _).trans (Nat.lt_pow_succ_log_self hb1 _))
              two_ne_zero
        _ = b ^ (2 * ℓ + 2) := by rw [← pow_mul]; ring_nf
    have : (Nat.log b ((T + 1) ^ 2) : ℝ) < 2 * ℓ + 2 := by exact_mod_cast this
    linarith
  -- the number of bad terms
  have hcardR : ((concatBad b (fun n ↦ (n + 1) ^ 2) w ε T).card : ℝ) ≤
      (β' ^ ℓ + 1) + (q / β' ^ ℓ + 1) * A + Bc := by
    have h := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at h
    have hd : (2 * ((Q / (2 * m) : ℕ) : ℝ)) ≤ q / β' ^ ℓ := by
      calc (2 * ((Q / (2 * m) : ℕ) : ℝ)) ≤ 2 * ((Q : ℝ) / ((2 * m : ℕ) : ℝ)) := by
            gcongr; exact Nat.cast_div_le
        _ = q / m := by rw [hqQ]; push_cast; field_simp
        _ ≤ q / β' ^ ℓ := div_le_div_of_nonneg_left hq0.le hP0 hmR
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    nlinarith
  set L : ℝ := (ℓ : ℝ) + 3
  have hL : 1 ≤ L := by simp only [L]; linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have hX : ((Nat.log b ((T + 1) ^ 2) : ℝ) + 1) * (concatBad b (fun n ↦ (n + 1) ^ 2) w ε T).card /
      concatStart b (fun n ↦ (n + 1) ^ 2) (T + 1) ≤
        4 * L * ((β' ^ ℓ + 1) + (q / β' ^ ℓ + 1) * A + Bc) / q := by
    rw [div_le_div_iff₀ (by linarith) hq0]
    have hc0 : (0 : ℝ) ≤ (concatBad b (fun n ↦ (n + 1) ^ 2) w ε T).card := Nat.cast_nonneg _
    have hl0 : (0 : ℝ) ≤ (Nat.log b ((T + 1) ^ 2) : ℝ) + 1 := by positivity
    calc ((Nat.log b ((T + 1) ^ 2) : ℝ) + 1) * (concatBad b (fun n ↦ (n + 1) ^ 2) w ε T).card * q
        ≤ (2 * L) * ((β' ^ ℓ + 1) + (q / β' ^ ℓ + 1) * A + Bc) * q := by gcongr
      _ = 4 * L * ((β' ^ ℓ + 1) + (q / β' ^ ℓ + 1) * A + Bc) * (q / 2) := by ring
      _ ≤ _ := by gcongr
  refine hX.trans ?_
  have e1 : (β' / b) ^ ℓ = β' ^ ℓ / q := div_pow _ _ _
  have e2 : (1 / (b : ℝ)) ^ ℓ = 1 / q := by rw [div_pow, one_pow]
  have e3 : (β / β') ^ ℓ = β ^ ℓ / β' ^ ℓ := div_pow _ _ _
  have e4 : (β / b) ^ ℓ = β ^ ℓ / q := div_pow _ _ _
  have hBℓ : 0 < β ^ ℓ := by positivity
  have hBc0 : (0 : ℝ) ≤ Bc := Nat.cast_nonneg _
  -- the three terms
  have t1 : 4 * L * (β' ^ ℓ + 1) / q = 4 * (L ^ 1 * (β' / b) ^ ℓ + L ^ 1 * (1 / b) ^ ℓ) := by
    rw [e1, e2]; field_simp
  have t2 : 4 * L * ((q / β' ^ ℓ + 1) * A) / q ≤
      4 * C * β ^ 2 * (L ^ 2 * (β / β') ^ ℓ + L ^ 2 * (β / b) ^ ℓ) := by
    rw [e3, e4, div_le_iff₀ hq0]
    have : 4 * L * ((q / β' ^ ℓ + 1) * A) ≤
        4 * L * ((q / β' ^ ℓ + 1) * (L * (C * (β ^ ℓ * β ^ 2)))) := by
      gcongr
    refine this.trans (le_of_eq ?_)
    field_simp
  have t3 : 4 * L * Bc / q ≤ √(32 * C * b ^ 2 * τb * (L ^ (ω + 2) * (β / b) ^ ℓ)) := by
    refine le_sqrt_of_sq_le ?_
    have hω : ((ℓ : ℝ) + 1) ^ ω ≤ L ^ ω := by gcongr; simp only [L]; linarith
    have hτ : 0 ≤ τb := Nat.cast_nonneg _
    rw [e4, div_pow, div_le_iff₀ (by positivity)]
    calc (4 * L * Bc) ^ 2 = 16 * L ^ 2 * Bc ^ 2 := by ring
      _ ≤ 16 * L ^ 2 * (Bb * ((b : ℝ) ^ 2 * (2 * q * (((ℓ : ℝ) + 1) ^ ω * τb)))) := by gcongr
      _ ≤ 16 * L ^ 2 * ((C * β ^ ℓ) * ((b : ℝ) ^ 2 * (2 * q * (L ^ ω * τb)))) := by
          gcongr
      _ = 32 * C * b ^ 2 * τb * (L ^ (ω + 2) * (β ^ ℓ / q)) * q ^ 2 := by
          rw [pow_add]; field_simp; ring
  calc 4 * L * ((β' ^ ℓ + 1) + (q / β' ^ ℓ + 1) * A + Bc) / q
      = 4 * L * (β' ^ ℓ + 1) / q + 4 * L * ((q / β' ^ ℓ + 1) * A) / q + 4 * L * Bc / q := by ring
    _ ≤ _ := by
      rw [t1]
      simp only [G, L] at t2 t3 ⊢
      linarith

end Squares

section Polynomials

variable {a : ℕ → ℕ}

/-- An upper bound on the occurrences of `w` inside the terms gives the same upper bound on its
frequency in the concatenation, as long as terms are short compared to the total length. -/
theorem eventually_concatOcc_le (hk : 0 < k) (hb : 0 < b) (w : Fin k → Fin b) {c : ℝ}
    (hc : 0 ≤ c) (hT : Tendsto (fun T : ℕ ↦ (T : ℝ) / concatStart b a T) atTop (𝓝 0))
    (hlen : Tendsto (fun T ↦ ((Nat.log b (a T) : ℝ) + 1) / concatStart b a T) atTop (𝓝 0))
    (h : ∀ ε > 0, ∀ᶠ T in atTop, (concatInternal b a w T : ℝ) ≤ (c + ε) * concatStart b a T)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, (concatOcc b a w N : ℝ) ≤ (c + ε) * N := by
  have hε4 : 0 < ε / 4 / (c + ε / 2) := by positivity
  have hk4 : 0 < ε / 4 / (2 * k) := by positivity
  obtain ⟨T1, hT1⟩ := eventually_atTop.1 (h (ε / 2) (by positivity))
  obtain ⟨T2, hT2⟩ := eventually_atTop.1 (hlen.eventually (ge_mem_nhds hε4))
  obtain ⟨T3, hT3⟩ := eventually_atTop.1 (hT.eventually (ge_mem_nhds hk4))
  set T0 := max (max T1 T2) (max T3 1)
  refine eventually_atTop.2 ⟨concatStart b a (T0 + 1), fun N hN ↦ ?_⟩
  obtain ⟨T, hT1', hT2'⟩ := exists_concatStart_le_lt b a N
  have hTT0 : T0 ≤ T := by
    by_contra hlt
    have := concatStart_mono b a (show T + 1 ≤ T0 + 1 by omega)
    omega
  have hS0 : (0 : ℝ) < concatStart b a T := by
    exact_mod_cast (show 0 < T by omega).trans_le (le_concatStart b a T)
  have hSN : (concatStart b a T : ℝ) ≤ N := by exact_mod_cast hT1'
  have hlenT := hT2 T (by omega)
  have hTT := hT3 T (by omega)
  rw [div_le_iff₀ hS0] at hlenT hTT
  have hocc : (concatOcc b a w N : ℝ) ≤ concatInternal b a w (T + 1) + k * ((T : ℝ) + 1) := by
    have h1 := concatOcc_mono (a := a) w hT2'.le
    have h2 := concatOcc_le (a := a) hk hb w (T + 1)
    have h3 : (((k - 1) * (T + 1) : ℕ) : ℝ) ≤ k * ((T : ℝ) + 1) := by
      push_cast; gcongr; exact_mod_cast Nat.sub_le k 1
    have : (concatOcc b a w N : ℝ) ≤ (concatInternal b a w (T + 1) + (k - 1) * (T + 1) : ℕ) := by
      exact_mod_cast h1.trans h2
    push_cast at this h3 ⊢
    linarith
  have hint := hT1 (T + 1) (by omega)
  have hS1 : (concatStart b a (T + 1) : ℝ) = concatStart b a T + ((Nat.log b (a T) : ℝ) + 1) := by
    rw [concatStart_succ]; push_cast; ring
  have hT1r : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hcε : 0 < c + ε / 2 := by positivity
  have hA : (c + ε / 2) * ((Nat.log b (a T) : ℝ) + 1) ≤ ε / 4 * concatStart b a T := by
    have := mul_le_mul_of_nonneg_left hlenT hcε.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hcε.ne'] at this
  have hB : (k : ℝ) * ((T : ℝ) + 1) ≤ ε / 4 * concatStart b a T := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_left hTT (show (0 : ℝ) ≤ 2 * k by positivity)
    rw [← mul_assoc, mul_div_cancel₀ _ (by positivity)] at this
    nlinarith
  calc (concatOcc b a w N : ℝ) ≤ (c + ε / 2) * concatStart b a (T + 1) + k * ((T : ℝ) + 1) := by
        linarith
    _ ≤ (c + ε / 2) * N + ε / 4 * N + ε / 4 * N := by
        rw [hS1, mul_add]
        have : (c + ε / 2) * (concatStart b a T : ℝ) ≤ (c + ε / 2) * N := by gcongr
        nlinarith
    _ = (c + ε) * N := by ring

/-- **Normality of a concatenation from an upper bound**: if every block `w` of length `k`
occurs inside the terms at most `C b⁻ᵏ + o(1)` times per digit, and the terms are short, then
the concatenation is normal (by Piatetski-Shapiro's hot-spot criterion). -/
theorem isNormalIn_concatenation_of_concatInternal_le [NeZero b] (hb : 2 ≤ b) {C : ℝ}
    (hC : 1 ≤ C) (hT : Tendsto (fun T : ℕ ↦ (T : ℝ) / concatStart b a T) atTop (𝓝 0))
    (hlen : Tendsto (fun T ↦ ((Nat.log b (a T) : ℝ) + 1) / concatStart b a T) atTop (𝓝 0))
    (h : ∀ k, 0 < k → ∀ (w : Fin k → Fin b) (ε : ℝ), 0 < ε → ∀ᶠ T in atTop,
      (concatInternal b a w T : ℝ) ≤ (C * ((b : ℝ) ^ k)⁻¹ + ε) * concatStart b a T) :
    IsNormalIn b (concatenation b a) := by
  have hb1 : 1 < b := by omega
  have hocc : ∀ k, 0 < k → ∀ (w : Fin k → Fin b) (ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop,
      (concatOcc b a w N : ℝ) ≤ (C * ((b : ℝ) ^ k)⁻¹ + ε) * N := fun k hk w ε hε ↦
    eventually_concatOcc_le hk (by omega) w (by positivity) hT hlen (h k hk w) hε
  set d : ℕ → Fin b := fun n ↦ Fin.ofNat b (concatDigit b a n)
  have hdv : ∀ n, (d n : ℕ) = concatDigit b a n := fun n ↦ by
    simp only [d, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (concatDigit_lt (b := b) (by omega) a n)
  -- the digit `b - 1` does not repeat forever
  have hd : ∀ n, ∃ m, n < m ∧ (d m : ℕ) + 1 < b := by
    by_contra! hcon
    obtain ⟨n, hn⟩ := hcon
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 * C) (show (1 : ℝ) < b by exact_mod_cast hb1)
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk; linarith
      · exact h
    set w : Fin k → Fin b := fun _ ↦ ⟨b - 1, by omega⟩
    obtain ⟨N, hN, hN'⟩ := ((hocc k hk0 w (1 / 4) (by norm_num)).and
      (eventually_ge_atTop (2 * n + 4))).exists
    have hlow : N - (n + 1) ≤ concatOcc b a w N := by
      rw [concatOcc, ← Nat.card_Ico (n + 1) N]
      refine Finset.card_le_card fun i hi ↦ ?_
      simp only [Finset.mem_Ico] at hi
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hi.2, fun j ↦ ?_⟩
      have := hn (i + j) (by omega)
      have := concatDigit_lt (b := b) (by omega) a (i + j)
      rw [← hdv] at *
      simp only [w]
      omega
    have hCk : C * ((b : ℝ) ^ k)⁻¹ ≤ 1 / 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
    have : ((N - (n + 1) : ℕ) : ℝ) ≤ N / 2 := by
      calc ((N - (n + 1) : ℕ) : ℝ) ≤ concatOcc b a w N := by exact_mod_cast hlow
        _ ≤ (C * ((b : ℝ) ^ k)⁻¹ + 1 / 4) * N := hN
        _ ≤ (1 / 4 + 1 / 4) * N := by gcongr
        _ = N / 2 := by ring
    rw [Nat.cast_sub (by omega)] at this
    have : (2 * n + 4 : ℝ) ≤ N := by exact_mod_cast hN'
    push_cast at *
    linarith
  have hdig : ∀ n, digit b (concatenation b a) n = concatDigit b a n := fun n ↦ by
    rw [concatenation, digit_ofDigits hb1 d hd, hdv]
  have hbc : ∀ {k} (w : Fin k → Fin b) N,
      blockCount b (concatenation b a) w N = concatOcc b a w N := fun w N ↦ by
    simp only [blockCount, concatOcc, hdig]
  refine isNormalIn_of_eventually_le hb (C := C) fun k w ε hε ↦ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have : (blockCount b (concatenation b a) w N : ℝ) ≤ N := by
      unfold blockCount
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range N).le
    rw [div_le_iff₀ hN0, pow_zero, inv_one, mul_one]
    nlinarith
  · filter_upwards [hocc k hk w ε hε, eventually_gt_atTop 0] with N h1 hN
    rw [hbc, div_le_iff₀ (by exact_mod_cast hN)]
    exact h1

/-- If the `k` digits of `m` ending `s` digits from the right encode `c`, then
`m / b ^ (s + k) - c / b ^ k` lies in `[0, 1 / b ^ k)` modulo one. -/
theorem fract_div_pow_sub_lt (hb : 0 < b) {m s c : ℕ} (h : m / b ^ s % b ^ k = c) :
    Int.fract ((m : ℝ) / (b : ℝ) ^ (s + k) - c / (b : ℝ) ^ k) < 1 / ((b ^ k : ℕ) : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  set q := m / b ^ s
  have hm : (m : ℝ) = (b : ℝ) ^ s * q + (m % b ^ s : ℕ) := by
    exact_mod_cast (Nat.div_add_mod m (b ^ s)).symm
  have hq : (q : ℝ) = (b : ℝ) ^ k * (q / b ^ k : ℕ) + c := by
    rw [← h]; exact_mod_cast (Nat.div_add_mod q (b ^ k)).symm
  have hr0 : (0 : ℝ) ≤ (m % b ^ s : ℕ) := Nat.cast_nonneg _
  have hr1 : ((m % b ^ s : ℕ) : ℝ) < (b : ℝ) ^ s := by
    exact_mod_cast Nat.mod_lt _ (pow_pos hb s)
  have heq : (m : ℝ) / (b : ℝ) ^ (s + k) - c / (b : ℝ) ^ k =
      ((q / b ^ k : ℕ) : ℝ) + ((m % b ^ s : ℕ) : ℝ) / (b : ℝ) ^ (s + k) := by
    rw [hm, hq, pow_add]; field_simp; ring
  rw [heq, Int.fract_natCast_add, Int.fract_eq_self.2 ⟨by positivity, ?_⟩]
  · rw [Nat.cast_pow, pow_add, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hb' k]
  · rw [div_lt_one (by positivity), pow_add]
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ b by exact_mod_cast hb) (n := k), pow_pos hb' s]

/-- The internal occurrences of `w` in the first `T` terms, sorted by position. -/
theorem concatInternal_le_sum_card (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b) {T L : ℕ}
    (hL : ∀ t < T, Nat.log b (a t) + 1 ≤ L) :
    concatInternal b a w T ≤ ∑ s ∈ range L, ((range T).filter fun t ↦
      Int.fract ((a t : ℝ) / (b : ℝ) ^ (s + k) - (blockCode w : ℕ) / (b : ℝ) ^ k) <
        1 / ((b ^ k : ℕ) : ℝ)).card := by
  classical
  rw [concatInternal]
  simp only [natBlockCount]
  calc ∑ t ∈ range T, ((range (Nat.log b (a t) + 1 + 1 - k)).filter
        fun s ↦ a t / b ^ s % b ^ k = blockCode w).card
      ≤ ∑ t ∈ range T, ((range L).filter fun s ↦ Int.fract ((a t : ℝ) / (b : ℝ) ^ (s + k) -
          (blockCode w : ℕ) / (b : ℝ) ^ k) < 1 / ((b ^ k : ℕ) : ℝ)).card := by
        refine sum_le_sum fun t ht ↦ card_le_card fun s hs ↦ ?_
        simp only [mem_filter, mem_range] at hs ht ⊢
        exact ⟨by have := hL t ht; omega, fract_div_pow_sub_lt hb hs.2⟩
    _ = _ := by
        simp only [card_filter]
        exact sum_comm

/-- **Counting digit blocks with Weyl sums**: positions `s` at which all Weyl sums of
`a t / b ^ (s + k)` are small contribute about `T / b ^ k` occurrences of `w`, the other positions
at most `T`. -/
theorem concatInternal_le_of_weylSum (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b) {T L : ℕ}
    (hL : ∀ t < T, Nat.log b (a t) + 1 ≤ L) (P : ℕ → Prop) [DecidablePred P] {ε : ℝ}
    (hε : 0 ≤ ε) (hW : ∀ s < L, P s → ∀ h ∈ Ico 1 (b ^ k),
      ‖Complex.weylSum (fun t ↦ (a t : ℝ) / (b : ℝ) ^ (s + k)) T h‖ ≤ ε * T) :
    (concatInternal b a w T : ℝ) ≤
      ((range L).filter fun s ↦ ¬ P s).card * T + L * (8 * T / (b : ℝ) ^ k + 16 * ε * T) := by
  have hK : 0 < b ^ k := pow_pos hb k
  have hK' : (0 : ℝ) < ((b ^ k : ℕ) : ℝ) := by exact_mod_cast hK
  set c : ℕ → ℕ := fun s ↦ ((range T).filter fun t ↦
      Int.fract ((a t : ℝ) / (b : ℝ) ^ (s + k) - (blockCode w : ℕ) / (b : ℝ) ^ k) <
        1 / ((b ^ k : ℕ) : ℝ)).card
  have h1 : (concatInternal b a w T : ℝ) ≤ ∑ s ∈ range L, (c s : ℝ) := by
    rw [← Nat.cast_sum]; exact Nat.cast_le.2 (concatInternal_le_sum_card hb hk w hL)
  have hcT : ∀ s, (c s : ℝ) ≤ T := fun s ↦ by
    exact_mod_cast (card_filter_le _ _).trans (card_range T).le
  have hcP : ∀ s ∈ (range L).filter P, (c s : ℝ) ≤ 8 * T / (b : ℝ) ^ k + 16 * ε * T := by
    intro s hs
    simp only [mem_filter, mem_range] at hs
    have hF := Complex.card_fract_sub_lt_le (fun t ↦ (a t : ℝ) / (b : ℝ) ^ (s + k))
      ((blockCode w : ℕ) / (b : ℝ) ^ k) hK T
    have hsum : ∑ h ∈ Ico 1 (b ^ k), ‖Complex.weylSum (fun t ↦ (a t : ℝ) / (b : ℝ) ^ (s + k)) T h‖
        ≤ (b ^ k : ℕ) * (ε * T) := by
      refine (sum_le_sum fun h hh ↦ hW s hs.1 hs.2 h hh).trans ?_
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      gcongr
      exact_mod_cast Nat.sub_le _ _
    calc (c s : ℝ) ≤ 8 * T / ((b ^ k : ℕ) : ℝ) + 16 / ((b ^ k : ℕ) : ℝ) *
          ∑ h ∈ Ico 1 (b ^ k), ‖Complex.weylSum (fun t ↦ (a t : ℝ) / (b : ℝ) ^ (s + k)) T h‖ := hF
      _ ≤ 8 * T / ((b ^ k : ℕ) : ℝ) + 16 / ((b ^ k : ℕ) : ℝ) * ((b ^ k : ℕ) * (ε * T)) := by
          gcongr
      _ = 8 * T / (b : ℝ) ^ k + 16 * ε * T := by
          rw [Nat.cast_pow]; field_simp
  rw [← sum_filter_not_add_sum_filter (range L) P] at h1
  refine h1.trans (add_le_add ?_ ?_)
  · exact (sum_le_sum fun s _ ↦ hcT s).trans (by rw [sum_const, nsmul_eq_mul])
  · refine (sum_le_sum hcP).trans ?_
    rw [sum_const, nsmul_eq_mul]
    gcongr
    exact_mod_cast (card_filter_le _ _).trans (card_range L).le

/-- A natural number `n` has more than `logb b n` digits in base `b`. -/
theorem logb_lt_natLog_add_one (n : ℕ) : logb b n < Nat.log b n + 1 := by
  rw [← natFloor_logb_natCast]; exact Nat.lt_floor_add_one _

/-- The number of digits of `M * T ^ d` is at most `logb M + d logb T` (plus one). -/
theorem natLog_mul_pow_le {M : ℕ} (hM : 1 ≤ M) (d : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    (Nat.log b (M * T ^ d) : ℝ) ≤ logb b M + d * logb b T := by
  refine (natLog_le_logb _ _).trans (le_of_eq ?_)
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have hT' : (T : ℝ) ≠ 0 := by positivity
  push_cast
  rw [logb_mul hM' (pow_ne_zero _ hT'), logb_pow]

/-- Terms of polynomial size `≥ c t ^ d` have `≈ d logb T` digits on average. -/
theorem eventually_concatStart_ge (hb : 1 < b) {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ t : ℕ in atTop, c * ((t : ℝ) + 1) ^ d ≤ a t) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ T : ℕ in atTop, (1 - η) * d * T * logb b T ≤ concatStart b a T := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨R, hR⟩ := exists_nat_gt (2 / η)
  have hR0 : (0 : ℝ) < R := (by positivity : (0 : ℝ) < 2 / η).trans hR
  have hR1 : 0 < R := by exact_mod_cast hR0
  have hRη : 1 / (R : ℝ) ≤ η / 2 := by
    rw [div_le_iff₀ hR0]; rw [div_lt_iff₀ hη] at hR; linarith
  obtain ⟨t0, ht0⟩ := eventually_atTop.1 hlow
  set c' := d * logb b R - logb b c
  have hℓ := (tendsto_logb_atTop hb').comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (t0 * R + R), eventually_ge_atTop 1,
    hℓ.eventually (eventually_ge_atTop ((2 / η + 1) * |c'|))] with T hT hT1 hℓT
  simp only [Function.comp_apply] at hℓT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  set ℓ := logb b T
  have hℓ0 : 0 ≤ ℓ := logb_nonneg hb' (by exact_mod_cast hT1)
  -- each term with `t ≥ T / R` has at least `g = d ℓ - c'` digits
  have hg : ∀ t ∈ Ico (T / R) T, d * ℓ - c' ≤ ((Nat.log b (a t) + 1 : ℕ) : ℝ) := by
    intro t ht
    rw [mem_Ico] at ht
    have htt0 : t0 ≤ t := by
      have : t0 ≤ T / R := (Nat.le_div_iff_mul_le hR1).2 (by nlinarith)
      omega
    have hTR : (T : ℝ) / R ≤ t + 1 := by
      rw [div_le_iff₀ hR0]
      have := Nat.lt_div_mul_add (a := T) hR1
      have : T ≤ (t + 1) * R := by nlinarith
      exact_mod_cast this
    have ha := ht0 t htt0
    have hpos : 0 < c * ((T : ℝ) / R) ^ d := by positivity
    have hle : c * ((T : ℝ) / R) ^ d ≤ a t := ha.trans' (by gcongr)
    calc d * ℓ - c' = logb b (c * ((T : ℝ) / R) ^ d) := by
          rw [logb_mul hc.ne' (by positivity), logb_pow, logb_div hT0.ne' hR0.ne']; ring
      _ ≤ logb b (a t) := logb_le_logb_of_le hb' hpos hle
      _ ≤ _ := by push_cast; exact (logb_lt_natLog_add_one (b := b) (a t)).le
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc'ℓ : |c'| ≤ ℓ := by
    have : 0 ≤ 2 / η * |c'| := by positivity
    nlinarith
  have hcard : (T : ℝ) * (1 - 1 / R) ≤ ((Ico (T / R) T).card : ℝ) := by
    rw [Nat.card_Ico, Nat.cast_sub (Nat.div_le_self _ _)]
    have := Nat.cast_div_le (α := ℝ) (m := T) (n := R)
    rw [mul_sub, mul_one, mul_one_div]
    linarith
  have hg0 : 0 ≤ d * ℓ - c' := by
    have := le_abs_self c'
    nlinarith
  calc (1 - η) * d * T * ℓ ≤ T * (1 - 1 / R) * (d * ℓ - c') := by
        have h1 : (1 - η / 2) * (d * ℓ - c') ≤ (1 - 1 / R) * (d * ℓ - c') := by gcongr
        have h2 : (1 - η) * d * ℓ ≤ (1 - η / 2) * (d * ℓ - c') := by
          have e1 : |c'| ≤ η / 2 * ℓ := by
            have : η / 2 * ((2 / η + 1) * |c'|) ≤ η / 2 * ℓ := by gcongr
            have e : η / 2 * ((2 / η + 1) * |c'|) = |c'| + η / 2 * |c'| := by field_simp
            have : 0 ≤ η / 2 * |c'| := by positivity
            linarith
          have e2 : η / 2 * ℓ ≤ η / 2 * (d * ℓ) := by gcongr; nlinarith
          have e3 : (1 - η / 2) * c' ≤ |c'| := by
            rcases le_or_gt 0 c' with h | h
            · rw [abs_of_nonneg h]; nlinarith
            · have : 0 ≤ |c'| := abs_nonneg _
              nlinarith
          nlinarith
        nlinarith
    _ ≤ ((Ico (T / R) T).card : ℝ) * (d * ℓ - c') := by gcongr
    _ = ∑ t ∈ Ico (T / R) T, (d * ℓ - c') := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ Ico (T / R) T, ((Nat.log b (a t) + 1 : ℕ) : ℝ) := sum_le_sum hg
    _ ≤ ∑ t ∈ range T, ((Nat.log b (a t) + 1 : ℕ) : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (fun t ht ↦ ?_) fun _ _ _ ↦ by positivity
        simp only [mem_Ico, mem_range] at ht ⊢; exact ht.2
    _ = concatStart b a T := by rw [concatStart]; push_cast; rfl

/-- Positions `s` at which the leading coefficient `A / b ^ (s + k)` of `f / b ^ (s + k)` is
not in the range of the uniform power saving are `O(δ logb T)` in number. -/
theorem card_filter_not_mid_le (hb : 1 < b) {A : ℝ} (hA : 1 ≤ A) {M : ℕ} (hM : 1 ≤ M)
    (d k : ℕ) {T : ℕ} (hT : 1 ≤ T) {δ : ℝ} (hδ : 0 ≤ δ) :
    (((range (Nat.log b (M * T ^ d) + 1)).filter fun s ↦ ¬((T : ℝ) ^ (δ - d) ≤
      A / (b : ℝ) ^ (s + k) ∧ (b : ℝ) ^ k * A / (b : ℝ) ^ (s + k) ≤ (T : ℝ) ^ (-δ))).card : ℝ) ≤
        2 * δ * logb b T + (logb b A + logb b M + k + 2) := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hA0 : 0 < A := by linarith
  set ℓ := logb b T
  have hℓ : 0 ≤ ℓ := logb_nonneg hb' (by exact_mod_cast hT)
  have hlA : 0 ≤ logb b A := logb_nonneg hb' hA
  have hlM : 0 ≤ logb b (M : ℝ) := logb_nonneg hb' (by exact_mod_cast hM)
  set L := Nat.log b (M * T ^ d) + 1
  have hL : (L : ℝ) ≤ logb b M + d * ℓ + 1 := by
    simp only [L]; push_cast; linarith [natLog_mul_pow_le (b := b) hM d hT]
  set u : ℝ := (d - δ) * ℓ - k
  set u' : ℝ := logb b A + δ * ℓ
  have hlogA : ∀ s : ℕ, logb b (A / (b : ℝ) ^ (s + k)) = logb b A - (s + k) := fun s ↦ by
    rw [logb_div hA0.ne' (by positivity), logb_pow, logb_self_eq_one hb']; push_cast; ring
  have hsub : (range L).filter (fun s ↦ ¬((T : ℝ) ^ (δ - d) ≤ A / (b : ℝ) ^ (s + k) ∧
      (b : ℝ) ^ k * A / (b : ℝ) ^ (s + k) ≤ (T : ℝ) ^ (-δ))) ⊆
      (range L).filter (fun s : ℕ ↦ u < s) ∪ (range L).filter (fun s : ℕ ↦ (s : ℝ) < u') := by
    intro s hs
    simp only [mem_filter, mem_union, not_and_or, not_le] at hs ⊢
    rcases hs.2 with h | h
    · left
      refine ⟨hs.1, ?_⟩
      have := logb_lt_logb hb' (by positivity) h
      rw [hlogA, logb_rpow_eq_mul_logb_of_pos hT0] at this
      simp only [u]; nlinarith
    · right
      refine ⟨hs.1, ?_⟩
      have := logb_lt_logb hb' (by positivity) h
      rw [mul_div_assoc, logb_mul (by positivity) (by positivity), logb_pow,
        logb_self_eq_one hb', hlogA, logb_rpow_eq_mul_logb_of_pos hT0] at this
      simp only [u']; linarith
  have h1 : (((range L).filter fun s : ℕ ↦ u < s).card : ℝ) ≤ logb b M + δ * ℓ + 1 + k := by
    have hss : (range L).filter (fun s : ℕ ↦ u < s) ⊆ Ico ⌈u⌉₊ L := fun s hs ↦ by
      simp only [mem_filter, mem_range, mem_Ico] at hs ⊢
      exact ⟨Nat.ceil_le.2 hs.2.le, hs.1⟩
    refine (Nat.cast_le.2 (card_le_card hss)).trans ?_
    rw [Nat.card_Ico]
    rcases le_total ⌈u⌉₊ L with h | h
    · rw [Nat.cast_sub h]
      have := Nat.le_ceil u
      simp only [u] at this
      nlinarith
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; positivity
  have h2 : (((range L).filter fun s : ℕ ↦ (s : ℝ) < u').card : ℝ) ≤ u' + 1 := by
    have hss : (range L).filter (fun s : ℕ ↦ (s : ℝ) < u') ⊆ range ⌈u'⌉₊ := fun s hs ↦ by
      simp only [mem_filter, mem_range] at hs ⊢
      exact Nat.lt_ceil.2 hs.2
    refine (Nat.cast_le.2 (card_le_card hss)).trans ?_
    rw [card_range]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  calc _ ≤ (((range L).filter fun s : ℕ ↦ u < s).card : ℝ) +
        (((range L).filter fun s : ℕ ↦ (s : ℝ) < u').card : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ _ := by simp only [u'] at h2; linarith

/-- **Normality of concatenations of polynomial-size sequences**: if `a t ≍ (t + 1) ^ d` and the
Weyl sums of `a t / b ^ (s + k)` are uniformly `o(T)` whenever the leading coefficient
`A / b ^ (s + k)` lies in `[T ^ (δ - d), T ^ (-δ) / b ^ k]`, then `0.a₀ a₁ a₂ …` is normal. -/
theorem isNormalIn_concatenation_of_growth [NeZero b] (hb : 2 ≤ b) {d : ℕ} (hd : 1 ≤ d) {A : ℝ}
    (hA : 1 ≤ A) {M : ℕ} (hM : 1 ≤ M) (hup : ∀ t, a t ≤ M * (t + 1) ^ d) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ t : ℕ in atTop, c * ((t : ℝ) + 1) ^ d ≤ a t)
    (hW : ∀ k, 0 < k → ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
      ∀ s, ∀ h ∈ Ico 1 (b ^ k),
      (T : ℝ) ^ (δ - d) ≤ A / (b : ℝ) ^ (s + k) →
        (b : ℝ) ^ k * A / (b : ℝ) ^ (s + k) ≤ (T : ℝ) ^ (-δ) →
          ‖Complex.weylSum (fun t ↦ (a t : ℝ) / (b : ℝ) ^ (s + k)) T h‖ ≤ ε * T) :
    IsNormalIn b (concatenation b a) := by
  classical
  have hb1 : 1 < b := by omega
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb1
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hℓ : Tendsto (fun T : ℕ ↦ logb b T) atTop atTop :=
    (tendsto_logb_atTop hb').comp tendsto_natCast_atTop_atTop
  have hS : ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ T : ℕ in atTop,
      (1 - η) * d * T * logb b T ≤ concatStart b a T := fun η hη hη1 ↦
    eventually_concatStart_ge (a := a) hb1 hd hc hlow hη hη1
  have hlog : ∀ T t, t < T → Nat.log b (a t) + 1 ≤ Nat.log b (M * T ^ d) + 1 := fun T t ht ↦ by
    have : a t ≤ M * T ^ d := (hup t).trans (by gcongr; omega)
    have := Nat.log_mono_right (b := b) this
    omega
  have hlM : 0 ≤ logb b (M : ℝ) := logb_nonneg hb' (by exact_mod_cast hM)
  refine isNormalIn_concatenation_of_concatInternal_le hb (C := 8) (by norm_num) ?_ ?_ ?_
  · -- `T = o(concatStart T)`
    have h2 : Tendsto (fun T : ℕ ↦ 2 * (logb b T)⁻¹) atTop (𝓝 (2 * 0)) :=
      (tendsto_inv_atTop_zero.comp hℓ).const_mul 2
    rw [mul_zero] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
    · exact Eventually.of_forall fun T ↦ by positivity
    filter_upwards [hS (1 / 2) (by norm_num) (by norm_num), eventually_ge_atTop 1,
      hℓ.eventually (eventually_gt_atTop 0)] with T hST hT hℓ0
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have : (1 / 2) * T * logb b T ≤ concatStart b a T := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]
    calc (T : ℝ) = 2 * (logb b T)⁻¹ * ((1 / 2) * T * logb b T) := by field_simp
      _ ≤ _ := by gcongr
  · -- the length of a term is `o(concatStart T)`
    set c := logb b (M : ℝ) + d * logb b 2 + 1
    have hc : 0 ≤ c := by have := logb_nonneg hb' (by norm_num : (1 : ℝ) ≤ 2); positivity
    have h2 : Tendsto (fun T : ℕ ↦ (2 * c + 2) * (T : ℝ)⁻¹) atTop (𝓝 ((2 * c + 2) * 0)) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _
    rw [mul_zero] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
    · exact Eventually.of_forall fun T ↦ by positivity
    filter_upwards [hS (1 / 2) (by norm_num) (by norm_num), eventually_ge_atTop 1,
      hℓ.eventually (eventually_ge_atTop 1)] with T hST hT hℓ1
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hS0 : (1 / 2) * d * T * logb b T ≤ concatStart b a T := by
      convert hST using 2; norm_num
    have hnum : ((Nat.log b (a T) : ℝ) + 1) ≤ c + d * logb b T := by
      have h1 := hlog (T + 1) T (by omega)
      have h2 := natLog_mul_pow_le (b := b) hM d (show 1 ≤ T + 1 by omega)
      have h3 : logb b ((T + 1 : ℕ) : ℝ) ≤ logb b 2 + logb b T := by
        rw [← logb_mul (by norm_num) hT0.ne']
        exact logb_le_logb_of_le hb' (by positivity) (by push_cast; linarith)
      have : ((Nat.log b (a T) : ℕ) : ℝ) + 1 ≤ (Nat.log b (M * (T + 1) ^ d) : ℝ) + 1 := by
        exact_mod_cast h1
      simp only [c]; nlinarith
    have hdℓ : 1 ≤ d * logb b T := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]
    calc ((Nat.log b (a T) : ℝ) + 1) ≤ c * (d * logb b T) + d * logb b T := by nlinarith
      _ = (2 * c + 2) * (T : ℝ)⁻¹ * ((1 / 2) * d * T * logb b T) := by field_simp
      _ ≤ _ := by gcongr
  · intro k hk w ε hε
    set κ : ℝ := 8 * ((b : ℝ) ^ k)⁻¹ with hκ
    have hbk : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ hb'.le
    have hκ0 : 0 ≤ κ := by positivity
    have hκ8 : κ ≤ 8 := by
      have := inv_le_one_of_one_le₀ hbk
      simp only [hκ]; linarith
    set δ : ℝ := ε * d / 8 with hδ
    have hδ0 : 0 < δ := by positivity
    set η : ℝ := ε / (4 * (8 + ε)) with hη
    have hη0 : 0 < η := by positivity
    have hη1 : η < 1 := by rw [hη, div_lt_one (by positivity)]; linarith
    have hκη : (κ + ε) * η ≤ ε / 4 := by
      calc (κ + ε) * η ≤ (8 + ε) * η := by gcongr
        _ = ε / 4 := by rw [hη]; field_simp
    set c2 := logb b A + logb b (M : ℝ) + k + 2
    set c3 := c2 + (logb b (M : ℝ) + 1) * (8 + ε / 4)
    filter_upwards [eventually_ge_atTop 1, hW k hk δ hδ0 (ε / 64) (by positivity),
      hS η hη0 hη1, hℓ.eventually (eventually_ge_atTop (4 * c3 / ε))] with T hT hWT hST hℓT
    set ℓ := logb b (T : ℝ)
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have hc2 : 0 ≤ c2 := by have := logb_nonneg hb' hA; positivity
    have hc3 : 0 ≤ c3 := by positivity
    have hℓ0 : 0 ≤ ℓ := le_trans (by positivity) hℓT
    have hc3ℓ : c3 ≤ ε / 4 * ℓ := by
      rw [div_le_iff₀ hε] at hℓT; linarith
    have hCI := concatInternal_le_of_weylSum (a := a) (by omega) hk w (T := T)
      (hlog T) (fun s ↦ (T : ℝ) ^ (δ - d) ≤ A / (b : ℝ) ^ (s + k) ∧
        (b : ℝ) ^ k * A / (b : ℝ) ^ (s + k) ≤ (T : ℝ) ^ (-δ)) (by positivity : 0 ≤ ε / 64)
      (fun s _ hs h hh ↦ hWT s h hh hs.1 hs.2)
    have hbad := card_filter_not_mid_le (A := A) hb1 hA hM d k hT hδ0.le
    have hL : ((Nat.log b (M * T ^ d) + 1 : ℕ) : ℝ) ≤ logb b M + d * ℓ + 1 := by
      push_cast; linarith [natLog_mul_pow_le (b := b) hM d hT]
    set bad := (((range (Nat.log b (M * T ^ d) + 1)).filter fun s ↦ ¬((T : ℝ) ^ (δ - d) ≤
      A / (b : ℝ) ^ (s + k) ∧ (b : ℝ) ^ k * A / (b : ℝ) ^ (s + k) ≤ (T : ℝ) ^ (-δ))).card : ℝ)
    set L := ((Nat.log b (M * T ^ d) + 1 : ℕ) : ℝ)
    have e1 : 8 * (T : ℝ) / (b : ℝ) ^ k + 16 * (ε / 64) * T = (κ + ε / 4) * T := by
      rw [hκ]; field_simp; ring
    rw [e1] at hCI
    have hdℓ : 0 ≤ (d : ℝ) * ℓ := by positivity
    have key : (2 * δ * ℓ + c2) + (logb b (M : ℝ) + d * ℓ + 1) * (κ + ε / 4) ≤
        (κ + 3 * ε / 4) * (d * ℓ) := by
      have : (logb b (M : ℝ) + 1) * (κ + ε / 4) ≤ (logb b (M : ℝ) + 1) * (8 + ε / 4) := by
        gcongr
      have : ε / 4 * ℓ ≤ ε / 4 * (d * ℓ) := by gcongr; nlinarith
      have e1 : 2 * δ * ℓ = ε / 4 * (d * ℓ) := by rw [hδ]; ring
      have e2 : (logb b (M : ℝ) + d * ℓ + 1) * (κ + ε / 4) =
          (logb b (M : ℝ) + 1) * (κ + ε / 4) + (d * ℓ) * κ + ε / 4 * (d * ℓ) := by ring
      have e3 : (κ + 3 * ε / 4) * (d * ℓ) = (d * ℓ) * κ + 3 * (ε / 4 * (d * ℓ)) := by ring
      have e4 : c3 = c2 + (logb b (M : ℝ) + 1) * (8 + ε / 4) := rfl
      rw [e1, e2, e3]
      linarith
    calc (concatInternal b a w T : ℝ) ≤ bad * T + L * ((κ + ε / 4) * T) := hCI
      _ ≤ (2 * δ * ℓ + c2) * T + (logb b (M : ℝ) + d * ℓ + 1) * ((κ + ε / 4) * T) := by
          gcongr
      _ = ((2 * δ * ℓ + c2) + (logb b (M : ℝ) + d * ℓ + 1) * (κ + ε / 4)) * T := by ring
      _ ≤ (κ + 3 * ε / 4) * (d * ℓ) * T := by gcongr
      _ ≤ (κ + ε) * ((1 - η) * d * T * ℓ) := by
          have : κ + 3 * ε / 4 ≤ (κ + ε) * (1 - η) := by nlinarith
          have : 0 ≤ (d : ℝ) * ℓ * T := by positivity
          nlinarith
      _ ≤ (κ + ε) * concatStart b a T := by gcongr

end Polynomials

/-- **The Davenport–Erdős theorem**: if `f` is a non-constant integer polynomial with `f(n) > 0`
for all `n ≥ 1`, then `0.f(1) f(2) f(3) …` is normal in every base `b ≥ 2`. -/
theorem isNormalIn_concatenation_polynomial {b : ℕ} [NeZero b] (hb : 2 ≤ b) {f : ℤ[X]}
    (hf : 0 < f.natDegree) (hpos : ∀ n : ℕ, 0 < f.eval ((n : ℤ) + 1)) :
    IsNormalIn b (concatenation b fun n ↦ (f.eval ((n : ℤ) + 1)).toNat) := by
  set a : ℕ → ℕ := fun n ↦ (f.eval ((n : ℤ) + 1)).toNat with ha
  set d := f.natDegree with hd
  set F : ℝ[X] := f.map (Int.castRingHom ℝ) with hF
  have hFd : F.natDegree = d := natDegree_map_eq_of_injective Int.cast_injective f
  have hFlc : F.leadingCoeff = f.leadingCoeff := leadingCoeff_map_of_injective Int.cast_injective f
  have hFeval : ∀ x : ℤ, F.eval (x : ℝ) = f.eval x := fun x ↦ by
    simp [hF, eval_map]
  have hat : ∀ t : ℕ, ((a t : ℕ) : ℤ) = f.eval ((t : ℤ) + 1) := fun t ↦
    Int.toNat_of_nonneg (hpos t).le
  have haF : ∀ t : ℕ, (a t : ℝ) = F.eval ((t : ℝ) + 1) := fun t ↦ by
    rw [show ((t : ℝ) + 1) = (((t : ℤ) + 1 : ℤ) : ℝ) by push_cast; ring, hFeval, ← hat]
    rfl
  have hshift : Tendsto (fun t : ℕ ↦ (t : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  -- the leading coefficient is positive
  have hlc : 0 < f.leadingCoeff := by
    by_contra h
    push Not at h
    have hdeg : 0 < F.degree := natDegree_pos_iff_degree_pos.1 (hFd ▸ hf)
    have hbot := tendsto_atBot_of_leadingCoeff_nonpos hdeg (by rw [hFlc]; exact_mod_cast h)
    obtain ⟨t, ht⟩ := (hshift.eventually (hbot.eventually (eventually_lt_atBot 0))).exists
    rw [← haF] at ht
    exact (Nat.cast_nonneg (a t)).not_gt ht
  set A : ℝ := (f.leadingCoeff : ℝ) with hA
  have hA1 : 1 ≤ A := by
    have : (1 : ℤ) ≤ f.leadingCoeff := hlc
    rw [hA]; exact_mod_cast this
  -- upper bound
  set M : ℕ := ⌈f.l1Norm⌉₊ + 1
  have hup : ∀ t, a t ≤ M * (t + 1) ^ d := fun t ↦ by
    have h := norm_eval_le_l1Norm_mul f ((t : ℤ) + 1)
    have hz : ‖((t : ℤ) + 1 : ℤ)‖ = (t : ℝ) + 1 := by
      rw [Int.norm_eq_abs]; push_cast; exact abs_of_pos (by positivity)
    rw [hz, max_eq_right (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]), Int.norm_eq_abs] at h
    have h1 : (a t : ℝ) ≤ f.l1Norm * ((t : ℝ) + 1) ^ d := by
      refine le_trans (le_of_eq ?_) ((le_abs_self _).trans h)
      exact_mod_cast hat t
    have h2 : f.l1Norm ≤ M := by
      simp only [M]; push_cast; linarith [Nat.le_ceil f.l1Norm]
    have : (a t : ℝ) ≤ M * ((t : ℝ) + 1) ^ d := h1.trans (by gcongr)
    exact_mod_cast this
  -- lower bound
  have hlow : ∀ᶠ t : ℕ in atTop, A / 2 * ((t : ℝ) + 1) ^ d ≤ a t := by
    have h := (isEquivalent_atTop_lead F).isLittleO.def (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hshift.eventually h] with t ht
    simp only [Pi.sub_apply, Real.norm_eq_abs, hFd, hFlc] at ht
    rw [haF]
    have hv : 0 ≤ A * ((t : ℝ) + 1) ^ d := by positivity
    rw [abs_of_nonneg hv, abs_le] at ht
    linarith [ht.1]
  refine isNormalIn_concatenation_of_growth hb hf hA1 (by omega) hup (by positivity) hlow ?_
  intro k hk δ hδ ε hε
  filter_upwards [Polynomial.eventually_norm_polyExpSum_le (d := d) hf hδ hε] with T hT s h hh h1 h2
  rw [mem_Ico] at hh
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  set φ : ℝ[X] := C ((h : ℝ) / (b : ℝ) ^ (s + k)) * F.comp (X + C 1) with hφ
  have hcd : (F.comp (X + C 1)).natDegree = d := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one, hFd]
  have hcl : (F.comp (X + C 1)).coeff d = A := by
    conv_lhs => rw [← hcd]
    change leadingCoeff _ = _
    rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; norm_num), leadingCoeff_X_add_C, one_pow,
      mul_one, hFlc]
  have hφd : φ.natDegree ≤ d := (natDegree_C_mul_le _ _).trans hcd.le
  have hφc : φ.coeff d = (h : ℝ) / (b : ℝ) ^ (s + k) * A := by rw [hφ, coeff_C_mul, hcl]
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh.1
  have hhK : (h : ℝ) ≤ (b : ℝ) ^ k := by exact_mod_cast hh.2.le
  have := hT φ hφd (by
      rw [hφc]
      refine h1.trans (le_of_le_of_eq ?_ (div_mul_eq_mul_div _ _ _).symm)
      rw [div_le_div_iff_of_pos_right (by positivity)]; nlinarith)
    (by
      rw [hφc]
      refine le_trans (le_of_eq_of_le (div_mul_eq_mul_div _ _ _) ?_) h2
      rw [div_le_div_iff_of_pos_right (by positivity)]
      gcongr)
  refine le_of_eq_of_le ?_ this
  unfold Complex.weylSum polyExpSum
  refine congrArg _ (sum_congr rfl fun t _ ↦ ?_)
  rw [Complex.cexpTwoPi]
  congr 1
  simp only [hφ, eval_mul, eval_C, eval_comp, eval_add, eval_X, ← haF]
  push_cast
  ring

/-- **Besicovitch's theorem**: the concatenation `0.1 4 9 16 25 …` of the squares is normal in
every base `b ≥ 2`. -/
theorem isNormalIn_concatenation_sq {b : ℕ} [NeZero b] (hb : 2 ≤ b) :
    IsNormalIn b (concatenation b fun n ↦ (n + 1) ^ 2) := by
  have hb1 : 1 < b := by omega
  refine isNormalIn_ofDigits hb ?_
  have ha : StrictMono fun n : ℕ ↦ (n + 1) ^ 2 := fun m n h ↦
    Nat.pow_lt_pow_left (by omega) two_ne_zero
  convert isNormalSeq_concatDigit_of_concatBad hb ha (by positivity) (c := 2)
    (Eventually.of_forall fun T ↦ (Nat.log_lt_of_lt_pow' (by omega) ?_).le)
    fun k hk w ε hε ↦ tendsto_concatBad_sq hb hk w hε using 2 with n
  · simp [Nat.mod_eq_of_lt (concatDigit_lt (b := b) (by omega) _ n)]
  · rw [pow_mul']
    exact Nat.pow_lt_pow_left (Nat.lt_pow_self hb1) two_ne_zero

end Real
