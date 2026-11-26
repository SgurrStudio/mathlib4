/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
public import Mathlib.Imported.TauCeti.NumberTheory.CircleMethod.TypeISum
public import Mathlib.NumberTheory.Normal.DifferenceTest

import Mathlib.Algebra.Order.Chebyshev

/-!
# Weyl's inequality

For a real polynomial `φ` of degree at most `k ≥ 1` whose `k`-th coefficient `α` satisfies
`|α - a / q| ≤ 1 / q²` with `gcd(a, q) = 1` and `q ≥ 1`, and for every `ε > 0`,

`‖∑_{n < N} e(φ(n))‖ ≤ C(k, ε) · N ^ (1 + ε) · (1 / q + 1 / N + q / N ^ k) ^ (2 ^ (1 - k))`.

The proof is Vaughan's (Lemma 2.4):

* Weyl differencing (`Polynomial.polyExpSum_sq_le`, from van der Corput's inequality) `k - 1`
  times, with `H = N`, lowers the phase to a linear one with frequency `k! α h₁ ⋯ h_{k-1}`; its
  geometric series is at most `min(N, 1 / ‖k! α h₁ ⋯ h_{k-1}‖)`
  (`Polynomial.norm_polyExpSum_pow_le_weylSum`).
* Regrouping by `m = h₁ ⋯ h_{k-1}` costs a factor `N ^ ε` by the divisor bound
  (`TauCeti.exists_pos_card_divisors_le_rpow`), see `Polynomial.weylSum_le`.
* The type I bound (`TauCeti.sum_min_inv_distInt_le`) sums the resulting
  `∑_{m ≤ k! N ^ (k-1)} min(N, 1 / ‖α m‖)`.

## Main statements

* `Polynomial.norm_polyExpSum_le_weyl`: **Weyl's inequality**.

## References

* R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Lemma 2.4.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §8.2.
-/

@[expose] public section

open Complex Finset TauCeti

namespace Polynomial

/-- The geometric-series weight `min(N, 1 / ‖β‖)`, taking the value `N` when `β` is an integer. -/
noncomputable def weylMin (N : ℕ) (β : ℝ) : ℝ :=
  if distInt β = 0 then N else min (N : ℝ) (distInt β)⁻¹

/-- The iterated sum `∑_{h₁, …, h_j ∈ [1, N)} min(N, 1 / ‖β h₁ ⋯ h_j‖)` left after `j` Weyl
differencings. -/
noncomputable def weylSum (N : ℕ) : ℕ → ℝ → ℝ
  | 0, β => weylMin N β
  | j + 1, β => ∑ h ∈ Ico 1 N, weylSum N j (β * h)

theorem weylMin_nonneg (N : ℕ) (β : ℝ) : 0 ≤ weylMin N β := by
  unfold weylMin
  split_ifs
  · positivity
  · exact le_min (Nat.cast_nonneg N) (inv_nonneg.2 (distInt_nonneg _))

theorem weylSum_nonneg (N j : ℕ) (β : ℝ) : 0 ≤ weylSum N j β := by
  induction j generalizing β with
  | zero => exact weylMin_nonneg N β
  | succ j ih => exact sum_nonneg fun h _ ↦ ih _

/-- A linear phase: its exponential sum over `n < L ≤ N` is at most `min(N, 1 / ‖α‖)`. -/
theorem norm_polyExpSum_le_weylMin {φ : ℝ[X]} (hφ : φ.natDegree ≤ 1) {L N : ℕ} (hLN : L ≤ N) :
    ‖polyExpSum φ L‖ ≤ weylMin N (φ.coeff 1) := by
  set α := φ.coeff 1
  have hev : ∀ x : ℝ, φ.eval x = α * x + φ.coeff 0 := fun x ↦ by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hφ]
    simp [α]
  have e : polyExpSum φ L = expTwoPiI (φ.coeff 0 - α) * ∑ n ∈ Icc 1 L, expTwoPiI (n * α) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [← expTwoPiI_add, expTwoPiI_def, hev]
    push_cast; ring_nf
  rw [e, norm_mul, norm_expTwoPiI, one_mul]
  refine (norm_sum_expTwoPiI_le L α).trans ?_
  have hL : (L : ℝ) ≤ N := by exact_mod_cast hLN
  unfold weylMin
  split_ifs with h
  · exact hL
  · have := distInt_nonneg α
    have hpos : 0 < distInt α := lt_of_le_of_ne this (Ne.symm h)
    refine min_le_min hL ?_
    rw [one_div]
    exact inv_anti₀ hpos (by linarith)

/-- **Weyl differencing**, iterated `j` times with `H = N`. -/
theorem norm_polyExpSum_pow_le_weylSum (j : ℕ) : ∃ K : ℝ, 0 < K ∧
    ∀ (N L : ℕ) (φ : ℝ[X]), 1 ≤ N → L ≤ N → φ.natDegree ≤ j + 1 →
      (‖polyExpSum φ L‖ / N) ^ 2 ^ j ≤
        K * (1 / N + weylSum N j ((j + 1).factorial * φ.coeff (j + 1)) / (N : ℝ) ^ (j + 1)) := by
  induction j with
  | zero =>
    refine ⟨1, one_pos, fun N L φ hN hLN hφ ↦ ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [pow_zero, pow_one, zero_add, Nat.factorial_one, Nat.cast_one, one_mul, weylSum]
    have := norm_polyExpSum_le_weylMin hφ hLN
    have h0 : 0 ≤ 1 / (N : ℝ) := by positivity
    calc ‖polyExpSum φ L‖ / N ≤ weylMin N (φ.coeff 1) / N := by gcongr
      _ ≤ 1 / N + weylMin N (φ.coeff 1) / N := by linarith
  | succ j ih =>
    obtain ⟨K, hK, hKj⟩ := ih
    set m := 2 ^ j
    have hm : 1 ≤ m := Nat.one_le_two_pow
    refine ⟨2 ^ (m - 1) * (2 ^ m + 4 ^ m * K), by positivity, fun N L φ hN hLN hφ ↦ ?_⟩
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    set c := φ.coeff (j + 1 + 1)
    set x : ℕ → ℝ := fun h ↦ ‖polyExpSum (taylor (h : ℝ) φ - φ) (L - h)‖ / N
    have hx0 : ∀ h, 0 ≤ x h := fun h ↦ by positivity
    set W := weylSum N (j + 1) ((j + 1 + 1).factorial * c)
    set Y := W / (N : ℝ) ^ (j + 1 + 1)
    have hY : 0 ≤ Y := div_nonneg (weylSum_nonneg _ _ _) (by positivity)
    have hxh : ∀ h ∈ Ico 1 N, x h ^ m ≤
        K * (1 / N + weylSum N j ((j + 1 + 1).factorial * c * h) / (N : ℝ) ^ (j + 1)) := by
      intro h hh
      obtain ⟨hdeg, hcoeff⟩ := natDegree_taylor_sub_le hφ (h : ℝ)
      have := hKj N (L - h) _ hN (by omega) hdeg
      rw [hcoeff] at this
      refine this.trans (le_of_eq ?_)
      congr 4
      rw [Nat.factorial_succ (j + 1)]; push_cast; ring
    have hsum : 1 / (N : ℝ) * ∑ h ∈ Ico 1 N, x h ^ m ≤ K * (1 / N + Y) := by
      have h1 : ∑ h ∈ Ico 1 N, x h ^ m ≤ K * (∑ _h ∈ Ico 1 N, 1 / (N : ℝ) +
          W / (N : ℝ) ^ (j + 1)) := by
        refine (sum_le_sum hxh).trans (le_of_eq ?_)
        rw [← mul_sum, sum_add_distrib]
        simp only [W, weylSum, sum_div]
      have h2 : ∑ _h ∈ Ico 1 N, 1 / (N : ℝ) ≤ 1 := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one_div, div_le_one hN0]
        exact_mod_cast Nat.sub_le N 1
      have hW : 0 ≤ W / (N : ℝ) ^ (j + 1) := div_nonneg (weylSum_nonneg _ _ _) (by positivity)
      calc 1 / (N : ℝ) * ∑ h ∈ Ico 1 N, x h ^ m
          ≤ 1 / N * (K * (1 + W / (N : ℝ) ^ (j + 1))) := by
            gcongr; exact h1.trans (by gcongr)
        _ = K * (1 / N + Y) := by simp only [Y]; rw [pow_succ]; field_simp; ring
    have hv := polyExpSum_sq_le φ hN le_rfl hLN
    have hjensen : (∑ h ∈ Ico 1 N, x h) ^ m ≤ (N : ℝ) ^ (m - 1) * ∑ h ∈ Ico 1 N, x h ^ m := by
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hm', Nat.add_sub_cancel]
      refine (pow_sum_le_card_mul_sum_pow (fun h _ ↦ hx0 h) m').trans ?_
      gcongr
      rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le N 1
    calc (‖polyExpSum φ L‖ / N) ^ 2 ^ (j + 1) = ((‖polyExpSum φ L‖ / N) ^ 2) ^ m := by
          rw [pow_succ', pow_mul]
      _ ≤ (2 / N + 4 / N * ∑ h ∈ Ico 1 N, x h) ^ m := by gcongr
      _ ≤ 2 ^ (m - 1) * ((2 / N) ^ m + (4 / N * ∑ h ∈ Ico 1 N, x h) ^ m) :=
          add_pow_le (by positivity) (by positivity) m
      _ ≤ 2 ^ (m - 1) * (2 ^ m * (1 / N) + 4 ^ m * (K * (1 / N + Y))) := by
          gcongr
          · rw [div_pow]
            calc (2 : ℝ) ^ m / (N : ℝ) ^ m ≤ 2 ^ m / N := by
                  gcongr; exact le_self_pow₀ hNR (by omega)
              _ = 2 ^ m * (1 / N) := by ring
          · rw [mul_pow, div_pow]
            calc (4 : ℝ) ^ m / (N : ℝ) ^ m * (∑ h ∈ Ico 1 N, x h) ^ m
                ≤ 4 ^ m / (N : ℝ) ^ m * ((N : ℝ) ^ (m - 1) * ∑ h ∈ Ico 1 N, x h ^ m) := by
                  gcongr
              _ = 4 ^ m * (1 / (N : ℝ) * ∑ h ∈ Ico 1 N, x h ^ m) := by
                  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                  rw [hm', Nat.add_sub_cancel, pow_succ]; field_simp; ring
              _ ≤ 4 ^ m * (K * (1 / N + Y)) := by gcongr
      _ ≤ 2 ^ (m - 1) * (2 ^ m * (1 / N + Y) + 4 ^ m * (K * (1 / N + Y))) := by
          gcongr; linarith
      _ = 2 ^ (m - 1) * (2 ^ m + 4 ^ m * K) * (1 / N + Y) := by ring

/-- Regrouping a double sum by the product `n = h m`: each `n` occurs at most `d(n)` times. -/
theorem sum_Ico_sum_Icc_mul_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N M : ℕ) :
    ∑ h ∈ Ico 1 N, ∑ m ∈ Icc 1 M, f (h * m) ≤
      ∑ n ∈ Icc 1 (N * M), (n.divisors.card : ℝ) * f n := by
  rw [← sum_product' (f := fun h m ↦ f (h * m))]
  have hmaps : ∀ p ∈ Ico 1 N ×ˢ Icc 1 M, p.1 * p.2 ∈ Icc 1 (N * M) := by
    intro p hp
    simp only [mem_product, mem_Ico, mem_Icc] at hp ⊢
    exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hp.1.2.le hp.2.2⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.1 hn).1; omega
  rw [sum_congr rfl (g := fun _ ↦ f n) (fun p hp ↦ by rw [(mem_filter.1 hp).2]), sum_const,
    nsmul_eq_mul]
  gcongr
  · exact hf n
  refine card_le_card_of_injOn Prod.fst ?_ ?_
  · intro p hp
    have hp := mem_filter.1 hp
    exact Nat.mem_divisors.2 ⟨⟨p.2, hp.2.symm⟩, hn0⟩
  · intro p hp p' hp' h
    have hp := mem_filter.1 hp
    have hp' := mem_filter.1 hp'
    have h1 : 1 ≤ p.1 := (mem_Ico.1 (mem_product.1 hp.1).1).1
    have h2 : p.1 * p.2 = p.1 * p'.2 := by rw [hp.2]; rw [h] at ⊢; exact hp'.2.symm
    exact Prod.ext h (Nat.eq_of_mul_eq_mul_left h1 h2)

/-- The divisor bound turns the iterated sum into a single sum, at the cost of `N ^ δ`. -/
theorem weylSum_le (j : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ A : ℝ, 0 < A ∧
    ∀ (N : ℕ) (β : ℝ), 1 ≤ N →
      weylSum N j β ≤ A * (N : ℝ) ^ δ * ∑ m ∈ Icc 1 (N ^ j), weylMin N (β * m) := by
  induction j generalizing δ with
  | zero =>
    refine ⟨1, one_pos, fun N β hN ↦ ?_⟩
    simp only [weylSum, pow_zero, Icc_self, sum_singleton, Nat.cast_one, mul_one, one_mul]
    exact le_mul_of_one_le_left (weylMin_nonneg N β)
      (Real.one_le_rpow (by exact_mod_cast hN) hδ.le)
  | succ j ih =>
    obtain ⟨A, hA, hAj⟩ := ih (half_pos hδ)
    obtain ⟨C, hC, hdiv⟩ := exists_pos_card_divisors_le_rpow
      (show 0 < δ / 2 / (j + 1 : ℝ) by positivity)
    refine ⟨A * C, by positivity, fun N β hN ↦ ?_⟩
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    set g : ℕ → ℝ := fun n ↦ weylMin N (β * n)
    have hg : ∀ n, 0 ≤ g n := fun n ↦ weylMin_nonneg N _
    have hd : ∀ n ∈ Icc 1 (N * N ^ j), (n.divisors.card : ℝ) ≤ C * (N : ℝ) ^ (δ / 2) := by
      intro n hn
      refine (hdiv n).trans ?_
      gcongr
      have hn' : (n : ℝ) ≤ (N : ℝ) ^ (j + 1) := by
        rw [pow_succ']; exact_mod_cast (mem_Icc.1 hn).2
      calc (n : ℝ) ^ (δ / 2 / (j + 1 : ℝ)) ≤ ((N : ℝ) ^ (j + 1)) ^ (δ / 2 / (j + 1 : ℝ)) := by
            gcongr
        _ = (N : ℝ) ^ (δ / 2) := by
            rw [← Real.rpow_natCast_mul (by positivity)]
            congr 1
            push_cast
            field_simp
    calc weylSum N (j + 1) β = ∑ h ∈ Ico 1 N, weylSum N j (β * h) := rfl
      _ ≤ ∑ h ∈ Ico 1 N, A * (N : ℝ) ^ (δ / 2) * ∑ m ∈ Icc 1 (N ^ j), g (h * m) := by
          refine sum_le_sum fun h _ ↦ (hAj N _ hN).trans (le_of_eq ?_)
          congr 1
          refine sum_congr rfl fun m _ ↦ ?_
          simp only [g]; push_cast; ring_nf
      _ = A * (N : ℝ) ^ (δ / 2) * ∑ h ∈ Ico 1 N, ∑ m ∈ Icc 1 (N ^ j), g (h * m) := by
          rw [mul_sum]
      _ ≤ A * (N : ℝ) ^ (δ / 2) * ∑ n ∈ Icc 1 (N * N ^ j), (n.divisors.card : ℝ) * g n := by
          gcongr
          exact sum_Ico_sum_Icc_mul_le hg N (N ^ j)
      _ ≤ A * (N : ℝ) ^ (δ / 2) * ∑ n ∈ Icc 1 (N * N ^ j), C * (N : ℝ) ^ (δ / 2) * g n := by
          gcongr with n hn
          · exact hg n
          · exact hd n hn
      _ = A * C * (N : ℝ) ^ δ * ∑ m ∈ Icc 1 (N ^ (j + 1)), weylMin N (β * m) := by
          rw [← pow_succ', ← mul_sum]
          have : (N : ℝ) ^ δ = (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) := by
            rw [← Real.rpow_add (by positivity)]; ring_nf
          rw [this]; ring

/-- The type I bound for `∑_{m ≤ M} min(N, 1 / ‖c α m‖)` with an integer factor `c ≥ 1`. -/
theorem sum_weylMin_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (ha : Int.gcd a q = 1)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N M c : ℕ) (hc : 1 ≤ c) :
    ∑ m ∈ Icc 1 M, weylMin N (c * α * m) ≤
      16 * (N * c * M / q + c * M + q) * Real.log (2 * (c * M) * q) := by
  set X : ℝ := N * c * M
  have hX : 0 ≤ X := by positivity
  set T : ℕ → ℝ := fun m ↦
    if distInt (m * α) = 0 then X / m else min (X / m) (distInt (m * α))⁻¹
  have hT : ∀ m, 0 ≤ T m := fun m ↦ by
    simp only [T]
    split_ifs
    · positivity
    · exact le_min (by positivity) (inv_nonneg.2 (distInt_nonneg _))
  have h1 : ∀ m ∈ Icc 1 M, weylMin N (c * α * m) ≤ T (c * m) := by
    intro m hm
    have hm := mem_Icc.1 hm
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hMR : (m : ℝ) ≤ M := by exact_mod_cast hm.2
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hNX : (N : ℝ) ≤ X / ((c * m : ℕ) : ℝ) := by
      rw [le_div_iff₀ (by push_cast; positivity)]
      simp only [X]; push_cast
      have : (0 : ℝ) ≤ N * c := by positivity
      nlinarith
    have he : ((c * m : ℕ) : ℝ) * α = c * α * m := by push_cast; ring
    simp only [weylMin, T, he]
    split_ifs
    · exact hNX
    · exact min_le_min hNX le_rfl
  have hinj : Set.InjOn (fun m ↦ c * m) (Icc 1 M : Set ℕ) := fun m _ m' _ h ↦
    Nat.eq_of_mul_eq_mul_left hc h
  have hsub : (Icc 1 M).image (fun m ↦ c * m) ⊆ Icc 1 (c * M) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_image.1 hx
    have hm := mem_Icc.1 hm
    exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul_left c hm.2⟩
  calc ∑ m ∈ Icc 1 M, weylMin N (c * α * m) ≤ ∑ m ∈ Icc 1 M, T (c * m) := sum_le_sum h1
    _ = ∑ m ∈ (Icc 1 M).image (fun m ↦ c * m), T m := (sum_image hinj).symm
    _ ≤ ∑ m ∈ Icc 1 (c * M), T m := sum_le_sum_of_subset_of_nonneg hsub fun m _ _ ↦ hT m
    _ ≤ 16 * (X / q + (c * M : ℕ) + q) * Real.log (2 * (c * M : ℕ) * q) :=
        sum_min_inv_distInt_le hq ha hα (c * M) hX
    _ = 16 * (N * c * M / q + c * M + q) * Real.log (2 * (c * M) * q) := by push_cast; rfl

/-- **Weyl's inequality.** If the `k`-th coefficient `α` of a real polynomial `φ` of degree at
most `k ≥ 1` satisfies `|α - a / q| ≤ 1 / q²` with `q ≥ 1` and `gcd(a, q) = 1`, then
`‖∑_{n < N} e(φ(n))‖ ≤ C N ^ (1 + ε) (1 / q + 1 / N + q / N ^ k) ^ (2 ^ (1 - k))`. -/
theorem norm_polyExpSum_le_weyl {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (φ : ℝ[X]) (a : ℤ) (q : ℕ), φ.natDegree ≤ k → 0 < q → Int.gcd a q = 1 →
      |φ.coeff k - a / q| ≤ 1 / (q : ℝ) ^ 2 →
        ‖polyExpSum φ N‖ ≤ C * (N : ℝ) ^ (1 + ε) *
          (1 / q + 1 / N + q / (N : ℝ) ^ k) ^ ((2 : ℝ) ^ (k - 1))⁻¹ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨K, hK, hKw⟩ := norm_polyExpSum_pow_le_weylSum j
  obtain ⟨A, hA, hAw⟩ := weylSum_le j hδ
  have hF : (1 : ℝ) ≤ (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  set F : ℝ := ((j + 1).factorial : ℝ)
  set D := 1 + Real.log (2 * F) + 2 * (j + 1) / δ
  have hlog2F : 0 ≤ Real.log (2 * F) := Real.log_nonneg (by linarith)
  have hD : 0 < D := by positivity
  set B := K * (1 + 16 * A * F) * D
  have hB : 0 < B := by positivity
  set r : ℝ := ((2 : ℝ) ^ j)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  refine ⟨max 1 (B ^ r), by positivity, fun N φ a q hφ hq ha hα ↦ ?_⟩
  set P : ℝ := 1 / q + 1 / N + q / (N : ℝ) ^ (j + 1)
  have hP : 0 ≤ P := by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [show polyExpSum φ 0 = 0 by simp [polyExpSum], norm_zero]
    positivity
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hS : ‖polyExpSum φ N‖ ≤ N := by
    have h1 : ∀ x : ℝ, ‖exp (2 * Real.pi * I * x)‖ = 1 := fun x ↦ by
      rw [← expTwoPiI_def]; exact norm_expTwoPiI x
    refine (norm_sum_le _ _).trans ?_
    simp [h1]
  have hNε : (N : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
    conv_lhs => rw [← Real.rpow_one (N : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  -- the trivial range `q > N ^ k`
  by_cases hqN : (N : ℝ) ^ (j + 1) < q
  · have hP1 : 1 ≤ P := by
      have : 1 ≤ q / (N : ℝ) ^ (j + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
      have : 0 ≤ 1 / (q : ℝ) + 1 / N := by positivity
      linarith
    calc ‖polyExpSum φ N‖ ≤ 1 * (N : ℝ) ^ (1 + ε) * 1 := by linarith
      _ ≤ max 1 (B ^ r) * (N : ℝ) ^ (1 + ε) * P ^ r := by
          gcongr
          · exact le_max_left _ _
          · exact Real.one_le_rpow hP1 hr0
  push Not at hqN
  -- Weyl differencing, the divisor bound, and the type I bound
  set α := φ.coeff (j + 1)
  set W := weylSum N j (F * α)
  have h1 := hKw N N φ hN le_rfl hφ
  have h2 : W ≤ A * (N : ℝ) ^ δ * ∑ m ∈ Icc 1 (N ^ j), weylMin N (F * α * m) := hAw N _ hN
  have h3 := sum_weylMin_le hq ha hα N (N ^ j) (j + 1).factorial
    (Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  push_cast at h3
  set Lg := Real.log (2 * (F * (N : ℝ) ^ j) * q)
  have hNδ : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hNR hδ.le
  have hLg0 : 0 ≤ Lg := Real.log_nonneg (by
    have : 1 ≤ (N : ℝ) ^ j := one_le_pow₀ hNR
    nlinarith [mul_le_mul hF this zero_le_one (by linarith)])
  have hlogN : Real.log N ≤ (N : ℝ) ^ δ / δ := Real.log_le_rpow_div hN0.le hδ
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hLg : Lg ≤ (Real.log (2 * F) + 2 * (j + 1) / δ) * (N : ℝ) ^ δ := by
    have hq' : Real.log q ≤ (j + 1) * Real.log N := by
      calc Real.log q ≤ Real.log ((N : ℝ) ^ (j + 1)) := Real.log_le_log (by linarith) hqN
        _ = (j + 1) * Real.log N := by rw [Real.log_pow]; push_cast; ring
    have e : Lg = Real.log (2 * F) + j * Real.log N + Real.log q := by
      simp only [Lg]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_mul (by norm_num) (by positivity)]
      ring
    rw [e]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (2 * j + 1) * Real.log N ≤ 2 * (j + 1) * ((N : ℝ) ^ δ / δ) := by
      nlinarith
    have : Real.log (2 * F) ≤ Real.log (2 * F) * (N : ℝ) ^ δ := le_mul_of_one_le_right hlog2F hNδ
    have : 2 * (j + 1) * ((N : ℝ) ^ δ / δ) = 2 * (j + 1) / δ * (N : ℝ) ^ δ := by ring
    nlinarith
  have hWP : W / (N : ℝ) ^ (j + 1) ≤ 16 * A * F * (N : ℝ) ^ δ * Lg * P := by
    rw [div_le_iff₀ (by positivity)]
    refine h2.trans ?_
    calc A * (N : ℝ) ^ δ * ∑ m ∈ Icc 1 (N ^ j), weylMin N (F * α * m)
        ≤ A * (N : ℝ) ^ δ * (16 * (N * F * (N : ℝ) ^ j / q + F * (N : ℝ) ^ j + q) * Lg) := by
          gcongr
      _ ≤ 16 * A * F * (N : ℝ) ^ δ * Lg * P * (N : ℝ) ^ (j + 1) := by
          have e : 16 * A * F * (N : ℝ) ^ δ * Lg * P * (N : ℝ) ^ (j + 1) =
              A * (N : ℝ) ^ δ * (16 * (N * F * (N : ℝ) ^ j / q + F * (N : ℝ) ^ j +
                F * q) * Lg) := by
            simp only [P]; rw [pow_succ]; field_simp
          rw [e]
          gcongr
          nlinarith
  have h4 : (‖polyExpSum φ N‖ / N) ^ 2 ^ j ≤ B * (N : ℝ) ^ ε * P := by
    have h1N : 1 / (N : ℝ) ≤ P := by
      have : 0 ≤ 1 / (q : ℝ) + q / (N : ℝ) ^ (j + 1) := by positivity
      simp only [P]; linarith
    have hε2 : (N : ℝ) ^ ε = (N : ℝ) ^ δ * (N : ℝ) ^ δ := by
      rw [← Real.rpow_add hN0]; congr 1; simp only [δ]; ring
    refine h1.trans ?_
    calc K * (1 / N + W / (N : ℝ) ^ (j + 1))
        ≤ K * (P + 16 * A * F * (N : ℝ) ^ δ * Lg * P) := by gcongr
      _ = K * P * (1 + 16 * A * F * (N : ℝ) ^ δ * Lg) := by ring
      _ ≤ K * P * ((1 + 16 * A * F) * (D * (N : ℝ) ^ δ) * (N : ℝ) ^ δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hu : (0 : ℝ) ≤ (N : ℝ) ^ δ := by positivity
          have hLD : Lg ≤ D * (N : ℝ) ^ δ :=
            hLg.trans (mul_le_mul_of_nonneg_right (by simp only [D]; linarith) hu)
          have hD1 : 1 ≤ D := by
            have h0 : 0 ≤ 2 * (j + 1 : ℝ) / δ := by positivity
            simp only [D]; linarith
          have hDN : 1 ≤ D * (N : ℝ) ^ δ * (N : ℝ) ^ δ := by
            have : 1 ≤ D * (N : ℝ) ^ δ := one_le_mul_of_one_le_of_one_le hD1 hNδ
            exact this.trans (le_mul_of_one_le_right (by positivity) hNδ)
          have h16 : 0 ≤ 16 * A * F * (N : ℝ) ^ δ := by positivity
          calc 1 + 16 * A * F * (N : ℝ) ^ δ * Lg
              ≤ D * (N : ℝ) ^ δ * (N : ℝ) ^ δ + 16 * A * F * (N : ℝ) ^ δ * (D * (N : ℝ) ^ δ) :=
                add_le_add hDN (mul_le_mul_of_nonneg_left hLD h16)
            _ = (1 + 16 * A * F) * (D * (N : ℝ) ^ δ) * (N : ℝ) ^ δ := by ring
      _ = B * (N : ℝ) ^ ε * P := by rw [hε2]; simp only [B]; ring
  -- take the `2 ^ j`-th root
  have h5 : ‖polyExpSum φ N‖ / N ≤ B ^ r * (N : ℝ) ^ ε * P ^ r := by
    have e : ‖polyExpSum φ N‖ / N = ((‖polyExpSum φ N‖ / N) ^ 2 ^ j) ^ r := by
      simp only [r]
      rw [show ((2 : ℝ) ^ j) = ((2 ^ j : ℕ) : ℝ) by push_cast; rfl,
        Real.pow_rpow_inv_natCast (by positivity) (by positivity)]
    rw [e]
    calc ((‖polyExpSum φ N‖ / N) ^ 2 ^ j) ^ r ≤ (B * (N : ℝ) ^ ε * P) ^ r := by gcongr
      _ = B ^ r * ((N : ℝ) ^ ε) ^ r * P ^ r := by
          rw [Real.mul_rpow (by positivity) hP, Real.mul_rpow hB.le (by positivity)]
      _ ≤ B ^ r * (N : ℝ) ^ ε * P ^ r := by
          gcongr
          rw [← Real.rpow_mul hN0.le]
          exact Real.rpow_le_rpow_of_exponent_le hNR (mul_le_of_le_one_right hε.le hr1)
  calc ‖polyExpSum φ N‖ = N * (‖polyExpSum φ N‖ / N) := by field_simp
    _ ≤ N * (B ^ r * (N : ℝ) ^ ε * P ^ r) := by gcongr
    _ = B ^ r * (N * (N : ℝ) ^ ε) * P ^ r := by ring
    _ = B ^ r * (N : ℝ) ^ (1 + ε) * P ^ r := by
        rw [Real.rpow_add hN0, Real.rpow_one]
    _ ≤ max 1 (B ^ r) * (N : ℝ) ^ (1 + ε) * P ^ r := by gcongr; exact le_max_right _ _

end Polynomial
