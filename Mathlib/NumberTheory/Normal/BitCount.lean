/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.Normal.Algebraic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Algebraic irrationals have many ones in their binary expansion

Bailey, Borwein, Crandall and Pomerance proved that if `x` is an irrational algebraic number of
degree `d`, then for some `c > 0` and all large `N` there are at least `c * N ^ (1 / d)` ones
among the first `N` binary digits of `x`. `Mathlib.NumberTheory.Normal.SqrtTwo` treats `√2`. This
file treats all algebraic irrationals, and more generally counts the nonzero digits in any base
`b ≥ 2` (see Bugeaud's book [Bugeaud2012], §8).

## Proof

We describe base `2`; base `b` is the same with `1/2` replaced by `1/b` and the coefficients of `F`
being the digits rather than `0` or `1`. We follow §6–7 of the paper, with Liouville's zero-run
bound `Real.exists_zero_run_le` in place of the Thue–Siegel–Roth step (this only changes the
constant). Shift `x` into `[1, 2)` and let `P = ∑ A_d X ^ d` be an integer polynomial of degree `D`
with `P(x) = 0` and `A_D > 0`. For a fixed `N`, let `F = ∑_{p ∈ S} X ^ p ∈ ℕ[X]`, where `S ∋ 0` is
the set of positions of the ones among the first `N` binary digits, so that
`F(1/2) = ⌊x * 2 ^ N⌋ / 2 ^ N` and `s = F(1) = |S|`.

* For `R : ℕ` put `T(R) = ∑_d A_d ∑_{n > R} [Xⁿ] F ^ d / 2 ^ (n - R)`. Then
  `2 ^ R * P(F(1/2)) - T(R)` is an integer and `|P(F(1/2))| ≪ 2 ^ (-N)`, so `T(R)` is within
  `1/8` of an integer for `R ≤ N - c₀`.
* Since `∑_R ∑_{n > R} [Xⁿ] F ^ d / 2 ^ (n - R) ≤ F(1) ^ d`, at most `≪ s ^ D` values of `R` have
  `T(R) ≥ 3/4`.
* `T(R - 1) = (T(R) + ∑_d A_d [X^R] F ^ d) / 2`. Between consecutive points of the support of
  `F ^ (D - 1)` (there are at most `s ^ (D - 1)` of them) only the `d = D` term survives, so
  `T` stays `≥ 3/4` going leftwards from a point of the support of `F ^ D`, as long as the
  lower powers have no support slightly to the right. Liouville's bound places a point of the
  support of `F ^ D` a fixed fraction `1/D` into every gap, so `T(R) ≥ 3/4` for a proportion
  `1/D` of all `R ≤ N`, up to `O(s ^ D)`.

Hence `N ≤ E * s ^ D + c` for constants `E, c`.

## Main statements

* `Real.exists_le_mul_card_digit_eq_one_pow`: if `x` is an irrational root of a nonzero integer
  polynomial `f`, there are `E, c` with `N ≤ E * (#ones among the first N digits + 1) ^ deg f + c`.
* `Real.eventually_le_card_digit_eq_one`: the same, as `c * N ^ (1 / deg f) ≤ #ones` for large `N`.
* `Real.eventually_le_card_digit_eq_one_of_isAlgebraic`: the Bailey–Borwein–Crandall–Pomerance
  bound with `d` the degree of `x` over `ℚ`.
* `Real.exists_le_mul_card_digit_ne_zero_pow`, `Real.eventually_le_card_digit_ne_zero`,
  `Real.eventually_le_card_digit_ne_zero_of_isAlgebraic`: the same for the number of nonzero
  digits in any base `b ≥ 2`.

## References

* [D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance,
  *On the binary expansions of algebraic numbers*][baileyborweincrandallpomerance2004]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012], §8
-/

@[expose] public section

open Polynomial Filter Finset

namespace Real.BBCP

/-! ### Auxiliary lemmas for the proof -/

/-- The part `∑_{n > R} [Xⁿ] p / b ^ (n - R)` of `b ^ R * p(1/b)` beyond position `R`. -/
noncomputable def tail (b : ℕ) (p : ℕ[X]) (R : ℕ) : ℝ :=
  ∑ n ∈ range (p.natDegree + 1), if R < n then (p.coeff n : ℝ) / (b : ℝ) ^ (n - R) else 0

theorem tail_nonneg (b : ℕ) (p : ℕ[X]) (R : ℕ) : 0 ≤ tail b p R :=
  sum_nonneg fun n _ ↦ by split_ifs <;> positivity

/-- Moving the cut one position to the right. -/
theorem tail_eq (b : ℕ) (p : ℕ[X]) (R : ℕ) :
    tail b p R = ((p.coeff (R + 1) : ℝ) + tail b p (R + 1)) / b := by
  have h1 : (p.coeff (R + 1) : ℝ) =
      ∑ n ∈ range (p.natDegree + 1), if n = R + 1 then (p.coeff n : ℝ) else 0 := by
    rw [sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [coeff_eq_zero_of_natDegree_lt (by simp at h; omega)]; simp
  rw [tail, tail, h1, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun n _ ↦ ?_
  rcases lt_trichotomy n (R + 1) with h | rfl | h
  · have h1 : ¬ R < n := by omega
    have h2 : n ≠ R + 1 := by omega
    have h3 : ¬ R + 1 < n := by omega
    simp [h1, h2, h3]
  · simp
  · have h1 : R < n := by omega
    have h2 : n ≠ R + 1 := by omega
    simp only [h1, h2, h, ite_true, ite_false, zero_add]
    have : n - R = (n - (R + 1)) + 1 := by omega
    rw [this, pow_succ]; ring

/-- If `p` has no support in `(R, R + L]`, its tail at `R` is at most `p(1) / 2 ^ L`. -/
theorem tail_le {b : ℕ} (hb : 1 ≤ b) (p : ℕ[X]) (R L : ℕ)
    (h : ∀ n, R < n → n ≤ R + L → p.coeff n = 0) :
    tail b p R ≤ ((p.eval 1 : ℕ) : ℝ) / (b : ℝ) ^ L := by
  rw [tail, eval_eq_sum_range, Nat.cast_sum, sum_div]
  refine sum_le_sum fun n _ ↦ ?_
  simp only [one_pow, mul_one]
  split_ifs with hR
  · by_cases hn : n ≤ R + L
    · rw [h n hR hn]; simp
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by exact_mod_cast hb) (by omega))
  · positivity

/-- Each coefficient of `p` contributes less than `1` to the sum of all tails. -/
theorem sum_tail_le {b : ℕ} (hb : 2 ≤ b) (p : ℕ[X]) (M : ℕ) :
    ∑ R ∈ range M, tail b p R ≤ ((p.eval 1 : ℕ) : ℝ) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have key : ∀ n M : ℕ, ∑ R ∈ range M, (if R < n then (1 : ℝ) / (b : ℝ) ^ (n - R) else 0) ≤
      1 / (b : ℝ) ^ (n - M) := by
    intro n M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      split_ifs with h
      · have : n - M = (n - (M + 1)) + 1 := by omega
        rw [this, pow_succ] at ih ⊢
        have : (0 : ℝ) < (b : ℝ) ^ (n - (M + 1)) := by positivity
        have e : (1 : ℝ) / (b : ℝ) ^ (n - (M + 1)) = b / ((b : ℝ) ^ (n - (M + 1)) * b) := by
          field_simp
        have e2 : (1 : ℝ) / ((b : ℝ) ^ (n - (M + 1)) * b) + 1 / ((b : ℝ) ^ (n - (M + 1)) * b) =
            2 / ((b : ℝ) ^ (n - (M + 1)) * b) := by ring
        rw [e]
        calc _ ≤ (1 : ℝ) / ((b : ℝ) ^ (n - (M + 1)) * b) + 1 / ((b : ℝ) ^ (n - (M + 1)) * b) := by
              gcongr
          _ ≤ _ := by rw [e2]; gcongr
      · rw [show n - (M + 1) = 0 by omega]
        rw [show n - M = 0 by omega] at ih
        simpa using ih
  simp only [tail]
  rw [sum_comm, eval_eq_sum_range, Nat.cast_sum]
  refine sum_le_sum fun n _ ↦ ?_
  have e : ∑ R ∈ range M, (if R < n then (p.coeff n : ℝ) / (b : ℝ) ^ (n - R) else 0) =
      p.coeff n * ∑ R ∈ range M, (if R < n then (1 : ℝ) / (b : ℝ) ^ (n - R) else 0) := by
    rw [mul_sum]; refine sum_congr rfl fun R _ ↦ ?_; split_ifs <;> ring
  rw [e]
  push_cast
  rw [one_pow, mul_one]
  have h1 : (1 : ℝ) / (b : ℝ) ^ (n - M) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith)
  exact mul_le_of_le_one_right (by positivity) ((key n M).trans h1)

/-- `b ^ R * p(1/b)` is an integer plus the tail at `R`. -/
theorem exists_pow_mul_aeval {b : ℕ} (hb : 1 ≤ b) (p : ℕ[X]) (R : ℕ) :
    ∃ I : ℕ, (b : ℝ) ^ R * aeval (1 / b : ℝ) p = I + tail b p R := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  refine ⟨∑ n ∈ range (p.natDegree + 1), if n ≤ R then p.coeff n * b ^ (R - n) else 0, ?_⟩
  rw [aeval_eq_sum_range, mul_sum, tail, Nat.cast_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [nsmul_eq_mul]
  by_cases h : n ≤ R
  · have h' : ¬ R < n := by omega
    simp only [h, h', ite_true, ite_false, add_zero]
    have : (b : ℝ) ^ R = (b : ℝ) ^ (R - n) * (b : ℝ) ^ n := by rw [← pow_add]; congr 1; omega
    rw [this, one_div, inv_pow]; push_cast; field_simp
  · have h' : R < n := by omega
    simp only [h, h', ite_true, ite_false]
    have : (b : ℝ) ^ n = (b : ℝ) ^ (n - R) * (b : ℝ) ^ R := by rw [← pow_add]; congr 1; omega
    rw [one_div, inv_pow, this]; field_simp; simp

theorem le_coeff_mul (p q : ℕ[X]) (a j : ℕ) : p.coeff a * q.coeff j ≤ (p * q).coeff (a + j) := by
  rw [coeff_mul]
  exact single_le_sum (f := fun x ↦ p.coeff x.1 * q.coeff x.2) (fun _ _ ↦ Nat.zero_le _)
    (a := (a, j)) (mem_antidiagonal.2 rfl)

/-- If `F` has constant coefficient `1`, the coefficients of `F ^ d` grow with `d`. -/
theorem coeff_pow_mono {F : ℕ[X]} (h0 : F.coeff 0 = 1) {d e : ℕ} (hde : d ≤ e) (n : ℕ) :
    (F ^ d).coeff n ≤ (F ^ e).coeff n := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e _ ih =>
    refine ih.trans ?_
    have := le_coeff_mul (F ^ e) F n 0
    rwa [h0, mul_one, add_zero, ← pow_succ] at this

theorem card_support_le_eval_one (p : ℕ[X]) : #p.support ≤ p.eval 1 := by
  rw [eval_eq_sum, Polynomial.sum_def, card_eq_sum_ones]
  exact sum_le_sum fun n hn ↦ by
    simpa [Nat.one_le_iff_ne_zero] using mem_support_iff.1 hn

/-- Summing a lower bound over the gaps between consecutive points of `B`: if every gap
`[a, b)` starting at a point `a ∈ B` contains at least `(b - a - K) / D` points satisfying `P`,
then `[min B, M)` contains at least `(M - min B - K * #B) / D` such points. -/
theorem gap_count (P : ℕ → Prop) [DecidablePred P] (D K : ℕ) (B : Finset ℕ) :
    ∀ M, (∀ y ∈ B, y < M) →
    (∀ a ∈ B, ∀ b, b ≤ M → a < b → (∀ y ∈ B, y ≤ a ∨ b ≤ y) →
      b - a ≤ D * #{R ∈ Ico a b | P R} + K) →
    ∀ m ∈ B, (∀ y ∈ B, m ≤ y) → M - m ≤ D * #{R ∈ Ico m M | P R} + K * #B := by
  induction B using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    intro M hM hgap m hm hmin
    have haM : a < M := hM a (mem_insert_self _ _)
    have hgapa := hgap a (mem_insert_self a s) M le_rfl haM fun y hy ↦ by
      rcases mem_insert.1 hy with rfl | hy
      · exact Or.inl le_rfl
      · exact Or.inl (ha y hy).le
    rw [card_insert_of_notMem fun h ↦ lt_irrefl a (ha a h), mul_add_one]
    rcases mem_insert.1 hm with rfl | hms
    · omega
    · have hma : m ≤ a := (ha m hms).le
      have ih' := ih a ha (fun a' ha' b hb hab hsep ↦ hgap a' (mem_insert_of_mem ha') b
        (hb.trans haM.le) hab fun y hy ↦ by
          rcases mem_insert.1 hy with rfl | hy
          · exact Or.inr hb
          · exact hsep y hy) m hms fun y hy ↦ hmin y (mem_insert_of_mem hy)
      have hsplit : #{R ∈ Ico m M | P R} = #{R ∈ Ico m a | P R} + #{R ∈ Ico a M | P R} := by
        rw [← card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive m a M)),
          ← filter_union, Ico_union_Ico_eq_Ico hma haM.le]
      rw [hsplit, mul_add]
      omega

/-- The tail `T(R)` of the formal base-`b` expansion of `P(F(1/b))` beyond position `R`. -/
noncomputable def T (b : ℕ) (A : ℕ → ℤ) (D : ℕ) (F : ℕ[X]) (R : ℕ) : ℝ :=
  ∑ d ∈ range (D + 1), (A d : ℝ) * tail b (F ^ d) R

/-- The recursion `T(R) = (∑_d A_d [X^(R+1)] F ^ d + T(R + 1)) / b`. -/
theorem T_eq (b : ℕ) (A : ℕ → ℤ) (D : ℕ) (F : ℕ[X]) (R : ℕ) :
    T b A D F R = ((∑ d ∈ range (D + 1), (A d : ℝ) * ((F ^ d).coeff (R + 1) : ℝ)) +
      T b A D F (R + 1)) / b := by
  simp only [T]
  rw [← sum_add_distrib, Finset.sum_div]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [tail_eq]; ring

theorem sum_abs_T_le {b : ℕ} (hb : 2 ≤ b) (A : ℕ → ℤ) (D : ℕ) (F : ℕ[X]) (hs : 1 ≤ F.eval 1)
    (M : ℕ) : ∑ R ∈ range M, |T b A D F R| ≤
      ((∑ d ∈ range (D + 1), (A d).natAbs : ℕ) : ℝ) * ((F.eval 1 : ℕ) : ℝ) ^ D := by
  calc ∑ R ∈ range M, |T b A D F R|
      ≤ ∑ R ∈ range M, ∑ d ∈ range (D + 1), |(A d : ℝ)| * tail b (F ^ d) R := by
        refine sum_le_sum fun R _ ↦ (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine sum_congr rfl fun d _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (tail_nonneg _ _ _)]
    _ = ∑ d ∈ range (D + 1), |(A d : ℝ)| * ∑ R ∈ range M, tail b (F ^ d) R := by
        rw [sum_comm]; simp_rw [mul_sum]
    _ ≤ ∑ d ∈ range (D + 1), |(A d : ℝ)| * ((F.eval 1 : ℕ) : ℝ) ^ D := by
        refine sum_le_sum fun d hd ↦ mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (sum_tail_le hb _ _).trans ?_
        rw [eval_pow, Nat.cast_pow]
        exact pow_le_pow_right₀ (by exact_mod_cast hs) (by simpa [Nat.lt_succ_iff] using hd)
    _ = _ := by
        rw [← sum_mul]; push_cast; simp [Nat.cast_natAbs]

/-- The combinatorial core of the argument, for a fixed truncation `F` of the base-`b`
expansion. -/
theorem core {b : ℕ} (hb : 2 ≤ b) (D : ℕ) (hD : 1 ≤ D) (A : ℕ → ℤ) (hAD : 1 ≤ A D) (F : ℕ[X])
    (h0 : F.coeff 0 = 1)
    (C M : ℕ) (hwin : ∀ n, D * n + C ≤ M → ∃ j, n < j ∧ j ≤ D * n + C ∧ F.coeff j ≠ 0)
    (hnear : ∀ R ≤ M, ∃ z : ℤ, |T b A D F R - z| ≤ 1 / (4 * b)) :
    3 * M ≤ (4 * D * (∑ d ∈ range (D + 1), (A d).natAbs) +
      3 * (C + 2 + (∑ d ∈ range (D + 1), (A d).natAbs) + b + D) + 3 * D) * (F.eval 1) ^ D := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hε : (0 : ℝ) < 1 / (4 * b) := by positivity
  have hε' : (1 : ℝ) / (4 * b) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set Asum := ∑ d ∈ range (D + 1), (A d).natAbs with hAsum
  set s := F.eval 1 with hs_def
  have hs : 1 ≤ s := by
    rw [hs_def, eval_eq_sum_range]
    calc 1 = F.coeff 0 * 1 ^ 0 := by rw [h0]; rfl
      _ ≤ _ := single_le_sum (f := fun i ↦ F.coeff i * 1 ^ i) (fun _ _ ↦ Nat.zero_le _)
        (mem_range.2 (Nat.succ_pos _))
  set L := D * s + 2 + Asum + b with hL_def
  -- the lower powers contribute at most `1 / (4 * b)` to `T` once their support is `L` away
  have hL : ((Asum : ℕ) : ℝ) * ((s : ℕ) : ℝ) ^ D / (b : ℝ) ^ L ≤ 1 / (4 * b) := by
    have h1 : 4 * b * (Asum * s ^ D) ≤ b ^ L := by
      have e : 2 ^ L = 2 ^ 2 * 2 ^ b * (2 ^ Asum * (2 ^ s) ^ D) := by
        rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add, hL_def]; congr 1; ring
      refine le_trans ?_ (Nat.pow_le_pow_left hb L)
      rw [e]
      gcongr
      all_goals first | exact Nat.lt_two_pow_self.le | norm_num
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((4 * b * (Asum * s ^ D) : ℕ) : ℝ) ≤ ((b ^ L : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  -- near-integers above `1 / (2 * b)` are above `3/4`
  have hup : ∀ R ≤ M, 1 / (2 * b) ≤ T b A D F R → 3 / 4 ≤ T b A D F R := by
    intro R hR h
    obtain ⟨z, hz⟩ := hnear R hR
    rw [abs_le] at hz
    have h2 : (1 : ℝ) / (4 * b) < 1 / (2 * b) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    have : (0 : ℝ) < z := by linarith
    have : (1 : ℝ) ≤ z := by exact_mod_cast (show (0 : ℤ) < z by exact_mod_cast this)
    linarith
  -- propagation of `T ≥ 3/4` leftwards from a point of the support of `F ^ D`
  have hprop : ∀ R Q, R < Q → Q + L ≤ M → 1 ≤ (F ^ D).coeff Q →
      (∀ n, R < n → n ≤ Q + L → ∀ d < D, (F ^ d).coeff n = 0) → 3 / 4 ≤ T b A D F R := by
    intro R Q hRQ hQM hQ hclear
    have hS : ∀ n, R < n → n ≤ Q + L →
        ∑ d ∈ range (D + 1), (A d : ℝ) * ((F ^ d).coeff n : ℝ) = A D * ((F ^ D).coeff n : ℝ) := by
      intro n h1 h2
      rw [sum_range_succ, sum_eq_zero fun d hd ↦ by
        rw [hclear n h1 h2 d (mem_range.1 hd)]; simp, zero_add]
    have hTQ : -(1 / (4 * b)) ≤ T b A D F Q := by
      simp only [T]
      rw [sum_range_succ]
      have h1 : -(1 / (4 * b) : ℝ) ≤ ∑ d ∈ range D, (A d : ℝ) * tail b (F ^ d) Q := by
        have : ∀ d ∈ range D, -(((A d).natAbs : ℝ) * ((s : ℕ) : ℝ) ^ D / (b : ℝ) ^ L) ≤
            (A d : ℝ) * tail b (F ^ d) Q := by
          intro d hd
          have ht := tail_le (b := b) (by omega) (F ^ d) Q L fun n h1 h2 ↦
            hclear n (by omega) (by omega) d (mem_range.1 hd)
          rw [eval_pow, Nat.cast_pow] at ht
          have ht' : tail b (F ^ d) Q ≤ ((s : ℕ) : ℝ) ^ D / (b : ℝ) ^ L := ht.trans (by
            gcongr
            · exact_mod_cast hs
            · exact (mem_range.1 hd).le)
          have := neg_abs_le ((A d : ℝ) * tail b (F ^ d) Q)
          rw [abs_mul, abs_of_nonneg (tail_nonneg _ _ _),
            show |(A d : ℝ)| = ((A d).natAbs : ℝ) by rw [Nat.cast_natAbs, Int.cast_abs]] at this
          have h3 : ((A d).natAbs : ℝ) * tail b (F ^ d) Q ≤
              ((A d).natAbs : ℝ) * (((s : ℕ) : ℝ) ^ D / (b : ℝ) ^ L) :=
            mul_le_mul_of_nonneg_left ht' (by positivity)
          rw [mul_div_assoc]
          linarith
        refine le_trans ?_ (sum_le_sum this)
        rw [sum_neg_distrib, neg_le_neg_iff, ← Finset.sum_div, ← sum_mul]
        refine le_trans ?_ hL
        gcongr
        rw [hAsum]; push_cast
        exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.le_succ D))
          fun _ _ _ ↦ by positivity
      have h2 : 0 ≤ (A D : ℝ) * tail b (F ^ D) Q :=
        mul_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ A D by omega)) (tail_nonneg _ _ _)
      linarith
    have hAD' : (1 : ℝ) ≤ A D := by exact_mod_cast hAD
    have key : ∀ k R', R' + 1 + k = Q → R ≤ R' → 3 / 4 ≤ T b A D F R' := by
      intro k
      induction k with
      | zero =>
        intro R' hR' hRR'
        apply hup R' (by omega)
        rw [T_eq, hS (R' + 1) (by omega) (by omega), hR']
        have : (1 : ℝ) ≤ ((F ^ D).coeff Q : ℝ) := by exact_mod_cast hQ
        have : (1 : ℝ) ≤ A D * ((F ^ D).coeff Q : ℝ) := by nlinarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      | succ k ih =>
        intro R' hR' hRR'
        have h1 := ih (R' + 1) (by omega) (by omega)
        apply hup R' (by omega)
        rw [T_eq, hS (R' + 1) (by omega) (by omega)]
        have : (0 : ℝ) ≤ A D * ((F ^ D).coeff (R' + 1) : ℝ) := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    exact key (Q - R - 1) R (by omega) le_rfl
  -- the gaps between consecutive points of the support of `F ^ (D - 1)`
  set B := (F ^ (D - 1)).support.filter (· < M) with hB
  have hFD : F ^ D = F ^ (D - 1) * F := by rw [← pow_succ, Nat.sub_add_cancel hD]
  set K := C + L + D with hK
  have hgap : ∀ a ∈ B, ∀ e, e ≤ M → a < e → (∀ y ∈ B, y ≤ a ∨ e ≤ y) →
      e - a ≤ D * #{R ∈ Ico a e | 3 / 4 ≤ T b A D F R} + K := by
    intro a ha e hbM hab hsep
    rw [hB, mem_filter, mem_support_iff] at ha
    set q := (e - a - (C + L)) / D with hq
    have hq1 : D * q ≤ e - a - (C + L) := Nat.mul_div_le _ _
    have hq2 : e - a - (C + L) < D * (q + 1) := Nat.lt_mul_div_succ _ (by omega)
    have hq3 : q ≤ D * q := Nat.le_mul_of_pos_left q (by omega)
    have hsub : Ico a (a + q) ⊆ (Ico a e).filter fun R ↦ 3 / 4 ≤ T b A D F R := by
      intro R hR
      rw [mem_Ico] at hR
      have hR1 : D * (R - a + 1) ≤ D * q := Nat.mul_le_mul_left _ (by omega)
      rw [mul_add_one] at hR1
      rw [mem_filter, mem_Ico]
      refine ⟨⟨hR.1, by omega⟩, ?_⟩
      obtain ⟨j, hj1, hj2, hj⟩ := hwin (R - a) (by omega)
      refine hprop R (a + j) (by omega) (by omega) ?_ fun n h1 h2 d hd ↦ ?_
      · rw [hFD]
        exact (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.1 hj)).trans
          (le_coeff_mul _ _ a j)
      · by_contra hne
        have h3 := (coeff_pow_mono h0 (show d ≤ D - 1 by omega) n)
        have hnB : n ∈ B := by
          rw [hB, mem_filter, mem_support_iff]
          exact ⟨by omega, by omega⟩
        rcases hsep n hnB with h | h <;> omega
    have := card_le_card hsub
    rw [Nat.card_Ico, Nat.add_sub_cancel_left] at this
    rw [mul_add_one] at hq2
    have : D * q ≤ D * #{R ∈ Ico a e | 3 / 4 ≤ T b A D F R} := Nat.mul_le_mul_left _ this
    omega
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hM0]; simp
  have h0B : 0 ∈ B := by
    rw [hB, mem_filter, mem_support_iff, coeff_zero_eq_eval_zero, eval_pow,
      ← coeff_zero_eq_eval_zero, h0, one_pow]
    exact ⟨one_ne_zero, hMpos⟩
  have hcount := gap_count (fun R ↦ 3 / 4 ≤ T b A D F R) D K B M (fun y hy ↦ (mem_filter.1 hy).2)
    hgap 0 h0B fun _ _ ↦ Nat.zero_le _
  rw [Nat.sub_zero] at hcount
  have hBcard : #B ≤ s ^ (D - 1) :=
    (card_filter_le _ _).trans ((card_support_le_eval_one _).trans (by rw [eval_pow]))
  set g := #{R ∈ Ico 0 M | 3 / 4 ≤ T b A D F R} with hg_def
  have hg : 3 * g ≤ 4 * Asum * s ^ D := by
    have h1 : (g : ℝ) * (3 / 4) ≤
        ∑ R ∈ (Ico 0 M).filter (fun R ↦ 3 / 4 ≤ T b A D F R), T b A D F R := by
      have := card_nsmul_le_sum ((Ico 0 M).filter fun R ↦ 3 / 4 ≤ T b A D F R) (T b A D F) (3 / 4)
        fun R hR ↦ (mem_filter.1 hR).2
      rwa [nsmul_eq_mul] at this
    have h2 : ∑ R ∈ (Ico 0 M).filter (fun R ↦ 3 / 4 ≤ T b A D F R), T b A D F R ≤
        ∑ R ∈ range M, |T b A D F R| := by
      rw [range_eq_Ico]
      exact (sum_le_sum fun R _ ↦ le_abs_self _).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ abs_nonneg _)
    have h3 := sum_abs_T_le hb A D F hs M
    have : ((3 * g : ℕ) : ℝ) ≤ ((4 * Asum * s ^ D : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hsD : s ^ D = s * s ^ (D - 1) := by rw [← pow_succ']; congr 1; omega
  have ht : s ^ (D - 1) ≤ s ^ D := Nat.pow_le_pow_right hs (by omega)
  have h1 : K * #B ≤ K * s ^ (D - 1) := Nat.mul_le_mul_left _ hBcard
  have h2 : (C + 2 + Asum + b + D) * s ^ (D - 1) ≤ (C + 2 + Asum + b + D) * s ^ D :=
    Nat.mul_le_mul_left _ ht
  have h3 : D * (3 * g) ≤ D * (4 * Asum * s ^ D) := Nat.mul_le_mul_left _ hg
  have hK' : K * s ^ (D - 1) = (C + 2 + Asum + b + D) * s ^ (D - 1) + D * s ^ D := by
    rw [hK, hL_def, hsD]; ring
  nlinarith

/-- The truncation `1 + ∑_{p < N} digit p * X ^ (p + 1)` of the base-`b` expansion of `x`. -/
noncomputable def trunc (b : ℕ) (x : ℝ) (N : ℕ) : ℕ[X] :=
  1 + ∑ p ∈ range N, monomial (p + 1) (digit b x p)

theorem trunc_coeff_zero (b : ℕ) (x : ℝ) (N : ℕ) : (trunc b x N).coeff 0 = 1 := by
  rw [trunc, coeff_add, finsetSum_coeff, sum_eq_zero fun q _ ↦ coeff_monomial_of_ne _ (by omega),
    add_zero]
  simp

theorem trunc_coeff_succ (b : ℕ) (x : ℝ) {N p : ℕ} (hp : p < N) :
    (trunc b x N).coeff (p + 1) = digit b x p := by
  rw [trunc, coeff_add, finsetSum_coeff, sum_eq_single p (fun q _ hq ↦
    coeff_monomial_of_ne _ (by omega)) (fun h ↦ absurd (mem_range.2 hp) h), coeff_one,
    coeff_monomial_same]
  simp

/-- `F(1)` is at most `b` times one more than the number of nonzero digits among the first `N`. -/
theorem trunc_eval_one_le {b : ℕ} (hb : 1 ≤ b) (x : ℝ) (N : ℕ) :
    (trunc b x N).eval 1 ≤ b * (((range N).filter fun n ↦ digit b x n ≠ 0).card + 1) := by
  have h : ∑ n ∈ range N, digit b x n ≤ b * ((range N).filter fun n ↦ digit b x n ≠ 0).card := by
    rw [card_filter, mul_sum]
    refine sum_le_sum fun n _ ↦ ?_
    have := digit_lt (b := b) (by omega) x n
    split_ifs <;> omega
  simp only [trunc, eval_add, eval_one, eval_finsetSum, eval_monomial, one_pow, mul_one]
  rw [mul_add_one]
  omega

/-- For `x ∈ [1, 2)`, `F(1/b) = ⌊x * b ^ N⌋ / b ^ N`. -/
theorem aeval_trunc {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x < 2) (N : ℕ) :
    aeval (1 / b : ℝ) (trunc b x N) = ⌊x * (b : ℝ) ^ N⌋₊ / (b : ℝ) ^ N := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  induction N with
  | zero =>
    have : ⌊x⌋₊ = 1 :=
      Nat.floor_eq_iff (by linarith) |>.2 ⟨by simpa using hx1, by norm_num; linarith⟩
    simp [trunc, this]
  | succ N ih =>
    have htr : trunc b x (N + 1) = trunc b x N + monomial (N + 1) (digit b x N) := by
      simp only [trunc, sum_range_succ, add_assoc]
    have hdiv : ⌊x * (b : ℝ) ^ (N + 1)⌋₊ / b = ⌊x * (b : ℝ) ^ N⌋₊ := by
      rw [← Nat.floor_div_natCast]
      congr 1
      rw [pow_succ]
      field_simp
    have hdig : digit b x N = ⌊x * (b : ℝ) ^ (N + 1)⌋₊ % b := by
      rw [digit, ← Int.natCast_floor_eq_floor (by positivity), ← Int.natCast_mod,
        Int.toNat_natCast]
    have hfl : (⌊x * (b : ℝ) ^ (N + 1)⌋₊ : ℝ) = b * ⌊x * (b : ℝ) ^ N⌋₊ + digit b x N := by
      rw [← hdiv, hdig]
      exact_mod_cast (Nat.div_add_mod _ b).symm
    rw [htr, map_add, ih, aeval_monomial, hfl, eq_natCast (algebraMap ℕ ℝ), one_div, inv_pow]
    field_simp
    ring

/-- A polynomial vanishing at `x` is Lipschitz-small near `x` on `[1, 2]`. -/
theorem exists_abs_aeval_le {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) (f : ℤ[X]) (fx : aeval x f = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Set.Icc (1 : ℝ) 2, |aeval y f| ≤ K * |x - y| := by
  set g := f.map (algebraMap ℤ ℝ)
  have hg : ∀ y, aeval y f = g.eval y := fun y ↦ by rw [aeval_def, eval_map]
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun y ↦ g.derivative.eval y) (s := Set.Icc (1 : ℝ) 2)
    (Polynomial.continuous _).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun y hy ↦ ?_⟩
  have := (convex_Icc (1 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le
    (f := fun y ↦ g.eval y) (C := max K 0) (fun y _ ↦ g.differentiableAt)
    (fun y hy ↦ by rw [Polynomial.deriv]; exact (hK y hy).trans (le_max_left K 0)) hy hx
  rw [hg] at fx
  rw [hg]
  rwa [fx, zero_sub, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs] at this

/-- The theorem for `x ∈ [1, 2)` and a polynomial with positive leading coefficient. -/
theorem main_Ico {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x < 2) (hx : Irrational x)
    {f : ℤ[X]} (hD : 1 ≤ f.natDegree) (hlead : 1 ≤ f.leadingCoeff) (fx : aeval x f = 0) :
    ∃ E c : ℕ, ∀ N : ℕ,
      N ≤ E * (((range N).filter fun n ↦ digit b x n ≠ 0).card + 1) ^ f.natDegree + c := by
  set D := f.natDegree with hD_def
  have f0 : f ≠ 0 := by rintro rfl; simp [hD_def] at hD
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  obtain ⟨C0, hC0⟩ := exists_zero_run_le hb hx f0 fx
  rw [← hD_def] at hC0
  obtain ⟨K, hK0, hK⟩ := exists_abs_aeval_le ⟨hx1, hx2.le⟩ f fx
  set c0 := ⌈4 * b * K⌉₊ with hc0
  set Asum := ∑ d ∈ range (D + 1), (f.coeff d).natAbs
  set E := 4 * D * Asum + 3 * (C0 + 1 + 2 + Asum + b + D) + 3 * D
  refine ⟨E * b ^ D, c0, fun N ↦ ?_⟩
  set P := (((range N).filter fun n ↦ digit b x n ≠ 0).card + 1) ^ D
  by_cases hN : N < c0
  · omega
  have hcore := core hb D hD (fun d ↦ f.coeff d) hlead (trunc b x N) (trunc_coeff_zero b x N)
    (C0 + 1) (N - c0) ?_ ?_
  · have hs : (trunc b x N).eval 1 ^ D ≤ b ^ D * P := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (trunc_eval_one_le (by omega) x N) D
    have : 3 * (N - c0) ≤ E * (trunc b x N).eval 1 ^ D := hcore
    have : E * (trunc b x N).eval 1 ^ D ≤ E * b ^ D * P := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ hs
    omega
  · intro n hn
    by_contra! hall
    have hDn : n + (D - 1) * n = D * n := by
      have : D = (D - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    have := hC0 n ((D - 1) * n + C0 + 1) fun j hj ↦ by
      have h := hall (n + j + 1) (by omega) (by omega)
      rwa [trunc_coeff_succ b x (by omega)] at h
    omega
  · intro R hR
    set y := aeval (1 / b : ℝ) (trunc b x N) with hy_def
    have hy := aeval_trunc hb hx1 hx2 N
    rw [← hy_def] at hy
    have h2N : (0 : ℝ) < (b : ℝ) ^ N := by positivity
    have hfl1 : (⌊x * (b : ℝ) ^ N⌋₊ : ℝ) ≤ x * (b : ℝ) ^ N := Nat.floor_le (by positivity)
    have hfl2 : x * (b : ℝ) ^ N < ⌊x * (b : ℝ) ^ N⌋₊ + 1 := Nat.lt_floor_add_one _
    have hfl3 : (b : ℝ) ^ N ≤ ⌊x * (b : ℝ) ^ N⌋₊ := by
      have : ((b ^ N : ℕ) : ℝ) ≤ ⌊x * (b : ℝ) ^ N⌋₊ := by
        exact_mod_cast Nat.le_floor (by push_cast; nlinarith)
      exact_mod_cast this
    have hyx : y ≤ x := by rw [hy, div_le_iff₀ h2N]; exact hfl1
    have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ h2N]; linarith
    have hxy : |x - y| ≤ 1 / (b : ℝ) ^ N := by
      rw [abs_of_nonneg (by linarith), hy, sub_le_iff_le_add, ← add_div, le_div_iff₀ h2N]
      linarith
    choose I hI using fun d ↦ exists_pow_mul_aeval (b := b) (by omega) (trunc b x N ^ d) R
    refine ⟨-∑ d ∈ range (D + 1), f.coeff d * I d, ?_⟩
    have heq : T b (fun d ↦ f.coeff d) D (trunc b x N) R +
        ((∑ d ∈ range (D + 1), f.coeff d * I d : ℤ) : ℝ) = (b : ℝ) ^ R * aeval y f := by
      rw [aeval_eq_sum_range, mul_sum, T]
      push_cast
      rw [← sum_add_distrib]
      refine sum_congr rfl fun d _ ↦ ?_
      rw [zsmul_eq_mul, hy_def, ← map_pow, mul_left_comm, hI d]
      ring
    rw [Int.cast_neg, sub_neg_eq_add, heq, abs_mul, abs_of_pos (by positivity)]
    have hRN : R + c0 ≤ N := by omega
    have h4K : 4 * b * K ≤ (b : ℝ) ^ c0 := by
      calc 4 * b * K ≤ c0 := Nat.le_ceil _
        _ ≤ ((2 ^ c0 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self.le
        _ ≤ ((b ^ c0 : ℕ) : ℝ) := by exact_mod_cast Nat.pow_le_pow_left hb c0
        _ = _ := by push_cast; rfl
    have e : (b : ℝ) ^ N = (b : ℝ) ^ (N - R) * (b : ℝ) ^ R := by
      rw [← pow_add]; congr 1; omega
    calc (b : ℝ) ^ R * |aeval y f| ≤ (b : ℝ) ^ R * (K * (1 / (b : ℝ) ^ N)) := by
          gcongr
          exact (hK y ⟨hy1, by linarith⟩).trans (by gcongr)
      _ = K / (b : ℝ) ^ (N - R) := by rw [e]; field_simp
      _ ≤ K / (b : ℝ) ^ c0 := div_le_div_of_nonneg_left hK0 (by positivity)
          (pow_le_pow_right₀ (by linarith) (by omega))
      _ ≤ 1 / (4 * b) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith

end Real.BBCP

namespace Real

variable {x : ℝ}

/-- **Bailey–Borwein–Crandall–Pomerance in base `b`**, explicit form. If `x` is an irrational root
of a nonzero integer polynomial `f` and `b ≥ 2`, there are constants `E` and `c` such that for
every `N`, if `k` of the first `N` base-`b` digits of `x` are nonzero, then
`N ≤ E * (k + 1) ^ f.natDegree + c`. -/
theorem exists_le_mul_card_digit_ne_zero_pow {b : ℕ} (hb : 2 ≤ b) (hx : Irrational x) {f : ℤ[X]}
    (f0 : f ≠ 0) (fx : aeval x f = 0) : ∃ E c : ℕ, ∀ N : ℕ,
      N ≤ E * (((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card + 1) ^ f.natDegree + c := by
  have hD : 0 < f.natDegree := natDegree_pos_of_aeval_root f0 fx fun c hc ↦ by simpa using hc
  -- shift `x` into `[1, 2)`
  set k : ℤ := ⌊x⌋ - 1
  set y := x + ((-k : ℤ) : ℝ) with hy
  have hk : (k : ℝ) = ⌊x⌋ - 1 := by simp [k]
  have hy1 : 1 ≤ y := by rw [hy]; push_cast; linarith [Int.floor_le x]
  have hy2 : y < 2 := by rw [hy]; push_cast; linarith [Int.lt_floor_add_one x]
  set g := f.comp (X + C k)
  have gy : aeval y g = 0 := by
    rw [aeval_comp]; simpa [hy] using fx
  have hgD : g.natDegree = f.natDegree := by rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have g0 : g ≠ 0 := by rintro h; rw [h, natDegree_zero] at hgD; omega
  have hcount : ∀ N, ((Finset.range N).filter fun n ↦ digit b y n ≠ 0) =
      (Finset.range N).filter fun n ↦ digit b x n ≠ 0 := fun N ↦ by
    simp only [hy, digit_add_intCast]
  -- make the leading coefficient positive
  obtain ⟨g', hg'D, hg'l, hg'y⟩ : ∃ g' : ℤ[X], g'.natDegree = f.natDegree ∧
      1 ≤ g'.leadingCoeff ∧ aeval y g' = 0 := by
    have hl : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 g0
    rcases lt_or_gt_of_ne hl with h | h
    · exact ⟨-g, by rw [natDegree_neg, hgD], by rw [leadingCoeff_neg]; omega,
        by rw [map_neg, gy, neg_zero]⟩
    · exact ⟨g, hgD, h, gy⟩
  obtain ⟨E, c, h⟩ := BBCP.main_Ico hb hy1 hy2 (hx.add_intCast _) (by omega) hg'l hg'y
  refine ⟨E, c, fun N ↦ ?_⟩
  have := h N
  rwa [hcount, hg'D] at this

/-- **Bailey–Borwein–Crandall–Pomerance in base `b`.** If `x` is an irrational root of a nonzero
integer polynomial `f` of degree `d` and `b ≥ 2`, there is `c > 0` such that for all large `N` at
least `c * N ^ (1 / d)` of the first `N` base-`b` digits of `x` are nonzero. -/
theorem eventually_le_card_digit_ne_zero {b : ℕ} (hb : 2 ≤ b) (hx : Irrational x) {f : ℤ[X]}
    (f0 : f ≠ 0) (fx : aeval x f = 0) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (1 / (f.natDegree : ℝ)) ≤
        ((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card := by
  have hD : 0 < f.natDegree := natDegree_pos_of_aeval_root f0 fx fun c hc ↦ by simpa using hc
  obtain ⟨E, c, h⟩ := exists_le_mul_card_digit_ne_zero_pow hb hx f0 fx
  set D := f.natDegree
  set E' := E + 1
  have hE' : (0 : ℝ) < 2 * E' := by positivity
  refine ⟨1 / (2 * (2 * (E' : ℝ)) ^ (1 / (D : ℝ))), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * c + 2 * E' + 1)] with N hN
  set k := ((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card
  set P := (k + 1) ^ D with hP
  have h1 : N ≤ 2 * E' * P := by
    have h0 : N ≤ E * P + c := h N
    have : N ≤ 2 * (E * P) := by omega
    have e : 2 * E' * P = 2 * (E * P) + 2 * P := by simp only [E']; ring
    omega
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : P = 1 := by rw [hP, show k = 0 by omega, zero_add, one_pow]
    rw [this] at h1
    omega
  have h2 : (N : ℝ) / (2 * E') ≤ ((k + 1 : ℕ) : ℝ) ^ D := by
    rw [div_le_iff₀ hE']
    have : (N : ℝ) ≤ ((2 * E' * P : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hP] at this; push_cast at this ⊢; linarith
  have h3 := Real.rpow_le_rpow (by positivity) h2 (show (0 : ℝ) ≤ 1 / (D : ℝ) by positivity)
  rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega), ← one_div,
    Real.div_rpow (by positivity) hE'.le] at h3
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have h4 : (0 : ℝ) < (2 * E') ^ (1 / (D : ℝ)) := by positivity
  rw [div_le_iff₀ h4] at h3
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  push_cast at h3
  nlinarith

/-- **Bailey–Borwein–Crandall–Pomerance in base `b`.** If `x` is an irrational algebraic number of
degree `d` and `b ≥ 2`, there is `c > 0` such that for all large `N` at least `c * N ^ (1 / d)` of
the first `N` base-`b` digits of `x` are nonzero. -/
theorem eventually_le_card_digit_ne_zero_of_isAlgebraic {b : ℕ} (hb : 2 ≤ b)
    (halg : IsAlgebraic ℚ x) (hx : Irrational x) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (1 / ((minpoly ℚ x).natDegree : ℝ)) ≤
        ((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card := by
  set p := minpoly ℚ x
  set f := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p
  have fx : aeval x f = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ p (minpoly.aeval ℚ x)
  obtain ⟨m, hm, hfm⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  have hb0 : (m : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hm
  have hdeg : f.natDegree = p.natDegree := by
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ) f, hfm,
      zsmul_eq_mul, ← C_eq_intCast, natDegree_C_mul hb0]
  have hp : 0 < p.natDegree := minpoly.natDegree_pos halg.isIntegral
  have f0 : f ≠ 0 := by rintro h; rw [h, natDegree_zero] at hdeg; omega
  rw [← hdeg]
  exact eventually_le_card_digit_ne_zero hb hx f0 fx

/-- In base `2` the nonzero digits are the ones. -/
theorem filter_digit_two_eq_one (x : ℝ) (N : ℕ) :
    ((Finset.range N).filter fun n ↦ digit 2 x n = 1) =
      (Finset.range N).filter fun n ↦ digit 2 x n ≠ 0 := by
  refine Finset.filter_congr fun n _ ↦ ?_
  have := digit_lt (b := 2) (by norm_num) x n
  omega

/-- **Bailey–Borwein–Crandall–Pomerance**, explicit form. If `x` is an irrational root of a
nonzero integer polynomial `f`, there are constants `E` and `c` such that for every `N`, if `k`
ones occur among the first `N` binary digits of `x`, then `N ≤ E * (k + 1) ^ f.natDegree + c`. -/
theorem exists_le_mul_card_digit_eq_one_pow (hx : Irrational x) {f : ℤ[X]} (f0 : f ≠ 0)
    (fx : aeval x f = 0) : ∃ E c : ℕ, ∀ N : ℕ,
      N ≤ E * (((Finset.range N).filter fun n ↦ digit 2 x n = 1).card + 1) ^ f.natDegree + c := by
  simp_rw [filter_digit_two_eq_one]
  exact exists_le_mul_card_digit_ne_zero_pow le_rfl hx f0 fx

/-- **Bailey–Borwein–Crandall–Pomerance.** If `x` is an irrational root of a nonzero integer
polynomial `f` of degree `d`, then there is `c > 0` such that for all large `N` at least
`c * N ^ (1 / d)` of the first `N` binary digits of `x` are ones. -/
theorem eventually_le_card_digit_eq_one (hx : Irrational x) {f : ℤ[X]} (f0 : f ≠ 0)
    (fx : aeval x f = 0) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (1 / (f.natDegree : ℝ)) ≤
        ((Finset.range N).filter fun n ↦ digit 2 x n = 1).card := by
  simp_rw [filter_digit_two_eq_one]
  exact eventually_le_card_digit_ne_zero le_rfl hx f0 fx

/-- **Bailey–Borwein–Crandall–Pomerance.** If `x` is an irrational algebraic number of degree `d`,
then there is `c > 0` such that for all large `N` at least `c * N ^ (1 / d)` of the first `N`
binary digits of `x` are ones. -/
theorem eventually_le_card_digit_eq_one_of_isAlgebraic (halg : IsAlgebraic ℚ x)
    (hx : Irrational x) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (1 / ((minpoly ℚ x).natDegree : ℝ)) ≤
        ((Finset.range N).filter fun n ↦ digit 2 x n = 1).card := by
  simp_rw [filter_digit_two_eq_one]
  exact eventually_le_card_digit_ne_zero_of_isAlgebraic le_rfl halg hx

end Real
