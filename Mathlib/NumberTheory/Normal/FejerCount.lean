/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Counting points in a short interval with Fejér squares

For a real sequence `x` and `K > 0`, the number of `n < L` with `x n - c ∈ [0, 1 / K)` modulo one
is at most `8 L / K + (16 / K) ∑_{1 ≤ h < K} |∑_{n < L} e(h x n)|`,
where `e(t) = exp(2 π i t)`.

This is the quantitative form of Weyl's criterion used by Davenport–Erdős: the indicator of a
short interval is dominated by the Fejér square `(2 / K²) |∑_{j < K} e(j t)|²`, which is a
trigonometric polynomial of degree `< K`.

## Main statements

* `Complex.card_fract_sub_lt_le`: the counting bound above.

## References

* [H. Davenport, P. Erdős, *Note on normal decimals*][DavenportErdos1952]
-/

@[expose] public section

open Finset
open scoped Real

namespace Complex

/-- The additive character `e(t) = exp(2 π i t)` of `ℝ / ℤ`, as a complex number. -/
noncomputable def cexpTwoPi (t : ℝ) : ℂ := exp (2 * π * I * t)

theorem cexpTwoPi_add (s t : ℝ) : cexpTwoPi (s + t) = cexpTwoPi s * cexpTwoPi t := by
  simp only [cexpTwoPi, ofReal_add, mul_add, exp_add]

theorem cexpTwoPi_intCast (m : ℤ) : cexpTwoPi m = 1 := by
  rw [cexpTwoPi, show 2 * (π : ℂ) * I * ((m : ℝ) : ℂ) = m * (2 * π * I) by push_cast; ring,
    exp_int_mul_two_pi_mul_I]

theorem norm_cexpTwoPi (t : ℝ) : ‖cexpTwoPi t‖ = 1 := by
  rw [cexpTwoPi, show 2 * (π : ℂ) * I * t = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I]

theorem conj_cexpTwoPi (t : ℝ) : starRingEnd ℂ (cexpTwoPi t) = cexpTwoPi (-t) := by
  rw [cexpTwoPi, cexpTwoPi, ← exp_conj]; congr 1
  simp only [map_mul, map_ofNat, conj_ofReal, conj_I, ofReal_neg]; ring

theorem cexpTwoPi_re (t : ℝ) : (cexpTwoPi t).re = Real.cos (2 * π * t) := by
  rw [cexpTwoPi, show 2 * (π : ℂ) * I * t = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring,
    exp_ofReal_mul_I_re]

theorem le_norm_sum_cexpTwoPi_sq {K : ℕ} {t : ℝ} (ht : |t| ≤ 1 / (8 * K)) :
    (K : ℝ) ^ 2 / 2 ≤ ‖∑ j ∈ range K, cexpTwoPi (j * t)‖ ^ 2 := by
  have hcos : ∀ j ∈ range K, Real.sqrt 2 / 2 ≤ Real.cos (2 * π * (j * t)) := fun j hj ↦ by
    have hj : (j : ℝ) < K := by exact_mod_cast mem_range.1 hj
    rw [← Real.cos_pi_div_four, ← Real.cos_abs (2 * π * (j * t))]
    have hK : (0 : ℝ) < K := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have h1 : |2 * π * (j * t)| ≤ π / 4 := by
      simp only [abs_mul, abs_two, abs_of_pos Real.pi_pos, Nat.abs_cast]
      calc 2 * π * (j * |t|) ≤ 2 * π * (K * (1 / (8 * K))) := by gcongr
        _ = π / 4 := by field_simp; ring
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h1
  have hre : (K : ℝ) * (Real.sqrt 2 / 2) ≤ (∑ j ∈ range K, cexpTwoPi (j * t)).re := by
    rw [re_sum]
    calc (K : ℝ) * (Real.sqrt 2 / 2) = ∑ _j ∈ range K, Real.sqrt 2 / 2 := by simp
      _ ≤ _ := sum_le_sum fun j hj ↦ (hcos j hj).trans (le_of_eq (cexpTwoPi_re _).symm)
  have h0 : 0 ≤ (K : ℝ) * (Real.sqrt 2 / 2) := by positivity
  have := (pow_le_pow_left₀ h0 (hre.trans (re_le_norm _)) 2)
  calc (K : ℝ) ^ 2 / 2 = ((K : ℝ) * (Real.sqrt 2 / 2)) ^ 2 := by
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]; ring
    _ ≤ _ := this

theorem norm_sum_cexpTwoPi_sq_eq_re (K : ℕ) (u : ℝ) :
    ‖∑ j ∈ range K, cexpTwoPi (j * u)‖ ^ 2 =
      (∑ j ∈ range K, ∑ j' ∈ range K, cexpTwoPi ((j - j') * u)).re := by
  rw [Complex.sq_norm, ← ofReal_re (normSq _), ← mul_conj, map_sum, sum_mul_sum]
  congr 1
  refine sum_congr rfl fun j _ ↦ sum_congr rfl fun j' _ ↦ ?_
  rw [conj_cexpTwoPi, ← cexpTwoPi_add]; congr 1; ring

/-- The Weyl sum `∑_{n < L} e(h x_n)`. -/
noncomputable def weylSum (x : ℕ → ℝ) (L : ℕ) (h : ℤ) : ℂ :=
  ∑ n ∈ range L, cexpTwoPi (h * x n)

theorem norm_weylSum_neg (x : ℕ → ℝ) (L : ℕ) (h : ℤ) :
    ‖weylSum x L (-h)‖ = ‖weylSum x L h‖ := by
  rw [← Complex.norm_conj (weylSum x L h), weylSum, weylSum, map_sum]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  rw [conj_cexpTwoPi]; push_cast; ring_nf

theorem norm_weylSum_le (x : ℕ → ℝ) (L : ℕ) (h : ℤ) : ‖weylSum x L h‖ ≤ L :=
  (norm_sum_le _ _).trans (by simp [norm_cexpTwoPi])

theorem sum_norm_sum_cexpTwoPi_sq_le (x : ℕ → ℝ) (L K : ℕ) (d : ℝ) :
    ∑ n ∈ range L, ‖∑ j ∈ range K, cexpTwoPi (j * (x n - d))‖ ^ 2 ≤
      ∑ j ∈ range K, ∑ j' ∈ range K, ‖weylSum x L ((j : ℤ) - j')‖ := by
  simp only [norm_sum_cexpTwoPi_sq_eq_re]
  rw [← re_sum, sum_comm]
  refine (re_le_norm _).trans ((norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_))
  rw [sum_comm]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j' _ ↦ ?_)
  have : ∑ n ∈ range L, cexpTwoPi (((j : ℝ) - j') * (x n - d)) =
      cexpTwoPi (-(((j : ℝ) - j') * d)) * weylSum x L ((j : ℤ) - j') := by
    rw [weylSum, mul_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [← cexpTwoPi_add]; push_cast; ring_nf
  rw [this, norm_mul, norm_cexpTwoPi, one_mul]

theorem sum_norm_weylSum_sub_le (x : ℕ → ℝ) (L : ℕ) {K j : ℕ} (hj : j < K) :
    ∑ j' ∈ range K, ‖weylSum x L ((j : ℤ) - j')‖ ≤
      L + 2 * ∑ h ∈ Ico 1 K, ‖weylSum x L h‖ := by
  classical
  have hsplit : range K = ((range K).filter (· < j)) ∪ {j} ∪ ((range K).filter (j < ·)) := by
    ext j'; simp only [mem_union, mem_filter, mem_range, mem_singleton]; omega
  rw [hsplit, sum_union, sum_union, sum_singleton]
  · set f : ℕ → ℝ := fun h ↦ ‖weylSum x L h‖
    have h1 : ∑ j' ∈ (range K).filter (· < j), ‖weylSum x L ((j : ℤ) - j')‖ ≤
        ∑ h ∈ Ico 1 K, f h := by
      calc ∑ j' ∈ (range K).filter (· < j), ‖weylSum x L ((j : ℤ) - j')‖
          = ∑ j' ∈ (range K).filter (· < j), f (j - j') := sum_congr rfl fun j' hj' ↦ by
            simp only [mem_filter, mem_range] at hj'
            simp only [f]; push_cast [hj'.2.le]; rfl
        _ = ∑ h ∈ ((range K).filter (· < j)).image (j - ·), f h := by
            rw [sum_image]
            intro a ha a' ha' e
            simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha ha'
            simp only at e; omega
        _ ≤ ∑ h ∈ Ico 1 K, f h := by
            refine sum_le_sum_of_subset_of_nonneg (fun h hh ↦ ?_) fun _ _ _ ↦ norm_nonneg _
            obtain ⟨j', hj', rfl⟩ := mem_image.1 hh
            simp only [mem_filter, mem_range] at hj'
            simp only [mem_Ico]; omega
    have h2 : ∑ j' ∈ (range K).filter (j < ·), ‖weylSum x L ((j : ℤ) - j')‖ ≤
        ∑ h ∈ Ico 1 K, f h := by
      calc ∑ j' ∈ (range K).filter (j < ·), ‖weylSum x L ((j : ℤ) - j')‖
          = ∑ j' ∈ (range K).filter (j < ·), f (j' - j) := sum_congr rfl fun j' hj' ↦ by
            simp only [mem_filter, mem_range] at hj'
            simp only [f]; rw [← norm_weylSum_neg]; push_cast [hj'.2.le]; ring_nf
        _ = ∑ h ∈ ((range K).filter (j < ·)).image (· - j), f h := by
            rw [sum_image]
            intro a ha a' ha' e
            simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha ha'
            simp only at e; omega
        _ ≤ ∑ h ∈ Ico 1 K, f h := by
            refine sum_le_sum_of_subset_of_nonneg (fun h hh ↦ ?_) fun _ _ _ ↦ norm_nonneg _
            obtain ⟨j', hj', rfl⟩ := mem_image.1 hh
            simp only [mem_filter, mem_range] at hj'
            simp only [mem_Ico]; omega
    have h0 : ‖weylSum x L ((j : ℤ) - j)‖ ≤ L := norm_weylSum_le x L _
    linarith
  · rw [disjoint_singleton_right]; simp
  · rw [disjoint_union_left, disjoint_singleton_left]
    refine ⟨?_, by simp⟩
    rw [disjoint_filter]; intro a _ h1 h2; omega

/-- **Counting with Fejér squares**: the number of `n < L` with `x n - c ∈ [0, 1/K) mod 1` is
at most `8 L / K` plus the Weyl sums of `x` with frequencies `1 ≤ h < K`. -/
theorem card_fract_sub_lt_le (x : ℕ → ℝ) (c : ℝ) {K : ℕ} (hK : 0 < K) (L : ℕ) :
    (((range L).filter fun n ↦ Int.fract (x n - c) < 1 / K).card : ℝ) ≤
      8 * L / K + 16 / K * ∑ h ∈ Ico 1 K, ‖weylSum x L h‖ := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set d : ℕ → ℝ := fun i ↦ c + (2 * i + 1) / (8 * K)
  set F : ℕ → ℝ := fun n ↦ ∑ i ∈ range 4, 2 / (K : ℝ) ^ 2 *
    ‖∑ j ∈ range K, cexpTwoPi (j * (x n - d i))‖ ^ 2
  have hF0 : ∀ n, 0 ≤ F n := fun n ↦ sum_nonneg fun _ _ ↦ by positivity
  have hpt : ∀ n, Int.fract (x n - c) < 1 / K → 1 ≤ F n := by
    intro n hn
    set y := Int.fract (x n - c)
    have hy0 : 0 ≤ y := Int.fract_nonneg _
    set i := ⌊4 * K * y⌋₊
    have hi4 : i < 4 := by
      refine (Nat.floor_lt (by positivity)).2 ?_
      calc 4 * (K : ℝ) * y < 4 * K * (1 / K) := by gcongr
        _ = 4 := by field_simp
    have hi1 : (i : ℝ) ≤ 4 * K * y := Nat.floor_le (by positivity)
    have hi2 : 4 * K * y < i + 1 := Nat.lt_floor_add_one _
    set t := y - (2 * i + 1) / (8 * K)
    have ht : |t| ≤ 1 / (8 * K) := by
      have e : t = (8 * K * y - (2 * i + 1)) / (8 * K) := by simp only [t]; field_simp
      rw [abs_le, e]; constructor
      · rw [neg_div', div_le_div_iff_of_pos_right (by positivity)]; linarith
      · rw [div_le_div_iff_of_pos_right (by positivity)]; linarith
    have he : ∑ j ∈ range K, cexpTwoPi (j * (x n - d i)) =
        ∑ j ∈ range K, cexpTwoPi (j * t) := by
      refine sum_congr rfl fun j _ ↦ ?_
      have : (j : ℝ) * (x n - d i) = j * t + ((j * ⌊x n - c⌋ : ℤ) : ℝ) := by
        simp only [d, t, y, Int.fract]; push_cast; ring
      rw [this, cexpTwoPi_add, cexpTwoPi_intCast, mul_one]
    have hsq := le_norm_sum_cexpTwoPi_sq ht
    calc (1 : ℝ) = 2 / (K : ℝ) ^ 2 * ((K : ℝ) ^ 2 / 2) := by field_simp
      _ ≤ 2 / (K : ℝ) ^ 2 * ‖∑ j ∈ range K, cexpTwoPi (j * (x n - d i))‖ ^ 2 := by
        rw [he]; gcongr
      _ ≤ F n := single_le_sum (f := fun i ↦ 2 / (K : ℝ) ^ 2 *
            ‖∑ j ∈ range K, cexpTwoPi (j * (x n - d i))‖ ^ 2) (fun _ _ ↦ by positivity)
            (mem_range.2 hi4)
  set W := ∑ h ∈ Ico 1 K, ‖weylSum x L h‖
  have hW : ∀ i, ∑ n ∈ range L, ‖∑ j ∈ range K, cexpTwoPi (j * (x n - d i))‖ ^ 2 ≤
      K * (L + 2 * W) :=
    fun i ↦ (sum_norm_sum_cexpTwoPi_sq_le x L K (d i)).trans <| (sum_le_sum fun j hj ↦
      sum_norm_weylSum_sub_le x L (mem_range.1 hj)).trans
        (le_of_eq (by rw [sum_const, card_range, nsmul_eq_mul]))
  calc (((range L).filter fun n ↦ Int.fract (x n - c) < 1 / K).card : ℝ)
      = ∑ n ∈ (range L).filter fun n ↦ Int.fract (x n - c) < 1 / K, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ (range L).filter fun n ↦ Int.fract (x n - c) < 1 / K, F n :=
        sum_le_sum fun n hn ↦ hpt n (mem_filter.1 hn).2
    _ ≤ ∑ n ∈ range L, F n := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun n _ _ ↦ hF0 n
    _ = ∑ i ∈ range 4, 2 / (K : ℝ) ^ 2 *
          ∑ n ∈ range L, ‖∑ j ∈ range K, cexpTwoPi (j * (x n - d i))‖ ^ 2 := by
        simp only [F]; rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ _i ∈ range 4, 2 / (K : ℝ) ^ 2 * (K * (L + 2 * W)) :=
        sum_le_sum fun i _ ↦ by gcongr; exact hW i
    _ = 8 * L / K + 16 / K * W := by
        rw [sum_const, card_range, nsmul_eq_mul]; field_simp [hK'.ne']; ring

end Complex
