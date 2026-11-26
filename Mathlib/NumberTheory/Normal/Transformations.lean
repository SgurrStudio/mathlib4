/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Normal.Borel
import Mathlib.NumberTheory.Normal.Rational
import Mathlib.NumberTheory.Normal.Weyl

/-!
# Invariance and non-invariance of normality under transformations

This file establishes both positive invariance theorems and sharp obstructions for operations on
normal numbers:

* **Rational affine invariance for absolute normality** (Wall 1949): `x ↦ q * x + r` (`q ∈ ℚ×`,
  `r ∈ ℚ`) preserves `Real.IsAbsolutelyNormal`.
* **Cesàro-zero / sparse-digit translations** (Aistleitner 2011; explicit subgroup of Rauzy 1976):
  translating `x` by any `y` whose fractional orbits `Int.fract (y * b ^ n)` have Cesàro mean `0`
  — in particular any `y` whose nonzero base-`b` digits have asymptotic density `0`, or
  Mathlib's `liouvilleNumber b` — preserves `Real.IsNormalIn b`.
* **Rotational rigidity in `ℝ²`**: rotating `(x, y)` by angle `θ` preserves coordinatewise base-`b`
  normality (or absolute normality) for all normal pairs `(x, y)` if and only if
  `sin θ = 0 ∨ cos θ = 0` (i.e., `θ` is a multiple of `π / 2`).
* **Universal normal decompositions**: every real number is the sum of two absolutely normal
  numbers, and every nonzero real number is the product of two absolutely normal numbers.

## Main statements

* `Real.isAbsolutelyNormal_mul_add_ratCast_iff`: `q * x + r` is absolutely normal iff `x` is.
* `Real.isNormalIn_add_iff_of_tendsto_cesaro_fract`: Cesàro-zero fractional-orbit translations
  preserve base-`b` normality.
* `Real.isNormalIn_add_iff_of_density_zero`: **Aistleitner (2011)**, translations by numbers with
  density-`0` nonzero base-`b` digits preserve base-`b` normality.
* `Real.isNormalIn_add_liouvilleNumber_iff`: adding `liouvilleNumber b` preserves base-`b`
  normality.
* `Real.rotation_preserves_isNormalIn_iff`, `Real.rotation_preserves_isAbsolutelyNormal_iff`:
  exact characterization of normality-preserving planar rotations.
* `Real.exists_isAbsolutelyNormal_add_eq`, `Real.exists_isAbsolutelyNormal_mul_eq`:
  every real (resp. nonzero real) is a sum (resp. product) of two absolutely normal numbers.

## References

* D. D. Wall, *Normal numbers*, PhD thesis, University of California, Berkeley, 1949.
* G. Rauzy, *Nombres normaux et processus déterministes*, Acta Arith. 29 (1976), 211–225.
* C. Aistleitner, *Normal numbers and the digits of their sums*,
  Unif. Distrib. Theory 6 (2011), no. 2, 49–58.
-/

@[expose] public section

open Filter MeasureTheory Topology

namespace Real

/-! ### Rational affine invariance for absolute normality -/

/-- Negation preserves absolute normality. -/
theorem IsAbsolutelyNormal.neg {x : ℝ} (h : IsAbsolutelyNormal x) : IsAbsolutelyNormal (-x) :=
  fun b hb ↦ (h b hb).neg hb

/-- Multiplying by a nonzero rational preserves absolute normality. -/
theorem IsAbsolutelyNormal.mul_ratCast {x : ℝ} (h : IsAbsolutelyNormal x) {q : ℚ} (hq : q ≠ 0) :
    IsAbsolutelyNormal (q * x) := fun b hb ↦ by
  rw [mul_comm]
  exact (h b hb).mul_ratCast hb hq

/-- Adding a rational preserves absolute normality. -/
theorem IsAbsolutelyNormal.add_ratCast {x : ℝ} (h : IsAbsolutelyNormal x) (r : ℚ) :
    IsAbsolutelyNormal (x + r) :=
  fun b hb ↦ (h b hb).add_ratCast hb r

/-- **Wall (1949)** for absolute normality: `q * x + r` is absolutely normal iff `x` is, for
every nonzero rational `q` and rational `r`. -/
theorem isAbsolutelyNormal_mul_add_ratCast_iff {x : ℝ} {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    IsAbsolutelyNormal (q * x + r) ↔ IsAbsolutelyNormal x :=
  ⟨fun h b hb ↦ (isNormalIn_mul_add_ratCast_iff hb hq r).1 (h b hb),
    fun h b hb ↦ (isNormalIn_mul_add_ratCast_iff hb hq r).2 (h b hb)⟩

/-! ### Cesàro-zero and sparse-digit translations -/

private theorem norm_cexp_sub_one_le (h : ℤ) (t : ℝ) :
    ‖Complex.exp (2 * π * Complex.I * (h : ℂ) * (t : ℂ)) - 1‖ ≤
      2 * π * |(h : ℝ)| * Int.fract t := by
  have hper : Complex.exp (2 * π * Complex.I * (h : ℂ) * (t : ℂ)) =
      Complex.exp (2 * π * Complex.I * (h : ℂ) * ((Int.fract t : ℝ) : ℂ)) := by
    have ht : (t : ℂ) = (Int.fract t : ℝ) + (⌊t⌋ : ℤ) := by
      exact_mod_cast (Int.fract_add_floor t).symm
    rw [ht, mul_add, Complex.exp_add]
    have hint : Complex.exp (2 * π * Complex.I * (h : ℂ) * (⌊t⌋ : ℤ)) = 1 := by
      have : (2 : ℂ) * π * Complex.I * (h : ℂ) * (⌊t⌋ : ℤ) =
          ((h * ⌊t⌋ : ℤ) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [hint, mul_one]
  rw [hper]
  set θ : ℝ := 2 * π * (h : ℝ) * Int.fract t
  have hθ : (2 : ℂ) * π * Complex.I * (h : ℂ) * ((Int.fract t : ℝ) : ℂ) =
      (θ : ℂ) * Complex.I := by
    simp only [θ]; push_cast; ring
  rw [hθ]
  have h1 : Complex.exp ((θ : ℂ) * Complex.I) - 1 =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
        (2 * Complex.I * Complex.sin ((θ / 2 : ℝ) : ℂ)) := by
    rw [Complex.sin]
    have hmul : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hsq : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hsin : 2 * Complex.I *
        ((Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I)) -
          Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) * Complex.I / 2) =
        Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I)) := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [neg_mul, hsin, mul_sub, hsq, hmul]
  rw [h1, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_ofNat, Complex.norm_I, mul_one, ← Complex.ofReal_sin, Complex.norm_real,
    Real.norm_eq_abs]
  calc 2 * |Real.sin (θ / 2)|
      ≤ 2 * |θ / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |θ| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
    _ = 2 * π * |(h : ℝ)| * Int.fract t := by
        simp only [θ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
          abs_of_nonneg (Int.fract_nonneg t)]

/-- If the fractional parts `Int.fract (y * b ^ n)` have Cesàro mean `0`, then translating by `y`
preserves base-`b` normality. -/
theorem isNormalIn_add_iff_of_tendsto_cesaro_fract {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hy : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, Int.fract (y * (b : ℝ) ^ n)) / N)
      atTop (𝓝 0)) :
    IsNormalIn b (x + y) ↔ IsNormalIn b x := by
  have hdiff : ∀ h : ℤ, Tendsto (fun N : ℕ ↦
      (∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * h * (((x + y : ℝ) : ℂ) * (b : ℝ) ^ n))) / N -
      (∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n))) / N)
      atTop (𝓝 0) := by
    intro h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_)
      (by simpa using hy.const_mul (2 * π * |(h : ℝ)|))
    rw [← sub_div, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast]
    calc ‖∑ n ∈ Finset.range N,
            (Complex.exp (2 * π * Complex.I * h * (((x + y : ℝ) : ℂ) * (b : ℝ) ^ n)) -
              Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n)))‖ / N
        ≤ (∑ n ∈ Finset.range N,
            ‖Complex.exp (2 * π * Complex.I * h * (((x + y : ℝ) : ℂ) * (b : ℝ) ^ n)) -
              Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n))‖) / N := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (∑ n ∈ Finset.range N, 2 * π * |(h : ℝ)| * Int.fract (y * (b : ℝ) ^ n)) / N := by
          gcongr with n _
          have hfac : Complex.exp (2 * π * Complex.I * h * (((x + y : ℝ) : ℂ) * (b : ℝ) ^ n)) -
              Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n)) =
              Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n)) *
                (Complex.exp (2 * π * Complex.I * h * ((y * (b : ℝ) ^ n : ℝ) : ℂ)) - 1) := by
            rw [mul_sub, mul_one, ← Complex.exp_add]
            congr 2; push_cast; ring
          have hu : ‖Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n))‖ = 1 := by
            rw [show (2 : ℂ) * π * Complex.I * h * (x * (b : ℝ) ^ n) =
                ((2 * π * (h : ℝ) * (x * (b : ℝ) ^ n) : ℝ) : ℂ) * Complex.I by push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          rw [hfac, norm_mul, hu, one_mul]
          exact norm_cexp_sub_one_le h (y * (b : ℝ) ^ n)
      _ = 2 * π * |(h : ℝ)| * ((∑ n ∈ Finset.range N, Int.fract (y * (b : ℝ) ^ n)) / N) := by
          rw [← Finset.mul_sum, mul_div_assoc]
  rw [isNormalIn_iff_tendsto_weylSum hb, isNormalIn_iff_tendsto_weylSum hb]
  constructor
  · intro hxy h hh
    have := (hxy h hh).sub (hdiff h)
    simpa only [sub_zero, sub_sub_cancel] using this
  · intro hx h hh
    have := (hdiff h).add (hx h hh)
    simpa only [zero_add, sub_add_cancel] using this

private theorem fract_lt_inv_pow_of_forall_digit_eq_zero {b : ℕ} (hb : 0 < b) (z : ℝ) (K : ℕ)
    (hz : ∀ j < K, digit b z j = 0) : Int.fract z < ((b : ℝ) ^ K)⁻¹ := by
  induction K with
  | zero => simpa using Int.fract_lt_one z
  | succ K ih =>
    have hK : Int.fract z < ((b : ℝ) ^ K)⁻¹ := ih fun j hj ↦ hz j (Nat.lt_succ_of_lt hj)
    have h0 : 0 ≤ Int.fract z * (b : ℝ) ^ (K + 1) :=
      mul_nonneg (Int.fract_nonneg z) (by positivity)
    have hlt : Int.fract z * (b : ℝ) ^ (K + 1) < b := by
      have h1 : Int.fract z * (b : ℝ) ^ K < 1 := by
        rw [← one_div, lt_div_iff₀ (by positivity)] at hK
        exact hK
      rw [pow_succ]
      nlinarith [show (0 : ℝ) < b by positivity]
    have hfl_lt : ⌊Int.fract z * (b : ℝ) ^ (K + 1)⌋₊ < b :=
      (Nat.floor_lt h0).2 hlt
    have hdig : ⌊Int.fract z * (b : ℝ) ^ (K + 1)⌋₊ % b = 0 := by
      have := hz K (Nat.lt_succ_self K)
      rw [← digit_fract, digit_eq_floor_mod (Int.fract_nonneg z)] at this
      exact this
    rw [Nat.mod_eq_of_lt hfl_lt] at hdig
    have h1 : Int.fract z * (b : ℝ) ^ (K + 1) < 1 := by
      have := Nat.lt_floor_add_one (Int.fract z * (b : ℝ) ^ (K + 1))
      rw [hdig, Nat.cast_zero, zero_add] at this
      exact this
    rw [← one_div, lt_div_iff₀ (by positivity)]
    exact h1

/-- **Aistleitner (2011)** (special case of Rauzy 1976): if the nonzero base-`b` digits of `y`
have asymptotic density `0`, then adding `y` preserves base-`b` normality. -/
theorem isNormalIn_add_iff_of_density_zero {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hy : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun n ↦ digit b y n ≠ 0).card : ℝ) / N)
      atTop (𝓝 0)) :
    IsNormalIn b (x + y) ↔ IsNormalIn b x := by
  refine isNormalIn_add_iff_of_tendsto_cesaro_fract hb ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (half_pos hε)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < b) : (1 : ℝ) < b))
  have hK' : ((b : ℝ) ^ K)⁻¹ < ε / 2 := by rwa [inv_pow] at hK
  have hshift : Tendsto (fun N : ℕ ↦
      (K : ℝ) * ((((Finset.range (N + K)).filter fun m ↦ digit b y m ≠ 0).card : ℝ) / N))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ ↦
        (((Finset.range (N + K)).filter fun m ↦ digit b y m ≠ 0).card : ℝ) / (N + K : ℕ))
        atTop (𝓝 0) := (tendsto_add_atTop_iff_nat K).2 hy
    have h2 : Tendsto (fun N : ℕ ↦ ((N + K : ℕ) : ℝ) / N) atTop (𝓝 1) := by
      have h0 : Tendsto (fun N : ℕ ↦ (1 : ℝ) + (K : ℝ) / N) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
      rw [add_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
      push_cast; field_simp [hNr]
    have h3 : Tendsto (fun N : ℕ ↦
        (K : ℝ) * (((((Finset.range (N + K)).filter fun m ↦ digit b y m ≠ 0).card : ℝ) /
          (N + K : ℕ)) * (((N + K : ℕ) : ℝ) / N))) atTop (𝓝 ((K : ℝ) * (0 * 1))) :=
      (h1.mul h2).const_mul (K : ℝ)
    simp only [zero_mul, mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNK : ((N + K : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hNK]
  rw [Metric.tendsto_atTop] at hshift
  obtain ⟨N₀, hN₀⟩ := hshift (ε / 2) (half_pos hε)
  refine ⟨max N₀ 1, fun N hN ↦ ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hsum_nonneg : 0 ≤ (∑ n ∈ Finset.range N, Int.fract (y * (b : ℝ) ^ n)) / N :=
    div_nonneg (Finset.sum_nonneg fun _ _ ↦ Int.fract_nonneg _) (Nat.cast_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nonneg]
  classical
  set B : Finset ℕ := (Finset.range N).filter fun n ↦ ∃ j < K, digit b y (n + j) ≠ 0
  set G : Finset ℕ := (Finset.range N).filter fun n ↦ ¬∃ j < K, digit b y (n + j) ≠ 0
  have hBcard : B.card ≤ K * ((Finset.range (N + K)).filter fun m ↦ digit b y m ≠ 0).card := by
    set S : Finset ℕ := (Finset.range (N + K)).filter fun m ↦ digit b y m ≠ 0
    have hsub : B ⊆ S.biUnion fun m ↦ (Finset.range K).image fun j ↦ m - j := by
      intro n hn
      simp only [B, Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨j, hj, hdig⟩ := hn.2
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, S, Finset.mem_filter]
      exact ⟨n + j, ⟨by omega, hdig⟩, j, hj, by omega⟩
    calc B.card ≤ (S.biUnion fun m ↦ (Finset.range K).image fun j ↦ m - j).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ m ∈ S, ((Finset.range K).image fun j ↦ m - j).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ S, K := Finset.sum_le_sum fun _ _ ↦
          Finset.card_image_le.trans (by simp)
      _ = K * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsplit : ∑ n ∈ Finset.range N, Int.fract (y * (b : ℝ) ^ n) =
      (∑ n ∈ B, Int.fract (y * (b : ℝ) ^ n)) + ∑ n ∈ G, Int.fract (y * (b : ℝ) ^ n) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range N) _ _).symm
  have hBle : ∑ n ∈ B, Int.fract (y * (b : ℝ) ^ n) ≤ B.card := by
    calc ∑ n ∈ B, Int.fract (y * (b : ℝ) ^ n)
        ≤ ∑ _n ∈ B, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦ (Int.fract_lt_one _).le
      _ = B.card := by simp
  have hGle : ∑ n ∈ G, Int.fract (y * (b : ℝ) ^ n) ≤ (N : ℝ) * ((b : ℝ) ^ K)⁻¹ := by
    calc ∑ n ∈ G, Int.fract (y * (b : ℝ) ^ n)
        ≤ ∑ _n ∈ G, ((b : ℝ) ^ K)⁻¹ := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          simp only [G, Finset.mem_filter, Finset.mem_range] at hn
          have hzero : ∀ j < K, digit b (y * (b : ℝ) ^ n) j = 0 := by
            intro j hj
            rw [← digit_add]
            by_contra hne
            exact hn.2 ⟨j, hj, hne⟩
          exact (fract_lt_inv_pow_of_forall_digit_eq_zero (by omega) (y * (b : ℝ) ^ n) K hzero).le
      _ = (G.card : ℝ) * ((b : ℝ) ^ K)⁻¹ := by simp
      _ ≤ (N : ℝ) * ((b : ℝ) ^ K)⁻¹ := by
          gcongr
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hBdiv : (B.card : ℝ) / N < ε / 2 := by
    have hlt := hN₀ N hN0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
    calc (B.card : ℝ) / N
        ≤ (K : ℝ) * ((((Finset.range (N + K)).filter fun m ↦ digit b y m ≠ 0).card : ℝ) / N) := by
          rw [← mul_div_assoc]
          gcongr
          exact_mod_cast hBcard
      _ < ε / 2 := hlt
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN1
  rw [hsplit, add_div]
  have h1 : (∑ n ∈ B, Int.fract (y * (b : ℝ) ^ n)) / N < ε / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right hBle hNr.le) hBdiv
  have h2 : (∑ n ∈ G, Int.fract (y * (b : ℝ) ^ n)) / N < ε / 2 := by
    calc (∑ n ∈ G, Int.fract (y * (b : ℝ) ^ n)) / N
        ≤ (N : ℝ) * ((b : ℝ) ^ K)⁻¹ / N := div_le_div_of_nonneg_right hGle hNr.le
      _ = ((b : ℝ) ^ K)⁻¹ := mul_div_cancel_left₀ _ hNr.ne'
      _ < ε / 2 := hK'
  linarith

private theorem add_le_factorial_add {m : ℕ} (hm : 1 ≤ m) (d : ℕ) :
    m.factorial + d ≤ (m + d).factorial := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show m + (d + 1) = (m + d) + 1 by omega, Nat.factorial_succ]
    have h1 : 1 ≤ (m + d).factorial := Nat.factorial_pos _
    nlinarith

private theorem sq_le_factorial {i : ℕ} (hi : 4 ≤ i) : i ^ 2 ≤ i.factorial := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hi
  clear hi
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by omega, Nat.factorial_succ]
    nlinarith

private theorem fract_liouvilleNumber_mul_pow_le {b : ℕ} (hb : 2 ≤ b) {n K : ℕ} (hK : 2 ≤ K)
    (hgap : ∀ i : ℕ, i.factorial ≤ n ∨ n + K ≤ i.factorial) :
    Int.fract (liouvilleNumber b * (b : ℝ) ^ n) ≤ 2 * ((b : ℝ) ^ K)⁻¹ := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hs := LiouvilleNumber.summable hb1
  have hex : ∃ m : ℕ, n < m.factorial := ⟨n + 1, by
    have := Nat.self_le_factorial (n + 1); omega⟩
  classical
  set m : ℕ := Nat.find hex
  have hm_gt : n < m.factorial := Nat.find_spec hex
  have hm_le : ∀ i < m, i.factorial ≤ n := fun i hi ↦ not_lt.1 (Nat.find_min hex hi)
  have hm_gap : n + K ≤ m.factorial := (hgap m).resolve_left (not_le.2 hm_gt)
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have : m = 0 := by omega
    rw [this, Nat.factorial_zero] at hm_gap
    omega
  have hsplit : liouvilleNumber b * (b : ℝ) ^ n =
      (∑ i ∈ Finset.range m, (b : ℝ) ^ (n - i.factorial)) +
        ∑' d : ℕ, 1 / (b : ℝ) ^ (m + d).factorial * (b : ℝ) ^ n := by
    rw [liouvilleNumber, ← hs.sum_add_tsum_nat_add m, add_mul, Finset.sum_mul, ← tsum_mul_right]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hle : i.factorial ≤ n := hm_le i (Finset.mem_range.1 hi)
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      rw [one_div, show (b : ℝ) ^ n = (b : ℝ) ^ (n - i.factorial) * (b : ℝ) ^ i.factorial by
        rw [← pow_add, Nat.sub_add_cancel hle]]
      field_simp [hb0]
    · congr 1
      ext d
      rw [add_comm d m]
  set T : ℝ := ∑' d : ℕ, 1 / (b : ℝ) ^ (m + d).factorial * (b : ℝ) ^ n
  have hT_nonneg : 0 ≤ T := tsum_nonneg fun _ ↦ by positivity
  have hT_le : T ≤ 2 * ((b : ℝ) ^ K)⁻¹ := by
    have hs_tail : Summable fun d : ℕ ↦ 1 / (b : ℝ) ^ (m + d).factorial * (b : ℝ) ^ n := by
      have h1 := ((summable_nat_add_iff m).2 hs).mul_right ((b : ℝ) ^ n)
      exact h1.congr fun d ↦ by rw [add_comm]
    have hgeom : Summable fun d : ℕ ↦ ((b : ℝ) ^ K)⁻¹ * (1 / 2 : ℝ) ^ d :=
      summable_geometric_two.mul_left _
    have hterm : ∀ d : ℕ, 1 / (b : ℝ) ^ (m + d).factorial * (b : ℝ) ^ n ≤
        ((b : ℝ) ^ K)⁻¹ * (1 / 2 : ℝ) ^ d := by
      intro d
      have hfd : n + K + d ≤ (m + d).factorial := (Nat.add_le_add_right hm_gap d).trans
        (add_le_factorial_add hm1 d)
      have hpow : (b : ℝ) ^ (n + K + d) ≤ (b : ℝ) ^ (m + d).factorial :=
        pow_le_pow_right₀ (by linarith) hfd
      have h2d : (2 : ℝ) ^ d ≤ (b : ℝ) ^ d :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb) d
      have hmul : (b : ℝ) ^ n * (b : ℝ) ^ K * (2 : ℝ) ^ d ≤ (b : ℝ) ^ (m + d).factorial := by
        calc (b : ℝ) ^ n * (b : ℝ) ^ K * (2 : ℝ) ^ d
            ≤ (b : ℝ) ^ n * (b : ℝ) ^ K * (b : ℝ) ^ d := by gcongr
          _ = (b : ℝ) ^ (n + K + d) := by rw [← pow_add, ← pow_add]
          _ ≤ (b : ℝ) ^ (m + d).factorial := hpow
      rw [one_div, one_div, inv_pow, ← mul_inv, mul_comm _ ((b : ℝ) ^ n), ← div_eq_mul_inv,
        div_le_iff₀ (by positivity)]
      calc (b : ℝ) ^ n = (b : ℝ) ^ n * ((b : ℝ) ^ K * (2 : ℝ) ^ d) *
            ((b : ℝ) ^ K * (2 : ℝ) ^ d)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
        _ ≤ (b : ℝ) ^ (m + d).factorial * ((b : ℝ) ^ K * (2 : ℝ) ^ d)⁻¹ := by
              gcongr; linarith [mul_assoc ((b : ℝ) ^ n) ((b : ℝ) ^ K) ((2 : ℝ) ^ d)]
        _ = ((b : ℝ) ^ K * (2 : ℝ) ^ d)⁻¹ * (b : ℝ) ^ (m + d).factorial := mul_comm _ _
    calc T ≤ ∑' d : ℕ, ((b : ℝ) ^ K)⁻¹ * (1 / 2 : ℝ) ^ d :=
          hs_tail.tsum_le_tsum hterm hgeom
      _ = ((b : ℝ) ^ K)⁻¹ * ∑' d : ℕ, (1 / 2 : ℝ) ^ d := tsum_mul_left
      _ = 2 * ((b : ℝ) ^ K)⁻¹ := by rw [tsum_geometric_two]; ring
  have hT_lt_one : T < 1 := by
    have h4 : (4 : ℝ) ≤ (b : ℝ) ^ K := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hK
        _ ≤ (b : ℝ) ^ K := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb) K
    have : 2 * ((b : ℝ) ^ K)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hM : ∑ i ∈ Finset.range m, (b : ℝ) ^ (n - i.factorial) =
      ((∑ i ∈ Finset.range m, b ^ (n - i.factorial) : ℕ) : ℝ) := by push_cast; rfl
  rw [hsplit, hM, show (((∑ i ∈ Finset.range m, b ^ (n - i.factorial) : ℕ) : ℝ)) =
      (((∑ i ∈ Finset.range m, b ^ (n - i.factorial) : ℕ) : ℤ) : ℝ) by push_cast; rfl,
    add_comm, Int.fract_add_intCast, Int.fract_eq_self.2 ⟨hT_nonneg, hT_lt_one⟩]
  exact hT_le

/-- Translating by Liouville's constant `liouvilleNumber b` preserves base-`b` normality,
exhibiting an explicit transcendental rotation in Rauzy's invariance group. -/
theorem isNormalIn_add_liouvilleNumber_iff {b : ℕ} (hb : 2 ≤ b) (x : ℝ) :
    IsNormalIn b (x + liouvilleNumber b) ↔ IsNormalIn b x := by
  refine isNormalIn_add_iff_of_tendsto_cesaro_fract hb ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 4 by linarith)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < b) : (1 : ℝ) < b))
  set K : ℕ := max K₀ 2
  have hK2 : 2 ≤ K := le_max_right _ _
  have hKb : 2 * ((b : ℝ) ^ K)⁻¹ < ε / 2 := by
    have h1 : ((b : ℝ) ^ K)⁻¹ ≤ ((b : ℝ) ^ K₀)⁻¹ := by
      rw [← inv_pow, ← inv_pow]
      exact pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ b))) (le_max_left _ _)
    rw [inv_pow] at hK₀
    linarith
  have hsqrt : Tendsto (fun N : ℕ ↦ (K : ℝ) * (Real.sqrt (N + K : ℕ) + 4) / N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ (K : ℝ) * (Real.sqrt (1 + (K : ℝ) / N) / Real.sqrt N +
        4 / N)) atTop (𝓝 ((K : ℝ) * (Real.sqrt (1 + 0) * 0 + 0))) := by
      have ha : Tendsto (fun N : ℕ ↦ Real.sqrt (1 + (K : ℝ) / N)) atTop (𝓝 (Real.sqrt (1 + 0))) :=
        (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))).sqrt
      have hb_inv : Tendsto (fun N : ℕ ↦ (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      have hc : Tendsto (fun N : ℕ ↦ (4 : ℝ) / N) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 4
      simpa only [div_eq_mul_inv] using ((ha.mul hb_inv).add hc).const_mul (K : ℝ)
    simp only [add_zero, mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have hsq : Real.sqrt (N + K : ℕ) = Real.sqrt N * Real.sqrt (1 + (K : ℝ) / N) := by
      rw [← Real.sqrt_mul hNr.le]
      congr 1
      push_cast
      field_simp [hNr.ne']
    rw [hsq]
    have hsn : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
    have hsq2 : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNr.le
    have hdiv : Real.sqrt (1 + (K : ℝ) / N) / Real.sqrt N =
        Real.sqrt N * Real.sqrt (1 + (K : ℝ) / N) / N := by
      rw [div_eq_div_iff hsn hNr.ne']
      calc Real.sqrt (1 + (K : ℝ) / N) * (N : ℝ)
          = Real.sqrt (1 + (K : ℝ) / N) * (Real.sqrt N * Real.sqrt N) := by rw [hsq2]
        _ = Real.sqrt N * Real.sqrt (1 + (K : ℝ) / N) * Real.sqrt N := by ring
    rw [hdiv, ← add_div, mul_div_assoc]
  rw [Metric.tendsto_atTop] at hsqrt
  obtain ⟨N₀, hN₀⟩ := hsqrt (ε / 2) (half_pos hε)
  refine ⟨max N₀ 1, fun N hN ↦ ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN1
  have hsum_nonneg : 0 ≤ (∑ n ∈ Finset.range N, Int.fract (liouvilleNumber b * (b : ℝ) ^ n)) / N :=
    div_nonneg (Finset.sum_nonneg fun _ _ ↦ Int.fract_nonneg _) hNr.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nonneg]
  classical
  set G : Finset ℕ := (Finset.range N).filter fun n ↦ ∀ i : ℕ, i.factorial ≤ n ∨ n + K ≤ i.factorial
  set B : Finset ℕ := (Finset.range N).filter fun n ↦
    ¬∀ i : ℕ, i.factorial ≤ n ∨ n + K ≤ i.factorial
  have hBcard : B.card ≤ K * (Nat.sqrt (N + K) + 4) := by
    have hsub : B ⊆ (Finset.range (Nat.sqrt (N + K) + 4)).biUnion fun i ↦
        (Finset.range K).image fun j ↦ i.factorial - j := by
      intro n hn
      simp only [B, Finset.mem_filter, Finset.mem_range] at hn
      push Not at hn
      obtain ⟨i, hi1, hi2⟩ := hn.2
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
      have hilt : i < Nat.sqrt (N + K) + 4 := by
        by_cases h4 : i < 4
        · omega
        · have hsq : i ^ 2 < N + K := lt_of_le_of_lt (sq_le_factorial (by omega)) (by omega)
          have hle : i ≤ Nat.sqrt (N + K) := Nat.le_sqrt.2 (by nlinarith)
          omega
      exact ⟨i, hilt, i.factorial - n, by omega, by omega⟩
    calc B.card ≤ ((Finset.range (Nat.sqrt (N + K) + 4)).biUnion fun i ↦
            (Finset.range K).image fun j ↦ i.factorial - j).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Finset.range (Nat.sqrt (N + K) + 4),
            ((Finset.range K).image fun j ↦ i.factorial - j).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Finset.range (Nat.sqrt (N + K) + 4), K :=
            Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le.trans (by simp)
      _ = K * (Nat.sqrt (N + K) + 4) := by simp [mul_comm]
  have hsplit : ∑ n ∈ Finset.range N, Int.fract (liouvilleNumber b * (b : ℝ) ^ n) =
      (∑ n ∈ B, Int.fract (liouvilleNumber b * (b : ℝ) ^ n)) +
        ∑ n ∈ G, Int.fract (liouvilleNumber b * (b : ℝ) ^ n) := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range N) _ _).symm
  have hBle : ∑ n ∈ B, Int.fract (liouvilleNumber b * (b : ℝ) ^ n) ≤ B.card := by
    calc ∑ n ∈ B, Int.fract (liouvilleNumber b * (b : ℝ) ^ n)
        ≤ ∑ _n ∈ B, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦ (Int.fract_lt_one _).le
      _ = B.card := by simp
  have hGle : ∑ n ∈ G, Int.fract (liouvilleNumber b * (b : ℝ) ^ n) ≤
      (N : ℝ) * (2 * ((b : ℝ) ^ K)⁻¹) := by
    calc ∑ n ∈ G, Int.fract (liouvilleNumber b * (b : ℝ) ^ n)
        ≤ ∑ _n ∈ G, (2 * ((b : ℝ) ^ K)⁻¹) := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          simp only [G, Finset.mem_filter] at hn
          exact fract_liouvilleNumber_mul_pow_le hb hK2 hn.2
      _ = (G.card : ℝ) * (2 * ((b : ℝ) ^ K)⁻¹) := by simp
      _ ≤ (N : ℝ) * (2 * ((b : ℝ) ^ K)⁻¹) := by
          gcongr
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hnat_sqrt : (Nat.sqrt (N + K) : ℝ) ≤ Real.sqrt (N + K : ℕ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _), sq]
    exact_mod_cast Nat.sqrt_le (N + K)
  have hBdiv : (B.card : ℝ) / N < ε / 2 := by
    have hlt := hN₀ N hN0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
    calc (B.card : ℝ) / N
        ≤ (K : ℝ) * ((Nat.sqrt (N + K) : ℝ) + 4) / N := by
          gcongr
          exact_mod_cast hBcard
      _ ≤ (K : ℝ) * (Real.sqrt (N + K : ℕ) + 4) / N := by gcongr
      _ < ε / 2 := hlt
  rw [hsplit, add_div]
  have h1 : (∑ n ∈ B, Int.fract (liouvilleNumber b * (b : ℝ) ^ n)) / N < ε / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right hBle hNr.le) hBdiv
  have h2 : (∑ n ∈ G, Int.fract (liouvilleNumber b * (b : ℝ) ^ n)) / N < ε / 2 := by
    calc (∑ n ∈ G, Int.fract (liouvilleNumber b * (b : ℝ) ^ n)) / N
        ≤ (N : ℝ) * (2 * ((b : ℝ) ^ K)⁻¹) / N := div_le_div_of_nonneg_right hGle hNr.le
      _ = 2 * ((b : ℝ) ^ K)⁻¹ := mul_div_cancel_left₀ _ hNr.ne'
      _ < ε / 2 := hKb
  linarith

/-! ### Rotational rigidity in `ℝ²` and universal normal decompositions -/

/-- **Rotational rigidity in `ℝ²`** (base `b`): rotating `(x, y)` by angle `θ` preserves
coordinatewise base-`b` normality for all base-`b` normal pairs `(x, y)` if and only if
`sin θ = 0 ∨ cos θ = 0`. -/
theorem rotation_preserves_isNormalIn_iff {b : ℕ} (hb : 2 ≤ b) (θ : ℝ) :
    (∀ x y : ℝ, IsNormalIn b x → IsNormalIn b y →
      IsNormalIn b (x * cos θ - y * sin θ) ∧ IsNormalIn b (x * sin θ + y * cos θ)) ↔
      sin θ = 0 ∨ cos θ = 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hc : cos θ / sin θ ≠ 0 := div_ne_zero hne.2 hne.1
    have hae : ∀ᵐ x : ℝ, IsAbsolutelyNormal x ∧ IsAbsolutelyNormal (x * (cos θ / sin θ)) :=
      ae_isAbsolutelyNormal.and (ae_mul_of_ae hc ae_isAbsolutelyNormal)
    obtain ⟨x, hx, hcx⟩ := hae.exists
    have h0 := (h x (x * (cos θ / sin θ)) (hx b hb) (hcx b hb)).1
    have hzero : x * cos θ - x * (cos θ / sin θ) * sin θ = 0 := by
      field_simp [hne.1]; ring
    rw [hzero] at h0
    exact (h0.irrational hb) ⟨0, by simp⟩
  · rintro (hsin | hcos) x y hx hy
    · have hcos2 : cos θ = 1 ∨ cos θ = -1 := by
        have := sin_sq_add_cos_sq θ
        rw [hsin, zero_pow two_ne_zero, zero_add, sq_eq_one_iff] at this
        exact this
      rcases hcos2 with hc | hc <;> simp [hsin, hc, hx, hy, hx.neg hb, hy.neg hb]
    · have hsin2 : sin θ = 1 ∨ sin θ = -1 := by
        have := sin_sq_add_cos_sq θ
        rw [hcos, zero_pow two_ne_zero, add_zero, sq_eq_one_iff] at this
        exact this
      rcases hsin2 with hs | hs <;> simp [hcos, hs, hx, hy, hx.neg hb, hy.neg hb]

/-- **Rotational rigidity in `ℝ²`** (absolute normality): rotating `(x, y)` by angle `θ`
preserves coordinatewise absolute normality for all absolutely normal pairs `(x, y)` if and only
if `sin θ = 0 ∨ cos θ = 0`. -/
theorem rotation_preserves_isAbsolutelyNormal_iff (θ : ℝ) :
    (∀ x y : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal y →
      IsAbsolutelyNormal (x * cos θ - y * sin θ) ∧
      IsAbsolutelyNormal (x * sin θ + y * cos θ)) ↔
      sin θ = 0 ∨ cos θ = 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hc : cos θ / sin θ ≠ 0 := div_ne_zero hne.2 hne.1
    have hae : ∀ᵐ x : ℝ, IsAbsolutelyNormal x ∧ IsAbsolutelyNormal (x * (cos θ / sin θ)) :=
      ae_isAbsolutelyNormal.and (ae_mul_of_ae hc ae_isAbsolutelyNormal)
    obtain ⟨x, hx, hcx⟩ := hae.exists
    have h0 := (h x (x * (cos θ / sin θ)) hx hcx).1
    have hzero : x * cos θ - x * (cos θ / sin θ) * sin θ = 0 := by
      field_simp [hne.1]; ring
    rw [hzero] at h0
    exact h0.irrational ⟨0, by simp⟩
  · rintro (hsin | hcos) x y hx hy
    · have hcos2 : cos θ = 1 ∨ cos θ = -1 := by
        have := sin_sq_add_cos_sq θ
        rw [hsin, zero_pow two_ne_zero, zero_add, sq_eq_one_iff] at this
        exact this
      rcases hcos2 with hc | hc <;> simp [hsin, hc, hx, hy, hx.neg, hy.neg]
    · have hsin2 : sin θ = 1 ∨ sin θ = -1 := by
        have := sin_sq_add_cos_sq θ
        rw [hcos, zero_pow two_ne_zero, add_zero, sq_eq_one_iff] at this
        exact this
      rcases hsin2 with hs | hs <;> simp [hcos, hs, hx, hy, hx.neg, hy.neg]

/-- Every real number is the sum of two absolutely normal numbers. -/
theorem exists_isAbsolutelyNormal_add_eq (y : ℝ) :
    ∃ x₁ x₂ : ℝ, IsAbsolutelyNormal x₁ ∧ IsAbsolutelyNormal x₂ ∧ x₁ + x₂ = y := by
  have hshift : ∀ᵐ x : ℝ, IsAbsolutelyNormal (x + (-y)) :=
    (measurePreserving_add_right volume (-y)).quasiMeasurePreserving.ae ae_isAbsolutelyNormal
  obtain ⟨x, hx, hxy⟩ := (ae_isAbsolutelyNormal.and hshift).exists
  have hyx : IsAbsolutelyNormal (y - x) := by
    simpa [neg_add_rev, sub_eq_add_neg, add_comm] using hxy.neg
  exact ⟨x, y - x, hx, hyx, add_sub_cancel _ _⟩

/-- Every nonzero real number is the product of two absolutely normal numbers. -/
theorem exists_isAbsolutelyNormal_mul_eq {y : ℝ} (hy : y ≠ 0) :
    ∃ x₁ x₂ : ℝ, IsAbsolutelyNormal x₁ ∧ IsAbsolutelyNormal x₂ ∧ x₁ * x₂ = y := by
  suffices hpos : ∀ {z : ℝ}, 0 < z →
      ∃ x₁ x₂ : ℝ, IsAbsolutelyNormal x₁ ∧ IsAbsolutelyNormal x₂ ∧ x₁ * x₂ = z by
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · obtain ⟨x₁, x₂, h1, h2, heq⟩ := hpos (neg_pos.2 hlt)
      exact ⟨-x₁, x₂, h1.neg, h2, by linarith⟩
    · exact hpos hgt
  intro z hz
  obtain ⟨t, hsub, ht_meas, ht_null⟩ :=
    exists_measurable_superset_of_null volume_setOf_not_isAbsolutelyNormal
  set s : Set ℝ := t ∩ Set.Ioi (0 : ℝ)
  have hs_meas : MeasurableSet s := ht_meas.inter measurableSet_Ioi
  have hs_null : volume s = 0 := measure_mono_null Set.inter_subset_left ht_null
  set f : ℝ → ℝ := fun x ↦ z / x
  have hf_deriv : ∀ x ∈ s, HasDerivWithinAt f (-z / x ^ 2) s x := fun x hx ↦ by
    have hx0 : x ≠ 0 := hx.2.ne'
    have h1 : HasDerivAt (fun u : ℝ ↦ z * u⁻¹) (z * -(x ^ 2)⁻¹) x :=
      (hasDerivAt_inv hx0).const_mul z
    have h2 : HasDerivAt f (-z / x ^ 2) x := by
      convert h1 using 1
      · ext u; exact div_eq_mul_inv z u
      · ring
    exact h2.hasDerivWithinAt
  have hf_inj : Set.InjOn f s := fun x₁ hx₁ x₂ hx₂ heq ↦ by
    have h1 : x₁ ≠ 0 := hx₁.2.ne'
    have h2 : x₂ ≠ 0 := hx₂.2.ne'
    have : z * x₂ = z * x₁ := by
      have := (div_eq_div_iff h1 h2).1 heq
      linarith
    exact (mul_left_cancel₀ hz.ne' this).symm
  have himg_null : volume (f '' s) = 0 := by
    have hlint := lintegral_image_eq_lintegral_abs_deriv_mul hs_meas hf_deriv hf_inj (fun _ ↦ 1)
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at hlint
    rw [hlint, Measure.restrict_eq_zero.2 hs_null, lintegral_zero_measure]
  have hunion_null : volume (t ∪ f '' s) = 0 := measure_union_null ht_null himg_null
  have hIoi_ne : volume (Set.Ioi (0 : ℝ)) ≠ 0 := by
    rw [Real.volume_Ioi]
    exact ENNReal.top_ne_zero
  have hne : (Set.Ioi (0 : ℝ) \ (t ∪ f '' s)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hempty
    exact hIoi_ne (measure_mono_null hempty hunion_null)
  obtain ⟨x, hxpos, hxnot⟩ := hne
  have hx_norm : IsAbsolutelyNormal x := by
    by_contra h
    exact hxnot (Or.inl (hsub h))
  have hzx_norm : IsAbsolutelyNormal (z / x) := by
    by_contra h
    have hmem : z / x ∈ s := ⟨hsub h, div_pos hz hxpos⟩
    have hfx : f (z / x) = x := by
      simp only [f]; field_simp [hz.ne', hxpos.ne']
    exact hxnot (Or.inr ⟨z / x, hmem, hfx⟩)
  exact ⟨x, z / x, hx_norm, hzx_norm, mul_div_cancel₀ z hxpos.ne'⟩

end Real
