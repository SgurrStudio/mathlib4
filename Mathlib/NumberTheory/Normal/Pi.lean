/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.NumberTheory.Normal.BaileyCrandall
public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Rational

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The BBP formula and Bailey–Crandall reduction for `π` and `log 2`

We prove the **Bailey–Borwein–Plouffe (BBP) formula** for `π` (1997):
$$\pi = \sum_{k=0}^\infty \frac{1}{16^k}
  \left(\frac{4}{8k+1} - \frac{2}{8k+4} - \frac{1}{8k+5} - \frac{1}{8k+6}\right).$$
Combined with the Bailey–Crandall shadowing theorem (`Mathlib/NumberTheory/Normal/BaileyCrandall`),
Maxfield's theorem (`Mathlib/NumberTheory/Normal/BasePow`), and `irrational_pi`, we obtain:

* `Real.isNormalIn_two_pi_iff`: `π` is normal in base `2` (and base `16`) if and only if the
  explicit base-`16` BBP orbit `bbpOrbit 16 bbpPiCoeff` is equidistributed modulo one.
* `Real.not_hasFiniteAttractorModOne_bbpOrbit_pi`: the BBP orbit of `π` does not converge to a
  finite subset of `UnitAddCircle`.
* `Real.isNormalIn_two_pi_of_hypothesisA`: Bailey–Crandall's Hypothesis A for the `π` orbit
  implies that `π` is normal in base `2`.
* `Real.isNormalIn_two_log_two_iff`: `log 2` is normal in base `2` if and only if the orbit
  `x₀ = 0`, `x_{n+1} = fract (2 x_n + 1 / (n + 1))` is equidistributed modulo one.

## References

* [D. H. Bailey, P. Borwein, S. Plouffe, *On the rapid computation of various polylogarithmic
  constants*][BaileyBorweinPlouffe1997]
* [D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant
  expansions*][BaileyCrandall2001]
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The `k`-th rational coefficient of the Bailey–Borwein–Plouffe formula for `π`. -/
noncomputable def bbpPiCoeff (k : ℕ) : ℝ :=
  4 / (8 * k + 1) - 2 / (8 * k + 4) - 1 / (8 * k + 5) - 1 / (8 * k + 6)

private lemma tendsto_bbpPiCoeff_zero : Tendsto bbpPiCoeff atTop (𝓝 0) := by
  have hdiv : ∀ c d : ℝ, Tendsto (fun k : ℕ ↦ c / (8 * (k : ℝ) + d)) atTop (𝓝 0) := fun c d ↦
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)).atTop_add tendsto_const_nhds)
  unfold bbpPiCoeff
  simpa only [sub_zero] using
    (((hdiv 4 1).sub (hdiv 2 4)).sub (hdiv 1 5)).sub (hdiv 1 6)

private lemma integral_bbpTerm (k : ℕ) :
    ∫ x in (0 : ℝ)..1, (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) * (x ^ 8 / 16) ^ k =
      bbpPiCoeff k / (16 : ℝ) ^ k := by
  have hint : ∀ m : ℕ, ∫ x in (0 : ℝ)..1, x ^ (8 * k + m) = 1 / (8 * (k : ℝ) + (m + 1 : ℕ)) := by
    intro m
    rw [integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
    push_cast
    ring
  have hexp : ∀ x : ℝ, (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) * (x ^ 8 / 16) ^ k =
      (16 : ℝ)⁻¹ ^ k * (4 * x ^ (8 * k + 0) - 2 * x ^ (8 * k + 3) -
        x ^ (8 * k + 4) - x ^ (8 * k + 5)) := by
    intro x
    rw [div_pow, pow_add, pow_add, pow_add, pow_add, pow_mul, inv_pow]
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_const_mul]
  have hc : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ ↦ x ^ (8 * k + m)) MeasureTheory.volume 0 1 :=
    fun m ↦ (continuous_pow _).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub
        (((hc 0).const_mul 4 |>.sub ((hc 3).const_mul 2)).sub (hc 4)) (hc 5),
      intervalIntegral.integral_sub ((hc 0).const_mul 4 |>.sub ((hc 3).const_mul 2)) (hc 4),
      intervalIntegral.integral_sub ((hc 0).const_mul 4) ((hc 3).const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hint 0, hint 3, hint 4, hint 5]
  simp only [bbpPiCoeff, inv_pow, div_eq_mul_inv]
  push_cast
  ring

private lemma integral_bbpIntegrand :
    ∫ x in (0 : ℝ)..1, (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) / (1 - x ^ 8 / 16) = π := by
  let F : ℝ → ℝ := fun x ↦
    4 * Real.arctan (x - 1) - 2 * Real.log (x ^ 2 - 2 * x + 2) + 2 * Real.log (2 - x ^ 2)
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F ((4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) / (1 - x ^ 8 / 16)) x := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hq1 : x ^ 2 - 2 * x + 2 ≠ 0 := by nlinarith [sq_nonneg (x - 1)]
    have hq2 : 2 - x ^ 2 ≠ 0 := by nlinarith
    have hx8 : x ^ 8 ≤ 1 := pow_le_one₀ hx0 hx1
    have hq3 : 1 - x ^ 8 / 16 ≠ 0 := by linarith
    have hq4 : 16 - x ^ 8 ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun t : ℝ ↦ 4 * Real.arctan (t - 1)) (4 * (1 + (x - 1) ^ 2)⁻¹) x := by
      simpa using ((hasDerivAt_id x).sub_const 1).arctan.const_mul 4
    have hd2 : HasDerivAt (fun t : ℝ ↦ 2 * Real.log (t ^ 2 - 2 * t + 2))
        (2 * ((2 * x - 2) / (x ^ 2 - 2 * x + 2))) x := by
      have hp1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 - 2 * t) (2 * x - 2) x := by
        have hsq : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have hlin : HasDerivAt (fun t : ℝ ↦ 2 * t) 2 x := by
          simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
        exact hsq.sub hlin
      exact ((hp1.add_const 2).log hq1).const_mul 2
    have hd3 : HasDerivAt (fun t : ℝ ↦ 2 * Real.log (2 - t ^ 2))
        (2 * (-(2 * x) / (2 - x ^ 2))) x := by
      have hp : HasDerivAt (fun t : ℝ ↦ 2 - t ^ 2) (-(2 * x)) x := by
        have hsq : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        exact hsq.const_sub 2
      exact (hp.log hq2).const_mul 2
    have hcomb := (hd1.sub hd2).add hd3
    have halg : 4 * (1 + (x - 1) ^ 2)⁻¹ - 2 * ((2 * x - 2) / (x ^ 2 - 2 * x + 2)) +
        2 * (-(2 * x) / (2 - x ^ 2)) =
        (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) / (1 - x ^ 8 / 16) := by
      have hq1' : 1 + (x - 1) ^ 2 = x ^ 2 - 2 * x + 2 := by ring
      rw [hq1', show 1 - x ^ 8 / 16 = (16 - x ^ 8) / 16 by ring]
      rw [← div_eq_mul_inv, mul_div_assoc', mul_div_assoc', ← sub_div, div_add_div _ _ hq1 hq2,
        div_div_eq_mul_div, div_eq_div_iff (mul_ne_zero hq1 hq2) hq4]
      ring
    rwa [halg] at hcomb
  have hcont : ContinuousOn
      (fun x : ℝ ↦ (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) / (1 - x ^ 8 / 16)) (Set.uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx ↦ ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    have : x ^ 8 ≤ 1 := pow_le_one₀ hx.1 hx.2
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [F, sub_self, arctan_zero, mul_zero, one_pow, zero_sub, arctan_neg, arctan_one,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero]
  norm_num
  ring

/-- **Bailey–Borwein–Plouffe (BBP) formula** for `π`. -/
theorem pi_eq_tsum_bbp : π = ∑' k : ℕ, bbpPiCoeff k / (16 : ℝ) ^ k := by
  symm
  refine HasSum.tsum_eq ?_
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  swap
  · intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : 0 < 8 * (k : ℝ) + 1 := by linarith
    have h4 : 0 < 8 * (k : ℝ) + 4 := by linarith
    have h5 : 0 < 8 * (k : ℝ) + 5 := by linarith
    have h6 : 0 < 8 * (k : ℝ) + 6 := by linarith
    refine div_nonneg ?_ (by positivity)
    rw [bbpPiCoeff]
    have hnum : (4 / (8 * (k : ℝ) + 1) - 2 / (8 * k + 4) - 1 / (8 * k + 5) - 1 / (8 * k + 6)) =
        (960 * (k : ℝ) ^ 2 + 1208 * k + 376) /
          ((8 * k + 1) * (8 * k + 4) * (8 * k + 5) * (8 * k + 6)) := by
      field_simp
      ring
    rw [hnum]
    positivity
  let g : ℝ → ℝ := fun x ↦ (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) / (1 - x ^ 8 / 16)
  let f : ℕ → ℝ → ℝ := fun k x ↦ (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) * (x ^ 8 / 16) ^ k
  have hpartial : ∀ N : ℕ,
      ∑ k ∈ Finset.range N, bbpPiCoeff k / (16 : ℝ) ^ k =
        ∫ x in (0 : ℝ)..1, ∑ k ∈ Finset.range N, f k x := by
    intro N
    rw [intervalIntegral.integral_finsetSum
      fun k _ ↦ (by fun_prop : Continuous (f k)).intervalIntegrable 0 1]
    exact Finset.sum_congr rfl fun k _ ↦ (integral_bbpTerm k).symm
  rw [← integral_bbpIntegrand, Metric.tendsto_atTop]
  intro ε hε
  have h16 : Tendsto (fun N : ℕ ↦ (16 : ℝ) * (16⁻¹ : ℝ) ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num : (16⁻¹ : ℝ) < 1)).const_mul 16
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 h16 ε hε
  refine ⟨N₀, fun N hN ↦ ?_⟩
  rw [hpartial N, Real.dist_eq, abs_sub_comm]
  have hcont_g : ContinuousOn g (Set.uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx ↦ ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    have : x ^ 8 ≤ 1 := pow_le_one₀ hx.1 hx.2
    linarith
  have hcont_s : ContinuousOn (fun x ↦ ∑ k ∈ Finset.range N, f k x) (Set.uIcc 0 1) := by
    fun_prop
  rw [← intervalIntegral.integral_sub hcont_g.intervalIntegrable hcont_s.intervalIntegrable]
  have hbound : ‖∫ x in (0 : ℝ)..1, (g x - ∑ k ∈ Finset.range N, f k x)‖ ≤
      16 * (16⁻¹ : ℝ) ^ N * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ ?_
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : x ≤ 1 := hx.2
    have hx8 : x ^ 8 ≤ 1 := pow_le_one₀ hx0 hx1
    have hden_pos : (15 : ℝ) / 16 ≤ 1 - x ^ 8 / 16 := by linarith
    have hden_ne : 1 - x ^ 8 / 16 ≠ 0 := by linarith
    have hgeom : ∑ k ∈ Finset.range N, (x ^ 8 / 16) ^ k =
        (1 - (x ^ 8 / 16) ^ N) / (1 - x ^ 8 / 16) := by
      rw [geom_sum_eq (by linarith), ← neg_div_neg_eq]
      congr 1 <;> ring
    have hrem : g x - ∑ k ∈ Finset.range N, f k x =
        (4 - 2 * x ^ 3 - x ^ 4 - x ^ 5) * (x ^ 8 / 16) ^ N / (1 - x ^ 8 / 16) := by
      simp only [g, f, ← Finset.mul_sum, hgeom]
      field_simp [hden_ne]
      ring
    rw [Real.norm_eq_abs, hrem, abs_div, abs_mul, abs_of_pos (by linarith : 0 < 1 - x ^ 8 / 16),
      abs_of_nonneg (by positivity : 0 ≤ (x ^ 8 / 16) ^ N)]
    have hnum : |4 - 2 * x ^ 3 - x ^ 4 - x ^ 5| ≤ 8 := by
      have h3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
      have h4 : x ^ 4 ≤ 1 := pow_le_one₀ hx0 hx1
      have h5 : x ^ 5 ≤ 1 := pow_le_one₀ hx0 hx1
      have h3' : 0 ≤ x ^ 3 := pow_nonneg hx0 3
      have h4' : 0 ≤ x ^ 4 := pow_nonneg hx0 4
      have h5' : 0 ≤ x ^ 5 := pow_nonneg hx0 5
      rw [abs_le]
      constructor <;> linarith
    have hpow : (x ^ 8 / 16) ^ N ≤ (16⁻¹ : ℝ) ^ N := by
      gcongr
      linarith
    calc |4 - 2 * x ^ 3 - x ^ 4 - x ^ 5| * (x ^ 8 / 16) ^ N / (1 - x ^ 8 / 16)
        ≤ 8 * (16⁻¹ : ℝ) ^ N / (15 / 16) := by gcongr
      _ ≤ 16 * (16⁻¹ : ℝ) ^ N := by
          have : (0 : ℝ) ≤ (16⁻¹ : ℝ) ^ N := by positivity
          linarith
  have hN' := hN₀ N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN'
  rw [Real.norm_eq_abs] at hbound
  simp only [sub_zero, abs_one, mul_one] at hbound
  exact hbound.trans_lt hN'

/-- `π / 16` is the BBP series `bbpSum 16 bbpPiCoeff`. -/
theorem pi_div_sixteen_eq_bbpSum : π / 16 = bbpSum 16 bbpPiCoeff := by
  rw [pi_eq_tsum_bbp, bbpSum, ← tsum_div_const]
  refine tsum_congr fun k ↦ ?_
  rw [div_div, ← pow_succ]
  norm_num

/-- `π` is normal in base `16` if and only if its BBP orbit is equidistributed modulo one. -/
theorem isNormalIn_sixteen_pi_iff :
    IsNormalIn 16 π ↔ IsEquidistributedModOne (bbpOrbit 16 bbpPiCoeff) := by
  have h1 : IsNormalIn 16 π ↔ IsNormalIn 16 (π / 16) := by
    have := isNormalIn_mul_pow_iff (b := 16) (x := π / 16) 1
    simpa [pow_one, div_mul_cancel₀] using this
  rw [h1, pi_div_sixteen_eq_bbpSum]
  exact isNormalIn_bbpSum_iff_isEquidistributedModOne (by norm_num) tendsto_bbpPiCoeff_zero

/-- `π` is normal in base `2` if and only if its base-`16` BBP orbit is equidistributed
modulo one. -/
theorem isNormalIn_two_pi_iff :
    IsNormalIn 2 π ↔ IsEquidistributedModOne (bbpOrbit 16 bbpPiCoeff) := by
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [← isNormalIn_sixteen_pi_iff, ← h16]
  exact (isNormalIn_pow_iff (b := 2) (by norm_num) (by norm_num : 0 < 4)).symm

/-- Because `π` is irrational, its BBP orbit does not have a finite attractor modulo one. -/
theorem not_hasFiniteAttractorModOne_bbpOrbit_pi :
    ¬ HasFiniteAttractorModOne (bbpOrbit 16 bbpPiCoeff) := by
  refine not_hasFiniteAttractorModOne_bbpOrbit (by norm_num) tendsto_bbpPiCoeff_zero ?_
  rw [← pi_div_sixteen_eq_bbpSum]
  exact irrational_pi.div_natCast (by norm_num)

/-- **Bailey–Crandall (2001)**: Hypothesis A for the `π` BBP orbit implies that `π` is normal in
base `2`. -/
theorem isNormalIn_two_pi_of_hypothesisA
    (hA : HasFiniteAttractorModOne (bbpOrbit 16 bbpPiCoeff) ∨
      IsEquidistributedModOne (bbpOrbit 16 bbpPiCoeff)) :
    IsNormalIn 2 π :=
  isNormalIn_two_pi_iff.2 (hA.resolve_left not_hasFiniteAttractorModOne_bbpOrbit_pi)

/-- The Mercator series `log 2 = ∑' k, 1 / ((k + 1) * 2 ^ (k + 1))` as a BBP sum. -/
theorem log_two_eq_bbpSum : Real.log 2 = bbpSum 2 (fun k ↦ ((k : ℝ) + 1)⁻¹) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := (1 / 2 : ℝ)) (by norm_num)
  have hlog : -Real.log (1 - (1 / 2 : ℝ)) = Real.log 2 := by
    have : (1 - (1 / 2 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
    rw [this, Real.log_inv, neg_neg]
  rw [hlog] at h
  rw [bbpSum, ← h.tsum_eq]
  refine tsum_congr fun k ↦ ?_
  rw [one_div, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_comm]
  norm_num

/-- `log 2` is normal in base `2` if and only if the Bailey–Crandall orbit
`x₀ = 0`, `x_{n+1} = fract (2 x_n + 1 / (n + 1))` is equidistributed modulo one. -/
theorem isNormalIn_two_log_two_iff :
    IsNormalIn 2 (Real.log 2) ↔
      IsEquidistributedModOne (bbpOrbit 2 (fun k ↦ ((k : ℝ) + 1)⁻¹)) := by
  rw [log_two_eq_bbpSum]
  refine isNormalIn_bbpSum_iff_isEquidistributedModOne (by norm_num) ?_
  exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

end Real
