/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Discrepancy
public import Mathlib.NumberTheory.Normal.Weyl

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Erdős–Turán inequality

We prove the **Erdős–Turán inequality** (P. Erdős and P. Turán, 1948): for any real sequence
`u : ℕ → ℝ`, `N ≥ 1`, and integer `M ≥ 0`,
`starDiscrepancy u N ≤ 16 / (M + 1) + (4 / π) * ∑ h ∈ Icc 1 M, (1 / h) * ‖W_N(h)‖`,
where `W_N(h) = (1 / N) ∑_{n < N} exp(2 π i h u_n)` is the `h`-th Weyl mean.

Combined with quantitative Wall's theorem (`Real.abs_blockCount_div_sub_le_discrepancy`), this
yields an explicit exponential-sum bound on digit-block frequency errors in any base `b ≥ 2`.

## Proof strategy

Convolve the zero-mean 1-periodic local discrepancy `g₀(t) = localDiscrepancy u N 0 (fract t) - h₀`
with the normalized Fejér kernel `F_M(t) = (1 / (M + 1)) * ‖∑_{k=0}^M e(k t)‖^2`:

1. Expanding `F_M(t) = ∑_{|h| ≤ M} (1 - |h| / (M + 1)) e(h t)` and integrating by parts gives
   `|(F_M * g₀)(y)| ≤ (1 / π) ∑_{h=1}^M (1 / h) ‖W_N(h)‖` uniformly in `y`.
2. On the other hand, `g₀` satisfies the slope-1 lower bound `g₀(y) - g₀(x) ≥ -(y - x)` for
   `0 ≤ y - x ≤ 1`, while Jordan's inequality bounds the Fejér tail integral by
   `1 / ((M + 1) δ)`. Choosing `δ = 4 / (M + 1)` forces `sup |g₀| / 2 ≤ δ + (1 / π) ∑ ...`,
   and `starDiscrepancy u N ≤ 2 * sup |g₀|`.

## References

* P. Erdős and P. Turán, *On a problem in the theory of uniform distribution*, Indag. Math. 10
  (1948), 370–378, 406–413.
* L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974, Ch. 2 §2.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Real

/-- The normalized Fejér kernel `F_M(t) = (1 / (M + 1)) * ‖∑_{k=0}^M e(k t)‖^2`. -/
private noncomputable def fejerKernel (M : ℕ) (t : ℝ) : ℝ :=
  (‖∑ k ∈ Finset.range (M + 1), Complex.exp (2 * π * Complex.I * (k : ℂ) * t)‖ ^ 2) / (M + 1 : ℝ)

private lemma fejerKernel_nonneg (M : ℕ) (t : ℝ) : 0 ≤ fejerKernel M t := by
  unfold fejerKernel; positivity

private lemma conj_exp_two_pi_I (a : ℝ) :
    starRingEnd ℂ (Complex.exp (2 * π * Complex.I * (a : ℂ))) =
      Complex.exp (-(2 * π * Complex.I * (a : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

private lemma fejerKernel_periodic (M : ℕ) : Function.Periodic (fejerKernel M) 1 := by
  intro t
  unfold fejerKernel
  have hsum :
      ∑ k ∈ Finset.range (M + 1), Complex.exp (2 * π * Complex.I * (k : ℂ) * ((t + 1 : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (M + 1), Complex.exp (2 * π * Complex.I * (k : ℂ) * (t : ℂ)) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have h : (2 * π * Complex.I * (k : ℂ) * ((t + 1 : ℝ) : ℂ)) =
        2 * π * Complex.I * (k : ℂ) * (t : ℂ) + ((k : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I (k : ℤ), mul_one]
  rw [hsum]

private lemma fejerKernel_continuous (M : ℕ) : Continuous (fejerKernel M) := by
  unfold fejerKernel
  fun_prop

/-- Expansion of the Fejér kernel: `F_M(t) = ∑_{h=-M}^M (1 - |h| / (M + 1)) e(h t)`. -/
private lemma fejerKernel_eq_sum (M : ℕ) (t : ℝ) :
    (fejerKernel M t : ℂ) =
      ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
        ((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ) *
          Complex.exp (2 * π * Complex.I * (h : ℂ) * t) := by
  have hM1 : (M + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
  have hsq : ((‖∑ k ∈ Finset.range (M + 1),
      Complex.exp (2 * π * Complex.I * (k : ℂ) * t)‖ ^ 2 : ℝ) : ℂ) =
      (∑ k ∈ Finset.range (M + 1), Complex.exp (2 * π * Complex.I * (k : ℂ) * t)) *
        (∑ j ∈ Finset.range (M + 1), Complex.exp (-(2 * π * Complex.I * (j : ℂ) * t))) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, mul_comm, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hmul : 2 * π * Complex.I * (j : ℂ) * (t : ℂ) =
        2 * π * Complex.I * (((j : ℝ) * t : ℝ) : ℂ) := by push_cast; ring
    rw [hmul, conj_exp_two_pi_I]
  have hdouble :
      (∑ k ∈ Finset.range (M + 1), Complex.exp (2 * π * Complex.I * (k : ℂ) * t)) *
        (∑ j ∈ Finset.range (M + 1), Complex.exp (-(2 * π * Complex.I * (j : ℂ) * t))) =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        Complex.exp (2 * π * Complex.I * (((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℂ) * t) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  have hfiber :
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        Complex.exp (2 * π * Complex.I * (((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℂ) * t) =
      ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
        (((M + 1 : ℤ) - |h| : ℤ) : ℂ) * Complex.exp (2 * π * Complex.I * (h : ℂ) * t) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ ↦ (p.1 : ℤ) - (p.2 : ℤ))
      (t := Finset.Icc (-(M : ℤ)) M)]
    · refine Finset.sum_congr rfl fun h hh ↦ ?_
      rw [Finset.mem_Icc] at hh
      have hconst : ∑ p ∈ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
          (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = h),
          Complex.exp (2 * π * Complex.I * (((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℂ) * t) =
          (((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
            (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℂ) *
            Complex.exp (2 * π * Complex.I * (h : ℂ) * t) := by
        rw [Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.1 hp).2],
          Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      congr 1
      have hcard : (((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
          (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℤ) = (M + 1 : ℤ) - |h| := by
        have hnat : ((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
            (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = h)).card = M + 1 - h.natAbs := by
          rcases le_or_gt 0 h with hh0 | hh0
          · lift h to ℕ using hh0
            have hle : h ≤ M := by exact_mod_cast hh.2
            rw [Int.natAbs_natCast]
            calc ((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
                  (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = (h : ℤ))).card
                = (Finset.range (M + 1 - h)).card := by
                  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
                  · intro p hp
                    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
                      Finset.mem_range] at hp
                    exact Finset.mem_range.2 (by omega)
                  · intro p₁ hp₁ p₂ hp₂ heq
                    rw [Finset.mem_filter] at hp₁ hp₂
                    exact Prod.ext (by omega) heq
                  · intro j hj
                    rw [Finset.mem_range] at hj
                    refine ⟨(j + h, j), ?_, rfl⟩
                    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
                    exact ⟨⟨by omega, by omega⟩, by omega⟩
              _ = M + 1 - h := Finset.card_range _
          · set a := h.natAbs
            have ha_eq : h = -(a : ℤ) := by omega
            have hle : a ≤ M := by omega
            calc ((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
                  (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ) = h)).card
                = (Finset.range (M + 1 - a)).card := by
                  refine Finset.card_bij (fun p _ ↦ p.1) ?_ ?_ ?_
                  · intro p hp
                    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
                      Finset.mem_range] at hp
                    exact Finset.mem_range.2 (by omega)
                  · intro p₁ hp₁ p₂ hp₂ heq
                    rw [Finset.mem_filter] at hp₁ hp₂
                    exact Prod.ext heq (by omega)
                  · intro k hk
                    rw [Finset.mem_range] at hk
                    refine ⟨(k, k + a), ?_, rfl⟩
                    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
                    exact ⟨⟨by omega, by omega⟩, by omega⟩
              _ = M + 1 - a := Finset.card_range _
        have hle : h.natAbs ≤ M + 1 := by omega
        have habs : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
        rw [hnat, habs]
        omega
      exact_mod_cast hcard
    · intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      omega
  unfold fejerKernel
  rw [Complex.ofReal_div, hsq, hdouble, hfiber, Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [mul_div_right_comm]
  congr 1
  push_cast
  field_simp [hM1]
  have habs : ((|h| : ℤ) : ℝ) = |(h : ℝ)| := Int.cast_abs
  rw [← Complex.ofReal_intCast, habs]

/-- Integral of `e(h t)` over `[0, 1]` is `0` for `h ≠ 0`. -/
private lemma integral_exp_two_pi_I_mul_int {h : ℤ} (hh : h ≠ 0) :
    ∫ t in (0 : ℝ)..1, Complex.exp (2 * π * Complex.I * (h : ℂ) * t) = 0 := by
  have hc : (2 * π * Complex.I * (h : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hh]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ Complex.exp (2 * π * Complex.I * (h : ℂ) * s) /
        (2 * π * Complex.I * (h : ℂ)))
        (Complex.exp (2 * π * Complex.I * (h : ℂ) * t)) t := fun t _ ↦ by
    have h1 : HasDerivAt (fun s : ℝ ↦ (2 * π * Complex.I * (h : ℂ)) * (s : ℂ))
        (2 * π * Complex.I * (h : ℂ)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * π * Complex.I * (h : ℂ))
    simpa [mul_div_cancel_right₀ _ hc] using (h1.cexp).div_const (2 * π * Complex.I * (h : ℂ))
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ Complex.exp (2 * π * Complex.I * (h : ℂ) * t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ ↦
      Complex.exp (2 * π * Complex.I * (h : ℂ) * t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : Complex.exp (2 * π * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
    have : 2 * π * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ) = (h : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [h1]
  simp

/-- The Fejér kernel has unit integral over `[0, 1]`. -/
private lemma integral_fejerKernel (M : ℕ) : ∫ t in (0 : ℝ)..1, fejerKernel M t = 1 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [fejerKernel_eq_sum]
  rw [intervalIntegral.integral_finsetSum]
  · have hzero : (0 : ℤ) ∈ Finset.Icc (-(M : ℤ)) M := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    rw [Finset.sum_eq_single (0 : ℤ)]
    · simp
    · intro h _ hh
      rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_I_mul_int hh, mul_zero]
    · intro h; exact absurd hzero h
  · intro h _
    exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- Pointwise tail bound for the Fejér kernel: `F_M(t) ≤ 1 / (4 (M + 1) t ^ 2)` for
`0 < |t| ≤ 1 / 2`. -/
private lemma fejerKernel_le_inv_sq (M : ℕ) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ 1 / 2) :
    fejerKernel M t ≤ 1 / (4 * (M + 1 : ℝ) * t ^ 2) := by
  set z : ℂ := Complex.exp (2 * π * Complex.I * t)
  have hgeom : (z - 1) * ∑ k ∈ Finset.range (M + 1), z ^ k = z ^ (M + 1) - 1 := by
    simpa [mul_comm] using geom_sum_mul z (M + 1)
  have hsum_eq : ∑ k ∈ Finset.range (M + 1), Complex.exp (2 * π * Complex.I * (k : ℂ) * t) =
      ∑ k ∈ Finset.range (M + 1), z ^ k := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Complex.exp_natCast_mul]
    congr 1; ring
  have hnorm_num : ‖z ^ (M + 1) - 1‖ ≤ 2 := by
    have hz1 : ‖z‖ = 1 := by
      have : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [show z = Complex.exp _ from rfl, this, Complex.norm_exp_ofReal_mul_I]
    calc ‖z ^ (M + 1) - 1‖ ≤ ‖z ^ (M + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ ^ (M + 1) + 1 := by rw [norm_pow, norm_one]
      _ = 2 := by rw [hz1, one_pow]; norm_num
  have hnorm_den : ‖z - 1‖ = 2 * |Real.sin (π * t)| := by
    have hfactor : z - 1 = Complex.exp (π * Complex.I * t) *
        (Complex.exp (π * Complex.I * t) - Complex.exp (-(π * Complex.I * t))) := by
      rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
      have h1 : π * Complex.I * (t : ℂ) + π * Complex.I * (t : ℂ) = 2 * π * Complex.I * t := by ring
      have h2 : π * Complex.I * (t : ℂ) + -(π * Complex.I * t) = 0 := by ring
      rw [h1, h2, Complex.exp_zero]
    have hsin : Complex.exp (π * Complex.I * t) - Complex.exp (-(π * Complex.I * t)) =
        2 * Complex.I * ((Real.sin (π * t) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sin, Complex.sin]
      have h1 : ((π * t : ℝ) : ℂ) * Complex.I = π * Complex.I * t := by push_cast; ring
      have h2 : -((π * t : ℝ) : ℂ) * Complex.I = -(π * Complex.I * t) := by push_cast; ring
      rw [h1, h2]
      field_simp [Complex.I_ne_zero]
      simp [Complex.I_sq]
    have hexp1 : ‖Complex.exp (π * Complex.I * t)‖ = 1 := by
      have : π * Complex.I * (t : ℂ) = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [hfactor, hsin, norm_mul, hexp1, one_mul, norm_mul, norm_mul,
      show ‖(2 : ℂ)‖ = 2 by norm_num, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have hjordan : 2 * |t| ≤ |Real.sin (π * t)| := by
    have h1 : 0 ≤ π * |t| := by positivity
    have h2 : π * |t| ≤ π / 2 := by nlinarith [Real.pi_pos]
    have hj := Real.mul_le_sin h1 h2
    have hsin_abs : Real.sin (π * |t|) = |Real.sin (π * t)| := by
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h] at ht ⊢
        exact (abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
          (by nlinarith [Real.pi_pos]))).symm
      · rw [abs_of_neg h] at ht ⊢
        rw [mul_neg, Real.sin_neg, ← abs_neg (Real.sin (π * t))]
        exact (abs_of_nonneg (by
          rw [← Real.sin_neg, ← mul_neg]
          exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
            (by nlinarith [Real.pi_pos]))).symm
    rw [← hsin_abs]
    have hsimp : 2 / π * (π * |t|) = 2 * |t| := by field_simp [Real.pi_ne_zero]
    linarith
  have htabs : 0 < |t| := abs_pos.2 ht0
  have hnorm_sum : ‖∑ k ∈ Finset.range (M + 1),
      Complex.exp (2 * π * Complex.I * (k : ℂ) * t)‖ ≤ 1 / (2 * |t|) := by
    rw [hsum_eq, le_div_iff₀ (by positivity)]
    have hmul := congrArg (fun x : ℂ ↦ ‖x‖) hgeom
    rw [norm_mul, hnorm_den] at hmul
    have h1 : 4 * |t| * ‖∑ k ∈ Finset.range (M + 1), z ^ k‖ ≤ 2 := by
      calc 4 * |t| * ‖∑ k ∈ Finset.range (M + 1), z ^ k‖
          = (2 * (2 * |t|)) * ‖∑ k ∈ Finset.range (M + 1), z ^ k‖ := by ring
        _ ≤ (2 * |Real.sin (π * t)|) * ‖∑ k ∈ Finset.range (M + 1), z ^ k‖ := by gcongr
        _ = ‖z ^ (M + 1) - 1‖ := hmul
        _ ≤ 2 := hnorm_num
    linarith
  unfold fejerKernel
  have hsq : ‖∑ k ∈ Finset.range (M + 1),
      Complex.exp (2 * π * Complex.I * (k : ℂ) * t)‖ ^ 2 ≤ 1 / (4 * t ^ 2) := by
    calc ‖∑ k ∈ Finset.range (M + 1),
            Complex.exp (2 * π * Complex.I * (k : ℂ) * t)‖ ^ 2
        ≤ (1 / (2 * |t|)) ^ 2 := by gcongr
      _ = 1 / (4 * t ^ 2) := by rw [div_pow, one_pow, mul_pow, sq_abs]; ring
  calc (‖∑ k ∈ Finset.range (M + 1),
          Complex.exp (2 * π * Complex.I * (k : ℂ) * t)‖ ^ 2) / (M + 1 : ℝ)
      ≤ (1 / (4 * t ^ 2)) / (M + 1 : ℝ) := by gcongr
    _ = 1 / (4 * (M + 1 : ℝ) * t ^ 2) := by
        field_simp [ht0, (show (M + 1 : ℝ) ≠ 0 by positivity)]

/-- Tail integral of the Fejér kernel: for `0 < δ ≤ 1`,
`(∫ t in (-1/2)..(-δ/2), F_M t) + (∫ t in (δ/2)..(1/2), F_M t) ≤ 1 / ((M + 1) * δ)`. -/
private lemma fejerKernel_tail_integral_le (M : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), fejerKernel M t) +
      (∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t) ≤ 1 / ((M + 1 : ℝ) * δ) := by
  have hint_pos : ∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t ≤ 1 / (2 * (M + 1 : ℝ) * δ) := by
    have hinv_int : IntervalIntegrable (fun t : ℝ ↦ 1 / (4 * (M + 1 : ℝ) * t ^ 2))
        volume (δ / 2) (1 / 2) := by
      refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
      rw [uIcc_of_le (by linarith)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      exact (ContinuousAt.div continuousAt_const
        (continuousAt_const.mul (continuousAt_id.pow 2))
        (by positivity : 4 * (M + 1 : ℝ) * t ^ 2 ≠ 0)).continuousWithinAt
    calc ∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t
        ≤ ∫ t in (δ / 2)..(1 / 2 : ℝ), 1 / (4 * (M + 1 : ℝ) * t ^ 2) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            ((fejerKernel_continuous M).intervalIntegrable _ _) hinv_int fun t ht ↦ ?_
          exact fejerKernel_le_inv_sq M (by linarith [ht.1])
            (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
      _ = (1 / (4 * (M + 1 : ℝ))) * ∫ t in (δ / 2)..(1 / 2 : ℝ), (t ^ 2)⁻¹ := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun t ht ↦ ?_
          rw [uIcc_of_le (by linarith)] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          field_simp [ht0, (show (M + 1 : ℝ) ≠ 0 by positivity)]
      _ = (1 / (4 * (M + 1 : ℝ))) * (2 / δ - 2) := by
          have hderiv : ∀ t ∈ uIcc (δ / 2) (1 / 2 : ℝ),
              HasDerivAt (fun s : ℝ ↦ -s⁻¹) ((t ^ 2)⁻¹) t := fun t ht ↦ by
            rw [uIcc_of_le (by linarith)] at ht
            have ht0 : t ≠ 0 := by linarith [ht.1]
            simpa using (hasDerivAt_inv ht0).fun_neg
          have hpow_int : IntervalIntegrable (fun t : ℝ ↦ (t ^ 2)⁻¹) volume (δ / 2) (1 / 2) := by
            refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
            rw [uIcc_of_le (by linarith)] at ht
            have ht0 : t ≠ 0 := by linarith [ht.1]
            exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).continuousWithinAt
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hpow_int]
          field_simp [hδ0.ne']
          ring
      _ ≤ 1 / (2 * (M + 1 : ℝ) * δ) := by
          have hval : (1 / (4 * (M + 1 : ℝ))) * (2 / δ - 2) =
              1 / (2 * (M + 1 : ℝ) * δ) - 1 / (2 * (M + 1 : ℝ)) := by
            field_simp [hδ0.ne', (show (M + 1 : ℝ) ≠ 0 by positivity)]
            ring
          linarith [show (0 : ℝ) ≤ 1 / (2 * (M + 1 : ℝ)) by positivity]
  have hint_neg : ∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), fejerKernel M t =
      ∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t := by
    have heven : ∀ t : ℝ, fejerKernel M (-t) = fejerKernel M t := fun t ↦ by
      unfold fejerKernel
      congr 2
      have hconj :
          ∑ k ∈ Finset.range (M + 1), Complex.exp (2 * π * Complex.I * (k : ℂ) * (-t : ℝ)) =
          starRingEnd ℂ (∑ k ∈ Finset.range (M + 1),
            Complex.exp (2 * π * Complex.I * (k : ℂ) * (t : ℝ))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        have h1 : 2 * π * Complex.I * (k : ℂ) * ((t : ℝ) : ℂ) =
            2 * π * Complex.I * (((k : ℝ) * t : ℝ) : ℂ) := by push_cast; ring
        have h2 : 2 * π * Complex.I * (k : ℂ) * ((-t : ℝ) : ℂ) =
            -(2 * π * Complex.I * (((k : ℝ) * t : ℝ) : ℂ)) := by push_cast; ring
        rw [h1, h2, conj_exp_two_pi_I]
      rw [hconj, Complex.norm_conj]
    have hcomp := intervalIntegral.integral_comp_neg (f := fejerKernel M) (a := δ / 2) (b := 1 / 2)
    simpa only [heven] using hcomp.symm
  have hadd : 1 / (2 * (M + 1 : ℝ) * δ) + 1 / (2 * (M + 1 : ℝ) * δ) = 1 / ((M + 1 : ℝ) * δ) := by
    field_simp [hδ0.ne', (show (M + 1 : ℝ) ≠ 0 by positivity)]
    ring
  linarith

/-- Helper: `HasDerivAt` for `s ↦ exp(-(2 π i h s)) / (-(2 π i h))`. -/
private lemma hasDerivAt_exp_neg_div {h : ℤ} (hh : h ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) /
        (-(2 * π * Complex.I * (h : ℂ))))
      (Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t))) t := by
  have hc : (2 * π * Complex.I * (h : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hh]
  have ha : HasDerivAt (fun s : ℝ ↦ -(2 * π * Complex.I * (h : ℂ) * (s : ℂ)))
      (-(2 * π * Complex.I * (h : ℂ))) t := by
    have h0 := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(2 * π * Complex.I * (h : ℂ)))
    convert h0 using 1
    · ext s; simp [Complex.ofRealCLM_apply]
    · simp [Complex.ofRealCLM_apply]
  have hdiv := (ha.cexp).div_const (-(2 * π * Complex.I * (h : ℂ)))
  have hsimp : Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) *
      (-(2 * π * Complex.I * (h : ℂ))) / (-(2 * π * Complex.I * (h : ℂ))) =
      Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) :=
    mul_div_cancel_right₀ _ (neg_ne_zero.2 hc)
  exact hsimp ▸ hdiv

/-- Fourier coefficient of the periodic local discrepancy `g(t) = localDiscrepancy u N 0 (fract t)`
at a nonzero integer frequency `h ≠ 0`. -/
private lemma fourier_localDiscrepancy (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {h : ℤ} (hh : h ≠ 0) :
    ∫ t in (0 : ℝ)..1,
      ((localDiscrepancy u N 0 (Int.fract t) : ℝ) : ℂ) *
        Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) =
      ((∑ n ∈ Finset.range N, Complex.exp (-(2 * π * Complex.I * (h : ℂ) * u n))) / N) /
        (2 * π * Complex.I * (h : ℂ)) := by
  have hc : (2 * π * Complex.I * (h : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hh]
  have hcongr : ∫ t in (0 : ℝ)..1,
      ((localDiscrepancy u N 0 (Int.fract t) : ℝ) : ℂ) *
        Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) =
      ∫ t in (0 : ℝ)..1,
        ((∑ n ∈ Finset.range N,
            (Ioi (Int.fract (u n))).indicator
              (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) t) / N -
          (t : ℂ) * Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t))) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hne1 : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by
      rw [ae_iff]
      simp
    filter_upwards [hne1] with t ht1 htIoc
    have htIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨htIoc.1, lt_of_le_of_ne htIoc.2 ht1⟩
    rw [Int.fract_eq_self.2 ⟨htIoo.1.le, htIoo.2⟩, localDiscrepancy, sub_zero]
    have hcard :
        ∑ n ∈ Finset.range N,
          (Ioi (Int.fract (u n))).indicator
            (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) t =
          (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card : ℂ) *
            Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      by_cases hlt : Int.fract (u n) < t
      · simp [Int.fract_nonneg, hlt]
      · simp [hlt]
    rw [hcard]
    push_cast
    ring
  rw [hcongr]
  have hexp_cont : Continuous fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) := by
    fun_prop
  have hind_int : ∀ x ∈ Ico (0 : ℝ) 1,
      IntervalIntegrable ((Ioi x).indicator
        fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) volume 0 1 := fun x _ ↦ by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (hexp_cont.intervalIntegrable 0 1).1.indicator measurableSet_Ioi
  have hsum_int : IntervalIntegrable
      (fun t : ℝ ↦ (∑ n ∈ Finset.range N, (Ioi (Int.fract (u n))).indicator
        (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) t) / N) volume 0 1 := by
    have h1 : ∀ s : Finset ℕ, IntervalIntegrable
        (fun t : ℝ ↦ ∑ n ∈ s, (Ioi (Int.fract (u n))).indicator
          (fun r : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * r))) t) volume 0 1 := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simp
      | cons a s ha ih =>
        simpa only [Finset.sum_cons] using
          (hind_int _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩).add ih
    exact (h1 (Finset.range N)).div_const _
  have hte_int : IntervalIntegrable
      (fun t : ℝ ↦ (t : ℂ) * Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t))) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hsum_int hte_int, intervalIntegral.integral_div,
    intervalIntegral.integral_finsetSum fun n _ ↦
      hind_int _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩]
  have hind_eval : ∀ x ∈ Ico (0 : ℝ) 1,
      ∫ t in (0 : ℝ)..1,
        (Ioi x).indicator (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) t =
      (Complex.exp (-(2 * π * Complex.I * (h : ℂ) * x)) - 1) / (2 * π * Complex.I * (h : ℂ)) := by
    intro x hx
    have h1 : IntervalIntegrable ((Ioi x).indicator
        fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) volume 0 x :=
      (hind_int x hx).mono_set (uIcc_subset_uIcc (by simp) (by simp [hx.1, hx.2.le]))
    have h2 : IntervalIntegrable ((Ioi x).indicator
        fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) volume x 1 :=
      (hind_int x hx).mono_set (uIcc_subset_uIcc (by simp [hx.1, hx.2.le]) (by simp))
    have h0 : ∫ t in (0 : ℝ)..x,
        (Ioi x).indicator (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) t = 0 := by
      rw [intervalIntegral.integral_of_le hx.1]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦
        Set.indicator_of_notMem (not_lt.2 ht.2) _
    have h3 : ∫ t in x..1,
        (Ioi x).indicator (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) t =
        ∫ t in x..1, Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) := by
      rw [intervalIntegral.integral_of_le hx.2.le, intervalIntegral.integral_of_le hx.2.le]
      exact setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ Set.indicator_of_mem ht.1 _
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, h0, zero_add, h3]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_exp_neg_div hh t) (hexp_cont.intervalIntegrable _ _)]
    have he1 : Complex.exp (-(2 * π * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ))) = 1 := by
      have : -(2 * π * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ)) =
          ((-h : ℤ) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [he1]
    field_simp [hc]
    ring
  have hte_eval :
      ∫ t in (0 : ℝ)..1, (t : ℂ) * Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) =
      -(1 / (2 * π * Complex.I * (h : ℂ))) := by
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun s : ℝ ↦ (s : ℂ)) (u' := fun _ ↦ (1 : ℂ))
      (v := fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) /
        (-(2 * π * Complex.I * (h : ℂ))))
      (v' := fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)))
      (fun t _ ↦ Complex.ofRealCLM.hasDerivAt) (fun t _ ↦ hasDerivAt_exp_neg_div hh t)
      intervalIntegrable_const (hexp_cont.intervalIntegrable 0 1)
    have hrem : ∫ t in (0 : ℝ)..1, (1 : ℂ) *
        (Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) /
          (-(2 * π * Complex.I * (h : ℂ)))) = 0 := by
      simp_rw [one_mul, intervalIntegral.integral_div]
      have hneg := integral_exp_two_pi_I_mul_int (neg_ne_zero.2 hh)
      have hcongr' : ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * π * Complex.I * (h : ℂ) * t)) =
          ∫ t in (0 : ℝ)..1, Complex.exp (2 * π * Complex.I * ((-h : ℤ) : ℂ) * t) := by
        refine intervalIntegral.integral_congr fun t _ ↦ ?_
        congr 1; push_cast; ring
      rw [hcongr', hneg, zero_div]
    have he1 : Complex.exp (-(2 * π * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ))) = 1 := by
      have : -(2 * π * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ)) =
          ((-h : ℤ) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [hibp, hrem, sub_zero, he1]
    push_cast
    field_simp [hc]
    ring
  have hfract_exp : ∀ n : ℕ,
      Complex.exp (-(2 * π * Complex.I * (h : ℂ) * ((Int.fract (u n) : ℝ) : ℂ))) =
        Complex.exp (-(2 * π * Complex.I * (h : ℂ) * ((u n : ℝ) : ℂ))) := fun n ↦ by
    have hfr : ((Int.fract (u n) : ℝ) : ℂ) = ((u n : ℝ) : ℂ) - ((⌊u n⌋ : ℤ) : ℂ) := by
      exact_mod_cast (rfl : Int.fract (u n) = u n - ⌊u n⌋)
    have hmul : -(2 * π * Complex.I * (h : ℂ) * ((Int.fract (u n) : ℝ) : ℂ)) =
        -(2 * π * Complex.I * (h : ℂ) * ((u n : ℝ) : ℂ)) +
          ((h * ⌊u n⌋ : ℤ) : ℂ) * (2 * π * Complex.I) := by
      rw [hfr]; push_cast; ring
    rw [hmul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I (h * ⌊u n⌋), mul_one]
  have hsum_eval :
      ∑ n ∈ Finset.range N,
        ∫ t in (0 : ℝ)..1,
          (Ioi (Int.fract (u n))).indicator
            (fun s : ℝ ↦ Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) t =
      ((∑ n ∈ Finset.range N, Complex.exp (-(2 * π * Complex.I * (h : ℂ) * u n))) - N) /
        (2 * π * Complex.I * (h : ℂ)) := by
    rw [Finset.sum_congr rfl fun n _ ↦ hind_eval _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
      ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    congr 2
    exact Finset.sum_congr rfl fun n _ ↦ hfract_exp n
  rw [hsum_eval, hte_eval]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp [hc, hN0]
  ring

/-- Slope-1 lower bound for the 1-periodic local discrepancy: for `0 ≤ y - x ≤ 1`,
`localDiscrepancy u N 0 (fract y) - localDiscrepancy u N 0 (fract x) ≥ -(y - x)`. -/
private lemma localDiscrepancy_fract_sub_ge (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {x y : ℝ} (hxy : x ≤ y) (hxy1 : y - x ≤ 1) :
    -(y - x) ≤ localDiscrepancy u N 0 (Int.fract y) - localDiscrepancy u N 0 (Int.fract x) := by
  have hfl : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy
  have hfl1 : ⌊y⌋ ≤ ⌊x⌋ + 1 := by
    have : y < (⌊x⌋ + 2 : ℤ) := by
      have := Int.lt_floor_add_one x
      push_cast; linarith
    have := Int.floor_lt.2 this
    omega
  rcases eq_or_lt_of_le hfl with heq | hlt
  · have hfx : Int.fract x ≤ Int.fract y := by
      rw [Int.fract, Int.fract, heq]; linarith
    have hdiff : Int.fract y - Int.fract x = y - x := by
      rw [Int.fract, Int.fract, heq]; ring
    have hcard :
        (((Finset.range N).filter fun n ↦
            Int.fract (u n) ∈ Ico (0 : ℝ) (Int.fract x)).card : ℝ) / N ≤
        (((Finset.range N).filter fun n ↦
            Int.fract (u n) ∈ Ico (0 : ℝ) (Int.fract y)).card : ℝ) / N := by
      gcongr
    simp only [localDiscrepancy, sub_zero]
    linarith
  · have hsucc : ⌊y⌋ = ⌊x⌋ + 1 := by omega
    have hdiff : Int.fract y - Int.fract x = (y - x) - 1 := by
      rw [Int.fract, Int.fract, hsucc]; push_cast; ring
    have h0 : (0 : ℝ) ≤
        (((Finset.range N).filter fun n ↦
            Int.fract (u n) ∈ Ico (0 : ℝ) (Int.fract y)).card : ℝ) / N := by
      positivity
    have h1 :
        (((Finset.range N).filter fun n ↦
            Int.fract (u n) ∈ Ico (0 : ℝ) (Int.fract x)).card : ℝ) / N ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range N).le
    simp only [localDiscrepancy, sub_zero]
    linarith

/-- **Erdős–Turán inequality**: the star discrepancy `D_N^*(u)` is bounded in terms of the first
`M` Weyl exponential sums `W_N(h) = (1 / N) ∑_{n < N} exp(2 π i h u_n)`. -/
theorem erdos_turan (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    starDiscrepancy u N ≤
      16 / (M + 1 : ℝ) +
        (4 / π) * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) *
            ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) / N‖ := by
  set W : ℝ := ∑ h ∈ Finset.Icc 1 M,
    (1 / (h : ℝ)) *
      ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) / N‖
  have hW_nonneg : 0 ≤ W := Finset.sum_nonneg fun h _ ↦ by positivity
  by_cases hM : M + 1 < 8
  · have h16 : (1 : ℝ) ≤ 16 / (M + 1 : ℝ) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact_mod_cast (by omega : M + 1 ≤ 16)
    have : 0 ≤ (4 / π) * W := by positivity
    linarith [starDiscrepancy_le_one u N]
  push Not at hM
  let g : ℝ → ℝ := fun t ↦ localDiscrepancy u N 0 (Int.fract t)
  have hg_per : Function.Periodic g 1 := fun t ↦ by simp only [g, Int.fract_add_one]
  have hg_int_01 : IntervalIntegrable g volume 0 1 := by
    have hcongr : EqOn g
        (fun t ↦ (∑ n ∈ Finset.range N,
          (Ioi (Int.fract (u n))).indicator (fun _ ↦ (1 : ℝ)) t) / N - t)
        (Ioo 0 1) := fun t ht ↦ by
      simp only [g, Int.fract_eq_self.2 ⟨ht.1.le, ht.2⟩, localDiscrepancy, sub_zero]
      have hcard :
          ∑ n ∈ Finset.range N, (Ioi (Int.fract (u n))).indicator (fun _ ↦ (1 : ℝ)) t =
            (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        by_cases hlt : Int.fract (u n) < t
        · simp [Int.fract_nonneg, hlt]
        · simp [hlt]
      rw [hcard]
    have hrhs : IntervalIntegrable
        (fun t ↦ (∑ n ∈ Finset.range N,
          (Ioi (Int.fract (u n))).indicator (fun _ ↦ (1 : ℝ)) t) / N - t)
        volume 0 1 := by
      have hind1 : ∀ x : ℝ,
          IntervalIntegrable ((Ioi x).indicator (fun _ ↦ (1 : ℝ))) volume 0 1 := fun x ↦ by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        exact (integrableOn_const (hs := measure_Ioc_lt_top.ne)).indicator measurableSet_Ioi
      have hsum : ∀ s : Finset ℕ, IntervalIntegrable
          (fun t ↦ ∑ n ∈ s, (Ioi (Int.fract (u n))).indicator (fun _ ↦ (1 : ℝ)) t)
          volume 0 1 := by
        intro s
        induction s using Finset.cons_induction with
        | empty => simp
        | cons a s ha ih =>
          simpa only [Finset.sum_cons] using (hind1 (Int.fract (u a))).add ih
      exact ((hsum (Finset.range N)).div_const _).sub (continuous_id.intervalIntegrable 0 1)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hrhs ⊢
    exact hrhs.congr_fun hcongr.symm measurableSet_Ioo
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b ↦ by
    have hint_nat : ∀ k : ℤ, IntervalIntegrable g volume (k : ℝ) ((k : ℝ) + 1) := fun k ↦ by
      have hsub := hg_int_01.comp_sub_right (k : ℝ)
      have hEq : (fun t ↦ g (t - k)) = g := by ext t; simp [g]
      rw [hEq, zero_add, add_comm] at hsub
      exact hsub
    have hint_range : ∀ k : ℤ, ∀ n : ℕ, IntervalIntegrable g volume (k : ℝ) ((k : ℝ) + n) := by
      intro k n
      induction n with
      | zero => simp
      | succ n ih =>
        have hstep := hint_nat (k + n)
        have hcast : ((k + n : ℤ) : ℝ) = (k : ℝ) + (n : ℝ) := by push_cast; rfl
        rw [hcast] at hstep
        have htrans := ih.trans hstep
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using htrans
    let k := ⌊min a b⌋
    let n := (⌈max a b⌉ - k).toNat + 1
    have hsub : uIcc a b ⊆ uIcc (k : ℝ) ((k : ℝ) + n) := by
      have hle_kn : (k : ℝ) ≤ (k : ℝ) + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
      rw [uIcc_of_le hle_kn]
      intro t ht
      rw [mem_uIcc] at ht
      have h1 : (k : ℝ) ≤ min a b := Int.floor_le _
      have h2 : max a b ≤ (k : ℝ) + n := by
        have hceil := Int.le_ceil (max a b)
        have hk : k ≤ ⌈max a b⌉ := by
          have : (k : ℝ) ≤ (⌈max a b⌉ : ℝ) := le_trans h1 (le_trans (min_le_max) hceil)
          exact_mod_cast this
        have hZ : ⌈max a b⌉ ≤ k + ((⌈max a b⌉ - k).toNat + 1 : ℕ) := by omega
        have hR : (⌈max a b⌉ : ℝ) ≤ (k : ℝ) + n := by exact_mod_cast hZ
        linarith
      rcases ht with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact ⟨le_trans h1 (le_trans (min_le_left _ _) h),
          le_trans h' (le_trans (le_max_right _ _) h2)⟩
      · exact ⟨le_trans h1 (le_trans (min_le_right _ _) h),
          le_trans h' (le_trans (le_max_left _ _) h2)⟩
    exact (hint_range k n).mono_set hsub
  set h₀ : ℝ := ∫ t in (0 : ℝ)..1, g t
  let g0 : ℝ → ℝ := fun t ↦ g t - h₀
  have hg0_per : Function.Periodic g0 1 := fun t ↦ by simp only [g0, hg_per t]
  have hg0_int : ∀ a b : ℝ, IntervalIntegrable g0 volume a b := fun a b ↦
    (hg_int a b).sub intervalIntegrable_const
  have hg0_mean : ∫ t in (0 : ℝ)..1, g0 t = 0 := by
    simp only [g0, intervalIntegral.integral_sub (hg_int 0 1) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul, h₀, sub_self]
  have hg0_bdd : BddAbove (range fun t : ℝ ↦ |g0 t|) := by
    refine ⟨1 + |h₀|, ?_⟩
    rintro _ ⟨t, rfl⟩
    have hg1 : |g t| ≤ 1 :=
      abs_localDiscrepancy_le_one u N le_rfl (Int.fract_nonneg t) (Int.fract_lt_one t).le
    calc |g0 t| = |g t - h₀| := rfl
      _ ≤ |g t| + |h₀| := abs_sub _ _
      _ ≤ 1 + |h₀| := by linarith
  set S : ℝ := ⨆ t : ℝ, |g0 t|
  have hg0_le_S : ∀ t : ℝ, |g0 t| ≤ S := fun t ↦ le_ciSup hg0_bdd t
  have hS_nonneg : 0 ≤ S := le_trans (abs_nonneg _) (hg0_le_S 0)
  have hD_le_2S : starDiscrepancy u N ≤ 2 * S := by
    have hh0 : |h₀| ≤ S := by
      have h0 : g 0 = 0 := by simp [g, localDiscrepancy]
      have : |g0 0| = |h₀| := by simp [g0, h0]
      linarith [hg0_le_S 0]
    refine starDiscrepancy_le fun t ht ↦ ?_
    by_cases ht1 : t = 1
    · rw [ht1, localDiscrepancy_zero_one u hN, abs_zero]; linarith
    · have hfr : Int.fract t = t := Int.fract_eq_self.2 ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
      have hgt : localDiscrepancy u N 0 t = g0 t + h₀ := by simp [g0, g, hfr]
      rw [hgt]
      exact (abs_add_le _ _).trans (by linarith [hg0_le_S t])
  have hconv_bound : ∀ y : ℝ, |∫ t in (-(1 / 2 : ℝ))..(1 / 2), g0 (y - t) * fejerKernel M t| ≤
      (1 / π) * W := by
    intro y
    have hper_prod : Function.Periodic (fun t ↦ g0 (y - t) * fejerKernel M t) 1 := fun t ↦ by
      dsimp only
      have h1 : y - (t + 1) = (y - t) - 1 := by ring
      have h2 : g0 ((y - t) - 1) = g0 (y - t) := by
        simpa [sub_add_cancel] using (hg0_per ((y - t) - 1)).symm
      rw [h1, h2, fejerKernel_periodic M t]
    have hshift1 : ∫ t in (-(1 / 2 : ℝ))..(1 / 2), g0 (y - t) * fejerKernel M t =
        ∫ t in (0 : ℝ)..1, g0 (y - t) * fejerKernel M t := by
      have := hper_prod.intervalIntegral_add_eq (-(1 / 2 : ℝ)) (0 : ℝ)
      norm_num at this
      exact this
    have hsub : ∫ t in (0 : ℝ)..1, g0 (y - t) * fejerKernel M t =
        ∫ s in (0 : ℝ)..1, g0 s * fejerKernel M (y - s) := by
      have hcomp := intervalIntegral.integral_comp_sub_left
        (fun s ↦ g0 s * fejerKernel M (y - s)) y (a := (0 : ℝ)) (b := 1)
      have hsimpl : (fun t ↦ g0 (y - t) * fejerKernel M (y - (y - t))) =
          (fun t ↦ g0 (y - t) * fejerKernel M t) := by ext t; ring_nf
      rw [hsimpl] at hcomp
      rw [hcomp]
      have hper2 : Function.Periodic (fun s ↦ g0 s * fejerKernel M (y - s)) 1 := fun s ↦ by
        dsimp only
        have h1 : y - (s + 1) = (y - s) - 1 := by ring
        have h2 : fejerKernel M ((y - s) - 1) = fejerKernel M (y - s) := by
          simpa [sub_add_cancel] using (fejerKernel_periodic M ((y - s) - 1)).symm
        rw [hg0_per s, h1, h2]
      have hper_eq := hper2.intervalIntegral_add_eq (y - 1) 0
      simpa only [sub_add_cancel, zero_add, sub_zero] using hper_eq
    rw [hshift1, hsub]
    have hC : ((∫ s in (0 : ℝ)..1, g0 s * fejerKernel M (y - s) : ℝ) : ℂ) =
        ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
          ((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ) *
            Complex.exp (2 * π * Complex.I * (h : ℂ) * y) *
            (∫ s in (0 : ℝ)..1, ((g0 s : ℝ) : ℂ) *
              Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) := by
      rw [← intervalIntegral.integral_ofReal]
      have hrew : ∀ s : ℝ, ((g0 s * fejerKernel M (y - s) : ℝ) : ℂ) =
          ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
            ((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ) *
              Complex.exp (2 * π * Complex.I * (h : ℂ) * y) *
              (((g0 s : ℝ) : ℂ) * Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) := fun s ↦ by
        rw [Complex.ofReal_mul, fejerKernel_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ ↦ ?_
        have hexp : Complex.exp (2 * π * Complex.I * (h : ℂ) * ((y - s : ℝ) : ℂ)) =
            Complex.exp (2 * π * Complex.I * (h : ℂ) * y) *
              Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hexp]; ring
      simp_rw [hrew]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun h _ ↦ ?_
        rw [intervalIntegral.integral_const_mul]
      · intro h _
        have hg0C : IntervalIntegrable (fun s : ℝ ↦ ((g0 s : ℝ) : ℂ)) volume 0 1 :=
          ⟨Complex.ofRealCLM.integrable_comp (hg0_int 0 1).1,
            Complex.ofRealCLM.integrable_comp (hg0_int 0 1).2⟩
        have hprod := hg0C.mul_continuousOn
          (by fun_prop : Continuous fun s : ℝ ↦
            Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))).continuousOn
        exact hprod.const_mul _
    have hterm : ∀ h ∈ Finset.Icc (-(M : ℤ)) M,
        ‖((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ) *
          Complex.exp (2 * π * Complex.I * (h : ℂ) * y) *
          (∫ s in (0 : ℝ)..1, ((g0 s : ℝ) : ℂ) *
            Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)))‖ ≤
        if h = 0 then 0 else
          (1 / (2 * π * (h.natAbs : ℝ))) *
            ‖(∑ n ∈ Finset.range N,
              Complex.exp (2 * π * Complex.I * (h.natAbs : ℂ) * u n)) / N‖ := by
      intro h hh
      by_cases h0 : h = 0
      · subst h0
        simp only [ite_true, Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
          mul_one, intervalIntegral.integral_ofReal, hg0_mean, Complex.ofReal_zero, norm_zero,
          le_rfl]
      · simp only [h0, ite_false]
        have hfour : ∫ s in (0 : ℝ)..1, ((g0 s : ℝ) : ℂ) *
            Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) =
            ((∑ n ∈ Finset.range N, Complex.exp (-(2 * π * Complex.I * (h : ℂ) * u n))) / N) /
              (2 * π * Complex.I * (h : ℂ)) := by
          have heq : (fun s : ℝ ↦ ((g0 s : ℝ) : ℂ) *
              Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s))) =
              (fun s : ℝ ↦ ((g s : ℝ) : ℂ) * Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) -
                ((h₀ : ℂ) * Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)))) := by
            ext s; simp only [g0, Complex.ofReal_sub]; ring
          rw [heq, intervalIntegral.integral_sub]
          · have hconst0 : ∫ s in (0 : ℝ)..1, (h₀ : ℂ) *
                Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) = 0 := by
              rw [intervalIntegral.integral_const_mul]
              have hcongr' : ∫ s in (0 : ℝ)..1,
                  Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)) =
                  ∫ s in (0 : ℝ)..1, Complex.exp (2 * π * Complex.I * ((-h : ℤ) : ℂ) * s) := by
                refine intervalIntegral.integral_congr fun s _ ↦ by congr 1; push_cast; ring
              rw [hcongr', integral_exp_two_pi_I_mul_int (neg_ne_zero.2 h0), mul_zero]
            rw [hconst0, sub_zero]
            exact fourier_localDiscrepancy u hN h0
          · have hgC : IntervalIntegrable (fun s : ℝ ↦ ((g s : ℝ) : ℂ)) volume 0 1 :=
              ⟨Complex.ofRealCLM.integrable_comp (hg_int 0 1).1,
                Complex.ofRealCLM.integrable_comp (hg_int 0 1).2⟩
            exact hgC.mul_continuousOn (by fun_prop : Continuous _).continuousOn
          · exact (by fun_prop : Continuous _).intervalIntegrable _ _
        rw [hfour, norm_mul, norm_mul, norm_div]
        have hcoeff_le : ‖((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
          · have : (0 : ℝ) ≤ (|h| : ℝ) / (M + 1 : ℝ) := by positivity
            linarith
          · rw [Finset.mem_Icc] at hh
            have hle : (|h| : ℝ) ≤ (M + 1 : ℝ) := by
              have : |h| ≤ (M : ℤ) := abs_le.2 hh
              have : (|h| : ℝ) ≤ (M : ℝ) := by exact_mod_cast this
              linarith
            have : (|h| : ℝ) / (M + 1 : ℝ) ≤ 1 := (div_le_one (by positivity)).2 hle
            linarith
        have hexp_norm : ‖Complex.exp (2 * π * Complex.I * (h : ℂ) * y)‖ = 1 := by
          have : 2 * π * Complex.I * (h : ℂ) * (y : ℂ) =
              ((2 * π * (h : ℝ) * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        have hden_norm : ‖2 * π * Complex.I * (h : ℂ)‖ = 2 * π * (h.natAbs : ℝ) := by
          rw [norm_mul, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
            Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
        have hweyl_norm :
            ‖(∑ n ∈ Finset.range N, Complex.exp (-(2 * π * Complex.I * (h : ℂ) * u n))) / N‖ =
            ‖(∑ n ∈ Finset.range N,
              Complex.exp (2 * π * Complex.I * (h.natAbs : ℂ) * u n)) / N‖ := by
          rcases le_or_gt 0 h with hh0 | hh0
          · have habs : (h.natAbs : ℂ) = (h : ℂ) := by
              rw [← Int.cast_natCast, Int.natAbs_of_nonneg hh0]
            rw [habs, norm_div, norm_div]
            congr 1
            have hconj : ∑ n ∈ Finset.range N, Complex.exp (-(2 * π * Complex.I * (h : ℂ) * u n)) =
                starRingEnd ℂ (∑ n ∈ Finset.range N,
                  Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) := by
              rw [map_sum]
              refine Finset.sum_congr rfl fun n _ ↦ ?_
              have h1 : 2 * π * Complex.I * (h : ℂ) * ((u n : ℝ) : ℂ) =
                  2 * π * Complex.I * (((h : ℝ) * u n : ℝ) : ℂ) := by push_cast; ring
              rw [h1, conj_exp_two_pi_I]
            rw [hconj, Complex.norm_conj]
          · have habs : (h.natAbs : ℂ) = -(h : ℂ) := by
              rw [← Int.cast_natCast, show (h.natAbs : ℤ) = -h by omega, Int.cast_neg]
            rw [habs]
            congr 2
            refine Finset.sum_congr rfl fun n _ ↦ by congr 1; ring
        rw [hexp_norm, mul_one, hden_norm, hweyl_norm]
        calc ‖((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ)‖ *
              (‖(∑ n ∈ Finset.range N,
                Complex.exp (2 * π * Complex.I * (h.natAbs : ℂ) * u n)) / N‖ /
                (2 * π * (h.natAbs : ℝ)))
            ≤ 1 * (‖(∑ n ∈ Finset.range N,
                Complex.exp (2 * π * Complex.I * (h.natAbs : ℂ) * u n)) / N‖ /
                (2 * π * (h.natAbs : ℝ))) := by gcongr
          _ = (1 / (2 * π * (h.natAbs : ℝ))) *
              ‖(∑ n ∈ Finset.range N,
                Complex.exp (2 * π * Complex.I * (h.natAbs : ℂ) * u n)) / N‖ := by ring
    have hnorm_eq : |∫ s in (0 : ℝ)..1, g0 s * fejerKernel M (y - s)| =
        ‖((∫ s in (0 : ℝ)..1, g0 s * fejerKernel M (y - s) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm_eq, hC]
    calc ‖∑ h ∈ Finset.Icc (-(M : ℤ)) M,
            ((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ) *
              Complex.exp (2 * π * Complex.I * (h : ℂ) * y) *
              (∫ s in (0 : ℝ)..1, ((g0 s : ℝ) : ℂ) *
                Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)))‖
        ≤ ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
            ‖((1 - (|h| : ℝ) / (M + 1 : ℝ) : ℝ) : ℂ) *
              Complex.exp (2 * π * Complex.I * (h : ℂ) * y) *
              (∫ s in (0 : ℝ)..1, ((g0 s : ℝ) : ℂ) *
                Complex.exp (-(2 * π * Complex.I * (h : ℂ) * s)))‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
            if h = 0 then 0 else
              (1 / (2 * π * (h.natAbs : ℝ))) *
                ‖(∑ n ∈ Finset.range N,
                  Complex.exp (2 * π * Complex.I * (h.natAbs : ℂ) * u n)) / N‖ :=
          Finset.sum_le_sum hterm
      _ = (1 / π) * W := by
          let F : ℕ → ℝ := fun k ↦
            (1 / (2 * π * (k : ℝ))) *
              ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (k : ℂ) * u n)) / N‖
          have hpair : ∑ h ∈ Finset.Icc (-(M : ℤ)) M, (if h = 0 then (0 : ℝ) else F h.natAbs) =
              2 * ∑ k ∈ Finset.Icc 1 M, F k := by
            have hunion : Finset.Icc (-(M : ℤ)) M =
                ({0} : Finset ℤ) ∪
                  ((Finset.Icc 1 M).image (fun k : ℕ ↦ (k : ℤ)) ∪
                    (Finset.Icc 1 M).image (fun k : ℕ ↦ -(k : ℤ))) := by
              ext h
              simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
              constructor
              · intro ⟨h1, h2⟩
                rcases lt_trichotomy h 0 with hlt | rfl | hgt
                · exact Or.inr (Or.inr ⟨h.natAbs, ⟨by omega, by omega⟩, by omega⟩)
                · exact Or.inl rfl
                · exact Or.inr (Or.inl ⟨h.natAbs, ⟨by omega, by omega⟩, by omega⟩)
              · rintro (rfl | ⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩) <;> omega
            have hd1 : Disjoint ({0} : Finset ℤ)
                ((Finset.Icc 1 M).image (fun k : ℕ ↦ (k : ℤ)) ∪
                  (Finset.Icc 1 M).image (fun k : ℕ ↦ -(k : ℤ))) := by
              simp only [Finset.disjoint_singleton_left, Finset.mem_union, Finset.mem_image,
                Finset.mem_Icc]
              rintro (⟨k, ⟨hk1, _⟩, hk0⟩ | ⟨k, ⟨hk1, _⟩, hk0⟩) <;> omega
            have hd2 : Disjoint ((Finset.Icc 1 M).image (fun k : ℕ ↦ (k : ℤ)))
                ((Finset.Icc 1 M).image (fun k : ℕ ↦ -(k : ℤ))) := by
              rw [Finset.disjoint_left]
              simp only [Finset.mem_image, Finset.mem_Icc]
              rintro _ ⟨k₁, ⟨hk₁, _⟩, rfl⟩ ⟨k₂, ⟨hk₂, _⟩, heq⟩
              omega
            rw [hunion, Finset.sum_union hd1, Finset.sum_singleton]
            simp only [↓reduceIte, zero_add]
            rw [Finset.sum_union hd2,
              Finset.sum_image (fun _ _ _ _ h ↦ by exact_mod_cast h),
              Finset.sum_image (fun _ _ _ _ h ↦ by omega)]
            have h1 : ∑ k ∈ Finset.Icc 1 M,
                (if (k : ℤ) = 0 then (0 : ℝ) else F (k : ℤ).natAbs) = ∑ k ∈ Finset.Icc 1 M, F k :=
              Finset.sum_congr rfl fun k hk ↦ by
                have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
                simp [hk0]
            have h2 : ∑ k ∈ Finset.Icc 1 M,
                (if -(k : ℤ) = 0 then (0 : ℝ) else F (-(k : ℤ)).natAbs) =
                ∑ k ∈ Finset.Icc 1 M, F k :=
              Finset.sum_congr rfl fun k hk ↦ by
                have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
                simp [hk0]
            rw [h1, h2, two_mul]
          rw [hpair, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          dsimp only [F]
          ring
  set δ : ℝ := 4 / (M + 1 : ℝ)
  have hδ0 : 0 < δ := by positivity
  have hδ_half : δ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (8 : ℝ) ≤ (M + 1 : ℝ) := by exact_mod_cast hM
    linarith
  have hδ1 : δ ≤ 1 := by linarith
  have htail : (∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), fejerKernel M t) +
      (∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t) ≤ 1 / 4 := by
    have ht := fejerKernel_tail_integral_le M hδ0 hδ1
    have hval : 1 / ((M + 1 : ℝ) * δ) = 1 / 4 := by
      dsimp only [δ]
      field_simp [(show (M + 1 : ℝ) ≠ 0 by positivity)]
    linarith
  have hfejer_int_half : ∫ t in (-(1 / 2 : ℝ))..(1 / 2), fejerKernel M t = 1 := by
    have := (fejerKernel_periodic M).intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
    norm_num at this
    rw [this, integral_fejerKernel M]
  have hcore : S / 2 ≤ δ + (1 / π) * W := by
    by_contra hlt
    push Not at hlt
    set η := (S / 2 - (δ + (1 / π) * W)) / 2 with hη_def
    have hη : 0 < η := by linarith [hη_def]
    have hex : ∃ a : ℝ, S - η < |g0 a| := by
      by_contra hall
      push Not at hall
      have : S ≤ S - η := ciSup_le hall
      linarith
    obtain ⟨a, ha⟩ := hex
    have hprod_int : ∀ y : ℝ, ∀ p q : ℝ,
        IntervalIntegrable (fun t ↦ g0 (y - t) * fejerKernel M t) volume p q := fun y p q ↦ by
      have hg_sub : IntervalIntegrable (fun t ↦ g0 (y - t)) volume p q := by
        simpa only [sub_sub_cancel] using (hg0_int (y - p) (y - q)).comp_sub_left y
      exact hg_sub.mul_continuousOn (fejerKernel_continuous M).continuousOn
    have hsplit3 : ∀ f : ℝ → ℝ,
        IntervalIntegrable f volume (-(1 / 2 : ℝ)) (-(δ / 2)) →
        IntervalIntegrable f volume (-(δ / 2)) (δ / 2) →
        IntervalIntegrable f volume (δ / 2) (1 / 2 : ℝ) →
        ∫ t in (-(1 / 2 : ℝ))..(1 / 2), f t =
          (∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), f t) +
          (∫ t in (-(δ / 2))..(δ / 2), f t) +
          (∫ t in (δ / 2)..(1 / 2 : ℝ), f t) := fun f h1 h2 h3 ↦ by
      rw [intervalIntegral.integral_add_adjacent_intervals h1 h2,
        intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3]
    set T := (∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), fejerKernel M t) +
      (∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t) with hT_def
    have hmid_fejer : ∫ t in (-(δ / 2))..(δ / 2), fejerKernel M t = 1 - T := by
      have h := hsplit3 (fejerKernel M)
        ((fejerKernel_continuous M).intervalIntegrable _ _)
        ((fejerKernel_continuous M).intervalIntegrable _ _)
        ((fejerKernel_continuous M).intervalIntegrable _ _)
      linarith [hfejer_int_half, hT_def]
    have hT0 : 0 ≤ T := add_nonneg
      (intervalIntegral.integral_nonneg (by linarith) fun t _ ↦ fejerKernel_nonneg M t)
      (intervalIntegral.integral_nonneg (by linarith) fun t _ ↦ fejerKernel_nonneg M t)
    rcases le_or_gt 0 (g0 a) with hga | hga
    · rw [abs_of_nonneg hga] at ha
      set y := a + δ / 2 with hy_def
      have hmid_low : (S - η - δ) * (1 - T) ≤
          ∫ t in (-(δ / 2))..(δ / 2), g0 (y - t) * fejerKernel M t := by
        calc (S - η - δ) * (1 - T)
            = ∫ t in (-(δ / 2))..(δ / 2), (S - η - δ) * fejerKernel M t := by
              rw [intervalIntegral.integral_const_mul, hmid_fejer]
          _ ≤ ∫ t in (-(δ / 2))..(δ / 2), g0 (y - t) * fejerKernel M t := by
              refine intervalIntegral.integral_mono_on (by linarith)
                (((fejerKernel_continuous M).intervalIntegrable _ _).const_mul _)
                (hprod_int y _ _) fun t ht ↦ ?_
              have hslope := localDiscrepancy_fract_sub_ge u hN (x := a) (y := y - t)
                (by linarith [ht.2, hy_def]) (by linarith [ht.1, hy_def])
              have hlow : S - η - δ ≤ g0 (y - t) := by
                have : g0 (y - t) - g0 a = g (y - t) - g a := by simp only [g0]; ring
                linarith [ht.1, hy_def]
              exact mul_le_mul_of_nonneg_right hlow (fejerKernel_nonneg M t)
      have hleft_low : (-S) * (∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), fejerKernel M t) ≤
          ∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), g0 (y - t) * fejerKernel M t := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on (by linarith)
          (((fejerKernel_continuous M).intervalIntegrable _ _).const_mul _)
          (hprod_int y _ _) fun t _ ↦
          mul_le_mul_of_nonneg_right (abs_le.1 (hg0_le_S _)).1 (fejerKernel_nonneg M t)
      have hright_low : (-S) * (∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t) ≤
          ∫ t in (δ / 2)..(1 / 2 : ℝ), g0 (y - t) * fejerKernel M t := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on (by linarith)
          (((fejerKernel_continuous M).intervalIntegrable _ _).const_mul _)
          (hprod_int y _ _) fun t _ ↦
          mul_le_mul_of_nonneg_right (abs_le.1 (hg0_le_S _)).1 (fejerKernel_nonneg M t)
      have htot : S - η - δ - 2 * S * T ≤
          ∫ t in (-(1 / 2 : ℝ))..(1 / 2), g0 (y - t) * fejerKernel M t := by
        rw [hsplit3 _ (hprod_int y _ _) (hprod_int y _ _) (hprod_int y _ _)]
        have : 0 ≤ (η + δ) * T := by positivity
        nlinarith [hT_def]
      have hupper := (abs_le.1 (hconv_bound y)).2
      nlinarith [hη_def]
    · rw [abs_of_neg hga] at ha
      set y := a - δ / 2 with hy_def
      have hmid_high : ∫ t in (-(δ / 2))..(δ / 2), g0 (y - t) * fejerKernel M t ≤
          (-(S - η - δ)) * (1 - T) := by
        calc ∫ t in (-(δ / 2))..(δ / 2), g0 (y - t) * fejerKernel M t
            ≤ ∫ t in (-(δ / 2))..(δ / 2), (-(S - η - δ)) * fejerKernel M t := by
              refine intervalIntegral.integral_mono_on (by linarith)
                (hprod_int y _ _)
                (((fejerKernel_continuous M).intervalIntegrable _ _).const_mul _) fun t ht ↦ ?_
              have hslope := localDiscrepancy_fract_sub_ge u hN (x := y - t) (y := a)
                (by linarith [ht.1, hy_def]) (by linarith [ht.2, hy_def])
              have hhigh : g0 (y - t) ≤ -(S - η - δ) := by
                have : g0 a - g0 (y - t) = g a - g (y - t) := by simp only [g0]; ring
                linarith [ht.2, hy_def]
              exact mul_le_mul_of_nonneg_right hhigh (fejerKernel_nonneg M t)
          _ = (-(S - η - δ)) * (1 - T) := by
              rw [intervalIntegral.integral_const_mul, hmid_fejer]
      have hleft_high : ∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), g0 (y - t) * fejerKernel M t ≤
          S * (∫ t in (-(1 / 2 : ℝ))..(-(δ / 2)), fejerKernel M t) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on (by linarith)
          (hprod_int y _ _)
          (((fejerKernel_continuous M).intervalIntegrable _ _).const_mul _) fun t _ ↦
          mul_le_mul_of_nonneg_right (abs_le.1 (hg0_le_S _)).2 (fejerKernel_nonneg M t)
      have hright_high : ∫ t in (δ / 2)..(1 / 2 : ℝ), g0 (y - t) * fejerKernel M t ≤
          S * (∫ t in (δ / 2)..(1 / 2 : ℝ), fejerKernel M t) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on (by linarith)
          (hprod_int y _ _)
          (((fejerKernel_continuous M).intervalIntegrable _ _).const_mul _) fun t _ ↦
          mul_le_mul_of_nonneg_right (abs_le.1 (hg0_le_S _)).2 (fejerKernel_nonneg M t)
      have htot : ∫ t in (-(1 / 2 : ℝ))..(1 / 2), g0 (y - t) * fejerKernel M t ≤
          -(S - η - δ - 2 * S * T) := by
        rw [hsplit3 _ (hprod_int y _ _) (hprod_int y _ _) (hprod_int y _ _)]
        have : 0 ≤ (η + δ) * T := by positivity
        nlinarith [hT_def]
      have hlower := (abs_le.1 (hconv_bound y)).1
      nlinarith [hη_def]
  have h16 : 4 * δ = 16 / (M + 1 : ℝ) := by dsimp only [δ]; ring
  have h4pi : 4 * ((1 / π) * W) = (4 / π) * W := by ring
  linarith

/-- **Erdős–Turán inequality** for the extreme discrepancy `D_N(u)`. -/
theorem erdos_turan_discrepancy (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    discrepancy u N ≤
      32 / (M + 1 : ℝ) +
        (8 / π) * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) *
            ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) / N‖ := by
  have h1 := discrepancy_le_two_mul_starDiscrepancy u N
  have h2 := erdos_turan u hN M
  have hr : 2 * (16 / (M + 1 : ℝ) + (4 / π) * ∑ h ∈ Finset.Icc 1 M,
      (1 / (h : ℝ)) *
        ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) / N‖) =
      32 / (M + 1 : ℝ) + (8 / π) * ∑ h ∈ Finset.Icc 1 M,
      (1 / (h : ℝ)) *
        ‖(∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * (h : ℂ) * u n)) / N‖ := by ring
  linarith

/-- Quantitative exponential-sum bound for base-`b` digit-block frequencies, combining quantitative
Wall's theorem with the Erdős–Turán inequality. -/
theorem abs_blockCount_div_sub_le_erdos_turan {b k : ℕ} (hb : 0 < b) (x : ℝ)
    (w : Fin k → Fin b) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    |(blockCount b x w N : ℝ) / N - ((b : ℝ) ^ k)⁻¹| ≤
      32 / (M + 1 : ℝ) +
        (8 / π) * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) *
            ‖(∑ n ∈ Finset.range N,
              Complex.exp (2 * π * Complex.I * (h : ℂ) * (x * (b : ℝ) ^ n))) / N‖ := by
  have h := (abs_blockCount_div_sub_le_discrepancy hb x w N).trans
    (erdos_turan_discrepancy (fun n ↦ x * (b : ℝ) ^ n) hN M)
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast] using h

end Real
