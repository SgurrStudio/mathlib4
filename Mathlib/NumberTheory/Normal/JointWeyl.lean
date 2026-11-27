/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Interleaving
public import Mathlib.NumberTheory.Normal.QuarterCantorDecay
public import Mathlib.NumberTheory.Normal.Rational
public import Mathlib.NumberTheory.Normal.Weyl

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Imported.NormalNumbers.VisitDeviationB
import Mathlib.Imported.TauCeti.Analysis.Fourier.Monomial
import Mathlib.Imported.TauCeti.MeasureTheory.Measure.AddCircle
import Mathlib.Imported.TauCeti.NumberTheory.Equidistribution.Weyl
import Mathlib.Imported.TauCeti.Topology.Instances.AddCircle.LiftIco

/-!
# Joint normality: 2D Weyl criterion, fixed-`x` a.e. joint normality, and `GL_2(ℚ)` invariance

We establish the Fourier-analytic and rational-linear invariance theory of jointly normal pairs
`(x, y) ∈ ℝ × ℝ`:

1. **2D Weyl criterion** (`Real.isJointlyNormalIn_iff_weyl`): `(x, y)` is jointly normal in
   base `b ≥ 2` iff all nontrivial 2D exponential sums `(1 / N) ∑_{n < N} e(h₁ b^n x + h₂ b^n y)`
   tend to `0`.
2. **Unified twisted Davenport–Erdős–LeVeque second-moment lemma** and **fixed-`x` a.e. joint
   normality** (`Real.ae_isJointlyNormalIn_of_isNormalIn`,
   `Real.ae_isJointlyAbsolutelyNormal_of_isAbsolutelyNormal`): for every fixed base-`b` normal
   (resp. absolutely normal) `x`, Lebesgue-almost every `y` is jointly normal with `x`.
3. **Irrational-slope counterexample** (`Real.ae_isJointlyAbsolutelyNormal_irrational_line`,
   `Real.not_preserves_isJointlyNormalIn_irrational_linear`): for any irrational `α` and real `u`,
   a.e. `y` satisfies `IsJointlyAbsolutelyNormal (-α * y + u) y`, so `(x, y) ↦ (x + α y + c, y)`
   does not preserve joint normality.
4. **`GL_2(ℚ)` and rational affine invariance** (`Real.IsJointlyNormalIn.div_nat`,
   `Real.IsJointlyNormalIn.linear_int`, `Real.IsJointlyNormalIn.linear_rat`,
   `Real.IsJointlyNormalIn.add_ratCast`, `Real.IsJointlyNormalIn.affine_rat`).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology ComplexConjugate
open scoped ENNReal
open NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare

namespace NormalNumbers.JointRigidity

/-! ### Helper lemmas for `ee` and 2D block counts -/

private theorem ee_int_mul_add_int_mul_fract (h₁ h₂ : ℤ) (t₁ t₂ : ℝ) :
    ee ((h₁ : ℝ) * Int.fract t₁ + (h₂ : ℝ) * Int.fract t₂) =
      ee ((h₁ : ℝ) * t₁ + (h₂ : ℝ) * t₂) := by
  rw [ee_add, ee_add, ee_int_mul_fract, ee_int_mul_fract]

private theorem ee_nat_mul (n : ℕ) (t : ℝ) : ee ((n : ℝ) * t) = ee t ^ n := by
  induction n with
  | zero => simp [ee]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ee_add, ih, pow_succ]

private theorem ee_int (m : ℤ) : ee (m : ℝ) = 1 := by
  unfold ee
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

private theorem sum_range_ee_div_eq_zero {h : ℤ} {B : ℕ} (hh : h ≠ 0) (hB : h.natAbs < B) :
    ∑ p ∈ Finset.range B, ee ((h : ℝ) * (p : ℝ) / (B : ℝ)) = 0 := by
  have hBpos : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
  set r : ℂ := ee ((h : ℝ) / (B : ℝ))
  have hpow : ∀ p : ℕ, ee ((h : ℝ) * (p : ℝ) / (B : ℝ)) = r ^ p := fun p ↦ by
    rw [show (h : ℝ) * (p : ℝ) / (B : ℝ) = (p : ℝ) * ((h : ℝ) / (B : ℝ)) by ring, ee_nat_mul]
  have hrB : r ^ B = 1 := by
    rw [← ee_nat_mul, mul_div_cancel₀ _ hBne, ee_int]
  have hrne : r ≠ 1 := by
    intro hr1
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hr1
    have heq : (((h : ℝ) / (B : ℝ) : ℝ) : ℂ) = (m : ℂ) := by
      have : (2 * Real.pi * Complex.I : ℂ) * (((h : ℝ) / (B : ℝ) : ℝ) : ℂ) =
          (2 * Real.pi * Complex.I : ℂ) * (m : ℂ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hm
      exact mul_left_cancel₀ hpi this
    have heqR : (h : ℝ) / (B : ℝ) = (m : ℝ) := by exact_mod_cast heq
    have heqZ : h = m * (B : ℤ) := by
      have : (h : ℝ) = (m : ℝ) * (B : ℝ) := (div_eq_iff hBne).1 heqR
      exact_mod_cast this
    have hdvd : B ∣ h.natAbs := by
      refine ⟨m.natAbs, ?_⟩
      have := congrArg Int.natAbs heqZ
      simpa [Int.natAbs_mul, mul_comm] using this
    have hle := Nat.le_of_dvd (Int.natAbs_pos.2 hh) hdvd
    omega
  have hmul : (∑ p ∈ Finset.range B, r ^ p) * (r - 1) = 0 := by
    rw [geom_sum_mul, hrB, sub_self]
  simp_rw [hpow]
  exact (mul_eq_zero.1 hmul).resolve_right (sub_ne_zero.2 hrne)

private theorem jointBlockCount_eq_card_floor_fract {b k : ℕ} (hb : 0 < b) (x y : ℝ)
    (u v : Fin k → Fin b) (N : ℕ) :
    Real.jointBlockCount b x y u v N =
      ((Finset.range N).filter fun i ↦
        ⌊Int.fract (x * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ = Real.blockCode u ∧
        ⌊Int.fract (y * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ = Real.blockCode v).card := by
  classical
  have hmatch : ∀ (z : ℝ) (w : Fin k → Fin b) (i : ℕ),
      (∀ j : Fin k, Real.digit b z (i + j) = w j) ↔
        ⌊Int.fract (z * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ = Real.blockCode w := by
    intro z w i
    have h := Real.forall_digit_eq_iff_digit_pow (x := z) hb w i 0
    simp only [zero_mul, add_zero] at h
    have hlt : ⌊Int.fract (z * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ < b ^ k := by
      rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) (by positivity))]
      push_cast
      exact mul_lt_of_lt_one_left (by positivity) (Int.fract_lt_one _)
    rw [h, ← Real.digit_fract, Real.digit_eq_floor_mod (Int.fract_nonneg _), zero_add, pow_one,
      Nat.cast_pow, Nat.mod_eq_of_lt hlt]
  rw [Real.jointBlockCount]
  congr 1
  refine Finset.filter_congr fun i _ ↦ ?_
  rw [hmatch x u i, hmatch y v i]

private theorem isJointlyNormalIn_iff_tendsto_card_floor {b : ℕ} (hb : 0 < b) (x y : ℝ) :
    Real.IsJointlyNormalIn b x y ↔
      ∀ k p q, p < b ^ k → q < b ^ k →
        Tendsto (fun N : ℕ ↦
          (((Finset.range N).filter fun n ↦
            ⌊Int.fract (x * (b : ℝ) ^ n) * (b : ℝ) ^ k⌋₊ = p ∧
            ⌊Int.fract (y * (b : ℝ) ^ n) * (b : ℝ) ^ k⌋₊ = q).card : ℝ) / N)
          atTop (𝓝 ((b : ℝ) ^ (2 * k))⁻¹) := by
  constructor
  · intro h k p q hp hq
    obtain ⟨u, hu⟩ := Real.exists_blockCode_eq (b := b) (k := k) ⟨p, hp⟩
    obtain ⟨v, hv⟩ := Real.exists_blockCode_eq (b := b) (k := k) ⟨q, hq⟩
    have := h k u v
    simp_rw [jointBlockCount_eq_card_floor_fract hb, hu, hv] at this
    exact this
  · intro h k u v
    simp_rw [jointBlockCount_eq_card_floor_fract hb]
    exact h k _ _ (Real.blockCode u).isLt (Real.blockCode v).isLt

/-! ### Part 1: 2D Weyl Criterion -/

private theorem weyl_of_isJointlyNormalIn {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hxy : Real.IsJointlyNormalIn b x y) {h₁ h₂ : ℤ} (hne : (h₁, h₂) ≠ (0, 0)) :
    Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y)) atTop (𝓝 0) := by
  classical
  have hb0 : 0 < b := by omega
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hfl := (isJointlyNormalIn_iff_tendsto_card_floor hb0 x y).1 hxy
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := 2 * Real.pi * (|(h₁ : ℝ)| + |(h₂ : ℝ)|)
  have hM : 0 ≤ M := by positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    (max (2 * M / ε) ((max h₁.natAbs h₂.natAbs : ℕ) : ℝ)) hb1
  set B : ℕ := b ^ k
  have hBpos : 0 < B := pow_pos hb0 k
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hBk1 : 2 * M / ε < (B : ℝ) := by
    have := lt_of_le_of_lt (le_max_left _ _) hk
    exact_mod_cast this
  have hBk2 : max h₁.natAbs h₂.natAbs < B := by
    have := lt_of_le_of_lt (le_max_right _ _) hk
    exact_mod_cast this
  have hMB : M / (B : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hBR]
    rw [div_lt_iff₀ hε] at hBk1
    linarith
  -- Cell counts `S N p q`
  let S : ℕ → ℕ → ℕ → ℕ := fun N p q ↦
    ((Finset.range N).filter fun n ↦
      ⌊Int.fract (x * (b : ℝ) ^ n) * (B : ℝ)⌋₊ = p ∧
      ⌊Int.fract (y * (b : ℝ) ^ n) * (B : ℝ)⌋₊ = q).card
  let A : ℕ → ℂ := fun N ↦
    ∑ p ∈ Finset.range B, ∑ q ∈ Finset.range B,
      (((S N p q : ℝ) / N : ℝ) : ℂ) *
        ee ((h₁ : ℝ) * ((p : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((q : ℝ) / (B : ℝ)))
  -- The step-function approximation `A N` tends to `0`.
  have hA_lim : Tendsto A atTop (𝓝 0) := by
    have hlim_pq : ∀ p ∈ Finset.range B, ∀ q ∈ Finset.range B,
        Tendsto (fun N : ℕ ↦
          (((S N p q : ℝ) / N : ℝ) : ℂ) *
            ee ((h₁ : ℝ) * ((p : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((q : ℝ) / (B : ℝ))))
          atTop
          (𝓝 ((((b : ℝ) ^ (2 * k))⁻¹ : ℂ) *
            ee ((h₁ : ℝ) * ((p : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((q : ℝ) / (B : ℝ))))) := by
      intro p hp q hq
      have ht := hfl k p q (Finset.mem_range.1 hp) (Finset.mem_range.1 hq)
      have htC : Tendsto (fun N : ℕ ↦ (((S N p q : ℝ) / N : ℝ) : ℂ)) atTop
          (𝓝 ((((b : ℝ) ^ (2 * k))⁻¹ : ℝ) : ℂ)) := by
        refine (Complex.continuous_ofReal.tendsto _).comp ?_
        simpa [S, B, Nat.cast_pow] using ht
      simpa using htC.mul_const _
    have hsum_lim := tendsto_finsetSum (Finset.range B) fun p hp ↦
      tendsto_finsetSum (Finset.range B) fun q hq ↦ hlim_pq p hp q hq
    have hzero :
        (∑ p ∈ Finset.range B, ∑ q ∈ Finset.range B,
          (((b : ℝ) ^ (2 * k))⁻¹ : ℂ) *
            ee ((h₁ : ℝ) * ((p : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((q : ℝ) / (B : ℝ)))) = 0 := by
      have hfac :
          (∑ p ∈ Finset.range B, ∑ q ∈ Finset.range B,
            (((b : ℝ) ^ (2 * k))⁻¹ : ℂ) *
              ee ((h₁ : ℝ) * ((p : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((q : ℝ) / (B : ℝ)))) =
          (((b : ℝ) ^ (2 * k))⁻¹ : ℂ) *
            (∑ p ∈ Finset.range B, ee ((h₁ : ℝ) * (p : ℝ) / (B : ℝ))) *
            (∑ q ∈ Finset.range B, ee ((h₂ : ℝ) * (q : ℝ) / (B : ℝ))) := by
        simp_rw [ee_add, mul_div_assoc']
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.mul_sum]
      rw [hfac]
      by_cases hh₁ : h₁ ≠ 0
      · rw [sum_range_ee_div_eq_zero hh₁ (lt_of_le_of_lt (le_max_left _ _) hBk2),
          mul_zero, zero_mul]
      · push Not at hh₁
        have hh₂ : h₂ ≠ 0 := fun h ↦ hne (Prod.ext hh₁ h)
        rw [sum_range_ee_div_eq_zero hh₂ (lt_of_le_of_lt (le_max_right _ _) hBk2), mul_zero]
    rwa [hzero] at hsum_lim
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hA_lim (ε / 2) (half_pos hε)
  refine ⟨max N₀ 1, fun N hN ↦ ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hAN : ‖A N‖ < ε / 2 := by
    simpa [dist_zero_right] using hN₀ N (le_trans (le_max_left _ _) hN)
  -- Express `A N` as `(N : ℂ)⁻¹ * ∑ n ∈ range N, ee (h₁ * (p_n / B) + h₂ * (q_n / B))`
  let px : ℕ → ℕ := fun n ↦ ⌊Int.fract (x * (b : ℝ) ^ n) * (B : ℝ)⌋₊
  let qy : ℕ → ℕ := fun n ↦ ⌊Int.fract (y * (b : ℝ) ^ n) * (B : ℝ)⌋₊
  have hpx_lt : ∀ n, px n < B := fun n ↦ by
    rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hBR.le)]
    exact mul_lt_of_lt_one_left hBR (Int.fract_lt_one _)
  have hqy_lt : ∀ n, qy n < B := fun n ↦ by
    rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hBR.le)]
    exact mul_lt_of_lt_one_left hBR (Int.fract_lt_one _)
  have hA_eq : A N = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      ee ((h₁ : ℝ) * ((px n : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((qy n : ℝ) / (B : ℝ))) := by
    have hfib :
        ∑ n ∈ Finset.range N,
          ee ((h₁ : ℝ) * ((px n : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((qy n : ℝ) / (B : ℝ))) =
        ∑ pq ∈ Finset.range B ×ˢ Finset.range B,
          (S N pq.1 pq.2 : ℂ) *
            ee ((h₁ : ℝ) * ((pq.1 : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((pq.2 : ℝ) / (B : ℝ))) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun n ↦ (px n, qy n))
        (t := Finset.range B ×ˢ Finset.range B)
        (fun n _ ↦ Finset.mem_product.2 ⟨Finset.mem_range.2 (hpx_lt n),
          Finset.mem_range.2 (hqy_lt n)⟩)]
      refine Finset.sum_congr rfl fun pq _ ↦ ?_
      have hcongr :
          ∑ n ∈ (Finset.range N).filter (fun n ↦ (px n, qy n) = pq),
            ee ((h₁ : ℝ) * ((px n : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((qy n : ℝ) / (B : ℝ))) =
          ∑ _n ∈ (Finset.range N).filter (fun n ↦ px n = pq.1 ∧ qy n = pq.2),
            ee ((h₁ : ℝ) * ((pq.1 : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((pq.2 : ℝ) / (B : ℝ))) := by
        refine Finset.sum_congr (by ext n; simp [Prod.ext_iff]) fun n hn ↦ ?_
        have h := (Finset.mem_filter.1 hn).2
        simp only [h.1, h.2]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    rw [hfib, Finset.sum_product, Finset.mul_sum]
    simp only [A]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    push_cast
    ring
  -- Pointwise Lipschitz error bound
  have hpt : ∀ n : ℕ,
      ‖ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y) -
        ee ((h₁ : ℝ) * ((px n : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((qy n : ℝ) / (B : ℝ)))‖ ≤
        M / (B : ℝ) := by
    intro n
    have heq : ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y) =
        ee ((h₁ : ℝ) * Int.fract (x * (b : ℝ) ^ n) + (h₂ : ℝ) * Int.fract (y * (b : ℝ) ^ n)) := by
      rw [ee_int_mul_add_int_mul_fract]
      congr 1
      ring
    rw [heq]
    refine (QuarterCantorDecay.norm_cexp_sub_le _ _).trans ?_
    have hdx : |Int.fract (x * (b : ℝ) ^ n) - (px n : ℝ) / (B : ℝ)| ≤ 1 / (B : ℝ) := by
      rw [abs_le]
      have h1 : (px n : ℝ) ≤ Int.fract (x * (b : ℝ) ^ n) * (B : ℝ) :=
        Nat.floor_le (mul_nonneg (Int.fract_nonneg _) hBR.le)
      have h2 : Int.fract (x * (b : ℝ) ^ n) * (B : ℝ) < (px n : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      constructor
      · have : (px n : ℝ) / (B : ℝ) ≤ Int.fract (x * (b : ℝ) ^ n) := (div_le_iff₀ hBR).2 h1
        linarith [show (0 : ℝ) ≤ 1 / (B : ℝ) by positivity]
      · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hBR]
        linarith
    have hdy : |Int.fract (y * (b : ℝ) ^ n) - (qy n : ℝ) / (B : ℝ)| ≤ 1 / (B : ℝ) := by
      rw [abs_le]
      have h1 : (qy n : ℝ) ≤ Int.fract (y * (b : ℝ) ^ n) * (B : ℝ) :=
        Nat.floor_le (mul_nonneg (Int.fract_nonneg _) hBR.le)
      have h2 : Int.fract (y * (b : ℝ) ^ n) * (B : ℝ) < (qy n : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      constructor
      · have : (qy n : ℝ) / (B : ℝ) ≤ Int.fract (y * (b : ℝ) ^ n) := (div_le_iff₀ hBR).2 h1
        linarith [show (0 : ℝ) ≤ 1 / (B : ℝ) by positivity]
      · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hBR]
        linarith
    have hsub :
        |(h₁ : ℝ) * Int.fract (x * (b : ℝ) ^ n) + (h₂ : ℝ) * Int.fract (y * (b : ℝ) ^ n) -
          ((h₁ : ℝ) * ((px n : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((qy n : ℝ) / (B : ℝ)))| ≤
        (|(h₁ : ℝ)| + |(h₂ : ℝ)|) / (B : ℝ) := by
      rw [show (h₁ : ℝ) * Int.fract (x * (b : ℝ) ^ n) + (h₂ : ℝ) * Int.fract (y * (b : ℝ) ^ n) -
          ((h₁ : ℝ) * ((px n : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((qy n : ℝ) / (B : ℝ))) =
          (h₁ : ℝ) * (Int.fract (x * (b : ℝ) ^ n) - (px n : ℝ) / (B : ℝ)) +
          (h₂ : ℝ) * (Int.fract (y * (b : ℝ) ^ n) - (qy n : ℝ) / (B : ℝ)) by ring]
      calc _ ≤ |(h₁ : ℝ) * (Int.fract (x * (b : ℝ) ^ n) - (px n : ℝ) / (B : ℝ))| +
              |(h₂ : ℝ) * (Int.fract (y * (b : ℝ) ^ n) - (qy n : ℝ) / (B : ℝ))| := abs_add_le _ _
        _ = |(h₁ : ℝ)| * |Int.fract (x * (b : ℝ) ^ n) - (px n : ℝ) / (B : ℝ)| +
              |(h₂ : ℝ)| * |Int.fract (y * (b : ℝ) ^ n) - (qy n : ℝ) / (B : ℝ)| := by
            rw [abs_mul, abs_mul]
        _ ≤ |(h₁ : ℝ)| * (1 / (B : ℝ)) + |(h₂ : ℝ)| * (1 / (B : ℝ)) := by gcongr
        _ = (|(h₁ : ℝ)| + |(h₂ : ℝ)|) / (B : ℝ) := by ring
    calc 2 * Real.pi * _ ≤ 2 * Real.pi * ((|(h₁ : ℝ)| + |(h₂ : ℝ)|) / (B : ℝ)) := by gcongr
      _ = M / (B : ℝ) := by simp only [M]; ring
  have hdiff :
      ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y) - A N‖ ≤ M / (B : ℝ) := by
    rw [hA_eq, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, _‖
        ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            ‖ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y) -
              ee ((h₁ : ℝ) * ((px n : ℝ) / (B : ℝ)) + (h₂ : ℝ) * ((qy n : ℝ) / (B : ℝ)))‖ := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, (M / (B : ℝ)) := by
          gcongr with n; exact hpt n
      _ = M / (B : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hNR.ne', one_mul]
  rw [dist_zero_right]
  calc ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y)‖
      ≤ ‖A N‖ + ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y) - A N‖ :=
        norm_le_insert' _ _
    _ < ε / 2 + ε / 2 := add_lt_add hAN (hdiff.trans_lt hMB)
    _ = ε := add_halves ε

private theorem frontier_preimage_subset_of_continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (s : Set Y) :
    frontier (f ⁻¹' s) ⊆ f ⁻¹' (frontier s) := by
  intro x hx
  refine ⟨hf.closure_preimage_subset s hx.1, fun hint ↦ hx.2 ?_⟩
  exact interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf) hint

private theorem isJointlyNormalIn_of_weyl {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hW : ∀ h₁ h₂ : ℤ, (h₁, h₂) ≠ (0, 0) →
      Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y)) atTop (𝓝 0)) :
    Real.IsJointlyNormalIn b x y := by
  classical
  have hb0 : 0 < b := by omega
  let z : ℕ → UnitAddTorus (Fin 2) := fun n i ↦
    (((if i = 0 then x else y) * (b : ℝ) ^ n : ℝ) : UnitAddCircle)
  have hz : TauCeti.AsympEquidistributed z
      (volume : Measure (UnitAddTorus (Fin 2))).toProbabilityMeasure := by
    rw [TauCeti.weyl_criterion]
    intro k hk
    have hne : (k 0, k 1) ≠ (0, 0) := by
      intro h
      apply hk
      funext i
      fin_cases i
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    have ht := (tendsto_add_atTop_iff_nat 1).2 (hW (k 0) (k 1) hne)
    refine ht.congr fun n ↦ ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hm := TauCeti.UnitAddTorus.mFourier_coe_apply k
      (fun j : Fin 2 ↦ (if j = 0 then x else y) * (b : ℝ) ^ i)
    rw [show z i = fun j : Fin 2 ↦ (((if j = 0 then x else y) * (b : ℝ) ^ i : ℝ) : UnitAddCircle)
      from rfl, hm]
    simp only [Fin.sum_univ_two, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, ee]
    congr 1
    push_cast
    ring
  rw [isJointlyNormalIn_iff_tendsto_card_floor hb0]
  intro k p q hp hq
  set B : ℝ := (b : ℝ) ^ k
  have hB : 0 < B := by positivity
  set a₁ : ℝ := (p : ℝ) / B
  set c₁ : ℝ := ((p : ℝ) + 1) / B
  set a₂ : ℝ := (q : ℝ) / B
  set c₂ : ℝ := ((q : ℝ) + 1) / B
  have ha₁ : 0 ≤ a₁ := by positivity
  have ha₁c₁ : a₁ ≤ c₁ := div_le_div_of_nonneg_right (by linarith) hB.le
  have hc₁ : c₁ ≤ 1 := (div_le_one hB).2 (by
    change (p : ℝ) + 1 ≤ (b : ℝ) ^ k
    exact_mod_cast Nat.succ_le_of_lt hp)
  have ha₂ : 0 ≤ a₂ := by positivity
  have ha₂c₂ : a₂ ≤ c₂ := div_le_div_of_nonneg_right (by linarith) hB.le
  have hc₂ : c₂ ≤ 1 := (div_le_one hB).2 (by
    change (q : ℝ) + 1 ≤ (b : ℝ) ^ k
    exact_mod_cast Nat.succ_le_of_lt hq)
  let lift : UnitAddCircle → ℝ := fun θ ↦ (AddCircle.equivIco 1 0 θ : ℝ)
  have hlift_m : Measurable lift :=
    measurable_subtypeVal.comp (AddCircle.measurableEquivIco 1 0).measurable
  set E₁ : Set UnitAddCircle := lift ⁻¹' Ico a₁ c₁
  set E₂ : Set UnitAddCircle := lift ⁻¹' Ico a₂ c₂
  set E : Set (UnitAddTorus (Fin 2)) := Set.univ.pi ![E₁, E₂]
  have hE_eq : E = (fun θ : UnitAddTorus (Fin 2) ↦ θ 0) ⁻¹' E₁ ∩
      (fun θ : UnitAddTorus (Fin 2) ↦ θ 1) ⁻¹' E₂ := by
    ext θ
    simp only [E, Set.mem_pi, Set.mem_univ, forall_true_left, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Set.mem_inter_iff,
      Set.mem_preimage]
  have hE_meas : MeasurableSet E := by
    rw [hE_eq]
    exact ((hlift_m measurableSet_Ico).preimage (measurable_pi_apply 0)).inter
      ((hlift_m measurableSet_Ico).preimage (measurable_pi_apply 1))
  have hvol_circle : ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 →
      (volume : Measure UnitAddCircle) (lift ⁻¹' Ico a c) = ENNReal.ofReal (c - a) := by
    intro a c ha hac hc
    rw [← Measure.map_apply hlift_m measurableSet_Ico, AddCircle.map_coe_equivIco_volume 0,
      Measure.restrict_apply measurableSet_Ico, zero_add, Set.Ico_inter_Ico, max_eq_left ha,
      min_eq_left hc, Real.volume_Ico]
  have hE_vol : (volume : Measure (UnitAddTorus (Fin 2))).real E = ((b : ℝ) ^ (2 * k))⁻¹ := by
    rw [Measure.real, volume_pi]
    change (Measure.pi (fun _ : Fin 2 ↦ (volume : Measure UnitAddCircle))
      (Set.univ.pi ![E₁, E₂])).toReal = _
    rw [Measure.pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, E₁, E₂,
      hvol_circle a₁ c₁ ha₁ ha₁c₁ hc₁, hvol_circle a₂ c₂ ha₂ ha₂c₂ hc₂,
      ← ENNReal.ofReal_mul (sub_nonneg.2 ha₁c₁), ENNReal.toReal_ofReal
        (mul_nonneg (sub_nonneg.2 ha₁c₁) (sub_nonneg.2 ha₂c₂))]
    have h1 : c₁ - a₁ = B⁻¹ := by simp only [a₁, c₁]; rw [← sub_div, add_sub_cancel_left, one_div]
    have h2 : c₂ - a₂ = B⁻¹ := by simp only [a₂, c₂]; rw [← sub_div, add_sub_cancel_left, one_div]
    rw [h1, h2, ← mul_inv, ← sq, show B ^ 2 = (b : ℝ) ^ (2 * k) by
      simp only [B]; rw [← pow_mul, mul_comm]]
  have hfront_circle : ∀ a c : ℝ, 0 ≤ a → c ≤ 1 →
      (volume : Measure UnitAddCircle) (frontier (lift ⁻¹' Ico a c)) = 0 := by
    intro a c ha hc
    refine measure_mono_null (AddCircle.frontier_preimage_equivIco_Ico_subset ha (b := c)
      (by linarith)) ?_
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton _) (measure_singleton _)
  have hfront : (volume : Measure (UnitAddTorus (Fin 2))) (frontier E) = 0 := by
    have hsub : frontier E ⊆
        (fun θ : UnitAddTorus (Fin 2) ↦ θ 0) ⁻¹' (frontier E₁) ∪
        (fun θ : UnitAddTorus (Fin 2) ↦ θ 1) ⁻¹' (frontier E₂) := by
      rw [hE_eq]
      refine (frontier_inter_subset _ _).trans (Set.union_subset ?_ ?_)
      · exact Set.inter_subset_left.trans
          ((frontier_preimage_subset_of_continuous
            (continuous_apply (0 : Fin 2) : Continuous fun θ : UnitAddTorus (Fin 2) ↦ θ 0) E₁).trans
            Set.subset_union_left)
      · exact Set.inter_subset_right.trans
          ((frontier_preimage_subset_of_continuous
            (continuous_apply (1 : Fin 2) : Continuous fun θ : UnitAddTorus (Fin 2) ↦ θ 1) E₂).trans
            Set.subset_union_right)
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · have h0 : (fun θ : UnitAddTorus (Fin 2) ↦ θ 0) ⁻¹' (frontier E₁) =
          Set.univ.pi ![frontier E₁, Set.univ] := by
        ext θ; simp [Fin.forall_fin_two]
      rw [h0, volume_pi, Measure.pi_pi, Fin.prod_univ_two]
      simp [E₁, hfront_circle a₁ c₁ ha₁ hc₁]
    · have h1 : (fun θ : UnitAddTorus (Fin 2) ↦ θ 1) ⁻¹' (frontier E₂) =
          Set.univ.pi ![Set.univ, frontier E₂] := by
        ext θ; simp [Fin.forall_fin_two]
      rw [h1, volume_pi, Measure.pi_pi, Fin.prod_univ_two]
      simp [E₂, hfront_circle a₂ c₂ ha₂ hc₂]
  have hfreq := hz.tendsto_frequency hE_meas (by simpa using hfront)
  rw [Measure.coe_toProbabilityMeasure, hE_vol] at hfreq
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hfreq.congr fun n ↦ ?_
  congr 3
  refine Finset.filter_congr fun i _ ↦ ?_
  rw [hE_eq]
  simp only [Set.mem_inter_iff, Set.mem_preimage, E₁, E₂, lift, z, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, AddCircle.coe_equivIco_mk_apply, div_one, mul_one,
    a₁, c₁, a₂, c₂]
  rw [Real.floor_mul_eq_iff_mem_Ico (Int.fract_nonneg _) hB p,
    Real.floor_mul_eq_iff_mem_Ico (Int.fract_nonneg _) hB q]

end NormalNumbers.JointRigidity

namespace Real

open NormalNumbers.DecayAeNormal NormalNumbers.JointRigidity

/-- **2D Weyl criterion for joint normality**: `(x, y)` is jointly normal in base `b ≥ 2` iff
all nontrivial 2D Weyl means `(1 / N) ∑_{n < N} e(h₁ b^n x + h₂ b^n y)` tend to `0`. -/
theorem isJointlyNormalIn_iff_weyl {b : ℕ} (hb : 2 ≤ b) (x y : ℝ) :
    IsJointlyNormalIn b x y ↔ ∀ h₁ h₂ : ℤ, (h₁, h₂) ≠ (0, 0) →
      Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y)) atTop (𝓝 0) :=
  ⟨fun h _ _ hne ↦ weyl_of_isJointlyNormalIn hb h hne, isJointlyNormalIn_of_weyl hb⟩

end Real

/-! ### Part 2: Unified twisted second-moment lemma, fixed-`x` a.e. joint normality, and
irrational-slope counterexample -/

namespace NormalNumbers.JointRigidity

open DecayAeNormal VisitDeviationB

/-- Lacunary decay bound with an arbitrary nonzero real frequency `lam`. -/
theorem decay_at_diff_real {b : ℕ} (hb : 2 ≤ b) {C δ lam : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hlam : lam ≠ 0) {m n : ℕ} (hmn : m ≠ n) :
    C * |lam * ((b : ℝ) ^ n - (b : ℝ) ^ m)| ^ (-δ) ≤
      C * |lam| ^ (-δ) * 2 ^ δ * ((b : ℝ) ^ (-δ / 2)) ^ n * ((b : ℝ) ^ (-δ / 2)) ^ m := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hlam0 : 0 < |lam| := abs_pos.2 hlam
  have hd : (b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) / 2 ≤ |(b : ℝ) ^ n - (b : ℝ) ^ m| := by
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · exact (b_pow_sub_ge b hb hlt).trans (le_abs_self _)
    · have := b_pow_sub_ge b hb hlt
      rw [add_comm m n] at this
      rw [abs_sub_comm]; exact this.trans (le_abs_self _)
  have hpos : (0 : ℝ) < (b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) / 2 := by positivity
  rw [abs_mul, Real.mul_rpow hlam0.le (abs_nonneg _)]
  have hmono := Real.rpow_le_rpow_of_nonpos hpos hd (by linarith : -δ ≤ 0)
  have hCL : 0 ≤ C * |lam| ^ (-δ) := by positivity
  calc C * (|lam| ^ (-δ) * |(b : ℝ) ^ n - (b : ℝ) ^ m| ^ (-δ))
      = C * |lam| ^ (-δ) * |(b : ℝ) ^ n - (b : ℝ) ^ m| ^ (-δ) := by ring
    _ ≤ C * |lam| ^ (-δ) * ((b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) / 2) ^ (-δ) :=
        mul_le_mul_of_nonneg_left hmono hCL
    _ = C * |lam| ^ (-δ) * 2 ^ δ * ((b : ℝ) ^ (-δ / 2)) ^ n * ((b : ℝ) ^ (-δ / 2)) ^ m := by
        rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
        have hsum : (b : ℝ) ^ ((((n + m : ℕ) : ℝ) / 2) * -δ) =
            (b : ℝ) ^ (-δ / 2 * (n : ℝ)) * (b : ℝ) ^ (-δ / 2 * (m : ℝ)) := by
          rw [← Real.rpow_add hb0]
          congr 1; push_cast; ring
        rw [hsum]; ring

/-- **Twisted second moment bound** under polynomial Fourier decay: adding any deterministic
phase `θ n` leaves the `O(N)` second-moment bound intact. -/
theorem twisted_second_moment_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {b : ℕ} (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (θ : ℕ → ℝ) {lam : ℝ} (hlam : lam ≠ 0) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (θ k + lam * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ ≤
      N + C * |lam| ^ (-δ) * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2 := by
  set s : ℝ := (b : ℝ) ^ (-δ / 2) with hs
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos (by linarith) _).le
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hint : ∀ (c ξ : ℝ), Integrable (fun ω ↦ ee (c + ξ * G ω)) μ := fun c ξ ↦
    Integrable.of_bound
      ((measurable_ee.comp (measurable_const.add (hG.const_mul ξ))).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω ↦ (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (θ k + lam * (b : ℝ) ^ k * G ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((θ n - θ m) + (lam * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k ↦ θ k + lam * (b : ℝ) ^ k * G ω)]
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (θ k + lam * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((θ n - θ m) + (lam * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂μ := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ ↦ integrable_finsetSum _ fun m _ ↦ hint _ _]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [integral_finsetSum _ fun m _ ↦ hint _ _]
  have hterm : ∀ n m : ℕ,
      ‖∫ ω, ee ((θ n - θ m) + (lam * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂μ‖ ≤
        (if n = m then 1 else 0) + C * |lam| ^ (-δ) * 2 ^ δ * s ^ n * s ^ m := by
    intro n m
    have hK : 0 ≤ C * |lam| ^ (-δ) * 2 ^ δ * s ^ n * s ^ m := by positivity
    split_ifs with hnm
    · refine (norm_integral_le_of_norm_le_const (C := 1)
        (Eventually.of_forall fun ω ↦ (norm_ee _).le)).trans ?_
      simp; linarith
    · have hpull : ∫ ω, ee ((θ n - θ m) + (lam * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂μ =
          ee (θ n - θ m) * ∫ ω, ee ((lam * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂μ := by
        rw [← integral_const_mul]
        congr 1; funext ω; exact ee_add _ _
      rw [hpull, norm_mul, norm_ee, one_mul, zero_add]
      have hne : lam * ((b : ℝ) ^ n - (b : ℝ) ^ m) ≠ 0 := by
        refine mul_ne_zero hlam (sub_ne_zero.2 fun he ↦ hnm ?_)
        exact Nat.pow_right_injective hb (by exact_mod_cast he)
      exact (hdec _ hne).trans (decay_at_diff_real hb hC hδ hlam (Ne.symm hnm))
  have hgeo : ∑ n ∈ Finset.range N, s ^ n ≤ (1 - s)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hs0 hs1]
    exact Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) (summable_geometric_of_lt_one hs0 hs1)
  have hreal : ∫ ω, ‖∑ k ∈ Finset.range N, ee (θ k + lam * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ((if n = m then (1 : ℝ) else 0) + C * |lam| ^ (-δ) * 2 ^ δ * s ^ n * s ^ m) := by
    have := congrArg Complex.re hI
    rw [Complex.ofReal_re] at this
    rw [this]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum fun n _ ↦ (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun m _ ↦ hterm n m
  have hsum : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ((if n = m then (1 : ℝ) else 0) + C * |lam| ^ (-δ) * 2 ^ δ * s ^ n * s ^ m) =
      N + C * |lam| ^ (-δ) * 2 ^ δ * (∑ n ∈ Finset.range N, s ^ n) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range]
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, Finset.sum_boole]
    rw [Finset.filter_true_of_mem (fun x hx ↦ Finset.mem_range.1 hx), Finset.card_range]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun m _ ↦ by ring
  rw [hsum] at hreal
  refine hreal.trans ?_
  have : 0 ≤ ∑ n ∈ Finset.range N, s ^ n := Finset.sum_nonneg fun _ _ ↦ by positivity
  have h2 : (2 : ℝ) ^ (-δ / 2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs2 : s ≤ (2 : ℝ) ^ (-δ / 2) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hbR (by linarith)
  have hinv : (1 - s)⁻¹ ≤ (1 - (2 : ℝ) ^ (-δ / 2))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h1 : ∑ n ∈ Finset.range N, s ^ n ≤ (1 - (2 : ℝ) ^ (-δ / 2))⁻¹ := hgeo.trans hinv
  gcongr

/-- **Twisted Davenport–Erdős–LeVeque**: polynomial Fourier decay of `G_* μ` implies that for
every base `b ≥ 2`, nonzero real `lam`, and deterministic phase sequence `θ`, the twisted Weyl
means `(1 / N) ∑_{n < N} e(θ n + lam b^n G ω)` tend to `0` for `μ`-a.e. `ω`. -/
theorem ae_tendsto_twisted_weyl_of_decay {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {b : ℕ} (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (θ : ℕ → ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ *
      ∑ n ∈ Finset.range N, ee (θ n + lam * (b : ℝ) ^ n * G ω)) atTop (𝓝 0) := by
  set Z : ℕ → Ω → ℂ := fun k ω ↦ ee (θ k + lam * (b : ℝ) ^ k * G ω)
  have hZm : ∀ k, Measurable (Z k) := fun k ↦
    measurable_ee.comp (measurable_const.add (hG.const_mul _))
  have hZb : ∀ k ω, ‖Z k ω‖ ≤ 1 := fun k ω ↦ (norm_ee _).le
  set S : ℕ → Ω → ℂ := fun N ω ↦ ∑ k ∈ Finset.range N, Z k ω
  have hSm : ∀ N, Measurable (S N) := fun N ↦ Finset.measurable_sum _ fun k _ ↦ hZm k
  have hSb : ∀ N ω, ‖S N ω‖ ≤ N := fun N ω ↦ (norm_sum_le _ _).trans (by
    simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) ↦ hZb k ω)
  set K : ℝ := C * |lam| ^ (-δ) * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2
  have hK : 0 ≤ K := by
    have : (2 : ℝ) ^ (-δ / 2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : 0 < 1 - (2 : ℝ) ^ (-δ / 2) := by linarith
    positivity
  set n : ℕ → ℕ := fun j ↦ (j + 1) ^ 2
  set f : ℕ → Ω → ℝ := fun j ω ↦ ‖S (n j) ω‖ ^ 2 / ((n j : ℝ)) ^ 2
  have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω ↦ by positivity
  have hfm : ∀ j, Measurable (f j) := fun j ↦ ((hSm _).norm.pow_const 2).div_const _
  have hfi : ∀ j, Integrable (f j) μ := fun j ↦
    Integrable.of_bound (hfm j).aestronglyMeasurable 1 (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_of_nonneg (hf0 j ω)]
      have hpos' : (0 : ℝ) < n j := by simp only [n]; positivity
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hSb _ ω) 2)
  have hfI : ∀ j, ∫ ω, f j ω ∂μ ≤ (1 + K) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) := by
    intro j
    have hpos' : (0 : ℝ) < n j := by simp only [n]; positivity
    have hn1 : (1 : ℝ) ≤ n j := by
      simp only [n]; exact_mod_cast Nat.one_le_pow 2 (j + 1) (by omega)
    simp only [f]
    rw [integral_div, div_le_iff₀ (by positivity)]
    have hm := twisted_second_moment_le μ hb G hG hC hδ hdec θ hlam (n j)
    calc ∫ ω, ‖S (n j) ω‖ ^ 2 ∂μ ≤ (n j : ℝ) + K := hm
      _ ≤ (1 + K) * (n j : ℝ) := by nlinarith
      _ = (1 + K) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) * ((n j : ℝ)) ^ 2 := by
        simp only [n]; push_cast; field_simp
  have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun j ↦ (hfm j).ennreal_ofReal.aemeasurable]
    have hs : Summable fun j : ℕ ↦ (1 + K) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) :=
      ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left _
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, (1 + K) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) hs]
    refine tsum_le_tsum fun j ↦ ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
    exact ENNReal.ofReal_le_ofReal (hfI j)
  have hae := ae_lt_top' (AEMeasurable.tsum fun j ↦ (hfm j).ennreal_ofReal.aemeasurable) hlin
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun j ↦ ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun j ↦ f j ω) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
  have h3 : Tendsto (fun j : ℕ ↦ S (j ^ 2) ω / ((j ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1, tendsto_zero_iff_norm_tendsto_zero]
    have hsqrt := h2.sqrt
    rw [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr fun j ↦ ?_
    simp only [f, n, norm_div, Complex.norm_natCast]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (by positivity)]
  have h4 := tendsto_of_tendsto_sq (fun k ↦ Z k ω) (fun k ↦ hZb k ω) h3
  exact h4.congr fun N ↦ by rw [div_eq_inv_mul]

/-- Fourier decay of Lebesgue measure on `[0, 1)`: `‖∫_{Ico 0 1} e(ξ y) dy‖ ≤ 1 / |ξ|`. -/
theorem norm_integral_Ico_ee_le {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖∫ y, ee (ξ * y) ∂(volume.restrict (Ico (0 : ℝ) 1))‖ ≤ 1 * |ξ| ^ (-1 : ℝ) := by
  have hIco : ∫ y, ee (ξ * y) ∂(volume.restrict (Ico (0 : ℝ) 1)) =
      ∫ y in (0 : ℝ)..1, ee (ξ * y) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc, intervalIntegral.integral_of_le zero_le_one]
  rw [hIco]
  set c : ℂ := 2 * Real.pi * Complex.I * (ξ : ℂ)
  have hc : c ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hξ
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ Complex.exp (c * (t : ℂ)) / c) (ee (ξ * y)) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ ↦ c * (t : ℂ)) c y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul c
    have h2 : HasDerivAt (fun t : ℝ ↦ Complex.exp (c * (t : ℂ)))
        (Complex.exp (c * (y : ℂ)) * c) y := h1.cexp
    refine (h2.div_const c).congr_deriv ?_
    rw [mul_div_cancel_right₀ _ hc]
    unfold ee; congr 1; simp only [c]; push_cast; ring
  have hint : IntervalIntegrable (fun y : ℝ ↦ ee (ξ * y)) volume 0 1 := by
    have hc' : Continuous fun y : ℝ ↦ ee (ξ * y) :=
      Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
    exact hc'.intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
  have h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = ee ξ := by
    unfold ee; simp only [c]; push_cast; ring_nf
  rw [← sub_div, h0, h1, norm_div]
  have hnum : ‖ee ξ - 1‖ ≤ 2 := by
    calc ‖ee ξ - 1‖ ≤ ‖ee ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_ee, norm_one]; norm_num
  have hden : ‖c‖ = 2 * Real.pi * |ξ| := by
    simp only [c, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Real.norm_eq_abs, mul_one, abs_of_pos Real.pi_pos]
  rw [hden, one_mul, Real.rpow_neg_one]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have hξpos : 0 < |ξ| := abs_pos.2 hξ
  calc ‖ee ξ - 1‖ / (2 * Real.pi * |ξ|) ≤ 2 / (2 * Real.pi * |ξ|) := by gcongr
    _ = 1 / (Real.pi * |ξ|) := by field_simp
    _ ≤ 1 / (1 * |ξ|) := by gcongr
    _ = |ξ|⁻¹ := by rw [one_mul, one_div]

private theorem ae_of_forall_int_ae_restrict_Ico {P : ℝ → Prop}
    (h : ∀ m : ℤ, ∀ᵐ t ∂(volume.restrict (Ico (0 : ℝ) 1)), P (t + m)) :
    ∀ᵐ y ∂(volume : Measure ℝ), P y := by
  rw [ae_iff]
  have hnull : ∀ m : ℤ,
      (volume : Measure ℝ)
        ((fun y : ℝ ↦ y + (-m : ℝ)) ⁻¹' {t : ℝ | ¬(t ∈ Ico (0 : ℝ) 1 → P (t + m))}) = 0 := by
    intro m
    have hm := h m
    rw [ae_restrict_iff' measurableSet_Ico, ae_iff] at hm
    exact (measurePreserving_add_right volume (-m : ℝ)).quasiMeasurePreserving.preimage_null hm
  refine measure_mono_null
    (t := ⋃ m : ℤ, (fun y : ℝ ↦ y + (-m : ℝ)) ⁻¹' {t : ℝ | ¬(t ∈ Ico (0 : ℝ) 1 → P (t + m))})
    ?_ (measure_iUnion_null hnull)
  intro y hy
  simp only [mem_iUnion, mem_preimage, mem_ofPred_eq, not_imp]
  refine ⟨⌊y⌋, ?_, fun hP ↦ hy ?_⟩
  · rw [← sub_eq_add_neg]
    exact ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  · simpa using hP

end NormalNumbers.JointRigidity

namespace Real

open NormalNumbers.DecayAeNormal NormalNumbers.JointRigidity

/-- **Fixed-`x` almost-everywhere joint normality**: for every fixed `x` normal in base `b ≥ 2`,
Lebesgue-almost every `y : ℝ` is jointly normal with `x` in base `b`. -/
theorem ae_isJointlyNormalIn_of_isNormalIn {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : IsNormalIn b x) :
    ∀ᵐ y ∂(volume : Measure ℝ), IsJointlyNormalIn b x y := by
  have hμ : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := ⟨by simp⟩
  have h0 : ∀ᵐ y ∂(volume.restrict (Ico (0 : ℝ) 1)), IsJointlyNormalIn b x y := by
    have hall : ∀ᵐ y ∂(volume.restrict (Ico (0 : ℝ) 1)),
        ∀ h₁ h₂ : ℤ, (h₁, h₂) ≠ (0, 0) →
          Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
            ee ((h₁ : ℝ) * (b : ℝ) ^ n * x + (h₂ : ℝ) * (b : ℝ) ^ n * y)) atTop (𝓝 0) := by
      rw [ae_all_iff]; intro h₁
      rw [ae_all_iff]; intro h₂
      by_cases hh₂ : h₂ = 0
      · subst hh₂
        by_cases hh₁ : h₁ = 0
        · subst hh₁; exact Eventually.of_forall fun _ h ↦ absurd rfl h
        · have hxW := (isNormalIn_iff_tendsto_weylSum hb).1 hx h₁ hh₁
          refine Eventually.of_forall fun y _ ↦ hxW.congr fun N ↦ ?_
          rw [div_eq_inv_mul]
          congr 1
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          unfold ee
          congr 1
          push_cast; ring
      · have hlam : (h₂ : ℝ) ≠ 0 := by exact_mod_cast hh₂
        have hae := ae_tendsto_twisted_weyl_of_decay (volume.restrict (Ico (0 : ℝ) 1)) hb
          id measurable_id one_pos one_pos
          (fun ξ hξ ↦ by simpa using norm_integral_Ico_ee_le hξ)
          (fun n ↦ (h₁ : ℝ) * (b : ℝ) ^ n * x) hlam
        filter_upwards [hae] with y hy _
        exact hy
    filter_upwards [hall] with y hy
    exact (isJointlyNormalIn_iff_weyl hb x y).2 hy
  refine ae_of_forall_int_ae_restrict_Ico fun m ↦ ?_
  filter_upwards [h0] with y hy
  exact (isJointlyNormalIn_add_intCast_right_iff m).2 hy

/-- **Fixed-`x` almost-everywhere joint absolute normality**: for every fixed absolutely normal `x`,
Lebesgue-almost every `y : ℝ` is jointly absolutely normal with `x`. -/
theorem ae_isJointlyAbsolutelyNormal_of_isAbsolutelyNormal {x : ℝ} (hx : IsAbsolutelyNormal x) :
    ∀ᵐ y ∂(volume : Measure ℝ), IsJointlyAbsolutelyNormal x y := by
  simp only [IsJointlyAbsolutelyNormal]
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · exact (ae_isJointlyNormalIn_of_isNormalIn hb (hx b hb)).mono fun _ h _ ↦ h
  · exact Eventually.of_forall fun _ h ↦ absurd h hb

/-- **Irrational-slope counterexample**: for every irrational `α` and real `u`, Lebesgue-almost
every `y : ℝ` satisfies `IsJointlyAbsolutelyNormal (-α * y + u) y`. -/
theorem ae_isJointlyAbsolutelyNormal_irrational_line {α : ℝ} (hα : Irrational α) (u : ℝ) :
    ∀ᵐ y ∂(volume : Measure ℝ), IsJointlyAbsolutelyNormal (-α * y + u) y := by
  have hμ : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := ⟨by simp⟩
  have hunit : ∀ u' : ℝ, ∀ᵐ y ∂(volume.restrict (Ico (0 : ℝ) 1)),
      IsJointlyAbsolutelyNormal (-α * y + u') y := by
    intro u'
    simp only [IsJointlyAbsolutelyNormal]
    rw [ae_all_iff]; intro b
    by_cases hb : 2 ≤ b
    · have hall : ∀ᵐ y ∂(volume.restrict (Ico (0 : ℝ) 1)),
          ∀ h₁ h₂ : ℤ, (h₁, h₂) ≠ (0, 0) →
            Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
              ee ((h₁ : ℝ) * (b : ℝ) ^ n * (-α * y + u') + (h₂ : ℝ) * (b : ℝ) ^ n * y))
              atTop (𝓝 0) := by
        rw [ae_all_iff]; intro h₁
        rw [ae_all_iff]; intro h₂
        by_cases hne : (h₁, h₂) = (0, 0)
        · exact Eventually.of_forall fun _ h ↦ absurd hne h
        · have hlam : (h₂ : ℝ) - (h₁ : ℝ) * α ≠ 0 := by
            intro h0
            by_cases hh₁ : h₁ = 0
            · subst hh₁
              have hh₂ : h₂ ≠ 0 := fun h ↦ hne (Prod.ext rfl h)
              simp [hh₂] at h0
            · apply hα.ne_rat ((h₂ : ℚ) / (h₁ : ℚ))
              have hh₁' : (h₁ : ℝ) ≠ 0 := by exact_mod_cast hh₁
              push_cast
              rw [eq_div_iff hh₁']
              linarith
          have hae := ae_tendsto_twisted_weyl_of_decay (volume.restrict (Ico (0 : ℝ) 1)) hb
            id measurable_id one_pos one_pos
            (fun ξ hξ ↦ by simpa using norm_integral_Ico_ee_le hξ)
            (fun n ↦ (h₁ : ℝ) * (b : ℝ) ^ n * u') hlam
          filter_upwards [hae] with y hy _
          refine hy.congr fun N ↦ ?_
          congr 1
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          congr 1; simp only [id]; ring
      filter_upwards [hall] with y hy _
      exact (isJointlyNormalIn_iff_weyl hb _ _).2 hy
    · exact Eventually.of_forall fun _ h ↦ absurd h hb
  refine ae_of_forall_int_ae_restrict_Ico fun m ↦ ?_
  filter_upwards [hunit (u - α * (m : ℝ))] with t ht
  intro b hb
  have h1 : -α * (t + (m : ℝ)) + u = -α * t + (u - α * (m : ℝ)) := by ring
  rw [h1, isJointlyNormalIn_add_intCast_right_iff m]
  exact ht b hb

/-- An irrational-slope shear `(x, y) ↦ (x + α * y + c, y)` does not preserve joint normality. -/
theorem not_preserves_isJointlyNormalIn_irrational_linear {b : ℕ} (hb : 2 ≤ b)
    {α : ℝ} (hα : Irrational α) (c : ℝ) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x + α * y + c) y := by
  intro hpres
  obtain ⟨y, hy⟩ := (ae_isJointlyAbsolutelyNormal_irrational_line hα (-c)).exists
  have h0 := (hpres (-α * y + (-c)) y (hy b hb)).left hb
  rw [show -α * y + -c + α * y + c = 0 by ring] at h0
  exact (h0.irrational hb).ne_zero rfl

end Real

/-! ### Part 3: `GL_2(ℚ)` and rational affine invariance of joint normality -/

namespace NormalNumbers.JointRigidity

private theorem jointBlockCount_eq_card_blockCodeAt {b k : ℕ} (hb : 0 < b) (x y : ℝ)
    (u v : Fin k → Fin b) (N : ℕ) :
    Real.jointBlockCount b x y u v N =
      ((Finset.range N).filter fun i ↦
        Real.blockCodeAt b k x i = ((Real.blockCode u : ℕ) : ℤ) ∧
        Real.blockCodeAt b k y i = ((Real.blockCode v : ℕ) : ℤ)).card := by
  rw [jointBlockCount_eq_card_floor_fract hb]
  refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
  rw [Real.blockCodeAt_eq hb, Real.blockCodeAt_eq hb, Nat.cast_inj, Nat.cast_inj]

private theorem tendsto_card_blockCodeAt_joint {b : ℕ} (hb : 0 < b) {x y : ℝ}
    (h : Real.IsJointlyNormalIn b x y) (k : ℕ) {p q : ℕ} (hp : p < b ^ k) (hq : q < b ^ k) :
    Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦
        Real.blockCodeAt b k x i = (p : ℤ) ∧ Real.blockCodeAt b k y i = (q : ℤ)).card : ℝ) / N)
      atTop (𝓝 ((b : ℝ) ^ (2 * k))⁻¹) := by
  convert (isJointlyNormalIn_iff_tendsto_card_floor hb x y).1 h k p q hp hq using 4 with N
  refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
  rw [Real.blockCodeAt_eq hb, Real.blockCodeAt_eq hb, Nat.cast_inj, Nat.cast_inj]

private theorem div_nat_blockCodeAt_mem {b D : ℕ} (hb : 0 < b) (hD : 0 < D) (z : ℝ)
    (k V i : ℕ) (hi : Real.blockCodeAt b k (z / D) i = (V : ℤ)) :
    ∃ j ∈ (Finset.range D).image (fun t ↦ (D * V + t) % b ^ k),
      Real.blockCodeAt b k z i = (j : ℤ) := by
  set B := b ^ k
  have hB : (0 : ℤ) < B := by exact_mod_cast pow_pos hb k
  set G := ⌊z * (b : ℝ) ^ i * (B : ℝ)⌋
  have hcode : Real.blockCodeAt b k (z / D) i = G / D % B := by
    rw [Real.blockCodeAt, show z / D * (b : ℝ) ^ i * ((b ^ k : ℕ) : ℝ) =
      z * (b : ℝ) ^ i * (B : ℝ) / D by ring, Int.floor_div_natCast]
  rw [hcode] at hi
  have ht0 : 0 ≤ G % (D : ℤ) := Int.emod_nonneg _ (by omega)
  have htm : G % (D : ℤ) < D := Int.emod_lt_of_pos _ (by omega)
  refine ⟨(D * V + (G % (D : ℤ)).toNat) % B,
    Finset.mem_image.2 ⟨(G % (D : ℤ)).toNat, Finset.mem_range.2 (by omega), rfl⟩, ?_⟩
  have h1 := Int.emod_add_mul_ediv G D
  have h2 := Int.emod_add_mul_ediv (G / D) B
  rw [hi] at h2
  generalize G / D = Q at h1 h2
  generalize Q / B = l at h2
  change G % ((b ^ k : ℕ) : ℤ) = _
  generalize G % (D : ℤ) = t at h1 ht0 htm ⊢
  have hG : G = (D * V + t) + B * (D * l) := by linear_combination -h1 - D * h2
  rw [hG, Int.add_mul_emod_self_left]
  push_cast
  rw [Int.toNat_of_nonneg ht0]

end NormalNumbers.JointRigidity

namespace Real

open NormalNumbers.DecayAeNormal NormalNumbers.JointRigidity

/-- Dividing both coordinates of a base-`b` jointly normal pair by a positive integer preserves
joint normality in base `b`. -/
theorem IsJointlyNormalIn.div_nat {b : ℕ} (hb : 2 ≤ b) {x y : ℝ} {D : ℕ} (hD : 0 < D)
    (h : IsJointlyNormalIn b x y) : IsJointlyNormalIn b (x / D) (y / D) := by
  classical
  have hb0 : 0 < b := by omega
  have hb2 : 2 ≤ b ^ 2 := by nlinarith
  rw [isJointlyNormalIn_iff_isNormalIn_interleave hb, ← isNormalIn_pow_iff hb (r := 2) (by omega)]
  refine isNormalIn_of_eventually_le hb2 (C := ((D * D : ℕ) : ℝ)) fun k w ε hε ↦ ?_
  let u : Fin k → Fin b := fun j ↦
    ⟨(w j : ℕ) / b, Nat.div_lt_of_lt_mul (by rw [← sq]; exact (w j).isLt)⟩
  let v : Fin k → Fin b := fun j ↦ ⟨(w j : ℕ) % b, Nat.mod_lt _ hb0⟩
  have hcnt : ∀ N, blockCount (b ^ 2) (interleave b (x / D) (y / D)) w N =
      jointBlockCount b (x / D) (y / D) u v N := fun N ↦ by
    simp only [blockCount, jointBlockCount]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ ↦ ?_
    rw [← forall_and]
    refine forall_congr' fun j ↦ ?_
    rw [digit_sq_interleave hb (x / D) (y / D) (i + j)]
    have hw : (w j : ℕ) = b * u j + v j := (Nat.div_add_mod (w j : ℕ) b).symm
    rw [hw]
    constructor
    · intro h'
      have hq : (b * digit b (x / D) (i + j) + digit b (y / D) (i + j)) / b =
          (b * u j + v j) / b := congrArg (· / b) h'
      have hr : (b * digit b (x / D) (i + j) + digit b (y / D) (i + j)) % b =
          (b * u j + v j) % b := congrArg (· % b) h'
      rw [Nat.mul_add_div hb0, Nat.mul_add_div hb0, Nat.div_eq_of_lt (digit_lt hb0 _ _),
        Nat.div_eq_of_lt (v j).isLt, add_zero, add_zero] at hq
      rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (digit_lt hb0 _ _),
        Nat.mod_eq_of_lt (v j).isLt] at hr
      exact ⟨hq, hr⟩
    · rintro ⟨h1, h2⟩; rw [h1, h2]
  set S₁ : Finset ℕ := (Finset.range D).image (fun t ↦ (D * (blockCode u : ℕ) + t) % b ^ k)
  set S₂ : Finset ℕ := (Finset.range D).image (fun t ↦ (D * (blockCode v : ℕ) + t) % b ^ k)
  set S : Finset (ℕ × ℕ) := S₁ ×ˢ S₂
  have hS_card : S.card ≤ D * D := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul (Finset.card_image_le.trans (by simp))
      (Finset.card_image_le.trans (by simp))
  have hS_lt : ∀ pq ∈ S, pq.1 < b ^ k ∧ pq.2 < b ^ k := by
    intro pq hpq
    simp only [S, S₁, S₂, Finset.mem_product, Finset.mem_image] at hpq
    obtain ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ := hpq
    rw [← h1, ← h2]
    exact ⟨Nat.mod_lt _ (pow_pos hb0 k), Nat.mod_lt _ (pow_pos hb0 k)⟩
  set δ : ℝ := ε / ((D * D : ℕ) + 1)
  have hδ : 0 < δ := by positivity
  have hev : ∀ pq ∈ S, ∀ᶠ N : ℕ in atTop,
      (((Finset.range N).filter fun i ↦
        blockCodeAt b k x i = (pq.1 : ℤ) ∧ blockCodeAt b k y i = (pq.2 : ℤ)).card : ℝ) / N ≤
        ((b : ℝ) ^ (2 * k))⁻¹ + δ := fun pq hpq ↦ by
    have hlt := hS_lt pq hpq
    exact ((tendsto_card_blockCodeAt_joint hb0 h k hlt.1 hlt.2).eventually
      (gt_mem_nhds (lt_add_of_pos_right _ hδ))).mono fun N hN ↦ hN.le
  filter_upwards [(Filter.eventually_all_finset S).2 hev, eventually_gt_atTop 0] with N hN hN0
  have hsub :
      ((Finset.range N).filter fun i ↦
        blockCodeAt b k (x / D) i = ((blockCode u : ℕ) : ℤ) ∧
        blockCodeAt b k (y / D) i = ((blockCode v : ℕ) : ℤ)) ⊆
      S.biUnion fun pq ↦ (Finset.range N).filter fun i ↦
        blockCodeAt b k x i = (pq.1 : ℤ) ∧ blockCodeAt b k y i = (pq.2 : ℤ) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨j₁, hj₁, h1⟩ := div_nat_blockCodeAt_mem hb0 hD x k (blockCode u) i hi.2.1
    obtain ⟨j₂, hj₂, h2⟩ := div_nat_blockCodeAt_mem hb0 hD y k (blockCode v) i hi.2.2
    exact Finset.mem_biUnion.2 ⟨(j₁, j₂), Finset.mem_product.2 ⟨hj₁, hj₂⟩,
      Finset.mem_filter.2 ⟨Finset.mem_range.2 hi.1, h1, h2⟩⟩
  rw [hcnt, jointBlockCount_eq_card_blockCodeAt hb0]
  have hpow : (((b ^ 2 : ℕ) : ℝ) ^ k)⁻¹ = ((b : ℝ) ^ (2 * k))⁻¹ := by
    push_cast; rw [← pow_mul]
  rw [hpow]
  calc (((Finset.range N).filter fun i ↦
          blockCodeAt b k (x / D) i = ((blockCode u : ℕ) : ℤ) ∧
          blockCodeAt b k (y / D) i = ((blockCode v : ℕ) : ℤ)).card : ℝ) / N
      ≤ (∑ pq ∈ S, (((Finset.range N).filter fun i ↦
          blockCodeAt b k x i = (pq.1 : ℤ) ∧ blockCodeAt b k y i = (pq.2 : ℤ)).card : ℝ)) / N := by
        gcongr
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ pq ∈ S, (((Finset.range N).filter fun i ↦
          blockCodeAt b k x i = (pq.1 : ℤ) ∧ blockCodeAt b k y i = (pq.2 : ℤ)).card : ℝ) / N :=
        Finset.sum_div _ _ _
    _ ≤ ∑ _pq ∈ S, (((b : ℝ) ^ (2 * k))⁻¹ + δ) := Finset.sum_le_sum hN
    _ = (S.card : ℝ) * (((b : ℝ) ^ (2 * k))⁻¹ + δ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((D * D : ℕ) : ℝ) * ((b : ℝ) ^ (2 * k))⁻¹ + ε := by
        have hS' : (S.card : ℝ) ≤ (D * D : ℕ) := by exact_mod_cast hS_card
        have hDδ : ((D * D : ℕ) : ℝ) * δ ≤ ε := by
          simp only [δ]
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
        have hpos : (0 : ℝ) ≤ ((b : ℝ) ^ (2 * k))⁻¹ + δ := by positivity
        nlinarith

/-- Nonsingular integer linear transformations preserve joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.linear_int {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℤ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0)
    (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b (a₁₁ * x + a₁₂ * y) (a₂₁ * x + a₂₂ * y) := by
  rw [isJointlyNormalIn_iff_weyl hb] at h ⊢
  intro h₁ h₂ hne
  set h₁' : ℤ := h₁ * a₁₁ + h₂ * a₂₁
  set h₂' : ℤ := h₁ * a₁₂ + h₂ * a₂₂
  have hne' : (h₁', h₂') ≠ (0, 0) := by
    intro h0
    have e1 : h₁' = 0 := congrArg Prod.fst h0
    have e2 : h₂' = 0 := congrArg Prod.snd h0
    have h1d : h₁ * (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0 := by linear_combination a₂₂ * e1 - a₂₁ * e2
    have h2d : h₂ * (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0 := by linear_combination -a₁₂ * e1 + a₁₁ * e2
    exact hne (Prod.ext ((mul_eq_zero.1 h1d).resolve_right hdet)
      ((mul_eq_zero.1 h2d).resolve_right hdet))
  refine (h h₁' h₂' hne').congr fun N ↦ ?_
  congr 1
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  congr 1
  simp only [h₁', h₂']
  push_cast; ring

/-- **`GL_2(ℚ)` invariance of joint normality**: every invertible rational linear transformation
preserves joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.linear_rat {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℚ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0)
    (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b (a₁₁ * x + a₁₂ * y) (a₂₁ * x + a₂₂ * y) := by
  set D : ℕ := a₁₁.den * a₁₂.den * a₂₁.den * a₂₂.den
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos a₁₁.den_pos a₁₂.den_pos) a₂₁.den_pos)
    a₂₂.den_pos
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  set m₁₁ : ℤ := a₁₁.num * (a₁₂.den * a₂₁.den * a₂₂.den : ℕ)
  set m₁₂ : ℤ := a₁₂.num * (a₁₁.den * a₂₁.den * a₂₂.den : ℕ)
  set m₂₁ : ℤ := a₂₁.num * (a₁₁.den * a₁₂.den * a₂₂.den : ℕ)
  set m₂₂ : ℤ := a₂₂.num * (a₁₁.den * a₁₂.den * a₂₁.den : ℕ)
  have hm₁₁ : (m₁₁ : ℚ) = D * a₁₁ := by
    simp only [m₁₁, D]; push_cast
    have := Rat.mul_den_eq_num a₁₁
    linear_combination -(a₁₂.den * a₂₁.den * a₂₂.den : ℚ) * this
  have hm₁₂ : (m₁₂ : ℚ) = D * a₁₂ := by
    simp only [m₁₂, D]; push_cast
    have := Rat.mul_den_eq_num a₁₂
    linear_combination -(a₁₁.den * a₂₁.den * a₂₂.den : ℚ) * this
  have hm₂₁ : (m₂₁ : ℚ) = D * a₂₁ := by
    simp only [m₂₁, D]; push_cast
    have := Rat.mul_den_eq_num a₂₁
    linear_combination -(a₁₁.den * a₁₂.den * a₂₂.den : ℚ) * this
  have hm₂₂ : (m₂₂ : ℚ) = D * a₂₂ := by
    simp only [m₂₂, D]; push_cast
    have := Rat.mul_den_eq_num a₂₂
    linear_combination -(a₁₁.den * a₁₂.den * a₂₁.den : ℚ) * this
  have hmdet : m₁₁ * m₂₂ - m₁₂ * m₂₁ ≠ 0 := by
    intro h0
    have h0Q : ((m₁₁ * m₂₂ - m₁₂ * m₂₁ : ℤ) : ℚ) = 0 := by exact_mod_cast h0
    push_cast at h0Q
    rw [hm₁₁, hm₁₂, hm₂₁, hm₂₂] at h0Q
    have : (D : ℚ) * (D : ℚ) * (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0 := by linear_combination h0Q
    exact hdet ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hDQ hDQ))
  have hdiv := (h.div_nat hb hD).linear_int hb hmdet
  have hmR : ∀ (m : ℤ) (a : ℚ), (m : ℚ) = D * a → (m : ℝ) = (D : ℝ) * (a : ℝ) := fun m a hma ↦ by
    have := congrArg ((↑) : ℚ → ℝ) hma
    simpa using this
  have h1 : (m₁₁ : ℝ) * (x / D) + (m₁₂ : ℝ) * (y / D) = a₁₁ * x + a₁₂ * y := by
    rw [hmR _ _ hm₁₁, hmR _ _ hm₁₂]; field_simp
  have h2 : (m₂₁ : ℝ) * (x / D) + (m₂₂ : ℝ) * (y / D) = a₂₁ * x + a₂₂ * y := by
    rw [hmR _ _ hm₂₁, hmR _ _ hm₂₂]; field_simp
  rwa [h1, h2] at hdiv

/-- Rational translations preserve joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.add_ratCast {b : ℕ} (hb : 2 ≤ b) {x y : ℝ} (r₁ r₂ : ℚ)
    (h : IsJointlyNormalIn b x y) : IsJointlyNormalIn b (x + r₁) (y + r₂) := by
  set D : ℕ := r₁.den * r₂.den
  have hD : 0 < D := Nat.mul_pos r₁.den_pos r₂.den_pos
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  set m₁ : ℤ := r₁.num * r₂.den
  set m₂ : ℤ := r₂.num * r₁.den
  have hDZ : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hdet : (D : ℤ) * (D : ℤ) - 0 * 0 ≠ 0 := by simpa using mul_ne_zero hDZ hDZ
  have hmul : IsJointlyNormalIn b ((D : ℝ) * x) ((D : ℝ) * y) := by
    simpa using h.linear_int hb (a₁₁ := D) (a₁₂ := 0) (a₂₁ := 0) (a₂₂ := D) hdet
  have hadd : IsJointlyNormalIn b ((D : ℝ) * x + m₁) ((D : ℝ) * y + m₂) :=
    (isJointlyNormalIn_add_intCast_right_iff m₂).2
      ((isJointlyNormalIn_add_intCast_left_iff m₁).2 hmul)
  have hdiv := hadd.div_nat hb hD
  have hr₁ : ((D : ℝ) * x + m₁) / D = x + r₁ := by
    simp only [m₁, D]; rw [Rat.cast_def]
    have : (r₁.den : ℝ) ≠ 0 := by exact_mod_cast r₁.den_ne_zero
    have : (r₂.den : ℝ) ≠ 0 := by exact_mod_cast r₂.den_ne_zero
    push_cast; field_simp
  have hr₂ : ((D : ℝ) * y + m₂) / D = y + r₂ := by
    simp only [m₂, D]; rw [Rat.cast_def]
    have : (r₁.den : ℝ) ≠ 0 := by exact_mod_cast r₁.den_ne_zero
    have : (r₂.den : ℝ) ≠ 0 := by exact_mod_cast r₂.den_ne_zero
    push_cast; field_simp
  rwa [hr₁, hr₂] at hdiv

/-- Invertible rational affine transformations preserve joint normality in base `b ≥ 2`. -/
theorem IsJointlyNormalIn.affine_rat {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℚ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0) (r₁ r₂ : ℚ)
    (h : IsJointlyNormalIn b x y) :
    IsJointlyNormalIn b (a₁₁ * x + a₁₂ * y + r₁) (a₂₁ * x + a₂₂ * y + r₂) :=
  (h.linear_rat hb hdet).add_ratCast hb r₁ r₂

/-- Invertible rational linear transformations preserve joint absolute normality. -/
theorem IsJointlyAbsolutelyNormal.linear_rat {x y : ℝ}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℚ} (hdet : a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0)
    (h : IsJointlyAbsolutelyNormal x y) :
    IsJointlyAbsolutelyNormal (a₁₁ * x + a₁₂ * y) (a₂₁ * x + a₂₂ * y) :=
  fun _ hb ↦ (h _ hb).linear_rat hb hdet

/-- Rational translations preserve joint absolute normality. -/
theorem IsJointlyAbsolutelyNormal.add_ratCast {x y : ℝ} (r₁ r₂ : ℚ)
    (h : IsJointlyAbsolutelyNormal x y) :
    IsJointlyAbsolutelyNormal (x + r₁) (y + r₂) :=
  fun _ hb ↦ (h _ hb).add_ratCast hb r₁ r₂

end Real
