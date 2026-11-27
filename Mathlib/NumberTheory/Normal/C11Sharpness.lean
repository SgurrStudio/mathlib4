/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.NumberTheory.Normal.Borel
import Mathlib.NumberTheory.Normal.Rational

/-!
# Sharpness of `C²` affine rigidity: non-affine `C^{1,1}` normality-preserving diffeomorphisms

In `Mathlib.NumberTheory.Normal.Rigidity`, it is shown that every `C²` map `f : ℝ → ℝ` preserving
normality in any fixed base `b ≥ 2` (or absolute normality) must be affine. We prove **Manai's
Theorem 1.4** (arXiv:2609.24665, §4.2), showing that the `C²` regularity hypothesis is sharp and
cannot be weakened to `C^{1,1}` (continuously differentiable with globally Lipschitz derivative):

There exists a non-affine, strictly increasing `C^{1,1}` diffeomorphism `e : ℝ ≃ ℝ` (with both
`deriv e` and `deriv e.symm` globally Lipschitz) that preserves base-`b` normality for *every*
integer base `b ≥ 2`, and hence preserves absolute normality.

## Proof outline

1. By Borel's normal number theorem (`Real.ae_isAbsolutelyNormal`) and outer regularity of
   Lebesgue measure, there is a compact subset `K ⊆ [0, 1]` of absolutely normal numbers with
   `0 < volume K`.
2. Any measurable subset `S ⊆ [0, 1]` with `0 < volume S` admits a median split `S = A ∪ B` into
   two positive-measure pieces whose 0-th and 1-st moments are linearly independent, allowing us to
   realize any target pair of moments `(u, v) ∈ ℝ²` by a bounded measurable function supported on
   `S` with `L^∞` norm `O(|u| + |v|)`.
3. Enumerating `ℚ` as `r 0 = -1, r 1 = 2, r 2, r 3, ...`, we inductively construct a bounded
   measurable function `h = H₀ + ∑' m, δ m` supported on `K` with `|h| ≤ 1/2` such that
   `∫ s in Iic (q : ℝ), h s ∈ ℚ` and `∫ s in Iic (q : ℝ), s * h s ∈ ℚ` for every `q ∈ ℚ`, while
   `∫ s in Iic (2 : ℝ), h s > 0`.
4. Setting `g x := x + x * ∫ s in Iic x, h s - ∫ s in Iic x, s * h s` gives a strictly increasing
   non-affine `C^{1,1}` diffeomorphism of `ℝ` with `1/2 ≤ deriv g x ≤ 3/2` everywhere and globally
   `(1/2)`-Lipschitz `deriv g`.
5. For every `y ∉ K`, choosing a rational `q` in an open ball around `y` inside `Kᶜ` shows that
   `g y = (1 + q₀) * y - q₁` with `q₀, q₁ ∈ ℚ` and `1 + q₀ > 0`, so `g` preserves non-normality
   in every base `b ≥ 2` by Wall's theorem (`Real.isNormalIn_mul_add_ratCast_iff`).
6. Taking `e := g.symm` yields the desired non-affine `C^{1,1}` diffeomorphism preserving normality
   in every base `b ≥ 2` and absolute normality.

## Main statements

* `Real.exists_nonAffine_C11_diffeomorph_preserves_isNormalIn`: Manai's Theorem 1.4.
* `Real.exists_nonAffine_C11_diffeomorph_preserves_isAbsolutelyNormal_forward`: absolute-normality
  corollary.

## References

* C. Manai, *On normality preserving operations*, arXiv:2609.24665, §4.2 (Theorem 1.4).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace NormalNumbers.C11Sharpness

/-! ### Step 1: Compact subset of `[0, 1]` of absolutely normal numbers with positive measure -/

private lemma exists_compact_absolutelyNormal_pos_volume :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0 : ℝ) 1 ∧ (∀ x ∈ K, Real.IsAbsolutelyNormal x) ∧
      0 < volume K := by
  have hnull : volume {x : ℝ | ¬ Real.IsAbsolutelyNormal x} = 0 :=
    ae_iff.1 Real.ae_isAbsolutelyNormal
  have hlt : volume {x : ℝ | ¬ Real.IsAbsolutelyNormal x} < (1 / 2 : ℝ≥0∞) := by
    rw [hnull]; norm_num
  obtain ⟨V, hSV, hVopen, hVlt⟩ :=
    ({x : ℝ | ¬ Real.IsAbsolutelyNormal x}).exists_isOpen_lt_of_lt (1 / 2 : ℝ≥0∞) hlt
  refine ⟨Icc (0 : ℝ) 1 \ V, isCompact_Icc.diff hVopen, sdiff_subset, fun x hx ↦ ?_, ?_⟩
  · by_contra hnot
    exact hx.2 (hSV hnot)
  · have hsub : Icc (0 : ℝ) 1 ⊆ (Icc (0 : ℝ) 1 \ V) ∪ V := fun x hx ↦ by
      by_cases hxV : x ∈ V
      · exact Or.inr hxV
      · exact Or.inl ⟨hx, hxV⟩
    have hle : volume (Icc (0 : ℝ) 1) ≤ volume (Icc (0 : ℝ) 1 \ V) + volume V :=
      (measure_mono hsub).trans (measure_union_le _ _)
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at hle
    by_contra h0
    have hzero : volume (Icc (0 : ℝ) 1 \ V) = 0 := le_antisymm (not_lt.1 h0) bot_le
    rw [hzero, zero_add] at hle
    have : (1 : ℝ≥0∞) < 1 / 2 := lt_of_le_of_lt hle hVlt
    exact absurd this (by norm_num)

/-! ### Step 2: Realizing 0-th and 1-st moments on a positive-measure subset of `[0, 1]` -/

private lemma exists_supported_with_moments {S : Set ℝ} (hS_meas : MeasurableSet S)
    (hS_sub : S ⊆ Icc (0 : ℝ) 1) (hS_pos : 0 < volume S) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ,
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ s, s ∉ S → f s = 0) ∧
        (∀ s, |f s| ≤ C * (|u| + |v|)) ∧
        (∫ s, f s = u) ∧ (∫ s, s * f s = v) := by
  have hS_ne_top : volume S ≠ ∞ := by
    have hle : volume S ≤ volume (Icc (0 : ℝ) 1) := measure_mono hS_sub
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at hle
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hS_toReal_pos : 0 < (volume S).toReal := ENNReal.toReal_pos hS_pos.ne' hS_ne_top
  -- Cumulative volume function `φ t = (volume (S ∩ Iic t)).toReal` is 1-Lipschitz on `ℝ`
  let φ : ℝ → ℝ := fun t ↦ (volume (S ∩ Iic t)).toReal
  have hφ_sub : ∀ a b : ℝ, a ≤ b → φ b - φ a = (volume (S ∩ Ioc a b)).toReal := by
    intro a b hab
    have hdisj : Disjoint (S ∩ Iic a) (S ∩ Ioc a b) := by
      rw [Set.disjoint_left]
      rintro x ⟨_, hx1⟩ ⟨_, hx2⟩
      exact not_le_of_gt hx2.1 hx1
    have hunion : S ∩ Iic b = (S ∩ Iic a) ∪ (S ∩ Ioc a b) := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
      constructor
      · intro ⟨hxS, hxb⟩
        by_cases hxa : x ≤ a
        · exact Or.inl ⟨hxS, hxa⟩
        · exact Or.inr ⟨hxS, lt_of_not_ge hxa, hxb⟩
      · rintro (⟨hxS, hxa⟩ | ⟨hxS, _, hxb⟩)
        · exact ⟨hxS, hxa.trans hab⟩
        · exact ⟨hxS, hxb⟩
    have hmeas_b : volume (S ∩ Iic b) = volume (S ∩ Iic a) + volume (S ∩ Ioc a b) := by
      rw [hunion, measure_union hdisj (hS_meas.inter measurableSet_Ioc)]
    have h1 : volume (S ∩ Iic a) ≠ ∞ :=
      ne_top_of_le_ne_top hS_ne_top (measure_mono inter_subset_left)
    have h2 : volume (S ∩ Ioc a b) ≠ ∞ :=
      ne_top_of_le_ne_top hS_ne_top (measure_mono inter_subset_left)
    dsimp only [φ]
    rw [hmeas_b, ENNReal.toReal_add h1 h2]
    ring
  have hφ_cont : Continuous φ := by
    refine Metric.continuous_iff.2 fun x ε hε ↦ ⟨ε, hε, fun y hy ↦ ?_⟩
    rw [Real.dist_eq] at hy ⊢
    rcases le_total x y with hxy | hyx
    · rw [hφ_sub x y hxy, abs_of_nonneg ENNReal.toReal_nonneg]
      have hle : (volume (S ∩ Ioc x y)).toReal ≤ (volume (Ioc x y)).toReal :=
        ENNReal.toReal_mono (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
          (measure_mono inter_subset_right)
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hxy)] at hle
      rw [abs_of_nonneg (sub_nonneg.2 hxy)] at hy
      linarith
    · rw [abs_sub_comm (φ y), hφ_sub y x hyx, abs_of_nonneg ENNReal.toReal_nonneg]
      have hle : (volume (S ∩ Ioc y x)).toReal ≤ (volume (Ioc y x)).toReal :=
        ENNReal.toReal_mono (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
          (measure_mono inter_subset_right)
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hyx)] at hle
      rw [abs_sub_comm y, abs_of_nonneg (sub_nonneg.2 hyx)] at hy
      linarith
  have hφ0 : φ 0 = 0 := by
    dsimp only [φ]
    have hsub : S ∩ Iic (0 : ℝ) ⊆ {0} := fun x ⟨hxS, hx0⟩ ↦
      le_antisymm hx0 (hS_sub hxS).1
    have hvol : volume (S ∩ Iic (0 : ℝ)) = 0 :=
      measure_mono_null hsub (measure_singleton 0)
    rw [hvol, ENNReal.toReal_zero]
  have hφ1 : φ 1 = (volume S).toReal := by
    dsimp only [φ]
    have heq : S ∩ Iic (1 : ℝ) = S := inter_eq_left.2 fun x hx ↦ (hS_sub hx).2
    rw [heq]
  have hhalf_mem : (volume S).toReal / 2 ∈ Icc (φ 0) (φ 1) := by
    rw [hφ0, hφ1]; constructor <;> linarith
  obtain ⟨m, hm_mem, hm_eq⟩ :=
    intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) hφ_cont.continuousOn hhalf_mem
  let A : Set ℝ := S ∩ Iic m
  let B : Set ℝ := S ∩ Ioi m
  have hA_meas : MeasurableSet A := hS_meas.inter measurableSet_Iic
  have hB_meas : MeasurableSet B := hS_meas.inter measurableSet_Ioi
  have hAB_disj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hx1⟩ ⟨_, hx2⟩
    exact not_le_of_gt hx2 hx1
  have hAB_union : A ∪ B = S := by
    ext x; simp only [A, B, mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx; rcases le_or_gt x m with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hA_ne_top : volume A ≠ ∞ := ne_top_of_le_ne_top hS_ne_top (measure_mono inter_subset_left)
  have hB_ne_top : volume B ≠ ∞ := ne_top_of_le_ne_top hS_ne_top (measure_mono inter_subset_left)
  set μA := (volume A).toReal
  set μB := (volume B).toReal
  have hμA_eq : μA = (volume S).toReal / 2 := hm_eq
  have hμB_eq : μB = (volume S).toReal / 2 := by
    have hadd : (volume S).toReal = μA + μB := by
      rw [← hAB_union, measure_union hAB_disj hB_meas, ENNReal.toReal_add hA_ne_top hB_ne_top]
    linarith
  have hμA_pos : 0 < μA := by linarith
  have hμB_pos : 0 < μB := by linarith
  have hB_pos : 0 < volume B := by
    by_contra h0
    have hzero : volume B = 0 := le_antisymm (not_lt.1 h0) bot_le
    have : μB = 0 := by simp [μB, hzero]
    linarith
  set νA := ∫ s in A, s
  set νB := ∫ s in B, s
  have hint_id_A : IntegrableOn (fun s : ℝ ↦ s) A volume := by
    refine IntegrableOn.mono_set (t := Icc (0 : ℝ) 1) ?_ (inter_subset_left.trans hS_sub)
    exact continuousOn_id.integrableOn_Icc
  have hint_id_B : IntegrableOn (fun s : ℝ ↦ s) B volume := by
    refine IntegrableOn.mono_set (t := Icc (0 : ℝ) 1) ?_ (inter_subset_left.trans hS_sub)
    exact continuousOn_id.integrableOn_Icc
  have hint_const_A : IntegrableOn (fun _ : ℝ ↦ m) A volume :=
    integrableOn_const hA_ne_top
  have hint_const_B : IntegrableOn (fun _ : ℝ ↦ m) B volume :=
    integrableOn_const hB_ne_top
  have hνA_le : νA ≤ m * μA := by
    have hle : ∫ s in A, s ≤ ∫ _ in A, m :=
      setIntegral_mono_on hint_id_A hint_const_A hA_meas fun s hs ↦ hs.2
    rw [setIntegral_const, smul_eq_mul, Measure.real_def, mul_comm] at hle
    exact hle
  have hνB_gt : m * μB < νB := by
    have hdiff : 0 < ∫ s in B, (s - m) := by
      have hpos_ae : ∀ᵐ s ∂(volume.restrict B), 0 ≤ s - m := by
        filter_upwards [ae_restrict_mem hB_meas] with s hs
        exact sub_nonneg.2 (le_of_lt hs.2)
      rw [integral_pos_iff_support_of_nonneg_ae hpos_ae (hint_id_B.sub hint_const_B)]
      have hsupp : B ⊆ Function.support fun s : ℝ ↦ s - m := fun s hs ↦ by
        simp only [Function.mem_support, sub_ne_zero]
        exact ne_of_gt hs.2
      rw [Measure.restrict_apply' hB_meas, inter_eq_right.2 hsupp]
      exact hB_pos
    rw [integral_sub hint_id_B hint_const_B, setIntegral_const, smul_eq_mul,
      Measure.real_def, mul_comm] at hdiff
    linarith
  set det := μA * νB - μB * νA
  have hdet_pos : 0 < det := by
    have h1 : μA * (m * μB) < μA * νB := mul_lt_mul_of_pos_left hνB_gt hμA_pos
    have h2 : μB * νA ≤ μB * (m * μA) := mul_le_mul_of_nonneg_left hνA_le hμB_pos.le
    dsimp only [det]
    linarith
  set C := (max (max |νB| |μB|) (max |νA| |μA|) + 1) / det
  have hC_pos : 0 < C := by
    have h0 : 0 ≤ max (max |νB| |μB|) (max |νA| |μA|) :=
      (abs_nonneg νB).trans ((le_max_left _ _).trans (le_max_left _ _))
    exact div_pos (by linarith) hdet_pos
  refine ⟨C, hC_pos, fun u v ↦ ?_⟩
  let α := (νB * u - μB * v) / det
  let β := (-νA * u + μA * v) / det
  let f : ℝ → ℝ := A.indicator (fun _ ↦ α) + B.indicator (fun _ ↦ β)
  have hf_meas : Measurable f :=
    (measurable_const.indicator hA_meas).add (measurable_const.indicator hB_meas)
  have hf_supp : ∀ s, s ∉ S → f s = 0 := fun s hs ↦ by
    have hsA : s ∉ A := fun h ↦ hs h.1
    have hsB : s ∉ B := fun h ↦ hs h.1
    simp [f, hsA, hsB]
  have hα_le : |α| ≤ C * (|u| + |v|) := by
    have hM1 : |νB| ≤ max (max |νB| |μB|) (max |νA| |μA|) + 1 := by
      linarith [le_max_left |νB| |μB|, le_max_left (max |νB| |μB|) (max |νA| |μA|)]
    have hM2 : |μB| ≤ max (max |νB| |μB|) (max |νA| |μA|) + 1 := by
      linarith [le_max_right |νB| |μB|, le_max_left (max |νB| |μB|) (max |νA| |μA|)]
    dsimp only [α, C]
    rw [abs_div, abs_of_pos hdet_pos, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hdet_pos.le
    calc |νB * u - μB * v|
        ≤ |νB * u| + |μB * v| := abs_sub _ _
      _ = |νB| * |u| + |μB| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ (max (max |νB| |μB|) (max |νA| |μA|) + 1) * |u| +
            (max (max |νB| |μB|) (max |νA| |μA|) + 1) * |v| := by
          gcongr
      _ = (max (max |νB| |μB|) (max |νA| |μA|) + 1) * (|u| + |v|) := by ring
  have hβ_le : |β| ≤ C * (|u| + |v|) := by
    have hM1 : |νA| ≤ max (max |νB| |μB|) (max |νA| |μA|) + 1 := by
      linarith [le_max_left |νA| |μA|, le_max_right (max |νB| |μB|) (max |νA| |μA|)]
    have hM2 : |μA| ≤ max (max |νB| |μB|) (max |νA| |μA|) + 1 := by
      linarith [le_max_right |νA| |μA|, le_max_right (max |νB| |μB|) (max |νA| |μA|)]
    dsimp only [β, C]
    rw [abs_div, abs_of_pos hdet_pos, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hdet_pos.le
    calc |-νA * u + μA * v|
        ≤ |-νA * u| + |μA * v| := abs_add_le _ _
      _ = |νA| * |u| + |μA| * |v| := by rw [abs_mul, abs_neg, abs_mul]
      _ ≤ (max (max |νB| |μB|) (max |νA| |μA|) + 1) * |u| +
            (max (max |νB| |μB|) (max |νA| |μA|) + 1) * |v| := by
          gcongr
      _ = (max (max |νB| |μB|) (max |νA| |μA|) + 1) * (|u| + |v|) := by ring
  have hf_bound : ∀ s, |f s| ≤ C * (|u| + |v|) := fun s ↦ by
    by_cases hsA : s ∈ A
    · have hsB : s ∉ B := Set.disjoint_left.1 hAB_disj hsA
      simp [f, hsA, hsB, hα_le]
    · by_cases hsB : s ∈ B
      · simp [f, hsA, hsB, hβ_le]
      · simp only [f, Pi.add_apply, indicator_of_notMem hsA, indicator_of_notMem hsB,
          add_zero, abs_zero]
        positivity
  have hf_int0 : ∫ s, f s = u := by
    have hiA : Integrable (A.indicator fun _ : ℝ ↦ α) volume :=
      (integrableOn_const hA_ne_top).integrable_indicator hA_meas
    have hiB : Integrable (B.indicator fun _ : ℝ ↦ β) volume :=
      (integrableOn_const hB_ne_top).integrable_indicator hB_meas
    change ∫ s, (A.indicator (fun _ ↦ α) s + B.indicator (fun _ ↦ β) s) = u
    rw [integral_add hiA hiB, integral_indicator hA_meas, integral_indicator hB_meas,
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, Measure.real_def,
      Measure.real_def]
    change μA * α + μB * β = u
    dsimp only [α, β]
    have hdet_ne : det ≠ 0 := hdet_pos.ne'
    field_simp [hdet_ne]
    dsimp only [det]
    ring
  have hf_int1 : ∫ s, s * f s = v := by
    have hmul_eq : (fun s : ℝ ↦ s * f s) =
        fun s ↦ A.indicator (fun t ↦ α * t) s + B.indicator (fun t ↦ β * t) s := by
      funext s
      by_cases hsA : s ∈ A
      · have hsB : s ∉ B := Set.disjoint_left.1 hAB_disj hsA
        simp [f, hsA, hsB, mul_comm]
      · by_cases hsB : s ∈ B
        · simp [f, hsA, hsB, mul_comm]
        · simp [f, hsA, hsB]
    have hiA : Integrable (A.indicator fun t : ℝ ↦ α * t) volume :=
      IntegrableOn.integrable_indicator (hint_id_A.const_mul α) hA_meas
    have hiB : Integrable (B.indicator fun t : ℝ ↦ β * t) volume :=
      IntegrableOn.integrable_indicator (hint_id_B.const_mul β) hB_meas
    rw [hmul_eq, integral_add hiA hiB, integral_indicator hA_meas, integral_indicator hB_meas,
      integral_const_mul, integral_const_mul]
    change α * νA + β * νB = v
    dsimp only [α, β]
    have hdet_ne : det ≠ 0 := hdet_pos.ne'
    field_simp [hdet_ne]
    dsimp only [det]
    ring
  exact ⟨f, hf_meas, hf_supp, hf_bound, hf_int0, hf_int1⟩

/-! ### Step 3: Inductive rational-moment construction over an enumeration of `ℚ` -/

private lemma integrable_of_bounded_supp {f : ℝ → ℝ} {S : Set ℝ} (hf_meas : Measurable f)
    (hf_supp : ∀ s, s ∉ S → f s = 0) (hS_sub : S ⊆ Icc (0 : ℝ) 1) {M : ℝ}
    (hf_bound : ∀ s, |f s| ≤ M) : Integrable f volume := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf_bound 0)
  have hbound : ∀ s, ‖f s‖ ≤ (Icc (0 : ℝ) 1).indicator (fun _ ↦ M) s := fun s ↦ by
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · simpa [hs, Real.norm_eq_abs] using hf_bound s
    · have hsS : s ∉ S := fun h ↦ hs (hS_sub h)
      simp [hs, hf_supp s hsS]
  have hdom : Integrable ((Icc (0 : ℝ) 1).indicator fun _ : ℝ ↦ M) volume :=
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc
  exact hdom.mono' hf_meas.aestronglyMeasurable (Eventually.of_forall hbound)

private lemma setIntegral_Iic_eq_of_supp_subset {f : ℝ → ℝ} {S : Set ℝ} {a : ℝ}
    (hf_supp : ∀ s, s ∉ S → f s = 0) (hsub : S ⊆ Iic a) :
    ∫ s in Iic a, f s = ∫ s, f s := by
  rw [← integral_indicator measurableSet_Iic]
  congr 1; funext s
  by_cases hs : s ∈ Iic a
  · simp [hs]
  · simp [hs, hf_supp s (fun h ↦ hs (hsub h))]

private lemma setIntegral_Iic_eq_zero_of_supp_disjoint {f : ℝ → ℝ} {S : Set ℝ} {a : ℝ}
    (hf_supp : ∀ s, s ∉ S → f s = 0) (hdisj : Disjoint S (Iic a)) :
    ∫ s in Iic a, f s = 0 := by
  rw [← integral_indicator measurableSet_Iic]
  have h0 : (Iic a).indicator f = 0 := by
    funext s
    by_cases hs : s ∈ Iic a
    · simp [hs, hf_supp s (fun h ↦ Set.disjoint_left.1 hdisj h hs)]
    · simp [hs]
  simp only [h0, Pi.zero_apply, integral_zero]

private lemma setIntegral_Iic_eq_of_measure_Ioc_zero {f : ℝ → ℝ} {K : Set ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf_supp : ∀ s, s ∉ K → f s = 0) (hzero : volume (K ∩ Ioc a b) = 0) :
    ∫ s in Iic b, f s = ∫ s in Iic a, f s := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  refine integral_congr_ae ?_
  have hsub : {s : ℝ | (Iic b).indicator f s ≠ (Iic a).indicator f s} ⊆ K ∩ Ioc a b := by
    intro s hs
    simp only [mem_ofPred_eq] at hs
    by_cases hsK : s ∈ K
    · refine ⟨hsK, ?_⟩
      by_cases hsa : s ≤ a
      · have hsb : s ≤ b := hsa.trans hab
        exact absurd (by simp [hsa, hsb]) hs
      · by_cases hsb : s ≤ b
        · exact ⟨lt_of_not_ge hsa, hsb⟩
        · exact absurd (by simp [hsa, hsb]) hs
    · exact absurd (by by_cases h1 : s ≤ b <;> by_cases h2 : s ≤ a <;>
        simp [h1, h2, hf_supp s hsK]) hs
  rw [Filter.EventuallyEq, ae_iff]
  exact measure_mono_null hsub hzero

private structure MomentState (K : Set ℝ) (r : ℕ → ℚ) (q₀ : ℚ) (n : ℕ) where
  H : ℝ → ℝ
  H_meas : Measurable H
  H_supp : ∀ s, s ∉ K → H s = 0
  H_bound : ∀ s, |H s| ≤ 1 / 4 + ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 3)
  H_rat0 : ∀ j < n, (∫ s in Iic (r j : ℝ), H s) ∈ Set.range ((↑) : ℚ → ℝ)
  H_rat1 : ∀ j < n, (∫ s in Iic (r j : ℝ), s * H s) ∈ Set.range ((↑) : ℚ → ℝ)
  H_two_0 : (∫ s in Iic (2 : ℝ), H s) = (q₀ : ℝ)

private lemma exists_next_momentState {K : Set ℝ} (hK_meas : MeasurableSet K)
    (hK_sub : K ⊆ Icc (0 : ℝ) 1) {r : ℕ → ℚ} (hr0 : r 0 = -1) (hr1 : r 1 = 2) {q₀ : ℚ}
    {n : ℕ} (hn : 2 ≤ n) (st : MomentState K r q₀ n) :
    ∃ (δ : ℝ → ℝ) (st' : MomentState K r q₀ (n + 1)),
      (∀ s, st'.H s = st.H s + δ s) ∧
      Measurable δ ∧
      (∀ s, s ∉ K → δ s = 0) ∧
      (∀ s, |δ s| ≤ (1 / 2 : ℝ) ^ (n + 3)) ∧
      (∀ j < n, ∫ s in Iic (r j : ℝ), δ s = 0) ∧
      (∀ j < n, ∫ s in Iic (r j : ℝ), s * δ s = 0) := by
  classical
  have hH_int : Integrable st.H volume :=
    integrable_of_bounded_supp st.H_meas st.H_supp hK_sub st.H_bound
  have hsH_int : Integrable (fun s ↦ s * st.H s) volume :=
    integrable_of_bounded_supp (measurable_id.mul st.H_meas)
      (fun s hs ↦ by simp [st.H_supp s hs]) hK_sub (fun s ↦ by
        by_cases hsK : s ∈ K
        · have hs01 := hK_sub hsK
          rw [abs_mul, abs_of_nonneg hs01.1]
          exact (mul_le_of_le_one_left (abs_nonneg _) hs01.2).trans (st.H_bound s)
        · simp only [st.H_supp s hsK, mul_zero, abs_zero]
          have : (0 : ℝ) ≤ 1 / 4 := by norm_num
          linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.range n) ↦
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (j + 3)])
  -- Trivial zero-correction helper when moments at `r n` are already rational
  have htriv :
      (∫ s in Iic (r n : ℝ), st.H s) ∈ Set.range ((↑) : ℚ → ℝ) →
      (∫ s in Iic (r n : ℝ), s * st.H s) ∈ Set.range ((↑) : ℚ → ℝ) →
      ∃ (δ : ℝ → ℝ) (st' : MomentState K r q₀ (n + 1)),
        (∀ s, st'.H s = st.H s + δ s) ∧
        Measurable δ ∧
        (∀ s, s ∉ K → δ s = 0) ∧
        (∀ s, |δ s| ≤ (1 / 2 : ℝ) ^ (n + 3)) ∧
        (∀ j < n, ∫ s in Iic (r j : ℝ), δ s = 0) ∧
        (∀ j < n, ∫ s in Iic (r j : ℝ), s * δ s = 0) := by
    intro hrat0 hrat1
    refine ⟨0,
      { H := st.H
        H_meas := st.H_meas
        H_supp := st.H_supp
        H_bound := fun s ↦ by
          rw [Finset.sum_range_succ]
          linarith [st.H_bound s, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (n + 3)]
        H_rat0 := fun j hj ↦ by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
          · exact st.H_rat0 j hlt
          · exact hrat0
        H_rat1 := fun j hj ↦ by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
          · exact st.H_rat1 j hlt
          · exact hrat1
        H_two_0 := st.H_two_0 },
      fun _ ↦ (add_zero _).symm, measurable_const, fun _ _ ↦ rfl,
      fun _ ↦ by simp, fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩
  set c : ℝ := (r n : ℝ)
  by_cases hneg : c ≤ -1
  · refine htriv ⟨0, ?_⟩ ⟨0, ?_⟩
    · rw [Rat.cast_zero, eq_comm]
      exact setIntegral_Iic_eq_zero_of_supp_disjoint st.H_supp (by
        rw [Set.disjoint_left]; intro s hsK hsc
        have := (hK_sub hsK).1; change s ≤ c at hsc; linarith)
    · rw [Rat.cast_zero, eq_comm]
      exact setIntegral_Iic_eq_zero_of_supp_disjoint (S := K)
        (fun s hs ↦ by simp [st.H_supp s hs]) (by
          rw [Set.disjoint_left]; intro s hsK hsc
          have := (hK_sub hsK).1; change s ≤ c at hsc; linarith)
  by_cases hbig : 2 ≤ c
  · have h0_eq : ∫ s in Iic c, st.H s = ∫ s in Iic (r 1 : ℝ), st.H s := by
      have hr1' : (r 1 : ℝ) = 2 := by exact_mod_cast hr1
      rw [hr1',
        setIntegral_Iic_eq_of_supp_subset st.H_supp (fun s hs ↦ (hK_sub hs).2.trans (by linarith)),
        setIntegral_Iic_eq_of_supp_subset st.H_supp (fun s hs ↦ (hK_sub hs).2.trans (by linarith))]
    have h1_eq : ∫ s in Iic c, s * st.H s = ∫ s in Iic (r 1 : ℝ), s * st.H s := by
      have hr1' : (r 1 : ℝ) = 2 := by exact_mod_cast hr1
      rw [hr1',
        setIntegral_Iic_eq_of_supp_subset (fun s hs ↦ by simp [st.H_supp s hs])
          (fun s hs ↦ (hK_sub hs).2.trans (by linarith)),
        setIntegral_Iic_eq_of_supp_subset (fun s hs ↦ by simp [st.H_supp s hs])
          (fun s hs ↦ (hK_sub hs).2.trans (by linarith))]
    exact htriv (h0_eq ▸ st.H_rat0 1 (by omega)) (h1_eq ▸ st.H_rat1 1 (by omega))
  by_cases hdup : ∃ j < n, (r j : ℝ) = c
  · obtain ⟨j, hj, hjc⟩ := hdup
    exact htriv (hjc ▸ st.H_rat0 j hj) (hjc ▸ st.H_rat1 j hj)
  -- Now `-1 < c < 2` and `c` is distinct from all previous cuts `r j` (`j < n`)
  push Not at hneg hbig hdup
  let leftSet : Finset ℕ := (Finset.range n).filter fun j ↦ (r j : ℝ) < c
  let rightSet : Finset ℕ := (Finset.range n).filter fun j ↦ c < (r j : ℝ)
  have hleft_ne : leftSet.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by
    have : (r 0 : ℝ) = -1 := by exact_mod_cast hr0
    linarith⟩⟩
  have hright_ne : rightSet.Nonempty := ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by
    have : (r 1 : ℝ) = 2 := by exact_mod_cast hr1
    linarith⟩⟩
  obtain ⟨jL, hjL_mem, hjL_max⟩ := Finset.exists_max_image leftSet (fun j ↦ (r j : ℝ)) hleft_ne
  obtain ⟨jR, hjR_mem, hjR_min⟩ := Finset.exists_min_image rightSet (fun j ↦ (r j : ℝ)) hright_ne
  have hjL_lt : jL < n := Finset.mem_range.1 (Finset.mem_filter.1 hjL_mem).1
  have hjR_lt : jR < n := Finset.mem_range.1 (Finset.mem_filter.1 hjR_mem).1
  set L : ℝ := (r jL : ℝ)
  set R : ℝ := (r jR : ℝ)
  have hLc : L < c := (Finset.mem_filter.1 hjL_mem).2
  have hcR : c < R := (Finset.mem_filter.1 hjR_mem).2
  let A : Set ℝ := K ∩ Ioc L c
  let B : Set ℝ := K ∩ Ioc c R
  by_cases hA0 : volume A = 0
  · have h0 := setIntegral_Iic_eq_of_measure_Ioc_zero hLc.le st.H_supp hA0
    have h1 := setIntegral_Iic_eq_of_measure_Ioc_zero (f := fun s ↦ s * st.H s) hLc.le
      (fun s hs ↦ by simp [st.H_supp s hs]) hA0
    exact htriv (h0 ▸ st.H_rat0 jL hjL_lt) (h1 ▸ st.H_rat1 jL hjL_lt)
  by_cases hB0 : volume B = 0
  · have h0 := (setIntegral_Iic_eq_of_measure_Ioc_zero hcR.le st.H_supp hB0).symm
    have h1 := (setIntegral_Iic_eq_of_measure_Ioc_zero (f := fun s ↦ s * st.H s) hcR.le
      (fun s hs ↦ by simp [st.H_supp s hs]) hB0).symm
    exact htriv (h0 ▸ st.H_rat0 jR hjR_lt) (h1 ▸ st.H_rat1 jR hjR_lt)
  -- Both `A` and `B` have positive measure: construct balanced correction `δ = δA + δB`
  have hA_pos : 0 < volume A := pos_iff_ne_zero.2 hA0
  have hB_pos : 0 < volume B := pos_iff_ne_zero.2 hB0
  obtain ⟨CA, hCA_pos, hA_mom⟩ := exists_supported_with_moments
    (hK_meas.inter measurableSet_Ioc) (inter_subset_left.trans hK_sub) hA_pos
  obtain ⟨CB, hCB_pos, hB_mom⟩ := exists_supported_with_moments
    (hK_meas.inter measurableSet_Ioc) (inter_subset_left.trans hK_sub) hB_pos
  set C := max CA CB
  have hC_pos : 0 < C := lt_of_lt_of_le hCA_pos (le_max_left CA CB)
  set ε : ℝ := (1 / 2 : ℝ) ^ (n + 3) / (2 * C)
  have hε_pos : 0 < ε := by positivity
  set m0 : ℝ := ∫ s in Iic c, st.H s
  set m1 : ℝ := ∫ s in Iic c, s * st.H s
  obtain ⟨p0, hp0_gt, hp0_lt⟩ := exists_rat_btwn (show m0 - ε < m0 + ε by linarith)
  obtain ⟨p1, hp1_gt, hp1_lt⟩ := exists_rat_btwn (show m1 - ε < m1 + ε by linarith)
  set u : ℝ := (p0 : ℝ) - m0
  set v : ℝ := (p1 : ℝ) - m1
  have huv_le : |u| + |v| ≤ (1 / 2 : ℝ) ^ (n + 3) / C := by
    have hu : |u| < ε := abs_lt.2 ⟨by linarith, by linarith⟩
    have hv : |v| < ε := abs_lt.2 ⟨by linarith, by linarith⟩
    have : 2 * ε = (1 / 2 : ℝ) ^ (n + 3) / C := by
      dsimp only [ε]; field_simp [hC_pos.ne']
    linarith
  obtain ⟨δA, hδA_meas, hδA_supp, hδA_bound, hδA_int0, hδA_int1⟩ := hA_mom u v
  obtain ⟨δB, hδB_meas, hδB_supp, hδB_bound, hδB_int0, hδB_int1⟩ := hB_mom (-u) (-v)
  have hAB_disj : Disjoint A B := by
    rw [Set.disjoint_left]; rintro s ⟨_, hs1⟩ ⟨_, hs2⟩
    exact not_le_of_gt hs2.1 hs1.2
  let δ : ℝ → ℝ := fun s ↦ δA s + δB s
  have hδ_meas : Measurable δ := hδA_meas.add hδB_meas
  have hδ_supp : ∀ s, s ∉ K → δ s = 0 := fun s hsK ↦ by
    simp [δ, hδA_supp s (fun h ↦ hsK h.1), hδB_supp s (fun h ↦ hsK h.1)]
  have hδA_le : ∀ s, |δA s| ≤ (1 / 2 : ℝ) ^ (n + 3) := fun s ↦ by
    calc |δA s| ≤ CA * (|u| + |v|) := hδA_bound s
      _ ≤ C * (|u| + |v|) := mul_le_mul_of_nonneg_right (le_max_left CA CB) (by positivity)
      _ ≤ C * ((1 / 2 : ℝ) ^ (n + 3) / C) := mul_le_mul_of_nonneg_left huv_le hC_pos.le
      _ = (1 / 2 : ℝ) ^ (n + 3) := mul_div_cancel₀ _ hC_pos.ne'
  have hδB_le : ∀ s, |δB s| ≤ (1 / 2 : ℝ) ^ (n + 3) := fun s ↦ by
    have habs : |-u| + |-v| = |u| + |v| := by rw [abs_neg, abs_neg]
    calc |δB s| ≤ CB * (|-u| + |-v|) := hδB_bound s
      _ = CB * (|u| + |v|) := by rw [habs]
      _ ≤ C * (|u| + |v|) := mul_le_mul_of_nonneg_right (le_max_right CA CB) (by positivity)
      _ ≤ C * ((1 / 2 : ℝ) ^ (n + 3) / C) := mul_le_mul_of_nonneg_left huv_le hC_pos.le
      _ = (1 / 2 : ℝ) ^ (n + 3) := mul_div_cancel₀ _ hC_pos.ne'
  have hδ_bound : ∀ s, |δ s| ≤ (1 / 2 : ℝ) ^ (n + 3) := fun s ↦ by
    by_cases hsA : s ∈ A
    · have hsB : s ∉ B := Set.disjoint_left.1 hAB_disj hsA
      simp only [δ, hδB_supp s hsB, add_zero]
      exact hδA_le s
    · simp only [δ, hδA_supp s hsA, zero_add]
      exact hδB_le s
  have hδA_int : Integrable δA volume :=
    integrable_of_bounded_supp hδA_meas hδA_supp (inter_subset_left.trans hK_sub) hδA_le
  have hδB_int : Integrable δB volume :=
    integrable_of_bounded_supp hδB_meas hδB_supp (inter_subset_left.trans hK_sub) hδB_le
  have hsδA_int : Integrable (fun s ↦ s * δA s) volume :=
    integrable_of_bounded_supp (S := A) (measurable_id.mul hδA_meas)
      (fun s hs ↦ by simp [hδA_supp s hs])
      (inter_subset_left.trans hK_sub) (fun s ↦ by
        by_cases hsA : s ∈ A
        · have hs01 := hK_sub hsA.1
          rw [abs_mul, abs_of_nonneg hs01.1]
          exact (mul_le_of_le_one_left (abs_nonneg _) hs01.2).trans (hδA_le s)
        · simp [hδA_supp s hsA])
  have hsδB_int : Integrable (fun s ↦ s * δB s) volume :=
    integrable_of_bounded_supp (S := B) (measurable_id.mul hδB_meas)
      (fun s hs ↦ by simp [hδB_supp s hs])
      (inter_subset_left.trans hK_sub) (fun s ↦ by
        by_cases hsB : s ∈ B
        · have hs01 := hK_sub hsB.1
          rw [abs_mul, abs_of_nonneg hs01.1]
          exact (mul_le_of_le_one_left (abs_nonneg _) hs01.2).trans (hδB_le s)
        · simp [hδB_supp s hsB])
  have hδ_int : Integrable δ volume := hδA_int.add hδB_int
  have hsδ_int : Integrable (fun s ↦ s * δ s) volume := by
    have : (fun s ↦ s * δ s) = fun s ↦ s * δA s + s * δB s := funext fun s ↦ mul_add s _ _
    rw [this]; exact hsδA_int.add hsδB_int
  -- Zero moments of `δ` at all previous cuts `r j` (`j < n`)
  have hδ_prev0 : ∀ j < n, ∫ s in Iic (r j : ℝ), δ s = 0 := fun j hj ↦ by
    have hne : (r j : ℝ) ≠ c := hdup j hj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hleL : (r j : ℝ) ≤ L :=
        hjL_max j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hlt⟩)
      exact setIntegral_Iic_eq_zero_of_supp_disjoint (S := A ∪ B)
        (fun s hs ↦ by simp [δ, hδA_supp s (fun h ↦ hs (Or.inl h)),
          hδB_supp s (fun h ↦ hs (Or.inr h))])
        (by
          rw [Set.disjoint_left]
          rintro s (⟨_, hs⟩ | ⟨_, hs⟩) hsr
          · change s ≤ (r j : ℝ) at hsr; linarith [hs.1]
          · change s ≤ (r j : ℝ) at hsr; linarith [hs.1, hLc])
    · have hgeR : R ≤ (r j : ℝ) :=
        hjR_min j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hgt⟩)
      rw [setIntegral_Iic_eq_of_supp_subset (S := A ∪ B)
        (fun s hs ↦ by simp [δ, hδA_supp s (fun h ↦ hs (Or.inl h)),
          hδB_supp s (fun h ↦ hs (Or.inr h))])
        (by rintro s (⟨_, hs⟩ | ⟨_, hs⟩)
            · exact hs.2.trans (hcR.le.trans hgeR)
            · exact hs.2.trans hgeR)]
      change ∫ s, (δA s + δB s) = 0
      rw [integral_add hδA_int hδB_int, hδA_int0, hδB_int0, add_neg_cancel]
  have hδ_prev1 : ∀ j < n, ∫ s in Iic (r j : ℝ), s * δ s = 0 := fun j hj ↦ by
    have hne : (r j : ℝ) ≠ c := hdup j hj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hleL : (r j : ℝ) ≤ L :=
        hjL_max j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hlt⟩)
      exact setIntegral_Iic_eq_zero_of_supp_disjoint (S := A ∪ B)
        (fun s hs ↦ by simp [δ, hδA_supp s (fun h ↦ hs (Or.inl h)),
          hδB_supp s (fun h ↦ hs (Or.inr h))])
        (by
          rw [Set.disjoint_left]
          rintro s (⟨_, hs⟩ | ⟨_, hs⟩) hsr
          · change s ≤ (r j : ℝ) at hsr; linarith [hs.1]
          · change s ≤ (r j : ℝ) at hsr; linarith [hs.1, hLc])
    · have hgeR : R ≤ (r j : ℝ) :=
        hjR_min j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hgt⟩)
      rw [setIntegral_Iic_eq_of_supp_subset (S := A ∪ B)
        (fun s hs ↦ by simp [δ, hδA_supp s (fun h ↦ hs (Or.inl h)),
          hδB_supp s (fun h ↦ hs (Or.inr h))])
        (by rintro s (⟨_, hs⟩ | ⟨_, hs⟩)
            · exact hs.2.trans (hcR.le.trans hgeR)
            · exact hs.2.trans hgeR)]
      have heq : (fun s ↦ s * δ s) = fun s ↦ s * δA s + s * δB s := funext fun s ↦ mul_add s _ _
      rw [heq, integral_add hsδA_int hsδB_int, hδA_int1, hδB_int1, add_neg_cancel]
  -- Moments of `δ` at the new cut `c = r n` equal `u` and `v`
  have hδ_at_c0 : ∫ s in Iic c, δ s = u := by
    change ∫ s in Iic c, (δA s + δB s) = u
    rw [integral_add hδA_int.integrableOn hδB_int.integrableOn,
      setIntegral_Iic_eq_of_supp_subset hδA_supp (fun _ hs ↦ hs.2.2),
      setIntegral_Iic_eq_zero_of_supp_disjoint hδB_supp
        (Set.disjoint_left.2 fun _ hs hsc ↦ not_le_of_gt hs.2.1 hsc),
      hδA_int0, add_zero]
  have hδ_at_c1 : ∫ s in Iic c, s * δ s = v := by
    have heq : (fun s ↦ s * δ s) = fun s ↦ s * δA s + s * δB s := funext fun s ↦ mul_add s _ _
    rw [heq, integral_add hsδA_int.integrableOn hsδB_int.integrableOn,
      setIntegral_Iic_eq_of_supp_subset (S := A) (fun s hs ↦ by simp [hδA_supp s hs])
        (fun _ hs ↦ hs.2.2),
      setIntegral_Iic_eq_zero_of_supp_disjoint (S := B) (fun s hs ↦ by simp [hδB_supp s hs])
        (Set.disjoint_left.2 fun _ hs hsc ↦ not_le_of_gt hs.2.1 hsc),
      hδA_int1, add_zero]
  let H' : ℝ → ℝ := fun s ↦ st.H s + δ s
  refine ⟨δ,
    { H := H'
      H_meas := st.H_meas.add hδ_meas
      H_supp := fun s hsK ↦ by simp [H', st.H_supp s hsK, hδ_supp s hsK]
      H_bound := fun s ↦ by
        rw [Finset.sum_range_succ]
        calc |st.H s + δ s| ≤ |st.H s| + |δ s| := abs_add_le _ _
          _ ≤ (1 / 4 + ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 3)) + (1 / 2 : ℝ) ^ (n + 3) :=
              add_le_add (st.H_bound s) (hδ_bound s)
          _ = 1 / 4 + (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 3) + (1 / 2 : ℝ) ^ (n + 3)) := by
              ring
      H_rat0 := fun j hj ↦ by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
        · have heq : ∫ s in Iic (r j : ℝ), H' s = ∫ s in Iic (r j : ℝ), st.H s := by
            dsimp only [H']
            rw [integral_add hH_int.integrableOn hδ_int.integrableOn, hδ_prev0 j hlt, add_zero]
          exact heq ▸ st.H_rat0 j hlt
        · refine ⟨p0, ?_⟩
          dsimp only [H']
          rw [integral_add hH_int.integrableOn hδ_int.integrableOn]
          change (p0 : ℝ) = m0 + ∫ s in Iic c, δ s
          rw [hδ_at_c0]; dsimp only [u]; ring
      H_rat1 := fun j hj ↦ by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
        · have heq : ∫ s in Iic (r j : ℝ), s * H' s = ∫ s in Iic (r j : ℝ), s * st.H s := by
            have hmul : (fun s ↦ s * H' s) = fun s ↦ s * st.H s + s * δ s :=
              funext fun s ↦ mul_add s _ _
            rw [hmul, integral_add hsH_int.integrableOn hsδ_int.integrableOn, hδ_prev1 j hlt,
              add_zero]
          exact heq ▸ st.H_rat1 j hlt
        · refine ⟨p1, ?_⟩
          have hmul : (fun s ↦ s * H' s) = fun s ↦ s * st.H s + s * δ s :=
            funext fun s ↦ mul_add s _ _
          rw [hmul, integral_add hsH_int.integrableOn hsδ_int.integrableOn]
          change (p1 : ℝ) = m1 + ∫ s in Iic c, s * δ s
          rw [hδ_at_c1]; dsimp only [v]; ring
      H_two_0 := by
        have hr1' : (r 1 : ℝ) = 2 := by exact_mod_cast hr1
        dsimp only [H']
        rw [integral_add hH_int.integrableOn hδ_int.integrableOn, ← hr1', hδ_prev0 1 (by omega),
          add_zero, hr1', st.H_two_0] },
    fun _ ↦ rfl, hδ_meas, hδ_supp, hδ_bound, hδ_prev0, hδ_prev1⟩

/-- Existence of a bounded measurable function `h` supported on `K` with `|h| ≤ 1/2`, rational
0-th and 1-st moments on `(-∞, q]` for every `q ∈ ℚ`, and positive total integral `∫ h > 0`. -/
private lemma exists_rational_moment_density {K : Set ℝ} (hK_meas : MeasurableSet K)
    (hK_sub : K ⊆ Icc (0 : ℝ) 1) (hK_pos : 0 < volume K) :
    ∃ h : ℝ → ℝ, Measurable h ∧ (∀ s, s ∉ K → h s = 0) ∧ (∀ s, |h s| ≤ 1 / 2) ∧
      (∀ q : ℚ, (∫ s in Iic (q : ℝ), h s) ∈ Set.range ((↑) : ℚ → ℝ)) ∧
      (∀ q : ℚ, (∫ s in Iic (q : ℝ), s * h s) ∈ Set.range ((↑) : ℚ → ℝ)) ∧
      0 < ∫ s in Iic (2 : ℝ), h s := by
  classical
  -- Enumerate `ℚ` starting with `r 0 = -1`, `r 1 = 2`
  obtain ⟨eQ, heQ_surj⟩ := exists_surjective_nat ℚ
  let r : ℕ → ℚ := fun n ↦ match n with
    | 0 => -1
    | 1 => 2
    | k + 2 => eQ k
  have hr_surj : Function.Surjective r := fun q ↦ by
    obtain ⟨k, hk⟩ := heQ_surj q
    exact ⟨k + 2, hk⟩
  -- Initial function `H₂` supported on `K` with `|H₂| ≤ 1/4`, `∫ H₂ = q₀ > 0`, `∫ s H₂ = 0`
  obtain ⟨CK, hCK_pos, hK_mom⟩ := exists_supported_with_moments hK_meas hK_sub hK_pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (4 * CK)
  have hN₀_pos : 0 < N₀ := by
    have : (0 : ℝ) < 4 * CK := by positivity
    exact_mod_cast this.trans hN₀
  let q₀ : ℚ := (N₀ : ℚ)⁻¹
  have hq₀_pos : (0 : ℝ) < (q₀ : ℝ) := by
    dsimp only [q₀]; push_cast; positivity
  obtain ⟨H₂, hH₂_meas, hH₂_supp, hH₂_bound', hH₂_int0, hH₂_int1⟩ := hK_mom (q₀ : ℝ) 0
  have hH₂_bound : ∀ s, |H₂ s| ≤ 1 / 4 := fun s ↦ by
    have h1 := hH₂_bound' s
    rw [abs_zero, add_zero, abs_of_pos hq₀_pos] at h1
    have hN0r : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN₀_pos
    have hq_le : CK * (q₀ : ℝ) ≤ 1 / 4 := by
      dsimp only [q₀]; push_cast
      rw [mul_inv_le_iff₀ hN0r]
      linarith
    exact h1.trans hq_le
  let st₂ : MomentState K r q₀ 2 :=
    { H := H₂
      H_meas := hH₂_meas
      H_supp := hH₂_supp
      H_bound := fun s ↦ by
        have hsum : 0 ≤ ∑ j ∈ Finset.range 2, (1 / 2 : ℝ) ^ (j + 3) := by positivity
        linarith [hH₂_bound s]
      H_rat0 := fun j hj ↦ by
        have hj' : j = 0 ∨ j = 1 := by omega
        rcases hj' with rfl | rfl
        · refine ⟨0, ?_⟩
          have hr0' : (r 0 : ℝ) = -1 := by simp [r]
          rw [hr0', Rat.cast_zero, eq_comm]
          exact setIntegral_Iic_eq_zero_of_supp_disjoint hH₂_supp
            (Set.disjoint_left.2 fun s hsK hs1 ↦ by
              have := (hK_sub hsK).1; change s ≤ -1 at hs1; linarith)
        · refine ⟨q₀, ?_⟩
          have hr1' : (r 1 : ℝ) = 2 := by simp [r]
          rw [hr1', setIntegral_Iic_eq_of_supp_subset hH₂_supp
            (fun s hs ↦ (hK_sub hs).2.trans (by norm_num)), hH₂_int0]
      H_rat1 := fun j hj ↦ by
        have hj' : j = 0 ∨ j = 1 := by omega
        rcases hj' with rfl | rfl
        · refine ⟨0, ?_⟩
          have hr0' : (r 0 : ℝ) = -1 := by simp [r]
          rw [hr0', Rat.cast_zero, eq_comm]
          exact setIntegral_Iic_eq_zero_of_supp_disjoint (fun s hs ↦ by simp [hH₂_supp s hs])
            (Set.disjoint_left.2 fun s hsK hs1 ↦ by
              have := (hK_sub hsK).1; change s ≤ -1 at hs1; linarith)
        · refine ⟨0, ?_⟩
          have hr1' : (r 1 : ℝ) = 2 := by simp [r]
          rw [hr1', Rat.cast_zero, setIntegral_Iic_eq_of_supp_subset
            (fun s hs ↦ by simp [hH₂_supp s hs])
            (fun s hs ↦ (hK_sub hs).2.trans (by norm_num)), hH₂_int1]
      H_two_0 := by
        rw [setIntegral_Iic_eq_of_supp_subset hH₂_supp
          (fun s hs ↦ (hK_sub hs).2.trans (by norm_num)), hH₂_int0] }
  -- Recursive construction of `(st_m, δ_m)` for `m : ℕ` (step `n = m + 2`)
  let stepFn : ∀ (m : ℕ) (st : MomentState K r q₀ (m + 2)),
      Σ' (δ : ℝ → ℝ) (st' : MomentState K r q₀ (m + 3)),
        (∀ s, st'.H s = st.H s + δ s) ∧
        Measurable δ ∧ (∀ s, s ∉ K → δ s = 0) ∧
        (∀ s, |δ s| ≤ (1 / 2 : ℝ) ^ (m + 5)) ∧
        (∀ j < m + 2, ∫ s in Iic (r j : ℝ), δ s = 0) ∧
        (∀ j < m + 2, ∫ s in Iic (r j : ℝ), s * δ s = 0) := fun m st ↦ by
    have h := exists_next_momentState hK_meas hK_sub (rfl : r 0 = -1) (rfl : r 1 = 2)
      (by omega : 2 ≤ m + 2) st
    exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
      Classical.choose_spec (Classical.choose_spec h)⟩
  let seq : ∀ m : ℕ, MomentState K r q₀ (m + 2) := Nat.rec st₂ fun m st ↦ (stepFn m st).2.1
  let δ : ℕ → ℝ → ℝ := fun m ↦ (stepFn m (seq m)).1
  have hδ_spec : ∀ m : ℕ,
      (∀ s, (seq (m + 1)).H s = (seq m).H s + δ m s) ∧
      Measurable (δ m) ∧ (∀ s, s ∉ K → δ m s = 0) ∧
      (∀ s, |δ m s| ≤ (1 / 2 : ℝ) ^ (m + 5)) ∧
      (∀ j < m + 2, ∫ s in Iic (r j : ℝ), δ m s = 0) ∧
      (∀ j < m + 2, ∫ s in Iic (r j : ℝ), s * δ m s = 0) :=
    fun m ↦ (stepFn m (seq m)).2.2
  have hseq_sum : ∀ (m : ℕ) (s : ℝ), (seq m).H s = H₂ s + ∑ k ∈ Finset.range m, δ k s := by
    intro m s
    induction m with
    | zero => simp [seq, st₂]
    | succ m ih =>
      rw [(hδ_spec m).1 s, ih, Finset.sum_range_succ, add_assoc]
  -- Define `h s := H₂ s + ∑' m, δ m s`
  let h : ℝ → ℝ := fun s ↦ H₂ s + ∑' m : ℕ, δ m s
  have hgeom_sum : Summable fun m : ℕ ↦ (1 / 2 : ℝ) ^ (m + 5) := by
    have h1 : Summable fun m : ℕ ↦ (1 / 2 : ℝ) ^ m :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h2 : (fun m : ℕ ↦ (1 / 2 : ℝ) ^ (m + 5)) = fun m ↦ (1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ 5 :=
      funext fun m ↦ pow_add _ _ _
    rw [h2]
    exact h1.mul_right ((1 / 2 : ℝ) ^ 5)
  have hgeom_val : ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 5) = 1 / 16 := by
    have h1 : ∑' m : ℕ, (1 / 2 : ℝ) ^ m = 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    have h2 : (fun m : ℕ ↦ (1 / 2 : ℝ) ^ (m + 5)) = fun m ↦ (1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ 5 :=
      funext fun m ↦ pow_add _ _ _
    rw [h2, tsum_mul_right, h1]; norm_num
  have hδ_summable : ∀ s : ℝ, Summable fun m : ℕ ↦ δ m s := fun s ↦
    Summable.of_norm_bounded hgeom_sum fun m ↦ by
      rw [Real.norm_eq_abs]; exact (hδ_spec m).2.2.2.1 s
  have hh_meas : Measurable h := by
    refine hH₂_meas.add (measurable_of_tendsto_metrizable
      (f := fun N s ↦ ∑ m ∈ Finset.range N, δ m s)
      (fun N ↦ Finset.measurable_sum _ fun m _ ↦ (hδ_spec m).2.1) ?_)
    rw [tendsto_pi_nhds]
    intro s
    exact (hδ_summable s).hasSum.tendsto_sum_nat
  have hh_supp : ∀ s, s ∉ K → h s = 0 := fun s hsK ↦ by
    have h0 : ∀ m : ℕ, δ m s = 0 := fun m ↦ (hδ_spec m).2.2.1 s hsK
    simp [h, hH₂_supp s hsK, h0]
  have hh_bound : ∀ s, |h s| ≤ 1 / 2 := fun s ↦ by
    have htsum_le : |∑' m : ℕ, δ m s| ≤ ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 5) := by
      have h1 : ‖∑' m : ℕ, δ m s‖ ≤ ∑' m : ℕ, ‖δ m s‖ :=
        norm_tsum_le_tsum_norm (hδ_summable s).norm
      have h2 : ∑' m : ℕ, ‖δ m s‖ ≤ ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 5) :=
        Summable.tsum_le_tsum (fun m ↦ by rw [Real.norm_eq_abs]; exact (hδ_spec m).2.2.2.1 s)
          (hδ_summable s).norm hgeom_sum
      rw [Real.norm_eq_abs] at h1
      exact h1.trans h2
    calc |h s| ≤ |H₂ s| + |∑' m : ℕ, δ m s| := abs_add_le _ _
      _ ≤ 1 / 4 + 1 / 16 := add_le_add (hH₂_bound s) (hgeom_val ▸ htsum_le)
      _ ≤ 1 / 2 := by norm_num
  have hH₂_int : Integrable H₂ volume :=
    integrable_of_bounded_supp hH₂_meas hH₂_supp hK_sub hH₂_bound
  have hsH₂_int : Integrable (fun s ↦ s * H₂ s) volume :=
    integrable_of_bounded_supp (measurable_id.mul hH₂_meas) (fun s hs ↦ by simp [hH₂_supp s hs])
      hK_sub (fun s ↦ by
        by_cases hsK : s ∈ K
        · have hs01 := hK_sub hsK
          rw [abs_mul, abs_of_nonneg hs01.1]
          exact (mul_le_of_le_one_left (abs_nonneg _) hs01.2).trans (hH₂_bound s)
        · simp [hH₂_supp s hsK])
  have hδ_int : ∀ m : ℕ, Integrable (δ m) volume := fun m ↦
    integrable_of_bounded_supp (hδ_spec m).2.1 (hδ_spec m).2.2.1 hK_sub (hδ_spec m).2.2.2.1
  have hsδ_int : ∀ m : ℕ, Integrable (fun s ↦ s * δ m s) volume := fun m ↦
    integrable_of_bounded_supp (measurable_id.mul (hδ_spec m).2.1)
      (fun s hs ↦ by simp [(hδ_spec m).2.2.1 s hs]) hK_sub (fun s ↦ by
        by_cases hsK : s ∈ K
        · have hs01 := hK_sub hsK
          rw [abs_mul, abs_of_nonneg hs01.1]
          exact (mul_le_of_le_one_left (abs_nonneg _) hs01.2).trans ((hδ_spec m).2.2.2.1 s)
        · simp [(hδ_spec m).2.2.1 s hsK])
  have hδ_norm_le : ∀ (a : ℝ) (m : ℕ), ∫ s in Iic a, ‖δ m s‖ ≤ (1 / 2 : ℝ) ^ (m + 5) := fun a m ↦ by
    have hbound : ∀ s, ‖δ m s‖ ≤ (Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 / 2 : ℝ) ^ (m + 5)) s :=
      fun s ↦ by
        by_cases hs : s ∈ Icc (0 : ℝ) 1
        · simpa [hs, Real.norm_eq_abs] using (hδ_spec m).2.2.2.1 s
        · simp [hs, (hδ_spec m).2.2.1 s (fun hk ↦ hs (hK_sub hk))]
    have hdom : Integrable ((Icc (0 : ℝ) 1).indicator fun _ : ℝ ↦ (1 / 2 : ℝ) ^ (m + 5)) volume :=
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        |>.integrable_indicator measurableSet_Icc
    calc ∫ s in Iic a, ‖δ m s‖
        ≤ ∫ s, ‖δ m s‖ :=
          setIntegral_le_integral (hδ_int m).norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
      _ ≤ ∫ s, (Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 / 2 : ℝ) ^ (m + 5)) s :=
          integral_mono (hδ_int m).norm hdom hbound
      _ = (1 / 2 : ℝ) ^ (m + 5) := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
            Measure.real_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one,
            one_mul]
  have hsδ_norm_le : ∀ (a : ℝ) (m : ℕ),
      ∫ s in Iic a, ‖s * δ m s‖ ≤ (1 / 2 : ℝ) ^ (m + 5) := fun a m ↦ by
    have hle : ∀ s, ‖s * δ m s‖ ≤ ‖δ m s‖ := fun s ↦ by
      by_cases hsK : s ∈ K
      · have hs01 := hK_sub hsK
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hs01.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hs01.2
      · simp [(hδ_spec m).2.2.1 s hsK]
    exact (setIntegral_mono_on (hsδ_int m).norm.integrableOn (hδ_int m).norm.integrableOn
      measurableSet_Iic fun s _ ↦ hle s).trans (hδ_norm_le a m)
  have hh_tsum_int : Integrable (fun s ↦ ∑' m : ℕ, δ m s) volume :=
    integrable_of_bounded_supp (measurable_of_tendsto_metrizable
      (f := fun N s ↦ ∑ m ∈ Finset.range N, δ m s)
      (fun N ↦ Finset.measurable_sum _ fun m _ ↦ (hδ_spec m).2.1)
      (tendsto_pi_nhds.2 fun s ↦ (hδ_summable s).hasSum.tendsto_sum_nat))
      (fun s hsK ↦ by
        have h0 : ∀ m : ℕ, δ m s = 0 := fun m ↦ (hδ_spec m).2.2.1 s hsK
        simp [h0]) hK_sub (fun s ↦ by
          have h1 : ‖∑' m : ℕ, δ m s‖ ≤ ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 5) :=
            (norm_tsum_le_tsum_norm (hδ_summable s).norm).trans
              (Summable.tsum_le_tsum (fun m ↦ by rw [Real.norm_eq_abs]; exact (hδ_spec m).2.2.2.1 s)
                (hδ_summable s).norm hgeom_sum)
          rw [Real.norm_eq_abs, hgeom_val] at h1
          exact h1)
  have hsh_tsum_int : Integrable (fun s ↦ ∑' m : ℕ, s * δ m s) volume := by
    have heq : (fun s ↦ ∑' m : ℕ, s * δ m s) = fun s ↦ s * ∑' m : ℕ, δ m s :=
      funext fun s ↦ tsum_mul_left
    rw [heq]
    exact integrable_of_bounded_supp
      (measurable_id.mul (measurable_of_tendsto_metrizable
        (f := fun N s ↦ ∑ m ∈ Finset.range N, δ m s)
        (fun N ↦ Finset.measurable_sum _ fun m _ ↦ (hδ_spec m).2.1)
        (tendsto_pi_nhds.2 fun s ↦ (hδ_summable s).hasSum.tendsto_sum_nat)))
      (fun s hsK ↦ by
        have h0 : ∀ m : ℕ, δ m s = 0 := fun m ↦ (hδ_spec m).2.2.1 s hsK
        simp [h0]) hK_sub (fun s ↦ by
          by_cases hsK : s ∈ K
          · have hs01 := hK_sub hsK
            have h1 : |∑' m : ℕ, δ m s| ≤ 1 / 16 := by
              have h' : ‖∑' m : ℕ, δ m s‖ ≤ ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 5) :=
                (norm_tsum_le_tsum_norm (hδ_summable s).norm).trans
                  (Summable.tsum_le_tsum
                    (fun m ↦ by rw [Real.norm_eq_abs]; exact (hδ_spec m).2.2.2.1 s)
                    (hδ_summable s).norm hgeom_sum)
              rwa [Real.norm_eq_abs, hgeom_val] at h'
            rw [abs_mul, abs_of_nonneg hs01.1]
            exact (mul_le_of_le_one_left (abs_nonneg _) hs01.2).trans h1
          · have h0 : ∀ m : ℕ, δ m s = 0 := fun m ↦ (hδ_spec m).2.2.1 s hsK
            simp [h0])
  have hint_finset : ∀ (μ : Measure ℝ) (F : ℕ → ℝ → ℝ) (n : ℕ),
      (∀ m ∈ Finset.range n, Integrable (F m) μ) →
      Integrable (fun s ↦ ∑ m ∈ Finset.range n, F m s) μ := by
    intro μ F n hF
    induction n with
    | zero => simp
    | succ n ih =>
      simp_rw [Finset.sum_range_succ]
      exact (ih fun m hm ↦ hF m (Finset.mem_range.2 (by have := Finset.mem_range.1 hm; omega))).add
        (hF n (Finset.mem_range.2 (Nat.lt_succ_self n)))
  have hint_sum : ∀ (μ : Measure ℝ) (F : ℕ → ℝ → ℝ) (n : ℕ),
      (∀ m ∈ Finset.range n, Integrable (F m) μ) →
      (∫ s, ∑ m ∈ Finset.range n, F m s ∂μ) = ∑ m ∈ Finset.range n, ∫ s, F m s ∂μ := by
    intro μ F n hF
    induction n with
    | zero => simp
    | succ n ih =>
      simp_rw [Finset.sum_range_succ]
      rw [integral_add
        (hint_finset μ F n fun m hm ↦ hF m (Finset.mem_range.2 (by
          have := Finset.mem_range.1 hm; omega)))
        (hF n (Finset.mem_range.2 (Nat.lt_succ_self n))),
        ih fun m hm ↦ hF m (Finset.mem_range.2 (by have := Finset.mem_range.1 hm; omega))]
  -- Integral of `h` at `r j` equals integral of `(seq j).H` (rational!)
  have hh_at_r0 : ∀ j : ℕ, ∫ s in Iic (r j : ℝ), h s = ∫ s in Iic (r j : ℝ), (seq j).H s := by
    intro j
    have hsum := hasSum_integral_of_summable_integral_norm
      (μ := volume.restrict (Iic (r j : ℝ)))
      (fun m ↦ (hδ_int m).integrableOn)
      (Summable.of_nonneg_of_le (fun m ↦ integral_nonneg fun _ ↦ norm_nonneg _)
        (hδ_norm_le (r j : ℝ)) hgeom_sum)
    have htsum_eq : ∫ s in Iic (r j : ℝ), ∑' m : ℕ, δ m s =
        ∑' m : ℕ, ∫ s in Iic (r j : ℝ), δ m s := hsum.tsum_eq.symm
    have hfin : ∑' m : ℕ, ∫ s in Iic (r j : ℝ), δ m s =
        ∑ m ∈ Finset.range j, ∫ s in Iic (r j : ℝ), δ m s := by
      refine tsum_eq_sum fun m hm ↦ ?_
      rw [Finset.mem_range, not_lt] at hm
      exact (hδ_spec m).2.2.2.2.1 j (by omega)
    dsimp only [h]
    rw [integral_add hH₂_int.integrableOn hh_tsum_int.integrableOn, htsum_eq, hfin,
      ← hint_sum (volume.restrict (Iic (r j : ℝ))) δ j (fun m _ ↦ (hδ_int m).integrableOn),
      ← integral_add hH₂_int.integrableOn
        (hint_finset (volume.restrict (Iic (r j : ℝ))) δ j (fun m _ ↦ (hδ_int m).integrableOn))]
    congr 1; funext s
    exact (hseq_sum j s).symm
  have hh_at_r1 : ∀ j : ℕ, ∫ s in Iic (r j : ℝ), s * h s =
      ∫ s in Iic (r j : ℝ), s * (seq j).H s := by
    intro j
    have hmul : (fun s ↦ s * h s) = fun s ↦ s * H₂ s + ∑' m : ℕ, s * δ m s := funext fun s ↦ by
      dsimp only [h]; rw [mul_add, tsum_mul_left]
    have hsum := hasSum_integral_of_summable_integral_norm
      (μ := volume.restrict (Iic (r j : ℝ)))
      (fun m ↦ (hsδ_int m).integrableOn)
      (Summable.of_nonneg_of_le (fun m ↦ integral_nonneg fun _ ↦ norm_nonneg _)
        (hsδ_norm_le (r j : ℝ)) hgeom_sum)
    have htsum_eq : ∫ s in Iic (r j : ℝ), ∑' m : ℕ, s * δ m s =
        ∑' m : ℕ, ∫ s in Iic (r j : ℝ), s * δ m s := hsum.tsum_eq.symm
    have hfin : ∑' m : ℕ, ∫ s in Iic (r j : ℝ), s * δ m s =
        ∑ m ∈ Finset.range j, ∫ s in Iic (r j : ℝ), s * δ m s := by
      refine tsum_eq_sum fun m hm ↦ ?_
      rw [Finset.mem_range, not_lt] at hm
      exact (hδ_spec m).2.2.2.2.2 j (by omega)
    rw [hmul, integral_add hsH₂_int.integrableOn hsh_tsum_int.integrableOn, htsum_eq, hfin,
      ← hint_sum (volume.restrict (Iic (r j : ℝ))) (fun m s ↦ s * δ m s) j
        (fun m _ ↦ (hsδ_int m).integrableOn),
      ← integral_add hsH₂_int.integrableOn
        (hint_finset (volume.restrict (Iic (r j : ℝ))) (fun m s ↦ s * δ m s) j
          (fun m _ ↦ (hsδ_int m).integrableOn))]
    congr 1; funext s
    rw [hseq_sum j s, mul_add, Finset.mul_sum]
  refine ⟨h, hh_meas, hh_supp, hh_bound, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨j, rfl⟩ := hr_surj q
    rw [hh_at_r0 j]
    exact (seq j).H_rat0 j (by omega)
  · intro q
    obtain ⟨j, rfl⟩ := hr_surj q
    rw [hh_at_r1 j]
    exact (seq j).H_rat1 j (by omega)
  · have hr1' : (r 1 : ℝ) = 2 := by simp [r]
    rw [← hr1', hh_at_r0 1, hr1', (seq 1).H_two_0]
    exact hq₀_pos

/-! ### Step 4–6: Constructing the `C^{1,1}` diffeomorphism and proving Manai's Theorem 1.4 -/

private lemma hasDerivAt_integral_g {K : Set ℝ} (hK_sub : K ⊆ Icc (0 : ℝ) 1) {h : ℝ → ℝ}
    (hh_meas : Measurable h) (hh_supp : ∀ s, s ∉ K → h s = 0) (hh_bound : ∀ s, |h s| ≤ 1 / 2) :
    let g : ℝ → ℝ := fun x ↦ x + x * (∫ s in Iic x, h s) - ∫ s in Iic x, s * h s
    let g' : ℝ → ℝ := fun x ↦ 1 + ∫ s in Iic x, h s
    (∀ x : ℝ, HasDerivAt g (g' x) x) ∧
    (∀ x : ℝ, 1 / 2 ≤ g' x ∧ g' x ≤ 3 / 2) ∧
    LipschitzWith (1 / 2 : ℝ≥0) g' := by
  intro g g'
  have hh_int : Integrable h volume := integrable_of_bounded_supp hh_meas hh_supp hK_sub hh_bound
  have hsh_int : Integrable (fun s ↦ s * h s) volume :=
    integrable_of_bounded_supp (measurable_id.mul hh_meas) (fun s hs ↦ by simp [hh_supp s hs])
      hK_sub (fun s ↦ by
        by_cases hsK : s ∈ K
        · have hs01 := hK_sub hsK
          rw [abs_mul, abs_of_nonneg hs01.1]
          exact (mul_le_of_le_one_left (abs_nonneg _) hs01.2).trans (hh_bound s)
        · simp [hh_supp s hsK])
  have hsplit : ∀ (f : ℝ → ℝ), Integrable f volume → ∀ a b : ℝ, a ≤ b →
      ∫ s in Iic b, f s = (∫ s in Iic a, f s) + ∫ s in Ioc a b, f s := fun f hf a b hab ↦ by
    have hdisj : Disjoint (Iic a) (Ioc a b) :=
      Set.disjoint_left.2 fun _ h1 h2 ↦ not_le_of_gt h2.1 h1
    have hunion : Iic b = Iic a ∪ Ioc a b := by
      ext s; simp only [mem_Iic, mem_union, mem_Ioc]
      constructor
      · intro hsb; rcases le_or_gt s a with hsa | hsa
        · exact Or.inl hsa
        · exact Or.inr ⟨hsa, hsb⟩
      · rintro (hsa | ⟨_, hsb⟩)
        · exact hsa.trans hab
        · exact hsb
    rw [hunion, setIntegral_union hdisj measurableSet_Ioc hf.integrableOn hf.integrableOn]
  -- Remainder bound `|g y - g x - (y - x) * g' x| ≤ (1 / 2) * (y - x) ^ 2`
  have hrem : ∀ x y : ℝ, |g y - g x - (y - x) * g' x| ≤ (1 / 2) * (y - x) ^ 2 := by
    intro x y
    rcases le_total x y with hxy | hyx
    · have h1 := hsplit h hh_int x y hxy
      have h2 := hsplit (fun s ↦ s * h s) hsh_int x y hxy
      have hdiff : g y - g x - (y - x) * g' x = ∫ s in Ioc x y, (y - s) * h s := by
        have hlin : ∫ s in Ioc x y, (y - s) * h s =
            y * (∫ s in Ioc x y, h s) - ∫ s in Ioc x y, s * h s := by
          have heq : (fun s ↦ (y - s) * h s) = fun s ↦ y * h s - s * h s :=
            funext fun s ↦ sub_mul y s (h s)
          rw [heq, integral_sub (hh_int.integrableOn.const_mul y) hsh_int.integrableOn,
            integral_const_mul]
        rw [hlin]
        dsimp only [g, g']
        rw [h1, h2]
        ring
      rw [hdiff]
      have hbound_int : ∀ s ∈ Ioc x y, ‖(y - s) * h s‖ ≤ (1 / 2) * (y - x) := fun s hs ↦ by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hs.2)]
        have hys : y - s ≤ y - x := by linarith [hs.1]
        calc (y - s) * |h s| ≤ (y - x) * (1 / 2) :=
              mul_le_mul hys (hh_bound s) (abs_nonneg _) (sub_nonneg.2 hxy)
          _ = (1 / 2) * (y - x) := mul_comm _ _
      have hle := norm_setIntegral_le_of_norm_le_const (s := Ioc x y)
        (lt_top_iff_ne_top.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) hbound_int
      rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hxy] at hle
      calc |∫ s in Ioc x y, (y - s) * h s|
          ≤ (1 / 2) * (y - x) * (y - x) := hle
        _ = (1 / 2) * (y - x) ^ 2 := by ring
    · have h1 := hsplit h hh_int y x hyx
      have h2 := hsplit (fun s ↦ s * h s) hsh_int y x hyx
      have hdiff : g y - g x - (y - x) * g' x = ∫ s in Ioc y x, (s - y) * h s := by
        have hlin : ∫ s in Ioc y x, (s - y) * h s =
            (∫ s in Ioc y x, s * h s) - y * (∫ s in Ioc y x, h s) := by
          have heq : (fun s ↦ (s - y) * h s) = fun s ↦ s * h s - y * h s :=
            funext fun s ↦ sub_mul s y (h s)
          rw [heq, integral_sub hsh_int.integrableOn (hh_int.integrableOn.const_mul y),
            integral_const_mul]
        rw [hlin]
        dsimp only [g, g']
        rw [h1, h2]
        ring
      rw [hdiff]
      have hbound_int : ∀ s ∈ Ioc y x, ‖(s - y) * h s‖ ≤ (1 / 2) * (x - y) := fun s hs ↦ by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hs.1.le)]
        have hsy : s - y ≤ x - y := by linarith [hs.2]
        calc (s - y) * |h s| ≤ (x - y) * (1 / 2) :=
              mul_le_mul hsy (hh_bound s) (abs_nonneg _) (sub_nonneg.2 hyx)
          _ = (1 / 2) * (x - y) := mul_comm _ _
      have hle := norm_setIntegral_le_of_norm_le_const (s := Ioc y x)
        (lt_top_iff_ne_top.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) hbound_int
      rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hyx] at hle
      calc |∫ s in Ioc y x, (s - y) * h s|
          ≤ (1 / 2) * (x - y) * (x - y) := hle
        _ = (1 / 2) * (y - x) ^ 2 := by ring
  refine ⟨fun x ↦ ?_, fun x ↦ ?_, ?_⟩
  · rw [hasDerivAt_iff_tendsto]
    refine squeeze_zero_norm' (a := fun y ↦ (1 / 2 : ℝ) * |y - x|) ?_ ?_
    · filter_upwards with y
      by_cases hyx : y = x
      · simp [hyx]
      · have hne : |y - x| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 hyx)
        simp only [Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_inv, abs_abs]
        calc |y - x|⁻¹ * |g y - g x - (y - x) * g' x|
            ≤ |y - x|⁻¹ * ((1 / 2) * (y - x) ^ 2) :=
              mul_le_mul_of_nonneg_left (hrem x y) (inv_nonneg.2 (abs_nonneg _))
          _ = (1 / 2) * |y - x| := by
              rw [← sq_abs (y - x), sq]; field_simp [hne]
    · have hcont : Continuous (fun y : ℝ ↦ (1 / 2 : ℝ) * |y - x|) :=
        continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))
      simpa using hcont.tendsto x
  · have habs : |∫ s in Iic x, h s| ≤ 1 / 2 := by
      have hbound : ∀ s, ‖h s‖ ≤ (Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 / 2 : ℝ)) s := fun s ↦ by
        by_cases hs : s ∈ Icc (0 : ℝ) 1
        · simpa [hs, Real.norm_eq_abs] using hh_bound s
        · simp [hs, hh_supp s (fun hk ↦ hs (hK_sub hk))]
      have hdom : Integrable ((Icc (0 : ℝ) 1).indicator fun _ : ℝ ↦ (1 / 2 : ℝ)) volume :=
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
          |>.integrable_indicator measurableSet_Icc
      calc |∫ s in Iic x, h s|
          = ‖∫ s in Iic x, h s‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in Iic x, ‖h s‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ s, ‖h s‖ :=
            setIntegral_le_integral hh_int.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
        _ ≤ ∫ s, (Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 / 2 : ℝ)) s :=
            integral_mono hh_int.norm hdom hbound
        _ = 1 / 2 := by
            rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
              Measure.real_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one,
              one_mul]
    rw [abs_le] at habs
    dsimp only [g']
    constructor <;> linarith
  · refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.dist_eq, Real.dist_eq]
    push_cast
    rcases le_total x y with hxy | hyx
    · rw [abs_sub_comm (g' x), abs_sub_comm x]
      have hdiff : g' y - g' x = ∫ s in Ioc x y, h s := by
        dsimp only [g']; rw [hsplit h hh_int x y hxy]; ring
      rw [hdiff, abs_of_nonneg (sub_nonneg.2 hxy)]
      have hle := norm_setIntegral_le_of_norm_le_const (f := h) (s := Ioc x y) (C := 1 / 2)
        (lt_top_iff_ne_top.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        (fun s _ ↦ by rw [Real.norm_eq_abs]; exact hh_bound s)
      rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hxy] at hle
      exact hle
    · have hdiff : g' x - g' y = ∫ s in Ioc y x, h s := by
        dsimp only [g']; rw [hsplit h hh_int y x hyx]; ring
      rw [hdiff, abs_of_nonneg (sub_nonneg.2 hyx)]
      have hle := norm_setIntegral_le_of_norm_le_const (f := h) (s := Ioc y x) (C := 1 / 2)
        (lt_top_iff_ne_top.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        (fun s _ ↦ by rw [Real.norm_eq_abs]; exact hh_bound s)
      rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hyx] at hle
      exact hle

end NormalNumbers.C11Sharpness

namespace Real

open MeasureTheory Set NormalNumbers.C11Sharpness

/-- **Manai's Theorem 1.4 (`C^{1,1}` sharpness of `C²` affine rigidity)**:
there exists a non-affine, strictly increasing `C^{1,1}` diffeomorphism `e : ℝ ≃ ℝ` (with both
`deriv e` and `deriv e.symm` globally Lipschitz) that preserves base-`b` normality for *every*
integer base `b ≥ 2`, and hence preserves absolute normality. -/
theorem exists_nonAffine_C11_diffeomorph_preserves_isNormalIn :
    ∃ e : ℝ ≃ ℝ, StrictMono e ∧ ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧
      (∃ C : NNReal, LipschitzWith C (deriv e)) ∧
      (∃ C : NNReal, LipschitzWith C (deriv e.symm)) ∧
      (¬ ∃ a c : ℝ, ∀ x : ℝ, e x = a * x + c) ∧
      (∀ b : ℕ, 2 ≤ b → ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (e x)) ∧
      (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (e x)) := by
  obtain ⟨K, hK_comp, hK_sub, hK_norm, hK_pos⟩ := exists_compact_absolutelyNormal_pos_volume
  obtain ⟨h, hh_meas, hh_supp, hh_bound, hh_rat0, hh_rat1, hh_pos2⟩ :=
    exists_rational_moment_density hK_comp.measurableSet hK_sub hK_pos
  let g : ℝ → ℝ := fun x ↦ x + x * (∫ s in Iic x, h s) - ∫ s in Iic x, s * h s
  let g' : ℝ → ℝ := fun x ↦ 1 + ∫ s in Iic x, h s
  obtain ⟨hg_hasDeriv, hg'_bounds, hg'_lip⟩ := hasDerivAt_integral_g hK_sub hh_meas hh_supp hh_bound
  have hg_deriv : deriv g = g' := funext fun x ↦ (hg_hasDeriv x).deriv
  have hg_diff : Differentiable ℝ g := fun x ↦ (hg_hasDeriv x).differentiableAt
  have hg_contDiff : ContDiff ℝ 1 g :=
    contDiff_one_iff_deriv.2 ⟨hg_diff, hg_deriv ▸ hg'_lip.continuous⟩
  have hg_cont : Continuous g := hg_diff.continuous
  -- Bilipschitz & strict monotonicity of `g` via Mean Value Theorem
  have hg_growth : ∀ x y : ℝ, x ≤ y → (1 / 2) * (y - x) ≤ g y - g x := by
    intro x y hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g g' hlt hg_cont.continuousOn
        (fun z _ ↦ hg_hasDeriv z)
      have hpos : 0 < y - x := sub_pos.2 hlt
      rw [eq_div_iff hpos.ne'] at hc
      nlinarith [(hg'_bounds c).1]
  have hg_mono : StrictMono g := fun x y hxy ↦ by
    have := hg_growth x y hxy.le
    linarith
  have hg_surj : Function.Surjective g := fun y ↦ by
    have hlow : g (min 0 (2 * (y - g 0))) ≤ y := by
      have h1 : min 0 (2 * (y - g 0)) ≤ 0 := min_le_left _ _
      have h2 := hg_growth (min 0 (2 * (y - g 0))) 0 h1
      have h3 : min 0 (2 * (y - g 0)) ≤ 2 * (y - g 0) := min_le_right _ _
      linarith
    have hhigh : y ≤ g (max 0 (2 * (y - g 0))) := by
      have h1 : 0 ≤ max 0 (2 * (y - g 0)) := le_max_left _ _
      have h2 := hg_growth 0 (max 0 (2 * (y - g 0))) h1
      have h3 : 2 * (y - g 0) ≤ max 0 (2 * (y - g 0)) := le_max_right _ _
      linarith
    have hle : min 0 (2 * (y - g 0)) ≤ max 0 (2 * (y - g 0)) :=
      (min_le_left _ _).trans (le_max_left _ _)
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hle hg_cont.continuousOn ⟨hlow, hhigh⟩
    exact ⟨x, hx⟩
  let eg : ℝ ≃ ℝ := Equiv.ofBijective g ⟨hg_mono.injective, hg_surj⟩
  let e : ℝ ≃ ℝ := eg.symm
  have he_left : ∀ x, e (g x) = x := eg.symm_apply_apply
  have he_right : ∀ y, g (e y) = y := eg.apply_symm_apply
  have he_symm_eq : (e.symm : ℝ → ℝ) = g := rfl
  have he_mono : StrictMono e := fun y₁ y₂ hy ↦ by
    by_contra hle
    push Not at hle
    have := hg_mono.monotone hle
    rw [he_right y₁, he_right y₂] at this
    linarith
  have he_lip : LipschitzWith 2 e := by
    refine LipschitzWith.of_dist_le_mul fun y₁ y₂ ↦ ?_
    rw [Real.dist_eq, Real.dist_eq]
    push_cast
    rcases le_total y₁ y₂ with h12 | h21
    · have hle : e y₁ ≤ e y₂ := he_mono.monotone h12
      have hgrow := hg_growth (e y₁) (e y₂) hle
      rw [he_right y₁, he_right y₂] at hgrow
      rw [abs_sub_comm (e y₁), abs_of_nonneg (sub_nonneg.2 hle),
        abs_sub_comm y₁, abs_of_nonneg (sub_nonneg.2 h12)]
      linarith
    · have hle : e y₂ ≤ e y₁ := he_mono.monotone h21
      have hgrow := hg_growth (e y₂) (e y₁) hle
      rw [he_right y₁, he_right y₂] at hgrow
      rw [abs_of_nonneg (sub_nonneg.2 hle), abs_of_nonneg (sub_nonneg.2 h21)]
      linarith
  have he_hasDeriv : ∀ y : ℝ, HasDerivAt e (g' (e y))⁻¹ y := fun y ↦
    (hg_hasDeriv (e y)).of_local_left_inverse he_lip.continuous.continuousAt
      (by linarith [(hg'_bounds (e y)).1]) (Eventually.of_forall he_right)
  have he_deriv : deriv e = fun y ↦ (g' (e y))⁻¹ := funext fun y ↦ (he_hasDeriv y).deriv
  have he_deriv_lip : LipschitzWith 4 (deriv e) := by
    refine LipschitzWith.of_dist_le_mul fun y₁ y₂ ↦ ?_
    rw [he_deriv, Real.dist_eq, Real.dist_eq]
    push_cast
    set a := g' (e y₁)
    set c := g' (e y₂)
    have ha : 1 / 2 ≤ a := (hg'_bounds (e y₁)).1
    have hc : 1 / 2 ≤ c := (hg'_bounds (e y₂)).1
    have ha_pos : 0 < a := by linarith
    have hc_pos : 0 < c := by linarith
    have hinv : |a⁻¹ - c⁻¹| = |c - a| / (a * c) := by
      rw [inv_sub_inv ha_pos.ne' hc_pos.ne', abs_div, abs_of_pos (mul_pos ha_pos hc_pos)]
    have h1 : |c - a| / (a * c) ≤ 4 * |a - c| := by
      rw [abs_sub_comm c a, div_le_iff₀ (mul_pos ha_pos hc_pos)]
      have hac : 1 / 4 ≤ a * c := by nlinarith
      nlinarith [abs_nonneg (a - c)]
    have h2 : |a - c| ≤ (1 / 2) * |e y₁ - e y₂| := by
      have h := hg'_lip.dist_le_mul (e y₁) (e y₂)
      rw [Real.dist_eq, Real.dist_eq] at h
      push_cast at h
      exact h
    have h3 : |e y₁ - e y₂| ≤ 2 * |y₁ - y₂| := by
      have h := he_lip.dist_le_mul y₁ y₂
      rw [Real.dist_eq, Real.dist_eq] at h
      push_cast at h
      exact h
    linarith
  have he_contDiff : ContDiff ℝ 1 e :=
    contDiff_one_iff_deriv.2 ⟨fun y ↦ (he_hasDeriv y).differentiableAt, he_deriv_lip.continuous⟩
  -- `e` is non-affine because `g' (-1) = 1 ≠ 1 + ∫_{Iic 2} h = g' 2`
  have he_nonAffine : ¬ ∃ a c : ℝ, ∀ y : ℝ, e y = a * y + c := by
    rintro ⟨a, c, haff⟩
    have ha0 : a ≠ 0 := by
      intro h0
      have h1 : e 0 = e 1 := by simp [haff, h0]
      exact zero_ne_one (e.injective h1)
    have hg_aff : ∀ x : ℝ, g x = a⁻¹ * x - a⁻¹ * c := fun x ↦ by
      have hx : x = a * g x + c := by simpa [he_left x] using haff (g x)
      field_simp [ha0]
      linarith
    have hg'_const : ∀ x : ℝ, g' x = a⁻¹ := fun x ↦ by
      have hd : HasDerivAt g a⁻¹ x := by
        have h1 : HasDerivAt (fun t : ℝ ↦ a⁻¹ * t - a⁻¹ * c) (a⁻¹ * 1) x :=
          ((hasDerivAt_id x).const_mul a⁻¹).sub_const _
        rw [mul_one] at h1
        exact h1.congr_of_eventuallyEq (Eventually.of_forall hg_aff)
      exact (hg_hasDeriv x).unique hd
    have hneg1 : g' (-1) = 1 := by
      dsimp only [g']
      rw [setIntegral_Iic_eq_zero_of_supp_disjoint hh_supp
        (Set.disjoint_left.2 fun s hsK hs1 ↦ by
          have := (hK_sub hsK).1; change s ≤ -1 at hs1; linarith), add_zero]
    have htwo : g' 2 = 1 + ∫ s in Iic (2 : ℝ), h s := rfl
    linarith [hg'_const (-1), hg'_const 2, hneg1, htwo, hh_pos2]
  -- `e` preserves base-`b` normality for EVERY base `b ≥ 2`
  have he_pres : ∀ b : ℕ, 2 ≤ b → ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (e x) := by
    intro b hb x hx
    by_contra hnot
    set y := e x
    have hyK : y ∉ K := fun hy ↦ hnot (hK_norm y hy b hb)
    have hopen : IsOpen Kᶜ := hK_comp.isClosed.isOpen_compl
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.1 hopen y hyK
    obtain ⟨q, hq_gt, hq_lt⟩ := exists_rat_btwn (show y < y + ε by linarith)
    have hdisj_Ioc : K ∩ Ioc y (q : ℝ) = ∅ := by
      ext s
      simp only [mem_inter_iff, mem_Ioc, mem_empty_iff_false, iff_false]
      rintro ⟨hsK, hs1, hs2⟩
      have hs_ball : s ∈ Metric.ball y ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hs1)]
        linarith
      exact hball hs_ball hsK
    have hzero : volume (K ∩ Ioc y (q : ℝ)) = 0 := by rw [hdisj_Ioc, measure_empty]
    have h0_eq : ∫ s in Iic y, h s = ∫ s in Iic (q : ℝ), h s :=
      (setIntegral_Iic_eq_of_measure_Ioc_zero hq_gt.le hh_supp hzero).symm
    have h1_eq : ∫ s in Iic y, s * h s = ∫ s in Iic (q : ℝ), s * h s :=
      (setIntegral_Iic_eq_of_measure_Ioc_zero (f := fun s ↦ s * h s) hq_gt.le
        (fun s hs ↦ by simp [hh_supp s hs]) hzero).symm
    obtain ⟨q0, hq0⟩ := hh_rat0 q
    obtain ⟨q1, hq1⟩ := hh_rat1 q
    have hg_eq : g y = ((1 + q0 : ℚ) : ℝ) * y + ((-q1 : ℚ) : ℝ) := by
      dsimp only [g]
      rw [h0_eq, h1_eq, ← hq0, ← hq1]
      push_cast; ring
    have hslope_ne : (1 + q0 : ℚ) ≠ 0 := by
      intro h0
      have hr : (1 : ℝ) + (q0 : ℝ) = 0 := by exact_mod_cast h0
      have hg'y : g' y = 1 + (q0 : ℝ) := by dsimp only [g']; rw [h0_eq, ← hq0]
      linarith [(hg'_bounds y).1]
    have hx_eq : x = ((1 + q0 : ℚ) : ℝ) * y + ((-q1 : ℚ) : ℝ) := by
      rw [← hg_eq, he_right x]
    rw [hx_eq] at hx
    exact hnot ((isNormalIn_mul_add_ratCast_iff hb hslope_ne (-q1)).1 hx)
  exact ⟨e, he_mono, he_contDiff, hg_contDiff, ⟨4, he_deriv_lip⟩, ⟨1 / 2, hg_deriv ▸ hg'_lip⟩,
    he_nonAffine, he_pres, fun x hx b hb ↦ he_pres b hb x (hx b hb)⟩

/-- Corollary: there exists a non-affine `C^{1,1}` diffeomorphism of `ℝ` (with globally Lipschitz
derivative) preserving absolute normality. -/
theorem exists_nonAffine_C11_diffeomorph_preserves_isAbsolutelyNormal_forward :
    ∃ e : ℝ ≃ ℝ, ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧ LocallyLipschitz (deriv e) ∧
      (¬ ∃ a c : ℝ, ∀ x : ℝ, e x = a * x + c) ∧
      (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (e x)) := by
  obtain ⟨e, _, he1, he2, ⟨C, hC⟩, _, hna, _, habs⟩ :=
    exists_nonAffine_C11_diffeomorph_preserves_isNormalIn
  exact ⟨e, he1, he2, hC.locallyLipschitz, hna, habs⟩

end Real

