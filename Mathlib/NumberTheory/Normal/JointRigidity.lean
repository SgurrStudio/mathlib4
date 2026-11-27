/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.JointWeyl
public import Mathlib.NumberTheory.Normal.MulRigidity
public import Mathlib.NumberTheory.Normal.Preservation
public import Mathlib.NumberTheory.Normal.Rigidity

/-!
# 2D `C²` affine rigidity for joint normality

Building on `Mathlib.NumberTheory.Normal.JointWeyl`, `Mathlib.NumberTheory.Normal.Rigidity`, and
`Mathlib.NumberTheory.Normal.MulRigidity`, we prove the 2D `C²` affine rigidity dichotomy for
jointly normal pairs `(x, y) ∈ ℝ × ℝ`:

1. **Fractal decay joint normality** (`ae_isJointlyAbsolutelyNormal_of_polyDecay`,
   `ae_isJointlyAbsolutelyNormal_of_polyDecayB`): any pushforward Cantor measure with polynomial
   Fourier decay is almost surely jointly absolutely normal with any fixed absolutely normal `y`.
2. **2D `C²` non-affine counterexample**
   (`Real.exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff`): every non-affine `C²`
   function `F : ℝ × ℝ → ℝ` maps some jointly absolutely normal pair to a non-normal real.
3. **Full 2D `C²` affine rigidity dichotomy**
   (`Real.exists_affine_of_contDiff_two_preserves_isJointlyNormalIn`,
   `Real.exists_rat_affine_of_contDiff_two_preserves_isJointlyNormalIn`,
   `Real.contDiff_two_preserves_isJointlyNormalIn_dichotomy`,
   `Real.exists_const_contDiff_two_preserves_isJointlyNormalIn`): every `C²` map
   `F : ℝ × ℝ → ℝ × ℝ` preserving `IsJointlyNormalIn b` is either constant (with a jointly normal
   value) or an invertible rational-linear affine map `A(x, y) + c` with `A ∈ GL_2(ℚ)` and
   `c₁, c₂ ∈ normalAddPreservers hb`.
4. **Concrete 2D non-preservation corollaries** for `(x * y, y)`, `(x + y, x * y)`, and
   `(x ^ 2, y ^ 2)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology ComplexConjugate
open scoped ENNReal
open NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare
open NormalNumbers.CantorSelfSimilar NormalNumbers.QuarterCantorDecay
open NormalNumbers.BaseCantorDecay NormalNumbers.MulRigidity

/-! ### Part 4: 2D `C²` non-affine counterexample -/

namespace NormalNumbers.JointRigidity

open DecayAeNormal ExplicitSquare CantorSelfSimilar QuarterCantorDecay BaseCantorDecay Rigidity

/-- **Polynomial Fourier decay ⇒ a.s. joint absolute normality with any fixed absolutely normal
`y`**. -/
theorem ae_isJointlyAbsolutelyNormal_of_decay {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∀ᵐ ω ∂μ, Real.IsJointlyAbsolutelyNormal (G ω) y := by
  simp only [Real.IsJointlyAbsolutelyNormal]
  rw [ae_all_iff]; intro c
  by_cases hc : 2 ≤ c
  · have hall : ∀ᵐ ω ∂μ, ∀ h₁ h₂ : ℤ, (h₁, h₂) ≠ (0, 0) →
        Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          ee ((h₁ : ℝ) * (c : ℝ) ^ n * G ω + (h₂ : ℝ) * (c : ℝ) ^ n * y)) atTop (𝓝 0) := by
      rw [ae_all_iff]; intro h₁
      rw [ae_all_iff]; intro h₂
      by_cases hh₁ : h₁ = 0
      · subst hh₁
        by_cases hh₂ : h₂ = 0
        · subst hh₂; exact Eventually.of_forall fun _ h ↦ absurd rfl h
        · have hyW := (Real.isNormalIn_iff_tendsto_weylSum hc).1 (hy c hc) h₂ hh₂
          refine Eventually.of_forall fun ω _ ↦ hyW.congr fun N ↦ ?_
          rw [div_eq_inv_mul]
          congr 1
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          unfold ee; congr 1; push_cast; ring
      · have hlam : (h₁ : ℝ) ≠ 0 := by exact_mod_cast hh₁
        have hae := ae_tendsto_twisted_weyl_of_decay μ hc G hG hC hδ hdec
          (fun n ↦ (h₂ : ℝ) * (c : ℝ) ^ n * y) hlam
        filter_upwards [hae] with ω hω _
        refine hω.congr fun N ↦ ?_
        congr 1
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        congr 1; ring
    filter_upwards [hall] with ω hω _
    exact (Real.isJointlyNormalIn_iff_weyl hc _ _).2 hω
  · exact Eventually.of_forall fun _ h ↦ absurd h hc

/-- Pushforward of quarter-Cantor measure with polynomial decay is a.s. jointly absolutely normal
with any fixed absolutely normal `y`. -/
theorem ae_isJointlyAbsolutelyNormal_of_polyDecay {F : ℝ → ℝ} (hF : Measurable F)
    (hd : PolyDecay F) {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∀ᵐ ω ∂coinMeasure, Real.IsJointlyAbsolutelyNormal (F (cantorReal ω)) y := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := hd
  exact ae_isJointlyAbsolutelyNormal_of_decay coinMeasure (fun ω ↦ F (cantorReal ω))
    (hF.comp measurable_cantorReal) hC hδ hdec hy

/-- Pushforward of base-`b` Cantor measure with polynomial decay is a.s. jointly absolutely normal
with any fixed absolutely normal `y`. -/
theorem ae_isJointlyAbsolutelyNormal_of_polyDecayB {b : ℕ} {F : ℝ → ℝ} (hF : Measurable F)
    (hd : PolyDecayB b F) {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∀ᵐ ω ∂coinMeasure, Real.IsJointlyAbsolutelyNormal (F (bReal b ω)) y := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := hd
  exact ae_isJointlyAbsolutelyNormal_of_decay coinMeasure (fun ω ↦ F (bReal b ω))
    (hF.comp measurable_bReal) hC hδ hdec hy

/-- Window witness jointly normal with a fixed absolutely normal `y`. -/
theorem exists_joint_of_window {b : ℕ} (hb : 2 ≤ b) {f G G' G'' : ℝ → ℝ} {a A : ℝ} {q s : ℚ}
    (hs : s ≠ 0) (ha : 0 < a) (hGm : Measurable G)
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (G' t) t)
    (hG' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G' (G'' t) t)
    (hlo : ∀ t ∈ Icc (0 : ℝ) 1, a ≤ |G'' t|) (hhi : ∀ t ∈ Icc (0 : ℝ) 1, |G'' t| ≤ A)
    (hsign : (∀ t ∈ Icc (0 : ℝ) 1, 0 < G'' t) ∨ ∀ t ∈ Icc (0 : ℝ) 1, G'' t < 0)
    (hfG : ∀ t ∈ Icc (0 : ℝ) 1, f (G t) = s * t + q)
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∃ x : ℝ, Real.IsJointlyAbsolutelyNormal x y ∧ ¬ Real.IsNormalIn b (f x) := by
  rcases (show b = 2 ∨ 3 ≤ b by omega) with rfl | hb3
  · have hW : ∀ t ∈ QuarterCantorDecay.W, t ∈ Icc (0 : ℝ) 1 :=
      fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
    have hd : PolyDecay G := polyDecay_of_abs ha hGm (fun t ht ↦ hG t (hW t ht))
      (fun t ht ↦ hG' t (hW t ht)) (fun t ht ↦ hlo t (hW t ht)) (fun t ht ↦ hhi t (hW t ht))
      (hsign.imp (fun h t ht ↦ h t (hW t ht)) (fun h t ht ↦ h t (hW t ht)))
    obtain ⟨ω, hω⟩ := (ae_isJointlyAbsolutelyNormal_of_polyDecay hGm hd hy).exists
    refine ⟨_, hω, fun h ↦ ?_⟩
    rw [hfG _ (hW _ (cantorReal_mem_window ω)), Real.isNormalIn_mul_add_ratCast_iff le_rfl hs] at h
    exact not_isNormalIn_two_pow_cantorReal ω one_pos (by simpa using h)
  · have hd : PolyDecayB b G := polyDecayB_of_abs hb ha hGm hG hG' hlo hhi hsign
    obtain ⟨ω, hω⟩ := (ae_isJointlyAbsolutelyNormal_of_polyDecayB hGm hd hy).exists
    refine ⟨_, hω, fun h ↦ ?_⟩
    rw [hfG _ (bReal_mem hb ω), Real.isNormalIn_mul_add_ratCast_iff hb hs] at h
    have := not_isNormalIn_bReal_add hb3 ω 0
    simp only [Int.cast_zero, add_zero] at this
    exact this h

open Classical in
/-- Core 1D local-inverse construction producing a witness jointly absolutely normal with a fixed
absolutely normal `y`. -/
theorem exists_joint_of_pos {b : ℕ} (hb : 2 ≤ b) {f F' F'' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt f (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hc1 : Continuous F') (hc2 : Continuous F'') {p : ℝ} (h1 : 0 < F' p) (h2 : F'' p ≠ 0)
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∃ x : ℝ, Real.IsJointlyAbsolutelyNormal x y ∧ ¬ Real.IsNormalIn b (f x) := by
  have h2' : 0 < |F'' p| := abs_pos.2 h2
  obtain ⟨δ1, hδ1, H1⟩ := Metric.continuous_iff.1 hc1 p (F' p / 2) (by positivity)
  obtain ⟨δ2, hδ2, H2⟩ := Metric.continuous_iff.1 hc2 p (|F'' p| / 2) (by positivity)
  set ε := min δ1 δ2 / 2 with hεdef
  have hε : 0 < ε := by positivity
  set u := p - ε
  set v := p + ε
  have huv : u < v := by simp only [u, v]; linarith
  have hd : ∀ x ∈ Icc u v, dist x p < δ1 ∧ dist x p < δ2 := fun x hx ↦ by
    have : |x - p| ≤ ε := abs_le.2 ⟨by simp only [u] at hx; linarith [hx.1],
      by simp only [v] at hx; linarith [hx.2]⟩
    rw [Real.dist_eq]
    constructor <;> [have := min_le_left δ1 δ2; have := min_le_right δ1 δ2] <;> linarith
  have hb1 : ∀ x ∈ Icc u v, F' p / 2 < F' x ∧ F' x < 3 * F' p / 2 := fun x hx ↦ by
    have := H1 x (hd x hx).1; rw [Real.dist_eq, abs_sub_lt_iff] at this
    constructor <;> linarith
  have hb2 : ∀ x ∈ Icc u v, |F'' x - F'' p| < |F'' p| / 2 := fun x hx ↦ by
    have := H2 x (hd x hx).2; rwa [Real.dist_eq] at this
  have hfI : ∀ x ∈ Icc u v, HasDerivAt f (F' x) x := fun x _ ↦ hF x
  have hpos : ∀ x ∈ Icc u v, 0 < F' x := fun x hx ↦ by linarith [(hb1 x hx).1]
  have hm := Rigidity.strictMonoOn hfI hpos
  have hpI : p ∈ Icc u v := ⟨by simp only [u]; linarith, by simp only [v]; linarith⟩
  have hα : f u < f p := hm ⟨le_rfl, huv.le⟩ hpI (by simp only [u]; linarith)
  have hβ : f p < f v := hm hpI ⟨huv.le, le_rfl⟩ (by simp only [v]; linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hα
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (sub_pos.2 (hq2.trans hβ))
  have hs1' : (0 : ℝ) < s := by exact_mod_cast hs1
  set g := Rigidity.inv f u v
  set U : Set ℝ := {t : ℝ | (s : ℝ) * t + q ∈ Ioo (f u) (f v)}
  have haff_c : Continuous fun t : ℝ ↦ (s : ℝ) * t + q := by fun_prop
  have hU : IsOpen U := isOpen_Ioo.preimage haff_c
  have hIU : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ U := fun t ht ↦ by
    simp only [U, mem_ofPred_eq, mem_Ioo]
    constructor <;> nlinarith [ht.1, ht.2]
  set G0 : ℝ → ℝ := fun t ↦ g (s * t + q)
  set G : ℝ → ℝ := U.piecewise G0 fun _ ↦ 0
  have haff : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ (s : ℝ) * t + q) s t := fun t ↦
    (((hasDerivAt_id' t).const_mul (s : ℝ)).add_const (q : ℝ)).congr_deriv (mul_one _)
  have hG0 : ∀ t ∈ U, HasDerivAt G0 ((F' (G0 t))⁻¹ * s) t := fun t ht ↦
    (Rigidity.hasDerivAt_inv huv hfI hpos ht).comp t (haff t)
  have hG0I : ∀ t ∈ U, G0 t ∈ Icc u v := fun t ht ↦
    (Rigidity.inv_spec huv hfI (Ioo_subset_Icc_self ht)).1
  have hGeq : ∀ t ∈ U, G =ᶠ[𝓝 t] G0 := fun t ht ↦ by
    filter_upwards [hU.mem_nhds ht] with z hz
    simp [G, hz]
  set G' : ℝ → ℝ := fun t ↦ (F' (G0 t))⁻¹ * s
  set G'' : ℝ → ℝ := fun t ↦ -(F'' (G0 t)) * s ^ 2 / F' (G0 t) ^ 3
  have hG : ∀ t ∈ U, HasDerivAt G (G' t) t := fun t ht ↦
    (hG0 t ht).congr_of_eventuallyEq (hGeq t ht)
  have hG' : ∀ t ∈ U, HasDerivAt G' (G'' t) t := fun t ht ↦ by
    have hne : F' (G0 t) ≠ 0 := (hpos _ (hG0I t ht)).ne'
    exact ((((hF' (G0 t)).comp t (hG0 t ht)).inv hne).mul_const (s : ℝ)).congr_deriv
      (by simp only [G'', Function.comp]; field_simp)
  have hGm : Measurable G := by
    refine ContinuousOn.measurable_piecewise (fun t ht ↦ ?_) continuousOn_const hU.measurableSet
    exact ((Rigidity.continuousAt_inv huv hfI hpos ht).comp (f := fun t : ℝ ↦ (s : ℝ) * t + q)
      haff_c.continuousAt).continuousWithinAt
  have habs : ∀ t ∈ Icc (0 : ℝ) 1, |G'' t| = |F'' (G0 t)| * s ^ 2 / F' (G0 t) ^ 3 :=
    fun t ht ↦ by
    have := hpos _ (hG0I t (hIU t ht))
    simp only [G'']
    rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < F' (G0 t) ^ 3),
      abs_of_pos (by positivity : (0 : ℝ) < (s : ℝ) ^ 2)]
  refine exists_joint_of_window hb (q := q) (show s ≠ 0 by exact_mod_cast hs1.ne')
    (G := G) (G' := G') (G'' := G'')
    (a := |F'' p| / 2 * s ^ 2 / (3 * F' p / 2) ^ 3)
    (A := 3 * |F'' p| / 2 * s ^ 2 / (F' p / 2) ^ 3) (by positivity) hGm
    (fun t ht ↦ hG t (hIU t ht)) (fun t ht ↦ hG' t (hIU t ht)) (fun t ht ↦ ?_)
    (fun t ht ↦ ?_) ?_ (fun t ht ↦ ?_) hy
  · have hx := hG0I t (hIU t ht)
    have e1 := hb1 _ hx
    have e2 := hb2 _ hx
    have e3 : |F'' p| / 2 ≤ |F'' (G0 t)| := by
      have := abs_sub_abs_le_abs_sub (F'' p) (F'' (G0 t))
      rw [abs_sub_comm] at this; linarith
    have hp0 := hpos _ hx
    rw [habs t ht]
    exact div_le_div₀ (by positivity) (by gcongr) (by positivity)
      (pow_le_pow_left₀ (by linarith) e1.2.le 3)
  · have hx := hG0I t (hIU t ht)
    have e1 := hb1 _ hx
    have e2 := hb2 _ hx
    have e3 : |F'' (G0 t)| ≤ 3 * |F'' p| / 2 := by
      have := abs_sub_abs_le_abs_sub (F'' (G0 t)) (F'' p)
      linarith
    have hp0 := hpos _ hx
    rw [habs t ht]
    exact div_le_div₀ (by positivity) (by gcongr) (by positivity)
      (pow_le_pow_left₀ (by linarith) e1.1.le 3)
  · rcases lt_or_gt_of_ne h2 with hneg | hpos'
    · refine Or.inl fun t ht ↦ ?_
      have hx := hG0I t (hIU t ht)
      have e2 := hb2 _ hx
      rw [abs_of_neg hneg, abs_lt] at e2
      have : F'' (G0 t) < 0 := by linarith
      have := hpos _ hx
      simp only [G'']
      apply div_pos _ (by positivity)
      have : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
      nlinarith
    · refine Or.inr fun t ht ↦ ?_
      have hx := hG0I t (hIU t ht)
      have e2 := hb2 _ hx
      rw [abs_of_pos hpos', abs_lt] at e2
      have : 0 < F'' (G0 t) := by linarith
      have := hpos _ hx
      simp only [G'']
      apply div_neg_of_neg_of_pos _ (by positivity)
      have : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
      nlinarith
  · have htU := hIU t ht
    simp only [G, Set.piecewise, htU, ite_true, G0]
    exact (Rigidity.inv_spec huv hfI (Ioo_subset_Icc_self htU)).2

/-- For any non-affine `C²` function `f : ℝ → ℝ` and any fixed absolutely normal `y`, there exists
`x` jointly absolutely normal with `y` such that `f x` is not normal in base `b`. -/
theorem exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff_1d {b : ℕ} (hb : 2 ≤ b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hna : ¬ ∃ a c : ℝ, ∀ x, f x = a * x + c)
    {y : ℝ} (hy : Real.IsAbsolutelyNormal y) :
    ∃ x : ℝ, Real.IsJointlyAbsolutelyNormal x y ∧ ¬ Real.IsNormalIn b (f x) := by
  obtain ⟨p, hp1, hp2⟩ := Rigidity.exists_deriv_ne_zero hf hna
  have hc1 : Continuous (deriv f) := (Rigidity.contDiff_deriv hf).continuous
  rcases lt_or_gt_of_ne hp1 with hneg | hpos
  · obtain ⟨x, hx, h⟩ := exists_joint_of_pos hb (f := fun x ↦ -f x) (F' := fun x ↦ -deriv f x)
      (F'' := fun x ↦ -deriv (deriv f) x) (fun x ↦ (Rigidity.hasDerivAt_deriv hf x).neg)
      (fun x ↦ (Rigidity.hasDerivAt_deriv_deriv hf x).neg) hc1.neg
      (Rigidity.continuous_deriv_deriv hf).neg (p := p) (by linarith) (neg_ne_zero.2 hp2) hy
    exact ⟨x, hx, fun h' ↦ h (h'.neg hb)⟩
  · exact exists_joint_of_pos hb (Rigidity.hasDerivAt_deriv hf)
      (Rigidity.hasDerivAt_deriv_deriv hf) hc1 (Rigidity.continuous_deriv_deriv hf) hpos hp2 hy

/-- The set of absolutely normal numbers is dense in `ℝ`. -/
theorem dense_isAbsolutelyNormal : Dense {x : ℝ | Real.IsAbsolutelyNormal x} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  have hpos : 0 < volume U := hU.measure_pos volume hne
  have hnull : volume {x : ℝ | ¬ Real.IsAbsolutelyNormal x} = 0 :=
    Real.volume_setOf_not_isAbsolutelyNormal
  by_contra hdisj
  have hsub : U ⊆ {x : ℝ | ¬ Real.IsAbsolutelyNormal x} := by
    intro x hxU hxnorm
    exact hdisj ⟨x, hxU, hxnorm⟩
  exact hpos.ne' (measure_mono_null hsub hnull)

private theorem isAffine_of_dense {g : ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2)
    (h : ∀ y, Real.IsAbsolutelyNormal y → ∃ a c : ℝ, ∀ x, g x y = a * x + c) :
    ∀ x y, g x y = (g 1 y - g 0 y) * x + g 0 y := by
  intro x y
  have hcl : IsClosed {t : ℝ | g x t = (g 1 t - g 0 t) * x + g 0 t} :=
    isClosed_eq (hg.comp (continuous_const.prodMk continuous_id))
      ((((hg.comp (continuous_const.prodMk continuous_id)).sub
        (hg.comp (continuous_const.prodMk continuous_id))).mul continuous_const).add
        (hg.comp (continuous_const.prodMk continuous_id)))
  have hsub : {t : ℝ | Real.IsAbsolutelyNormal t} ⊆
      {t : ℝ | g x t = (g 1 t - g 0 t) * x + g 0 t} := by
    intro t ht
    obtain ⟨a, c, hac⟩ := h t ht
    simp only [mem_ofPred_eq, hac]
    ring
  have huniv : {t : ℝ | g x t = (g 1 t - g 0 t) * x + g 0 t} = Set.univ := by
    rw [← hcl.closure_eq]
    exact Set.eq_univ_of_subset (closure_mono hsub) dense_isAbsolutelyNormal.closure_eq
  have : y ∈ {t : ℝ | g x t = (g 1 t - g 0 t) * x + g 0 t} := by rw [huniv]; trivial
  exact this

end NormalNumbers.JointRigidity

namespace Real

open NormalNumbers.JointRigidity

/-- **2D `C²` non-affine counterexample**: if `F₁ : ℝ × ℝ → ℝ` is `C²` and not globally affine,
then for every base `b ≥ 2` there exist jointly absolutely normal `x, y` with `F₁ (x, y)` not
normal in base `b`. -/
theorem exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff {b : ℕ} (hb : 2 ≤ b)
    {F₁ : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F₁)
    (hna : ¬ ∃ a₁ a₂ c : ℝ, ∀ p : ℝ × ℝ, F₁ p = a₁ * p.1 + a₂ * p.2 + c) :
    ∃ x y : ℝ, IsJointlyAbsolutelyNormal x y ∧ ¬ IsNormalIn b (F₁ (x, y)) := by
  by_cases h1 : ∃ y, IsAbsolutelyNormal y ∧ ¬ ∃ a c : ℝ, ∀ x, F₁ (x, y) = a * x + c
  · obtain ⟨y, hy, hna1⟩ := h1
    have hf : ContDiff ℝ 2 fun x : ℝ ↦ F₁ (x, y) := hF.comp (contDiff_id.prodMk contDiff_const)
    obtain ⟨x, hxy, hnot⟩ :=
      exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff_1d hb hf hna1 hy
    exact ⟨x, y, hxy, hnot⟩
  by_cases h2 : ∃ x, IsAbsolutelyNormal x ∧ ¬ ∃ a c : ℝ, ∀ y, F₁ (x, y) = a * y + c
  · obtain ⟨x, hx, hna2⟩ := h2
    have hf : ContDiff ℝ 2 fun y : ℝ ↦ F₁ (x, y) := hF.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨y, hyx, hnot⟩ :=
      exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff_1d hb hf hna2 hx
    exact ⟨x, y, hyx.symm, hnot⟩
  by_cases h3 : ∃ v, IsAbsolutelyNormal v ∧ ¬ ∃ a c : ℝ, ∀ u, F₁ (u, u + v) = a * u + c
  · obtain ⟨v, hv, hna3⟩ := h3
    have hf : ContDiff ℝ 2 fun u : ℝ ↦ F₁ (u, u + v) :=
      hF.comp (contDiff_id.prodMk (contDiff_id.add contDiff_const))
    obtain ⟨u, huv, hnot⟩ :=
      exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff_1d hb hf hna3 hv
    have hgl : IsJointlyAbsolutelyNormal u (u + v) := by
      have := huv.linear_rat (a₁₁ := 1) (a₁₂ := 0) (a₂₁ := 1) (a₂₂ := 1) (by norm_num)
      simpa using this
    exact ⟨u, u + v, hgl, hnot⟩
  -- Otherwise all three families of slices are affine for all dense absolutely normal parameters,
  -- hence everywhere by continuity, forcing `F₁` to be globally affine.
  exfalso
  push Not at h1 h2 h3
  have hc : Continuous F₁ := hF.continuous
  have hH := isAffine_of_dense (g := fun x y ↦ F₁ (x, y)) hc h1
  have hV := isAffine_of_dense (g := fun y x ↦ F₁ (x, y)) (hc.comp continuous_swap) h2
  have hD := isAffine_of_dense (g := fun u v ↦ F₁ (u, u + v))
    (hc.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))) h3
  set d : ℝ := F₁ (1, 1) - F₁ (1, 0) - F₁ (0, 1) + F₁ (0, 0)
  set a₁ : ℝ := F₁ (1, 0) - F₁ (0, 0)
  set a₂ : ℝ := F₁ (0, 1) - F₁ (0, 0)
  set c : ℝ := F₁ (0, 0)
  have hbil : ∀ x y : ℝ, F₁ (x, y) = d * x * y + a₁ * x + a₂ * y + c := fun x y ↦ by
    have hx := hH x y
    have h0 := hV y 0
    have h1' := hV y 1
    rw [h0, h1'] at hx
    simp only [d, a₁, a₂, c]
    linarith
  have hd0 : d = 0 := by
    have h22 := hD 2 0
    simp only [add_zero] at h22
    have e22 := hbil 2 2
    have e11 := hbil 1 1
    have e00 := hbil 0 0
    linarith
  refine hna ⟨a₁, a₂, c, fun p ↦ ?_⟩
  have := hbil p.1 p.2
  rw [hd0, zero_mul, zero_mul, zero_add] at this
  exact this

end Real

/-! ### Part 5: Twisted multiplicative rigidity and full 2D `C²` affine rigidity -/

namespace NormalNumbers.JointRigidity

open DecayAeNormal ExplicitSquare CantorSelfSimilar BaseCantorDecay MulRigidity

/-- Twisted martingale increment `u (K + t) * incr b θ K i t ω`. -/
private def twIncr (u : ℕ → ℂ) (b : ℕ) (θ : ℝ) (K i t : ℕ) (ω : ℕ → Bool) : ℂ :=
  u (K + t) * MulRigidity.incr b θ K i t ω

private theorem ae_tendsto_twIncr (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (b : ℕ) (θ : ℝ) (K i : ℕ) :
    ∀ᵐ ω ∂coinMeasure, Tendsto
      (fun N : ℕ ↦ (∑ t ∈ Finset.range N, twIncr u b θ K i t ω) / (N : ℂ)) atTop (𝓝 0) := by
  have hwb : ∀ n ω, ‖wf b θ n ω‖ ≤ 1 := fun n ω ↦ (norm_wf θ n ω).le
  have hm0 : ∀ t, Measurable (MulRigidity.incr b θ K i t) := fun t ↦
    ((measurable_condE _ (measurable_wf θ _)).sub
      (measurable_condE _ (measurable_wf θ _))).div_const _
  have hm : ∀ t, Measurable (twIncr u b θ K i t) := fun t ↦ measurable_const.mul (hm0 t)
  have hb : ∀ t ω, ‖twIncr u b θ K i t ω‖ ≤ 1 := fun t ω ↦ by
    simp only [twIncr, norm_mul, hu, one_mul]
    exact norm_incr_le θ K i t ω
  refine ae_tendsto_avg_of_orthogonal coinMeasure (fun t ↦ twIncr u b θ K i t) hm hb
    fun t t' htt' ↦ ?_
  set φ : (ℕ → Bool) → ℂ := fun ω ↦ conj (MulRigidity.incr b θ K i t ω) / 2
  have hφm : Measurable φ := (Complex.continuous_conj.measurable.comp (hm0 t)).div_const _
  have hφd : DepOn (t' + i) φ := by
    intro ω ω' h
    simp only [φ, MulRigidity.incr]
    rw [(depOn_condE (t + i + 1) _).mono (by omega) ω ω' h,
      (depOn_condE (t + i) _).mono (by omega) ω ω' h]
  have hφb : ∀ ω, ‖φ ω‖ ≤ 1 := fun ω ↦ by
    simp only [φ, norm_div, Complex.norm_conj, Complex.norm_ofNat]
    linarith [norm_incr_le (b := b) θ K i t ω]
  have horth0 := integral_mul_condE_sub (m := t' + i) hφm hφd hφb (measurable_wf θ (K + t'))
    (hwb (K + t'))
  have hrew : (fun ω ↦ conj (twIncr u b θ K i t ω) * twIncr u b θ K i t' ω) =
      fun ω ↦ (conj (u (K + t)) * u (K + t')) *
        (φ ω * (condE (t' + i + 1) (wf b θ (K + t')) ω -
          condE (t' + i) (wf b θ (K + t')) ω)) := by
    funext ω
    simp only [twIncr, φ, MulRigidity.incr, map_mul]
    ring
  rw [hrew, integral_const_mul, horth0, mul_zero]

/-- Twisted version of `MulRigidity.ae_tendsto_weyl`: multiplying `e(θ b^n Y)` by any unit-modulus
deterministic sequence `u n` preserves a.s. vanishing of Weyl means for irrational `θ`. -/
private theorem ae_tendsto_weyl_twisted {b : ℕ} (hb : 2 ≤ b) {θ : ℝ} (hθ : Irrational θ)
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1) :
    ∀ᵐ ω ∂coinMeasure, Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.range N, u n * wf b θ n ω) / (N : ℂ)) atTop (𝓝 0) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have key : ∀ j : ℕ, ∀ᵐ ω ∂coinMeasure, ∃ C : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, u n * wf b θ n ω‖ ≤ (1 / ((j : ℝ) + 1)) * N + C := by
    intro j
    set ε : ℝ := 1 / ((j : ℝ) + 1)
    have hε : 0 < ε := by positivity
    obtain ⟨K, hK⟩ := ((tendsto_prod_cos hb hθ).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).exists
    have hLt : Tendsto (fun L : ℕ ↦ 2 * Real.pi * |θ| / (b : ℝ) ^ L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hb1)
    obtain ⟨L, hL⟩ := (hLt.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).exists
    have hall : ∀ᵐ ω ∂coinMeasure, ∀ i : ℕ, Tendsto
        (fun N : ℕ ↦ (∑ t ∈ Finset.range N, twIncr u b θ K i t ω) / (N : ℂ)) atTop (𝓝 0) :=
      ae_all_iff.2 fun i ↦ ae_tendsto_twIncr u hu b θ K i
    filter_upwards [hall] with ω hω
    have hsum : Tendsto (fun N : ℕ ↦ ∑ i ∈ Finset.range (K + L),
        ‖(∑ t ∈ Finset.range N, twIncr u b θ K i t ω) / (N : ℂ)‖) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.range (K + L)) fun i _ ↦ (hω i).norm
    obtain ⟨M0, hM0⟩ := eventually_atTop.1
      (hsum.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 6 by positivity)))
    set C1 : ℝ := 2 * ((K + L : ℕ) : ℝ) * (M0 : ℝ)
    have hC1 : 0 ≤ C1 := by positivity
    have hZ : ∀ M : ℕ, 2 * ∑ i ∈ Finset.range (K + L),
        ‖∑ t ∈ Finset.range M, twIncr u b θ K i t ω‖ ≤ ε / 3 * M + C1 := by
      intro M
      by_cases hM : M0 ≤ M ∧ 0 < M
      · have h := hM0 M hM.1
        have hMpos : (0 : ℝ) < M := by exact_mod_cast hM.2
        have : ∑ i ∈ Finset.range (K + L), ‖∑ t ∈ Finset.range M, twIncr u b θ K i t ω‖ =
            M * ∑ i ∈ Finset.range (K + L),
              ‖(∑ t ∈ Finset.range M, twIncr u b θ K i t ω) / (M : ℂ)‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [norm_div, Complex.norm_natCast]; field_simp
        rw [this]; nlinarith
      · have hMM : M ≤ M0 := by by_contra hc; exact hM ⟨by omega, by omega⟩
        have hb' : ∀ i, ‖∑ t ∈ Finset.range M, twIncr u b θ K i t ω‖ ≤ M0 := fun i ↦ by
          calc ‖∑ t ∈ Finset.range M, twIncr u b θ K i t ω‖
              ≤ ∑ t ∈ Finset.range M, ‖twIncr u b θ K i t ω‖ := norm_sum_le _ _
            _ ≤ ∑ _t ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum fun t _ ↦ by
                simp only [twIncr, norm_mul, hu, one_mul]; exact norm_incr_le (b := b) θ K i t ω
            _ = (M : ℝ) := by simp
            _ ≤ (M0 : ℝ) := by exact_mod_cast hMM
        have : ∑ i ∈ Finset.range (K + L), ‖∑ t ∈ Finset.range M, twIncr u b θ K i t ω‖ ≤
            ((K + L : ℕ) : ℝ) * M0 := by
          simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.range (K + L)) ↦ hb' i
        have : 0 ≤ ε / 3 * M := by positivity
        simp only [C1]; nlinarith
    have hshift : ∀ M : ℕ, ‖∑ t ∈ Finset.range M, u (K + t) * wf b θ (K + t) ω‖ ≤ ε * M + C1 := by
      intro M
      have hdec : ∀ t, u (K + t) * wf b θ (K + t) ω =
          u (K + t) * (wf b θ (K + t) ω - condE (K + t + L) (wf b θ (K + t)) ω) +
            2 * ∑ i ∈ Finset.range (K + L), twIncr u b θ K i t ω +
            u (K + t) * condE t (wf b θ (K + t)) ω := by
        intro t
        have htel : ∑ i ∈ Finset.range (K + L), twIncr u b θ K i t ω =
            u (K + t) *
              ((condE (t + (K + L)) (wf b θ (K + t)) ω - condE t (wf b θ (K + t)) ω) / 2) := by
          simp only [twIncr, ← Finset.mul_sum, MulRigidity.incr, ← Finset.sum_div]
          congr 2
          exact Finset.sum_range_sub (fun i ↦ condE (t + i) (wf b θ (K + t)) ω) (K + L)
        rw [htel, show t + (K + L) = K + t + L by omega]
        ring
      rw [Finset.sum_congr rfl fun t _ ↦ hdec t, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_comm]
      have h1 : ‖∑ t ∈ Finset.range M,
          u (K + t) * (wf b θ (K + t) ω - condE (K + t + L) (wf b θ (K + t)) ω)‖ ≤ ε / 3 * M := by
        calc _ ≤ ∑ t ∈ Finset.range M,
              ‖u (K + t) * (wf b θ (K + t) ω - condE (K + t + L) (wf b θ (K + t)) ω)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _t ∈ Finset.range M, (ε / 3) := Finset.sum_le_sum fun t _ ↦ by
              rw [norm_mul, hu, one_mul]
              exact (norm_wf_sub_condE_le hb θ (K + t) L ω).trans hL.le
          _ = ε / 3 * M := by simp [mul_comm]
      have h3 : ‖∑ t ∈ Finset.range M, u (K + t) * condE t (wf b θ (K + t)) ω‖ ≤ ε / 3 * M := by
        calc _ ≤ ∑ t ∈ Finset.range M, ‖u (K + t) * condE t (wf b θ (K + t)) ω‖ := norm_sum_le _ _
          _ ≤ ∑ _t ∈ Finset.range M, (ε / 3) := Finset.sum_le_sum fun t _ ↦ by
              rw [norm_mul, hu, one_mul]
              exact (norm_condE_wf_le_prod hb θ K t ω).trans hK.le
          _ = ε / 3 * M := by simp [mul_comm]
      have h2 : ‖2 * ∑ i ∈ Finset.range (K + L), ∑ t ∈ Finset.range M, twIncr u b θ K i t ω‖ ≤
          ε / 3 * M + C1 := by
        rw [norm_mul, Complex.norm_ofNat]
        refine le_trans ?_ (hZ M)
        gcongr; exact norm_sum_le _ _
      refine (norm_add_le _ _).trans ?_
      have := norm_add_le
        (∑ t ∈ Finset.range M,
          u (K + t) * (wf b θ (K + t) ω - condE (K + t + L) (wf b θ (K + t)) ω))
        (2 * ∑ i ∈ Finset.range (K + L), ∑ t ∈ Finset.range M, twIncr u b θ K i t ω)
      linarith [h1, h2, h3]
    refine ⟨C1 + K, fun N ↦ ?_⟩
    have hεN : 0 ≤ ε * N := by positivity
    rcases le_or_gt N K with hNK | hNK
    · have : ‖∑ n ∈ Finset.range N, u n * wf b θ n ω‖ ≤ N := by
        calc _ ≤ ∑ n ∈ Finset.range N, ‖u n * wf b θ n ω‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ by
              rw [norm_mul, hu, one_mul]; exact (norm_wf θ n ω).le
          _ = (N : ℝ) := by simp
      have : (N : ℝ) ≤ K := by exact_mod_cast hNK
      linarith
    · obtain ⟨M, rfl⟩ : ∃ M, N = K + M := ⟨N - K, by omega⟩
      rw [Finset.sum_range_add]
      have hK' : ‖∑ n ∈ Finset.range K, u n * wf b θ n ω‖ ≤ K := by
        calc _ ≤ ∑ n ∈ Finset.range K, ‖u n * wf b θ n ω‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ by
              rw [norm_mul, hu, one_mul]; exact (norm_wf θ n ω).le
          _ = (K : ℝ) := by simp
      have hMN : ε * M ≤ ε * ((K + M : ℕ) : ℝ) := by gcongr; exact_mod_cast Nat.le_add_left M K
      linarith [norm_add_le (∑ n ∈ Finset.range K, u n * wf b θ n ω)
        (∑ t ∈ Finset.range M, u (K + t) * wf b θ (K + t) ω), hshift M]
  filter_upwards [ae_all_iff.2 key] with ω hω
  refine tendsto_avg_of_bound fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨C, hC⟩ := hω j
  exact ⟨C, fun N ↦ (hC N).trans (by gcongr)⟩

/-- For irrational `θ` and any real shift `d`, `θ * bReal b ω + d` is normal in base `b` for
almost every Cantor point `ω`. -/
theorem ae_isNormal_mul_bReal_add {b : ℕ} (hb : 2 ≤ b) {θ : ℝ} (hθ : Irrational θ) (d : ℝ) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (θ * bReal b ω + d) := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ ↦
      (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * (θ * bReal b ω + d))) / (N : ℂ))
      atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Eventually.of_forall fun _ hne ↦ absurd hh hne
    · have hae := ae_tendsto_weyl_twisted hb (hθ.intCast_mul hh)
        (fun k ↦ ee ((h : ℝ) * (b : ℝ) ^ k * d)) (fun _ ↦ norm_ee _)
      filter_upwards [hae] with ω hω _
      refine hω.congr fun N ↦ ?_
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      unfold wf
      rw [← ee_add]
      congr 1; ring
  filter_upwards [hall] with ω hω
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (fun _ ↦ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) fun h hh ↦ ?_
  refine (hω h hh).congr fun N ↦ ?_
  rw [LevinSparse.fourierMean_orbit]

/-- **1D affine multiplicative-additive rigidity**: if `x ↦ r * x + c` with `r ≠ 0` preserves
base-`b` normality, then `r` is a nonzero rational and `c ∈ Real.normalAddPreservers hb`. -/
theorem rat_and_addPreserver_of_preserves_affine {b : ℕ} (hb : 2 ≤ b) {r c : ℝ} (hr : r ≠ 0)
    (hpres : ∀ x : ℝ, Real.IsNormalIn b x → Real.IsNormalIn b (r * x + c)) :
    (∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = r) ∧ c ∈ Real.normalAddPreservers hb := by
  have hrat : ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = r := by
    by_cases hirr : Irrational r
    · exfalso
      have hB : 2 ≤ b ^ 2 := by nlinarith
      have hB3 : 3 ≤ b ^ 2 := by nlinarith
      obtain ⟨ω, hω⟩ := (ae_isNormal_mul_bReal_add hB hirr.inv (-(r⁻¹ * c))).exists
      set z : ℝ := r⁻¹ * bReal (b ^ 2) ω + -(r⁻¹ * c)
      have hz : Real.IsNormalIn b z := ((Real.isNormalIn_iff_isNormal _ _).2 hω).of_pow hb two_pos
      have hrz : Real.IsNormalIn b (r * z + c) := hpres z hz
      have heq : r * z + c = bReal (b ^ 2) ω := by
        simp only [z]; field_simp; ring
      rw [heq] at hrz
      exact not_isNormal_bReal hB3 ω ((Real.isNormalIn_iff_isNormal _ _).1 (hrz.pow hb two_pos))
    · obtain ⟨q, rfl⟩ : ∃ q : ℚ, (q : ℝ) = r := not_not.1 hirr
      exact ⟨q, by exact_mod_cast hr, rfl⟩
  obtain ⟨q, hq, rfl⟩ := hrat
  refine ⟨⟨q, hq, rfl⟩, fun x hx ↦ ?_⟩
  have hqx : Real.IsNormalIn b ((q⁻¹ : ℚ) * x) := by
    simpa using (Real.isNormalIn_mul_add_ratCast_iff hb (inv_ne_zero hq) 0 (x := x)).2 hx
  have hres := hpres _ hqx
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  convert hres using 1
  push_cast; field_simp

/-- If an affine form `r₁ * x + r₂ * y + c` with `(r₁, r₂) ≠ (0, 0)` maps every base-`b` jointly
normal pair to a base-`b` normal number, then `r₁, r₂ ∈ ℚ` and `c ∈ normalAddPreservers hb`. -/
theorem rat_and_addPreserver_of_affine_joint {b : ℕ} (hb : 2 ≤ b) {r₁ r₂ c : ℝ}
    (hne : r₁ ≠ 0 ∨ r₂ ≠ 0)
    (hpres : ∀ x y : ℝ, Real.IsJointlyNormalIn b x y → Real.IsNormalIn b (r₁ * x + r₂ * y + c)) :
    (∃ q₁ q₂ : ℚ, (q₁ : ℝ) = r₁ ∧ (q₂ : ℝ) = r₂) ∧ c ∈ Real.normalAddPreservers hb := by
  -- Helper assuming first coefficient is nonzero
  have hfirst : ∀ (a₁ a₂ d : ℝ), a₁ ≠ 0 →
      (∀ x y : ℝ, Real.IsJointlyNormalIn b x y → Real.IsNormalIn b (a₁ * x + a₂ * y + d)) →
      (∃ q₁ q₂ : ℚ, (q₁ : ℝ) = a₁ ∧ (q₂ : ℝ) = a₂) ∧ d ∈ Real.normalAddPreservers hb := by
    intro a₁ a₂ d ha₁ hp
    -- Step 1: `a₂ / a₁` is rational (otherwise irrational-slope line hits `0`)
    have hratio : ∃ s : ℚ, (s : ℝ) = a₂ / a₁ := by
      by_contra h
      have hirr : Irrational (a₂ / a₁) := h
      obtain ⟨y, hy⟩ := (Real.ae_isJointlyAbsolutelyNormal_irrational_line hirr (-d / a₁)).exists
      have h0 := hp (-(a₂ / a₁) * y + (-d / a₁)) y (hy b hb)
      have heq : a₁ * (-(a₂ / a₁) * y + -d / a₁) + a₂ * y + d = 0 := by field_simp; ring
      rw [heq] at h0
      exact (h0.irrational hb).ne_zero rfl
    obtain ⟨s, hs⟩ := hratio
    -- Step 2: `z ↦ a₁ * z + d` preserves `IsNormalIn b`
    have h1d : ∀ z : ℝ, Real.IsNormalIn b z → Real.IsNormalIn b (a₁ * z + d) := by
      intro z hz
      obtain ⟨y, hzy⟩ := (Real.ae_isJointlyNormalIn_of_isNormalIn hb hz).exists
      have hgl : Real.IsJointlyNormalIn b (z + (-s : ℚ) * y) y := by
        have := hzy.linear_rat hb (a₁₁ := 1) (a₁₂ := -s) (a₂₁ := 0) (a₂₂ := 1) (by norm_num)
        simpa using this
      have hres := hp _ _ hgl
      convert hres using 1
      have ha₂ : a₂ = a₁ * (s : ℝ) := by rw [hs]; field_simp
      rw [ha₂]; push_cast; ring
    obtain ⟨⟨q₁, hq₁, rfl⟩, hd⟩ := rat_and_addPreserver_of_preserves_affine hb ha₁ h1d
    refine ⟨⟨q₁, q₁ * s, rfl, ?_⟩, hd⟩
    push_cast; rw [hs]; field_simp
  rcases hne with h1 | h2
  · exact hfirst r₁ r₂ c h1 hpres
  · have hp' : ∀ x y : ℝ, Real.IsJointlyNormalIn b x y → Real.IsNormalIn b (r₂ * x + r₁ * y + c) :=
      fun x y hxy ↦ by
        have := hpres y x (hxy.symm hb)
        convert this using 1; ring
    obtain ⟨⟨q₂, q₁, rfl, rfl⟩, hc⟩ := hfirst r₂ r₁ c h2 hp'
    exact ⟨⟨q₁, q₂, rfl, rfl⟩, hc⟩

/-- `normalAddPreservers hb` is closed under multiplication by nonzero rationals. -/
private theorem ratCast_mul_mem_normalAddPreservers {b : ℕ} (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0)
    {c : ℝ} (hc : c ∈ Real.normalAddPreservers hb) :
    (q : ℝ) * c ∈ Real.normalAddPreservers hb := by
  intro x hx
  have h1 : Real.IsNormalIn b ((q⁻¹ : ℚ) * x) := by
    simpa using (Real.isNormalIn_mul_add_ratCast_iff hb (inv_ne_zero hq) 0 (x := x)).2 hx
  have h2 : Real.IsNormalIn b ((q⁻¹ : ℚ) * x + c) := hc _ h1
  have h3 : Real.IsNormalIn b ((q : ℝ) * ((q⁻¹ : ℚ) * x + c)) := by
    simpa using (Real.isNormalIn_mul_add_ratCast_iff hb hq 0 (x := (q⁻¹ : ℚ) * x + c)).2 h2
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  convert h3 using 1
  push_cast; field_simp

/-- If `(u, q * u + t)` is jointly normal in base `b ≥ 2` for some `u` and rational `q`, then
`t` is normal in base `b`. -/
private theorem isNormalIn_of_isJointlyNormalIn_rat_mul_add {b : ℕ} (hb : 2 ≤ b) {u t : ℝ}
    {q : ℚ} (h : Real.IsJointlyNormalIn b u ((q : ℝ) * u + t)) :
    Real.IsNormalIn b t := by
  have hd : (q.den : ℕ) ≠ 0 := q.den_ne_zero
  have hdpos : 0 < q.den := q.den_pos
  have hdZ : (q.den : ℤ) ≠ 0 := by exact_mod_cast hd
  have hdt : Real.IsNormalIn b ((q.den : ℝ) * t) := by
    rw [Real.isNormalIn_iff_tendsto_weylSum hb]
    intro k hk
    have hW := (Real.isJointlyNormalIn_iff_weyl hb _ _).1 h (-(k * q.num)) (k * q.den)
      (fun h0 ↦ mul_ne_zero hk hdZ (congrArg Prod.snd h0))
    refine hW.congr fun N ↦ ?_
    rw [div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    unfold ee; congr 1
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have hdR : (q.den : ℝ) ≠ 0 := by exact_mod_cast hd
    rw [hq]
    push_cast
    field_simp
    ring
  have := (Real.isNormalIn_mul_add_ratCast_iff hb (q := (q.den : ℚ))
    (by exact_mod_cast hd) 0 (x := t)).1 (by simpa using hdt)
  exact this

end NormalNumbers.JointRigidity

namespace Real

open NormalNumbers.JointRigidity

/-- **2D `C²` affine rigidity (affine form)**: every `C²` map `F : ℝ × ℝ → ℝ × ℝ` preserving
base-`b` joint normality (`b ≥ 2`) is globally affine. -/
theorem exists_affine_of_contDiff_two_preserves_isJointlyNormalIn {b : ℕ} (hb : 2 ≤ b)
    {F : ℝ × ℝ → ℝ × ℝ} (hF : ContDiff ℝ 2 F)
    (hpres : ∀ x y : ℝ, IsJointlyNormalIn b x y →
      IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2) :
    ∃ a₁₁ a₁₂ c₁ a₂₁ a₂₂ c₂ : ℝ, ∀ x y : ℝ,
      F (x, y) = (a₁₁ * x + a₁₂ * y + c₁, a₂₁ * x + a₂₂ * y + c₂) := by
  have h1 : ∃ a₁₁ a₁₂ c₁ : ℝ, ∀ p : ℝ × ℝ, (F p).1 = a₁₁ * p.1 + a₁₂ * p.2 + c₁ := by
    by_contra hna
    obtain ⟨x, y, hxy, hnot⟩ :=
      exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff hb (contDiff_fst.comp hF) hna
    exact hnot ((hpres x y (hxy b hb)).left hb)
  have h2 : ∃ a₂₁ a₂₂ c₂ : ℝ, ∀ p : ℝ × ℝ, (F p).2 = a₂₁ * p.1 + a₂₂ * p.2 + c₂ := by
    by_contra hna
    obtain ⟨x, y, hxy, hnot⟩ :=
      exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff hb (contDiff_snd.comp hF) hna
    exact hnot ((hpres x y (hxy b hb)).right hb)
  obtain ⟨a₁₁, a₁₂, c₁, hF₁⟩ := h1
  obtain ⟨a₂₁, a₂₂, c₂, hF₂⟩ := h2
  exact ⟨a₁₁, a₁₂, c₁, a₂₁, a₂₂, c₂, fun x y ↦ Prod.ext (hF₁ (x, y)) (hF₂ (x, y))⟩

/-- **Full 2D `C²` affine rigidity (non-constant case)**: every non-constant `C²` map
`F : ℝ × ℝ → ℝ × ℝ` preserving base-`b` joint normality (`b ≥ 2`) is of the form
`F (x, y) = (a₁₁ x + a₁₂ y + c₁, a₂₁ x + a₂₂ y + c₂)` with `(aᵢⱼ) ∈ GL_2(ℚ)` and
`c₁, c₂ ∈ normalAddPreservers hb`. -/
theorem exists_rat_affine_of_contDiff_two_preserves_isJointlyNormalIn {b : ℕ} (hb : 2 ≤ b)
    {F : ℝ × ℝ → ℝ × ℝ} (hF : ContDiff ℝ 2 F)
    (hnc : ¬ ∃ p₀ : ℝ × ℝ, ∀ p : ℝ × ℝ, F p = p₀)
    (hpres : ∀ x y : ℝ, IsJointlyNormalIn b x y →
      IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2) :
    ∃ (a₁₁ a₁₂ a₂₁ a₂₂ : ℚ) (c₁ c₂ : ℝ),
      a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0 ∧
      c₁ ∈ normalAddPreservers hb ∧ c₂ ∈ normalAddPreservers hb ∧
      ∀ x y : ℝ, F (x, y) = (a₁₁ * x + a₁₂ * y + c₁, a₂₁ * x + a₂₂ * y + c₂) := by
  obtain ⟨r₁₁, r₁₂, c₁, r₂₁, r₂₂, c₂, hFeq⟩ :=
    exists_affine_of_contDiff_two_preserves_isJointlyNormalIn hb hF hpres
  have hpres' : ∀ x y : ℝ, IsJointlyNormalIn b x y →
      IsJointlyNormalIn b (r₁₁ * x + r₁₂ * y + c₁) (r₂₁ * x + r₂₂ * y + c₂) := fun x y hxy ↦ by
    have := hpres x y hxy
    rwa [hFeq] at this
  -- Helper: a row `(0, 0)` with the other row nonzero is impossible (it hits `(c, c)`).
  have hno_zero_row : ∀ (a₁ a₂ d₁ d₂ : ℝ), (a₁ ≠ 0 ∨ a₂ ≠ 0) →
      (∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (a₁ * x + a₂ * y + d₁) d₂) →
      False := by
    intro a₁ a₂ d₁ d₂ hne hp
    obtain ⟨⟨q₁, q₂, rfl, rfl⟩, hd₁⟩ :=
      rat_and_addPreserver_of_affine_joint hb hne (fun x y hxy ↦ (hp x y hxy).left hb)
    obtain ⟨x₀, y₀, hxy₀⟩ := exists_isJointlyNormalIn hb
    have hd₂ : IsNormalIn b d₂ := (hp x₀ y₀ hxy₀).right hb
    have hz : IsNormalIn b (d₂ + -d₁) := (normalAddPreservers hb).neg_mem hd₁ d₂ hd₂
    obtain ⟨w, hzw⟩ := (ae_isJointlyNormalIn_of_isNormalIn hb hz).exists
    -- Find `(x, y)` jointly normal with `q₁ * x + q₂ * y = d₂ - d₁`
    have hex : ∃ x y : ℝ, IsJointlyNormalIn b x y ∧ (q₁ : ℝ) * x + (q₂ : ℝ) * y = d₂ + -d₁ := by
      rcases hne with hq₁ | hq₂
      · have hq₁' : q₁ ≠ 0 := by exact_mod_cast hq₁
        have hgl := hzw.linear_rat hb (a₁₁ := q₁⁻¹) (a₁₂ := -q₁⁻¹ * q₂) (a₂₁ := 0) (a₂₂ := 1)
          (by simp [hq₁'])
        refine ⟨_, _, hgl, ?_⟩
        have : (q₁ : ℝ) ≠ 0 := by exact_mod_cast hq₁'
        push_cast; field_simp; ring
      · have hq₂' : q₂ ≠ 0 := by exact_mod_cast hq₂
        have hgl := hzw.linear_rat hb (a₁₁ := 0) (a₁₂ := 1) (a₂₁ := q₂⁻¹) (a₂₂ := -q₂⁻¹ * q₁)
          (by simp [hq₂'])
        refine ⟨_, _, hgl, ?_⟩
        have : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq₂'
        push_cast; field_simp; ring
    obtain ⟨x, y, hxy, heq⟩ := hex
    have hself := hp x y hxy
    rw [heq, add_assoc, neg_add_cancel, add_zero] at hself
    exact not_isJointlyNormalIn_self hb hd₂ hself
  -- Neither row can be zero (since `F` is non-constant).
  have hrow1 : r₁₁ ≠ 0 ∨ r₁₂ ≠ 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨rfl, rfl⟩
    have hrow2 : r₂₁ ≠ 0 ∨ r₂₂ ≠ 0 := by
      by_contra h2
      push Not at h2
      rcases h2 with ⟨rfl, rfl⟩
      refine hnc ⟨(c₁, c₂), fun p ↦ ?_⟩
      simpa using hFeq p.1 p.2
    exact hno_zero_row r₂₁ r₂₂ c₂ c₁ hrow2 fun x y hxy ↦ by
      have := (hpres' x y hxy).symm hb
      simpa using this
  have hrow2 : r₂₁ ≠ 0 ∨ r₂₂ ≠ 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨rfl, rfl⟩
    exact hno_zero_row r₁₁ r₁₂ c₁ c₂ hrow1 fun x y hxy ↦ by
      simpa using hpres' x y hxy
  obtain ⟨⟨a₁₁, a₁₂, rfl, rfl⟩, hc₁⟩ :=
    rat_and_addPreserver_of_affine_joint hb hrow1 (fun x y hxy ↦ (hpres' x y hxy).left hb)
  obtain ⟨⟨a₂₁, a₂₂, rfl, rfl⟩, hc₂⟩ :=
    rat_and_addPreserver_of_affine_joint hb hrow2 (fun x y hxy ↦ (hpres' x y hxy).right hb)
  refine ⟨a₁₁, a₁₂, a₂₁, a₂₂, c₁, c₂, ?_, hc₁, hc₂, hFeq⟩
  -- Show `det ≠ 0` using disjointness of `normalAddPreservers hb` and `IsNormalIn b`.
  intro hdet
  have hq_exists : ∃ q : ℚ, q ≠ 0 ∧ a₂₁ = q * a₁₁ ∧ a₂₂ = q * a₁₂ := by
    rcases hrow1 with h11 | h12
    · have ha₁₁ : a₁₁ ≠ 0 := by exact_mod_cast h11
      refine ⟨a₂₁ / a₁₁, ?_, by field_simp, ?_⟩
      · intro h0
        have ha₂₁ : a₂₁ = 0 := (div_eq_zero_iff.1 h0).resolve_right ha₁₁
        rw [ha₂₁, mul_zero, sub_zero] at hdet
        have ha₂₂ : a₂₂ = 0 := (mul_eq_zero.1 hdet).resolve_left ha₁₁
        rcases hrow2 with h | h <;> simp [ha₂₁, ha₂₂] at h
      · rw [div_mul_eq_mul_div, eq_div_iff ha₁₁]; linear_combination hdet
    · have ha₁₂ : a₁₂ ≠ 0 := by exact_mod_cast h12
      refine ⟨a₂₂ / a₁₂, ?_, ?_, by field_simp⟩
      · intro h0
        have ha₂₂ : a₂₂ = 0 := (div_eq_zero_iff.1 h0).resolve_right ha₁₂
        rw [ha₂₂, mul_zero, zero_sub, neg_eq_zero] at hdet
        have ha₂₁ : a₂₁ = 0 := (mul_eq_zero.1 hdet).resolve_left ha₁₂
        rcases hrow2 with h | h <;> simp [ha₂₁, ha₂₂] at h
      · rw [div_mul_eq_mul_div, eq_div_iff ha₁₂]; linear_combination -hdet
  obtain ⟨q, hq, hq1, hq2⟩ := hq_exists
  obtain ⟨x₀, y₀, hxy₀⟩ := exists_isJointlyNormalIn hb
  have hres := hpres' x₀ y₀ hxy₀
  set u : ℝ := a₁₁ * x₀ + a₁₂ * y₀ + c₁
  set t : ℝ := c₂ - (q : ℝ) * c₁
  have hu2 : (a₂₁ : ℝ) * x₀ + (a₂₂ : ℝ) * y₀ + c₂ = (q : ℝ) * u + t := by
    rw [hq1, hq2]; simp only [u, t]; push_cast; ring
  rw [hu2] at hres
  have ht_norm : IsNormalIn b t := isNormalIn_of_isJointlyNormalIn_rat_mul_add hb hres
  have ht_pres : t ∈ normalAddPreservers hb :=
    (normalAddPreservers hb).sub_mem hc₂ (ratCast_mul_mem_normalAddPreservers hb hq hc₁)
  exact not_preserves_isNormalIn_add_of_isNormalIn hb ht_norm ht_pres

/-- **Full dichotomy for `C²` preservers of base-`b` joint normality**: every `C²` map
`F : ℝ × ℝ → ℝ × ℝ` preserving `IsJointlyNormalIn b` (`b ≥ 2`) is either constant with a jointly
normal value, or an invertible rational-linear affine map shifted by `normalAddPreservers hb`. -/
theorem contDiff_two_preserves_isJointlyNormalIn_dichotomy {b : ℕ} (hb : 2 ≤ b)
    {F : ℝ × ℝ → ℝ × ℝ} (hF : ContDiff ℝ 2 F)
    (hpres : ∀ x y : ℝ, IsJointlyNormalIn b x y →
      IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2) :
    (∃ c₁ c₂ : ℝ, IsJointlyNormalIn b c₁ c₂ ∧ ∀ x y : ℝ, F (x, y) = (c₁, c₂)) ∨
    (∃ (a₁₁ a₁₂ a₂₁ a₂₂ : ℚ) (c₁ c₂ : ℝ),
      a₁₁ * a₂₂ - a₁₂ * a₂₁ ≠ 0 ∧
      c₁ ∈ normalAddPreservers hb ∧ c₂ ∈ normalAddPreservers hb ∧
      ∀ x y : ℝ, F (x, y) = (a₁₁ * x + a₁₂ * y + c₁, a₂₁ * x + a₂₂ * y + c₂)) := by
  by_cases hc : ∃ p₀ : ℝ × ℝ, ∀ p : ℝ × ℝ, F p = p₀
  · left
    obtain ⟨⟨c₁, c₂⟩, hp₀⟩ := hc
    obtain ⟨x₀, y₀, hxy₀⟩ := exists_isJointlyNormalIn hb
    have hnorm := hpres x₀ y₀ hxy₀
    rw [hp₀ (x₀, y₀)] at hnorm
    exact ⟨c₁, c₂, hnorm, fun x y ↦ hp₀ (x, y)⟩
  · right
    exact exists_rat_affine_of_contDiff_two_preserves_isJointlyNormalIn hb hF hc hpres

/-- Sharpness of the non-constant hypothesis: constant `C²` maps with a jointly normal value
preserve `IsJointlyNormalIn b` yet have zero determinant and shift outside
`normalAddPreservers hb`. -/
theorem exists_const_contDiff_two_preserves_isJointlyNormalIn {b : ℕ} (hb : 2 ≤ b) :
    ∃ F : ℝ × ℝ → ℝ × ℝ, ContDiff ℝ 2 F ∧ (∃ p₀, ∀ p, F p = p₀) ∧
      ∀ x y : ℝ, IsJointlyNormalIn b x y →
        IsJointlyNormalIn b (F (x, y)).1 (F (x, y)).2 := by
  obtain ⟨c₁, c₂, hc⟩ := exists_isJointlyNormalIn hb
  exact ⟨fun _ ↦ (c₁, c₂), contDiff_const, ⟨(c₁, c₂), fun _ ↦ rfl⟩, fun _ _ _ ↦ hc⟩

/-! ### Concrete 2D non-preservation corollaries -/

/-- Multiplication `x * y` does not preserve normality from jointly absolutely normal pairs. -/
theorem exists_isJointlyAbsolutelyNormal_not_isNormalIn_mul {b : ℕ} (hb : 2 ≤ b) :
    ∃ x y : ℝ, IsJointlyAbsolutelyNormal x y ∧ ¬ IsNormalIn b (x * y) := by
  refine exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff hb (F₁ := fun p ↦ p.1 * p.2)
    (contDiff_fst.mul contDiff_snd) ?_
  rintro ⟨a₁, a₂, c, h⟩
  have h00 := h (0, 0)
  have h10 := h (1, 0)
  have h01 := h (0, 1)
  have h11 := h (1, 1)
  simp only at h00 h10 h01 h11
  linarith

/-- `(x, y) ↦ (x * y, y)` does not preserve joint normality in base `b ≥ 2`. -/
theorem not_preserves_isJointlyNormalIn_mul_snd {b : ℕ} (hb : 2 ≤ b) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x * y) y := by
  intro hpres
  obtain ⟨x, y, hxy, hnot⟩ := exists_isJointlyAbsolutelyNormal_not_isNormalIn_mul hb
  exact hnot ((hpres x y (hxy b hb)).left hb)

/-- `(x, y) ↦ (x + y, x * y)` does not preserve joint normality in base `b ≥ 2`. -/
theorem not_preserves_isJointlyNormalIn_add_mul {b : ℕ} (hb : 2 ≤ b) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x + y) (x * y) := by
  intro hpres
  obtain ⟨x, y, hxy, hnot⟩ := exists_isJointlyAbsolutelyNormal_not_isNormalIn_mul hb
  exact hnot ((hpres x y (hxy b hb)).right hb)

/-- `(x, y) ↦ (x ^ 2, y ^ 2)` does not preserve joint normality in base `b ≥ 2`. -/
theorem not_preserves_isJointlyNormalIn_sq_sq {b : ℕ} (hb : 2 ≤ b) :
    ¬ ∀ x y : ℝ, IsJointlyNormalIn b x y → IsJointlyNormalIn b (x ^ 2) (y ^ 2) := by
  intro hpres
  obtain ⟨x, y, hxy, hnot⟩ := exists_isJointlyAbsolutelyNormal_not_isNormalIn_of_contDiff hb
    (F₁ := fun p ↦ p.1 ^ 2) (contDiff_fst.pow 2) (by
      rintro ⟨a₁, a₂, c, h⟩
      have h0 := h (0, 0)
      have h1 := h (1, 0)
      have h2 := h (2, 0)
      simp only at h0 h1 h2
      linarith)
  exact hnot ((hpres x y (hxy b hb)).left hb)

end Real
