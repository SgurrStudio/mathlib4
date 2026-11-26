/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.NumberTheory.Normal.Borel
public import Mathlib.NumberTheory.Normal.Rational

/-!
# Preservation and non-preservation of normality under maps

We study which translations, dilations, and smooth maps preserve normality in a fixed base `b ≥ 2`
or absolute normality, both from an algebraic and from a metric (Lebesgue measure) perspective.

## Main statements

* `Real.not_preserves_isNormalIn_add_of_isNormalIn`: no normal number `α` preserves normality under
  translation `x ↦ x + α` (witnessed by `x = -α`).
* `Real.not_preserves_isNormalIn_mul_of_isNormalIn_inv`: if `α ≠ 0` and `α⁻¹` is normal, then
  `x ↦ α * x` does not preserve normality (witnessed by `x = α⁻¹`).
* `Real.volume_setOf_preserves_isNormalIn_add_eq_zero`,
  `Real.volume_setOf_preserves_isAbsolutelyNormal_add_eq_zero`: the set of additive normality
  preservers has Lebesgue measure zero.
* `Real.ae_isAbsolutelyNormal_inv`, `Real.ae_isAbsolutelyNormal_pow`,
  `Real.ae_isAbsolutelyNormal_exp`, `Real.ae_isAbsolutelyNormal_aeval_rat_poly`: for
  Lebesgue-almost every `x : ℝ`, `x⁻¹`, `x ^ k` (`k ≥ 1`), `Real.exp x`, and `Polynomial.aeval x p`
  (simultaneously for every non-constant `p : Polynomial ℚ`) are absolutely normal.
* `Real.volume_setOf_preserves_isNormalIn_mul_eq_zero`,
  `Real.volume_setOf_preserves_isAbsolutelyNormal_mul_eq_zero`: the set of multiplicative normality
  preservers has Lebesgue measure zero.
* `Real.normalAddPreservers`, `Real.absolutelyNormalAddPreservers`: additive normality preservers
  form an `AddSubgroup ℝ` containing `ℚ`.
* `Real.normalMulPreservers`, `Real.absolutelyNormalMulPreservers`,
  `Real.normalMulEquivPreservers`, `Real.absolutelyNormalMulEquivPreservers`: multiplicative
  normality preservers form a `Submonoid ℝ` containing `ℚ \ {0}`, and two-sided multiplicative
  preservers form a `Subgroup ℝˣ`.
-/

@[expose] public section

open Filter MeasureTheory Polynomial Set Topology
open scoped ENNReal

namespace Real

variable {b : ℕ} {x α β : ℝ}

/-! ### Rational invariance helpers -/

private lemma isNormalIn_neg_iff (hb : 2 ≤ b) : IsNormalIn b (-x) ↔ IsNormalIn b x :=
  ⟨fun h ↦ by simpa using h.neg hb, fun h ↦ h.neg hb⟩

private lemma isNormalIn_mul_ratCast_iff (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0) :
    IsNormalIn b ((q : ℝ) * x) ↔ IsNormalIn b x := by
  simpa using isNormalIn_mul_add_ratCast_iff hb hq 0 (x := x)

private lemma isNormalIn_add_ratCast_iff (hb : 2 ≤ b) (r : ℚ) :
    IsNormalIn b (x + (r : ℝ)) ↔ IsNormalIn b x := by
  simpa using isNormalIn_mul_add_ratCast_iff hb (q := 1) one_ne_zero r (x := x)

private lemma isAbsolutelyNormal_neg_iff : IsAbsolutelyNormal (-x) ↔ IsAbsolutelyNormal x :=
  forall₂_congr fun _ hb ↦ isNormalIn_neg_iff hb

private lemma isAbsolutelyNormal_mul_ratCast_iff {q : ℚ} (hq : q ≠ 0) :
    IsAbsolutelyNormal ((q : ℝ) * x) ↔ IsAbsolutelyNormal x :=
  forall₂_congr fun _ hb ↦ isNormalIn_mul_ratCast_iff hb hq

private lemma isAbsolutelyNormal_add_ratCast_iff (r : ℚ) :
    IsAbsolutelyNormal (x + (r : ℝ)) ↔ IsAbsolutelyNormal x :=
  forall₂_congr fun _ hb ↦ isNormalIn_add_ratCast_iff hb r

private lemma isAbsolutelyNormal_mul_add_ratCast_iff {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    IsAbsolutelyNormal ((q : ℝ) * x + (r : ℝ)) ↔ IsAbsolutelyNormal x :=
  forall₂_congr fun _ hb ↦ isNormalIn_mul_add_ratCast_iff hb hq r

/-! ### Elementary non-preservation witnesses -/

/-- If `α` is normal in base `b ≥ 2`, then translation by `α` does not preserve base-`b`
normality: `-α` is normal in base `b`, whereas `-α + α = 0` is rational. -/
theorem not_preserves_isNormalIn_add_of_isNormalIn (hb : 2 ≤ b) (hα : IsNormalIn b α) :
    ¬ ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α) := by
  intro h
  have h0 : IsNormalIn b (-α + α) := h (-α) (hα.neg hb)
  rw [neg_add_cancel] at h0
  exact (h0.irrational hb).ne_zero rfl

/-- If `α` is absolutely normal, then translation by `α` does not preserve absolute normality. -/
theorem not_preserves_isAbsolutelyNormal_add_of_isAbsolutelyNormal (hα : IsAbsolutelyNormal α) :
    ¬ ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α) := by
  intro h
  have h0 : IsAbsolutelyNormal (-α + α) := h (-α) (isAbsolutelyNormal_neg_iff.2 hα)
  rw [neg_add_cancel] at h0
  exact h0.irrational.ne_zero rfl

/-- If `α ≠ 0` and `α⁻¹` is normal in base `b ≥ 2`, then multiplication by `α` does not preserve
base-`b` normality: `α * α⁻¹ = 1` is rational. -/
theorem not_preserves_isNormalIn_mul_of_isNormalIn_inv (hb : 2 ≤ b) (hα0 : α ≠ 0)
    (hα : IsNormalIn b α⁻¹) : ¬ ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x) := by
  intro h
  have h1 : IsNormalIn b (α * α⁻¹) := h α⁻¹ hα
  rw [mul_inv_cancel₀ hα0] at h1
  exact (h1.irrational hb).ne_one rfl

/-- If `α ≠ 0` and `α⁻¹` is absolutely normal, then multiplication by `α` does not preserve
absolute normality. -/
theorem not_preserves_isAbsolutelyNormal_mul_of_isAbsolutelyNormal_inv (hα0 : α ≠ 0)
    (hα : IsAbsolutelyNormal α⁻¹) :
    ¬ ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x) := by
  intro h
  have h1 : IsAbsolutelyNormal (α * α⁻¹) := h α⁻¹ hα
  rw [mul_inv_cancel₀ hα0] at h1
  exact h1.irrational.ne_one rfl

/-- Any multiplicative preserver of base-`b` normality (`b ≥ 2`) is nonzero. -/
theorem ne_zero_of_preserves_isNormalIn_mul (hb : 2 ≤ b)
    (h : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)) : α ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_isAbsolutelyNormal
  have h0 : IsNormalIn b (0 * x) := h x (hx b hb)
  rw [zero_mul] at h0
  exact (h0.irrational hb).ne_zero rfl

/-- Any multiplicative preserver of absolute normality is nonzero. -/
theorem ne_zero_of_preserves_isAbsolutelyNormal_mul
    (h : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)) : α ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_isAbsolutelyNormal
  have h0 : IsAbsolutelyNormal (0 * x) := h x hx
  rw [zero_mul] at h0
  exact h0.irrational.ne_zero rfl

/-! ### Measure-zero sets of additive preservers -/

/-- The set of real numbers `α` whose translation `x ↦ x + α` preserves base-`b` normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isNormalIn_add_eq_zero (hb : 2 ≤ b) :
    volume {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)} = 0 := by
  refine measure_mono_null (t := {α : ℝ | ¬ IsNormalIn b α}) ?_
    (ae_iff.1 (ae_isNormalIn (by omega)))
  intro α hα hnorm
  exact not_preserves_isNormalIn_add_of_isNormalIn hb hnorm hα

/-- The set of real numbers `α` whose translation `x ↦ x + α` preserves absolute normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isAbsolutelyNormal_add_eq_zero :
    volume {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)} = 0 := by
  refine measure_mono_null (t := {α : ℝ | ¬ IsAbsolutelyNormal α}) ?_
    volume_setOf_not_isAbsolutelyNormal
  intro α hα hnorm
  exact not_preserves_isAbsolutelyNormal_add_of_isAbsolutelyNormal hnorm hα

/-! ### Null-set pullbacks under locally `C¹` maps with non-vanishing derivative -/

private theorem volume_inter_preimage_eq_zero_of_injOn_hasDerivAt {I t : Set ℝ} {f f' : ℝ → ℝ}
    (hI : IsOpen I) (hf : ∀ x ∈ I, HasDerivAt f (f' x) x) (hf'c : ContinuousOn f' I)
    (hf'_ne : ∀ x ∈ I, f' x ≠ 0) (hinj : InjOn f I) (ht : volume t = 0) :
    volume (I ∩ f ⁻¹' t) = 0 := by
  obtain ⟨t', htt', ht'm, ht'0⟩ := exists_measurable_superset_of_null ht
  refine measure_mono_null (inter_subset_inter_right I (preimage_mono htt')) ?_
  set u := I ∩ f ⁻¹' t'
  have hfc : ContinuousOn f I := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hu_meas : MeasurableSet u := by
    have hsub : u = (Subtype.val : I → ℝ) '' ((f ∘ Subtype.val) ⁻¹' t') := by
      ext x
      simp [u, and_comm]
    rw [hsub]
    exact hI.measurableSet.subtype_image (hfc.domRestrict.measurable ht'm)
  have hcov : ∫⁻ _ in f '' u, (1 : ℝ≥0∞) = ∫⁻ x in u, ENNReal.ofReal |f' x| * 1 :=
    lintegral_image_eq_lintegral_abs_deriv_mul hu_meas
      (fun x hx ↦ (hf x hx.1).hasDerivWithinAt) (hinj.mono inter_subset_left) (fun _ ↦ 1)
  have hzero : ∫⁻ x in u, ENNReal.ofReal |f' x| = 0 := by
    have hfu : volume (f '' u) = 0 :=
      measure_mono_null (by rintro y ⟨x, ⟨_, hxt'⟩, rfl⟩; exact hxt') ht'0
    simpa [hfu] using hcov.symm
  have hmeas : AEMeasurable (fun x ↦ ENNReal.ofReal |f' x|) (volume.restrict u) :=
    ((ENNReal.continuous_ofReal.comp continuous_abs).comp_continuousOn
      (hf'c.mono inter_subset_left)).aemeasurable hu_meas
  have hae : (fun x ↦ ENNReal.ofReal |f' x|) =ᵐ[volume.restrict u] 0 :=
    (lintegral_eq_zero_iff' hmeas).1 hzero
  have hfalse : ∀ᵐ x ∂(volume.restrict u), False := by
    filter_upwards [hae, ae_restrict_mem hu_meas] with x hx0 hxu
    have hpos : 0 < ENNReal.ofReal |f' x| := ENNReal.ofReal_pos.2 (abs_pos.2 (hf'_ne x hxu.1))
    exact hpos.ne' hx0
  simpa [ae_iff, Measure.restrict_apply_univ] using hfalse

/-- If `f` is `C¹` with non-vanishing derivative on an open set `U ⊆ ℝ` of full Lebesgue measure,
then preimages of Lebesgue null sets under `f` are null. -/
theorem volume_preimage_eq_zero_of_hasDerivAt_ne_zero {U t : Set ℝ} {f f' : ℝ → ℝ}
    (hU : IsOpen U) (hUc : volume Uᶜ = 0) (hf : ∀ x ∈ U, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' U) (hf'_ne : ∀ x ∈ U, f' x ≠ 0) (ht : volume t = 0) :
    volume (f ⁻¹' t) = 0 := by
  let S : Set (ℚ × ℚ) := {p | Ioo (p.1 : ℝ) p.2 ⊆ U ∧
    ((∀ y ∈ Ioo (p.1 : ℝ) p.2, 0 < f' y) ∨ (∀ y ∈ Ioo (p.1 : ℝ) p.2, f' y < 0))}
  have hcover : U ⊆ ⋃ p ∈ S, Ioo (p.1 : ℝ) p.2 := by
    intro x hx
    have hcont : ContinuousAt f' x := hf'c.continuousAt (hU.mem_nhds hx)
    rcases lt_or_gt_of_ne (hf'_ne x hx) with hneg | hpos
    · have hmem : U ∩ f' ⁻¹' Iio 0 ∈ 𝓝 x :=
        Filter.inter_mem (hU.mem_nhds hx) (hcont.preimage_mem_nhds (Iio_mem_nhds hneg))
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (sub_lt_self x hε)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right x hε)
      have hsub : Ioo (p : ℝ) q ⊆ U ∩ f' ⁻¹' Iio 0 := by
        intro y hy
        exact hball (by rw [Real.ball_eq_Ioo]; exact ⟨hp1.trans hy.1, hy.2.trans hq2⟩)
      exact mem_biUnion (show (p, q) ∈ S from ⟨hsub.trans inter_subset_left,
        Or.inr fun y hy ↦ (hsub hy).2⟩) ⟨hp2, hq1⟩
    · have hmem : U ∩ f' ⁻¹' Ioi 0 ∈ 𝓝 x :=
        Filter.inter_mem (hU.mem_nhds hx) (hcont.preimage_mem_nhds (Ioi_mem_nhds hpos))
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (sub_lt_self x hε)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right x hε)
      have hsub : Ioo (p : ℝ) q ⊆ U ∩ f' ⁻¹' Ioi 0 := by
        intro y hy
        exact hball (by rw [Real.ball_eq_Ioo]; exact ⟨hp1.trans hy.1, hy.2.trans hq2⟩)
      exact mem_biUnion (show (p, q) ∈ S from ⟨hsub.trans inter_subset_left,
        Or.inl fun y hy ↦ (hsub hy).2⟩) ⟨hp2, hq1⟩
  have hsub_tot : f ⁻¹' t ⊆ Uᶜ ∪ ⋃ p ∈ S, (Ioo (p.1 : ℝ) p.2 ∩ f ⁻¹' t) := by
    intro x hx
    by_cases hxU : x ∈ U
    · obtain ⟨p, hpS, hxp⟩ := mem_iUnion₂.1 (hcover hxU)
      exact Or.inr (mem_biUnion hpS ⟨hxp, hx⟩)
    · exact Or.inl hxU
  refine measure_mono_null hsub_tot (measure_union_null hUc ?_)
  refine (measure_biUnion_null_iff (Set.to_countable S)).2 fun p hp ↦ ?_
  have hfc : ContinuousOn f (Ioo (p.1 : ℝ) p.2) :=
    fun y hy ↦ (hf y (hp.1 hy)).continuousAt.continuousWithinAt
  have hinj : InjOn f (Ioo (p.1 : ℝ) p.2) := by
    rcases hp.2 with hpos | hneg
    · exact (strictMonoOn_of_deriv_pos (convex_Ioo _ _) hfc fun y hy ↦ by
        rw [interior_Ioo] at hy
        rw [(hf y (hp.1 hy)).deriv]
        exact hpos y hy).injOn
    · exact (strictAntiOn_of_deriv_neg (convex_Ioo _ _) hfc fun y hy ↦ by
        rw [interior_Ioo] at hy
        rw [(hf y (hp.1 hy)).deriv]
        exact hneg y hy).injOn
  exact volume_inter_preimage_eq_zero_of_injOn_hasDerivAt isOpen_Ioo
    (fun y hy ↦ hf y (hp.1 hy)) (hf'c.mono hp.1) (fun y hy ↦ hf'_ne y (hp.1 hy)) hinj ht

/-- If `P` holds Lebesgue-almost everywhere and `f` is `C¹` with non-vanishing derivative on an
open set of full measure, then `P (f x)` holds for Lebesgue-almost every `x`. -/
theorem ae_comp_of_hasDerivAt_ne_zero {U : Set ℝ} {f f' : ℝ → ℝ} {P : ℝ → Prop}
    (hU : IsOpen U) (hUc : volume Uᶜ = 0) (hf : ∀ x ∈ U, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' U) (hf'_ne : ∀ x ∈ U, f' x ≠ 0) (hP : ∀ᵐ y : ℝ, P y) :
    ∀ᵐ x : ℝ, P (f x) := by
  rw [ae_iff] at hP ⊢
  exact volume_preimage_eq_zero_of_hasDerivAt_ne_zero hU hUc hf hf'c hf'_ne hP

/-! ### Almost-everywhere absolute normality of smooth images -/

/-- For Lebesgue-almost every `x : ℝ`, `x⁻¹` is absolutely normal. -/
theorem ae_isAbsolutelyNormal_inv : ∀ᵐ x : ℝ, IsAbsolutelyNormal x⁻¹ := by
  refine ae_comp_of_hasDerivAt_ne_zero (U := ({0} : Set ℝ)ᶜ) (f' := fun x ↦ -(x ^ 2)⁻¹)
    isClosed_singleton.isOpen_compl (by simp)
    (fun x hx ↦ hasDerivAt_inv hx) ?_ ?_ ae_isAbsolutelyNormal
  · exact (continuousOn_id.pow 2).inv₀ (fun x hx ↦ pow_ne_zero 2 hx) |>.neg
  · intro x hx
    exact neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hx))

/-- For Lebesgue-almost every `x : ℝ` and any `k ≥ 1`, `x ^ k` is absolutely normal. -/
theorem ae_isAbsolutelyNormal_pow {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x : ℝ, IsAbsolutelyNormal (x ^ k) := by
  refine ae_comp_of_hasDerivAt_ne_zero (U := ({0} : Set ℝ)ᶜ)
    (f' := fun x ↦ (k : ℝ) * x ^ (k - 1))
    isClosed_singleton.isOpen_compl (by simp)
    (fun x _ ↦ hasDerivAt_pow k x) ?_ ?_ ae_isAbsolutelyNormal
  · exact (continuous_const.mul (continuous_pow (k - 1))).continuousOn
  · intro x hx
    exact mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (pow_ne_zero _ hx)

/-- For Lebesgue-almost every `x : ℝ`, `Real.exp x` is absolutely normal. -/
theorem ae_isAbsolutelyNormal_exp : ∀ᵐ x : ℝ, IsAbsolutelyNormal (Real.exp x) :=
  ae_comp_of_hasDerivAt_ne_zero (U := univ) (f' := Real.exp) isOpen_univ (by simp)
    (fun x _ ↦ Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
    (fun x _ ↦ Real.exp_ne_zero x) ae_isAbsolutelyNormal

/-- For a fixed non-constant rational polynomial `p`, `Polynomial.aeval x p` is absolutely normal
for Lebesgue-almost every `x : ℝ`. -/
theorem ae_isAbsolutelyNormal_aeval_rat_poly_single (p : ℚ[X]) (hp : 1 ≤ p.natDegree) :
    ∀ᵐ x : ℝ, IsAbsolutelyNormal (Polynomial.aeval x p) := by
  set q : ℝ[X] := p.map (algebraMap ℚ ℝ)
  have hqdeg : q.natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective (algebraMap ℚ ℝ)) p
  have hqd_ne : q.derivative ≠ 0 := by
    intro h
    have hdeg := Polynomial.derivative_eq_zero.1 h
    omega
  set Z : Set ℝ := {x : ℝ | q.derivative.eval x = 0}
  have hZ_fin : Z.Finite := by
    refine (q.derivative.roots.toFinset.finite_toSet).subset fun x hx ↦ ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hqd_ne]
    exact hx
  have hfun : ∀ x : ℝ, Polynomial.aeval x p = q.eval x := fun x ↦ by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  simp_rw [hfun]
  refine ae_comp_of_hasDerivAt_ne_zero (U := Zᶜ) (f' := fun x ↦ q.derivative.eval x)
    hZ_fin.isClosed.isOpen_compl ?_ (fun x _ ↦ q.hasDerivAt x)
    (fun x _ ↦ (q.derivative.hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x hx ↦ hx) ae_isAbsolutelyNormal
  rw [compl_compl]
  exact hZ_fin.countable.measure_zero volume

/-- For Lebesgue-almost every `x : ℝ`, `Polynomial.aeval x p` is absolutely normal simultaneously
for every non-constant rational polynomial `p : Polynomial ℚ`. -/
theorem ae_isAbsolutelyNormal_aeval_rat_poly :
    ∀ᵐ x : ℝ, ∀ p : ℚ[X], 1 ≤ p.natDegree → IsAbsolutelyNormal (Polynomial.aeval x p) := by
  have : Countable ℚ[X] :=
    Function.Injective.countable (f := AddMonoidAlgebra.coeff) fun p₁ p₂ h ↦ by
      cases p₁; cases p₂; congr
  rw [ae_all_iff]
  intro p
  by_cases hp : 1 ≤ p.natDegree
  · exact (ae_isAbsolutelyNormal_aeval_rat_poly_single p hp).mono fun x hx _ ↦ hx
  · exact Eventually.of_forall fun _ h ↦ absurd h hp

/-! ### Measure-zero sets of multiplicative preservers -/

/-- The set of real numbers `α` whose multiplication `x ↦ α * x` preserves base-`b` normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isNormalIn_mul_eq_zero (hb : 2 ≤ b) :
    volume {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)} = 0 := by
  have hae : ∀ᵐ α : ℝ, IsNormalIn b α⁻¹ :=
    ae_isAbsolutelyNormal_inv.mono fun α h ↦ h b hb
  refine measure_mono_null (t := ({0} : Set ℝ) ∪ {α : ℝ | ¬ IsNormalIn b α⁻¹}) ?_
    (measure_union_null (by simp) (ae_iff.1 hae))
  intro α hα
  by_cases h0 : α = 0
  · exact Or.inl h0
  · exact Or.inr fun hnorm ↦ not_preserves_isNormalIn_mul_of_isNormalIn_inv hb h0 hnorm hα

/-- The set of real numbers `α` whose multiplication `x ↦ α * x` preserves absolute normality
has Lebesgue measure zero. -/
theorem volume_setOf_preserves_isAbsolutelyNormal_mul_eq_zero :
    volume {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)} = 0 := by
  refine measure_mono_null (t := ({0} : Set ℝ) ∪ {α : ℝ | ¬ IsAbsolutelyNormal α⁻¹}) ?_
    (measure_union_null (by simp) (ae_iff.1 ae_isAbsolutelyNormal_inv))
  intro α hα
  by_cases h0 : α = 0
  · exact Or.inl h0
  · exact Or.inr fun hnorm ↦
      not_preserves_isAbsolutelyNormal_mul_of_isAbsolutelyNormal_inv h0 hnorm hα

/-! ### Algebraic structure of additive and multiplicative preservers -/

theorem preserves_isNormalIn_add_zero :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + 0) := by
  simp

theorem preserves_isNormalIn_add_add
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α))
    (hβ : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + β)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + (α + β)) := fun x hx ↦ by
  rw [← add_assoc]
  exact hβ (x + α) (hα x hx)

theorem preserves_isNormalIn_add_neg (hb : 2 ≤ b)
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + -α) := fun x hx ↦ by
  have h := (hα (-x) (hx.neg hb)).neg hb
  convert h using 1
  ring

theorem preserves_isNormalIn_add_sub (hb : 2 ≤ b)
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α))
    (hβ : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + β)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + (α - β)) := by
  rw [sub_eq_add_neg]
  exact preserves_isNormalIn_add_add hα (preserves_isNormalIn_add_neg hb hβ)

theorem preserves_isNormalIn_add_ratCast (hb : 2 ≤ b) (r : ℚ) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + (r : ℝ)) :=
  fun _ hx ↦ hx.add_ratCast hb r

/-- Forward preservation of base-`b` normality under translation is equivalent to two-sided
preservation, because `-x` is normal iff `x` is normal. -/
theorem preserves_isNormalIn_add_iff_forall_iff (hb : 2 ≤ b) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)) ↔
      (∀ x : ℝ, IsNormalIn b x ↔ IsNormalIn b (x + α)) := by
  refine ⟨fun h x ↦ ⟨h x, fun hx ↦ ?_⟩, fun h x ↦ (h x).1⟩
  have hneg := preserves_isNormalIn_add_neg hb h (x + α) hx
  rwa [add_assoc, add_neg_cancel, add_zero] at hneg

/-- The additive subgroup of `ℝ` consisting of all translations preserving base-`b` normality
(`b ≥ 2`). -/
def normalAddPreservers (hb : 2 ≤ b) : AddSubgroup ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α)}
  zero_mem' := preserves_isNormalIn_add_zero
  add_mem' := preserves_isNormalIn_add_add
  neg_mem' := preserves_isNormalIn_add_neg hb

theorem ratCast_mem_normalAddPreservers (hb : 2 ≤ b) (r : ℚ) :
    (r : ℝ) ∈ normalAddPreservers hb :=
  preserves_isNormalIn_add_ratCast hb r

theorem preserves_isAbsolutelyNormal_add_zero :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + 0) := by
  simp

theorem preserves_isAbsolutelyNormal_add_add
    (hα : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α))
    (hβ : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + β)) :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + (α + β)) := fun x hx ↦ by
  rw [← add_assoc]
  exact hβ (x + α) (hα x hx)

theorem preserves_isAbsolutelyNormal_add_neg
    (hα : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)) :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + -α) := fun x hx ↦ by
  have h := isAbsolutelyNormal_neg_iff.2 (hα (-x) (isAbsolutelyNormal_neg_iff.2 hx))
  convert h using 1
  ring

theorem preserves_isAbsolutelyNormal_add_iff_forall_iff :
    (∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)) ↔
      (∀ x : ℝ, IsAbsolutelyNormal x ↔ IsAbsolutelyNormal (x + α)) := by
  refine ⟨fun h x ↦ ⟨h x, fun hx ↦ ?_⟩, fun h x ↦ (h x).1⟩
  have hneg := preserves_isAbsolutelyNormal_add_neg h (x + α) hx
  rwa [add_assoc, add_neg_cancel, add_zero] at hneg

/-- The additive subgroup of `ℝ` consisting of all translations preserving absolute normality. -/
def absolutelyNormalAddPreservers : AddSubgroup ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (x + α)}
  zero_mem' := preserves_isAbsolutelyNormal_add_zero
  add_mem' := preserves_isAbsolutelyNormal_add_add
  neg_mem' := preserves_isAbsolutelyNormal_add_neg

theorem ratCast_mem_absolutelyNormalAddPreservers (r : ℚ) :
    (r : ℝ) ∈ absolutelyNormalAddPreservers :=
  fun _ hx ↦ (isAbsolutelyNormal_add_ratCast_iff r).2 hx

theorem preserves_isNormalIn_mul_one :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (1 * x) := by
  simp

theorem preserves_isNormalIn_mul_mul
    (hα : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x))
    (hβ : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (β * x)) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b ((α * β) * x) := fun x hx ↦ by
  rw [mul_assoc]
  exact hα (β * x) (hβ x hx)

theorem preserves_isNormalIn_mul_ratCast (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0) :
    ∀ x : ℝ, IsNormalIn b x → IsNormalIn b ((q : ℝ) * x) :=
  fun _ hx ↦ (isNormalIn_mul_ratCast_iff hb hq).2 hx

/-- The multiplicative submonoid of `ℝ` consisting of all dilations preserving base-`b`
normality. -/
def normalMulPreservers (b : ℕ) : Submonoid ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)}
  one_mem' := preserves_isNormalIn_mul_one
  mul_mem' := preserves_isNormalIn_mul_mul

theorem ratCast_mem_normalMulPreservers (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0) :
    (q : ℝ) ∈ normalMulPreservers b :=
  preserves_isNormalIn_mul_ratCast hb hq

/-- The multiplicative subgroup of `ℝˣ` consisting of all two-sided multiplicative preservers of
base-`b` normality. -/
def normalMulEquivPreservers (b : ℕ) : Subgroup ℝˣ where
  carrier := {α : ℝˣ | ∀ x : ℝ, IsNormalIn b x ↔ IsNormalIn b ((α : ℝ) * x)}
  one_mem' := fun x ↦ by simp
  mul_mem' := fun hα hβ x ↦ by
    rw [Units.val_mul, mul_assoc]
    exact (hβ x).trans (hα _)
  inv_mem' := fun {u} hu x ↦ by
    simpa [Units.val_inv_eq_inv_val] using (hu ((u : ℝ)⁻¹ * x)).symm

theorem preserves_isAbsolutelyNormal_mul_one :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (1 * x) := by
  simp

theorem preserves_isAbsolutelyNormal_mul_mul
    (hα : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x))
    (hβ : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (β * x)) :
    ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal ((α * β) * x) := fun x hx ↦ by
  rw [mul_assoc]
  exact hα (β * x) (hβ x hx)

/-- The multiplicative submonoid of `ℝ` consisting of all dilations preserving absolute
normality. -/
def absolutelyNormalMulPreservers : Submonoid ℝ where
  carrier := {α : ℝ | ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (α * x)}
  one_mem' := preserves_isAbsolutelyNormal_mul_one
  mul_mem' := preserves_isAbsolutelyNormal_mul_mul

theorem ratCast_mem_absolutelyNormalMulPreservers {q : ℚ} (hq : q ≠ 0) :
    (q : ℝ) ∈ absolutelyNormalMulPreservers :=
  fun _ hx ↦ (isAbsolutelyNormal_mul_ratCast_iff hq).2 hx

/-- The multiplicative subgroup of `ℝˣ` consisting of all two-sided multiplicative preservers of
absolute normality. -/
def absolutelyNormalMulEquivPreservers : Subgroup ℝˣ where
  carrier := {α : ℝˣ | ∀ x : ℝ, IsAbsolutelyNormal x ↔ IsAbsolutelyNormal ((α : ℝ) * x)}
  one_mem' := fun x ↦ by simp
  mul_mem' := fun hα hβ x ↦ by
    rw [Units.val_mul, mul_assoc]
    exact (hβ x).trans (hα _)
  inv_mem' := fun {u} hu x ↦ by
    simpa [Units.val_inv_eq_inv_val] using (hu ((u : ℝ)⁻¹ * x)).symm

end Real
