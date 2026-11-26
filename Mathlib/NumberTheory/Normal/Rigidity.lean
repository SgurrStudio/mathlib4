/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.NonPreservation
public import Mathlib.NumberTheory.Normal.Rational
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# `C²` affine rigidity of normality preservation

A `C²` map `f : ℝ → ℝ` that sends every base-`b` normal number to a base-`b` normal number is
affine (Manai, arXiv:2609.24665). We prove the contrapositive in a strong form: if `f` is `C²`
and not affine, then for every base `b ≥ 2` there is an absolutely normal `x` with `f x` not
normal in base `b`.

The proof: `f''(p) ≠ 0` and `f'(p) ≠ 0` for some `p`, so on a small interval around `p` the map
`f` is a `C²` diffeomorphism whose inverse `g` has `g'' = -f''(g) / f'(g)³` bounded away from `0`.
Composing `g` with a rational affine map onto the window, the Kaufman-type decay of
`NormalNumbers.QuarterCantorDecay` (base `2`) or `NormalNumbers.BaseCantorDecay` (base `b ≥ 3`)
makes `x = g(q + s Y)` absolutely normal for almost every Cantor point `Y`, while
`f x = q + s Y` is not normal in base `b`, by Wall's theorem.

## Main statements

* `Real.exists_isAbsolutelyNormal_not_isNormalIn_of_contDiff`
* `Real.exists_affine_of_contDiff_two_preserves_isNormalIn`
* `Real.exists_affine_of_contDiff_two_preserves_isAbsolutelyNormal`
-/

@[expose] public noncomputable section

open Filter Topology Set

namespace NormalNumbers.Rigidity

/-! ### A point where `f'` and `f''` do not vanish -/

section Analytic

variable {f : ℝ → ℝ}

theorem hasDerivAt_deriv (hf : ContDiff ℝ 2 f) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (hf.differentiable (by norm_num) x).hasDerivAt

theorem contDiff_deriv (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) :=
  (contDiff_succ_iff_deriv (n := 1).1 (hf.of_le le_rfl)).2.2

theorem hasDerivAt_deriv_deriv (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x :=
  ((contDiff_deriv hf).differentiable (by norm_num) x).hasDerivAt

theorem continuous_deriv_deriv (hf : ContDiff ℝ 2 f) : Continuous (deriv (deriv f)) :=
  (contDiff_deriv hf).continuous_deriv le_rfl

/-- A `C²` map with `f'' ≡ 0` is affine. -/
theorem exists_affine_of_deriv_deriv_eq_zero (hf : ContDiff ℝ 2 f)
    (h : ∀ x, deriv (deriv f) x = 0) : ∃ a c : ℝ, ∀ x, f x = a * x + c := by
  have h1 : ∀ x, deriv f x = deriv f 0 := fun x =>
    is_const_of_deriv_eq_zero ((contDiff_deriv hf).differentiable (by norm_num)) h x 0
  set a := deriv f 0
  have hd : Differentiable ℝ fun x => f x - a * x :=
    (hf.differentiable (by norm_num)).sub (differentiable_id.const_mul a)
  have h2 : ∀ x, deriv (fun x => f x - a * x) x = 0 := fun x => by
    have hh : HasDerivAt (fun x => f x - a * x) (deriv f x - a * 1) x :=
      (hasDerivAt_deriv hf x).sub ((hasDerivAt_id' x).const_mul a)
    rw [hh.deriv, h1]; simp [a]
  refine ⟨a, f 0 - a * 0, fun x => ?_⟩
  have := is_const_of_deriv_eq_zero hd h2 x 0
  linarith

/-- A non-affine `C²` map has a point where neither `f'` nor `f''` vanishes. -/
theorem exists_deriv_ne_zero (hf : ContDiff ℝ 2 f) (hna : ¬ ∃ a c : ℝ, ∀ x, f x = a * x + c) :
    ∃ p, deriv f p ≠ 0 ∧ deriv (deriv f) p ≠ 0 := by
  obtain ⟨p, hp⟩ : ∃ p, deriv (deriv f) p ≠ 0 := by
    by_contra h; push Not at h; exact hna (exists_affine_of_deriv_deriv_eq_zero hf h)
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ x in 𝓝 p, deriv (deriv f) x ≠ 0 :=
    (continuous_deriv_deriv hf).continuousAt.eventually_ne hp
  have hz : deriv f =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hev] with x hx
    by_contra h0; exact hx (hcon x h0)
  exact hp (by rw [hz.deriv_eq]; simp)

end Analytic

/-! ### Inverting a monotone map on an interval -/

section Inverse

variable {f f' : ℝ → ℝ} {u v : ℝ}

/-- The inverse of `f` on `[u, v]`. -/
def inv (f : ℝ → ℝ) (u v : ℝ) : ℝ → ℝ := Function.invFunOn f (Icc u v)

variable (huv : u < v) (hf : ∀ x ∈ Icc u v, HasDerivAt f (f' x) x)
  (hpos : ∀ x ∈ Icc u v, 0 < f' x)

include hf hpos in
theorem strictMonoOn : StrictMonoOn f (Icc u v) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc u v)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hf x (Ioo_subset_Icc_self hx)).deriv]
  exact hpos x (Ioo_subset_Icc_self hx)

include huv hf in
theorem inv_spec {y : ℝ} (hy : y ∈ Icc (f u) (f v)) :
    inv f u v y ∈ Icc u v ∧ f (inv f u v y) = y := by
  have hex : ∃ x ∈ Icc u v, f x = y :=
    intermediate_value_Icc huv.le (fun x hx => (hf x hx).continuousAt.continuousWithinAt) hy
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

include huv hf hpos in
theorem inv_apply {x : ℝ} (hx : x ∈ Icc u v) : inv f u v (f x) = x := by
  have hm := strictMonoOn hf hpos
  have hy : f x ∈ Icc (f u) (f v) :=
    ⟨hm.monotoneOn ⟨le_rfl, huv.le⟩ hx hx.1, hm.monotoneOn hx ⟨huv.le, le_rfl⟩ hx.2⟩
  have := inv_spec huv hf hy
  exact hm.injOn this.1 hx this.2

include huv hf in
theorem inv_mem_Ioo {y : ℝ} (hy : y ∈ Ioo (f u) (f v)) : inv f u v y ∈ Ioo u v := by
  obtain ⟨h1, h2⟩ := inv_spec huv hf (Ioo_subset_Icc_self hy)
  refine ⟨lt_of_le_of_ne h1.1 fun h => ?_, lt_of_le_of_ne h1.2 fun h => ?_⟩
  · rw [← h] at h2; exact hy.1.ne h2
  · rw [h] at h2; exact hy.2.ne' h2

include huv hf hpos in
theorem continuousAt_inv {y : ℝ} (hy : y ∈ Ioo (f u) (f v)) : ContinuousAt (inv f u v) y := by
  have hm := strictMonoOn hf hpos
  have hmono : MonotoneOn (inv f u v) (Icc (f u) (f v)) := by
    intro y₁ hy₁ y₂ hy₂ h
    obtain ⟨a₁, b₁⟩ := inv_spec huv hf hy₁
    obtain ⟨a₂, b₂⟩ := inv_spec huv hf hy₂
    by_contra hlt; push Not at hlt
    have := hm a₂ a₁ hlt
    rw [b₁, b₂] at this; linarith
  have himg : inv f u v '' Icc (f u) (f v) = Icc u v := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact (inv_spec huv hf hy).1
    · intro x hx
      exact ⟨f x, ⟨hm.monotoneOn ⟨le_rfl, huv.le⟩ hx hx.1, hm.monotoneOn hx ⟨huv.le, le_rfl⟩ hx.2⟩,
        inv_apply huv hf hpos hx⟩
  refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono (Icc_mem_nhds hy.1 hy.2) ?_
  rw [himg]
  have := inv_mem_Ioo huv hf hy
  exact Icc_mem_nhds this.1 this.2

include huv hf hpos in
theorem hasDerivAt_inv {y : ℝ} (hy : y ∈ Ioo (f u) (f v)) :
    HasDerivAt (inv f u v) (f' (inv f u v y))⁻¹ y := by
  have hmem := Ioo_subset_Icc_self (inv_mem_Ioo huv hf hy)
  refine HasDerivAt.of_local_left_inverse (continuousAt_inv huv hf hpos hy) (hf _ hmem)
    (hpos _ hmem).ne' ?_
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  exact (inv_spec huv hf (Ioo_subset_Icc_self hz)).2

end Inverse

/-! ### From decay data on `[0, 1]` to a witness -/

open ExplicitSquare CantorSelfSimilar QuarterCantorDecay BaseCantorDecay in
/-- If `G` has second derivative bounded away from `0` on `[0, 1]` and `f (G t) = q + s t` there,
then some absolutely normal `x` has `f x` not normal in base `b`. -/
theorem exists_of_window {b : ℕ} (hb : 2 ≤ b) {f G G' G'' : ℝ → ℝ} {a A : ℝ} {q s : ℚ}
    (hs : s ≠ 0) (ha : 0 < a) (hGm : Measurable G)
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (G' t) t)
    (hG' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G' (G'' t) t)
    (hlo : ∀ t ∈ Icc (0 : ℝ) 1, a ≤ |G'' t|) (hhi : ∀ t ∈ Icc (0 : ℝ) 1, |G'' t| ≤ A)
    (hsign : (∀ t ∈ Icc (0 : ℝ) 1, 0 < G'' t) ∨ ∀ t ∈ Icc (0 : ℝ) 1, G'' t < 0)
    (hfG : ∀ t ∈ Icc (0 : ℝ) 1, f (G t) = s * t + q) :
    ∃ x : ℝ, Real.IsAbsolutelyNormal x ∧ ¬ Real.IsNormalIn b (f x) := by
  rcases (show b = 2 ∨ 3 ≤ b by omega) with rfl | hb3
  · have hW : ∀ t ∈ QuarterCantorDecay.W, t ∈ Icc (0 : ℝ) 1 :=
      fun t ht => ⟨by linarith [ht.1], ht.2⟩
    have hd : PolyDecay G := polyDecay_of_abs ha hGm (fun t ht => hG t (hW t ht))
      (fun t ht => hG' t (hW t ht)) (fun t ht => hlo t (hW t ht)) (fun t ht => hhi t (hW t ht))
      (hsign.imp (fun h t ht => h t (hW t ht)) (fun h t ht => h t (hW t ht)))
    obtain ⟨ω, hω⟩ := (ae_isAbsolutelyNormal_of_polyDecay hGm hd).exists
    refine ⟨_, hω, fun h => ?_⟩
    rw [hfG _ (hW _ (cantorReal_mem_window ω)), Real.isNormalIn_mul_add_ratCast_iff le_rfl hs]
      at h
    exact not_isNormalIn_two_pow_cantorReal ω one_pos (by simpa using h)
  · have hd : PolyDecayB b G := polyDecayB_of_abs hb ha hGm hG hG' hlo hhi hsign
    obtain ⟨ω, hω⟩ := (ae_isAbsolutelyNormal_of_polyDecayB hGm hd).exists
    refine ⟨_, hω, fun h => ?_⟩
    rw [hfG _ (bReal_mem hb ω), Real.isNormalIn_mul_add_ratCast_iff hb hs] at h
    have := not_isNormalIn_bReal_add hb3 ω 0
    simp only [Int.cast_zero, add_zero] at this
    exact this h

/-! ### The local inverse -/

open Classical in
/-- **Core construction.** If `f' > 0` and `f'' ≠ 0` at `p` (with `f'`, `f''` continuous), then some
absolutely normal `x` has `f x` not normal in base `b`. -/
theorem exists_of_pos {b : ℕ} (hb : 2 ≤ b) {f F' F'' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt f (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hc1 : Continuous F') (hc2 : Continuous F'') {p : ℝ} (h1 : 0 < F' p) (h2 : F'' p ≠ 0) :
    ∃ x : ℝ, Real.IsAbsolutelyNormal x ∧ ¬ Real.IsNormalIn b (f x) := by
  have h2' : 0 < |F'' p| := abs_pos.2 h2
  obtain ⟨δ1, hδ1, H1⟩ := Metric.continuous_iff.1 hc1 p (F' p / 2) (by positivity)
  obtain ⟨δ2, hδ2, H2⟩ := Metric.continuous_iff.1 hc2 p (|F'' p| / 2) (by positivity)
  set ε := min δ1 δ2 / 2 with hεdef
  have hε : 0 < ε := by positivity
  set u := p - ε
  set v := p + ε
  have huv : u < v := by simp only [u, v]; linarith
  have hd : ∀ x ∈ Icc u v, dist x p < δ1 ∧ dist x p < δ2 := fun x hx => by
    have : |x - p| ≤ ε := abs_le.2 ⟨by simp only [u] at hx; linarith [hx.1],
      by simp only [v] at hx; linarith [hx.2]⟩
    rw [Real.dist_eq]
    constructor <;> [have := min_le_left δ1 δ2; have := min_le_right δ1 δ2] <;> linarith
  have hb1 : ∀ x ∈ Icc u v, F' p / 2 < F' x ∧ F' x < 3 * F' p / 2 := fun x hx => by
    have := H1 x (hd x hx).1; rw [Real.dist_eq, abs_sub_lt_iff] at this
    constructor <;> linarith
  have hb2 : ∀ x ∈ Icc u v, |F'' x - F'' p| < |F'' p| / 2 := fun x hx => by
    have := H2 x (hd x hx).2; rwa [Real.dist_eq] at this
  have hfI : ∀ x ∈ Icc u v, HasDerivAt f (F' x) x := fun x _ => hF x
  have hpos : ∀ x ∈ Icc u v, 0 < F' x := fun x hx => by linarith [(hb1 x hx).1]
  have hm := strictMonoOn hfI hpos
  have hpI : p ∈ Icc u v := ⟨by simp only [u]; linarith, by simp only [v]; linarith⟩
  have hα : f u < f p := hm ⟨le_rfl, huv.le⟩ hpI (by simp only [u]; linarith)
  have hβ : f p < f v := hm hpI ⟨huv.le, le_rfl⟩ (by simp only [v]; linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hα
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (sub_pos.2 (hq2.trans hβ))
  have hs1' : (0 : ℝ) < s := by exact_mod_cast hs1
  set g := inv f u v
  set U : Set ℝ := {t : ℝ | (s : ℝ) * t + q ∈ Ioo (f u) (f v)}
  have haff_c : Continuous fun t : ℝ => (s : ℝ) * t + q := by fun_prop
  have hU : IsOpen U := isOpen_Ioo.preimage haff_c
  have hIU : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ U := fun t ht => by
    simp only [U, mem_ofPred_eq, mem_Ioo]
    constructor <;> nlinarith [ht.1, ht.2]
  set G0 : ℝ → ℝ := fun t => g (s * t + q)
  set G : ℝ → ℝ := U.piecewise G0 fun _ => 0
  have haff : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (s : ℝ) * t + q) s t := fun t =>
    (((hasDerivAt_id' t).const_mul (s : ℝ)).add_const (q : ℝ)).congr_deriv (mul_one _)
  have hG0 : ∀ t ∈ U, HasDerivAt G0 ((F' (G0 t))⁻¹ * s) t := fun t ht =>
    (hasDerivAt_inv huv hfI hpos ht).comp t (haff t)
  have hG0I : ∀ t ∈ U, G0 t ∈ Icc u v := fun t ht =>
    (inv_spec huv hfI (Ioo_subset_Icc_self ht)).1
  have hGeq : ∀ t ∈ U, G =ᶠ[𝓝 t] G0 := fun t ht => by
    filter_upwards [hU.mem_nhds ht] with z hz
    simp [G, hz]
  set G' : ℝ → ℝ := fun t => (F' (G0 t))⁻¹ * s
  set G'' : ℝ → ℝ := fun t => -(F'' (G0 t)) * s ^ 2 / F' (G0 t) ^ 3
  have hG : ∀ t ∈ U, HasDerivAt G (G' t) t := fun t ht =>
    (hG0 t ht).congr_of_eventuallyEq (hGeq t ht)
  have hG' : ∀ t ∈ U, HasDerivAt G' (G'' t) t := fun t ht => by
    have hne : F' (G0 t) ≠ 0 := (hpos _ (hG0I t ht)).ne'
    exact ((((hF' (G0 t)).comp t (hG0 t ht)).inv hne).mul_const (s : ℝ)).congr_deriv
      (by simp only [G'', Function.comp]; field_simp)
  have hGm : Measurable G := by
    refine ContinuousOn.measurable_piecewise (fun t ht => ?_) continuousOn_const
      hU.measurableSet
    exact ((continuousAt_inv huv hfI hpos ht).comp (f := fun t : ℝ => (s : ℝ) * t + q)
      haff_c.continuousAt).continuousWithinAt
  have habs : ∀ t ∈ Icc (0 : ℝ) 1, |G'' t| = |F'' (G0 t)| * s ^ 2 / F' (G0 t) ^ 3 :=
    fun t ht => by
    have := hpos _ (hG0I t (hIU t ht))
    simp only [G'']
    rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < F' (G0 t) ^ 3),
      abs_of_pos (by positivity : (0 : ℝ) < (s : ℝ) ^ 2)]
  refine exists_of_window hb (q := q) (show s ≠ 0 by exact_mod_cast hs1.ne')
    (G := G) (G' := G') (G'' := G'')
    (a := |F'' p| / 2 * s ^ 2 / (3 * F' p / 2) ^ 3)
    (A := 3 * |F'' p| / 2 * s ^ 2 / (F' p / 2) ^ 3) (by positivity) hGm
    (fun t ht => hG t (hIU t ht)) (fun t ht => hG' t (hIU t ht)) (fun t ht => ?_)
    (fun t ht => ?_) ?_ (fun t ht => ?_)
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
    · refine Or.inl fun t ht => ?_
      have hx := hG0I t (hIU t ht)
      have e2 := hb2 _ hx
      rw [abs_of_neg hneg, abs_lt] at e2
      have : F'' (G0 t) < 0 := by linarith
      have := hpos _ hx
      simp only [G'']
      apply div_pos _ (by positivity)
      have : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
      nlinarith
    · refine Or.inr fun t ht => ?_
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
    exact (inv_spec huv hfI (Ioo_subset_Icc_self htU)).2

end NormalNumbers.Rigidity

namespace Real

open NormalNumbers.Rigidity

/-- **Non-preservation by non-affine `C²` maps**: if `f` is `C²` and not affine, then for every
base `b ≥ 2` some absolutely normal `x` has `f x` not normal in base `b`. -/
theorem exists_isAbsolutelyNormal_not_isNormalIn_of_contDiff {b : ℕ} (hb : 2 ≤ b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hna : ¬ ∃ a c : ℝ, ∀ x, f x = a * x + c) :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsNormalIn b (f x) := by
  obtain ⟨p, hp1, hp2⟩ := exists_deriv_ne_zero hf hna
  have hc1 : Continuous (deriv f) := (contDiff_deriv hf).continuous
  rcases lt_or_gt_of_ne hp1 with hneg | hpos
  · obtain ⟨x, hx, h⟩ := exists_of_pos hb (f := fun x => -f x) (F' := fun x => -deriv f x)
      (F'' := fun x => -deriv (deriv f) x) (fun x => (hasDerivAt_deriv hf x).neg)
      (fun x => (hasDerivAt_deriv_deriv hf x).neg) hc1.neg (continuous_deriv_deriv hf).neg
      (p := p) (by linarith) (neg_ne_zero.2 hp2)
    exact ⟨x, hx, fun h' => h (h'.neg hb)⟩
  · exact exists_of_pos hb (hasDerivAt_deriv hf) (hasDerivAt_deriv_deriv hf) hc1
      (continuous_deriv_deriv hf) hpos hp2

/-- **`C²` affine rigidity in a fixed base** (Manai, arXiv:2609.24665): a `C²` map sending every
base-`b` normal number (`b ≥ 2`) to a base-`b` normal number is affine. -/
theorem exists_affine_of_contDiff_two_preserves_isNormalIn {b : ℕ} (hb : 2 ≤ b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hpres : ∀ x : ℝ, IsNormalIn b x → IsNormalIn b (f x)) :
    ∃ a c : ℝ, ∀ x : ℝ, f x = a * x + c := by
  by_contra hna
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_not_isNormalIn_of_contDiff hb hf hna
  exact h (hpres x (hx b hb))

/-- **`C²` affine rigidity for absolute normality** (Manai, arXiv:2609.24665): a `C²` map sending
every absolutely normal number to an absolutely normal number is affine. -/
theorem exists_affine_of_contDiff_two_preserves_isAbsolutelyNormal {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hpres : ∀ x : ℝ, IsAbsolutelyNormal x → IsAbsolutelyNormal (f x)) :
    ∃ a c : ℝ, ∀ x : ℝ, f x = a * x + c := by
  by_contra hna
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_not_isNormalIn_of_contDiff le_rfl hf hna
  exact h (hpres x hx 2 le_rfl)

end Real
