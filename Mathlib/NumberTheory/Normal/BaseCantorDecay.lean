/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.QuarterCantorDecay

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Polynomial Fourier decay of nonlinear images of a base-`b` Cantor measure

For `b ≥ 2`, let `Y = ∑ ωᵢ b^{-(i+1)}` with fair coins `ωᵢ ∈ {0, 1}` (`bReal b ω`). For `b ≥ 3`
the base-`b` digits of `Y` avoid `2`, so `Y` is not normal in base `b`
(`not_isNormal_bReal`). We prove that for every `F` with `0 < a ≤ F'' ≤ A` on `[0, 1]` the
pushforward of the law of `Y` under `F` has polynomial Fourier decay (`polyDecay`), by the
argument of `NormalNumbers.QuarterCantorDecay` with `4` replaced by `b`: a Riesz product,
linearisation on cylinders, and block averaging over coin flips.

## References

* R. Kaufman, *On the theorem of Jarník and Besicovitch*, Acta Arith. 39 (1981), 265–267.
* C. A. Mosquera and P. S. Shmerkin, *Self-similar measures: asymptotic bounds for the dimension
  and Fourier decay of smooth images*, Ann. Acad. Sci. Fenn. Math. 43 (2018), 823–834.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace NormalNumbers.BaseCantorDecay

open ExplicitSquare CantorSelfSimilar CantorCylinders QuarterCantorDecay

variable {b : ℕ}

/-! ### The base-`b` Cantor law -/

/-- The digits `ωᵢ ∈ {0, 1}`. -/
def bDigits (ω : ℕ → Bool) (i : ℕ) : ℕ := if ω i then 1 else 0

/-- The base-`b` Cantor point `∑ ωᵢ b^{-(i+1)}`. -/
def bReal (b : ℕ) (ω : ℕ → Bool) : ℝ := realOfDigits b (bDigits ω)

/-- Fourier transform of `F_* μ_b`, `μ_b` the law of `bReal b` under fair coins. -/
def bFourier (b : ℕ) (F : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ ω, Complex.exp (2 * π * Complex.I * ((ξ * F (bReal b ω) : ℝ) : ℂ)) ∂coinMeasure

/-- Polynomial Fourier decay of `F_* μ_b`. -/
def PolyDecayB (b : ℕ) (F : ℝ → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ξ : ℝ, ξ ≠ 0 → ‖bFourier b F ξ‖ ≤ C * |ξ| ^ (-δ)

theorem bDigits_le (ω : ℕ → Bool) (i : ℕ) : (bDigits ω i : ℝ) ≤ 1 := by
  unfold bDigits; split_ifs <;> norm_num

theorem summable_bReal (hb : 2 ≤ b) (ω : ℕ → Bool) :
    Summable fun i => (bDigits ω i : ℝ) / (b : ℝ) ^ (i + 1) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_geometric_of_lt_one (r := 1 / (b : ℝ)) (by positivity)
      ((div_lt_one (by linarith)).2 hb1))
  rw [div_pow, one_pow]
  exact div_le_div₀ zero_le_one (bDigits_le ω i) (by positivity)
    (pow_le_pow_right₀ hb1.le (Nat.le_succ i))

theorem bReal_consB (hb : 2 ≤ b) (c : Bool) (ω : ℕ → Bool) :
    bReal b (consB c ω) = ((if c then 1 else 0) + bReal b ω) / b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  unfold bReal realOfDigits
  rw [(summable_bReal hb (consB c ω)).tsum_eq_zero_add, add_div, ← tsum_div_const]
  congr 1
  · cases c <;> simp [bDigits, consB]
  · refine tsum_congr fun i => ?_
    simp only [bDigits, consB, pow_succ]
    field_simp
    rfl

theorem measurable_bReal : Measurable (bReal b) := by
  unfold bReal realOfDigits
  refine Measurable.tsum fun i => Measurable.div_const ?_ _
  refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
  exact (measurable_of_countable (fun c : Bool => if c then 1 else 0)).comp (measurable_pi_apply i)

/-- The window `[0, 1]`. -/
abbrev W0 : Set ℝ := Set.Icc (0 : ℝ) 1

theorem bReal_mem (hb : 2 ≤ b) (ω : ℕ → Bool) : bReal b ω ∈ W0 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hs := summable_bReal hb ω
  refine ⟨tsum_nonneg fun i => by positivity, ?_⟩
  have hg : Summable fun i : ℕ => (1 / (b : ℝ)) ^ (i + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by positivity)
      ((div_lt_one (by linarith)).2 hb1))
  calc bReal b ω = ∑' i, (bDigits ω i : ℝ) / (b : ℝ) ^ (i + 1) := rfl
    _ ≤ ∑' i : ℕ, (1 / (b : ℝ)) ^ (i + 1) := by
        refine hs.tsum_le_tsum (fun i => ?_) hg
        rw [div_pow, one_pow]; gcongr; exact bDigits_le ω i
    _ = (1 - 1 / (b : ℝ))⁻¹ * (1 / (b : ℝ)) := by
        simp_rw [pow_succ]
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity)
          ((div_lt_one (by linarith)).2 hb1)]
    _ ≤ 1 := by
        have h1 : (1 : ℝ) - 1 / b = (b - 1) / b := by field_simp
        rw [h1, inv_div, div_mul_div_comm, mul_one, div_le_one (by nlinarith)]
        nlinarith

/-- For `b ≥ 3` the digit `2` never occurs, so `bReal b ω` is not normal in base `b`. -/
theorem not_isNormal_bReal (hb : 3 ≤ b) (ω : ℕ → Bool) : ¬ IsNormal b (bReal b ω) := by
  intro h
  have hlt : ∀ i, bDigits ω i < b := fun i => by unfold bDigits; split_ifs <;> omega
  have hp : ProperDigits b (bDigits ω) := fun N =>
    ⟨N, le_rfl, by unfold bDigits; split_ifs <;> omega⟩
  have hmem := realOfDigits_mem_Ico b (by omega) _ hlt hp
  rw [Set.mem_Ico] at hmem
  unfold IsNormal at h
  rw [show Int.fract (bReal b ω) = bReal b ω from Int.fract_eq_self.mpr hmem, bReal,
    digitOf_realOfDigits b (by omega) _ hlt hp] at h
  have ht := h [2] (by simp) (by intro d hd; simp at hd; omega)
  have h0 : ∀ n, countOccurrences [2] ((List.range n).map (bDigits ω)) = 0 := by
    intro n
    rw [countOccurrences_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i - ⟨-, h⟩
    simp only [List.length_singleton, List.range'_one, List.map_cons, List.map_nil,
      List.cons.injEq, and_true] at h
    unfold bDigits at h
    split_ifs at h; omega
  simp only [h0, Nat.cast_zero, zero_div] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  have hb0 : (0 : ℝ) < (b : ℝ) ^ [2].length := by positivity
  exact (inv_pos.2 hb0).ne this

/-! ### Self-similarity and cylinders -/

/-- The IFS map `ψ_c t = (c + t) / b`. -/
def psiB (b : ℕ) (c : Bool) (t : ℝ) : ℝ := ((if c then 1 else 0) + t) / b

theorem continuous_psiB (c : Bool) : Continuous (psiB b c) := by unfold psiB; fun_prop

theorem bFourier_self_similar (hb : 2 ≤ b) (F : ℝ → ℝ) (hF : Measurable F) (ξ : ℝ) :
    bFourier b F ξ =
      2⁻¹ * bFourier b (F ∘ psiB b true) ξ + 2⁻¹ * bFourier b (F ∘ psiB b false) ξ := by
  set g : (ℕ → Bool) → ℂ := fun ω =>
    Complex.exp (2 * Real.pi * Complex.I * ((ξ * F (bReal b ω) : ℝ) : ℂ))
  have hgm : Measurable g := by
    refine Complex.measurable_exp.comp (measurable_const.mul ?_)
    exact Complex.measurable_ofReal.comp (measurable_const.mul (hF.comp measurable_bReal))
  have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      simp only [g, Complex.norm_exp]
      simp)
  have hpf : ∀ c, bFourier b (F ∘ psiB b c) ξ = ∫ ω, g (consB c ω) ∂coinMeasure := by
    intro c
    unfold bFourier
    congr 1; funext ω
    simp only [g, Function.comp, bReal_consB hb, psiB]
  rw [hpf, hpf]
  unfold bFourier
  change ∫ ω, g ω ∂coinMeasure = _
  conv_lhs => rw [coinMeasure_eq]
  rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
      ((hgi _ inferInstance).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    integral_map (measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
    integral_map (measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
  simp [ENNReal.toReal_inv]

/-- Offset of the cylinder map `φ_w`. -/
def offsB (b : ℕ) : List Bool → ℝ
  | [] => 0
  | c :: w => (if c then 1 else 0) / b + offsB b w / b

/-- The cylinder map `φ_w t = offs w + t / b^{|w|}`. -/
def phiB (b : ℕ) (w : List Bool) (t : ℝ) : ℝ := offsB b w + t / (b : ℝ) ^ w.length

theorem psiB_comp_phiB (hb : 2 ≤ b) (c : Bool) (w : List Bool) :
    psiB b c ∘ phiB b w = phiB b (c :: w) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  funext t
  simp only [Function.comp, psiB, phiB, offsB, List.length_cons, pow_succ]
  field_simp
  ring

theorem bFourier_cylinders (hb : 2 ≤ b) (m : ℕ) (F : ℝ → ℝ) (hF : Measurable F) (ξ : ℝ) :
    bFourier b F ξ =
      ((2 : ℂ) ^ m)⁻¹ * ((words m).map fun w => bFourier b (F ∘ phiB b w) ξ).sum := by
  induction m generalizing F with
  | zero =>
    simp [words]
    congr 1; funext t; simp [phiB, offsB]
  | succ m ih =>
    rw [bFourier_self_similar hb F hF ξ, ih _ (hF.comp (continuous_psiB true).measurable),
      ih _ (hF.comp (continuous_psiB false).measurable)]
    simp only [words, List.map_append, List.map_map, List.sum_append, Function.comp_assoc,
      psiB_comp_phiB hb]
    simp only [Function.comp_def]
    ring

theorem phiB_mem (hb : 2 ≤ b) (w : List Bool) {t : ℝ} (ht : t ∈ W0) : phiB b w t ∈ W0 := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  induction w generalizing t with
  | nil => simpa [phiB, offsB] using ht
  | cons c w ih =>
    rw [← psiB_comp_phiB hb]
    have := ih ht
    simp only [Function.comp, psiB]
    constructor
    · apply div_nonneg _ (by linarith); split_ifs <;> linarith [this.1]
    · rw [div_le_one (by linarith)]; split_ifs <;> linarith [this.2]

/-! ### The Riesz product -/

theorem norm_bFourier_le_one (F : ℝ → ℝ) (ξ : ℝ) : ‖bFourier b F ξ‖ ≤ 1 := by
  unfold bFourier
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => norm_cexp (ξ * F (bReal b ω)))]
  simp

/-- The Fourier transform of the base-`b` Cantor law itself. -/
abbrev cF (b : ℕ) (s : ℝ) : ℂ := bFourier b id s

theorem bFourier_psiB (hb : 2 ≤ b) (c : Bool) (s : ℝ) :
    bFourier b (id ∘ psiB b c) s =
      Complex.exp (2 * π * Complex.I * ((s * (if c then 1 else 0) / b : ℝ) : ℂ)) *
        cF b (s / b) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  unfold cF bFourier
  rw [← integral_const_mul]
  congr 1; funext ω
  rw [← Complex.exp_add]
  congr 1
  simp only [Function.comp, id, psiB]
  push_cast; field_simp

theorem norm_cF (hb : 2 ≤ b) (s : ℝ) :
    ‖cF b s‖ = |Real.cos (π * s / b)| * ‖cF b (s / b)‖ := by
  have h := bFourier_self_similar hb id measurable_id s
  rw [bFourier_psiB hb, bFourier_psiB hb] at h
  simp only [ite_true, ite_false, Bool.false_eq_true, mul_one, mul_zero, zero_div,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h
  have e1 : Complex.exp (2 * π * Complex.I * ((s / b : ℝ) : ℂ)) =
      Complex.exp (2 * π * Complex.I * ((s / (2 * b) : ℝ) : ℂ)) *
        Complex.exp (((π * s / b : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : (1 : ℂ) = Complex.exp (2 * π * Complex.I * ((s / (2 * b) : ℝ) : ℂ)) *
        Complex.exp (-((π * s / b : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; ring
  have hsum : (2 : ℂ)⁻¹ * (Complex.exp (2 * π * Complex.I * ((s / b : ℝ) : ℂ)) * cF b (s / b)) +
      2⁻¹ * cF b (s / b) = Complex.exp (2 * π * Complex.I * ((s / (2 * b) : ℝ) : ℂ)) *
      (Complex.cos ((π * s / b : ℝ) : ℂ) * cF b (s / b)) := by
    rw [Complex.cos, e1]; nth_rw 2 [← one_mul (cF b (s / b))]; rw [e2]; ring
  rw [show cF b s = bFourier b id s from rfl, h, hsum, norm_mul, norm_cexp, one_mul,
    norm_mul, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]

theorem norm_cF_le_prod (hb : 2 ≤ b) (s : ℝ) (K : ℕ) :
    ‖cF b s‖ ≤ ∏ k ∈ Finset.range K, |Real.cos (π * s / (b * (b : ℝ) ^ k))| := by
  induction K generalizing s with
  | zero => simpa using norm_bFourier_le_one id s
  | succ K ih =>
    rw [Finset.prod_range_succ', norm_cF hb]
    simp only [pow_zero, mul_one]
    rw [mul_comm]
    gcongr
    refine (ih (s / b)).trans_eq (Finset.prod_congr rfl fun k _ => ?_)
    rw [pow_succ]; congr 2; ring

theorem norm_cF_le_blocks (hb : 2 ≤ b) (s : ℝ) (J r L : ℕ) (hLJ : L * r ≤ J) (hr : 0 < r) :
    ‖cF b s‖ ≤ ∏ l ∈ Finset.range L, |Real.cos (π * s / (b * (b : ℝ) ^ (J - l * r)))| := by
  classical
  refine (norm_cF_le_prod hb s (J + 1)).trans ?_
  have hinj : Set.InjOn (fun l => J - l * r) (Finset.range L) := by
    intro l hl l' hl' h
    simp only [Finset.coe_range, Set.mem_Iio] at hl hl'
    have h1 : l * r ≤ J := le_trans (Nat.mul_le_mul_right _ hl.le) hLJ
    have h2 : l' * r ≤ J := le_trans (Nat.mul_le_mul_right _ hl'.le) hLJ
    have : l * r = l' * r := by simp only at h; omega
    exact Nat.eq_of_mul_eq_mul_right hr this
  rw [← Finset.prod_image (f := fun k => |Real.cos (π * s / (b * (b : ℝ) ^ k))|) hinj]
  refine prod_le_prod_sub ?_ _ (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
  intro k hk
  simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
  omega

/-! ### Calculus on the window -/

section Calculus

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF : ∀ t ∈ W0, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ W0, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W0, a ≤ F'' t) (hhi : ∀ t ∈ W0, F'' t ≤ A)

include hF' hlo hhi in
theorem abs_deriv_sub_le (ha : 0 ≤ a) {x y : ℝ} (hx : x ∈ W0) (hy : y ∈ W0) :
    |F' y - F' x| ≤ A * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F') (f' := F'') (C := A)
    (s := W0) (fun t ht => (hF' t ht).hasDerivWithinAt)
    (fun t ht => by rw [Real.norm_eq_abs, abs_of_nonneg (ha.trans (hlo t ht))]; exact hhi t ht)
    (convex_Icc _ _) hx hy
  simpa [Real.norm_eq_abs] using this

include hF' hlo in
theorem deriv_sub_ge {x y : ℝ} (hx : x ∈ W0) (hy : y ∈ W0) (hxy : x < y) :
    a * (y - x) ≤ F' y - F' x := by
  have hsub : Set.Icc x y ⊆ W0 := Set.Icc_subset_Icc hx.1 hy.2
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F' F'' hxy
    (fun t ht => (hF' t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hF' t (hsub (Set.Ioo_subset_Icc_self ht)))
  have := hlo c (hsub (Set.Ioo_subset_Icc_self hc))
  rw [hceq, le_div_iff₀ (sub_pos.2 hxy)] at this
  linarith

include hF hF' hlo hhi in
theorem abs_taylor_le (ha : 0 ≤ a) {p h : ℝ} (hp : p ∈ W0) (hph : p + h ∈ W0) (h0 : 0 ≤ h) :
    |F (p + h) - F p - F' p * h| ≤ A * h ^ 2 := by
  have hsub : Set.Icc p (p + h) ⊆ W0 := Set.Icc_subset_Icc hp.1 hph.2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => F x - F' p * x) (f' := fun x => F' x - F' p) (C := A * h)
    (s := Set.Icc p (p + h))
    (fun t ht => ((hF t (hsub ht)).sub
      ((hasDerivAt_id t).const_mul (F' p))).hasDerivWithinAt.congr_deriv (by simp))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      refine (abs_deriv_sub_le hF' hlo hhi ha hp (hsub ht)).trans ?_
      gcongr
      · exact ha.trans ((hlo p hp).trans (hhi p hp))
      · rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2])
    (convex_Icc _ _) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  simp only [Real.norm_eq_abs] at this
  rw [show F (p + h) - F p - F' p * h = F (p + h) - F' p * (p + h) - (F p - F' p * p) by ring]
  refine this.trans_eq ?_
  rw [show p + h - p = h by ring, abs_of_nonneg h0]; ring

include hF hF' hlo hhi in
/-- **Linearisation on a cylinder.** -/
theorem norm_bFourier_phiB_le (hb : 2 ≤ b) (hFm : Measurable F) (ha : 0 ≤ a) (w : List Bool)
    (ξ : ℝ) :
    ‖bFourier b (F ∘ phiB b w) ξ‖ ≤ ‖cF b (ξ * F' (phiB b w 0) / (b : ℝ) ^ w.length)‖ +
      2 * π * |ξ| * A / ((b : ℝ) ^ w.length) ^ 2 := by
  set m := w.length
  set p := phiB b w 0 with hp
  set s := ξ * F' p / (b : ℝ) ^ m with hs
  have h4 : (0 : ℝ) < (b : ℝ) ^ m := by
    have : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    positivity
  have hpW : p ∈ W0 := phiB_mem hb w ⟨le_rfl, by norm_num⟩
  set f : (ℕ → Bool) → ℂ := fun ω =>
    Complex.exp (2 * π * Complex.I * ((ξ * (F ∘ phiB b w) (bReal b ω) : ℝ) : ℂ)) with hf
  set g : (ℕ → Bool) → ℂ := fun ω => Complex.exp (2 * π * Complex.I *
    ((ξ * (F p + F' p * (bReal b ω / (b : ℝ) ^ m)) : ℝ) : ℂ)) with hg
  have hcm : Measurable (bReal b) := measurable_bReal
  have hphi : Continuous (phiB b w) := by unfold phiB; fun_prop
  have hfi : Integrable f coinMeasure :=
    Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_const.mul
        ((hFm.comp hphi.measurable).comp hcm))))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => (norm_cexp _).le)
  have hgi : Integrable g coinMeasure :=
    Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_const.mul (measurable_const.add
        (measurable_const.mul (hcm.div_const _))))))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => (norm_cexp _).le)
  have hgint : ∫ ω, g ω ∂coinMeasure =
      Complex.exp (2 * π * Complex.I * ((ξ * F p : ℝ) : ℂ)) * cF b s := by
    unfold cF bFourier
    rw [← integral_const_mul]
    congr 1; funext ω
    simp only [hg, hs, id]
    rw [← Complex.exp_add]; congr 1
    push_cast
    field_simp
  have hpt : ∀ ω, ‖f ω - g ω‖ ≤ 2 * π * |ξ| * A / ((b : ℝ) ^ m) ^ 2 := by
    intro ω
    have ht := bReal_mem hb ω
    set h := bReal b ω / (b : ℝ) ^ m with hh
    have h0 : 0 ≤ h := div_nonneg ht.1 h4.le
    have hle : h ≤ 1 / (b : ℝ) ^ m := by
      rw [hh]; exact div_le_div_of_nonneg_right ht.2 h4.le
    have hph : phiB b w (bReal b ω) = p + h := by
      simp only [hp, phiB, hh]; ring
    have hT := abs_taylor_le hF hF' hlo hhi ha hpW (hph ▸ phiB_mem hb w ht) h0
    refine (norm_cexp_sub_le _ _).trans ?_
    simp only [Function.comp, hph]
    rw [← mul_sub, abs_mul]
    have hA : 0 ≤ A := ha.trans ((hlo p hpW).trans (hhi p hpW))
    have : A * h ^ 2 ≤ A / ((b : ℝ) ^ m) ^ 2 := by
      have : h ^ 2 ≤ (1 / (b : ℝ) ^ m) ^ 2 := pow_le_pow_left₀ h0 hle 2
      calc A * h ^ 2 ≤ A * (1 / (b : ℝ) ^ m) ^ 2 := by gcongr
        _ = A / ((b : ℝ) ^ m) ^ 2 := by rw [div_pow, one_pow, mul_one_div]
    calc 2 * π * (|ξ| * |F (p + h) - (F p + F' p * h)|)
        ≤ 2 * π * (|ξ| * (A / ((b : ℝ) ^ m) ^ 2)) := by
          gcongr
          rw [show F (p + h) - (F p + F' p * h) = F (p + h) - F p - F' p * h by ring]
          exact hT.trans this
      _ = 2 * π * |ξ| * A / ((b : ℝ) ^ m) ^ 2 := by ring
  have hsplit : bFourier b (F ∘ phiB b w) ξ =
      ∫ ω, g ω ∂coinMeasure + ∫ ω, (f ω - g ω) ∂coinMeasure := by
    rw [integral_sub hfi hgi]; unfold bFourier; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [hgint, norm_mul, norm_cexp, one_mul]
  · refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)).trans_eq ?_
    simp

end Calculus

/-! ### Words as coin vectors -/

/-- The offset of the cylinder with coin vector `v`. -/
def ptB (b : ℕ) {m : ℕ} (v : Fin m → Bool) : ℝ :=
  ∑ i : Fin m, (if v i then 1 else 0) / (b : ℝ) ^ ((i : ℕ) + 1)

theorem phiB_ofFn {m : ℕ} (v : Fin m → Bool) : phiB b (List.ofFn v) 0 = ptB b v := by
  rw [phiB, zero_div, add_zero]
  induction m with
  | zero => simp [offsB, ptB]
  | succ m ih =>
    rw [List.ofFn_succ, offsB, ih, ptB, ptB, Fin.sum_univ_succ, Finset.sum_div]
    simp [pow_succ, div_div, mul_comm]

theorem ptB_mem (hb : 2 ≤ b) {m : ℕ} (v : Fin m → Bool) : ptB b v ∈ W0 := by
  rw [← phiB_ofFn]; exact phiB_mem hb _ ⟨le_rfl, by norm_num⟩

theorem ptB_update {m : ℕ} (v : Fin m → Bool) (j : Fin m) (c : Bool) :
    ptB b (Function.update v j c) - ptB b v =
      ((if c then 1 else 0) - (if v j then 1 else 0)) / (b : ℝ) ^ ((j : ℕ) + 1) := by
  rw [ptB, ptB, ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · simp only [Function.update_self]; ring
  · intro i _ hij; simp [Function.update_of_ne hij]
  · simp

theorem abs_ptB_flip (hb : 2 ≤ b) {m : ℕ} (v : Fin m → Bool) (j : Fin m) :
    |ptB b (flip j v) - ptB b v| = 1 / (b : ℝ) ^ ((j : ℕ) + 1) := by
  have : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  rw [QuarterCantorDecay.flip, ptB_update]
  cases h : v j <;>
    simp only [Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true] <;>
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) ^ ((j : ℕ) + 1))] <;> norm_num

theorem ptB_sub_ptB_trunc (hb : 2 ≤ b) {m : ℕ} (N : ℕ) (v : Fin m → Bool) :
    0 ≤ ptB b v - ptB b (trunc N v) ∧ ptB b v - ptB b (trunc N v) ≤ 1 / (b : ℝ) ^ N := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hq0 : (0 : ℝ) ≤ 1 / b := by positivity
  have hq1 : (1 : ℝ) / b < 1 := (div_lt_one (by linarith)).2 hb1
  have hd : ptB b v - ptB b (trunc N v) =
      ∑ i : Fin m, (if (i : ℕ) < N then 0 else
        (if v i then 1 else 0) / (b : ℝ) ^ ((i : ℕ) + 1)) := by
    rw [ptB, ptB, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trunc]
    by_cases hi : (i : ℕ) < N <;> by_cases hv : v i <;> simp [hi, hv]
  rw [hd]
  constructor
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  · calc ∑ i : Fin m, (if (i : ℕ) < N then 0 else
            (if v i then 1 else 0) / (b : ℝ) ^ ((i : ℕ) + 1))
        ≤ ∑ i : Fin m, (if (i : ℕ) < N then 0 else 1 / b * (1 / b : ℝ) ^ (i : ℕ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs with h1 h2
          · exact le_rfl
          · exact le_of_eq (by rw [one_div_pow, pow_succ]; field_simp)
          · rw [zero_div]; positivity
      _ = ∑ i ∈ Finset.range m, (if i < N then 0 else 1 / b * (1 / b : ℝ) ^ i) :=
          Fin.sum_univ_eq_sum_range (fun i => if i < N then 0 else 1 / b * (1 / b : ℝ) ^ i) m
      _ ≤ ∑ i ∈ Finset.range (max m N), (if i < N then 0 else 1 / b * (1 / b : ℝ) ^ i) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (le_max_left _ _)) fun i _ _ => ?_
          split_ifs <;> positivity
      _ = ∑ i ∈ Finset.Ico N (max m N), 1 / b * (1 / b : ℝ) ^ i := by
          rw [← Finset.sum_range_add_sum_Ico _ (le_max_right m N)]
          rw [Finset.sum_eq_zero fun i hi =>
            ite_eq_left_iff.2 (fun h => absurd (Finset.mem_range.1 hi) h), zero_add]
          exact Finset.sum_congr rfl fun i hi =>
            ite_eq_right_iff.2 (fun h => absurd h (by simp at hi; omega))
      _ = 1 / b * ∑ i ∈ Finset.Ico N (max m N), (1 / b : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ 1 / b * ((1 / b : ℝ) ^ N / (1 - 1 / b)) := by
          gcongr; exact geom_sum_Ico_le_of_lt_one hq0 hq1
      _ ≤ 1 / (b : ℝ) ^ N := by
          have hpos : 0 < 1 - 1 / (b : ℝ) := by linarith
          have key : 1 / (b : ℝ) ≤ 1 - 1 / b := by
            rw [le_sub_iff_add_le, ← add_div, div_le_one (by linarith)]; linarith
          rw [mul_div_assoc', div_le_iff₀ hpos, one_div_pow]
          have : (0 : ℝ) ≤ 1 / (b : ℝ) ^ N := by positivity
          calc 1 / (b : ℝ) * ((1 : ℝ) / (b : ℝ) ^ N) ≤ (1 - 1 / b) * (1 / (b : ℝ) ^ N) := by
                gcongr
            _ = 1 / (b : ℝ) ^ N * (1 - 1 / b) := by ring

/-! ### The average of the Riesz products over the cylinders -/

section Averaging

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF' : ∀ t ∈ W0, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W0, a ≤ F'' t) (hhi : ∀ t ∈ W0, F'' t ≤ A)

include hF' hlo hhi in
/-- **The cylinder average of the Riesz products decays.** -/
theorem sum_norm_cF_le (hb : 2 ≤ b) (ha : 0 < a) {ξ : ℝ} {m J r L : ℕ} (hr : 0 < r)
    (hLm : L * r ≤ m) (hLJ : L * r ≤ J)
    (hX1 : 1 / (2 * b) ≤ A * (|ξ| / (b : ℝ) ^ (m + J + 2)))
    (hX2 : A * (|ξ| / (b : ℝ) ^ (m + J + 2)) ≤ 1 / 2) :
    ∑ v : Fin m → Bool, ‖cF b (ξ * F' (ptB b v) / (b : ℝ) ^ m)‖ ≤
      ((1 + Real.cos (π * (a / (2 * b * A) / 2))) / 2 + π * b / (2 * (b : ℝ) ^ r)) ^ L * 2 ^ m := by
  have hAa : a ≤ A := (hlo 1 ⟨by norm_num, le_rfl⟩).trans (hhi 1 ⟨by norm_num, le_rfl⟩)
  have hA : 0 < A := ha.trans_le hAa
  have hB0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hB2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set B : ℝ := (b : ℝ) with hBdef
  set X := |ξ| / B ^ (m + J + 2) with hXdef
  set e : ℝ := π * b / (2 * B ^ r) with he
  set c : ℝ := a / (2 * b * A) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 / 4 := by
    rw [hc, div_le_iff₀ (by positivity)]; nlinarith
  -- the surrogate factors
  set u : ℕ → (Fin m → Bool) → ℝ := fun l v =>
    ξ * F' (ptB b (trunc (l * r + r) v)) / (B ^ m * (B * B ^ (J - l * r)))
  set g : ℕ → (Fin m → Bool) → ℝ := fun l v => |Real.cos (π * u l v)| + e
  have hg0 : ∀ l v, 0 ≤ g l v := fun l v => by positivity
  have hpow : ∀ l, l < L → B ^ m * (B * B ^ (J - l * r)) * B ^ (l * r) * B =
      B ^ (m + J + 2) := by
    intro l hl
    have : l * r ≤ J := le_trans (Nat.mul_le_mul_right _ hl.le) hLJ
    rw [show B ^ (m + J + 2) = B ^ m * (B * B ^ (J - l * r)) * B ^ (l * r) * B by
      rw [mul_assoc (B ^ m), mul_assoc B, ← pow_add, Nat.sub_add_cancel this]; ring]
  -- pointwise domination
  have hdom : ∀ v, ‖cF b (ξ * F' (ptB b v) / B ^ m)‖ ≤ ∏ l ∈ Finset.range L, g l v := by
    intro v
    refine (norm_cF_le_blocks hb _ J r L hLJ hr).trans
      (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l hl => ?_)
    have hl := Finset.mem_range.1 hl
    have hd := ptB_sub_ptB_trunc hb (l * r + r) v
    have hF'd := abs_deriv_sub_le hF' hlo hhi ha.le (ptB_mem hb (trunc (l * r + r) v))
      (ptB_mem hb v)
    have key : |π * (ξ * F' (ptB b v) / B ^ m) / (B * B ^ (J - l * r)) - π * u l v| ≤ e := by
      have h4 : (0 : ℝ) < B ^ m * (B * B ^ (J - l * r)) := by positivity
      rw [show π * (ξ * F' (ptB b v) / B ^ m) / (B * B ^ (J - l * r)) - π * u l v =
        π * ξ * (F' (ptB b v) - F' (ptB b (trunc (l * r + r) v))) /
          (B ^ m * (B * B ^ (J - l * r))) by simp only [u]; field_simp]
      rw [abs_div, abs_of_pos h4, abs_mul, abs_mul, abs_of_pos Real.pi_pos, div_le_iff₀ h4]
      have hdiff : |F' (ptB b v) - F' (ptB b (trunc (l * r + r) v))| ≤
          A * (1 / B ^ (l * r + r)) :=
        hF'd.trans (by rw [abs_of_nonneg hd.1]; gcongr; exact hd.2)
      have hX : |ξ| * A = X * A * B ^ (m + J + 2) := by
        rw [hXdef]; field_simp
      calc π * |ξ| * |F' (ptB b v) - F' (ptB b (trunc (l * r + r) v))|
          ≤ π * |ξ| * (A * (1 / B ^ (l * r + r))) := by gcongr
        _ = π * (|ξ| * A) / (B ^ (l * r) * B ^ r) := by rw [pow_add]; ring
        _ = π * (A * X) * B ^ (m + J + 2) / (B ^ (l * r) * B ^ r) := by
          rw [hX]; ring
        _ ≤ π * (1 / 2) * B ^ (m + J + 2) / (B ^ (l * r) * B ^ r) := by gcongr
        _ = e * (B ^ m * (B * B ^ (J - l * r))) := by
          rw [← hpow l hl, he, ← hBdef]; field_simp
    have := Real.abs_cos_sub_cos_le (π * (ξ * F' (ptB b v) / B ^ m) / (B * B ^ (J - l * r)))
      (π * u l v)
    simp only [g]
    have h3 := abs_abs_sub_abs_le_abs_sub (Real.cos (π * (ξ * F' (ptB b v) / B ^ m) /
      (B * B ^ (J - l * r)))) (Real.cos (π * u l v))
    rw [show π * (ξ * F' (ptB b v) / B ^ m) / (B * B ^ (J - l * r)) =
      π * (ξ * F' (ptB b v) / B ^ m / (B * B ^ (J - l * r))) by ring] at this h3 key ⊢
    have := (abs_le.1 (h3.trans (this.trans key))).2
    linarith
  -- the block averaging hypotheses
  have hdep : ∀ l < L, ∀ v v', (∀ j : Fin m, (j : ℕ) < l * r + r → v j = v' j) →
      g l v = g l v' := by
    intro l _ v v' h
    simp only [g, u, trunc_congr h]
  have hflip : ∀ l < L, ∀ v (j : Fin m), (j : ℕ) = l * r →
      g l v + g l (QuarterCantorDecay.flip j v) ≤ 2 * ((1 + Real.cos (π * (c / 2))) / 2 + e) := by
    intro l hl v j hj
    have htr : trunc (l * r + r) (QuarterCantorDecay.flip j v) =
        QuarterCantorDecay.flip j (trunc (l * r + r) v) := by
      have : (j : ℕ) < l * r + r := by omega
      rw [QuarterCantorDecay.flip, trunc_update v j this, QuarterCantorDecay.flip]
      simp [trunc, this]
    set t := trunc (l * r + r) v
    have hpd : |ptB b (QuarterCantorDecay.flip j t) - ptB b t| = 1 / B ^ ((j : ℕ) + 1) :=
      abs_ptB_flip hb t j
    set Δ := u l (QuarterCantorDecay.flip j v) - u l v with hΔ
    have hΔeq : Δ = ξ * (F' (ptB b (QuarterCantorDecay.flip j t)) - F' (ptB b t)) /
        (B ^ m * (B * B ^ (J - l * r))) := by
      simp only [hΔ, u, htr, t]; ring
    have h4 : (0 : ℝ) < B ^ m * (B * B ^ (J - l * r)) := by positivity
    have hlowF : a * |ptB b (QuarterCantorDecay.flip j t) - ptB b t| ≤
        |F' (ptB b (QuarterCantorDecay.flip j t)) - F' (ptB b t)| := by
      rcases lt_or_gt_of_ne (show ptB b (QuarterCantorDecay.flip j t) ≠ ptB b t by
        intro h; rw [h, sub_self, abs_zero] at hpd
        have : (0 : ℝ) < 1 / B ^ ((j : ℕ) + 1) := by positivity
        linarith) with h | h
      · have := deriv_sub_ge hF' hlo (ptB_mem hb _) (ptB_mem hb _) h
        rw [abs_of_neg (sub_neg.2 h), abs_of_neg (by nlinarith)]; linarith
      · have := deriv_sub_ge hF' hlo (ptB_mem hb _) (ptB_mem hb _) h
        rw [abs_of_pos (sub_pos.2 h), abs_of_pos (by nlinarith)]; linarith
    have hupF := abs_deriv_sub_le hF' hlo hhi ha.le (ptB_mem hb t)
      (ptB_mem hb (QuarterCantorDecay.flip j t))
    have hscale : |ξ| * |ptB b (QuarterCantorDecay.flip j t) - ptB b t| /
        (B ^ m * (B * B ^ (J - l * r))) = X := by
      rw [hpd, hXdef, ← hpow l hl, ← hj, pow_succ]; field_simp
    have hΔabs : |Δ| = |ξ| * |F' (ptB b (QuarterCantorDecay.flip j t)) - F' (ptB b t)| /
        (B ^ m * (B * B ^ (J - l * r))) := by
      rw [hΔeq, abs_div, abs_mul, abs_of_pos h4]
    have hΔlo : c ≤ |Δ| := by
      have : a * X ≤ |Δ| := by
        rw [hΔabs, ← hscale]
        calc a * (|ξ| * |ptB b (QuarterCantorDecay.flip j t) - ptB b t| /
              (B ^ m * (B * B ^ (J - l * r))))
            = |ξ| * (a * |ptB b (QuarterCantorDecay.flip j t) - ptB b t|) /
                (B ^ m * (B * B ^ (J - l * r))) := by ring
          _ ≤ _ := by gcongr
      refine le_trans ?_ this
      rw [hc, div_le_iff₀ (by positivity)]
      have : 1 / (2 * B) ≤ A * X := hX1
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    have hΔhi : |Δ| ≤ 1 - c := by
      have : |Δ| ≤ A * X := by
        rw [hΔabs, ← hscale]
        calc |ξ| * |F' (ptB b (QuarterCantorDecay.flip j t)) - F' (ptB b t)| /
              (B ^ m * (B * B ^ (J - l * r)))
            ≤ |ξ| * (A * |ptB b (QuarterCantorDecay.flip j t) - ptB b t|) /
                (B ^ m * (B * B ^ (J - l * r))) := by
              gcongr
          _ = _ := by ring
      linarith
    have := abs_cos_add_abs_cos_le (u l v) hc0 (by linarith) hΔlo hΔhi
    simp only [g]
    rw [show u l (QuarterCantorDecay.flip j v) = u l v + Δ by rw [hΔ]; ring]
    linarith
  calc ∑ v : Fin m → Bool, ‖cF b (ξ * F' (ptB b v) / B ^ m)‖
      ≤ ∑ v, ∏ l ∈ Finset.range L, g l v := Finset.sum_le_sum fun v _ => hdom v
    _ ≤ _ := sum_prod_le hr hLm g hg0 hdep hflip

end Averaging

/-! ### Assembly -/

section Decay

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF : ∀ t ∈ W0, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ W0, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W0, a ≤ F'' t) (hhi : ∀ t ∈ W0, F'' t ≤ A)

include hF hF' hlo hhi in
/-- **One scale.** Splitting into the `2^m` cylinders of depth `m`. -/
theorem norm_bFourier_le_scale (hb : 2 ≤ b) (hFm : Measurable F) (ha : 0 < a) {ξ : ℝ}
    {m J r L : ℕ} (hr : 0 < r) (hLm : L * r ≤ m) (hLJ : L * r ≤ J)
    (hX1 : 1 / (2 * b) ≤ A * (|ξ| / (b : ℝ) ^ (m + J + 2)))
    (hX2 : A * (|ξ| / (b : ℝ) ^ (m + J + 2)) ≤ 1 / 2) :
    ‖bFourier b F ξ‖ ≤
      ((1 + Real.cos (π * (a / (2 * b * A) / 2))) / 2 + π * b / (2 * (b : ℝ) ^ r)) ^ L +
        2 * π * |ξ| * A / ((b : ℝ) ^ m) ^ 2 := by
  set ρ := (1 + Real.cos (π * (a / (2 * b * A) / 2))) / 2 + π * b / (2 * (b : ℝ) ^ r)
  set E := 2 * π * |ξ| * A / ((b : ℝ) ^ m) ^ 2
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [bFourier_cylinders hb m F hFm ξ, sum_words, norm_mul, norm_inv, norm_pow,
    Complex.norm_ofNat, inv_mul_le_iff₀ h2]
  have hsum := sum_norm_cF_le hF' hlo hhi hb ha hr hLm hLJ hX1 hX2
  calc ‖∑ v : Fin m → Bool, bFourier b (F ∘ phiB b (List.ofFn v)) ξ‖
      ≤ ∑ v : Fin m → Bool, ‖bFourier b (F ∘ phiB b (List.ofFn v)) ξ‖ := norm_sum_le _ _
    _ ≤ ∑ v : Fin m → Bool, (‖cF b (ξ * F' (ptB b v) / (b : ℝ) ^ m)‖ + E) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have := norm_bFourier_phiB_le hF hF' hlo hhi hb hFm ha.le (List.ofFn v) ξ
        rwa [List.length_ofFn, phiB_ofFn] at this
    _ ≤ ρ ^ L * 2 ^ m + 2 ^ m * E := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        linarith
    _ = 2 ^ m * (ρ ^ L + E) := by ring

include hF hF' hlo hhi in
/-- **Kaufman-type polynomial Fourier decay** for the pushforward of the base-`b` Cantor law
under a `C²` map with `0 < a ≤ F'' ≤ A` on `[0, 1]`. -/
theorem polyDecay (hb : 2 ≤ b) (hFm : Measurable F) (ha : 0 < a) : PolyDecayB b F := by
  have hAa : a ≤ A := (hlo 1 ⟨by norm_num, le_rfl⟩).trans (hhi 1 ⟨by norm_num, le_rfl⟩)
  have hA : 0 < A := ha.trans_le hAa
  have hB0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hB2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hB1 : (1 : ℝ) < b := by linarith
  set B : ℝ := (b : ℝ) with hBdef
  set ρ0 := (1 + Real.cos (π * (a / (2 * b * A) / 2))) / 2 with hρ0
  have hc0 : 0 < a / (2 * b * A) := by positivity
  have hc1 : a / (2 * b * A) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hcos : Real.cos (π * (a / (2 * b * A) / 2)) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0)
      (show π * (a / (2 * b * A) / 2) ≤ π by nlinarith [Real.pi_pos])
      (show (0 : ℝ) < π * (a / (2 * b * A) / 2) by positivity)
    rwa [Real.cos_zero] at this
  have hρ01 : ρ0 < 1 := by rw [hρ0]; linarith
  have hρ00 : 0 ≤ ρ0 := by rw [hρ0]; linarith [Real.neg_one_le_cos (π * (a / (2 * b * A) / 2))]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (1 - ρ0) / (π * B) by
    have := Real.pi_pos; apply div_pos <;> nlinarith) (show 1 / B < 1 from (div_lt_one hB0).2 hB1)
  set r := n + 1 with hrdef
  have hr : 0 < r := Nat.succ_pos n
  set e : ℝ := π * b / (2 * B ^ r) with he
  have he1 : e ≤ (1 - ρ0) / 2 := by
    have h1 : (1 / B) ^ r ≤ (1 / B) ^ n := pow_le_pow_of_le_one (by positivity)
      ((div_lt_one hB0).2 hB1).le (Nat.le_succ n)
    have h2 : e = π * B / 2 * (1 / B) ^ r := by rw [he, one_div_pow]; ring
    rw [h2]
    have := Real.pi_pos
    calc π * B / 2 * (1 / B) ^ r ≤ π * B / 2 * ((1 - ρ0) / (π * B)) := by gcongr; linarith
      _ = (1 - ρ0) / 2 := by field_simp
  have he0 : 0 ≤ e := by positivity
  set ρ := ρ0 + e with hρ
  set β : ℝ := max ρ (1 / 2) with hβ
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hβ1 : β < 1 := max_lt (by rw [hρ]; linarith) (by norm_num)
  set γ : ℝ := B ^ (3 * r) with hγ
  have hγ1 : 1 < γ := one_lt_pow₀ hB1 (by omega)
  have hγ0 : 0 < γ := by positivity
  set K : ℝ := π * B ^ 2 * γ with hK
  have hK0 : 0 ≤ K := by positivity
  set δ : ℝ := -Real.log β / Real.log γ with hδ
  have hlγ : 0 < Real.log γ := Real.log_pos hγ1
  have hδ0 : 0 < δ := div_pos (neg_pos.2 (Real.log_neg hβ0 hβ1)) hlγ
  have hβγ : γ ^ (-δ) = β := by
    rw [Real.rpow_def_of_pos hγ0, hδ, show Real.log γ * -(-Real.log β / Real.log γ) =
      Real.log β by field_simp, Real.exp_log hβ0]
  set C1 := (1 + K) * (2 * A / (B ^ 2 * γ)) ^ (-δ)
  set C2 := (B / (2 * A)) ^ δ
  have hC1 : 0 < C1 := by positivity
  have hC2 : 0 < C2 := by positivity
  refine ⟨C1 + C2, δ, by positivity, hδ0, fun ξ hξ => ?_⟩
  have hξ0 : 0 < |ξ| := abs_pos.2 hξ
  have hpos : 0 ≤ |ξ| ^ (-δ) := by positivity
  by_cases hsmall : 2 * A * |ξ| / B < 1
  · have hlt : |ξ| ≤ B / (2 * A) := by
      rw [le_div_iff₀ (by positivity)]; rw [div_lt_one hB0] at hsmall; linarith
    have h1 : (B / (2 * A)) ^ (-δ) ≤ |ξ| ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hξ0 hlt (by linarith)
    have h2 : C2 * (B / (2 * A)) ^ (-δ) = 1 := by
      rw [Real.rpow_neg (by positivity), mul_inv_cancel₀ hC2.ne']
    calc ‖bFourier b F ξ‖ ≤ 1 := norm_bFourier_le_one F ξ
      _ = C2 * (B / (2 * A)) ^ (-δ) := h2.symm
      _ ≤ C2 * |ξ| ^ (-δ) := by gcongr
      _ ≤ (C1 + C2) * |ξ| ^ (-δ) := by nlinarith
  push Not at hsmall
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near hsmall hB1
  set q := N / (3 * r) with hq
  set m := q * r * 2 with hm
  set J := N - m with hJ
  have hdm := Nat.div_add_mod N (3 * r)
  have hmod := Nat.mod_lt N (show 0 < 3 * r by omega)
  have hqr : q ≤ q * r := Nat.le_mul_of_pos_right q hr
  rw [← hq, show 3 * r * q = 3 * (q * r) by ring] at hdm
  have hLm : q * r ≤ m := by omega
  have hLJ : q * r ≤ J := by omega
  have hmJ : m + J = N := by omega
  have hexp : N + q ≤ 2 * m + 3 * r := by omega
  have hNq : N ≤ 3 * r * (q + 1) := by
    rw [show 3 * r * (q + 1) = 3 * (q * r) + 3 * r by ring]; omega
  have h4N : (0 : ℝ) < B ^ N := by positivity
  have hX : A * (|ξ| / B ^ (m + J + 2)) = 2 * A * |ξ| / B / (2 * B ^ (N + 1)) := by
    rw [hmJ, show N + 2 = N + 1 + 1 by ring, pow_succ B (N + 1)]; field_simp
  have hX1 : 1 / (2 * b) ≤ A * (|ξ| / B ^ (m + J + 2)) := by
    rw [hX, ← hBdef, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 * (2 * B ^ (N + 1)) = 2 * B * B ^ N := by rw [pow_succ]; ring
      _ ≤ 2 * B * (2 * A * |ξ| / B) := by gcongr
      _ = 2 * A * |ξ| / B * (2 * B) := by ring
  have hX2 : A * (|ξ| / B ^ (m + J + 2)) ≤ 1 / 2 := by
    rw [hX, div_le_iff₀ (by positivity)]; linarith
  have hscale := norm_bFourier_le_scale hF hF' hlo hhi hb hFm ha hr hLm hLJ hX1 hX2
  have hAξ : 2 * (A * |ξ|) < B ^ (N + 2) := by
    have := (div_lt_iff₀ hB0).1 hN2
    calc 2 * (A * |ξ|) = 2 * A * |ξ| := by ring
      _ < B ^ (N + 1) * B := this
      _ = B ^ (N + 2) := (pow_succ B (N + 1)).symm
  -- the linearisation error
  have hpow : B ^ N * B ^ q ≤ (B ^ m) ^ 2 * γ := by
    rw [hγ, ← pow_mul, ← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hB1.le (by rw [mul_comm m 2]; exact hexp)
  have hE : 2 * π * |ξ| * A / ((B ^ m) ^ 2) ≤ K * β ^ q := by
    have hq2 : 1 / B ^ q ≤ β ^ q := by
      calc 1 / B ^ q ≤ 1 / 2 ^ q := by gcongr
        _ = (1 / 2) ^ q := by rw [one_div_pow]
        _ ≤ β ^ q := pow_le_pow_left₀ (by norm_num) (le_max_right _ _) q
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hq2 hK0)
    rw [hK, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 2 * π * |ξ| * A * B ^ q = π * B ^ q * (2 * (A * |ξ|)) := by ring
      _ ≤ π * B ^ q * B ^ (N + 2) := by gcongr
      _ = π * B ^ 2 * (B ^ N * B ^ q) := by rw [pow_add]; ring
      _ ≤ π * B ^ 2 * ((B ^ m) ^ 2 * γ) := by gcongr
      _ = π * B ^ 2 * γ * (B ^ m) ^ 2 := by ring
  have hρq : (ρ0 + e) ^ q ≤ β ^ q := pow_le_pow_left₀ (by linarith) (le_max_left _ _) q
  have hmain : ‖bFourier b F ξ‖ ≤ (1 + K) * β ^ q := by
    have := hscale.trans (add_le_add hρq hE); linarith
  -- converting the scale back to `|ξ|`
  have hγq : 2 * A * |ξ| / (B ^ 2 * γ) ≤ γ ^ q := by
    rw [div_le_iff₀ (by positivity)]
    have : B ^ N ≤ γ ^ (q + 1) := by
      rw [hγ, ← pow_mul]; exact pow_le_pow_right₀ hB1.le (by linarith [hNq])
    rw [pow_succ] at this
    have h2 : B ^ (N + 2) ≤ B ^ 2 * (γ ^ q * γ) := by rw [pow_add, mul_comm]; gcongr
    calc 2 * A * |ξ| = 2 * (A * |ξ|) := by ring
      _ ≤ B ^ (N + 2) := hAξ.le
      _ ≤ B ^ 2 * (γ ^ q * γ) := h2
      _ = γ ^ q * (B ^ 2 * γ) := by ring
  have hβq : β ^ q ≤ (2 * A / (B ^ 2 * γ)) ^ (-δ) * |ξ| ^ (-δ) := by
    rw [← hβγ, ← Real.rpow_natCast, ← Real.rpow_mul hγ0.le, mul_comm, Real.rpow_mul hγ0.le,
      Real.rpow_natCast, ← Real.mul_rpow (by positivity) hξ0.le]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [show 2 * A / (B ^ 2 * γ) * |ξ| = 2 * A * |ξ| / (B ^ 2 * γ) by ring]; exact hγq
  calc ‖bFourier b F ξ‖ ≤ (1 + K) * β ^ q := hmain
    _ ≤ (1 + K) * ((2 * A / (B ^ 2 * γ)) ^ (-δ) * |ξ| ^ (-δ)) := by gcongr
    _ = C1 * |ξ| ^ (-δ) := by ring
    _ ≤ (C1 + C2) * |ξ| ^ (-δ) := by nlinarith

end Decay

end NormalNumbers.BaseCantorDecay
