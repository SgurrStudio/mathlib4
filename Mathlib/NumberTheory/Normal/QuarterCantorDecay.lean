/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.NormalNumbers.CantorCylinders

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Polynomial Fourier decay of nonlinear images of the quarter-Cantor measure

Let `μ` be the law of `cantorReal ω` under fair coins (the quarter-Cantor measure of
`NormalNumbers.ExplicitSquare`, supported in `[1/2, 2/3]`). We prove that for every `F` with
`a ≤ F'' ≤ A` on `[1/2, 1]` (`0 < a`), the pushforward `F_* μ` has polynomial Fourier decay
(`NormalNumbers.QuarterCantorDecay.polyDecay`). This is the input that
`NormalNumbers.ExplicitSquare` cites as `BakerBanajiQuarterCantor`.

## Proof (after Kaufman)

1. **Riesz product.** Self-similarity gives `|μ̂(s)| = |cos(π s / 8)| |μ̂(s / 4)|`, hence
   `|μ̂(s)| ≤ ∏_{k < K} |cos(π s / (8 · 4^k))|`.
2. **Linearisation.** Split `μ` into the `2^m` cylinders of depth `m`
   (`CantorCylinders.pushFourier_cylinders`). On a cylinder `F` is affine up to an error
   `A · 16^{-m}`, so `|\widehat{F_* μ}(ξ)| ≤ 2^{-m} ∑_w |μ̂(ξ F'(p_w) / 4^m)| + 2π A |ξ| 16^{-m}`.
3. **Averaging.** Flipping the `i`-th coin of `w` moves `p_w` by `4^{-i} / 8`, hence moves
   `F'(p_w)` by `≍ 4^{-i}` because `F'' ≍ 1`. At the scale `k = J - i` this moves the Riesz
   factor's phase by an amount in `[c, 1 - c]`, so on average over that coin the factor is at most
   `ρ < 1`. Treating digit blocks of length `r` one at a time (after truncating the digits beyond
   the block, which costs a small `e`) bounds the average of the product by `(ρ + e)^L`.

## References

* R. Kaufman, *On the theorem of Jarník and Besicovitch*, Acta Arith. 39 (1981), 265–267.
* C. A. Mosquera and P. S. Shmerkin, *Self-similar measures: asymptotic bounds for the dimension
  and Fourier decay of smooth images*, Ann. Acad. Sci. Fenn. Math. 43 (2018), 823–834.
* S. Baker and A. Banaji, *Polynomial Fourier decay for fractal measures and their pushforwards*,
  Math. Ann. 392 (2025).
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace NormalNumbers.QuarterCantorDecay

open ExplicitSquare CantorSelfSimilar CantorCylinders

/-! ### Basic facts about the quarter-Cantor law -/

theorem cantorReal_mem_window (ω : ℕ → Bool) : cantorReal ω ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  refine ⟨?_, (cantorReal_mem_Ico ω).2.le⟩
  have hs : Summable fun i => (cantorDigits ω i : ℝ) / ((2 : ℕ) : ℝ) ^ (i + 1) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((summable_geometric_two).mul_left (1 / 2))
    have : (cantorDigits ω i : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (cantorDigits_lt ω i)
    rw [Nat.cast_ofNat, pow_succ]
    calc (cantorDigits ω i : ℝ) / (2 ^ i * 2) ≤ 1 / (2 ^ i * 2) := by gcongr
      _ = 1 / 2 * (1 / 2) ^ i := by rw [div_pow, one_pow]; field_simp
  have := hs.le_tsum 0 (fun j _ => by positivity)
  unfold cantorReal realOfDigits
  simpa [cantorDigits] using this

theorem norm_cexp (x : ℝ) : ‖Complex.exp (2 * π * Complex.I * (x : ℂ))‖ = 1 := by
  rw [show 2 * π * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_pushFourier_le_one (F : ℝ → ℝ) (ξ : ℝ) : ‖pushFourier F ξ‖ ≤ 1 := by
  unfold pushFourier
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => norm_cexp (ξ * F (cantorReal ω)))]
  simp

theorem norm_cexp_sub_le (x y : ℝ) :
    ‖Complex.exp (2 * π * Complex.I * (x : ℂ)) - Complex.exp (2 * π * Complex.I * (y : ℂ))‖ ≤
      2 * π * |x - y| := by
  have h : Complex.exp (2 * π * Complex.I * (x : ℂ)) - Complex.exp (2 * π * Complex.I * (y : ℂ)) =
      Complex.exp (2 * π * Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((2 * π * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [h, norm_mul, norm_cexp, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-! ### Step 1: the Riesz product -/

/-- The Fourier transform of the quarter-Cantor law itself. -/
abbrev cantorFourier (s : ℝ) : ℂ := pushFourier id s

theorem pushFourier_psi (c : Bool) (s : ℝ) :
    pushFourier (id ∘ psi c) s =
      Complex.exp (2 * π * Complex.I * ((s * (3 / 8 + (if c then 1 / 8 else 0)) : ℝ) : ℂ)) *
        cantorFourier (s / 4) := by
  unfold cantorFourier pushFourier
  rw [← integral_const_mul]
  congr 1; funext ω
  rw [← Complex.exp_add]
  congr 1
  simp only [Function.comp, id, psi]
  push_cast; ring

theorem norm_cantorFourier (s : ℝ) :
    ‖cantorFourier s‖ = |Real.cos (π * s / 8)| * ‖cantorFourier (s / 4)‖ := by
  have h := pushFourier_self_similar id measurable_id s
  rw [pushFourier_psi, pushFourier_psi] at h
  simp only [ite_true, ite_false, Bool.false_eq_true] at h
  have e1 : Complex.exp (2 * π * Complex.I * ((s * (3 / 8 + 1 / 8)) : ℝ)) =
      Complex.exp (2 * π * Complex.I * ((7 * s / 16 : ℝ) : ℂ)) *
        Complex.exp (((π * s / 8 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (2 * π * Complex.I * ((s * (3 / 8 + 0)) : ℝ)) =
      Complex.exp (2 * π * Complex.I * ((7 * s / 16 : ℝ) : ℂ)) *
        Complex.exp (-((π * s / 8 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hsum : (2 : ℂ)⁻¹ * (Complex.exp (2 * π * Complex.I * ((s * (3 / 8 + 1 / 8)) : ℝ)) *
      cantorFourier (s / 4)) + 2⁻¹ * (Complex.exp (2 * π * Complex.I * ((s * (3 / 8 + 0)) : ℝ)) *
      cantorFourier (s / 4)) = Complex.exp (2 * π * Complex.I * ((7 * s / 16 : ℝ) : ℂ)) *
      (Complex.cos ((π * s / 8 : ℝ) : ℂ) * cantorFourier (s / 4)) := by
    rw [Complex.cos, e1, e2]; ring
  rw [show cantorFourier s = pushFourier id s from rfl, h, hsum, norm_mul, norm_cexp, one_mul,
    norm_mul, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]

theorem norm_cantorFourier_le_prod (s : ℝ) (K : ℕ) :
    ‖cantorFourier s‖ ≤ ∏ k ∈ Finset.range K, |Real.cos (π * s / (8 * 4 ^ k))| := by
  induction K generalizing s with
  | zero => simpa using norm_pushFourier_le_one id s
  | succ K ih =>
    rw [Finset.prod_range_succ', norm_cantorFourier]
    simp only [pow_zero, mul_one]
    rw [mul_comm]
    gcongr
    refine (ih (s / 4)).trans_eq (Finset.prod_congr rfl fun k _ => ?_)
    rw [pow_succ]; congr 2; ring

/-! ### Calculus on the window -/

/-- The window `[1/2, 1]`, which contains every quarter-Cantor point and every cylinder. -/
abbrev W : Set ℝ := Set.Icc (1 / 2 : ℝ) 1

section Calculus

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF : ∀ t ∈ W, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ W, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W, a ≤ F'' t) (hhi : ∀ t ∈ W, F'' t ≤ A)

include hF' hlo hhi in
theorem abs_deriv_sub_le (ha : 0 ≤ a) {x y : ℝ} (hx : x ∈ W) (hy : y ∈ W) :
    |F' y - F' x| ≤ A * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F') (f' := F'') (C := A)
    (s := W) (fun t ht => (hF' t ht).hasDerivWithinAt)
    (fun t ht => by rw [Real.norm_eq_abs, abs_of_nonneg (ha.trans (hlo t ht))]; exact hhi t ht)
    (convex_Icc _ _) hx hy
  simpa [Real.norm_eq_abs] using this

include hF' hlo in
theorem deriv_sub_ge {x y : ℝ} (hx : x ∈ W) (hy : y ∈ W) (hxy : x < y) :
    a * (y - x) ≤ F' y - F' x := by
  have hsub : Set.Icc x y ⊆ W := Set.Icc_subset_Icc hx.1 hy.2
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F' F'' hxy
    (fun t ht => (hF' t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hF' t (hsub (Set.Ioo_subset_Icc_self ht)))
  have := hlo c (hsub (Set.Ioo_subset_Icc_self hc))
  rw [hceq, le_div_iff₀ (sub_pos.2 hxy)] at this
  linarith

include hF hF' hlo hhi in
theorem abs_taylor_le (ha : 0 ≤ a) {p h : ℝ} (hp : p ∈ W) (hph : p + h ∈ W) (h0 : 0 ≤ h) :
    |F (p + h) - F p - F' p * h| ≤ A * h ^ 2 := by
  have hsub : Set.Icc p (p + h) ⊆ W := Set.Icc_subset_Icc hp.1 hph.2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => F x - F' p * x) (f' := fun x => F' x - F' p) (C := A * h)
    (s := Set.Icc p (p + h))
    (fun t ht => ((hF t (hsub ht)).sub
      ((hasDerivAt_id t).const_mul (F' p))).hasDerivWithinAt.congr_deriv
      (by simp))
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
theorem norm_pushFourier_phi_le (hFm : Measurable F) (ha : 0 ≤ a) (w : List Bool) (ξ : ℝ) :
    ‖pushFourier (F ∘ phi w) ξ‖ ≤ ‖cantorFourier (ξ * F' (phi w (1 / 2)) / 4 ^ w.length)‖ +
      2 * π * |ξ| * A / (4 * 16 ^ w.length) := by
  set m := w.length
  set p := phi w (1 / 2) with hp
  set s := ξ * F' p / 4 ^ m with hs
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have hpW : p ∈ W := phi_mem_window w ⟨le_rfl, by norm_num⟩
  set f : (ℕ → Bool) → ℂ := fun ω =>
    Complex.exp (2 * π * Complex.I * ((ξ * (F ∘ phi w) (cantorReal ω) : ℝ) : ℂ)) with hf
  set g : (ℕ → Bool) → ℂ := fun ω => Complex.exp (2 * π * Complex.I *
    ((ξ * (F p + F' p * ((cantorReal ω - 1 / 2) / 4 ^ m)) : ℝ) : ℂ)) with hg
  have hcm := measurable_cantorReal
  have hphi : Continuous (phi w) := by unfold phi; fun_prop
  have hfi : Integrable f coinMeasure :=
    Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_const.mul
        ((hFm.comp hphi.measurable).comp hcm))))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => (norm_cexp _).le)
  have hgi : Integrable g coinMeasure :=
    Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_const.mul (measurable_const.add
        (measurable_const.mul ((hcm.sub measurable_const).div_const _))))))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => (norm_cexp _).le)
  have hgint : ∫ ω, g ω ∂coinMeasure =
      Complex.exp (2 * π * Complex.I * ((ξ * F p - s / 2 : ℝ) : ℂ)) * cantorFourier s := by
    unfold cantorFourier pushFourier
    rw [← integral_const_mul]
    congr 1; funext ω
    simp only [hg, hs, id]
    rw [← Complex.exp_add]; congr 1
    push_cast
    field_simp
    ring
  have hpt : ∀ ω, ‖f ω - g ω‖ ≤ 2 * π * |ξ| * A / (4 * 16 ^ m) := by
    intro ω
    have ht := cantorReal_mem_window ω
    set h := (cantorReal ω - 1 / 2) / 4 ^ m with hh
    have h0 : 0 ≤ h := div_nonneg (by linarith [ht.1]) h4.le
    have hle : h ≤ 1 / (2 * 4 ^ m) := by
      rw [hh, div_le_div_iff₀ h4 (by positivity)]; nlinarith [ht.2]
    have hph : phi w (cantorReal ω) = p + h := by
      simp only [hp, phi, hh]; field_simp; ring
    have hT := abs_taylor_le hF hF' hlo hhi ha hpW (hph ▸ phi_mem_window w ht) h0
    refine (norm_cexp_sub_le _ _).trans ?_
    simp only [Function.comp, hph]
    rw [← mul_sub, abs_mul]
    have hA : 0 ≤ A := ha.trans ((hlo p hpW).trans (hhi p hpW))
    have : A * h ^ 2 ≤ A / (4 * 16 ^ m) := by
      have : h ^ 2 ≤ (1 / (2 * 4 ^ m)) ^ 2 := pow_le_pow_left₀ h0 hle 2
      calc A * h ^ 2 ≤ A * (1 / (2 * 4 ^ m)) ^ 2 := by gcongr
        _ = A / (4 * 16 ^ m) := by
          rw [show (16 : ℝ) ^ m = (4 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          field_simp; ring
    calc 2 * π * (|ξ| * |F (p + h) - (F p + F' p * h)|) ≤ 2 * π * (|ξ| * (A / (4 * 16 ^ m))) := by
          gcongr
          rw [show F (p + h) - (F p + F' p * h) = F (p + h) - F p - F' p * h by ring]
          exact hT.trans this
      _ = 2 * π * |ξ| * A / (4 * 16 ^ m) := by ring
  have hsplit : pushFourier (F ∘ phi w) ξ =
      ∫ ω, g ω ∂coinMeasure + ∫ ω, (f ω - g ω) ∂coinMeasure := by
    rw [integral_sub hfi hgi]; unfold pushFourier; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [hgint, norm_mul, norm_cexp, one_mul]
  · refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)).trans_eq ?_
    simp

end Calculus

/-! ### Words as coin vectors -/

theorem sum_words {β : Type*} [AddCommMonoid β] (m : ℕ) (f : List Bool → β) :
    ((words m).map f).sum = ∑ v : Fin m → Bool, f (List.ofFn v) := by
  induction m generalizing f with
  | zero => simp [words]
  | succ m ih =>
    rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [words, List.map_append, List.map_map, List.sum_append, Function.comp_def, ih]
    simp [Fin.consEquiv, List.ofFn_succ]

/-- The offset of the cylinder with coin vector `v`. -/
def offsV {m : ℕ} (v : Fin m → Bool) : ℝ :=
  ∑ i : Fin m, (3 / 8 + (if v i then 1 / 8 else 0)) / 4 ^ (i : ℕ)

theorem offs_ofFn {m : ℕ} (v : Fin m → Bool) : offs (List.ofFn v) = offsV v := by
  induction m with
  | zero => simp [offs, offsV]
  | succ m ih =>
    rw [List.ofFn_succ, offs, ih, offsV, offsV, Fin.sum_univ_succ, Finset.sum_div]
    simp only [Fin.val_zero, pow_zero, div_one, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

/-- The left end `phi w (1 / 2)` of the cylinder with coin vector `v`. -/
def pt {m : ℕ} (v : Fin m → Bool) : ℝ := offsV v + 1 / 2 / 4 ^ m

theorem phi_ofFn {m : ℕ} (v : Fin m → Bool) : phi (List.ofFn v) (1 / 2) = pt v := by
  rw [phi, offs_ofFn, List.length_ofFn, pt]

theorem pt_mem {m : ℕ} (v : Fin m → Bool) : pt v ∈ W := by
  rw [← phi_ofFn]; exact phi_mem_window _ ⟨le_rfl, by norm_num⟩

theorem pt_update {m : ℕ} (v : Fin m → Bool) (j : Fin m) (b : Bool) :
    pt (Function.update v j b) - pt v =
      ((if b then 1 / 8 else 0) - (if v j then 1 / 8 else 0)) / 4 ^ (j : ℕ) := by
  rw [pt, pt, add_sub_add_right_eq_sub, offsV, offsV, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single j]
  · simp only [Function.update_self]; ring
  · intro i _ hij; simp [Function.update_of_ne hij]
  · simp

theorem abs_pt_flip {m : ℕ} (v : Fin m → Bool) (j : Fin m) :
    |pt (Function.update v j (!v j)) - pt v| = 1 / 8 / 4 ^ (j : ℕ) := by
  rw [pt_update]
  cases h : v j <;>
    simp only [Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true] <;>
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (j : ℕ))] <;> norm_num

/-- Forget the coins from index `N` on. -/
def trunc {m : ℕ} (N : ℕ) (v : Fin m → Bool) : Fin m → Bool :=
  fun i => if (i : ℕ) < N then v i else false

theorem pt_sub_pt_trunc {m : ℕ} (N : ℕ) (v : Fin m → Bool) :
    0 ≤ pt v - pt (trunc N v) ∧ pt v - pt (trunc N v) ≤ 1 / 6 / 4 ^ N := by
  have hd : pt v - pt (trunc N v) =
      ∑ i : Fin m, (if (i : ℕ) < N then 0 else (if v i then 1 / 8 else 0) / 4 ^ (i : ℕ)) := by
    rw [pt, pt, add_sub_add_right_eq_sub, offsV, offsV, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trunc]
    by_cases hi : (i : ℕ) < N <;> by_cases hv : v i <;> simp [hi, hv]; ring
  rw [hd]
  constructor
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  · calc ∑ i : Fin m, (if (i : ℕ) < N then 0 else (if v i then 1 / 8 else 0) / 4 ^ (i : ℕ))
        ≤ ∑ i : Fin m, (if (i : ℕ) < N then 0 else 1 / 8 * (1 / 4 : ℝ) ^ (i : ℕ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs with h1 h2
          · exact le_rfl
          · exact le_of_eq (by rw [one_div_pow]; ring)
          · rw [zero_div]; positivity
      _ = ∑ i ∈ Finset.range m, (if i < N then 0 else 1 / 8 * (1 / 4 : ℝ) ^ i) :=
          Fin.sum_univ_eq_sum_range (fun i => if i < N then 0 else 1 / 8 * (1 / 4 : ℝ) ^ i) m
      _ ≤ ∑ i ∈ Finset.range (max m N), (if i < N then 0 else 1 / 8 * (1 / 4 : ℝ) ^ i) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (le_max_left _ _)) fun i _ _ => ?_
          split_ifs <;> positivity
      _ = ∑ i ∈ Finset.Ico N (max m N), 1 / 8 * (1 / 4 : ℝ) ^ i := by
          rw [← Finset.sum_range_add_sum_Ico _ (le_max_right m N)]
          rw [Finset.sum_eq_zero fun i hi =>
            ite_eq_left_iff.2 (fun h => absurd (Finset.mem_range.1 hi) h), zero_add]
          exact Finset.sum_congr rfl fun i hi =>
            ite_eq_right_iff.2 (fun h => absurd h (by simp at hi; omega))
      _ = 1 / 8 * ∑ i ∈ Finset.Ico N (max m N), (1 / 4 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ 1 / 8 * ((1 / 4 : ℝ) ^ N / (1 - 1 / 4)) := by
          gcongr; exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ = 1 / 6 / 4 ^ N := by rw [div_pow, one_pow]; ring

theorem trunc_update {m : ℕ} {N : ℕ} (v : Fin m → Bool) (j : Fin m) (hj : (j : ℕ) < N)
    (b : Bool) :
    trunc N (Function.update v j b) = Function.update (trunc N v) j b := by
  funext i
  by_cases hij : i = j
  · subst hij; simp [trunc, hj]
  · simp [trunc, Function.update_of_ne hij]

theorem trunc_congr {m : ℕ} {N : ℕ} {v v' : Fin m → Bool}
    (h : ∀ j : Fin m, (j : ℕ) < N → v j = v' j) :
    trunc N v = trunc N v' := by
  funext i; simp only [trunc]; split_ifs with hi
  · exact h i hi
  · rfl

/-! ### Averaging over one coin -/

theorem abs_cos_pi_eq (u : ℝ) : |Real.cos (π * u)| = Real.cos (π * |u - round u|) := by
  have h := abs_sub_round u
  have key : |Real.cos (π * u)| = |Real.cos (π * (u - round u))| := by
    rw [show π * u = π * (u - round u) + ((round u : ℤ) : ℝ) * π by ring,
      Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hc : 0 ≤ Real.cos (π * (u - round u)) := by
    rw [abs_le] at h
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  rw [key, abs_of_nonneg hc, ← Real.cos_abs (π * (u - round u)), abs_mul,
    abs_of_pos Real.pi_pos]

/-- If two phases differ by an amount at distance `≥ c` from the integers, one of the two Riesz
factors is at most `cos (π c / 2)`. -/
theorem abs_cos_add_abs_cos_le {c Δ : ℝ} (u : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hΔ : c ≤ |Δ|) (hΔ1 : |Δ| ≤ 1 - c) :
    |Real.cos (π * u)| + |Real.cos (π * (u + Δ))| ≤ 1 + Real.cos (π * (c / 2)) := by
  rw [abs_cos_pi_eq, abs_cos_pi_eq]
  set θ₁ := |u - round u|
  set θ₂ := |u + Δ - round (u + Δ)|
  have h₁ : θ₁ ≤ 1 / 2 := abs_sub_round u
  have h₂ : θ₂ ≤ 1 / 2 := abs_sub_round (u + Δ)
  have key : c / 2 ≤ θ₁ ∨ c / 2 ≤ θ₂ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc₁, hc₂⟩ := hcon
    set k : ℤ := round (u + Δ) - round u
    have hk : |Δ - k| < c := by
      have : Δ - k = (u + Δ - round (u + Δ)) - (u - round u) := by simp only [k]; push_cast; ring
      rw [this]
      exact (abs_sub _ _).trans_lt (by linarith)
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
      have := neg_abs_le Δ
      rw [abs_lt] at hk; linarith
    · rw [hk0, Int.cast_zero, sub_zero] at hk; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have := le_abs_self Δ
      rw [abs_lt] at hk; linarith
  have hmono : ∀ θ, c / 2 ≤ θ → θ ≤ 1 / 2 → Real.cos (π * θ) ≤ Real.cos (π * (c / 2)) :=
    fun θ hθ hθ' => Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos]) (by gcongr)
  rcases key with h | h
  · linarith [hmono θ₁ h h₁, Real.cos_le_one (π * θ₂)]
  · linarith [hmono θ₂ h h₂, Real.cos_le_one (π * θ₁)]

/-! ### Averaging over blocks of coins -/

/-- Flip coin `j`. -/
def flip {m : ℕ} (j : Fin m) (v : Fin m → Bool) : Fin m → Bool := Function.update v j (!v j)

theorem flip_flip {m : ℕ} (j : Fin m) (v : Fin m → Bool) : flip j (flip j v) = v := by
  simp [flip]

/-- Flipping coin `j` as a permutation of coin vectors. -/
def flipEquiv {m : ℕ} (j : Fin m) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  ⟨flip j, flip j, flip_flip j, flip_flip j⟩

/-- **Block averaging.** If the `l`-th factor depends only on the coins before `(l + 1) r`, and
on average over the coin `l r` is at most `ρ`, then the average of the product of the first `L`
factors is at most `ρ ^ L`. -/
theorem sum_prod_le {m L r : ℕ} (hr : 0 < r) (hLm : L * r ≤ m) {ρ : ℝ}
    (g : ℕ → (Fin m → Bool) → ℝ) (hg0 : ∀ l v, 0 ≤ g l v)
    (hdep : ∀ l < L, ∀ v v', (∀ j : Fin m, (j : ℕ) < l * r + r → v j = v' j) → g l v = g l v')
    (hflip : ∀ l < L, ∀ v (j : Fin m), (j : ℕ) = l * r → g l v + g l (flip j v) ≤ 2 * ρ) :
    ∑ v, ∏ l ∈ Finset.range L, g l v ≤ ρ ^ L * 2 ^ m := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hLm' : L * r ≤ m := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ L)) hLm
    have ih := ih hLm' (fun l hl => hdep l (by omega)) (fun l hl => hflip l (by omega))
    have hj : L * r < m := lt_of_lt_of_le (by nlinarith) hLm
    set j : Fin m := ⟨L * r, hj⟩
    set G : (Fin m → Bool) → ℝ := fun v => ∏ l ∈ Finset.range L, g l v
    have hG0 : ∀ v, 0 ≤ G v := fun v => Finset.prod_nonneg fun l _ => hg0 l v
    have hGflip : ∀ v, G (flip j v) = G v := by
      intro v
      refine Finset.prod_congr rfl fun l hl => (hdep l (by simp at hl; omega) _ _ fun i hi => ?_)
      have hne : i ≠ j := by
        intro h; subst h; simp at hl; simp only [j] at hi; nlinarith
      simp [flip, Function.update_of_ne hne]
    have hρ : 0 ≤ ρ := by
      have := hflip L (Nat.lt_succ_self L) (fun _ => false) j rfl
      linarith [hg0 L (fun _ => false), hg0 L (flip j fun _ => false)]
    have hsum : ∑ v, G v * g L v = ∑ v, G v * g L (flip j v) := by
      rw [← (flipEquiv j).sum_comp]
      exact Finset.sum_congr rfl fun v _ => by
        simp only [flipEquiv, Equiv.coe_fn_mk, hGflip]
    calc ∑ v, ∏ l ∈ Finset.range (L + 1), g l v = ∑ v, G v * g L v := by
          simp only [Finset.prod_range_succ, G]
      _ = (∑ v, G v * (g L v + g L (flip j v))) / 2 := by
          simp only [mul_add, Finset.sum_add_distrib, ← hsum]; ring
      _ ≤ (∑ v, G v * (2 * ρ)) / 2 := by
          gcongr with v
          · exact hG0 v
          · exact hflip L (Nat.lt_succ_self L) v j rfl
      _ = ρ * ∑ v, G v := by rw [← Finset.sum_mul]; ring
      _ ≤ ρ * (ρ ^ L * 2 ^ m) := by gcongr
      _ = ρ ^ (L + 1) * 2 ^ m := by ring

/-! ### The average of the Riesz products over the cylinders -/

theorem prod_le_prod_sub {ι : Type*} [DecidableEq ι] {s t : Finset ι} (hst : s ⊆ t) (f : ι → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  rw [← Finset.prod_sdiff hst]
  refine mul_le_of_le_one_left (Finset.prod_nonneg fun i hi => h0 i (hst hi)) ?_
  exact Finset.prod_le_one₀ (fun i hi => h0 i (Finset.sdiff_subset hi))
    fun i hi => h1 i (Finset.sdiff_subset hi)

theorem norm_cantorFourier_le_blocks (s : ℝ) (J r L : ℕ) (hLJ : L * r ≤ J) (hr : 0 < r) :
    ‖cantorFourier s‖ ≤ ∏ l ∈ Finset.range L, |Real.cos (π * s / (8 * 4 ^ (J - l * r)))| := by
  classical
  refine (norm_cantorFourier_le_prod s (J + 1)).trans ?_
  have hinj : Set.InjOn (fun l => J - l * r) (Finset.range L) := by
    intro l hl l' hl' h
    simp only [Finset.coe_range, Set.mem_Iio] at hl hl'
    have h1 : l * r ≤ J := le_trans (Nat.mul_le_mul_right _ hl.le) hLJ
    have h2 : l' * r ≤ J := le_trans (Nat.mul_le_mul_right _ hl'.le) hLJ
    have : l * r = l' * r := by simp only at h; omega
    exact Nat.eq_of_mul_eq_mul_right hr this
  rw [← Finset.prod_image (f := fun k => |Real.cos (π * s / (8 * 4 ^ k))|) hinj]
  refine prod_le_prod_sub ?_ _ (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
  intro k hk
  simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
  omega

section Averaging

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF' : ∀ t ∈ W, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W, a ≤ F'' t) (hhi : ∀ t ∈ W, F'' t ≤ A)

include hF' hlo hhi in
/-- **The cylinder average of the Riesz products decays.** -/
theorem sum_norm_cantorFourier_le (ha : 0 < a) {ξ : ℝ} {m J r L : ℕ} (hr : 0 < r)
    (hLm : L * r ≤ m) (hLJ : L * r ≤ J)
    (hX1 : 1 / 8 ≤ A * (|ξ| / (64 * 4 ^ (m + J))))
    (hX2 : A * (|ξ| / (64 * 4 ^ (m + J))) ≤ 1 / 2) :
    ∑ v : Fin m → Bool, ‖cantorFourier (ξ * F' (pt v) / 4 ^ m)‖ ≤
      ((1 + Real.cos (π * (a / (8 * A) / 2))) / 2 + 2 * π / 3 / 4 ^ r) ^ L * 2 ^ m := by
  have hAa : a ≤ A := (hlo 1 ⟨by norm_num, le_rfl⟩).trans (hhi 1 ⟨by norm_num, le_rfl⟩)
  have hA : 0 < A := ha.trans_le hAa
  set X := |ξ| / (64 * 4 ^ (m + J)) with hXdef
  set e : ℝ := 2 * π / 3 / 4 ^ r with he
  set c : ℝ := a / (8 * A) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 / 8 := by
    rw [hc, div_le_iff₀ (by positivity)]; linarith
  -- the surrogate factors
  set u : ℕ → (Fin m → Bool) → ℝ := fun l v =>
    ξ * F' (pt (trunc (l * r + r) v)) / (4 ^ m * (8 * 4 ^ (J - l * r)))
  set g : ℕ → (Fin m → Bool) → ℝ := fun l v => |Real.cos (π * u l v)| + e
  have hg0 : ∀ l v, 0 ≤ g l v := fun l v => by positivity
  have hpow : ∀ l, l < L → (4 : ℝ) ^ m * (8 * 4 ^ (J - l * r)) * 4 ^ (l * r) * 8 =
      64 * 4 ^ (m + J) := by
    intro l hl
    have : l * r ≤ J := le_trans (Nat.mul_le_mul_right _ hl.le) hLJ
    rw [show (64 : ℝ) * 4 ^ (m + J) = 4 ^ m * (8 * 4 ^ (J - l * r)) * 4 ^ (l * r) * 8 by
      rw [mul_assoc (4 ^ m), mul_assoc (8 : ℝ), ← pow_add, Nat.sub_add_cancel this, pow_add]; ring]
  -- pointwise domination
  have hdom : ∀ v, ‖cantorFourier (ξ * F' (pt v) / 4 ^ m)‖ ≤ ∏ l ∈ Finset.range L, g l v := by
    intro v
    refine (norm_cantorFourier_le_blocks _ J r L hLJ hr).trans
      (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l hl => ?_)
    have hl := Finset.mem_range.1 hl
    have hd := pt_sub_pt_trunc (l * r + r) v
    have hF'd := abs_deriv_sub_le hF' hlo hhi ha.le (pt_mem (trunc (l * r + r) v)) (pt_mem v)
    have key : |π * (ξ * F' (pt v) / 4 ^ m) / (8 * 4 ^ (J - l * r)) - π * u l v| ≤ e := by
      have h4 : (0 : ℝ) < 4 ^ m * (8 * 4 ^ (J - l * r)) := by positivity
      rw [show π * (ξ * F' (pt v) / 4 ^ m) / (8 * 4 ^ (J - l * r)) - π * u l v =
        π * ξ * (F' (pt v) - F' (pt (trunc (l * r + r) v))) / (4 ^ m * (8 * 4 ^ (J - l * r))) by
          simp only [u]; field_simp]
      rw [abs_div, abs_of_pos h4, abs_mul, abs_mul, abs_of_pos Real.pi_pos, div_le_iff₀ h4]
      have hdiff : |F' (pt v) - F' (pt (trunc (l * r + r) v))| ≤ A * (1 / 6 / 4 ^ (l * r + r)) :=
        hF'd.trans (by rw [abs_of_nonneg hd.1]; gcongr; exact hd.2)
      have hX : |ξ| * A = X * A * (64 * 4 ^ (m + J)) := by
        rw [hXdef]; field_simp
      calc π * |ξ| * |F' (pt v) - F' (pt (trunc (l * r + r) v))|
          ≤ π * |ξ| * (A * (1 / 6 / 4 ^ (l * r + r))) := by gcongr
        _ = π * (|ξ| * A) / (6 * 4 ^ (l * r + r)) := by ring
        _ = π * (A * X) * (64 * 4 ^ (m + J)) / (6 * 4 ^ (l * r) * 4 ^ r) := by
          rw [hX, pow_add]; ring
        _ ≤ π * (1 / 2) * (64 * 4 ^ (m + J)) / (6 * 4 ^ (l * r) * 4 ^ r) := by gcongr
        _ = e * (4 ^ m * (8 * 4 ^ (J - l * r))) := by
          rw [← hpow l hl, he]; field_simp; ring
    have := Real.abs_cos_sub_cos_le (π * (ξ * F' (pt v) / 4 ^ m) / (8 * 4 ^ (J - l * r)))
      (π * u l v)
    simp only [g]
    have h3 := abs_abs_sub_abs_le_abs_sub (Real.cos (π * (ξ * F' (pt v) / 4 ^ m) /
      (8 * 4 ^ (J - l * r)))) (Real.cos (π * u l v))
    rw [show π * (ξ * F' (pt v) / 4 ^ m) / (8 * 4 ^ (J - l * r)) =
      π * (ξ * F' (pt v) / 4 ^ m / (8 * 4 ^ (J - l * r))) by ring] at this h3 key ⊢
    have := (abs_le.1 (h3.trans (this.trans key))).2
    linarith
  -- the block averaging hypotheses
  have hdep : ∀ l < L, ∀ v v', (∀ j : Fin m, (j : ℕ) < l * r + r → v j = v' j) →
      g l v = g l v' := by
    intro l _ v v' h
    simp only [g, u, trunc_congr h]
  have hflip : ∀ l < L, ∀ v (j : Fin m), (j : ℕ) = l * r →
      g l v + g l (flip j v) ≤ 2 * ((1 + Real.cos (π * (c / 2))) / 2 + e) := by
    intro l hl v j hj
    have htr : trunc (l * r + r) (flip j v) = flip j (trunc (l * r + r) v) := by
      have : (j : ℕ) < l * r + r := by omega
      rw [flip, trunc_update v j this, flip]
      simp [trunc, this]
    set t := trunc (l * r + r) v
    have hpd : |pt (flip j t) - pt t| = 1 / 8 / 4 ^ (j : ℕ) := abs_pt_flip t j
    set Δ := u l (flip j v) - u l v with hΔ
    have hΔeq : Δ = ξ * (F' (pt (flip j t)) - F' (pt t)) / (4 ^ m * (8 * 4 ^ (J - l * r))) := by
      simp only [hΔ, u, htr, t]; ring
    have h4 : (0 : ℝ) < 4 ^ m * (8 * 4 ^ (J - l * r)) := by positivity
    have hlowF : a * |pt (flip j t) - pt t| ≤ |F' (pt (flip j t)) - F' (pt t)| := by
      rcases lt_or_gt_of_ne (show pt (flip j t) ≠ pt t by
        intro h; rw [h, sub_self, abs_zero] at hpd
        have : (0 : ℝ) < 1 / 8 / 4 ^ (j : ℕ) := by positivity
        linarith) with h | h
      · have := deriv_sub_ge hF' hlo (pt_mem _) (pt_mem _) h
        rw [abs_of_neg (sub_neg.2 h), abs_of_neg (by nlinarith)]; linarith
      · have := deriv_sub_ge hF' hlo (pt_mem _) (pt_mem _) h
        rw [abs_of_pos (sub_pos.2 h), abs_of_pos (by nlinarith)]; linarith
    have hupF := abs_deriv_sub_le hF' hlo hhi ha.le (pt_mem t) (pt_mem (flip j t))
    have hscale : |ξ| * |pt (flip j t) - pt t| / (4 ^ m * (8 * 4 ^ (J - l * r))) = X := by
      rw [hpd, hXdef, ← hpow l hl, ← hj]; field_simp
    have hΔabs :
        |Δ| = |ξ| * |F' (pt (flip j t)) - F' (pt t)| / (4 ^ m * (8 * 4 ^ (J - l * r))) := by
      rw [hΔeq, abs_div, abs_mul, abs_of_pos h4]
    have hΔlo : c ≤ |Δ| := by
      have : a * X ≤ |Δ| := by
        rw [hΔabs, ← hscale]
        calc a * (|ξ| * |pt (flip j t) - pt t| / (4 ^ m * (8 * 4 ^ (J - l * r))))
            = |ξ| * (a * |pt (flip j t) - pt t|) / (4 ^ m * (8 * 4 ^ (J - l * r))) := by ring
          _ ≤ _ := by gcongr
      refine le_trans ?_ this
      rw [hc, div_le_iff₀ (by positivity)]
      nlinarith
    have hΔhi : |Δ| ≤ 1 - c := by
      have : |Δ| ≤ A * X := by
        rw [hΔabs, ← hscale]
        calc |ξ| * |F' (pt (flip j t)) - F' (pt t)| / (4 ^ m * (8 * 4 ^ (J - l * r)))
            ≤ |ξ| * (A * |pt (flip j t) - pt t|) / (4 ^ m * (8 * 4 ^ (J - l * r))) := by
              gcongr
          _ = _ := by ring
      linarith
    have := abs_cos_add_abs_cos_le (u l v) hc0 (by linarith) hΔlo hΔhi
    simp only [g]
    rw [show u l (flip j v) = u l v + Δ by rw [hΔ]; ring]
    linarith
  calc ∑ v : Fin m → Bool, ‖cantorFourier (ξ * F' (pt v) / 4 ^ m)‖
      ≤ ∑ v, ∏ l ∈ Finset.range L, g l v := Finset.sum_le_sum fun v _ => hdom v
    _ ≤ _ := sum_prod_le hr hLm g hg0 hdep hflip

end Averaging

section Decay

variable {F F' F'' : ℝ → ℝ} {a A : ℝ}
  (hF : ∀ t ∈ W, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ W, HasDerivAt F' (F'' t) t)
  (hlo : ∀ t ∈ W, a ≤ F'' t) (hhi : ∀ t ∈ W, F'' t ≤ A)

include hF hF' hlo hhi in
/-- **One scale.** Splitting into the `2^m` cylinders of depth `m`. -/
theorem norm_pushFourier_le_scale (hFm : Measurable F) (ha : 0 < a) {ξ : ℝ} {m J r L : ℕ}
    (hr : 0 < r) (hLm : L * r ≤ m) (hLJ : L * r ≤ J)
    (hX1 : 1 / 8 ≤ A * (|ξ| / (64 * 4 ^ (m + J))))
    (hX2 : A * (|ξ| / (64 * 4 ^ (m + J))) ≤ 1 / 2) :
    ‖pushFourier F ξ‖ ≤
      ((1 + Real.cos (π * (a / (8 * A) / 2))) / 2 + 2 * π / 3 / 4 ^ r) ^ L +
        2 * π * |ξ| * A / (4 * 16 ^ m) := by
  set ρ := (1 + Real.cos (π * (a / (8 * A) / 2))) / 2 + 2 * π / 3 / 4 ^ r
  set E := 2 * π * |ξ| * A / (4 * 16 ^ m)
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [pushFourier_cylinders m F hFm ξ, sum_words, norm_mul, norm_inv, norm_pow,
    Complex.norm_ofNat, inv_mul_le_iff₀ h2]
  have hsum := sum_norm_cantorFourier_le hF' hlo hhi ha hr hLm hLJ hX1 hX2
  calc ‖∑ v : Fin m → Bool, pushFourier (F ∘ phi (List.ofFn v)) ξ‖
      ≤ ∑ v : Fin m → Bool, ‖pushFourier (F ∘ phi (List.ofFn v)) ξ‖ := norm_sum_le _ _
    _ ≤ ∑ v : Fin m → Bool, (‖cantorFourier (ξ * F' (pt v) / 4 ^ m)‖ + E) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have := norm_pushFourier_phi_le hF hF' hlo hhi hFm ha.le (List.ofFn v) ξ
        rwa [List.length_ofFn, phi_ofFn] at this
    _ ≤ ρ ^ L * 2 ^ m + 2 ^ m * E := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        linarith
    _ = 2 ^ m * (ρ ^ L + E) := by ring

include hF hF' hlo hhi in
/-- **Kaufman-type polynomial Fourier decay** for the pushforward of the quarter-Cantor law
under a `C²` map with `0 < a ≤ F'' ≤ A` on the window. -/
theorem polyDecay (hFm : Measurable F) (ha : 0 < a) : PolyDecay F := by
  have hAa : a ≤ A := (hlo 1 ⟨by norm_num, le_rfl⟩).trans (hhi 1 ⟨by norm_num, le_rfl⟩)
  have hA : 0 < A := ha.trans_le hAa
  set ρ0 := (1 + Real.cos (π * (a / (8 * A) / 2))) / 2 with hρ0
  have hc0 : 0 < a / (8 * A) := by positivity
  have hc1 : a / (8 * A) ≤ 1 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hcos : Real.cos (π * (a / (8 * A) / 2)) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0)
      (show π * (a / (8 * A) / 2) ≤ π by nlinarith [Real.pi_pos])
      (show (0 : ℝ) < π * (a / (8 * A) / 2) by positivity)
    rwa [Real.cos_zero] at this
  have hρ01 : ρ0 < 1 := by rw [hρ0]; linarith
  have hρ00 : 0 ≤ ρ0 := by rw [hρ0]; linarith [Real.neg_one_le_cos (π * (a / (8 * A) / 2))]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 3 * (1 - ρ0) / (4 * π) by
    have := Real.pi_pos; apply div_pos <;> linarith) (show (1 / 4 : ℝ) < 1 by norm_num)
  set r := n + 1 with hrdef
  have hr : 0 < r := Nat.succ_pos n
  set e : ℝ := 2 * π / 3 / 4 ^ r with he
  have he1 : e ≤ (1 - ρ0) / 2 := by
    have h1 : (1 / 4 : ℝ) ^ r ≤ (1 / 4) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.le_succ n)
    have h2 : e = 2 * π / 3 * (1 / 4) ^ r := by rw [he, one_div_pow]; ring
    rw [h2]
    have := Real.pi_pos
    calc 2 * π / 3 * (1 / 4) ^ r ≤ 2 * π / 3 * (3 * (1 - ρ0) / (4 * π)) := by gcongr; linarith
      _ = (1 - ρ0) / 2 := by field_simp; ring
  have he0 : 0 ≤ e := by positivity
  set ρ := ρ0 + e with hρ
  set β : ℝ := max ρ (1 / 4) with hβ
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hβ1 : β < 1 := max_lt (by rw [hρ]; linarith) (by norm_num)
  set γ : ℝ := 4 ^ (3 * r) with hγ
  have hγ1 : 1 < γ := one_lt_pow₀ (by norm_num) (by omega)
  have hγ0 : 0 < γ := by positivity
  set K : ℝ := 16 * π * γ with hK
  have hK0 : 0 ≤ K := by positivity
  set δ : ℝ := -Real.log β / Real.log γ with hδ
  have hlγ : 0 < Real.log γ := Real.log_pos hγ1
  have hδ0 : 0 < δ := div_pos (neg_pos.2 (Real.log_neg hβ0 hβ1)) hlγ
  have hβγ : γ ^ (-δ) = β := by
    rw [Real.rpow_def_of_pos hγ0, hδ, show Real.log γ * -(-Real.log β / Real.log γ) =
      Real.log β by field_simp, Real.exp_log hβ0]
  set C1 := (1 + K) * (A / (32 * γ)) ^ (-δ)
  set C2 := (8 / A) ^ δ
  have hC1 : 0 < C1 := by positivity
  have hC2 : 0 < C2 := by positivity
  refine ⟨C1 + C2, δ, by positivity, hδ0, fun ξ hξ => ?_⟩
  have hξ0 : 0 < |ξ| := abs_pos.2 hξ
  have hpos : 0 ≤ |ξ| ^ (-δ) := by positivity
  by_cases hsmall : A * |ξ| / 8 < 1
  · have hlt : |ξ| ≤ 8 / A := by rw [le_div_iff₀ hA]; linarith
    have h1 : (8 / A) ^ (-δ) ≤ |ξ| ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hξ0 hlt (by linarith)
    have h2 : C2 * (8 / A) ^ (-δ) = 1 := by
      rw [Real.rpow_neg (by positivity), mul_inv_cancel₀ hC2.ne']
    calc ‖pushFourier F ξ‖ ≤ 1 := norm_pushFourier_le_one F ξ
      _ = C2 * (8 / A) ^ (-δ) := h2.symm
      _ ≤ C2 * |ξ| ^ (-δ) := by gcongr
      _ ≤ (C1 + C2) * |ξ| ^ (-δ) := by nlinarith
  push Not at hsmall
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near hsmall (by norm_num : (1 : ℝ) < 4)
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
  have h4N : (0 : ℝ) < 4 ^ N := by positivity
  have hX : A * (|ξ| / (64 * 4 ^ (m + J))) = A * |ξ| / 8 / (8 * 4 ^ N) := by
    rw [hmJ]; field_simp; ring
  have hX1 : 1 / 8 ≤ A * (|ξ| / (64 * 4 ^ (m + J))) := by
    rw [hX, le_div_iff₀ (by positivity)]; linarith
  have hX2 : A * (|ξ| / (64 * 4 ^ (m + J))) ≤ 1 / 2 := by
    rw [hX, div_le_iff₀ (by positivity)]; rw [pow_succ] at hN2; linarith
  have hscale := norm_pushFourier_le_scale hF hF' hlo hhi hFm ha hr hLm hLJ hX1 hX2
  have hAξ : A * |ξ| < 32 * 4 ^ N := by rw [pow_succ] at hN2; linarith
  -- the linearisation error
  have h16 : (16 : ℝ) ^ m = 4 ^ (2 * m) := by rw [pow_mul (4 : ℝ) 2 m]; norm_num
  have hpow : (4 : ℝ) ^ N * 4 ^ q ≤ 16 ^ m * γ := by
    rw [h16, hγ, ← pow_add, ← pow_add]; exact pow_le_pow_right₀ (by norm_num) hexp
  have hE : 2 * π * |ξ| * A / (4 * 16 ^ m) ≤ K * β ^ q := by
    have hq4 : (1 / 4 : ℝ) ^ q ≤ β ^ q := pow_le_pow_left₀ (by norm_num) (le_max_right _ _) q
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hq4 hK0)
    rw [one_div_pow, hK, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 2 * π * |ξ| * A * 4 ^ q = 2 * π * 4 ^ q * (A * |ξ|) := by ring
      _ ≤ 2 * π * 4 ^ q * (32 * 4 ^ N) := by gcongr
      _ = 64 * π * (4 ^ N * 4 ^ q) := by ring
      _ ≤ 64 * π * (16 ^ m * γ) := by gcongr
      _ = 16 * π * γ * (4 * 16 ^ m) := by ring
  have hρq : (ρ0 + e) ^ q ≤ β ^ q := pow_le_pow_left₀ (by linarith) (le_max_left _ _) q
  have hmain : ‖pushFourier F ξ‖ ≤ (1 + K) * β ^ q := by
    have := hscale.trans (add_le_add hρq hE); linarith
  -- converting the scale back to `|ξ|`
  have hγq : A * |ξ| / (32 * γ) ≤ γ ^ q := by
    rw [div_le_iff₀ (by positivity)]
    have : (4 : ℝ) ^ N ≤ γ ^ (q + 1) := by
      rw [hγ, ← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by linarith [hNq])
    rw [pow_succ] at this; nlinarith
  have hβq : β ^ q ≤ (A / (32 * γ)) ^ (-δ) * |ξ| ^ (-δ) := by
    rw [← hβγ, ← Real.rpow_natCast, ← Real.rpow_mul hγ0.le, mul_comm, Real.rpow_mul hγ0.le,
      Real.rpow_natCast, ← Real.mul_rpow (by positivity) hξ0.le]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [show A / (32 * γ) * |ξ| = A * |ξ| / (32 * γ) by ring]; exact hγq
  calc ‖pushFourier F ξ‖ ≤ (1 + K) * β ^ q := hmain
    _ ≤ (1 + K) * ((A / (32 * γ)) ^ (-δ) * |ξ| ^ (-δ)) := by gcongr
    _ = C1 * |ξ| ^ (-δ) := by ring
    _ ≤ (C1 + C2) * |ξ| ^ (-δ) := by nlinarith

end Decay

end NormalNumbers.QuarterCantorDecay
