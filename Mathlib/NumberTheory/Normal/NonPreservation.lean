/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.NormalNumbers.CantorLiouvilleAll
public import Mathlib.Imported.NormalNumbers.VisitDeviationB
public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Bridge
public import Mathlib.NumberTheory.Normal.BaseCantorDecay
public import Mathlib.NumberTheory.Normal.QuarterCantorDecay

/-!
# Squaring, inversion, the exponential and Möbius maps do not preserve normality

Let `y` run over the quarter-Cantor set (`NormalNumbers.CantorSelfSimilar.cantorReal`): its
base-`4` digits are all `1` or `2`, so `y` is not normal in any base `2 ^ k`. For `G` one of
`√`, `x ↦ x⁻¹`, `log`, the second derivative of `G` is bounded away from `0` on `[1/2, 1]`, so the
pushforward of the quarter-Cantor law under `G` has polynomial Fourier decay
(`NormalNumbers.QuarterCantorDecay.polyDecay`), and almost every `x = G y` is absolutely normal
(Davenport–Erdős–LeVeque in every base). Then `x` is absolutely normal while `x ^ 2 = y`,
`x⁻¹ = y`, or `exp x = y` is not normal in base `2 ^ k`. For a base `b ≥ 3` the same argument
runs on the base-`b` Cantor measure (`NormalNumbers.BaseCantorDecay`), whose points (shifted by
`1`) have no digit `2`.

## Main statements

* `NormalNumbers.QuarterCantorDecay.ae_isAbsolutelyNormal_of_polyDecay`
* `NormalNumbers.QuarterCantorDecay.polyDecay_sqrt`, `polyDecay_inv`, `polyDecay_log`
* `NormalNumbers.QuarterCantorDecay.exists_computable_isNormal_sqrt`: an unconditional computable
  witness for the `√` case of Manai's Theorem 2.
* `Real.exists_isAbsolutelyNormal_not_isAbsolutelyNormal_sq`, `..._inv`, `..._exp`
* `Real.exists_isNormalIn_two_pow_not_isNormalIn_sq`, `..._inv`, `..._exp`: bases `b = 2 ^ k`
* `Real.exists_isNormalIn_not_isNormalIn_sq`, `..._inv`, `..._exp`, `..._mobius`: every base
  `b ≥ 2`, using the base-`b` Cantor measure of `NormalNumbers.BaseCantorDecay` for `b ≥ 3`
* `Real.exists_isAbsolutelyNormal_not_isAbsolutelyNormal_mobius` and
  `Real.exists_isNormalIn_two_pow_not_isNormalIn_mobius`: Möbius maps with `c ≠ 0`

## References

* R. Kaufman, *On the theorem of Jarník and Besicovitch*, Acta Arith. 39 (1981).
* C. A. Mosquera, P. S. Shmerkin, *Self-similar measures: asymptotic bounds for the dimension and
  Fourier decay of smooth images*, Ann. Acad. Sci. Fenn. Math. 43 (2018).
* M. Manai, arXiv:2609.24665, Theorem 2.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology

namespace NormalNumbers.QuarterCantorDecay

open ExplicitSquare CantorSelfSimilar DecayAeNormal

/-- Decay is invariant under `F ↦ -F`. -/
theorem PolyDecay.of_neg {F : ℝ → ℝ} (h : PolyDecay fun t => -F t) : PolyDecay F := by
  obtain ⟨C, δ, hC, hδ, hd⟩ := h
  refine ⟨C, δ, hC, hδ, fun ξ hξ => ?_⟩
  have := hd (-ξ) (neg_ne_zero.2 hξ)
  rw [abs_neg] at this
  refine le_trans (le_of_eq ?_) this
  unfold pushFourier
  congr 2; funext ω; congr 3; push_cast; ring

/-- **Polynomial decay ⇒ a.s. normality in base `b`**: Davenport–Erdős–LeVeque along `(j+1)²`. -/
theorem ae_isNormal_of_decay_b {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {b : ℕ} (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ)) :
    ∀ᵐ ω ∂μ, IsNormal b (G ω) := by
  refine CantorLiouvilleAll.ae_isNormal_of_secondMoment μ hb G hG (fun j => (j + 1) ^ 2)
    (fun i j hij => Nat.pow_lt_pow_left (by omega) (by norm_num)) ?_ ?_
  · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have : Tendsto (fun j : ℕ => (1 + 1 / ((j : ℝ) + 1)) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
      ((tendsto_const_nhds.add h0).pow 2)
    rw [add_zero, one_pow] at this
    refine this.congr fun j => ?_
    push_cast
    field_simp
  · intro h hh
    set K := C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2
    have hK : 0 ≤ K := by
      have : (2 : ℝ) ^ (-δ / 2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have : 0 < 1 - (2 : ℝ) ^ (-δ / 2) := by linarith
      positivity
    have hs : Summable fun j : ℕ => (1 + K) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) :=
      ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left _
    refine hs.of_nonneg_of_le (fun j => div_nonneg (integral_nonneg fun ω => by positivity)
      (by positivity)) fun j => ?_
    have hN : (1 : ℝ) ≤ (((j + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
    have hm := VisitDeviationB.second_moment_le_b μ b hb G hG hC hδ hdec h hh ((j + 1) ^ 2)
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ (((j + 1) ^ 2 : ℕ) : ℝ) + K := hm
      _ ≤ (1 + K) * (((j + 1) ^ 2 : ℕ) : ℝ) := by nlinarith
      _ = (1 + K) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) * ((((j + 1) ^ 2 : ℕ) : ℝ)) ^ 2 := by
        push_cast; field_simp

/-- **Polynomial decay ⇒ `F(y)` is absolutely normal for almost every quarter-Cantor `y`.** -/
theorem ae_isAbsolutelyNormal_of_polyDecay {F : ℝ → ℝ} (hF : Measurable F) (hd : PolyDecay F) :
    ∀ᵐ ω ∂coinMeasure, Real.IsAbsolutelyNormal (F (cantorReal ω)) := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := hd
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → IsNormal b (F (cantorReal ω)) := by
    rw [ae_all_iff]; intro b
    by_cases hb : 2 ≤ b
    · filter_upwards [ae_isNormal_of_decay_b coinMeasure hb _ (hF.comp measurable_cantorReal)
        hC hδ hdec] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hb
  filter_upwards [hall] with ω hω b hb
  exact (Real.isNormalIn_iff_isNormal b _).2 (hω b hb)

/-- Quarter-Cantor points are not normal in any base `2 ^ k`. -/
theorem not_isNormalIn_two_pow_cantorReal (ω : ℕ → Bool) {k : ℕ} (hk : 0 < k) :
    ¬ Real.IsNormalIn (2 ^ k) (cantorReal ω) := fun h =>
  not_isNormal_cantorReal ω ((Real.isNormalIn_iff_isNormal 2 _).1 (h.of_pow le_rfl hk))

/-- **Decay for `0 < a ≤ |G''| ≤ A`** on the window, `G''` of constant sign. -/
theorem polyDecay_of_abs {G G' G'' : ℝ → ℝ} {a A : ℝ} (ha : 0 < a) (hGm : Measurable G)
    (hG : ∀ t ∈ W, HasDerivAt G (G' t) t) (hG' : ∀ t ∈ W, HasDerivAt G' (G'' t) t)
    (hlo : ∀ t ∈ W, a ≤ |G'' t|) (hhi : ∀ t ∈ W, |G'' t| ≤ A)
    (hsign : (∀ t ∈ W, 0 < G'' t) ∨ ∀ t ∈ W, G'' t < 0) : PolyDecay G := by
  rcases hsign with hs | hs
  · refine polyDecay hG hG' (a := a) (A := A) (fun t ht => ?_) (fun t ht => ?_) hGm ha
    · simpa [abs_of_pos (hs t ht)] using hlo t ht
    · exact (le_abs_self _).trans (hhi t ht)
  · refine PolyDecay.of_neg (polyDecay (F' := fun t => -G' t) (F'' := fun t => -G'' t)
      (a := a) (A := A) (fun t ht => (hG t ht).neg) (fun t ht => (hG' t ht).neg)
      (fun t ht => ?_) (fun t ht => ?_) hGm.neg ha)
    · simpa [abs_of_neg (hs t ht)] using hlo t ht
    · exact (neg_le_abs _).trans (hhi t ht)

theorem pos_of_mem_W {t : ℝ} (ht : t ∈ W) : 0 < t := lt_of_lt_of_le (by norm_num) ht.1

/-- **`√` has polynomial decay**: this proves the `√` case of `BakerBanajiQuarterCantor`. -/
theorem polyDecay_sqrt : PolyDecay Real.sqrt := by
  have hd : ∀ t ∈ W, HasDerivAt (fun s => (2 * Real.sqrt s)⁻¹)
      (-(2 * (2 * Real.sqrt t)⁻¹) / (2 * Real.sqrt t) ^ 2) t := fun t ht =>
    (((Real.hasDerivAt_sqrt (pos_of_mem_W ht).ne').const_mul 2).congr_deriv
      (by rw [one_div])).inv (by positivity [Real.sqrt_pos.2 (pos_of_mem_W ht)])
  have heq : ∀ t ∈ W, -(2 * (2 * Real.sqrt t)⁻¹) / (2 * Real.sqrt t) ^ 2 =
      -(1 / (4 * Real.sqrt t ^ 3)) := fun t ht => by
    have := Real.sqrt_pos.2 (pos_of_mem_W ht); field_simp; ring
  have hs : ∀ t ∈ W, 1 / 2 ≤ Real.sqrt t ∧ Real.sqrt t ≤ 1 := fun t ht =>
    ⟨Real.le_sqrt_of_sq_le (by nlinarith [ht.1]), Real.sqrt_le_one.2 ht.2⟩
  refine polyDecay_of_abs (a := 1 / 4) (A := 2) (by norm_num)
    Real.continuous_sqrt.measurable
    (fun t ht => ((Real.hasDerivAt_sqrt (pos_of_mem_W ht).ne').congr_deriv (by rw [one_div])))
    hd (fun t ht => ?_) (fun t ht => ?_) (Or.inr fun t ht => ?_)
  · rw [heq t ht, abs_neg, abs_of_pos (by have := (hs t ht).1; positivity),
      le_div_iff₀ (by have := (hs t ht).1; positivity)]
    have := (hs t ht).2; have := (hs t ht).1
    nlinarith [pow_le_one₀ (by linarith) (hs t ht).2 (n := 3)]
  · rw [heq t ht, abs_neg, abs_of_pos (by have := (hs t ht).1; positivity),
      div_le_iff₀ (by have := (hs t ht).1; positivity)]
    have h1 := (hs t ht).1
    nlinarith [pow_le_pow_left₀ (by norm_num) h1 3]
  · rw [heq t ht, neg_neg_iff_pos]; have := (hs t ht).1; positivity

theorem polyDecay_inv : PolyDecay fun t => t⁻¹ := by
  refine polyDecay_of_abs (G := fun t => t⁻¹) (G' := fun t => -(t ^ 2)⁻¹)
    (G'' := fun t => 2 / t ^ 3) (a := 2) (A := 16) (by norm_num) measurable_inv
    (fun t ht => hasDerivAt_inv (pos_of_mem_W ht).ne')
    (fun t ht => ((hasDerivAt_pow 2 t).inv (by have := pos_of_mem_W ht; positivity)).neg.congr_deriv
      (by have := pos_of_mem_W ht; field_simp; ring)) (fun t ht => ?_) (fun t ht => ?_)
    (Or.inl fun t ht => by have := pos_of_mem_W ht; positivity)
  · have := pos_of_mem_W ht
    rw [abs_of_pos (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [pow_le_one₀ this.le ht.2 (n := 3)]
  · have := pos_of_mem_W ht
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num) ht.1 3]

theorem polyDecay_log : PolyDecay Real.log := by
  refine polyDecay_of_abs (G' := fun t => t⁻¹) (G'' := fun t => -(t ^ 2)⁻¹)
    (a := 1) (A := 4) one_pos Real.measurable_log
    (fun t ht => Real.hasDerivAt_log (pos_of_mem_W ht).ne')
    (fun t ht => hasDerivAt_inv (pos_of_mem_W ht).ne') (fun t ht => ?_) (fun t ht => ?_)
    (Or.inr fun t ht => by have := pos_of_mem_W ht; simp only [neg_neg_iff_pos]; positivity)
  · have := pos_of_mem_W ht
    rw [abs_neg, abs_of_pos (by positivity), ← one_div, le_div_iff₀ (by positivity)]
    nlinarith [ht.2]
  · have := pos_of_mem_W ht
    rw [abs_neg, abs_of_pos (by positivity), ← one_div, div_le_iff₀ (by positivity)]
    nlinarith [ht.1]

/-- An unconditional computable quarter-Cantor `y` with `√y` normal in base 2 (Manai
2609.24665, Theorem 2, the `√` case), via
`ExplicitSquare.exists_computable_isNormal_sqrt_of_polyDecay`. -/
theorem exists_computable_isNormal_sqrt :
    ∃ e : ℕ → Bool, Computable e ∧ IsNormal 2 (Real.sqrt (cantorReal e)) :=
  exists_computable_isNormal_sqrt_of_polyDecay polyDecay_sqrt

/-- The common witness: an absolutely normal `x = G y` with `H x = y` quarter-Cantor. -/
theorem exists_of_ae {G H : ℝ → ℝ}
    (hae : ∀ᵐ ω ∂coinMeasure, Real.IsAbsolutelyNormal (G (cantorReal ω)))
    (hHG : ∀ t ∈ W, H (G t) = t) :
    ∃ x : ℝ, Real.IsAbsolutelyNormal x ∧ ∀ k : ℕ, 0 < k → ¬ Real.IsNormalIn (2 ^ k) (H x) := by
  obtain ⟨ω, hω⟩ := hae.exists
  refine ⟨_, hω, fun k hk => ?_⟩
  rw [hHG _ (cantorReal_mem_window ω)]
  exact not_isNormalIn_two_pow_cantorReal ω hk

/-- **Möbius maps.** For `c ≠ 0` and nonzero determinant there is an absolutely normal `x`
whose Möbius image is a quarter-Cantor point plus an integer. -/
theorem exists_isAbsolutelyNormal_mobius (a₁ a₂ c d : ℝ) (hc : c ≠ 0)
    (hdet : a₁ * d - a₂ * c ≠ 0) : ∃ x : ℝ, Real.IsAbsolutelyNormal x ∧
      ∃ ω : ℕ → Bool, ∃ r : ℤ, (a₁ * x + a₂) / (c * x + d) = cantorReal ω + r := by
  set s := a₁ / c
  set r : ℤ := ⌈|s|⌉ + 2
  set t : ℝ := r - s with htdef
  have ht : 2 ≤ t := by
    have h1 : |s| ≤ (⌈|s|⌉ : ℝ) := Int.le_ceil _
    have h2 : s ≤ |s| := le_abs_self s
    simp only [htdef, r]; push_cast; linarith
  set E : ℝ := (a₁ * d - a₂ * c) / c ^ 2 with hEdef
  have hE : E ≠ 0 := div_ne_zero hdet (pow_ne_zero 2 hc)
  have hEa : 0 < |E| := abs_pos.2 hE
  set G : ℝ → ℝ := fun y => -d / c - E * (y + t)⁻¹ with hGdef
  have hv : ∀ y ∈ W, 2 ≤ y + t ∧ y + t ≤ t + 1 := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hvpos : ∀ y ∈ W, 0 < y + t := fun y hy => by linarith [(hv y hy).1]
  have hd : PolyDecay G := by
    refine polyDecay_of_abs (G' := fun y => E * ((y + t) ^ 2)⁻¹)
      (G'' := fun y => -(2 * E) / (y + t) ^ 3) (a := 2 * |E| / (t + 1) ^ 3) (A := 2 * |E| / 8)
      (by positivity)
      (measurable_const.sub (measurable_const.mul (measurable_id.add_const t).inv))
      (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) ?_
    · have h0 := (hvpos y hy).ne'
      exact ((((hasDerivAt_id' y).add_const t).inv h0).const_mul E).const_sub (-d / c)
        |>.congr_deriv (by field_simp)
    · have h0 := (hvpos y hy).ne'
      exact (((((hasDerivAt_id' y).add_const t).fun_pow 2).inv (pow_ne_zero 2 h0)).const_mul E)
        |>.congr_deriv (by field_simp; ring)
    · have h0 := hvpos y hy
      rw [neg_div, abs_neg, abs_div (2 * E), abs_mul, abs_two,
        abs_of_pos (by positivity : (0 : ℝ) < (y + t) ^ 3)]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ h0.le (hv y hy).2 3)
    · have h0 := hvpos y hy
      rw [neg_div, abs_neg, abs_div (2 * E), abs_mul, abs_two,
        abs_of_pos (by positivity : (0 : ℝ) < (y + t) ^ 3)]
      gcongr
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ (y + t) ^ 3 := pow_le_pow_left₀ (by norm_num) (hv y hy).1 3
    · rcases lt_or_gt_of_ne hE with h | h
      · exact Or.inl fun y hy => by have := hvpos y hy; apply div_pos (by linarith); positivity
      · exact Or.inr fun y hy => by
          have := hvpos y hy; apply div_neg_of_neg_of_pos (by linarith); positivity
  have hGm : Measurable G :=
    measurable_const.sub (measurable_const.mul (measurable_id.add_const t).inv)
  obtain ⟨ω, hω⟩ := (ae_isAbsolutelyNormal_of_polyDecay hGm hd).exists
  refine ⟨G (cantorReal ω), hω, ω, r, ?_⟩
  have hy := cantorReal_mem_window ω
  have hyr : cantorReal ω + (r : ℝ) = (cantorReal ω + t) + a₁ / c := by rw [htdef]; ring
  have h0 : cantorReal ω + t ≠ 0 := (hvpos _ hy).ne'
  rw [hyr, hGdef]
  simp only
  generalize cantorReal ω + t = v at h0 ⊢
  have hden : c * (-d / c - E * v⁻¹) + d = -(c * E) / v := by field_simp; ring
  rw [div_eq_iff (by rw [hden]; exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero hc hE)) h0), hEdef]
  field_simp
  ring

end NormalNumbers.QuarterCantorDecay

namespace Real

open NormalNumbers.QuarterCantorDecay

/-- An absolutely normal number whose square is not normal in any base `2 ^ k`. -/
theorem exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_sq :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ∀ k : ℕ, 0 < k → ¬ IsNormalIn (2 ^ k) (x ^ 2) :=
  exists_of_ae (ae_isAbsolutelyNormal_of_polyDecay Real.continuous_sqrt.measurable polyDecay_sqrt)
    fun _ ht => Real.sq_sqrt (pos_of_mem_W ht).le

/-- An absolutely normal number whose inverse is not normal in any base `2 ^ k`. -/
theorem exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_inv :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ∀ k : ℕ, 0 < k → ¬ IsNormalIn (2 ^ k) x⁻¹ :=
  exists_of_ae (H := fun x => x⁻¹)
    (ae_isAbsolutelyNormal_of_polyDecay (F := fun t => t⁻¹) measurable_inv polyDecay_inv)
    fun t _ => inv_inv t

/-- An absolutely normal number whose exponential is not normal in any base `2 ^ k`. -/
theorem exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_exp :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ∀ k : ℕ, 0 < k → ¬ IsNormalIn (2 ^ k) (Real.exp x) :=
  exists_of_ae (ae_isAbsolutelyNormal_of_polyDecay Real.measurable_log polyDecay_log)
    fun _ ht => Real.exp_log (pos_of_mem_W ht)

private lemma two_le_two_pow {k : ℕ} (hk : 0 < k) : 2 ≤ 2 ^ k :=
  le_self_pow₀ (by norm_num) hk.ne'

/-- Squaring does not preserve absolute normality. -/
theorem exists_isAbsolutelyNormal_not_isAbsolutelyNormal_sq :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsAbsolutelyNormal (x ^ 2) := by
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_sq
  exact ⟨x, hx, fun h' => h 1 one_pos (by simpa using h' 2 le_rfl)⟩

/-- Inversion does not preserve absolute normality. -/
theorem exists_isAbsolutelyNormal_not_isAbsolutelyNormal_inv :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsAbsolutelyNormal x⁻¹ := by
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_inv
  exact ⟨x, hx, fun h' => h 1 one_pos (by simpa using h' 2 le_rfl)⟩

/-- The exponential does not preserve absolute normality. -/
theorem exists_isAbsolutelyNormal_not_isAbsolutelyNormal_exp :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsAbsolutelyNormal (Real.exp x) := by
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_exp
  exact ⟨x, hx, fun h' => h 1 one_pos (by simpa using h' 2 le_rfl)⟩

/-- Squaring does not preserve normality in base `2 ^ k`. -/
theorem exists_isNormalIn_two_pow_not_isNormalIn_sq {k : ℕ} (hk : 0 < k) :
    ∃ x : ℝ, IsNormalIn (2 ^ k) x ∧ ¬ IsNormalIn (2 ^ k) (x ^ 2) := by
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_sq
  exact ⟨x, hx _ (two_le_two_pow hk), h k hk⟩

/-- Inversion does not preserve normality in base `2 ^ k`. -/
theorem exists_isNormalIn_two_pow_not_isNormalIn_inv {k : ℕ} (hk : 0 < k) :
    ∃ x : ℝ, IsNormalIn (2 ^ k) x ∧ ¬ IsNormalIn (2 ^ k) x⁻¹ := by
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_inv
  exact ⟨x, hx _ (two_le_two_pow hk), h k hk⟩

/-- The exponential does not preserve normality in base `2 ^ k`. -/
theorem exists_isNormalIn_two_pow_not_isNormalIn_exp {k : ℕ} (hk : 0 < k) :
    ∃ x : ℝ, IsNormalIn (2 ^ k) x ∧ ¬ IsNormalIn (2 ^ k) (Real.exp x) := by
  obtain ⟨x, hx, h⟩ := exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_exp
  exact ⟨x, hx _ (two_le_two_pow hk), h k hk⟩

/-- An absolutely normal number whose image under a Möbius map with `c ≠ 0` is not normal in any
base `2 ^ k`. -/
theorem exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_mobius (a₁ a₂ c d : ℝ) (hc : c ≠ 0)
    (hdet : a₁ * d - a₂ * c ≠ 0) : ∃ x : ℝ, IsAbsolutelyNormal x ∧
      ∀ k : ℕ, 0 < k → ¬ IsNormalIn (2 ^ k) ((a₁ * x + a₂) / (c * x + d)) := by
  obtain ⟨x, hx, ω, r, he⟩ := exists_isAbsolutelyNormal_mobius a₁ a₂ c d hc hdet
  refine ⟨x, hx, fun k hk h => ?_⟩
  rw [he, isNormalIn_add_intCast_iff] at h
  exact not_isNormalIn_two_pow_cantorReal ω hk h

/-- No Möbius map with `c ≠ 0` preserves absolute normality. -/
theorem exists_isAbsolutelyNormal_not_isAbsolutelyNormal_mobius (a₁ a₂ c d : ℝ) (hc : c ≠ 0)
    (hdet : a₁ * d - a₂ * c ≠ 0) :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsAbsolutelyNormal ((a₁ * x + a₂) / (c * x + d)) := by
  obtain ⟨x, hx, h⟩ :=
    exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_mobius a₁ a₂ c d hc hdet
  exact ⟨x, hx, fun h' => h 1 one_pos (by simpa using h' 2 le_rfl)⟩

/-- No Möbius map with `c ≠ 0` preserves normality in base `2 ^ k`. -/
theorem exists_isNormalIn_two_pow_not_isNormalIn_mobius {k : ℕ} (hk : 0 < k) (a₁ a₂ c d : ℝ)
    (hc : c ≠ 0) (hdet : a₁ * d - a₂ * c ≠ 0) :
    ∃ x : ℝ, IsNormalIn (2 ^ k) x ∧ ¬ IsNormalIn (2 ^ k) ((a₁ * x + a₂) / (c * x + d)) := by
  obtain ⟨x, hx, h⟩ :=
    exists_isAbsolutelyNormal_forall_not_isNormalIn_two_pow_mobius a₁ a₂ c d hc hdet
  exact ⟨x, hx _ (two_le_two_pow hk), h k hk⟩

/-! ### General bases -/

open NormalNumbers.BaseCantorDecay

/-- An absolutely normal number whose square is not normal in base `b`. -/
theorem exists_isAbsolutelyNormal_not_isNormalIn_sq {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsNormalIn b (x ^ 2) := by
  sorry

/-- An absolutely normal number whose inverse is not normal in base `b`. -/
theorem exists_isAbsolutelyNormal_not_isNormalIn_inv {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsNormalIn b x⁻¹ := by
  sorry

/-- An absolutely normal number whose exponential is not normal in base `b`. -/
theorem exists_isAbsolutelyNormal_not_isNormalIn_exp {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsNormalIn b (Real.exp x) := by
  sorry

/-- An absolutely normal number whose Möbius image (`c ≠ 0`) is not normal in base `b`. -/
theorem exists_isAbsolutelyNormal_not_isNormalIn_mobius {b : ℕ} (hb : 2 ≤ b) (a₁ a₂ c d : ℝ)
    (hc : c ≠ 0) (hdet : a₁ * d - a₂ * c ≠ 0) :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ ¬ IsNormalIn b ((a₁ * x + a₂) / (c * x + d)) := by
  sorry

/-- Squaring does not preserve base-`b` normality (`b ≥ 2`). -/
theorem exists_isNormalIn_not_isNormalIn_sq {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b (x ^ 2) := by
  sorry

/-- Inversion does not preserve base-`b` normality (`b ≥ 2`). -/
theorem exists_isNormalIn_not_isNormalIn_inv {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b x⁻¹ := by
  sorry

/-- The exponential does not preserve base-`b` normality (`b ≥ 2`). -/
theorem exists_isNormalIn_not_isNormalIn_exp {b : ℕ} (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b (Real.exp x) := by
  sorry

/-- No Möbius map with `c ≠ 0` preserves base-`b` normality (`b ≥ 2`). -/
theorem exists_isNormalIn_not_isNormalIn_mobius {b : ℕ} (hb : 2 ≤ b) (a₁ a₂ c d : ℝ)
    (hc : c ≠ 0) (hdet : a₁ * d - a₂ * c ≠ 0) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b ((a₁ * x + a₂) / (c * x + d)) := by
  sorry

end Real
