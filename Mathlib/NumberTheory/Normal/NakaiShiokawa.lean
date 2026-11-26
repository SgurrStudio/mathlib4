/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.DavenportErdos

import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Imported.TauCeti.Analysis.Polynomial.L1Norm
import Mathlib.Topology.Algebra.Order.Polynomial

/-!
# The Nakai–Shiokawa theorem

Let `f` be a non-constant polynomial with real coefficients taking positive values at the
positive integers. **Nakai and Shiokawa** proved that the number `0.⌊f(1)⌋ ⌊f(2)⌋ ⌊f(3)⌋ …`,
obtained by concatenating the base-`b` expansions of the integer parts `⌊f(n)⌋`, is normal in
base `b`. For integer polynomials this is the Davenport–Erdős theorem
(`Real.isNormalIn_concatenation_polynomial`).

## Main statements

* `Real.isNormalIn_concatenation_floor_polynomial`: the Nakai–Shiokawa theorem.

## Proof

We reuse the Davenport–Erdős assembly `Real.isNormalIn_concatenation_of_growth`. The only new
point is the Weyl sum of `⌊f(t)⌋ / b ^ (s + k)`: it differs from that of `f(t) / b ^ (s + k)`
by at most `2 π h T / b ^ (s + k)`, which is `o(T)` at the positions `s` that matter, and the
latter is `o(T)` by the `d`-th difference test (`Polynomial.eventually_norm_polyExpSum_le`),
which already allows a real leading coefficient.

## References

* [Y. Nakai, I. Shiokawa, *Discrepancy estimates for a class of normal numbers*][NakaiShiokawa1992]
-/

@[expose] public section

open Polynomial Filter Topology Finset

namespace Real

/-- **The Nakai–Shiokawa theorem**: if `f` is a non-constant real polynomial with `f(n) > 0` for
all `n ≥ 1`, then `0.⌊f(1)⌋ ⌊f(2)⌋ ⌊f(3)⌋ …` is normal in every base `b ≥ 2`. -/
theorem isNormalIn_concatenation_floor_polynomial {b : ℕ} [NeZero b] (hb : 2 ≤ b) {f : ℝ[X]}
    (hf : 0 < f.natDegree) (hpos : ∀ n : ℕ, 0 < f.eval ((n : ℝ) + 1)) :
    IsNormalIn b (concatenation b fun n ↦ ⌊f.eval ((n : ℝ) + 1)⌋₊) := by
  set a : ℕ → ℕ := fun n ↦ ⌊f.eval ((n : ℝ) + 1)⌋₊ with ha
  set d := f.natDegree with hd
  set α := f.leadingCoeff with hα
  have hshift : Tendsto (fun t : ℕ ↦ (t : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  -- the leading coefficient is positive
  have hα0 : 0 < α := by
    by_contra h
    push Not at h
    have hbot := tendsto_atBot_of_leadingCoeff_nonpos (natDegree_pos_iff_degree_pos.1 hf) h
    obtain ⟨t, ht⟩ := (hshift.eventually (hbot.eventually (eventually_lt_atBot 0))).exists
    exact (hpos t).not_gt ht
  have hfl : ∀ t : ℕ, (a t : ℝ) ≤ f.eval ((t : ℝ) + 1) ∧ f.eval ((t : ℝ) + 1) < a t + 1 :=
    fun t ↦ ⟨Nat.floor_le (hpos t).le, Nat.lt_floor_add_one _⟩
  set A : ℝ := max α 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  have hαA : α ≤ A := le_max_left _ _
  -- upper bound
  set M : ℕ := ⌈f.l1Norm⌉₊ + 1
  have hup : ∀ t, a t ≤ M * (t + 1) ^ d := fun t ↦ by
    have h := norm_eval_le_l1Norm_mul f ((t : ℝ) + 1)
    have hz : ‖(t : ℝ) + 1‖ = t + 1 := Real.norm_of_nonneg (by positivity)
    rw [Real.norm_of_nonneg (hpos t).le, hz,
      max_eq_right (by linarith [t.cast_nonneg' (α := ℝ)])] at h
    have h2 : f.l1Norm ≤ M := by
      simp only [M]; push_cast; linarith [Nat.le_ceil f.l1Norm]
    have : (a t : ℝ) ≤ M * ((t : ℝ) + 1) ^ d := (hfl t).1.trans (h.trans (by gcongr))
    exact_mod_cast this
  -- lower bound
  have hlow : ∀ᶠ t : ℕ in atTop, α / 4 * ((t : ℝ) + 1) ^ d ≤ a t := by
    have h := (isEquivalent_atTop_lead f).isLittleO.def (by norm_num : (0 : ℝ) < 1 / 2)
    have hbig : ∀ᶠ t : ℕ in atTop, 4 / α ≤ (t : ℝ) + 1 := hshift.eventually (eventually_ge_atTop _)
    filter_upwards [hshift.eventually h, hbig] with t ht ht'
    simp only [Pi.sub_apply, Real.norm_eq_abs] at ht
    have hv : 0 ≤ α * ((t : ℝ) + 1) ^ d := by positivity
    rw [abs_of_nonneg hv, abs_le] at ht
    have h1 : (t : ℝ) + 1 ≤ ((t : ℝ) + 1) ^ d :=
      le_self_pow₀ (by linarith [t.cast_nonneg' (α := ℝ)]) hf.ne'
    have h4 : 1 ≤ α / 4 * ((t : ℝ) + 1) ^ d := by
      rw [div_le_iff₀ hα0] at ht'
      nlinarith
    linarith [ht.1, (hfl t).2]
  refine isNormalIn_concatenation_of_growth hb hf hA1 (by omega) hup (by positivity) hlow ?_
  intro k hk δ hδ ε hε
  have hrp : ∀ {r : ℝ}, 0 < r → ∀ C : ℝ, ∀ᶠ T : ℕ in atTop, C ≤ (T : ℝ) ^ r := fun hr C ↦
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop C)
  filter_upwards [Polynomial.eventually_norm_polyExpSum_le (d := d) hf (half_pos hδ)
    (half_pos hε), hrp (half_pos hδ) (A / α), hrp hδ (4 * π / ε), eventually_ge_atTop 1]
    with T hT hTA hTε hT1 s h hh h1 h2
  rw [mem_Ico] at hh
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  set B : ℝ := (b : ℝ) ^ (s + k) with hB
  have hB0 : 0 < B := by positivity
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh.1
  have hhK : (h : ℝ) ≤ (b : ℝ) ^ k := by exact_mod_cast hh.2.le
  -- `h / B ≤ T ^ (-δ)`
  have hhB : (h : ℝ) / B ≤ (T : ℝ) ^ (-δ) := by
    refine le_trans ?_ h2
    rw [mul_div_assoc]
    calc (h : ℝ) / B = h * (1 / B) := by ring
      _ ≤ (b : ℝ) ^ k * (A / B) := by gcongr
  set φ : ℝ[X] := C ((h : ℝ) / B) * f.comp (X + C 1) with hφ
  have hcd : (f.comp (X + C 1)).natDegree = d := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hcl : (f.comp (X + C 1)).coeff d = α := by
    conv_lhs => rw [← hcd]
    change leadingCoeff _ = _
    rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; norm_num), leadingCoeff_X_add_C, one_pow,
      mul_one]
  have hφd : φ.natDegree ≤ d := (natDegree_C_mul_le _ _).trans hcd.le
  have hφc : φ.coeff d = (h : ℝ) / B * α := by rw [hφ, coeff_C_mul, hcl]
  have hφT := hT φ hφd (by
      rw [hφc]
      have e : (T : ℝ) ^ (δ / 2 - d) * (A / α) ≤ (T : ℝ) ^ (δ - d) := by
        calc (T : ℝ) ^ (δ / 2 - d) * (A / α) ≤ (T : ℝ) ^ (δ / 2 - d) * (T : ℝ) ^ (δ / 2) := by
              gcongr
          _ = _ := by rw [← rpow_add hT0]; ring_nf
      have e3 : (T : ℝ) ^ (δ / 2 - d) * A ≤ A / B * α := by
        have := mul_le_mul_of_nonneg_right (e.trans h1) hα0.le
        rwa [mul_assoc, div_mul_cancel₀ _ hα0.ne'] at this
      calc (T : ℝ) ^ (δ / 2 - d) = (T : ℝ) ^ (δ / 2 - d) * A / A := by
            field_simp [(by positivity : (0 : ℝ) < A).ne']
        _ ≤ A / B * α / A := by gcongr
        _ = 1 / B * α := by field_simp [(by positivity : (0 : ℝ) < A).ne']
        _ ≤ (h : ℝ) / B * α := by gcongr)
    (by
      rw [hφc]
      calc (h : ℝ) / B * α ≤ (b : ℝ) ^ k * A / B := by
            rw [div_mul_eq_mul_div]; gcongr
        _ ≤ (T : ℝ) ^ (-δ) := h2
        _ ≤ (T : ℝ) ^ (-(δ / 2)) := by
            gcongr
            · exact_mod_cast hT1
            · linarith)
  -- Lipschitz bound for `cexpTwoPi`
  have hlip : ∀ u v : ℝ, ‖Complex.cexpTwoPi u - Complex.cexpTwoPi v‖ ≤ 2 * π * |u - v| := by
    intro u v
    have e : Complex.cexpTwoPi u - Complex.cexpTwoPi v =
        Complex.cexpTwoPi v * (Complex.exp (Complex.I * ((2 * π * (u - v) : ℝ) : ℂ)) - 1) := by
      rw [show u = v + (u - v) by ring, Complex.cexpTwoPi_add, Complex.cexpTwoPi]
      simp only [Complex.cexpTwoPi]
      push_cast
      ring_nf
    rw [e, norm_mul, Complex.norm_cexpTwoPi, one_mul]
    refine norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hterm : ∀ t ∈ range T, ‖Complex.cexpTwoPi ((h : ℤ) * ((a t : ℝ) / B)) -
      Complex.exp (2 * π * Complex.I * φ.eval (t : ℝ))‖ ≤ 2 * π * (T : ℝ) ^ (-δ) := by
    intro t _
    have hev : φ.eval (t : ℝ) = (h : ℝ) * (f.eval ((t : ℝ) + 1) / B) := by
      simp only [hφ, eval_mul, eval_C, eval_comp, eval_add, eval_X]; ring
    rw [hev, ← Complex.cexpTwoPi]
    refine (hlip _ _).trans ?_
    gcongr
    push_cast
    rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos hB0, abs_of_pos (by positivity),
      abs_of_nonpos (by linarith [(hfl t).1])]
    calc (h : ℝ) * (-((a t : ℝ) - f.eval ((t : ℝ) + 1)) / B) ≤ h * (1 / B) := by
          gcongr; linarith [(hfl t).2]
      _ = h / B := by ring
      _ ≤ _ := hhB
  have hsum : ‖Complex.weylSum (fun t ↦ (a t : ℝ) / B) T h - polyExpSum φ T‖ ≤
      T * (2 * π * (T : ℝ) ^ (-δ)) := by
    unfold Complex.weylSum polyExpSum
    rw [← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    simpa using sum_le_sum hterm
  have hsmall : 2 * π * (T : ℝ) ^ (-δ) ≤ ε / 2 := by
    rw [rpow_neg hT0.le]
    rw [div_le_iff₀ hε] at hTε
    have := rpow_pos_of_pos hT0 δ
    rw [← div_eq_mul_inv, div_le_iff₀ this]
    nlinarith
  calc ‖Complex.weylSum (fun t ↦ (a t : ℝ) / B) T h‖
      ≤ ‖Complex.weylSum (fun t ↦ (a t : ℝ) / B) T h - polyExpSum φ T‖ + ‖polyExpSum φ T‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ T * (ε / 2) + ε / 2 * T := by gcongr; exact hsum.trans (by gcongr)
    _ = ε * T := by ring

end Real
