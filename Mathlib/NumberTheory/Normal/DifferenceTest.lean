/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Imported.TauCeti.Analysis.SpecificLimits.VanDerCorput
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Exponential sums with polynomial phases: the `d`-th difference test

For a real polynomial `φ` of degree `d` we bound `∑_{n < L} e(φ(n))`, where `e(x) = exp(2πix)`,
in terms of its leading coefficient `α` alone: if `α` is small, but not too small compared with
`L ^ (-d)`, the sum is `o(L)`. Unlike Weyl's inequality this needs no rational approximation to
`α`, so it needs no divisor bound. It is the input for the Davenport–Erdős theorem, where
`α = h a / b ^ m` is the leading coefficient of `h f(n) / b ^ m`.

The proof applies van der Corput's inequality (`TauCeti.vanDerCorput_inequality`, imported from
Tau Ceti) `d - 1` times, each time lowering the degree by one, and ends with a geometric series.

## Main statements

* `Polynomial.norm_polyExpSum_pow_le`: the `d`-th difference test.
* `Polynomial.eventually_norm_polyExpSum_le`: its uniform form, `o(T)` for leading coefficients
  in `[T ^ (δ - d), T ^ (-δ)]`.
-/

@[expose] public section

open Complex Finset Filter Topology

namespace Polynomial

/-- A linear exponential sum with small frequency `0 < α ≤ 1/2` is at most `1 / (2α)`. -/
theorem _root_.Complex.norm_sum_exp_linear_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1 / 2) (c : ℝ)
    (L : ℕ) :
    ‖∑ n ∈ range L, exp (2 * Real.pi * I * (α * n + c))‖ ≤ 1 / (2 * α) := by
  set z := exp (2 * Real.pi * I * α)
  have hz : ‖z - 1‖ = 2 * Real.sin (Real.pi * α) := by
    simp only [z]
    rw [show 2 * (Real.pi : ℂ) * I * α = I * ((2 * Real.pi * α : ℝ) : ℂ) by push_cast; ring,
      norm_exp_I_mul_ofReal_sub_one, show 2 * Real.pi * α / 2 = Real.pi * α by ring,
      Real.norm_eq_abs, abs_of_nonneg (by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (x := Real.pi * α) (by positivity)
          (by nlinarith [Real.pi_pos])
        linarith)]
  have hsin : 2 * α ≤ Real.sin (Real.pi * α) := by
    have := Real.mul_le_sin (x := Real.pi * α) (by positivity) (by nlinarith [Real.pi_pos])
    rwa [show 2 / Real.pi * (Real.pi * α) = 2 * α by field_simp] at this
  have hz1 : z ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hz; linarith
  have hnorm : ∀ t : ℝ, ‖exp (2 * Real.pi * I * t)‖ = 1 := fun t ↦ by
    rw [show 2 * (Real.pi : ℂ) * I * t = ((2 * Real.pi * t : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have e : ∑ n ∈ range L, exp (2 * Real.pi * I * (α * n + c)) =
      exp (2 * Real.pi * I * c) * ∑ n ∈ range L, z ^ n := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [← exp_natCast_mul, ← exp_add]; congr 1; ring
  rw [e, norm_mul, hnorm, one_mul, geom_sum_eq hz1, norm_div, hz]
  have hzL : ‖z ^ L - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, show ‖z‖ = 1 from hnorm α, one_pow, norm_one]; norm_num
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

/-- The difference `p (X + h) - p` of a polynomial of degree `≤ d + 1` has degree `≤ d`, with
leading coefficient `(d + 1) * p.coeff (d + 1) * h`. -/
theorem natDegree_taylor_sub_le {R : Type*} [CommRing R] {p : R[X]} {d : ℕ}
    (hp : p.natDegree ≤ d + 1) (h : R) :
    (taylor h p - p).natDegree ≤ d ∧ (taylor h p - p).coeff d = (d + 1) * p.coeff (d + 1) * h := by
  have key : ∀ n, d ≤ n → (taylor h p).coeff n = p.coeff n + (n + 1) * p.coeff (n + 1) * h := by
    intro n hn
    rw [taylor_coeff]
    have hdeg : (hasseDeriv n p).natDegree ≤ 1 :=
      (natDegree_hasseDeriv_le p n).trans (by omega)
    rw [eq_X_add_C_of_natDegree_le_one hdeg, eval_add, eval_mul, eval_C, eval_X, eval_C,
      hasseDeriv_coeff, hasseDeriv_coeff]
    simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul, add_comm 1 n,
      Nat.choose_succ_self_right]
    push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    have hn' : d < n := by exact_mod_cast hn
    rw [coeff_sub, key n hn'.le, coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 1 by omega)]
    ring
  · rw [coeff_sub, key d le_rfl]; ring

private theorem exp_mul_conj_exp (a b : ℝ) :
    exp (2 * Real.pi * I * a) * starRingEnd ℂ (exp (2 * Real.pi * I * b)) =
      exp (2 * Real.pi * I * (a - b)) := by
  rw [← exp_conj, ← exp_add]
  congr 1
  simp only [map_mul, map_ofNat, conj_ofReal, conj_I]
  ring

private theorem sum_Ico_inv_le (H : ℕ) : ∑ h ∈ Ico 1 H, (1 / (h : ℝ)) ≤ 1 + Real.log H := by
  rcases Nat.lt_or_ge 1 H with hH | hH
  · have := harmonic_le_one_add_log (H - 1)
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
    have e : Ico 1 H = Icc 1 (H - 1) := by ext; simp; omega
    rw [e]
    simp only [one_div]
    refine this.trans ?_
    have h1 : (0 : ℝ) < (H - 1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hH
    gcongr
    exact_mod_cast Nat.sub_le H 1
  · rw [Ico_eq_empty (by omega), sum_empty]
    interval_cases H <;> simp

/-- The exponential sum `∑_{n < L} e(φ(n))` of a real polynomial phase. -/
noncomputable def polyExpSum (φ : ℝ[X]) (L : ℕ) : ℂ :=
  ∑ n ∈ range L, exp (2 * Real.pi * I * φ.eval (n : ℝ))

private theorem norm_exp_two_pi_I_mul (t : ℝ) : ‖exp (2 * Real.pi * I * t)‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * I * t = ((2 * Real.pi * t : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I]

/-- **Weyl differencing** in van der Corput's form. -/
theorem polyExpSum_sq_le (φ : ℝ[X]) {N L H : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) (hLN : L ≤ N) :
    (‖polyExpSum φ L‖ / N) ^ 2 ≤ 2 / H +
      4 / H * ∑ h ∈ Ico 1 H, ‖polyExpSum (taylor (h : ℝ) φ - φ) (L - h)‖ / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have h := TauCeti.vanDerCorput_inequality L H fun n ↦ exp (2 * Real.pi * I * φ.eval (n : ℝ))
  have hb : ∑ n ∈ range L, ‖exp (2 * Real.pi * I * φ.eval (n : ℝ))‖ ^ 2 = L := by
    simp [norm_exp_two_pi_I_mul]
  have hC : ∀ h ∈ Ico 1 H, ∑ n ∈ range (L - h), exp (2 * Real.pi * I * φ.eval ((n + h : ℕ) : ℝ)) *
      starRingEnd ℂ (exp (2 * Real.pi * I * φ.eval (n : ℝ))) =
        polyExpSum (taylor (h : ℝ) φ - φ) (L - h) := fun h _ ↦ by
    refine sum_congr rfl fun n _ ↦ ?_
    rw [exp_mul_conj_exp, eval_sub, taylor_eval]; push_cast; ring_nf
  have hsum : ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) * ‖∑ n ∈ range (L - h),
      exp (2 * Real.pi * I * φ.eval ((n + h : ℕ) : ℝ)) *
        starRingEnd ℂ (exp (2 * Real.pi * I * φ.eval (n : ℝ)))‖ =
      ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) * ‖polyExpSum (taylor (h : ℝ) φ - φ) (L - h)‖ :=
    sum_congr rfl fun h hh ↦ by rw [hC h hh]
  rw [hb, hsum] at h
  set X := ∑ h ∈ Ico 1 H, ‖polyExpSum (taylor (h : ℝ) φ - φ) (L - h)‖
  have hX : ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) * ‖polyExpSum (taylor (h : ℝ) φ - φ) (L - h)‖ ≤
      H * X := by
    rw [mul_sum]
    refine sum_le_sum fun h _ ↦ ?_
    gcongr; exact_mod_cast Nat.sub_le H h
  have hLH : ((L + H - 1 : ℕ) : ℝ) ≤ 2 * N := by
    have : L + H - 1 ≤ 2 * N := by omega
    exact_mod_cast this
  have hL : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hX0 : 0 ≤ X := sum_nonneg fun _ _ ↦ norm_nonneg _
  have h2 : (H : ℝ) ^ 2 * ‖polyExpSum φ L‖ ^ 2 ≤ 2 * N * (H * N + 2 * (H * X)) :=
    h.trans (by gcongr)
  rw [div_pow, div_le_iff₀ (by positivity)]
  rw [← sum_div, show (2 / H + 4 / H * (X / N)) * N ^ 2 = 2 * N * (H * N + 2 * (H * X)) / H ^ 2 by
    field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **The `d`-th difference test**: a polynomial phase of degree `d` whose leading coefficient `α`
is small but not too small has a small exponential sum. -/
theorem norm_polyExpSum_pow_le {d : ℕ} (hd : 1 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (N L H : ℕ) (φ : ℝ[X]) (α : ℝ), 1 ≤ H → H ≤ N → L ≤ N → φ.natDegree ≤ d →
      φ.coeff d = α → 0 < α → (d.factorial : ℝ) * α * (H : ℝ) ^ (d - 1) ≤ 1 / 2 →
        (‖polyExpSum φ L‖ / N) ^ 2 ^ (d - 1) ≤
          K * (1 / H + (1 + Real.log H) ^ (d - 1) / (α * N * (H : ℝ) ^ (d - 1))) := by
  induction d, hd using Nat.le_induction with
  | base =>
    refine ⟨1, one_pos, fun N L H φ α hH hHN hLN hφ hα hα0 hα1 ↦ ?_⟩
    simp only [Nat.sub_self, pow_zero, pow_one, Nat.factorial_one, Nat.cast_one, one_mul,
      mul_one] at hα1 ⊢
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have e : polyExpSum φ L = ∑ n ∈ range L, exp (2 * Real.pi * I * (α * n + φ.coeff 0)) := by
      refine sum_congr rfl fun n _ ↦ ?_
      have : φ.eval (n : ℝ) = α * n + φ.coeff 0 := by
        conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hφ]
        simp [hα]
      rw [this]; push_cast; ring_nf
    rw [e]
    have h1 := Complex.norm_sum_exp_linear_le hα0 hα1 (φ.coeff 0) L
    have hH0 : (0 : ℝ) ≤ 1 / H := by positivity
    calc ‖∑ n ∈ range L, exp (2 * Real.pi * I * (α * n + φ.coeff 0))‖ / N
        ≤ 1 / (2 * α) / N := by gcongr
      _ ≤ 1 / (α * N) := by rw [div_div]; gcongr; nlinarith
      _ ≤ 1 / H + 1 / (α * N) := by linarith
  | succ d hd ih =>
    obtain ⟨K, hK, hKd⟩ := ih
    set m := 2 ^ (d - 1)
    have hm : 1 ≤ m := Nat.one_le_two_pow
    refine ⟨2 ^ (m - 1) * (2 ^ m + 4 ^ m * K), by positivity,
      fun N L H φ α hH hHN hLN hφ hα hα0 hα1 ↦ ?_⟩
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hH0 : (0 : ℝ) < H := by linarith
    have hlog : 0 ≤ Real.log H := Real.log_nonneg hHR
    simp only [Nat.add_sub_cancel] at hα1 ⊢
    have hpow : 2 ^ d = 2 * m := by
      simp only [m]; rw [← pow_succ']; congr 1; omega
    set x : ℕ → ℝ := fun h ↦ ‖polyExpSum (taylor (h : ℝ) φ - φ) (L - h)‖ / N
    have hx0 : ∀ h, 0 ≤ x h := fun h ↦ by positivity
    set Y := (1 + Real.log H) ^ d / (α * N * (H : ℝ) ^ d)
    have hY : 0 ≤ Y := by positivity
    -- bounds for the differenced sums
    have hxh : ∀ h ∈ Ico 1 H, x h ^ m ≤
        K * (1 / H + (1 + Real.log H) ^ (d - 1) / ((d + 1) * α * N * (H : ℝ) ^ (d - 1)) *
          (1 / h)) := fun h hh ↦ by
      have hh' := mem_Ico.1 hh
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh'.1
      have hhH : (h : ℝ) ≤ H := by exact_mod_cast hh'.2.le
      obtain ⟨hdeg, hcoeff⟩ := natDegree_taylor_sub_le hφ (h : ℝ)
      rw [hα] at hcoeff
      have := hKd N (L - h) H _ _ hH hHN (by omega) hdeg hcoeff (by positivity) (by
        calc (d.factorial : ℝ) * ((d + 1) * α * h) * (H : ℝ) ^ (d - 1)
            ≤ (d.factorial : ℝ) * ((d + 1) * α * H) * (H : ℝ) ^ (d - 1) := by gcongr
          _ = ((d + 1).factorial : ℝ) * α * (H : ℝ) ^ d := by
              rw [Nat.factorial_succ, show (H : ℝ) ^ d = H * (H : ℝ) ^ (d - 1) by
                rw [← pow_succ']; congr 1; omega]
              push_cast; ring
          _ ≤ 1 / 2 := hα1)
      refine this.trans (le_of_eq ?_)
      field_simp
    have hsum : 1 / (H : ℝ) * ∑ h ∈ Ico 1 H, x h ^ m ≤ K * (1 / H + Y) := by
      have h1 : ∑ h ∈ Ico 1 H, x h ^ m ≤ K * (∑ _h ∈ Ico 1 H, 1 / (H : ℝ) +
          (1 + Real.log H) ^ (d - 1) / ((d + 1) * α * N * (H : ℝ) ^ (d - 1)) *
            ∑ h ∈ Ico 1 H, (1 / (h : ℝ))) := by
        refine (sum_le_sum hxh).trans (le_of_eq ?_)
        rw [← mul_sum, sum_add_distrib, ← mul_sum]
      have h2 : ∑ _h ∈ Ico 1 H, 1 / (H : ℝ) ≤ 1 := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one_div]
        rw [div_le_one hH0]; exact_mod_cast Nat.sub_le H 1
      have h3 := sum_Ico_inv_le H
      have h4 : (1 + Real.log H) ^ (d - 1) / ((d + 1) * α * N * (H : ℝ) ^ (d - 1)) *
          ∑ h ∈ Ico 1 H, (1 / (h : ℝ)) ≤ H * Y := by
        calc _ ≤ (1 + Real.log H) ^ (d - 1) / ((d + 1) * α * N * (H : ℝ) ^ (d - 1)) *
              (1 + Real.log H) := by gcongr
          _ ≤ (1 + Real.log H) ^ (d - 1) / (α * N * (H : ℝ) ^ (d - 1)) * (1 + Real.log H) := by
              have : 0 ≤ α * N * (H : ℝ) ^ (d - 1) := by positivity
              gcongr
              nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
          _ = H * Y := by
              simp only [Y]
              rw [show d = (d - 1) + 1 by omega, Nat.add_sub_cancel, pow_succ, pow_succ]
              field_simp
      calc 1 / (H : ℝ) * ∑ h ∈ Ico 1 H, x h ^ m ≤ 1 / H * (K * (1 + H * Y)) := by
            gcongr; exact h1.trans (by gcongr)
        _ = K * (1 / H + Y) := by field_simp
    -- van der Corput
    have hv := polyExpSum_sq_le φ hH hHN hLN
    have hS0 : 0 ≤ ∑ h ∈ Ico 1 H, x h := sum_nonneg fun h _ ↦ hx0 h
    have hjensen : (∑ h ∈ Ico 1 H, x h) ^ m ≤ (H : ℝ) ^ (m - 1) * ∑ h ∈ Ico 1 H, x h ^ m := by
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hm', Nat.add_sub_cancel]
      refine (pow_sum_le_card_mul_sum_pow (fun h _ ↦ hx0 h) m').trans ?_
      gcongr
      rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le H 1
    calc (‖polyExpSum φ L‖ / N) ^ 2 ^ d = ((‖polyExpSum φ L‖ / N) ^ 2) ^ m := by
          rw [hpow, pow_mul]
      _ ≤ (2 / H + 4 / H * ∑ h ∈ Ico 1 H, x h) ^ m := by gcongr
      _ ≤ 2 ^ (m - 1) * ((2 / H) ^ m + (4 / H * ∑ h ∈ Ico 1 H, x h) ^ m) :=
          add_pow_le (by positivity) (by positivity) m
      _ ≤ 2 ^ (m - 1) * (2 ^ m * (1 / H) + 4 ^ m * (K * (1 / H + Y))) := by
          gcongr
          · rw [div_pow]
            calc (2 : ℝ) ^ m / (H : ℝ) ^ m ≤ 2 ^ m / H := by
                  gcongr; exact le_self_pow₀ hHR (by omega)
              _ = 2 ^ m * (1 / H) := by ring
          · rw [mul_pow, div_pow]
            calc (4 : ℝ) ^ m / (H : ℝ) ^ m * (∑ h ∈ Ico 1 H, x h) ^ m
                ≤ 4 ^ m / (H : ℝ) ^ m * ((H : ℝ) ^ (m - 1) * ∑ h ∈ Ico 1 H, x h ^ m) := by
                  gcongr
              _ = 4 ^ m * (1 / (H : ℝ) * ∑ h ∈ Ico 1 H, x h ^ m) := by
                  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                  rw [hm', Nat.add_sub_cancel, pow_succ]; field_simp; ring
              _ ≤ 4 ^ m * (K * (1 / H + Y)) := by gcongr
      _ ≤ 2 ^ (m - 1) * (2 ^ m * (1 / H + Y) + 4 ^ m * (K * (1 / H + Y))) := by
          gcongr; linarith
      _ = 2 ^ (m - 1) * (2 ^ m + 4 ^ m * K) * (1 / H + Y) := by ring

/-- `(1 + log x) ^ m = o(x ^ r)` for every `r > 0`. -/
theorem tendsto_one_add_log_pow_mul_rpow_neg (m : ℕ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ ↦ (1 + Real.log x) ^ m * x ^ (-r)) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (m : ℝ) hr).tendsto_div_nhds_zero).const_mul
    ((2 : ℝ) ^ m)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_ <;>
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  · have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
    positivity
  · have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
    have h1 : 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le hx0]
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, ← div_eq_mul_inv, mul_div_assoc', ← mul_pow]
    gcongr
    linarith

/-- The choice of the differencing length `H` in the uniform power saving. -/
private theorem exists_good_H {m : ℕ} (hm : 1 ≤ m) {T : ℕ} (hT : 1 ≤ T) {α δ : ℝ}
    (hα1 : (T : ℝ) ^ (δ - (m + 1 : ℕ)) ≤ α) (hα2 : α ≤ (T : ℝ) ^ (-δ))
    (hsmall : 2 * ((m + 1).factorial : ℝ) * (T : ℝ) ^ (-δ) ≤ 1) :
    ∃ H : ℕ, 1 ≤ H ∧ H ≤ T ∧ ((m + 1).factorial : ℝ) * α * (H : ℝ) ^ m ≤ 1 / 2 ∧
      1 / (H : ℝ) + (1 + Real.log H) ^ m / (α * T * (H : ℝ) ^ m) ≤
        2 * ((T : ℝ) ^ (-1 : ℝ) + (2 * ((m + 1).factorial : ℝ)) ^ (1 / (m : ℝ)) *
          (T : ℝ) ^ (-(δ / m))) + 2 ^ m * ((1 + Real.log T) ^ m *
            ((T : ℝ) ^ (-δ) + 2 * ((m + 1).factorial : ℝ) * (T : ℝ) ^ (-1 : ℝ))) := by
  set c : ℝ := 2 * ((m + 1).factorial : ℝ) with hc
  have hc0 : 0 < c := by positivity
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hα0 : 0 < α := (Real.rpow_pos_of_pos hT0 _).trans_le hα1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set y : ℝ := (c * α) ^ (-(1 / (m : ℝ))) with hy
  have hcα : c * α ≤ 1 := (mul_le_mul_of_nonneg_left hα2 hc0.le).trans hsmall
  have hy1 : 1 ≤ y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) hcα
    (by rw [neg_nonpos]; positivity)
  have hym : y ^ m = (c * α)⁻¹ := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show -(1 / (m : ℝ)) * m = -1 by field_simp, Real.rpow_neg_one]
  have hyinv : 1 / y ≤ c ^ (1 / (m : ℝ)) * (T : ℝ) ^ (-(δ / m)) := by
    rw [hy, Real.rpow_neg (by positivity), one_div, inv_inv,
      show -(δ / m) = -δ * (1 / (m : ℝ)) by ring, Real.rpow_mul hT0.le,
      ← Real.mul_rpow hc0.le (by positivity)]
    gcongr
  set z : ℝ := min (T : ℝ) y with hz
  have hz1 : 1 ≤ z := le_min hT1 hy1
  set H : ℕ := ⌊z⌋₊ with hH
  have hH1 : 1 ≤ H := Nat.le_floor (by simpa using hz1)
  have hHz : (H : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzH : z ≤ 2 * H := by
    have := Nat.lt_floor_add_one z
    have : (1 : ℝ) ≤ H := by exact_mod_cast hH1
    linarith
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  have hHT : H ≤ T := by exact_mod_cast hHz.trans (min_le_left _ _)
  have hHy : (H : ℝ) ≤ y := hHz.trans (min_le_right _ _)
  refine ⟨H, hH1, hHT, ?_, ?_⟩
  · have : (H : ℝ) ^ m ≤ (c * α)⁻¹ := hym ▸ pow_le_pow_left₀ hH0.le hHy m
    calc ((m + 1).factorial : ℝ) * α * (H : ℝ) ^ m ≤ ((m + 1).factorial : ℝ) * α * (c * α)⁻¹ := by
          gcongr
      _ = 1 / 2 := by rw [hc]; field_simp
  · -- `1 / z ≤ 1 / T + 1 / y` and `1 / z ^ m ≤ 1 / T ^ m + 1 / y ^ m`
    have hz0 : 0 < z := by linarith
    have hzinv : 1 / z ≤ (T : ℝ) ^ (-1 : ℝ) + 1 / y := by
      rw [Real.rpow_neg_one, ← one_div]
      rcases min_choice (T : ℝ) y with h | h <;> rw [← hz] at h <;> rw [h]
      · have : 0 ≤ 1 / y := by positivity
        linarith
      · have : 0 ≤ 1 / (T : ℝ) := by positivity
        linarith
    have hzminv : 1 / z ^ m ≤ 1 / (T : ℝ) ^ m + c * α := by
      rcases min_choice (T : ℝ) y with h | h <;> rw [← hz] at h <;> rw [h]
      · have : 0 ≤ c * α := by positivity
        linarith
      · rw [hym, one_div, inv_inv]
        have : 0 ≤ 1 / (T : ℝ) ^ m := by positivity
        linarith
    have h1 : 1 / (H : ℝ) ≤
        2 * ((T : ℝ) ^ (-1 : ℝ) + c ^ (1 / (m : ℝ)) * (T : ℝ) ^ (-(δ / m))) := by
      calc 1 / (H : ℝ) ≤ 2 * (1 / z) := by
            rw [mul_one_div, div_le_div_iff₀ hH0 hz0]
            linarith
        _ ≤ _ := by gcongr; exact hzinv.trans (by gcongr)
    have hlog : (1 + Real.log H) ^ m ≤ (1 + Real.log T) ^ m := by
      have : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH1)
      gcongr
    have hαT : 1 / (α * (T : ℝ) ^ (m + 1)) ≤ (T : ℝ) ^ (-δ) := by
      rw [div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = (T : ℝ) ^ (-δ) * ((T : ℝ) ^ (δ - (m + 1 : ℕ)) * (T : ℝ) ^ (m + 1)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
            simp
        _ ≤ _ := by gcongr
    have h2 : 1 / (α * T * (H : ℝ) ^ m) ≤
        2 ^ m * ((T : ℝ) ^ (-δ) + c * (T : ℝ) ^ (-1 : ℝ)) := by
      have hzm : z ^ m ≤ 2 ^ m * (H : ℝ) ^ m := by rw [← mul_pow]; gcongr
      have hHm : 1 / (H : ℝ) ^ m ≤ 2 ^ m * (1 / z ^ m) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc 1 / (α * T * (H : ℝ) ^ m) = 1 / (α * T) * (1 / (H : ℝ) ^ m) := by
            rw [one_div_mul_one_div]
        _ ≤ 1 / (α * T) * (2 ^ m * (1 / z ^ m)) := by gcongr
        _ = 2 ^ m * (1 / (α * T) * (1 / z ^ m)) := by ring
        _ ≤ 2 ^ m * (1 / (α * T) * (1 / (T : ℝ) ^ m + c * α)) := by gcongr
        _ = 2 ^ m * (1 / (α * (T : ℝ) ^ (m + 1)) + c * (T : ℝ) ^ (-1 : ℝ)) := by
            rw [Real.rpow_neg_one]; field_simp; ring
        _ ≤ _ := by gcongr
    calc _ ≤ 2 * ((T : ℝ) ^ (-1 : ℝ) + c ^ (1 / (m : ℝ)) * (T : ℝ) ^ (-(δ / m))) +
          (1 + Real.log T) ^ m * (2 ^ m * ((T : ℝ) ^ (-δ) + c * (T : ℝ) ^ (-1 : ℝ))) := by
          rw [div_eq_mul_one_div _ (α * T * (H : ℝ) ^ m)]
          gcongr
      _ = _ := by ring

/-- **Uniform power saving**: a polynomial phase of degree `d` whose leading coefficient lies in
`[T ^ (δ - d), T ^ (-δ)]` has exponential sum `o(T)` over `n < T`, uniformly. -/
theorem eventually_norm_polyExpSum_le {d : ℕ} (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ T : ℕ in atTop, ∀ φ : ℝ[X], φ.natDegree ≤ d →
      (T : ℝ) ^ (δ - d) ≤ φ.coeff d → φ.coeff d ≤ (T : ℝ) ^ (-δ) → ‖polyExpSum φ T‖ ≤ ε * T := by
  obtain ⟨K, hK, hb⟩ := norm_polyExpSum_pow_le hd
  suffices hkey : ∀ᶠ T : ℕ in atTop, 1 ≤ T ∧ ∀ α : ℝ, (T : ℝ) ^ (δ - d) ≤ α →
      α ≤ (T : ℝ) ^ (-δ) → ∃ H : ℕ, 1 ≤ H ∧ H ≤ T ∧
        (d.factorial : ℝ) * α * (H : ℝ) ^ (d - 1) ≤ 1 / 2 ∧
        K * (1 / H + (1 + Real.log H) ^ (d - 1) / (α * T * (H : ℝ) ^ (d - 1))) ≤
          ε ^ 2 ^ (d - 1) by
    filter_upwards [hkey] with T ⟨hT, hT'⟩ φ hφ h1 h2
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    obtain ⟨H, hH1, hHT, hHα, hle⟩ := hT' _ h1 h2
    have := (hb T T H φ _ hH1 hHT le_rfl hφ rfl
      ((Real.rpow_pos_of_pos hT0 _).trans_le h1) hHα).trans hle
    have h' := (pow_le_pow_iff_left₀ (by positivity) hε.le (by positivity)).1 this
    rwa [div_le_iff₀ hT0] at h'
  have hnat : Tendsto (fun T : ℕ ↦ (T : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have t1 := (tendsto_rpow_neg_atTop one_pos).comp hnat
  have tδ := (tendsto_rpow_neg_atTop hδ).comp hnat
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- linear phases: take `H = T`
    have hlim : Tendsto (fun T : ℕ ↦ K * ((T : ℝ) ^ (-1 : ℝ) + (T : ℝ) ^ (-δ))) atTop
        (𝓝 (K * (0 + 0))) := (t1.add tδ).const_mul K
    rw [add_zero, mul_zero] at hlim
    filter_upwards [eventually_ge_atTop 1, hlim.eventually (ge_mem_nhds (pow_pos hε (2 ^ 0))),
      tδ.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with T hT h1 h2
    refine ⟨hT, fun α hα1 hα2 ↦ ⟨T, hT, le_rfl, ?_, ?_⟩⟩
    · simpa using hα2.trans h2
    · have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
      have hα0 : 0 < α := (Real.rpow_pos_of_pos hT0 _).trans_le hα1
      have : 1 / (α * T) ≤ (T : ℝ) ^ (-δ) := by
        rw [div_le_iff₀ (by positivity)]
        calc (1 : ℝ) = (T : ℝ) ^ (-δ) * ((T : ℝ) ^ (δ - (0 + 1 : ℕ)) * T) := by
              rw [← Real.rpow_add_one hT0.ne', ← Real.rpow_add hT0]; simp
          _ ≤ _ := by gcongr
      simp only [pow_zero, mul_one, pow_one] at h1 ⊢
      rw [Real.rpow_neg_one] at h1
      calc K * (1 / T + 1 / (α * T)) ≤ K * ((T : ℝ)⁻¹ + (T : ℝ) ^ (-δ)) := by
            rw [one_div]; gcongr
        _ ≤ ε := h1
  · set c : ℝ := 2 * ((m + 1).factorial : ℝ)
    have tδm := (tendsto_rpow_neg_atTop (show 0 < δ / m by positivity)).comp hnat
    have tl1 := (tendsto_one_add_log_pow_mul_rpow_neg m one_pos).comp hnat
    have tlδ := (tendsto_one_add_log_pow_mul_rpow_neg m hδ).comp hnat
    have hlim : Tendsto (fun T : ℕ ↦ K * (2 * ((T : ℝ) ^ (-1 : ℝ) + c ^ (1 / (m : ℝ)) *
        (T : ℝ) ^ (-(δ / m))) + 2 ^ m * ((1 + Real.log T) ^ m * (T : ℝ) ^ (-δ) +
          c * ((1 + Real.log T) ^ m * (T : ℝ) ^ (-1 : ℝ))))) atTop
        (𝓝 (K * (2 * (0 + c ^ (1 / (m : ℝ)) * 0) + 2 ^ m * (0 + c * 0)))) :=
      (((t1.add (tδm.const_mul _)).const_mul 2).add
        ((tlδ.add (tl1.const_mul c)).const_mul _)).const_mul K
    simp only [mul_zero, add_zero] at hlim
    filter_upwards [eventually_ge_atTop 1, hlim.eventually (ge_mem_nhds (pow_pos hε (2 ^ m))),
      tδ.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / c by positivity))] with T hT h1 h2
    refine ⟨hT, fun α hα1 hα2 ↦ ?_⟩
    obtain ⟨H, hH1, hHT, hHα, hle⟩ := exists_good_H hm hT hα1 hα2
      (by rw [le_div_iff₀' (by positivity)] at h2; exact h2)
    refine ⟨H, hH1, hHT, hHα, (mul_le_mul_of_nonneg_left hle hK.le).trans (le_trans ?_ h1)⟩
    exact le_of_eq (by ring)

end Polynomial
