/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.TauCeti.NumberTheory.DiophantineApproximation.Exponent
public import Mathlib.NumberTheory.Normal.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Irrationality exponent and base-`b` digit bounds for `e = exp 1`

While the normality of `e = Real.exp 1` remains open (see `Wanted/NumberTheory/Normal/PiExp.lean`),
the Hermite–Padé integrals
$$I_n = \int_0^1 \frac{x^n (1 - x)^n}{n!} e^x \, dx, \qquad
  J_n = \int_0^1 \frac{x^{n+1} (1 - x)^n}{n!} e^x \, dx$$
yield simultaneous integer linear forms `I_n = A_n e - B_n` and `J_n = C_n e - D_n` with
determinant `A_n D_n - B_n C_n = (-1)^{n+1}`, `|A_n|, |C_n| ≤ 8^n (n+1)!`, and
`0 < I_n, J_n ≤ e / (4^n n!)`.

This gives a short, self-contained proof of:

* `Real.irrational_exp_one`: `e = exp 1` is irrational.
* `Real.irrationalityExponent_exp_one`: the irrationality exponent of `e` (in the sense of
  `TauCeti.irrationalityExponent`) equals `2`.
* `Real.exists_zero_run_le_of_irrationalityExponent_lt`: for any irrational `x` with
  `TauCeti.irrationalityExponent x < μ`, runs of `m` consecutive base-`b` zeros starting at
  position `n` satisfy `m ≤ (μ - 1) * n + C`.
* `Real.exists_zero_run_le_exp_one`: in every base `b ≥ 2` and for every `ε > 0`, runs of `m`
  consecutive zeros in the base-`b` expansion of `e` starting at position `n` have length at most
  `(1 + ε) * n + C`.

## References

* [C. S. Davis, *Rational approximations to e*][Davis1978]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace Real

section HermitePade

private noncomputable def expI (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n / n.factorial * Real.exp x

private noncomputable def expJ (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ (n + 1) * (1 - x) ^ n / n.factorial * Real.exp x

private def expPade : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 1, 0, -1)
  | n + 1 =>
    let (a, b, c, d) := expPade n
    let a' := -a + 2 * c
    let b' := -b + 2 * d
    (a', b', -(2 * (n : ℤ) + 3) * a' + c, -(2 * (n : ℤ) + 3) * b' + d)

private lemma expI_zero : expI 0 = Real.exp 1 - 1 := by
  simp [expI, integral_exp]

private lemma expJ_zero : expJ 0 = 1 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ (t - 1) * Real.exp t) (x * Real.exp x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ ↦ t - 1) 1 x := (hasDerivAt_id x).sub_const 1
    convert h1.mul (Real.hasDerivAt_exp x) using 1
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun x : ℝ ↦ x * Real.exp x).intervalIntegrable 0 1)
  simp only [expJ, zero_add, pow_one, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
    div_one]
  rw [h]
  norm_num

private lemma expI_succ (n : ℕ) : expI (n + 1) = -expI n + 2 * expJ n := by
  let F : ℝ → ℝ := fun x ↦
    x ^ (n + 1) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x
  let f : ℝ → ℝ := fun x ↦
    (x ^ n * (1 - x) ^ n / n.factorial * Real.exp x -
      2 * (x ^ (n + 1) * (1 - x) ^ n / n.factorial * Real.exp x)) +
      x ^ (n + 1) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (f x) x := by
    intro x _
    have hp1 : HasDerivAt (fun t : ℝ ↦ t ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * x ^ n) x := by
      simpa using hasDerivAt_pow (n + 1) x
    have hp2 : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ (n + 1))
        (-(((n + 1 : ℕ) : ℝ) * (1 - x) ^ n)) x := by
      have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have hcomp := (hasDerivAt_pow (n + 1) (1 - x)).comp x hsub
      simpa [Function.comp_def, mul_neg, mul_one] using hcomp
    have hprod := (hp1.mul hp2).div_const ((n + 1).factorial : ℝ)
    have hF := hprod.mul (Real.hasDerivAt_exp x)
    convert hF using 1
    have hfac : ((n + 1).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hfac0 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
    simp only [Pi.mul_apply, f, hfac, pow_succ]
    field_simp [hfac0, hn1]
    ring
  have h0 : ∫ x in (0 : ℝ)..1, f x = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous f).intervalIntegrable 0 1)]
    simp [F]
  have hcI : IntervalIntegrable
      (fun x : ℝ ↦ x ^ n * (1 - x) ^ n / n.factorial * Real.exp x)
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hcJ : IntervalIntegrable
      (fun x : ℝ ↦ x ^ (n + 1) * (1 - x) ^ n / n.factorial * Real.exp x)
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hcI1 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ (n + 1) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x)
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hsplit : ∫ x in (0 : ℝ)..1, f x = (expI n - 2 * expJ n) + expI (n + 1) := by
    simp only [f]
    rw [intervalIntegral.integral_add (hcI.sub (hcJ.const_mul 2)) hcI1,
      intervalIntegral.integral_sub hcI (hcJ.const_mul 2), intervalIntegral.integral_const_mul]
    rfl
  linarith

private lemma expJ_succ (n : ℕ) :
    expJ (n + 1) = -(2 * (n : ℝ) + 3) * expI (n + 1) + expJ n := by
  let G : ℝ → ℝ := fun x ↦
    x ^ (n + 2) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x
  let g : ℝ → ℝ := fun x ↦
    ((2 * (n : ℝ) + 3) *
        (x ^ (n + 1) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x) -
      x ^ (n + 1) * (1 - x) ^ n / n.factorial * Real.exp x) +
      x ^ (n + 2) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt G (g x) x := by
    intro x _
    have hp1 : HasDerivAt (fun t : ℝ ↦ t ^ (n + 2)) (((n + 2 : ℕ) : ℝ) * x ^ (n + 1)) x := by
      simpa using hasDerivAt_pow (n + 2) x
    have hp2 : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ (n + 1))
        (-(((n + 1 : ℕ) : ℝ) * (1 - x) ^ n)) x := by
      have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have hcomp := (hasDerivAt_pow (n + 1) (1 - x)).comp x hsub
      simpa [Function.comp_def, mul_neg, mul_one] using hcomp
    have hprod := (hp1.mul hp2).div_const ((n + 1).factorial : ℝ)
    have hG := hprod.mul (Real.hasDerivAt_exp x)
    convert hG using 1
    have hfac : ((n + 1).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hfac0 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
    simp only [Pi.mul_apply, g, hfac, pow_succ]
    push_cast
    field_simp [hfac0, hn1]
    ring
  have h0 : ∫ x in (0 : ℝ)..1, g x = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous g).intervalIntegrable 0 1)]
    simp [G]
  have hcI1 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ (n + 1) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x)
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hcJ : IntervalIntegrable
      (fun x : ℝ ↦ x ^ (n + 1) * (1 - x) ^ n / n.factorial * Real.exp x)
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hcJ1 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ (n + 2) * (1 - x) ^ (n + 1) / (n + 1).factorial * Real.exp x)
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hsplit : ∫ x in (0 : ℝ)..1, g x =
      ((2 * (n : ℝ) + 3) * expI (n + 1) - expJ n) + expJ (n + 1) := by
    simp only [g]
    rw [intervalIntegral.integral_add ((hcI1.const_mul _).sub hcJ) hcJ1,
      intervalIntegral.integral_sub (hcI1.const_mul _) hcJ, intervalIntegral.integral_const_mul]
    rfl
  linarith

private lemma expPade_spec (n : ℕ) :
    let (a, b, c, d) := expPade n
    expI n = (a : ℝ) * Real.exp 1 - b ∧
    expJ n = (c : ℝ) * Real.exp 1 - d ∧
    a * d - b * c = (-1 : ℤ) ^ (n + 1) ∧
    |a| ≤ (8 : ℤ) ^ n * (n.factorial : ℤ) ∧
    |c| ≤ (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := by
  induction n with
  | zero =>
    simp only [expPade, Int.cast_one, one_mul, Int.cast_zero, zero_mul, Int.cast_neg, sub_neg_eq_add,
      zero_add, expI_zero, expJ_zero, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, mul_one, abs_one, abs_zero]
    norm_num
  | succ n ih =>
    rcases h : expPade n with ⟨a, b, c, d⟩
    rw [h] at ih
    rcases ih with ⟨hI, hJ, hdet, ha, hc⟩
    simp only [expPade, h]
    set a' : ℤ := -a + 2 * c
    set b' : ℤ := -b + 2 * d
    set c' : ℤ := -(2 * (n : ℤ) + 3) * a' + c
    set d' : ℤ := -(2 * (n : ℤ) + 3) * b' + d
    have hI' : expI (n + 1) = (a' : ℝ) * Real.exp 1 - b' := by
      rw [expI_succ, hI, hJ]
      simp only [a', b']
      push_cast
      ring
    have hJ' : expJ (n + 1) = (c' : ℝ) * Real.exp 1 - d' := by
      rw [expJ_succ, hI', hJ]
      simp only [c', d']
      push_cast
      ring
    have hdet' : a' * d' - b' * c' = (-1 : ℤ) ^ (n + 2) := by
      have hcalc : a' * d' - b' * c' = -(a * d - b * c) := by
        simp only [a', b', c', d']
        ring
      rw [hcalc, hdet, pow_succ]
      ring
    have hfac2 : ((n + 2).factorial : ℤ) = ((n : ℤ) + 2) * ((n + 1).factorial : ℤ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
    have ha'_3 : |a'| ≤ 3 * (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := by
      calc |a'| ≤ |-a| + |2 * c| := abs_add_le _ _
        _ = |a| + 2 * |c| := by rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2)]
        _ ≤ (8 : ℤ) ^ n * (n.factorial : ℤ) +
              2 * ((8 : ℤ) ^ n * ((n + 1).factorial : ℤ)) := by linarith
        _ ≤ (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) +
              2 * ((8 : ℤ) ^ n * ((n + 1).factorial : ℤ)) := by
            gcongr
            exact Nat.le_succ n
        _ = 3 * (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := by ring
    have ha' : |a'| ≤ (8 : ℤ) ^ (n + 1) * ((n + 1).factorial : ℤ) := by
      have hnonneg : (0 : ℤ) ≤ (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := by positivity
      calc |a'| ≤ 3 * (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := ha'_3
        _ ≤ 8 * (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := by linarith
        _ = (8 : ℤ) ^ (n + 1) * ((n + 1).factorial : ℤ) := by rw [pow_succ]; ring
    have hc' : |c'| ≤ (8 : ℤ) ^ (n + 1) * ((n + 2).factorial : ℤ) := by
      have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
      have hpos : (0 : ℤ) ≤ 2 * (n : ℤ) + 3 := by linarith
      have hnonneg : (0 : ℤ) ≤ (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := by positivity
      calc |c'| ≤ |-(2 * (n : ℤ) + 3) * a'| + |c| := abs_add_le _ _
        _ = (2 * (n : ℤ) + 3) * |a'| + |c| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hpos]
        _ ≤ (2 * (n : ℤ) + 3) * (3 * (8 : ℤ) ^ n * ((n + 1).factorial : ℤ)) +
              (8 : ℤ) ^ n * ((n + 1).factorial : ℤ) := by
            nlinarith
        _ = (6 * (n : ℤ) + 10) * ((8 : ℤ) ^ n * ((n + 1).factorial : ℤ)) := by ring
        _ ≤ (8 * ((n : ℤ) + 2)) * ((8 : ℤ) ^ n * ((n + 1).factorial : ℤ)) := by nlinarith
        _ = (8 : ℤ) ^ (n + 1) * ((n + 2).factorial : ℤ) := by
            rw [pow_succ, hfac2]; ring
    exact ⟨hI', hJ', hdet', ha', hc'⟩

private lemma expI_pos (n : ℕ) : 0 < expI n := by
  refine intervalIntegral.integral_pos zero_lt_one (by fun_prop : Continuous _).continuousOn ?_ ?_
  · intro x hx
    exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg hx.1.le _)
      (pow_nonneg (sub_nonneg.2 hx.2) _)) (Nat.cast_nonneg _)) (Real.exp_pos x).le
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
    positivity

private lemma expI_le (n : ℕ) : expI n ≤ Real.exp 1 / ((4 : ℝ) ^ n * n.factorial) := by
  have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      x ^ n * (1 - x) ^ n / n.factorial * Real.exp x ≤
        Real.exp 1 / ((4 : ℝ) ^ n * n.factorial) := by
    intro x hx
    have hq : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have hq0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.2 hx.2)
    have hpow : x ^ n * (1 - x) ^ n ≤ (1 / 4 : ℝ) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hq0 hq n
    have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.2 hx.2
    have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
    calc x ^ n * (1 - x) ^ n / n.factorial * Real.exp x
        ≤ (1 / 4 : ℝ) ^ n / n.factorial * Real.exp 1 := by gcongr
      _ = Real.exp 1 / ((4 : ℝ) ^ n * n.factorial) := by
          rw [one_div, inv_pow]; ring
  calc expI n
      ≤ ∫ _ in (0 : ℝ)..1, Real.exp 1 / ((4 : ℝ) ^ n * n.factorial) :=
        intervalIntegral.integral_mono_on zero_le_one
          ((by fun_prop : Continuous _).intervalIntegrable 0 1)
          intervalIntegrable_const hle
    _ = Real.exp 1 / ((4 : ℝ) ^ n * n.factorial) := by simp

private lemma expJ_le (n : ℕ) : expJ n ≤ Real.exp 1 / ((4 : ℝ) ^ n * n.factorial) := by
  have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      x ^ (n + 1) * (1 - x) ^ n / n.factorial * Real.exp x ≤
        x ^ n * (1 - x) ^ n / n.factorial * Real.exp x := by
    intro x hx
    have hpow : x ^ (n + 1) ≤ x ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hx.1 n) hx.2
    gcongr
    exact pow_nonneg (sub_nonneg.2 hx.2) n
  refine (intervalIntegral.integral_mono_on zero_le_one
    ((by fun_prop : Continuous _).intervalIntegrable 0 1)
    ((by fun_prop : Continuous _).intervalIntegrable 0 1) hle).trans (expI_le n)

private lemma expJ_nonneg (n : ℕ) : 0 ≤ expJ n := by
  refine intervalIntegral.integral_nonneg zero_le_one fun x hx ↦ ?_
  exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg hx.1 _)
    (pow_nonneg (sub_nonneg.2 hx.2) _)) (Nat.cast_nonneg _)) (Real.exp_pos x).le

private lemma pow_sub_le_factorial (M : ℕ) : ∀ k : ℕ, M ^ (k - M) ≤ k.factorial := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < M
    · have : k + 1 - M = 0 := by omega
      rw [this, pow_zero]
      exact Nat.factorial_pos _
    · have hsub : k + 1 - M = (k - M) + 1 := by omega
      rw [hsub, pow_succ, Nat.factorial_succ]
      calc M ^ (k - M) * M ≤ k.factorial * M := Nat.mul_le_mul_right M ih
        _ ≤ k.factorial * (k + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (k + 1) * k.factorial := Nat.mul_comm _ _

private lemma mul_succ_le_four_pow (n : ℕ) : n * (n + 1) ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases n with _ | n
    · norm_num
    · have h1 : (n + 2) * (n + 3) ≤ 4 * ((n + 1) * (n + 2)) := by nlinarith
      calc (n + 2) * (n + 3) ≤ 4 * ((n + 1) * (n + 2)) := h1
        _ ≤ 4 * 4 ^ (n + 1) := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (n + 2) := by rw [pow_succ']; ring

end HermitePade

/-- `e = Real.exp 1` is irrational. -/
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((q.den : ℝ) * Real.exp 1)
    (by norm_num : (1 : ℝ) < 4)
  rcases hp : expPade n with ⟨a, b, c, d⟩
  have hspec := expPade_spec n
  rw [hp] at hspec
  have hI_eq : expI n = (a : ℝ) * Real.exp 1 - b := hspec.1
  have hmul : (q.den : ℝ) * expI n = ((a * q.num - b * (q.den : ℤ) : ℤ) : ℝ) := by
    rw [hI_eq, ← hq]
    have hqden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
    rw [Rat.cast_def]
    push_cast
    field_simp [hqden]
  have hint_pos : (0 : ℤ) < a * q.num - b * (q.den : ℤ) := by
    have hpos : (0 : ℝ) < ((a * q.num - b * (q.den : ℤ) : ℤ) : ℝ) := by
      rw [← hmul]
      exact mul_pos (Nat.cast_pos.2 q.pos) (expI_pos n)
    exact_mod_cast hpos
  have hint_ge_one : (1 : ℝ) ≤ (q.den : ℝ) * expI n := by
    rw [hmul]
    exact_mod_cast hint_pos
  have hbound : (q.den : ℝ) * expI n < 1 := by
    have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h4 : (q.den : ℝ) * Real.exp 1 < (4 : ℝ) ^ n * n.factorial := by
      calc (q.den : ℝ) * Real.exp 1 < (4 : ℝ) ^ n := hn
        _ = (4 : ℝ) ^ n * 1 := (mul_one _).symm
        _ ≤ (4 : ℝ) ^ n * n.factorial := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc (q.den : ℝ) * expI n
        ≤ (q.den : ℝ) * (Real.exp 1 / ((4 : ℝ) ^ n * n.factorial)) :=
          mul_le_mul_of_nonneg_left (expI_le n) (Nat.cast_nonneg _)
      _ = (q.den : ℝ) * Real.exp 1 / ((4 : ℝ) ^ n * n.factorial) := by ring
      _ < 1 := (div_lt_one (by positivity)).2 h4
  linarith

/-- The irrationality exponent of `e = Real.exp 1` is `2`. -/
theorem irrationalityExponent_exp_one :
    TauCeti.irrationalityExponent (Real.exp 1) = 2 := by
  refine le_antisymm ?_ ((TauCeti.two_le_irrationalityExponent_iff _).2 irrational_exp_one)
  rw [TauCeti.irrationalityExponent_le_iff]
  intro μ hμ
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  by_contra hlt
  have h2lt : 2 < μ := by
    by_contra hle
    exact hlt (ENNReal.ofReal_le_ofReal (not_lt.1 hle))
  set ε : ℝ := (μ - 2) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨C, hCpos, hC⟩ := hμ.exists_pos
  set M : ℕ := Nat.ceil ((8 : ℝ) ^ (1 / ε)) + 1
  have hM_ge : (8 : ℝ) ^ (1 / ε) ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  have h8_le_M : (8 : ℝ) ≤ (M : ℝ) ^ ε := by
    have h1 := Real.rpow_le_rpow (by positivity) hM_ge hε.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hε.ne', Real.rpow_one] at h1
  let f : ℕ → ℝ := fun n ↦ (4 : ℝ) ^ n * n.factorial
  have hf_unbdd : ∀ B : ℝ, ∃ n : ℕ, B ≤ f n := fun B ↦ by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 4)
    refine ⟨n, hn.le.trans ?_⟩
    have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc (4 : ℝ) ^ n = (4 : ℝ) ^ n * 1 := (mul_one _).symm
      _ ≤ (4 : ℝ) ^ n * n.factorial := mul_le_mul_of_nonneg_left h1 (by positivity)
  set K : ℝ := 128 * Real.exp 1 * (8 : ℝ) ^ M * (2 * Real.exp 1) ^ ε
  have hKpos : 0 < K := by positivity
  have hq_large : ∀ᶠ q : ℕ in atTop,
      f M < 2 * Real.exp 1 * q ∧ 2 * C * K ≤ (q : ℝ) ^ ε := by
    have h1 : ∀ᶠ q : ℕ in atTop, f M < 2 * Real.exp 1 * q :=
      ((tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < 2 * Real.exp 1)).eventually
        (eventually_gt_atTop (f M)))
    have h2 : ∀ᶠ q : ℕ in atTop, 2 * C * K ≤ (q : ℝ) ^ ε :=
      (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (2 * C * K)))
    exact h1.and h2
  obtain ⟨q, ⟨hqM, hqK⟩, hq_pos, p, _, happrox⟩ := (hq_large.and_frequently hC).exists
  have hq_rpos : (0 : ℝ) < q := Nat.cast_pos.2 hq_pos
  classical
  have hex : ∃ n : ℕ, 2 * Real.exp 1 * q ≤ f n := hf_unbdd _
  set n : ℕ := Nat.find hex
  have hfn : 2 * Real.exp 1 * q ≤ f n := Nat.find_spec hex
  have hn_gt_M : M < n := by
    by_contra hle
    have hle' : n ≤ M := not_lt.1 hle
    have hf_mono : f n ≤ f M := by
      simp only [f]
      exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hle')
        (Nat.cast_le.2 (Nat.factorial_le hle')) (Nat.cast_nonneg _) (by positivity)
    linarith
  have hn_pos : 1 ≤ n := by omega
  have hfn_prev : f (n - 1) < 2 * Real.exp 1 * q :=
    not_le.1 (Nat.find_min hex (by omega : n - 1 < n))
  rcases hp : expPade n with ⟨a, b, c, d⟩
  have hspec := expPade_spec n
  rw [hp] at hspec
  rcases hspec with ⟨hI_eq, hJ_eq, hdet, ha_bd, hc_bd⟩
  have hqI : (q : ℝ) * expI n ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left (expI_le n) hq_rpos.le
    have h2 : (q : ℝ) * (Real.exp 1 / f n) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity : 0 < f n)]
      linarith
    exact h1.trans h2
  have hqJ : (q : ℝ) * expJ n ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left (expJ_le n) hq_rpos.le
    have h2 : (q : ℝ) * (Real.exp 1 / f n) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity : 0 < f n)]
      linarith
    exact h1.trans h2
  have hne : a * p - b * (q : ℤ) ≠ 0 ∨ c * p - d * (q : ℤ) ≠ 0 := by
    by_contra hboth
    push Not at hboth
    have h1 : a * p = b * (q : ℤ) := sub_eq_zero.1 hboth.1
    have h2 : c * p = d * (q : ℤ) := sub_eq_zero.1 hboth.2
    have hzero : (a * d - b * c) * (q : ℤ) = 0 := by
      calc (a * d - b * c) * (q : ℤ) = a * (d * q) - c * (b * q) := by ring
        _ = a * (c * p) - c * (a * p) := by rw [← h1, ← h2]
        _ = 0 := by ring
    have hdet_ne : a * d - b * c ≠ 0 := by rw [hdet]; exact pow_ne_zero _ (by norm_num)
    exact (by omega : q ≠ 0) (Int.ofNat_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hdet_ne))
  have hlow : (1 / 2 : ℝ) ≤ (8 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (q : ℝ) *
      |Real.exp 1 - p / q| := by
    have hstep : ∀ (u v : ℤ) (R : ℝ), R = (u : ℝ) * Real.exp 1 - v → 0 ≤ R →
        (q : ℝ) * R ≤ 1 / 2 → u * p - v * (q : ℤ) ≠ 0 →
        |(u : ℝ)| ≤ (8 : ℝ) ^ n * ((n + 1).factorial : ℝ) →
        (1 / 2 : ℝ) ≤ (8 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (q : ℝ) *
          |Real.exp 1 - p / q| := by
      intro u v R hR hR0 hqR huv hu_bd
      have h1 : (1 : ℝ) ≤ |((u * p - v * (q : ℤ) : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs huv
      have hid : ((u * p - v * (q : ℤ) : ℤ) : ℝ) =
          (u : ℝ) * (q : ℝ) * (p / q - Real.exp 1) + (q : ℝ) * R := by
        rw [hR]
        push_cast
        field_simp [hq_rpos.ne']
        ring
      have htri : (1 : ℝ) ≤ |(u : ℝ)| * (q : ℝ) * |Real.exp 1 - p / q| + (q : ℝ) * R := by
        calc (1 : ℝ) ≤ |((u * p - v * (q : ℤ) : ℤ) : ℝ)| := h1
          _ = |(u : ℝ) * (q : ℝ) * (p / q - Real.exp 1) + (q : ℝ) * R| := by rw [hid]
          _ ≤ |(u : ℝ) * (q : ℝ) * (p / q - Real.exp 1)| + |(q : ℝ) * R| := abs_add_le _ _
          _ = |(u : ℝ)| * (q : ℝ) * |Real.exp 1 - p / q| + (q : ℝ) * R := by
              rw [abs_mul, abs_mul, abs_of_pos hq_rpos, abs_sub_comm,
                abs_of_nonneg (mul_nonneg hq_rpos.le hR0)]
      have h2 : (1 / 2 : ℝ) ≤ |(u : ℝ)| * (q : ℝ) * |Real.exp 1 - p / q| := by linarith
      refine h2.trans ?_
      gcongr
    rcases hne with hne1 | hne2
    · refine hstep a b (expI n) hI_eq (expI_pos n).le hqI hne1 ?_
      have : |(a : ℝ)| ≤ (8 : ℝ) ^ n * (n.factorial : ℝ) := by exact_mod_cast ha_bd
      exact this.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.2 (Nat.factorial_le (Nat.le_succ n))) (by positivity))
    · refine hstep c d (expJ n) hJ_eq (expJ_nonneg n) hqJ hne2 ?_
      exact_mod_cast hc_bd
  have h8_bound : (8 : ℝ) ^ (n - 1) ≤ (8 : ℝ) ^ M * (2 * Real.exp 1 * q) ^ ε := by
    have hsplit : (8 : ℝ) ^ (n - 1) = (8 : ℝ) ^ M * (8 : ℝ) ^ (n - 1 - M) := by
      rw [← pow_add, show M + (n - 1 - M) = n - 1 by omega]
    have hpow : (8 : ℝ) ^ (n - 1 - M) ≤ ((n - 1).factorial : ℝ) ^ ε := by
      calc (8 : ℝ) ^ (n - 1 - M)
          ≤ ((M : ℝ) ^ ε) ^ (n - 1 - M) := pow_le_pow_left₀ (by positivity) h8_le_M _
        _ = ((M : ℝ) ^ (n - 1 - M)) ^ ε := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
              mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
        _ ≤ ((n - 1).factorial : ℝ) ^ ε := by
            refine Real.rpow_le_rpow (by positivity) ?_ hε.le
            exact_mod_cast pow_sub_le_factorial M (n - 1)
    have hfac_le_f : ((n - 1).factorial : ℝ) ≤ f (n - 1) := by
      simp only [f]
      exact le_mul_of_one_le_left (Nat.cast_nonneg _) (one_le_pow₀ (by norm_num))
    calc (8 : ℝ) ^ (n - 1) = (8 : ℝ) ^ M * (8 : ℝ) ^ (n - 1 - M) := hsplit
      _ ≤ (8 : ℝ) ^ M * ((n - 1).factorial : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (8 : ℝ) ^ M * (2 * Real.exp 1 * q) ^ ε := by
          gcongr
          exact hfac_le_f.trans hfn_prev.le
  have hcoef_bound : (8 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ K * (q : ℝ) ^ (1 + ε) := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    have hfac_eq : ((n + 1).factorial : ℝ) =
        ((n * (n + 1) : ℕ) : ℝ) * ((n - 1).factorial : ℝ) := by
      rw [hm, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have h4pow : ((n * (n + 1) : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by
      exact_mod_cast mul_succ_le_four_pow n
    have h8split : (8 : ℝ) ^ n = 8 * 2 ^ (n - 1) * (4 : ℝ) ^ (n - 1) := by
      rw [hm, Nat.add_sub_cancel, pow_succ, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
      ring
    have h24 : (2 : ℝ) ^ (n - 1) * (4 : ℝ) ^ n = 4 * (8 : ℝ) ^ (n - 1) := by
      rw [hm, Nat.add_sub_cancel, pow_succ, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
      ring
    have hqpow : (2 * Real.exp 1 * q) ^ ε = (2 * Real.exp 1) ^ ε * (q : ℝ) ^ ε :=
      Real.mul_rpow (by positivity) hq_rpos.le
    calc (8 : ℝ) ^ n * ((n + 1).factorial : ℝ)
        = (8 * (2 : ℝ) ^ (n - 1) * ((n * (n + 1) : ℕ) : ℝ)) * f (n - 1) := by
          rw [h8split, hfac_eq]; simp only [f]; ring
      _ ≤ (8 * (2 : ℝ) ^ (n - 1) * (4 : ℝ) ^ n) * (2 * Real.exp 1 * q) := by
          gcongr
      _ = 64 * Real.exp 1 * (8 : ℝ) ^ (n - 1) * q := by
          rw [show 8 * (2 : ℝ) ^ (n - 1) * (4 : ℝ) ^ n =
            8 * ((2 : ℝ) ^ (n - 1) * (4 : ℝ) ^ n) by ring, h24]; ring
      _ ≤ 64 * Real.exp 1 * ((8 : ℝ) ^ M * (2 * Real.exp 1 * q) ^ ε) * q := by
          gcongr
      _ ≤ 128 * Real.exp 1 * ((8 : ℝ) ^ M * ((2 * Real.exp 1) ^ ε * (q : ℝ) ^ ε)) * q := by
          rw [hqpow]
          have : (0 : ℝ) ≤
              Real.exp 1 * ((8 : ℝ) ^ M * ((2 * Real.exp 1) ^ ε * (q : ℝ) ^ ε)) * q := by
            positivity
          linarith
      _ = K * (q : ℝ) ^ (1 + ε) := by
          rw [Real.rpow_add hq_rpos, Real.rpow_one]
          simp only [K]
          ring
  have hcontra : (1 / 2 : ℝ) < (1 / 2 : ℝ) := by
    have hμ_eq : (1 + ε) + 1 + ε = μ := by simp only [ε]; ring
    have hq_split : (q : ℝ) ^ μ = (q : ℝ) ^ (1 + ε) * (q : ℝ) * (q : ℝ) ^ ε := by
      calc (q : ℝ) ^ μ = (q : ℝ) ^ ((1 + ε) + 1 + ε) := by rw [hμ_eq]
        _ = (q : ℝ) ^ (1 + ε) * (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ ε := by
            rw [Real.rpow_add hq_rpos, Real.rpow_add hq_rpos]
        _ = (q : ℝ) ^ (1 + ε) * (q : ℝ) * (q : ℝ) ^ ε := by rw [Real.rpow_one]
    calc (1 / 2 : ℝ)
        ≤ (8 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (q : ℝ) * |Real.exp 1 - p / q| := hlow
      _ < (8 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (q : ℝ) * (C / (q : ℝ) ^ μ) := by gcongr
      _ ≤ K * (q : ℝ) ^ (1 + ε) * (q : ℝ) * (C / (q : ℝ) ^ μ) := by gcongr
      _ = C * K / (q : ℝ) ^ ε := by
          rw [hq_split]
          have h1 : (q : ℝ) ^ (1 + ε) ≠ 0 := (Real.rpow_pos_of_pos hq_rpos _).ne'
          have h2 : (q : ℝ) ^ ε ≠ 0 := (Real.rpow_pos_of_pos hq_rpos _).ne'
          field_simp [h1, h2, hq_rpos.ne']
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hq_rpos ε)]
          linarith
  exact lt_irrefl _ hcontra

private lemma mul_pow_lt_one_of_digit_eq_zero {b : ℕ} (hb : 0 < b) {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y < 1) {m : ℕ} (h : ∀ j < m, digit b y j = 0) : y * (b : ℝ) ^ m < 1 := by
  induction m with
  | zero => simpa using hy1
  | succ m ih =>
    have ih' := ih fun j hj ↦ h j (by omega)
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hlt : y * (b : ℝ) ^ (m + 1) < b := by rw [pow_succ]; nlinarith
    have h0 : 0 ≤ y * (b : ℝ) ^ (m + 1) := mul_nonneg hy0 (by positivity)
    have hfl_lt : ⌊y * (b : ℝ) ^ (m + 1)⌋ < b := Int.floor_lt.2 hlt
    have hfl_nn : 0 ≤ ⌊y * (b : ℝ) ^ (m + 1)⌋ := Int.floor_nonneg.2 h0
    have hdig : digit b y m = 0 := h m (Nat.lt_succ_self m)
    rw [digit, Int.emod_eq_of_lt hfl_nn hfl_lt] at hdig
    have hfl0 : ⌊y * (b : ℝ) ^ (m + 1)⌋ = 0 := by omega
    simpa using Int.floor_lt.1 (by omega : ⌊y * (b : ℝ) ^ (m + 1)⌋ < (1 : ℤ))

/-- Any irrational number with irrationality exponent strictly less than `μ` has base-`b` zero
runs starting at position `n` of length at most `(μ - 1) * n + C`. -/
theorem exists_zero_run_le_of_irrationalityExponent_lt {b : ℕ} (hb : 2 ≤ b) {x μ : ℝ}
    (hx : Irrational x) (hμ : TauCeti.irrationalityExponent x < ENNReal.ofReal μ) :
    ∃ C : ℝ, ∀ n m : ℕ, (∀ j < m, digit b x (n + j) = 0) →
      (m : ℝ) ≤ (μ - 1) * n + C := by
  have h2le : (2 : ℝ≥0∞) ≤ TauCeti.irrationalityExponent x :=
    (TauCeti.two_le_irrationalityExponent_iff x).2 hx
  have hμ_pos : 0 < μ := by
    by_contra hle
    have h0 : ENNReal.ofReal μ = 0 := ENNReal.ofReal_eq_zero.2 (not_lt.1 hle)
    rw [h0] at hμ
    exact not_lt_zero' hμ
  have h2ltμ : (2 : ℝ) < μ := by
    have : ENNReal.ofReal 2 < ENNReal.ofReal μ := by
      simpa using h2le.trans_lt hμ
    exact (ENNReal.ofReal_lt_ofReal_iff hμ_pos).1 this
  have hnotL : ¬ LiouvilleWith μ x := fun hL ↦
    not_le_of_gt hμ (TauCeti.le_irrationalityExponent_of_liouvilleWith hL)
  have happrox : ∃ Q₀ : ℕ, ∀ q ≥ Q₀, 0 < q → ∀ p : ℤ, 1 / (q : ℝ) ^ μ ≤ |x - p / q| := by
    have hnot : ¬ ∃ᶠ q : ℕ in atTop, ∃ p : ℤ, x ≠ p / q ∧ |x - p / q| < 1 / (q : ℝ) ^ μ :=
      fun hf ↦ hnotL ⟨1, hf⟩
    rw [Filter.not_frequently, eventually_atTop] at hnot
    obtain ⟨Q₀, hQ₀⟩ := hnot
    refine ⟨Q₀, fun q hq _ p ↦ ?_⟩
    have hne : x ≠ (p : ℝ) / q := by
      intro heq
      exact hx ⟨(p : ℚ) / q, by push_cast; exact heq.symm⟩
    have := hQ₀ q hq
    push Not at this
    exact this p hne
  obtain ⟨Q₀, hQ₀⟩ := happrox
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hfin : ∀ n : ℕ, ∃ M : ℕ, ¬ ∀ j < M, digit b x (n + j) = 0 := by
    intro n
    have hypos : 0 < Int.fract (x * (b : ℝ) ^ n) := by
      refine lt_of_le_of_ne (Int.fract_nonneg _) fun h0 ↦ ?_
      have heq : x * (b : ℝ) ^ n = ⌊x * (b : ℝ) ^ n⌋ := by
        have := Int.fract_add_floor (x * (b : ℝ) ^ n)
        linarith
      have hbne : ((b : ℝ) ^ n) ≠ 0 := by positivity
      exact hx ⟨(⌊x * (b : ℝ) ^ n⌋ : ℚ) / (b : ℚ) ^ n, by
        push_cast; rw [div_eq_iff hbne]; linarith⟩
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (Int.fract (x * (b : ℝ) ^ n))⁻¹ hb1
    refine ⟨M, fun hall ↦ ?_⟩
    have hlt := mul_pow_lt_one_of_digit_eq_zero (b := b) (by omega)
      (Int.fract_nonneg _) (Int.fract_lt_one _)
      (fun j hj ↦ by rw [← digit_add_eq_digit_fract]; exact hall j hj)
    have : 1 < Int.fract (x * (b : ℝ) ^ n) * (b : ℝ) ^ M := by
      rwa [inv_lt_iff_one_lt_mul₀' hypos] at hM
    linarith
  choose M hM using hfin
  set C : ℝ := (((Finset.range Q₀).sup M : ℕ) : ℝ)
  refine ⟨C, fun n m hm ↦ ?_⟩
  by_cases hn : n < Q₀
  · have hmM : m ≤ M n := by
      by_contra hgt
      exact hM n fun j hj ↦ hm j (by omega)
    have hMC : (M n : ℝ) ≤ C := Nat.cast_le.2 (Finset.le_sup (Finset.mem_range.2 hn))
    have hnn : 0 ≤ (μ - 1) * n := mul_nonneg (by linarith) (Nat.cast_nonneg n)
    linarith [show (m : ℝ) ≤ M n from Nat.cast_le.2 hmM]
  · have hqge : Q₀ ≤ b ^ n := (not_lt.1 hn).trans (Nat.le_of_lt (Nat.lt_pow_self (by omega)))
    have hqpos : 0 < b ^ n := pow_pos (by omega) n
    have hlow := hQ₀ (b ^ n) hqge hqpos ⌊x * (b : ℝ) ^ n⌋
    have hfract : |x - (⌊x * (b : ℝ) ^ n⌋ : ℝ) / (b ^ n : ℕ)| =
        Int.fract (x * (b : ℝ) ^ n) / (b : ℝ) ^ n := by
      have hbne : (b : ℝ) ^ n ≠ 0 := by positivity
      rw [Nat.cast_pow, show x - (⌊x * (b : ℝ) ^ n⌋ : ℝ) / (b : ℝ) ^ n =
        Int.fract (x * (b : ℝ) ^ n) / (b : ℝ) ^ n by
        rw [Int.fract]; field_simp [hbne]]
      exact abs_of_nonneg (div_nonneg (Int.fract_nonneg _) (by positivity))
    have hup : Int.fract (x * (b : ℝ) ^ n) * (b : ℝ) ^ m < 1 :=
      mul_pow_lt_one_of_digit_eq_zero (b := b) (by omega) (Int.fract_nonneg _) (Int.fract_lt_one _)
        (fun j hj ↦ by rw [← digit_add_eq_digit_fract]; exact hm j hj)
    have hlt_pow : (b : ℝ) ^ (n + m) < (b : ℝ) ^ (μ * n) := by
      have h1 : 1 / ((b : ℝ) ^ n) ^ μ < 1 / (b : ℝ) ^ (n + m) := by
        calc 1 / ((b : ℝ) ^ n) ^ μ
            ≤ Int.fract (x * (b : ℝ) ^ n) / (b : ℝ) ^ n := by
              rw [← hfract]; simpa only [Nat.cast_pow] using hlow
          _ < 1 / (b : ℝ) ^ (n + m) := by
              rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_add]
              nlinarith [show (0 : ℝ) < (b : ℝ) ^ n by positivity]
      have h2 : (b : ℝ) ^ (n + m) < ((b : ℝ) ^ n) ^ μ :=
        (one_div_lt_one_div (by positivity) (by positivity)).1 h1
      rwa [← Real.rpow_natCast (b : ℝ) n, ← Real.rpow_mul (by positivity), mul_comm] at h2
    rw [← Real.rpow_natCast (b : ℝ) (n + m)] at hlt_pow
    have hnm : ((n + m : ℕ) : ℝ) < μ * n := (Real.rpow_lt_rpow_left_iff hb1).1 hlt_pow
    push_cast at hnm
    have hC0 : 0 ≤ C := Nat.cast_nonneg _
    linarith

/-- Unconditional digit bound for `e = Real.exp 1`: in every base `b ≥ 2` and for every `ε > 0`,
runs of `m` consecutive zeros starting at position `n` have length at most `(1 + ε) * n + C`. -/
theorem exists_zero_run_le_exp_one {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n m : ℕ, (∀ j < m, digit b (Real.exp 1) (n + j) = 0) →
      (m : ℝ) ≤ (1 + ε) * n + C := by
  have hlt : TauCeti.irrationalityExponent (Real.exp 1) < ENNReal.ofReal (2 + ε) := by
    rw [irrationalityExponent_exp_one, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  obtain ⟨C, hC⟩ := exists_zero_run_le_of_irrationalityExponent_lt hb irrational_exp_one hlt
  refine ⟨C, fun n m hm ↦ ?_⟩
  simpa only [show 2 + ε - 1 = 1 + ε by ring] using hC n m hm

end Real
