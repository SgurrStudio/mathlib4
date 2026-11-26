/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.PrimeProducts
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.Ridout
public import Mathlib.NumberTheory.Normal.Algebraic

/-!
# Runs of equal digits in algebraic numbers are `o(n)`

Borel's conjecture (see `Wanted/NumberTheory/Normal/Basic.lean`) predicts that the base-`b`
expansion of an irrational algebraic number `x` looks random. Liouville's inequality only shows
that a run of zeros starting at position `n` has length `O(n)`. **Ridout's theorem** improves this
to `o(n)`: for every `ε > 0`, eventually every run of zeros, or of the digit `b - 1`, starting at
position `n` has length at most `ε * n`.

A run of `m` zeros at position `n` makes `x` within `b ^ (-(n + m))` of `p / b ^ n` with
`p = ⌊x * b ^ n⌋`. The denominator `b ^ n` is a product of primes dividing `b`, and Ridout's theorem
(`Rat.finite_setOf_ridout`, with the primes of `b` as `S₂`) says only finitely many such
rationals approximate `x` to within `(b ^ n) ^ (-(1 + ε))`. Since `x` is irrational, each of
those finitely many rationals stays a fixed distance from `x`, so for large `n` none of them
occurs. A run of digits `b - 1` gives the approximation `(p + 1) / b ^ n` from above.

## Main statements

* `Real.eventually_lt_abs_sub_div_pow`: for `x` algebraic and irrational, eventually in `n`, every
  `p / b ^ n ∈ [0, 1]` is farther than `(b ^ n) ^ (-(1 + ε))` from `x`.
* `Real.eventually_zero_run_le_mul`: runs of zeros starting at position `n` have length at most
  `ε * n` for large `n`.
* `Real.eventually_pred_run_le_mul`: the same for runs of the digit `b - 1`.

## References

* [D. Ridout, *Rational approximations to algebraic numbers*, Mathematika 4 (1957)]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012], Ch. 8
-/

@[expose] public section

open Filter

namespace Real

variable {b : ℕ} {x : ℝ}

/-- For `y ∈ [0, 1)`, the integer part of `y * b` is the first digit of `y`. -/
private theorem floor_mul_eq_digit (hb : 0 < b) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ⌊y * (b : ℝ) ^ 1⌋ = digit b y 0 := by
  have hnn : 0 ≤ y * (b : ℝ) ^ 1 := by positivity
  have h0 : 0 ≤ ⌊y * (b : ℝ) ^ 1⌋ := Int.floor_nonneg.2 hnn
  have hlt : ⌊y * (b : ℝ) ^ 1⌋ < b := Int.floor_lt.2 (by
    rw [pow_one]; push_cast; nlinarith [(Nat.cast_pos.2 hb : (0 : ℝ) < b)])
  rw [digit, zero_add, Int.emod_eq_of_lt h0 hlt, Int.toNat_of_nonneg h0]

/-- The exponent bookkeeping: `(b ^ n) ^ (-(1 + ε)) < (b ^ (n + m))⁻¹` forces `m ≤ ε * n`. -/
private theorem run_le_of_lt (hb1 : (1 : ℝ) < b) {n m : ℕ} {ε : ℝ}
    (h : ((b : ℝ) ^ n) ^ (-(1 + ε)) < ((b : ℝ) ^ (n + m))⁻¹) : (m : ℝ) ≤ ε * n := by
  have hb0 : (0 : ℝ) ≤ b := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb0, ← Real.rpow_natCast, ← Real.rpow_neg hb0,
    Real.rpow_lt_rpow_left_iff hb1] at h
  push_cast at h
  nlinarith

/-- If the first `m` base-`b` digits of `y ∈ [0, 1)` are all `b - 1`, then
`(1 - y) * b ^ m ≤ 1`. -/
private theorem one_sub_mul_pow_le_one_of_digit_eq_pred (hb : 0 < b) {m : ℕ} :
    ∀ {y : ℝ}, 0 ≤ y → y < 1 → (∀ j < m, digit b y j = b - 1) → (1 - y) * (b : ℝ) ^ m ≤ 1 := by
  induction m with
  | zero => intro y hy0 _ _; simpa using hy0
  | succ m ih =>
    intro y hy0 hy1 h
    have hz := ih (Int.fract_nonneg (y * (b : ℝ) ^ 1)) (Int.fract_lt_one _) fun j hj ↦ by
      rw [← digit_add_eq_digit_fract, add_comm]; exact h (j + 1) (by omega)
    have hfl := floor_mul_eq_digit hb hy0 hy1
    rw [h 0 (by omega)] at hfl
    have hy : (1 - y) * (b : ℝ) ^ 1 = 1 - Int.fract (y * (b : ℝ) ^ 1) := by
      rw [Int.fract, hfl, Nat.cast_sub (by omega : 1 ≤ b)]
      push_cast
      ring
    rwa [show (1 - y) * (b : ℝ) ^ (m + 1) = (1 - y) * (b : ℝ) ^ 1 * (b : ℝ) ^ m by ring, hy]

/-- **Ridout's theorem for `b`-adic approximations.** For `x` algebraic and irrational, `b ≥ 2` and
`ε > 0`, eventually in `n` every rational `p / b ^ n` with `0 ≤ p ≤ b ^ n` is farther than
`(b ^ n) ^ (-(1 + ε))` from `x`. -/
theorem eventually_lt_abs_sub_div_pow (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x) (hx : Irrational x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℤ, 0 ≤ p → p ≤ (b : ℤ) ^ n →
      ((b : ℝ) ^ n) ^ (-(1 + ε)) < |x - p / (b : ℝ) ^ n| := by
  classical
  have hb0 : b ≠ 0 := by omega
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  set R := {β : ℚ | |x - (β : ℝ)|
      * (∏ l ∈ (∅ : Finset Nat.Primes), ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
      * ∏ l ∈ b.primesOf, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
    ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)} with hRdef
  have hR : R.Finite := Rat.finite_setOf_ridout halg ∅ b.primesOf hε
  have hev : ∀ β ∈ R, ∀ᶠ n : ℕ in atTop, ((b : ℝ) ^ n)⁻¹ < |x - (β : ℝ)| := fun β _ ↦
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb1)).eventually
      (gt_mem_nhds (abs_pos.2 (sub_ne_zero.2 (hx.ne_rat β))))
  filter_upwards [hR.eventually_all.2 hev] with n hn p hp0 hpb
  by_contra! hle
  have hB : (1 : ℝ) ≤ (b : ℝ) ^ n := one_le_pow₀ hb1.le
  set β : ℚ := p / ((b ^ n : ℕ) : ℚ) with hβdef
  have hβR : (β : ℝ) = p / (b : ℝ) ^ n := by rw [hβdef]; push_cast; rfl
  rw [← hβR] at hle
  refine (hn β ?_).not_ge (hle.trans ?_)
  swap
  · calc ((b : ℝ) ^ n) ^ (-(1 + ε)) ≤ ((b : ℝ) ^ n) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      _ = ((b : ℝ) ^ n)⁻¹ := Real.rpow_neg_one _
  -- `β` is a solution of Ridout's inequality
  have hbn0 : b ^ n ≠ 0 := pow_ne_zero _ hb0
  have hden_dvd : β.den ∣ b ^ n := by
    have hβ' : β = Rat.divInt p ((b ^ n : ℕ) : ℤ) := by
      rw [Rat.divInt_eq_div, hβdef]; push_cast; rfl
    rw [hβ']
    exact_mod_cast Rat.den_dvd p ((b ^ n : ℕ) : ℤ)
  have hden_le : (β.den : ℝ) ≤ (b : ℝ) ^ n := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hbn0) hden_dvd
  have hD0 : (0 : ℝ) < β.den := by exact_mod_cast β.den_pos
  have hβ0 : 0 ≤ β := div_nonneg (by exact_mod_cast hp0) (Nat.cast_nonneg _)
  have hβ1 : β ≤ 1 := by
    rw [hβdef, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hbn0)]
    exact_mod_cast hpb
  have hnum : β.num.natAbs ≤ β.den := by
    have h := Rat.mul_den_eq_num β
    have : (β.num.natAbs : ℚ) ≤ β.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← h, abs_mul, abs_of_nonneg hβ0, Nat.abs_cast]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _) hβ1
    exact_mod_cast this
  have hprod : ∏ l ∈ b.primesOf, ((padicNorm (l : ℕ) (β.den : ℚ) : ℚ) : ℝ) = (β.den : ℝ)⁻¹ := by
    rw [← Rat.cast_prod, Rat.prod_padicNorm_natCast _ β.den β.den_nz
      fun l hl ↦ Nat.mem_primesOf_of_dvd_pow hb0 (hl.trans hden_dvd)]
    push_cast
    rfl
  rw [hRdef, Set.mem_ofPred_eq, Finset.prod_empty, mul_one, hprod,
    max_eq_right (by exact_mod_cast hnum)]
  calc |x - (β : ℝ)| * (β.den : ℝ)⁻¹ ≤ (β.den : ℝ) ^ (-(1 + ε)) * (β.den : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        gcongr
        exact hle.trans (Real.rpow_le_rpow_of_nonpos hD0 hden_le (by linarith))
    _ = (β.den : ℝ) ^ (-2 - ε) := by
        rw [← Real.rpow_add hD0]
        ring_nf

/-- **Zero runs in algebraic numbers are `o(n)`** (Ridout). For `x` algebraic and irrational,
`b ≥ 2` and `ε > 0`, eventually in `n` every run of zeros in the base-`b` expansion of `x`
starting at position `n` has length at most `ε * n`. This strengthens the Liouville bound
`(d - 1) * n + C`. -/
theorem eventually_zero_run_le_mul (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x) (hx : Irrational x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (∀ j < m, digit b x (n + j) = 0) → (m : ℝ) ≤ ε * n := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : 0 < b := by omega
  set y := Int.fract x with hy
  have halg' : IsAlgebraic ℚ y := halg.sub (isAlgebraic_intCast _)
  filter_upwards [eventually_lt_abs_sub_div_pow hb halg' (hx.sub_intCast _) hε] with n hn m hrun
  have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hy0 : 0 ≤ y * (b : ℝ) ^ n := mul_nonneg (Int.fract_nonneg x) hBn.le
  have hyb : y * (b : ℝ) ^ n < (b : ℝ) ^ n := by
    nlinarith [Int.fract_lt_one x]
  have h := hn ⌊y * (b : ℝ) ^ n⌋ (Int.floor_nonneg.2 hy0) (by
    have : (⌊y * (b : ℝ) ^ n⌋ : ℝ) ≤ (b : ℝ) ^ n := (Int.floor_le _).trans hyb.le
    exact_mod_cast this)
  exact run_le_of_lt hb1 (h.trans (abs_sub_floor_div_lt_of_digit_eq_zero hb0 fun j hj ↦ by
    rw [hy, digit_fract]; exact hrun j hj))

/-- **Runs of the digit `b - 1` in algebraic numbers are `o(n)`** (Ridout). -/
theorem eventually_pred_run_le_mul (hb : 2 ≤ b) (halg : IsAlgebraic ℚ x) (hx : Irrational x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (∀ j < m, digit b x (n + j) = b - 1) → (m : ℝ) ≤ ε * n := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : 0 < b := by omega
  set y := Int.fract x with hy
  have halg' : IsAlgebraic ℚ y := halg.sub (isAlgebraic_intCast _)
  filter_upwards [eventually_lt_abs_sub_div_pow hb halg' (hx.sub_intCast _) hε] with n hn m hrun
  have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  set z := Int.fract (y * (b : ℝ) ^ n)
  have hz := one_sub_mul_pow_le_one_of_digit_eq_pred hb0 (Int.fract_nonneg (y * (b : ℝ) ^ n))
    (Int.fract_lt_one _) (m := m) fun j hj ↦ by
      rw [← digit_add_eq_digit_fract, hy, digit_fract]; exact hrun j hj
  have hy0 : 0 ≤ y * (b : ℝ) ^ n := mul_nonneg (Int.fract_nonneg x) hBn.le
  have hyb : y * (b : ℝ) ^ n < (b : ℝ) ^ n := by
    nlinarith [Int.fract_lt_one x]
  have h := hn (⌊y * (b : ℝ) ^ n⌋ + 1) (by linarith [Int.floor_nonneg.2 hy0]) (by
    have : ⌊y * (b : ℝ) ^ n⌋ < (b : ℤ) ^ n := Int.floor_lt.2 (by exact_mod_cast hyb)
    omega)
  have heq : |y - ((⌊y * (b : ℝ) ^ n⌋ + 1 : ℤ) : ℝ) / (b : ℝ) ^ n|
      = (1 - z) * ((b : ℝ) ^ n)⁻¹ := by
    rw [abs_sub_comm, abs_of_nonneg]
    · simp only [z, Int.fract]; push_cast; field_simp; ring
    · rw [sub_nonneg, le_div_iff₀ hBn]; push_cast; exact (Int.lt_floor_add_one _).le
  rw [heq] at h
  refine run_le_of_lt hb1 (h.trans_le ?_)
  rw [pow_add, mul_inv, mul_comm]
  gcongr
  rw [← one_div, le_div_iff₀ (by positivity)]
  exact hz

end Real
