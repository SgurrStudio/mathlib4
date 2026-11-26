/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Imported.SubspaceTheorems.DiophantineApproximation.FactorComplexity
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.NumberTheory.Normal.Exp

/-!
# Morse–Hedlund digit complexity lower bounds for irrationals, `π`, and `e`

A normal number in base `b` has maximal block complexity `p(n) = b ^ n`. For transcendental
constants such as `π` and `e = exp 1` (unlike algebraic irrationals, where Adamczewski–Bugeaud
gives `p(n) / n → ∞`, see `Mathlib/NumberTheory/Normal/Complexity.lean`), the strongest general
unconditional lower bound on block complexity comes from **Morse–Hedlund's theorem** (1938): every
irrational real number has at least `n + 1` distinct base-`b` blocks of length `n`.

## Main statements

* `Real.not_isEventuallyPeriodic_digit`: the base-`b` digit sequence of an irrational real number
  is not eventually periodic.
* `Real.succ_le_complexity_digit`: for every irrational `x` and base `b ≥ 2`,
  `n + 1 ≤ Function.complexity (digit b x) n`.
* `Real.succ_le_complexity_digit_pi`: Morse–Hedlund lower bound for `π`.
* `Real.succ_le_complexity_digit_exp_one`: Morse–Hedlund lower bound for `e = exp 1`.

## References

* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

namespace Real

private lemma floor_mul_ediv {b : ℕ} (hb : 0 < b) (u : ℝ) :
    ⌊u * (b : ℝ)⌋ / (b : ℤ) = ⌊u⌋ := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbZ : (0 : ℤ) < b := Nat.cast_pos.2 hb
  refine le_antisymm ?_ ?_
  · rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hbZ]
    have hlt : u * (b : ℝ) < ((⌊u⌋ : ℝ) + 1) * b :=
      mul_lt_mul_of_pos_right (Int.lt_floor_add_one u) hb'
    exact Int.floor_lt.2 (by push_cast; exact hlt)
  · rw [Int.le_ediv_iff_mul_le hbZ]
    have hle : (⌊u⌋ : ℝ) * b ≤ u * (b : ℝ) :=
      mul_le_mul_of_nonneg_right (Int.floor_le u) hb'.le
    exact Int.le_floor.2 (by exact_mod_cast hle)

private lemma eq_of_digit_eq {b : ℕ} (hb : 2 ≤ b) {y z : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (h : ∀ j : ℕ, digit b y j = digit b z j) : y = z := by
  have hfl : ∀ m : ℕ, ⌊y * (b : ℝ) ^ m⌋ = ⌊z * (b : ℝ) ^ m⌋ := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, mul_one]
      rw [Int.floor_eq_zero_iff.2 ⟨hy0, hy1⟩, Int.floor_eq_zero_iff.2 ⟨hz0, hz1⟩]
    | succ m ih =>
      have hdivy : ⌊y * (b : ℝ) ^ (m + 1)⌋ / (b : ℤ) = ⌊y * (b : ℝ) ^ m⌋ := by
        rw [pow_succ, ← mul_assoc]; exact floor_mul_ediv (by omega) _
      have hdivz : ⌊z * (b : ℝ) ^ (m + 1)⌋ / (b : ℤ) = ⌊z * (b : ℝ) ^ m⌋ := by
        rw [pow_succ, ← mul_assoc]; exact floor_mul_ediv (by omega) _
      have hmod : ⌊y * (b : ℝ) ^ (m + 1)⌋ % (b : ℤ) = ⌊z * (b : ℝ) ^ (m + 1)⌋ % (b : ℤ) := by
        have hm := h m
        simp only [digit] at hm
        have hbZ : (0 : ℤ) < b := by exact_mod_cast (by omega : 0 < b)
        have hny := Int.emod_nonneg ⌊y * (b : ℝ) ^ (m + 1)⌋ hbZ.ne'
        have hnz := Int.emod_nonneg ⌊z * (b : ℝ) ^ (m + 1)⌋ hbZ.ne'
        omega
      rw [← Int.mul_ediv_add_emod ⌊y * (b : ℝ) ^ (m + 1)⌋ b,
          ← Int.mul_ediv_add_emod ⌊z * (b : ℝ) ^ (m + 1)⌋ b, hdivy, hdivz, ih, hmod]
  by_contra hne
  have hpos : 0 < |y - z| := abs_sub_pos.2 hne
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt |y - z|⁻¹ (by exact_mod_cast hb : (1 : ℝ) < b)
  have h1 : 1 < |y - z| * (b : ℝ) ^ m := (inv_lt_iff_one_lt_mul₀' hpos).1 hm
  have h2 : |y - z| * (b : ℝ) ^ m < 1 := by
    rw [← abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) ^ m), ← abs_mul, sub_mul]
    have hy_le : (⌊y * (b : ℝ) ^ m⌋ : ℝ) ≤ y * (b : ℝ) ^ m := Int.floor_le _
    have hy_lt : y * (b : ℝ) ^ m < ⌊y * (b : ℝ) ^ m⌋ + 1 := Int.lt_floor_add_one _
    have hz_le : (⌊z * (b : ℝ) ^ m⌋ : ℝ) ≤ z * (b : ℝ) ^ m := Int.floor_le _
    have hz_lt : z * (b : ℝ) ^ m < ⌊z * (b : ℝ) ^ m⌋ + 1 := Int.lt_floor_add_one _
    rw [hfl m] at hy_le hy_lt
    rw [abs_lt]
    constructor <;> linarith
  linarith

/-- The base-`b` digit sequence of an irrational number is not eventually periodic. -/
theorem not_isEventuallyPeriodic_digit {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : Irrational x) :
    ¬ Function.IsEventuallyPeriodic (digit b x) := by
  rintro ⟨r, s, hs, hper⟩
  have hfr : Int.fract (x * (b : ℝ) ^ r) = Int.fract (x * (b : ℝ) ^ (r + s)) := by
    refine eq_of_digit_eq hb (Int.fract_nonneg _) (Int.fract_lt_one _)
      (Int.fract_nonneg _) (Int.fract_lt_one _) fun j ↦ ?_
    rw [← digit_add_eq_digit_fract, ← digit_add_eq_digit_fract,
      show r + s + j = r + j + s by omega]
    exact (hper (r + j) (Nat.le_add_right r j)).symm
  have hpow_ne : ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) ≠ 0 := by
    have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
    have hlt : (b : ℝ) ^ r < (b : ℝ) ^ (r + s) :=
      pow_lt_pow_right₀ hb1 (by omega)
    linarith
  have hint : x * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) =
      (⌊x * (b : ℝ) ^ (r + s)⌋ - ⌊x * (b : ℝ) ^ r⌋ : ℤ) := by
    push_cast
    have h1 := Int.fract_add_floor (x * (b : ℝ) ^ r)
    have h2 := Int.fract_add_floor (x * (b : ℝ) ^ (r + s))
    linarith
  exact hx ⟨((⌊x * (b : ℝ) ^ (r + s)⌋ - ⌊x * (b : ℝ) ^ r⌋ : ℤ) : ℚ) /
      ((b : ℚ) ^ (r + s) - (b : ℚ) ^ r), by
    push_cast
    rw [div_eq_iff hpow_ne]
    exact_mod_cast hint.symm⟩

/-- **Morse–Hedlund theorem for `Real.digit`**: in any base `b ≥ 2`, an irrational real number has
at least `n + 1` distinct blocks of `n` consecutive digits. -/
theorem succ_le_complexity_digit {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : Irrational x) (n : ℕ) :
    n + 1 ≤ Function.complexity (digit b x) n := by
  let a : ℕ → Fin b := fun i ↦ ⟨digit b x i, digit_lt (by omega) x i⟩
  have ha : ¬ Function.IsEventuallyPeriodic a := by
    rintro ⟨r, s, hs, hper⟩
    exact not_isEventuallyPeriodic_digit hb hx ⟨r, s, hs, fun k hk ↦ congrArg Fin.val (hper k hk)⟩
  have hlt : n < Function.complexity a n := Function.lt_complexity ha n
  have hc : Function.complexity (digit b x) n = Function.complexity a n := by
    have hd : digit b x = Fin.val ∘ a := rfl
    rw [hd]
    unfold Function.complexity Function.factors
    rw [show (Set.range fun i ↦ Function.factor (Fin.val ∘ a) i n) =
        List.map Fin.val '' Set.range fun i ↦ Function.factor a i n by
      rw [← Set.range_comp]; congr 1; funext i
      simp [Function.factor, List.map_ofFn]; rfl]
    exact Set.ncard_image_of_injective _ (List.map_injective_iff.2 Fin.val_injective)
  omega

/-- In every base `b ≥ 2`, `π` has at least `n + 1` distinct blocks of `n` consecutive digits. -/
theorem succ_le_complexity_digit_pi {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    n + 1 ≤ Function.complexity (digit b π) n :=
  succ_le_complexity_digit hb irrational_pi n

/-- In every base `b ≥ 2`, `e = exp 1` has at least `n + 1` distinct blocks of `n` consecutive
digits. -/
theorem succ_le_complexity_digit_exp_one {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    n + 1 ≤ Function.complexity (digit b (Real.exp 1)) n :=
  succ_le_complexity_digit hb irrational_exp_one n

end Real
