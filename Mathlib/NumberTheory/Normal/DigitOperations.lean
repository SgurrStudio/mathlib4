/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.CopelandErdos

/-!
# Digit operations and subsequence preservation for normal numbers

We establish invariance and non-preservation results for base-`b` normal numbers under digit
modifications, digit permutations, and subsequence extractions:

## Main statements

* `Real.isNormalSeq_of_density_zero_diff`, `Real.isNormalIn_of_density_zero_digit_diff`:
  modifying a set of digits of asymptotic density `0` preserves normality in base `b`.
* `Real.isNormalIn_of_eventually_digit_eq`: modifying finitely many digits preserves normality.
* `Real.isNormalSeq_comp_equiv`, `Real.isNormalIn_ofDigits_comp_equiv`: permuting the digit
  alphabet `Fin b` preserves normality in base `b`.
* `Real.exists_isNormalIn_digit_eq_zero_on_density_zero`: for any set of positions of density `0`,
  there exists a base-`b` normal number whose digits vanish on that set.
* `Real.not_preserves_isNormalSeq_of_density_zero`: no subsequence whose range has density `0`
  preserves normality, in particular along squares (`Real.exists_isNormalIn_not_isNormalSeq_sq`)
  and powers of two (`Real.exists_isNormalIn_not_isNormalSeq_two_pow`).
* `Real.exists_strictMono_positive_density_digit_eq_zero`: for every base-`b` normal number `x`,
  there exists a strictly increasing subsequence of density `1 / b` along which all digits of `x`
  are `0` (hence not normal), showing that positive density alone does not guarantee normality
  preservation.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- Modifying a digit sequence on a set of positions of asymptotic density `0` preserves
normality in base `b`. -/
theorem isNormalSeq_of_density_zero_diff {d₁ d₂ : ℕ → ℕ} (h₁ : IsNormalSeq b d₁)
    (hd : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ d₁ i ≠ d₂ i).card : ℝ) / N) atTop (𝓝 0)) :
    IsNormalSeq b d₂ := by sorry

/-- If `x` is normal in base `b` and the set of positions where `x` and `y` have different base-`b`
digits has asymptotic density `0`, then `y` is also normal in base `b`. -/
theorem isNormalIn_of_density_zero_digit_diff (_hb : 2 ≤ b) {x y : ℝ} (hx : IsNormalIn b x)
    (hd : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ digit b x i ≠ digit b y i).card : ℝ) / N)
      atTop (𝓝 0)) :
    IsNormalIn b y := by sorry

/-- If `x` is normal in base `b` and `y` eventually has the same base-`b` digits as `x`, then `y`
is normal in base `b`. -/
theorem isNormalIn_of_eventually_digit_eq (hb : 2 ≤ b) {x y : ℝ} (hx : IsNormalIn b x)
    (heq : ∀ᶠ i in atTop, digit b x i = digit b y i) :
    IsNormalIn b y := by sorry

/-- Permuting the base-`b` digits of a normal number produces a normal digit sequence. -/
theorem isNormalSeq_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (σ ⟨digit b x n, digit_lt (by omega) x n⟩ : ℕ) := by sorry

/-- Permuting the base-`b` digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩) := by sorry

/-- If a digit sequence `d : ℕ → Fin b` is normal in base `b ≥ 2`, then it is the base-`b` digit
expansion of `ofDigits d`. -/
theorem digit_ofDigits_of_isNormalSeq (hb : 2 ≤ b) {d : ℕ → Fin b}
    (h : IsNormalSeq b fun n ↦ d n) (n : ℕ) :
    digit b (ofDigits d) n = d n := by sorry

/-- For any set of positions of asymptotic density `0`, there exists a number normal in base `b`
whose base-`b` digits vanish at all positions in that set. -/
theorem exists_isNormalIn_digit_eq_zero_on_density_zero (hb : 2 ≤ b) (P : ℕ → Prop)
    [DecidablePred P]
    (hP : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter P).card : ℝ) / N) atTop (𝓝 0)) :
    ∃ x : ℝ, IsNormalIn b x ∧ ∀ n, P n → digit b x n = 0 := by sorry

/-- A constant-zero digit sequence is not normal in any base `b ≥ 2`. -/
theorem not_isNormalSeq_of_forall_eq_zero (hb : 2 ≤ b) {d : ℕ → ℕ} (hd : ∀ n, d n = 0) :
    ¬ IsNormalSeq b d := by sorry

/-- No subsequence whose range has asymptotic density `0` preserves normality in base `b ≥ 2`. -/
theorem not_preserves_isNormalSeq_of_density_zero (hb : 2 ≤ b) {s : ℕ → ℕ}
    [DecidablePred fun n ↦ n ∈ Set.range s]
    (hs : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ n ∈ Set.range s).card : ℝ) / N) atTop (𝓝 0)) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalSeq b (fun n ↦ digit b x (s n)) := by sorry

/-- Extracting digits at square indices does not preserve normality in base `b ≥ 2`. -/
theorem exists_isNormalIn_not_isNormalSeq_sq (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalSeq b (fun n ↦ digit b x (n ^ 2)) := by sorry

/-- Extracting digits at power-of-two indices does not preserve normality in base `b ≥ 2`. -/
theorem exists_isNormalIn_not_isNormalSeq_two_pow (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalSeq b (fun n ↦ digit b x (2 ^ n)) := by sorry

open Classical in
/-- For every number `x` normal in base `b ≥ 2`, there exists a strictly increasing subsequence
whose range has positive asymptotic density `1 / b` along which all base-`b` digits of `x` are `0`
(and hence the extracted digit sequence is not normal). This shows that positive density alone
does not guarantee preservation of normality. -/
theorem exists_strictMono_positive_density_digit_eq_zero (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      Tendsto (fun N : ℕ ↦
        (((Finset.range N).filter fun n ↦ n ∈ Set.range s).card : ℝ) / N)
        atTop (𝓝 (1 / (b : ℝ))) ∧
      (∀ n, digit b x (s n) = 0) ∧
      ¬ IsNormalSeq b (fun n ↦ digit b x (s n)) := by sorry

end Real
