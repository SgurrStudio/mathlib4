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
    IsNormalSeq b d₂ := by
  intro k w
  set A : ℕ → Finset ℕ := fun N ↦ (Finset.range N).filter fun i ↦ ∀ j : Fin k, d₁ (i + j) = w j
  set B : ℕ → Finset ℕ := fun N ↦ (Finset.range N).filter fun i ↦ ∀ j : Fin k, d₂ (i + j) = w j
  set D : ℕ → Finset ℕ := fun M ↦ (Finset.range M).filter fun i ↦ d₁ i ≠ d₂ i
  have hsub : ∀ N, (A N \ B N).card ≤ k * (D (N + k)).card ∧
      (B N \ A N).card ≤ k * (D (N + k)).card := by
    intro N
    set U := (Finset.range k).biUnion fun j ↦ (D (N + k)).image fun m ↦ m - j
    have hU : U.card ≤ k * (D (N + k)).card := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ j ∈ Finset.range k, ((D (N + k)).image fun m ↦ m - j).card
          ≤ ∑ _j ∈ Finset.range k, (D (N + k)).card :=
            Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le
        _ = k * (D (N + k)).card := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hdiff : ∀ i ∈ Finset.range N, (∃ j : Fin k, d₁ (i + j) ≠ d₂ (i + j)) → i ∈ U := by
      rintro i hi ⟨j, hj⟩
      simp only [U, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
      refine ⟨j, j.isLt, i + j, ?_, Nat.add_sub_cancel i j⟩
      simp only [D, Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := Finset.mem_range.1 hi; omega, hj⟩
    constructor
    · refine (Finset.card_le_card fun i hi ↦ ?_).trans hU
      rw [Finset.mem_sdiff] at hi
      simp only [A, B, Finset.mem_filter, Finset.mem_range] at hi
      refine hdiff i (Finset.mem_range.2 hi.1.1) ?_
      by_contra! hall
      exact hi.2 ⟨hi.1.1, fun j ↦ (hall j).symm.trans (hi.1.2 j)⟩
    · refine (Finset.card_le_card fun i hi ↦ ?_).trans hU
      rw [Finset.mem_sdiff] at hi
      simp only [A, B, Finset.mem_filter, Finset.mem_range] at hi
      refine hdiff i (Finset.mem_range.2 hi.1.1) ?_
      by_contra! hall
      exact hi.2 ⟨hi.1.1, fun j ↦ (hall j).trans (hi.1.2 j)⟩
  have habs : ∀ N, |((B N).card : ℝ) - ((A N).card : ℝ)| ≤ (k : ℝ) * ((D (N + k)).card : ℝ) := by
    intro N
    have h1 : (A N).card ≤ (A N \ B N).card + (B N).card :=
      Finset.card_le_card_sdiff_add_card
    have h2 : (B N).card ≤ (B N \ A N).card + (A N).card :=
      Finset.card_le_card_sdiff_add_card
    obtain ⟨hAB, hBA⟩ := hsub N
    have hAB' : ((A N \ B N).card : ℝ) ≤ (k : ℝ) * ((D (N + k)).card : ℝ) := by exact_mod_cast hAB
    have hBA' : ((B N \ A N).card : ℝ) ≤ (k : ℝ) * ((D (N + k)).card : ℝ) := by exact_mod_cast hBA
    have h1' : ((A N).card : ℝ) ≤ ((A N \ B N).card : ℝ) + ((B N).card : ℝ) := by
      exact_mod_cast h1
    have h2' : ((B N).card : ℝ) ≤ ((B N \ A N).card : ℝ) + ((A N).card : ℝ) := by
      exact_mod_cast h2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hratio : Tendsto (fun N : ℕ ↦ ((N : ℝ) + k) / N) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)).const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [add_div, div_self (by exact_mod_cast hN.ne')]
  have hD_shift : Tendsto (fun N : ℕ ↦ ((D (N + k)).card : ℝ) / N) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun N : ℕ ↦ ((D (N + k)).card : ℝ) / ((N + k : ℕ) : ℝ)) atTop (𝓝 0) :=
      hd.comp (tendsto_add_atTop_nat k)
    have hmul := hcomp.mul hratio
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hNk : (N : ℝ) + k ≠ 0 := by positivity
    push_cast
    field_simp
  have hdiff_zero : Tendsto (fun N : ℕ ↦
      ((B N).card : ℝ) / N - ((A N).card : ℝ) / N) atTop (𝓝 0) := by
    have hbd : Tendsto (fun N : ℕ ↦ (k : ℝ) * (((D (N + k)).card : ℝ) / N)) atTop (𝓝 0) := by
      simpa using hD_shift.const_mul (k : ℝ)
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hNpos, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (habs N) hNpos.le
  have hsum := (h₁ k w).add hdiff_zero
  rw [add_zero] at hsum
  refine hsum.congr fun N ↦ ?_
  simp only [A, B]
  ring

/-- If `x` is normal in base `b` and the set of positions where `x` and `y` have different base-`b`
digits has asymptotic density `0`, then `y` is also normal in base `b`. -/
theorem isNormalIn_of_density_zero_digit_diff (_hb : 2 ≤ b) {x y : ℝ} (hx : IsNormalIn b x)
    (hd : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ digit b x i ≠ digit b y i).card : ℝ) / N)
      atTop (𝓝 0)) :
    IsNormalIn b y :=
  isNormalIn_iff_isNormalSeq.2
    (isNormalSeq_of_density_zero_diff (isNormalIn_iff_isNormalSeq.1 hx) hd)

/-- If `x` is normal in base `b` and `y` eventually has the same base-`b` digits as `x`, then `y`
is normal in base `b`. -/
theorem isNormalIn_of_eventually_digit_eq (hb : 2 ≤ b) {x y : ℝ} (hx : IsNormalIn b x)
    (heq : ∀ᶠ i in atTop, digit b x i = digit b y i) :
    IsNormalIn b y := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 heq
  refine isNormalIn_of_density_zero_digit_diff hb hx ?_
  refine squeeze_zero (fun N ↦ by positivity) (fun N ↦ ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (M : ℝ))
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  have hsub : ((Finset.range N).filter fun i ↦ digit b x i ≠ digit b y i) ⊆ Finset.range M := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    by_contra h
    exact hi.2 (hM i (by omega))
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_range M).le

/-- Permuting the base-`b` digits of a normal number produces a normal digit sequence. -/
theorem isNormalSeq_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (σ ⟨digit b x n, digit_lt (by omega) x n⟩ : ℕ) := by
  intro k w
  have h := hx k (σ.symm ∘ w)
  refine h.congr fun N ↦ ?_
  congr 2
  rw [blockCount]
  refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
  refine forall_congr' fun j ↦ ?_
  simp only [Function.comp_apply]
  have h1 : (σ ⟨digit b x (i + j), digit_lt (by omega) x (i + j)⟩ : ℕ) = (w j : ℕ) ↔
      σ ⟨digit b x (i + j), digit_lt (by omega) x (i + j)⟩ = w j := Fin.val_inj
  have h2 : digit b x (i + j) = (σ.symm (w j) : ℕ) ↔
      (⟨digit b x (i + j), digit_lt (by omega) x (i + j)⟩ : Fin b) = σ.symm (w j) := by
    simp [Fin.ext_iff]
  rw [h1, h2, ← Equiv.eq_symm_apply]

/-- Permuting the base-`b` digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_comp_equiv (hb : 2 ≤ b) (σ : Equiv.Perm (Fin b))
    (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦ σ ⟨digit b x n, digit_lt (by omega) x n⟩) :=
  isNormalIn_ofDigits hb (isNormalSeq_comp_equiv hb σ hx)

/-- If a digit sequence `d : ℕ → Fin b` is normal in base `b ≥ 2`, then it is the base-`b` digit
expansion of `ofDigits d`. -/
theorem digit_ofDigits_of_isNormalSeq (hb : 2 ≤ b) {d : ℕ → Fin b}
    (h : IsNormalSeq b fun n ↦ d n) (n : ℕ) :
    digit b (ofDigits d) n = d n := by
  refine digit_ofDigits (by omega) d ?_ n
  by_contra! hcon
  obtain ⟨m, hm⟩ := hcon
  have h0 := h 1 fun _ ↦ ⟨0, by omega⟩
  have hle : ∀ N, (((Finset.range N).filter fun i ↦
      ∀ j : Fin 1, (d (i + j) : ℕ) = ((fun _ ↦ (⟨0, by omega⟩ : Fin b)) j : ℕ)).card : ℝ) ≤
      m + 1 := fun N ↦ by
    have hsub : ((Finset.range N).filter fun i ↦
        ∀ j : Fin 1, (d (i + j) : ℕ) = ((fun _ ↦ (⟨0, by omega⟩ : Fin b)) j : ℕ)) ⊆
        Finset.range (m + 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Fin.forall_fin_one, Fin.val_zero,
        add_zero] at hi
      by_contra him
      have := hm i (by simp at him; omega)
      omega
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_range _).le
  have h1 : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun i ↦
      ∀ j : Fin 1, (d (i + j) : ℕ) = ((fun _ ↦ (⟨0, by omega⟩ : Fin b)) j : ℕ)).card : ℝ) / N)
      atTop (𝓝 0) :=
    squeeze_zero (fun N ↦ by positivity) (fun N ↦ div_le_div_of_nonneg_right (hle N)
      (Nat.cast_nonneg N)) (tendsto_const_div_atTop_nhds_zero_nat _)
  have := tendsto_nhds_unique h0 h1
  simp at this
  omega

/-- For any set of positions of asymptotic density `0`, there exists a number normal in base `b`
whose base-`b` digits vanish at all positions in that set. -/
theorem exists_isNormalIn_digit_eq_zero_on_density_zero (hb : 2 ≤ b) (P : ℕ → Prop)
    [DecidablePred P]
    (hP : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter P).card : ℝ) / N) atTop (𝓝 0)) :
    ∃ x : ℝ, IsNormalIn b x ∧ ∀ n, P n → digit b x n = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_isAbsolutelyNormal
  have hx₀b : IsNormalIn b x₀ := hx₀ b hb
  let d : ℕ → Fin b := fun n ↦
    if P n then ⟨0, by omega⟩ else ⟨digit b x₀ n, digit_lt (by omega) x₀ n⟩
  have hdiff : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ digit b x₀ i ≠ (d i : ℕ)).card : ℝ) / N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N ↦ by positivity) (fun N ↦ ?_) hP
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    have hsub : ((Finset.range N).filter fun i ↦ digit b x₀ i ≠ (d i : ℕ)) ⊆
        (Finset.range N).filter P := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      refine ⟨hi.1, ?_⟩
      by_contra hPi
      exact hi.2 (by simp [d, hPi])
    exact_mod_cast Finset.card_le_card hsub
  have hd_norm : IsNormalSeq b fun n ↦ (d n : ℕ) :=
    isNormalSeq_of_density_zero_diff (isNormalIn_iff_isNormalSeq.1 hx₀b) hdiff
  refine ⟨ofDigits d, isNormalIn_ofDigits hb hd_norm, fun n hn ↦ ?_⟩
  rw [digit_ofDigits_of_isNormalSeq hb hd_norm n]
  simp [d, hn]

/-- A constant-zero digit sequence is not normal in any base `b ≥ 2`. -/
theorem not_isNormalSeq_of_forall_eq_zero (hb : 2 ≤ b) {d : ℕ → ℕ} (hd : ∀ n, d n = 0) :
    ¬ IsNormalSeq b d := by
  intro h
  have h1 := h 1 fun _ ↦ ⟨1, by omega⟩
  have h0 : ∀ N, ((Finset.range N).filter fun i ↦
      ∀ j : Fin 1, d (i + j) = ((fun _ ↦ (⟨1, by omega⟩ : Fin b)) j : ℕ)).card = 0 := fun N ↦ by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    have := hi 0
    simp [hd] at this
  simp only [h0, Nat.cast_zero, zero_div] at h1
  have hb0 : ((b : ℝ) ^ 1)⁻¹ ≠ 0 := by
    simp only [pow_one, ne_eq, inv_eq_zero, Nat.cast_eq_zero]
    omega
  exact hb0 (tendsto_nhds_unique tendsto_const_nhds h1).symm

/-- No subsequence whose range has asymptotic density `0` preserves normality in base `b ≥ 2`. -/
theorem not_preserves_isNormalSeq_of_density_zero (hb : 2 ≤ b) {s : ℕ → ℕ}
    [DecidablePred fun n ↦ n ∈ Set.range s]
    (hs : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ n ∈ Set.range s).card : ℝ) / N) atTop (𝓝 0)) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalSeq b (fun n ↦ digit b x (s n)) := by
  obtain ⟨x, hx, h0⟩ :=
    exists_isNormalIn_digit_eq_zero_on_density_zero hb (fun n ↦ n ∈ Set.range s) hs
  exact ⟨x, hx, not_isNormalSeq_of_forall_eq_zero hb fun n ↦ h0 (s n) ⟨n, rfl⟩⟩

private theorem tendsto_natSqrt_div_atTop :
    Tendsto (fun N : ℕ ↦ (Nat.sqrt N : ℝ) / N) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun ε hε ↦ Eventually.of_forall fun N ↦ hε.trans_le (by positivity), fun ε hε ↦ ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := (by positivity : (0 : ℝ) < 1 / ε).trans hK
    exact_mod_cast this
  filter_upwards [eventually_ge_atTop (K ^ 2)] with N hN
  have hKN : K ≤ Nat.sqrt N := Nat.le_sqrt.2 (by simpa [sq] using hN)
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos hKpos 2) hN
  have hmul : Nat.sqrt N * K ≤ N :=
    (Nat.mul_le_mul_left _ hKN).trans (Nat.sqrt_le N)
  have hmul' : (Nat.sqrt N : ℝ) * K ≤ N := by exact_mod_cast hmul
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1 : 1 < (K : ℝ) * ε := (div_lt_iff₀ hε).1 hK
  rw [div_lt_iff₀ hN']
  nlinarith

/-- Extracting digits at square indices does not preserve normality in base `b ≥ 2`. -/
theorem exists_isNormalIn_not_isNormalSeq_sq (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalSeq b (fun n ↦ digit b x (n ^ 2)) := by
  classical
  refine not_preserves_isNormalSeq_of_density_zero hb (s := fun n ↦ n ^ 2) ?_
  have hbound : Tendsto (fun N : ℕ ↦ ((Nat.sqrt N : ℝ) + 1) / N) atTop (𝓝 0) := by
    have h := tendsto_natSqrt_div_atTop.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    rw [add_zero] at h
    exact h.congr fun N ↦ (add_div _ _ _).symm
  refine squeeze_zero (fun N ↦ by positivity) (fun N ↦ ?_) hbound
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  have hsub : ((Finset.range N).filter fun m ↦ m ∈ Set.range fun n : ℕ ↦ n ^ 2) ⊆
      (Finset.range (Nat.sqrt N + 1)).image fun n : ℕ ↦ n ^ 2 := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range] at hm
    obtain ⟨hmN, k, rfl⟩ := hm
    refine Finset.mem_image.2 ⟨k, Finset.mem_range.2 ?_, rfl⟩
    have hk : k ≤ Nat.sqrt N := Nat.le_sqrt.2 (by simpa [sq] using hmN.le)
    omega
  have hcard : ((Finset.range N).filter fun m ↦ m ∈ Set.range fun n : ℕ ↦ n ^ 2).card ≤
      Nat.sqrt N + 1 :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (Finset.card_range _).le)
  exact_mod_cast hcard

private theorem sub_one_sq_le_two_pow : ∀ k : ℕ, (k - 1) ^ 2 ≤ 2 ^ k
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide
  | k + 5 => by
    have ih := sub_one_sq_le_two_pow (k + 4)
    have h1 : (k + 5 - 1) ^ 2 ≤ 2 * (k + 4 - 1) ^ 2 := by
      have : (k + 4) ^ 2 ≤ 2 * (k + 3) ^ 2 := by zify; nlinarith [Int.natCast_nonneg k]
      simpa using this
    calc (k + 5 - 1) ^ 2 ≤ 2 * (k + 4 - 1) ^ 2 := h1
      _ ≤ 2 * 2 ^ (k + 4) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 5) := by rw [← pow_succ']

/-- Extracting digits at power-of-two indices does not preserve normality in base `b ≥ 2`. -/
theorem exists_isNormalIn_not_isNormalSeq_two_pow (hb : 2 ≤ b) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalSeq b (fun n ↦ digit b x (2 ^ n)) := by
  classical
  refine not_preserves_isNormalSeq_of_density_zero hb (s := fun n ↦ 2 ^ n) ?_
  have hbound : Tendsto (fun N : ℕ ↦ ((Nat.sqrt N : ℝ) + 2) / N) atTop (𝓝 0) := by
    have h := tendsto_natSqrt_div_atTop.add (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    rw [add_zero] at h
    exact h.congr fun N ↦ (add_div _ _ _).symm
  refine squeeze_zero' (Eventually.of_forall fun N ↦ by positivity) ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with N hN
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  have hsub : ((Finset.range N).filter fun m ↦ m ∈ Set.range fun n : ℕ ↦ 2 ^ n) ⊆
      (Finset.range (Nat.log 2 N + 1)).image fun n : ℕ ↦ 2 ^ n := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range] at hm
    obtain ⟨hmN, k, rfl⟩ := hm
    refine Finset.mem_image.2 ⟨k, Finset.mem_range.2 ?_, rfl⟩
    have hk : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) hmN.le
    omega
  have hlog : Nat.log 2 N ≤ Nat.sqrt N + 1 := by
    have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have hsq : (Nat.log 2 N - 1) ^ 2 ≤ N := (sub_one_sq_le_two_pow _).trans hpow
    have hle : Nat.log 2 N - 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by simpa [sq] using hsq)
    omega
  have hcard : ((Finset.range N).filter fun m ↦ m ∈ Set.range fun n : ℕ ↦ 2 ^ n).card ≤
      Nat.sqrt N + 2 := by
    have := (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (Finset.card_range _).le)
    omega
  exact_mod_cast hcard

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
      ¬ IsNormalSeq b (fun n ↦ digit b x (s n)) := by
  have hzero : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b x n = 0).card : ℝ) / N)
      atTop (𝓝 (1 / (b : ℝ))) := by
    have h := hx.isSimplyNormalIn ⟨0, by omega⟩
    rw [one_div]
    refine h.congr fun N ↦ ?_
    simp [blockCount]
  have hinf : {n : ℕ | digit b x n = 0}.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    have hle : ∀ N, (((Finset.range N).filter fun n ↦ digit b x n = 0).card : ℝ) ≤ M + 1 :=
      fun N ↦ by
        have hsub : ((Finset.range N).filter fun n ↦ digit b x n = 0) ⊆ Finset.range (M + 1) := by
          intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          have := hM hn.2
          omega
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_range _).le
    have h0 : Tendsto (fun N : ℕ ↦
        (((Finset.range N).filter fun n ↦ digit b x n = 0).card : ℝ) / N) atTop (𝓝 0) :=
      squeeze_zero (fun N ↦ by positivity) (fun N ↦ div_le_div_of_nonneg_right (hle N)
        (Nat.cast_nonneg N)) (tendsto_const_div_atTop_nhds_zero_nat _)
    have heq := tendsto_nhds_unique hzero h0
    simp only [one_div, inv_eq_zero, Nat.cast_eq_zero] at heq
    omega
  refine ⟨Nat.nth (fun n ↦ digit b x n = 0), Nat.nth_strictMono hinf, ?_,
    Nat.nth_mem_of_infinite hinf,
    not_isNormalSeq_of_forall_eq_zero hb (Nat.nth_mem_of_infinite hinf)⟩
  have hrange : Set.range (Nat.nth fun n ↦ digit b x n = 0) = {n : ℕ | digit b x n = 0} :=
    Nat.range_nth_of_infinite hinf
  refine hzero.congr fun N ↦ ?_
  congr 2
  refine congrArg Finset.card (Finset.filter_congr fun n _ ↦ ?_)
  rw [hrange]
  rfl

end Real
