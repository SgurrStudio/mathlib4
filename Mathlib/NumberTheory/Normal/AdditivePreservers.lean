/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.NumberTheory.Normal.DigitOperations
public import Mathlib.NumberTheory.Normal.Preservation
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uncountable and transcendental additive normality preservers

We prove that for every base `b ≥ 2`, the additive subgroup `Real.normalAddPreservers hb` of real
numbers `t` such that `x ↦ x + t` preserves base-`b` normality is uncountable — in fact has
cardinality `Cardinal.continuum` — contains explicit transcendental numbers (in particular
Mathlib's `liouvilleNumber b`), and is closed under rational scalar multiplication.

## Proof outline

1. **Carry-run bound**: For any base-`b` normal number `x`, the length of any run of `(b - 1)`
   digits ending at position `n` is `o(n)` (because digit `0` has asymptotic density `b⁻¹ > 0`).
2. **Sparse base-`b` series**: For any strictly increasing sequence `a : ℕ → ℕ` with
   `a k / a (k + 1) → 0` and any bit sequence `c : ℕ → Bool`, adding
   `sparseSeries b a c = ∑' k, if c k then ((b : ℝ) ^ (a k + 1))⁻¹ else 0` to a base-`b` normal
   number `x` changes `digit b x` only on a set of asymptotic density zero, so `x + t` is normal
   in base `b` by `Real.isNormalIn_of_density_zero_digit_diff`.
3. **Liouville constants & continuum cardinality**: Taking `a k = (k + 2)! - 1` shows that
   `liouvilleNumber b` (which is transcendental by `transcendental_liouvilleNumber`) lies in
   `normalAddPreservers hb`, and that `c ↦ sparseSeries b a c` is an injection from `ℕ → Bool`
   into `normalAddPreservers hb`, giving `#(normalAddPreservers hb) = 𝔠`.

## Main statements

* `Real.isNormalIn_add_sparseSeries`: sparse base-`b` series preserve base-`b` normality under
  addition.
* `Real.liouvilleNumber_mem_normalAddPreservers`: `liouvilleNumber b ∈ normalAddPreservers hb`.
* `Real.exists_transcendental_mem_normalAddPreservers`: existence of a transcendental additive
  normality preserver in every base `b ≥ 2`.
* `Real.cardinalMk_normalAddPreservers`, `Real.uncountable_normalAddPreservers`:
  `normalAddPreservers hb` has cardinality `Cardinal.continuum` and is uncountable.
* `Real.ratCast_mul_mem_normalAddPreservers`: `normalAddPreservers hb` is closed under
  multiplication by rationals `q : ℚ`.
-/

@[expose] public section

open Filter Topology
open scoped Cardinal

namespace Real

variable {b : ℕ} {x t : ℝ}

/-- A sparse base-`b` series with bit coefficients `c : ℕ → Bool` at digit positions `a k`. -/
noncomputable def sparseSeries (b : ℕ) (a : ℕ → ℕ) (c : ℕ → Bool) : ℝ :=
  ∑' k : ℕ, if c k then ((b : ℝ) ^ (a k + 1))⁻¹ else 0

/-! ### Carry-run bound for base-`b` normal numbers -/

/-- For a base-`b` normal number `x`, any run of `(b - 1)` digits ending at position `n` has
length `o(n)`. -/
private lemma run_maxDigit_littleO (hb : 2 ≤ b) (hx : IsNormalIn b x) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ m n : ℕ, N₀ ≤ n → m ≤ n →
      (∀ j : ℕ, m ≤ j → j < n → digit b x j = b - 1) → ((n - m : ℕ) : ℝ) < ε * n := by
  have hb0 : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by positivity
  -- Frequency of digit `0` converges to `b⁻¹`
  have hc0 : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ digit b x i = 0).card : ℝ) / N) atTop (𝓝 (b : ℝ)⁻¹) := by
    have h1 := hx 1 (fun _ : Fin 1 ↦ (⟨0, hb0⟩ : Fin b))
    rw [pow_one] at h1
    refine h1.congr fun N ↦ ?_
    refine congrArg (fun S : Finset ℕ ↦ (S.card : ℝ) / N) ?_
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Fin.forall_fin_one, Fin.val_zero, add_zero]
  set η : ℝ := min ((b : ℝ)⁻¹ / 2) (ε * (b : ℝ)⁻¹ / 4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη_half : η ≤ (b : ℝ)⁻¹ / 2 := min_le_left _ _
  have hη_eps : η ≤ ε * (b : ℝ)⁻¹ / 4 := min_le_right _ _
  obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.1 hc0 η hη
  set M : ℕ := max M₁ 1
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (b : ℝ) * M)
  refine ⟨max N₀ M, fun m n hn hmn hrun ↦ ?_⟩
  have hne : b - 1 ≠ 0 := by omega
  -- Zero-count on `[0, n)` equals zero-count on `[0, m)`
  have hcnt_eq : ((Finset.range n).filter fun i ↦ digit b x i = 0).card =
      ((Finset.range m).filter fun i ↦ digit b x i = 0).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hin, hi0⟩
      refine ⟨?_, hi0⟩
      by_contra! hmi
      exact hne ((hrun i hmi hin).symm.trans hi0)
    · rintro ⟨him, hi0⟩
      exact ⟨lt_of_lt_of_le him hmn, hi0⟩
  have hn_ge_M₁ : M₁ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn_pos : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
    positivity
  have hspec_n := hM₁ n hn_ge_M₁
  rw [Real.dist_eq, abs_lt] at hspec_n
  have hlow_n : ((b : ℝ)⁻¹ - η) * n <
      (((Finset.range n).filter fun i ↦ digit b x i = 0).card : ℝ) := by
    have := (lt_div_iff₀ hn_pos).1 (by linarith : (b : ℝ)⁻¹ - η <
      (((Finset.range n).filter fun i ↦ digit b x i = 0).card : ℝ) / n)
    linarith
  have hm_ge_M : M ≤ m := by
    have hcm_le : (((Finset.range m).filter fun i ↦ digit b x i = 0).card : ℝ) ≤ m := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    have hn_gt : 2 * (b : ℝ) * M < n :=
      lt_of_lt_of_le hN₀ (by exact_mod_cast le_trans (le_max_left _ _) hn)
    have hM_lt_m : (M : ℝ) < m := by
      have h1 : (b : ℝ)⁻¹ / 2 * n ≤ ((b : ℝ)⁻¹ - η) * n := by nlinarith
      have h2 : (M : ℝ) < (b : ℝ)⁻¹ / 2 * n := by
        have hmul : (b : ℝ) * (2 * (b : ℝ) * M) < (b : ℝ) * n :=
          mul_lt_mul_of_pos_left hn_gt hbR
        have : (b : ℝ)⁻¹ / 2 * (2 * (b : ℝ) * M) = M := by field_simp [hbR.ne']
        nlinarith [mul_lt_mul_of_pos_left hn_gt (show (0 : ℝ) < (b : ℝ)⁻¹ / 2 by positivity)]
      rw [hcnt_eq] at hlow_n
      linarith
    exact_mod_cast hM_lt_m.le
  have hm_ge_M₁ : M₁ ≤ m := le_trans (le_max_left _ _) hm_ge_M
  have hm_pos : (0 : ℝ) < m := by
    have : 1 ≤ m := le_trans (le_max_right _ _) hm_ge_M
    positivity
  have hspec_m := hM₁ m hm_ge_M₁
  rw [Real.dist_eq, abs_lt] at hspec_m
  have hup_m : (((Finset.range m).filter fun i ↦ digit b x i = 0).card : ℝ) <
      ((b : ℝ)⁻¹ + η) * m := by
    have := (div_lt_iff₀ hm_pos).1 (by linarith :
      (((Finset.range m).filter fun i ↦ digit b x i = 0).card : ℝ) / m < (b : ℝ)⁻¹ + η)
    linarith
  rw [hcnt_eq] at hlow_n
  have hmnR : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hmn
  have hm_le_n : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdiff_pos : 0 < (b : ℝ)⁻¹ - η := by linarith
  have hkey : ((n : ℝ) - m) * ((b : ℝ)⁻¹ - η) < 2 * η * n := by nlinarith
  have h2η : 2 * η ≤ ε * ((b : ℝ)⁻¹ - η) := by nlinarith
  have hkey2 : ((n : ℝ) - m) * ((b : ℝ)⁻¹ - η) < ε * n * ((b : ℝ)⁻¹ - η) := by nlinarith
  rw [hmnR]
  nlinarith

/-! ### Exact digit preservation under small fractional perturbations -/

private lemma fract_mul_pow_mul_eq (hb : 0 < b) (y : ℝ) (i : ℕ) :
    Int.fract (y * (b : ℝ) ^ i) * (b : ℝ) =
      (digit b y i : ℝ) + Int.fract (y * (b : ℝ) ^ (i + 1)) := by
  have hbR : (0 : ℝ) < b := by positivity
  have hpow : y * (b : ℝ) ^ (i + 1) =
      ((⌊y * (b : ℝ) ^ i⌋ * (b : ℤ) : ℤ) : ℝ) + Int.fract (y * (b : ℝ) ^ i) * b := by
    rw [pow_succ, ← mul_assoc]
    have hfl := Int.floor_add_fract (y * (b : ℝ) ^ i)
    push_cast
    linarith [congrArg (· * (b : ℝ)) hfl]
  have hfract : Int.fract (y * (b : ℝ) ^ (i + 1)) =
      Int.fract (Int.fract (y * (b : ℝ) ^ i) * b) := by
    rw [hpow, Int.fract_intCast_add]
  have hdig : (digit b y i : ℝ) = (⌊Int.fract (y * (b : ℝ) ^ i) * b⌋ : ℝ) := by
    have hnn : 0 ≤ Int.fract (y * (b : ℝ) ^ i) * b :=
      mul_nonneg (Int.fract_nonneg _) hbR.le
    have hfl_nn : 0 ≤ ⌊Int.fract (y * (b : ℝ) ^ i) * b⌋ := Int.floor_nonneg.2 hnn
    have hdef : digit b y i = ⌊Int.fract (y * (b : ℝ) ^ i) * b⌋.toNat := by
      rw [digit, pow_succ, ← mul_assoc]
      have hmod : ⌊y * (b : ℝ) ^ i * b⌋ % (b : ℤ) = ⌊Int.fract (y * (b : ℝ) ^ i) * b⌋ := by
        have hfl_eq : ⌊y * (b : ℝ) ^ i * b⌋ =
            ⌊y * (b : ℝ) ^ i⌋ * (b : ℤ) + ⌊Int.fract (y * (b : ℝ) ^ i) * b⌋ := by
          rw [mul_assoc, ← pow_succ, hpow, Int.floor_intCast_add]
        rw [hfl_eq, Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod]
        refine Int.emod_eq_of_lt hfl_nn ?_
        have hlt : Int.fract (y * (b : ℝ) ^ i) * b < (b : ℤ) := by
          push_cast
          exact (mul_lt_iff_lt_one_left hbR).2 (Int.fract_lt_one _)
        exact Int.floor_lt.2 hlt
      rw [hmod]
    rw [hdef]
    exact_mod_cast Int.toNat_of_nonneg hfl_nn
  rw [hdig, hfract, Int.floor_add_fract]

private lemma digit_add_eq_of_digit_zero_of_fract_lt_one (hb : 0 < b) (x t : ℝ) (i : ℕ)
    (ht0 : digit b t i = 0)
    (hsum : Int.fract (x * (b : ℝ) ^ (i + 1)) + Int.fract (t * (b : ℝ) ^ (i + 1)) < 1) :
    digit b (x + t) i = digit b x i := by
  have hbR : (0 : ℝ) < b := by positivity
  have hx_eq := fract_mul_pow_mul_eq hb x i
  have ht_eq := fract_mul_pow_mul_eq hb t i
  rw [ht0, Nat.cast_zero, zero_add] at ht_eq
  have hdx_le : (digit b x i : ℝ) + 1 ≤ b := by
    exact_mod_cast digit_lt hb x i
  have hadd_mul : (Int.fract (x * (b : ℝ) ^ i) + Int.fract (t * (b : ℝ) ^ i)) * b =
      (digit b x i : ℝ) +
        (Int.fract (x * (b : ℝ) ^ (i + 1)) + Int.fract (t * (b : ℝ) ^ (i + 1))) := by
    linarith
  have hfrac_lt : Int.fract (x * (b : ℝ) ^ i) + Int.fract (t * (b : ℝ) ^ i) < 1 := by
    nlinarith
  have hfrac_nn : 0 ≤ Int.fract (x * (b : ℝ) ^ i) + Int.fract (t * (b : ℝ) ^ i) :=
    add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _)
  have hxt_fract : Int.fract ((x + t) * (b : ℝ) ^ i) =
      Int.fract (x * (b : ℝ) ^ i) + Int.fract (t * (b : ℝ) ^ i) := by
    have heq : (x + t) * (b : ℝ) ^ i =
        ((⌊x * (b : ℝ) ^ i⌋ + ⌊t * (b : ℝ) ^ i⌋ : ℤ) : ℝ) +
          (Int.fract (x * (b : ℝ) ^ i) + Int.fract (t * (b : ℝ) ^ i)) := by
      push_cast
      linarith [Int.floor_add_fract (x * (b : ℝ) ^ i), Int.floor_add_fract (t * (b : ℝ) ^ i)]
    rw [heq, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨hfrac_nn, hfrac_lt⟩]
  have hxt_eq := fract_mul_pow_mul_eq hb (x + t) i
  rw [hxt_fract, hadd_mul] at hxt_eq
  have hcast : (digit b (x + t) i : ℝ) = (digit b x i : ℝ) := by
    have hfl1 : ⌊(digit b (x + t) i : ℝ) + Int.fract ((x + t) * (b : ℝ) ^ (i + 1))⌋ =
        (digit b (x + t) i : ℤ) := by
      rw [← Int.cast_natCast, Int.floor_intCast_add,
        Int.floor_eq_zero_iff.2 ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, add_zero]
    have hfl2 : ⌊(digit b x i : ℝ) +
        (Int.fract (x * (b : ℝ) ^ (i + 1)) + Int.fract (t * (b : ℝ) ^ (i + 1)))⌋ =
        (digit b x i : ℤ) := by
      rw [← Int.cast_natCast, Int.floor_intCast_add,
        Int.floor_eq_zero_iff.2 ⟨add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _), hsum⟩,
        add_zero]
    have hfl_eq : (digit b (x + t) i : ℤ) = (digit b x i : ℤ) := by
      rw [← hfl1, ← hxt_eq, hfl2]
    exact_mod_cast hfl_eq
  exact_mod_cast hcast

private lemma fract_mul_pow_lt_of_digit_lt (hb : 0 < b) (x : ℝ) :
    ∀ (k m : ℕ), digit b x (m + k) < b - 1 →
      Int.fract (x * (b : ℝ) ^ m) < 1 - ((b : ℝ) ^ (k + 1))⁻¹ := by
  have hbR : (0 : ℝ) < b := by positivity
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [add_zero] at hm
    have hdx : (digit b x m : ℝ) ≤ (b : ℝ) - 2 := by
      have : digit b x m + 2 ≤ b := by omega
      have hcast : ((digit b x m + 2 : ℕ) : ℝ) ≤ b := by exact_mod_cast this
      push_cast at hcast
      linarith
    have heq := fract_mul_pow_mul_eq hb x m
    have hlt1 := Int.fract_lt_one (x * (b : ℝ) ^ (m + 1))
    rw [pow_one]
    have : Int.fract (x * (b : ℝ) ^ m) * b < b - 1 := by linarith
    have hdiv : Int.fract (x * (b : ℝ) ^ m) < (b - 1) / b := (lt_div_iff₀ hbR).2 this
    have hrew : ((b : ℝ) - 1) / b = 1 - (b : ℝ)⁻¹ := by field_simp [hbR.ne']
    linarith
  | succ k ih =>
    intro m hm
    have hm' : digit b x ((m + 1) + k) < b - 1 := by rwa [show m + 1 + k = m + (k + 1) by omega]
    have hih := ih (m + 1) hm'
    have hdx : (digit b x m : ℝ) ≤ (b : ℝ) - 1 := by
      have : digit b x m + 1 ≤ b := digit_lt hb x m
      have hcast : ((digit b x m + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast this
      push_cast at hcast
      linarith
    have heq := fract_mul_pow_mul_eq hb x m
    have hlt : Int.fract (x * (b : ℝ) ^ m) * b < b - ((b : ℝ) ^ (k + 1))⁻¹ := by linarith
    have hdiv : Int.fract (x * (b : ℝ) ^ m) < (b - ((b : ℝ) ^ (k + 1))⁻¹) / b :=
      (lt_div_iff₀ hbR).2 hlt
    have hrew : ((b : ℝ) - ((b : ℝ) ^ (k + 1))⁻¹) / b = 1 - ((b : ℝ) ^ (k + 2))⁻¹ := by
      have hpow : (b : ℝ) ^ (k + 2) = (b : ℝ) ^ (k + 1) * b := by rw [pow_succ]
      rw [hpow]
      field_simp [hbR.ne']
    linarith

/-! ### Properties of sparse base-`b` series -/

private lemma summable_sparseSeries (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a) (c : ℕ → Bool) :
    Summable fun k : ℕ ↦ if c k then ((b : ℝ) ^ (a k + 1))⁻¹ else 0 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hgeom : Summable fun k : ℕ ↦ ((b : ℝ)⁻¹) ^ k :=
    summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)
  refine Summable.of_nonneg_of_le (fun k ↦ by split_ifs <;> positivity) (fun k ↦ ?_) hgeom
  split_ifs
  · rw [inv_pow]
    have hle : k ≤ a k + 1 := Nat.le_succ_of_le (ha.id_le k)
    have hpow : (b : ℝ) ^ k ≤ (b : ℝ) ^ (a k + 1) :=
      pow_le_pow_right₀ hb1.le hle
    exact inv_anti₀ (by positivity) hpow
  · positivity

private lemma sparseSeries_tail_le (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (c : ℕ → Bool) (k : ℕ) :
    (∑' r : ℕ, if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) ≤
      2 * ((b : ℝ) ^ (a k + 1))⁻¹ := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hterm : ∀ r : ℕ, (if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) ≤
      ((b : ℝ) ^ (a k + 1))⁻¹ * ((b : ℝ)⁻¹) ^ r := fun r ↦ by
    have hle : a k + r ≤ a (k + r) := by
      induction r with
      | zero => simp
      | succ r ih =>
        have := ha (show k + r < k + (r + 1) by omega)
        omega
    split_ifs
    · rw [inv_pow, ← mul_inv, ← pow_add]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hb1.le (by omega))
    · positivity
  have hgeom : Summable fun r : ℕ ↦ ((b : ℝ) ^ (a k + 1))⁻¹ * ((b : ℝ)⁻¹) ^ r :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)).mul_left _
  have hsum_tail : Summable fun r : ℕ ↦ if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0 := by
    have h := (summable_nat_add_iff k).2 (summable_sparseSeries hb ha c)
    simpa [Nat.add_comm] using h
  calc (∑' r : ℕ, if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0)
      ≤ ∑' r : ℕ, ((b : ℝ) ^ (a k + 1))⁻¹ * ((b : ℝ)⁻¹) ^ r :=
        hsum_tail.tsum_le_tsum hterm hgeom
    _ = ((b : ℝ) ^ (a k + 1))⁻¹ * (1 - (b : ℝ)⁻¹)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)]
    _ ≤ 2 * ((b : ℝ) ^ (a k + 1))⁻¹ := by
        have hinv : (1 - (b : ℝ)⁻¹)⁻¹ ≤ 2 := by
          have hsub : (1 : ℝ) / 2 ≤ 1 - (b : ℝ)⁻¹ := by
            have : (b : ℝ)⁻¹ ≤ 1 / 2 := by
              rw [inv_eq_one_div]
              exact one_div_le_one_div_of_le (by norm_num) hb2
            linarith
          have hinv_le := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hsub
          norm_num at hinv_le
          exact hinv_le
        have hpos : 0 ≤ ((b : ℝ) ^ (a k + 1))⁻¹ := by positivity
        nlinarith

private lemma sparseSeries_digit_eq_of_gap (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (c : ℕ → Bool) (x : ℝ) (k i j : ℕ)
    (hprev : ∀ m < k, a m < i) (hij : i < j) (hjk : j + 1 < a k) (hdig : digit b x j < b - 1) :
    digit b (x + sparseSeries b a c) i = digit b x i := by
  have hb0 : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by positivity
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set t := sparseSeries b a c
  -- Split `t = P + R` where `P` is the sum over `m < k` and `R` is the tail `m ≥ k`
  set P : ℝ := ∑ m ∈ Finset.range k, if c m then ((b : ℝ) ^ (a m + 1))⁻¹ else 0
  set R : ℝ := ∑' r : ℕ, if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0
  have ht_eq : t = P + R := by
    have hsplit := (summable_sparseSeries hb ha c).sum_add_tsum_nat_add k
    dsimp only [t, sparseSeries, P, R]
    rw [← hsplit]
    congr 1
    exact tsum_congr fun r ↦ by rw [Nat.add_comm]
  have hP_int : ∀ s : ℕ, i ≤ s → ∃ M : ℤ, P * (b : ℝ) ^ s = (M : ℝ) := fun s his ↦ by
    dsimp only [P]
    rw [Finset.sum_mul]
    have hterm : ∀ m ∈ Finset.range k,
        (if c m then ((b : ℝ) ^ (a m + 1))⁻¹ else 0) * (b : ℝ) ^ s =
          (((if c m then b ^ (s - (a m + 1)) else 0 : ℕ) : ℤ) : ℝ) := fun m hm ↦ by
      have ham : a m + 1 ≤ s := by
        have := hprev m (Finset.mem_range.1 hm)
        omega
      split_ifs
      · have hpow : (b : ℝ) ^ s = (b : ℝ) ^ (a m + 1) * (b : ℝ) ^ (s - (a m + 1)) := by
          rw [← pow_add, Nat.add_sub_of_le ham]
        rw [hpow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
        norm_cast
      · simp
    refine ⟨∑ m ∈ Finset.range k, ((if c m then b ^ (s - (a m + 1)) else 0 : ℕ) : ℤ), ?_⟩
    rw [Finset.sum_congr rfl hterm]
    push_cast
    rfl
  have hR_nn : 0 ≤ R := tsum_nonneg fun r ↦ by split_ifs <;> positivity
  have hR_le : R ≤ 2 * ((b : ℝ) ^ (a k + 1))⁻¹ := sparseSeries_tail_le hb ha c k
  -- Show `Int.fract (t * b^(i+1)) = R * b^(i+1) < ((b : ℝ) ^ (j - i))⁻¹`
  have hR_mul_i1 : R * (b : ℝ) ^ (i + 1) < ((b : ℝ) ^ (j - i))⁻¹ := by
    have hdiff : a k + 1 = (i + 1) + (j - i) + (a k - j) := by omega
    have hak_j : 2 ≤ a k - j := by omega
    calc R * (b : ℝ) ^ (i + 1)
        ≤ (2 * ((b : ℝ) ^ (a k + 1))⁻¹) * (b : ℝ) ^ (i + 1) := by gcongr
      _ = 2 * ((b : ℝ) ^ (a k - j))⁻¹ * ((b : ℝ) ^ (j - i))⁻¹ := by
          rw [hdiff, pow_add, pow_add]
          field_simp [hbR.ne']
      _ ≤ 2 * ((b : ℝ) ^ 2)⁻¹ * ((b : ℝ) ^ (j - i))⁻¹ := by
          gcongr
          linarith
      _ < 1 * ((b : ℝ) ^ (j - i))⁻¹ := by
          have h2b2 : 2 * ((b : ℝ) ^ 2)⁻¹ < 1 := by
            rw [mul_inv_lt_iff₀ (by positivity)]
            nlinarith
          exact mul_lt_mul_of_pos_right h2b2 (by positivity)
      _ = ((b : ℝ) ^ (j - i))⁻¹ := one_mul _
  have hR_mul_i1_lt1 : R * (b : ℝ) ^ (i + 1) < 1 :=
    lt_of_lt_of_le hR_mul_i1 (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith)))
  have ht_fract_i1 : Int.fract (t * (b : ℝ) ^ (i + 1)) = R * (b : ℝ) ^ (i + 1) := by
    obtain ⟨M, hM⟩ := hP_int (i + 1) (by omega)
    rw [ht_eq, add_mul, hM, Int.fract_intCast_add,
      Int.fract_eq_self.2 ⟨by positivity, hR_mul_i1_lt1⟩]
  -- Show `digit b t i = 0`
  have ht_dig0 : digit b t i = 0 := by
    obtain ⟨M, hM⟩ := hP_int i le_rfl
    have hR_mul_i_lt : R * (b : ℝ) ^ i * b < 1 := by
      have : R * (b : ℝ) ^ i * b = R * (b : ℝ) ^ (i + 1) := by rw [pow_succ, mul_assoc]
      linarith
    have hR_mul_i_lt1 : R * (b : ℝ) ^ i < 1 := by nlinarith
    have hfr : Int.fract (t * (b : ℝ) ^ i) = R * (b : ℝ) ^ i := by
      rw [ht_eq, add_mul, hM, Int.fract_intCast_add,
        Int.fract_eq_self.2 ⟨by positivity, hR_mul_i_lt1⟩]
    have heq := fract_mul_pow_mul_eq hb0 t i
    rw [hfr] at heq
    have hlt1 : (digit b t i : ℝ) < 1 := by
      linarith [Int.fract_nonneg (t * (b : ℝ) ^ (i + 1))]
    have hnat : digit b t i < 1 := by exact_mod_cast hlt1
    omega
  -- Apply `fract_mul_pow_lt_of_digit_lt` and `digit_add_eq_of_digit_zero_of_fract_lt_one`
  have hx_fract : Int.fract (x * (b : ℝ) ^ (i + 1)) < 1 - ((b : ℝ) ^ (j - i))⁻¹ := by
    have h := fract_mul_pow_lt_of_digit_lt hb0 x (j - (i + 1)) (i + 1) (by
      rwa [show i + 1 + (j - (i + 1)) = j by omega])
    rwa [show j - (i + 1) + 1 = j - i by omega] at h
  exact digit_add_eq_of_digit_zero_of_fract_lt_one hb0 x t i ht_dig0 (by linarith)

/-! ### Main theorems -/

/-- Adding any sparse base-`b` series with `a k / a (k + 1) → 0` preserves base-`b` normality. -/
theorem isNormalIn_add_sparseSeries (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0))
    (c : ℕ → Bool) (hx : IsNormalIn b x) :
    IsNormalIn b (x + sparseSeries b a c) := by
  refine isNormalIn_of_density_zero_digit_diff hb hx ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := min (ε / 10) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη_eps : 10 * η ≤ ε := by linarith [min_le_left (ε / 10) (1 / 4)]
  have hη_quarter : η ≤ 1 / 4 := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := run_maxDigit_littleO hb hx hη
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 hratio η hη
  set K₁ : ℕ := max K₀ (N₁ + 2)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((10 : ℝ) / η)
  refine ⟨max (a (K₁ + 1) + 1) N₂, fun N hN ↦ ?_⟩
  have hN_gt_aK : a (K₁ + 1) < N :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hN)
  have hN_pos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    positivity
  -- Pick the largest `k` with `a k ≤ N`; then `K₁ + 1 ≤ k` and `N < a (k + 1)`
  have hex : ∃ m : ℕ, N < a m := ⟨N + 1, lt_of_lt_of_le (Nat.lt_succ_self N) (ha.id_le (N + 1))⟩
  let m₀ := Nat.find hex
  have hm₀_gt : N < a m₀ := Nat.find_spec hex
  have hm₀_ge : K₁ + 2 ≤ m₀ := by
    by_contra! hlt
    have hle : a m₀ ≤ a (K₁ + 1) := ha.monotone (by omega)
    omega
  set k : ℕ := m₀ - 1
  have hk_ge : K₁ + 1 ≤ k := by omega
  have hak_le_N : a k ≤ N := by
    have hnot : ¬ N < a k := Nat.find_min hex (by omega)
    omega
  have hN_lt_ak1 : N < a (k + 1) := by
    rwa [show k + 1 = m₀ by omega]
  have hk1_ge : K₁ ≤ k - 1 := by omega
  -- Cover all differing positions `< N` by three explicit intervals
  set s1 := Finset.range (a (k - 1) + 1)
  set s2 := Finset.Ico (a k - (⌊η * N⌋₊ + 3)) (a k + 1)
  set s3 := Finset.Ico (N - (⌊2 * η * N⌋₊ + 3)) N
  have hsub : ((Finset.range N).filter fun i ↦ digit b x i ≠ digit b (x + sparseSeries b a c) i) ⊆
      s1 ∪ (s2 ∪ s3) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hiN, hneq⟩ := hi
    simp only [Finset.mem_union, s1, s2, s3, Finset.mem_range, Finset.mem_Ico]
    by_cases h1 : i ≤ a (k - 1)
    · exact Or.inl (by omega)
    · push Not at h1
      by_cases h2 : i ≤ a k
      · right; left
        refine ⟨?_, by omega⟩
        by_cases hclose : a k ≤ i + 2
        · omega
        · push Not at hclose
          -- `i` must lie in the `(b - 1)`-run ending at `a k - 1`
          have hrun : ∀ j : ℕ, i + 1 ≤ j → j < a k - 1 → digit b x j = b - 1 := by
            intro j hj1 hj2
            by_contra hne_max
            have hlt_max : digit b x j < b - 1 :=
              lt_of_le_of_ne (Nat.le_sub_one_of_lt (digit_lt (by omega) x j)) hne_max
            have hprev : ∀ m < k, a m < i := fun m hm ↦
              lt_of_le_of_lt (ha.monotone (by omega : m ≤ k - 1)) h1
            exact hneq (sparseSeries_digit_eq_of_gap hb ha c x k i j hprev (by omega)
              (by omega) hlt_max).symm
          have hak_big : N₁ ≤ a k - 1 := by
            have ha_le : k ≤ a k := ha.id_le k
            have hK_ge : N₁ + 2 ≤ K₁ := le_max_right _ _
            omega
          have hbd := hN₁ (i + 1) (a k - 1) hak_big (by omega) hrun
          have hle_N : ((a k - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show a k - 1 ≤ N by omega)
          have hlt_fl : (a k - 1) - (i + 1) < ⌊η * N⌋₊ + 1 := by
            have hltR : (((a k - 1) - (i + 1) : ℕ) : ℝ) < η * N :=
              lt_of_lt_of_le hbd (by nlinarith)
            exact_mod_cast lt_trans hltR (Nat.lt_floor_add_one (η * N))
          omega
      · right; right
        push Not at h2
        refine ⟨?_, hiN⟩
        by_cases hclose : a (k + 1) ≤ i + 2
        · omega
        · push Not at hclose
          have hrun : ∀ j : ℕ, i + 1 ≤ j → j < a (k + 1) - 1 → digit b x j = b - 1 := by
            intro j hj1 hj2
            by_contra hne_max
            have hlt_max : digit b x j < b - 1 :=
              lt_of_le_of_ne (Nat.le_sub_one_of_lt (digit_lt (by omega) x j)) hne_max
            have hprev : ∀ m < k + 1, a m < i := fun m hm ↦
              lt_of_le_of_lt (ha.monotone (by omega : m ≤ k)) h2
            exact hneq (sparseSeries_digit_eq_of_gap hb ha c x (k + 1) i j hprev (by omega)
              (by omega) hlt_max).symm
          have hak1_big : N₁ ≤ a (k + 1) - 1 := by
            have ha_le : k + 1 ≤ a (k + 1) := ha.id_le (k + 1)
            have hK_ge : N₁ + 2 ≤ K₁ := le_max_right _ _
            omega
          have hbd := hN₁ (i + 1) (a (k + 1) - 1) hak1_big (by omega) hrun
          have hsub_cast : (((a (k + 1) - 1) - (i + 1) : ℕ) : ℝ) =
              ((a (k + 1) - 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ) := Nat.cast_sub (by omega)
          rw [hsub_cast] at hbd
          have hi1_le_N : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hiN
          have hak1_lt_2N : ((a (k + 1) - 1 : ℕ) : ℝ) < 2 * N := by nlinarith
          have hN_sub_lt : ((N - (i + 1) : ℕ) : ℝ) < 2 * η * N := by
            have hN_le : (N : ℝ) ≤ ((a (k + 1) - 1 : ℕ) : ℝ) := by
              exact_mod_cast (show N ≤ a (k + 1) - 1 by omega)
            rw [Nat.cast_sub (by omega : i + 1 ≤ N)]
            nlinarith
          have hlt_fl : N - (i + 1) < ⌊2 * η * N⌋₊ + 1 := by
            exact_mod_cast lt_trans hN_sub_lt (Nat.lt_floor_add_one (2 * η * N))
          omega
  -- Bound the cardinality of the 3-interval cover
  have hcard_le : (((Finset.range N).filter fun i ↦
      digit b x i ≠ digit b (x + sparseSeries b a c) i).card : ℝ) ≤
      (s1.card : ℝ) + (s2.card : ℝ) + (s3.card : ℝ) := by
    have hnat : ((Finset.range N).filter fun i ↦
        digit b x i ≠ digit b (x + sparseSeries b a c) i).card ≤
        s1.card + (s2.card + s3.card) :=
      (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hcast : (((Finset.range N).filter fun i ↦
        digit b x i ≠ digit b (x + sparseSeries b a c) i).card : ℝ) ≤
        ((s1.card + (s2.card + s3.card) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hs1_le : (s1.card : ℝ) ≤ η * N + 1 := by
    have hspec := hK₀ (k - 1) (le_trans (le_max_left _ _) hk1_ge)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hspec
    have hrew : k - 1 + 1 = k := by omega
    rw [hrew] at hspec
    have hak_pos : (0 : ℝ) < a k := by
      have ha_le : k ≤ a k := ha.id_le k
      have hk1 : 1 ≤ k := by omega
      have hak1 : 0 < a k := by omega
      positivity
    have hak1_lt : (a (k - 1) : ℝ) < η * a k := (div_lt_iff₀ hak_pos).1 hspec
    have hak_le : (a k : ℝ) ≤ N := by exact_mod_cast hak_le_N
    simp only [s1, Finset.card_range, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hs2_le : (s2.card : ℝ) ≤ η * N + 4 := by
    have hnat : s2.card ≤ ⌊η * N⌋₊ + 4 := by
      simp only [s2, Nat.card_Ico]; omega
    have hcast : (s2.card : ℝ) ≤ ((⌊η * N⌋₊ + 4 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith [Nat.floor_le (by positivity : 0 ≤ η * N)]
  have hs3_le : (s3.card : ℝ) ≤ 2 * η * N + 3 := by
    have hnat : s3.card ≤ ⌊2 * η * N⌋₊ + 3 := by
      simp only [s3, Nat.card_Ico]; omega
    have hcast : (s3.card : ℝ) ≤ ((⌊2 * η * N⌋₊ + 3 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith [Nat.floor_le (by positivity : 0 ≤ 2 * η * N)]
  have h10_lt : (10 : ℝ) < η * N := by
    have hN_gt : (10 : ℝ) / η < N :=
      lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right _ _) hN)
    linarith [(div_lt_iff₀ hη).1 hN_gt]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hN_pos]
  nlinarith

/-- The factorial exponent sequence `k ↦ (k + 2)! - 1` is strictly increasing. -/
private lemma strictMono_factorial_sub_one : StrictMono fun k : ℕ ↦ (k + 2).factorial - 1 := by
  refine strictMono_nat_of_lt_succ fun k ↦ ?_
  have h1 : 1 ≤ (k + 2).factorial := Nat.factorial_pos _
  have h2 : (k + 2).factorial < (k + 1 + 2).factorial := by
    have hsucc : (k + 1 + 2).factorial = (k + 3) * (k + 2).factorial := by
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.factorial_succ (k + 2)]
    nlinarith
  omega

/-- The factorial exponent sequence satisfies `((k + 2)! - 1) / ((k + 3)! - 1) → 0`. -/
private lemma tendsto_factorial_sub_one_ratio :
    Tendsto (fun k : ℕ ↦ (((k + 2).factorial - 1 : ℕ) : ℝ) /
      (((k + 3).factorial - 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  refine squeeze_zero (fun k ↦ by positivity) (fun k ↦ ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ) |>.comp (tendsto_add_atTop_nat 3))
  dsimp only [Function.comp_apply]
  have hfac_pos : 2 ≤ (k + 2).factorial := by
    calc 2 = Nat.factorial 2 := by decide
      _ ≤ (k + 2).factorial := Nat.factorial_le (by omega)
  have hnum : (((k + 2).factorial - 1 : ℕ) : ℝ) ≤ ((k + 2).factorial : ℝ) := by
    exact_mod_cast Nat.sub_le _ 1
  have hden_nat : (k + 3) * (k + 2).factorial ≤ 2 * ((k + 3).factorial - 1) := by
    have hsucc : (k + 3).factorial = (k + 3) * (k + 2).factorial := Nat.factorial_succ (k + 2)
    have hprod : 2 ≤ (k + 3) * (k + 2).factorial := by nlinarith
    omega
  have hden : ((k + 3 : ℕ) : ℝ) * ((k + 2).factorial : ℝ) ≤
      2 * (((k + 3).factorial - 1 : ℕ) : ℝ) := by
    exact_mod_cast hden_nat
  have hden_pos : (0 : ℝ) < (((k + 3).factorial - 1 : ℕ) : ℝ) := by
    have : 1 < (k + 3).factorial := by
      calc 1 < 2 := by norm_num
        _ ≤ (k + 2).factorial := hfac_pos
        _ ≤ (k + 3).factorial := Nat.factorial_le (by omega)
    have : 0 < (k + 3).factorial - 1 := by omega
    positivity
  rw [div_le_div_iff₀ hden_pos (by positivity)]
  nlinarith

/-- Mathlib's base-`b` Liouville constant `liouvilleNumber b` preserves base-`b` normality under
addition. -/
theorem liouvilleNumber_mem_normalAddPreservers (hb : 2 ≤ b) :
    liouvilleNumber (b : ℝ) ∈ normalAddPreservers hb := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hsplit := (LiouvilleNumber.summable hb1).sum_add_tsum_nat_add 2
  have hrat : (∑ i ∈ Finset.range 2, 1 / (b : ℝ) ^ i.factorial) = ((2 / (b : ℚ) : ℚ) : ℝ) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  have htail : (∑' i : ℕ, 1 / (b : ℝ) ^ (i + 2).factorial) =
      sparseSeries b (fun k ↦ (k + 2).factorial - 1) (fun _ ↦ true) := by
    refine tsum_congr fun k ↦ ?_
    have hpos : 1 ≤ (k + 2).factorial := Nat.factorial_pos _
    simp [Nat.sub_add_cancel hpos]
  have hmem_tail : sparseSeries b (fun k ↦ (k + 2).factorial - 1) (fun _ ↦ true) ∈
      normalAddPreservers hb := fun _ hx ↦
    isNormalIn_add_sparseSeries hb strictMono_factorial_sub_one tendsto_factorial_sub_one_ratio
      (fun _ ↦ true) hx
  have heq : liouvilleNumber (b : ℝ) =
      ((2 / (b : ℚ) : ℚ) : ℝ) + sparseSeries b (fun k ↦ (k + 2).factorial - 1) (fun _ ↦ true) := by
    dsimp only [liouvilleNumber]
    rw [← hsplit, hrat, htail]
  rw [heq]
  exact (normalAddPreservers hb).add_mem (ratCast_mem_normalAddPreservers hb _) hmem_tail

/-- In every base `b ≥ 2`, there exists a transcendental (in particular irrational) real number
whose translation preserves base-`b` normality. -/
theorem exists_transcendental_mem_normalAddPreservers (hb : 2 ≤ b) :
    ∃ t : ℝ, Transcendental ℤ t ∧ t ∈ normalAddPreservers hb :=
  ⟨liouvilleNumber (b : ℝ), transcendental_liouvilleNumber hb,
    liouvilleNumber_mem_normalAddPreservers hb⟩

/-- The encoding `c ↦ sparseSeries b (fun k ↦ (k + 2)! - 1) c` is injective on `ℕ → Bool`. -/
private lemma injective_sparseSeries_factorial (hb : 2 ≤ b) :
    Function.Injective (sparseSeries b fun k ↦ (k + 2).factorial - 1) := by
  have hbR : (0 : ℝ) < b := by positivity
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set a : ℕ → ℕ := fun k ↦ (k + 2).factorial - 1
  have ha : StrictMono a := strictMono_factorial_sub_one
  intro c₁ c₂ heq
  by_contra hne
  have hex : ∃ k : ℕ, c₁ k ≠ c₂ k := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  let k := Nat.find hex
  have hk_ne : c₁ k ≠ c₂ k := Nat.find_spec hex
  have hk_lt : ∀ m < k, c₁ m = c₂ m := fun m hm ↦ by
    have := Nat.find_min hex hm
    push Not at this
    exact this
  -- Compare tails after splitting off the first `k` equal terms
  have htail_eq :
      (∑' r : ℕ, if c₁ (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) =
      (∑' r : ℕ, if c₂ (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) := by
    have h1 := (summable_sparseSeries hb ha c₁).sum_add_tsum_nat_add k
    have h2 := (summable_sparseSeries hb ha c₂).sum_add_tsum_nat_add k
    have hpre : (∑ m ∈ Finset.range k, if c₁ m then ((b : ℝ) ^ (a m + 1))⁻¹ else 0) =
        (∑ m ∈ Finset.range k, if c₂ m then ((b : ℝ) ^ (a m + 1))⁻¹ else 0) :=
      Finset.sum_congr rfl fun m hm ↦ by rw [hk_lt m (Finset.mem_range.1 hm)]
    have hsum1 : (∑' r : ℕ, if c₁ (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) =
        ∑' r : ℕ, if c₁ (r + k) then ((b : ℝ) ^ (a (r + k) + 1))⁻¹ else 0 :=
      tsum_congr fun r ↦ by rw [Nat.add_comm]
    have hsum2 : (∑' r : ℕ, if c₂ (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) =
        ∑' r : ℕ, if c₂ (r + k) then ((b : ℝ) ^ (a (r + k) + 1))⁻¹ else 0 :=
      tsum_congr fun r ↦ by rw [Nat.add_comm]
    dsimp only [sparseSeries] at heq
    linarith
  have hsplit_tail : ∀ c : ℕ → Bool,
      (∑' r : ℕ, if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) =
      (if c k then ((b : ℝ) ^ (a k + 1))⁻¹ else 0) +
      (∑' r : ℕ, if c (k + 1 + r) then ((b : ℝ) ^ (a (k + 1 + r) + 1))⁻¹ else 0) := fun c ↦ by
    have hsum : Summable fun r : ℕ ↦ if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0 := by
      have h := (summable_nat_add_iff k).2 (summable_sparseSeries hb ha c)
      simpa [Nat.add_comm] using h
    rw [hsum.tsum_eq_zero_add]
    simp only [add_zero]
    congr 1
    exact tsum_congr fun r ↦ by rw [show k + (r + 1) = k + 1 + r by omega]
  -- Gap `a (k + 1) ≥ a k + 4`, so tail from `k + 1` is strictly less than `((b : ℝ) ^ (a k + 1))⁻¹`
  have htail_strict : ∀ c : ℕ → Bool,
      (∑' r : ℕ, if c (k + 1 + r) then ((b : ℝ) ^ (a (k + 1 + r) + 1))⁻¹ else 0) <
        ((b : ℝ) ^ (a k + 1))⁻¹ := fun c ↦ by
    have hle := sparseSeries_tail_le hb ha c (k + 1)
    have hgap : a k + 4 ≤ a (k + 1) := by
      have hfac2 : 2 ≤ (k + 2).factorial := by
        calc 2 = Nat.factorial 2 := by decide
          _ ≤ (k + 2).factorial := Nat.factorial_le (by omega)
      have hsucc : (k + 1 + 2).factorial = (k + 3) * (k + 2).factorial := by
        rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.factorial_succ (k + 2)]
      have hge : (k + 2).factorial + 4 ≤ (k + 1 + 2).factorial := by nlinarith
      dsimp only [a]
      omega
    have hpow : (b : ℝ) ^ (a k + 4 + 1) ≤ (b : ℝ) ^ (a (k + 1) + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    calc (∑' r : ℕ, if c (k + 1 + r) then ((b : ℝ) ^ (a (k + 1 + r) + 1))⁻¹ else 0)
        ≤ 2 * ((b : ℝ) ^ (a (k + 1) + 1))⁻¹ := hle
      _ ≤ 2 * ((b : ℝ) ^ (a k + 4 + 1))⁻¹ := by
          gcongr
      _ = 2 * ((b : ℝ) ^ 4)⁻¹ * ((b : ℝ) ^ (a k + 1))⁻¹ := by
          have : (b : ℝ) ^ (a k + 4 + 1) = (b : ℝ) ^ 4 * (b : ℝ) ^ (a k + 1) := by
            rw [← pow_add]; congr 1; omega
          rw [this]
          field_simp [hbR.ne']
      _ < 1 * ((b : ℝ) ^ (a k + 1))⁻¹ := by
          have h2b4 : 2 * ((b : ℝ) ^ 4)⁻¹ < 1 := by
            rw [mul_inv_lt_iff₀ (by positivity)]
            nlinarith [sq_nonneg ((b : ℝ) ^ 2 - 4)]
          exact mul_lt_mul_of_pos_right h2b4 (by positivity)
      _ = ((b : ℝ) ^ (a k + 1))⁻¹ := one_mul _
  rw [hsplit_tail c₁, hsplit_tail c₂] at htail_eq
  have hnn1 : 0 ≤ ∑' r : ℕ, if c₁ (k + 1 + r) then ((b : ℝ) ^ (a (k + 1 + r) + 1))⁻¹ else 0 :=
    tsum_nonneg fun r ↦ by split_ifs <;> positivity
  have hnn2 : 0 ≤ ∑' r : ℕ, if c₂ (k + 1 + r) then ((b : ℝ) ^ (a (k + 1 + r) + 1))⁻¹ else 0 :=
    tsum_nonneg fun r ↦ by split_ifs <;> positivity
  cases hc1 : c₁ k <;> cases hc2 : c₂ k
  · exact hk_ne (hc1.trans hc2.symm)
  · simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte, zero_add] at htail_eq
    linarith [htail_strict c₁]
  · simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte, zero_add] at htail_eq
    linarith [htail_strict c₂]
  · exact hk_ne (hc1.trans hc2.symm)

/-- The additive subgroup `normalAddPreservers hb` has cardinality `Cardinal.continuum`. -/
theorem cardinalMk_normalAddPreservers (hb : 2 ≤ b) :
    #(normalAddPreservers hb) = 𝔠 := by
  refine le_antisymm ?_ ?_
  · calc #(normalAddPreservers hb)
        ≤ #ℝ := Cardinal.mk_subtype_le _
      _ = 𝔠 := Cardinal.mk_real
  · let f : (ℕ → Bool) → normalAddPreservers hb := fun c ↦
      ⟨sparseSeries b (fun k ↦ (k + 2).factorial - 1) c, fun _ hx ↦
        isNormalIn_add_sparseSeries hb strictMono_factorial_sub_one tendsto_factorial_sub_one_ratio
          c hx⟩
    have hf : Function.Injective f := fun c₁ c₂ h ↦
      injective_sparseSeries_factorial hb (congrArg Subtype.val h)
    calc 𝔠 = 2 ^ ℵ₀ := Cardinal.two_power_aleph0.symm
      _ = #(ℕ → Bool) := by simp
      _ ≤ #(normalAddPreservers hb) := Cardinal.mk_le_of_injective hf

/-- In every base `b ≥ 2`, there are uncountably many real numbers whose translation preserves
base-`b` normality. -/
theorem uncountable_normalAddPreservers (hb : 2 ≤ b) :
    Uncountable (normalAddPreservers hb) := by
  rw [← Cardinal.aleph0_lt_mk_iff, cardinalMk_normalAddPreservers hb]
  exact Cardinal.aleph0_lt_continuum

/-- The additive normality preservers in base `b ≥ 2` are closed under rational scaling. -/
theorem ratCast_mul_mem_normalAddPreservers (hb : 2 ≤ b) (q : ℚ)
    {α : ℝ} (hα : α ∈ normalAddPreservers hb) :
    (q : ℝ) * α ∈ normalAddPreservers hb := by
  by_cases hq : q = 0
  · subst hq
    simp
  · intro x hx
    have h1 : IsNormalIn b ((q⁻¹ : ℚ) * x) := by
      simpa using (isNormalIn_mul_add_ratCast_iff hb (inv_ne_zero hq) 0 (x := x)).2 hx
    have h2 : IsNormalIn b ((q⁻¹ : ℚ) * x + α) := hα _ h1
    have h3 : IsNormalIn b ((q : ℝ) * ((q⁻¹ : ℚ) * x + α)) := by
      have := (isNormalIn_mul_add_ratCast_iff hb hq 0 (x := (q⁻¹ : ℚ) * x + α)).2 h2
      simpa using this
    have heq : (q : ℝ) * ((q⁻¹ : ℚ) * x + α) = x + (q : ℝ) * α := by
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      push_cast
      field_simp [hqR]
    rwa [heq] at h3

end Real
