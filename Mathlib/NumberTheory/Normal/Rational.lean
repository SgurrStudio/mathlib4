/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.PiatetskiShapiro
public import Mathlib.NumberTheory.Normal.Wall

import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Normality is invariant under rational affine maps

**Wall** (1949) proved that if `x` is normal in base `b`, then so is `q * x + r` for all rational
numbers `q ≠ 0` and `r`.

## Main statements

* `Real.IsNormalIn.mul_natCast`, `Real.IsNormalIn.div_natCast`, `Real.IsNormalIn.neg`:
  normality is preserved by multiplication and division by positive integers, and by negation.
* `Real.isNormalIn_mul_add_ratCast_iff`: `q * x + r` is normal in base `b` iff `x` is.

## Proof sketch

Both for `n * x` and for `x / m`, the block of `k` digits at position `i` is determined by the
block of `x` at position `i` together with a bounded amount of extra information (a carry
`< n`, respectively the residue of `⌊x * b ^ i⌋` modulo `m`). Hence each block of the new number
has upper frequency at most `C * b⁻ᵏ`, and Piatetski-Shapiro's criterion
(`Real.isNormalIn_of_eventually_le`) applies.

## References

* [D. D. Wall, *Normal Numbers*][Wall1949]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- The block code `⌊fract z * B⌋₊` is `⌊z * B⌋ mod B`. -/
theorem natCast_floor_fract_mul (z : ℝ) {B : ℕ} (hB : 0 < B) :
    ((⌊Int.fract z * B⌋₊ : ℕ) : ℤ) = ⌊z * B⌋ % (B : ℤ) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  rw [Int.natCast_floor_eq_floor (mul_nonneg (Int.fract_nonneg z) hB'.le), Int.fract, sub_mul,
    show (⌊z⌋ : ℝ) * B = ((⌊z⌋ * B : ℤ) : ℝ) by push_cast; ring, Int.floor_sub_intCast,
    show ⌊z⌋ = ⌊z * B⌋ / (B : ℤ) by rw [← Int.floor_div_natCast, mul_div_cancel_right₀ _ hB'.ne'],
    Int.emod_def]
  ring

/-- The base-`b` block of length `k` at position `i` of `y`, as an integer `< b ^ k`. -/
noncomputable def blockCodeAt (b k : ℕ) (y : ℝ) (i : ℕ) : ℤ :=
  ⌊y * (b : ℝ) ^ i * ((b ^ k : ℕ) : ℝ)⌋ % ((b ^ k : ℕ) : ℤ)

theorem blockCodeAt_eq (hb : 0 < b) (k : ℕ) (y : ℝ) (i : ℕ) :
    blockCodeAt b k y i = (⌊Int.fract (y * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊ : ℕ) := by
  rw [blockCodeAt, ← natCast_floor_fract_mul _ (pow_pos hb k), Nat.cast_pow]

theorem blockCount_eq_card_blockCodeAt (hb : 0 < b) {k : ℕ} (y : ℝ) (w : Fin k → Fin b) (N : ℕ) :
    blockCount b y w N = ((Finset.range N).filter fun i ↦
      blockCodeAt b k y i = ((blockCode w : ℕ) : ℤ)).card := by
  rw [blockCount_eq_card_floor_fract hb]
  refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
  rw [blockCodeAt_eq hb, Nat.cast_inj]

/-- Each block of a normal number occurs with frequency `b⁻ᵏ`, in terms of `blockCodeAt`. -/
theorem IsNormalIn.tendsto_card_blockCodeAt (hb : 0 < b) (h : IsNormalIn b x) (k : ℕ) {j : ℕ}
    (hj : j < b ^ k) : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter fun i ↦
      blockCodeAt b k x i = j).card : ℝ) / N) atTop (𝓝 ((b : ℝ) ^ k)⁻¹) := by
  convert (isNormalIn_iff_tendsto_card_floor hb).1 h k j hj using 4 with N
  refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
  rw [blockCodeAt_eq hb, Nat.cast_inj]

/-- If each block of `y` at position `i` determines the block of `x` at position `i` up to at
most `C` possibilities, and `x` is normal, then so is `y`. -/
theorem isNormalIn_of_blockCodeAt_mem (hb : 2 ≤ b) (hx : IsNormalIn b x) {y : ℝ} (C : ℕ)
    (hS : ∀ (k V : ℕ), ∃ S : Finset ℕ, S.card ≤ C ∧
      ∀ i, blockCodeAt b k y i = V → ∃ j ∈ S, blockCodeAt b k x i = j) :
    IsNormalIn b y := by
  classical
  have hb0 : 0 < b := by omega
  refine isNormalIn_of_eventually_le hb (C := C) fun k w ε hε ↦ ?_
  obtain ⟨S, hSC, hSm⟩ := hS k (blockCode w)
  set δ := ε / (C + 1)
  have hδ : 0 < δ := by positivity
  have hbk : 0 < ((b : ℝ) ^ k)⁻¹ := by positivity
  -- each `x`-block in `S` eventually has frequency at most `b⁻ᵏ + δ`
  have hev : ∀ j ∈ S, ∀ᶠ N : ℕ in atTop, (((Finset.range N).filter fun i ↦
      blockCodeAt b k x i = j).card : ℝ) / N ≤ ((b : ℝ) ^ k)⁻¹ + δ := fun j _ ↦ by
    by_cases hj : j < b ^ k
    · exact ((hx.tendsto_card_blockCodeAt hb0 k hj).eventually
        (gt_mem_nhds (lt_add_of_pos_right _ hδ))).mono fun N h ↦ h.le
    · refine Eventually.of_forall fun N ↦ ?_
      have : ((Finset.range N).filter fun i ↦ blockCodeAt b k x i = j) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun i _ h ↦ ?_
        have := Int.emod_lt_of_pos ⌊x * (b : ℝ) ^ i * ((b ^ k : ℕ) : ℝ)⌋
          (show (0 : ℤ) < ((b ^ k : ℕ) : ℤ) by exact_mod_cast pow_pos hb0 k)
        rw [← blockCodeAt, h] at this
        omega
      rw [this]
      simp only [Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  filter_upwards [(Filter.eventually_all_finset S).2 hev, eventually_gt_atTop 0] with N hN hN0
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsub : ((Finset.range N).filter fun i ↦ blockCodeAt b k y i = ((blockCode w : ℕ) : ℤ)) ⊆
      S.biUnion fun j ↦ (Finset.range N).filter fun i ↦ blockCodeAt b k x i = j := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨j, hjS, hj⟩ := hSm i hi.2
    exact Finset.mem_biUnion.2 ⟨j, hjS, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi.1, hj⟩⟩
  rw [blockCount_eq_card_blockCodeAt hb0]
  calc (((Finset.range N).filter fun i ↦ blockCodeAt b k y i = ((blockCode w : ℕ) : ℤ)).card : ℝ)
        / N ≤ (∑ j ∈ S, (((Finset.range N).filter fun i ↦
          blockCodeAt b k x i = j).card : ℝ)) / N := by
        gcongr
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ j ∈ S, (((Finset.range N).filter fun i ↦ blockCodeAt b k x i = j).card : ℝ) / N :=
        Finset.sum_div _ _ _
    _ ≤ ∑ _j ∈ S, (((b : ℝ) ^ k)⁻¹ + δ) := Finset.sum_le_sum hN
    _ = S.card * (((b : ℝ) ^ k)⁻¹ + δ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * ((b : ℝ) ^ k)⁻¹ + ε := by
        have hS' : (S.card : ℝ) ≤ C := by exact_mod_cast hSC
        have : (C : ℝ) * δ ≤ ε := by
          simp only [δ]
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
        nlinarith

theorem IsNormalIn.mul_natCast (hb : 2 ≤ b) (h : IsNormalIn b x) {n : ℕ} (hn : 0 < n) :
    IsNormalIn b (x * n) := by
  have hb0 : 0 < b := by omega
  refine isNormalIn_of_blockCodeAt_mem hb h (n * n) fun k V ↦ ?_
  set B := b ^ k
  have hB : 0 < B := pow_pos hb0 k
  refine ⟨((Finset.range n) ×ˢ (Finset.range n)).image fun p ↦ (V + B * p.1 - p.2) / n,
    Finset.card_image_le.trans (by simp), fun i hi ↦ ?_⟩
  -- write `x * b ^ i * B = G + t` and `⌊n * t⌋₊ = c`
  set X := x * (b : ℝ) ^ i * (B : ℝ)
  set G := ⌊X⌋
  set c := ⌊(n : ℝ) * Int.fract X⌋₊
  have hc : c < n := by
    rw [Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg X))]
    exact mul_lt_of_lt_one_right (by exact_mod_cast hn) (Int.fract_lt_one X)
  set J := (G % (B : ℤ)).toNat
  have hJ : (J : ℤ) = G % (B : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hJB : J < B := by
    have := Int.emod_lt_of_pos G (show (0 : ℤ) < B by exact_mod_cast hB)
    omega
  have hcode : blockCodeAt b k (x * n) i = (((n * J + c) % B : ℕ) : ℤ) := by
    have hfl : ⌊x * n * (b : ℝ) ^ i * (B : ℝ)⌋ = n * G + c := by
      rw [show x * n * (b : ℝ) ^ i * (B : ℝ) = ((n * G : ℤ) : ℝ) + n * Int.fract X by
        simp only [X, G, Int.fract]; push_cast; ring, Int.floor_intCast_add,
        ← Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg X))]
    simp only [blockCodeAt]
    change ⌊x * n * (b : ℝ) ^ i * (B : ℝ)⌋ % (B : ℤ) = _
    rw [hfl]
    push_cast
    rw [hJ]
    exact (((Int.mod_modEq G B).mul_left n).add_right c).symm
  rw [hcode] at hi
  have hV : (n * J + c) % B = V := by exact_mod_cast hi
  refine ⟨J, Finset.mem_image.2 ⟨((n * J + c) / B, c), ?_, ?_⟩, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨(Nat.div_lt_iff_lt_mul hB).2 ?_, hc⟩
    have := Nat.mul_le_mul_left n (show J + 1 ≤ B by omega)
    nlinarith
  · have h1 := Nat.div_add_mod (n * J + c) B
    rw [hV] at h1
    simp only
    rw [show V + B * ((n * J + c) / B) - c = n * J by omega, Nat.mul_div_cancel_left _ hn]
  · rw [blockCodeAt, hJ]

theorem IsNormalIn.div_natCast (hb : 2 ≤ b) (h : IsNormalIn b x) {m : ℕ} (hm : 0 < m) :
    IsNormalIn b (x / m) := by
  have hb0 : 0 < b := by omega
  refine isNormalIn_of_blockCodeAt_mem hb h m fun k V ↦ ?_
  set B := b ^ k
  have hB : (0 : ℤ) < B := by exact_mod_cast pow_pos hb0 k
  refine ⟨(Finset.range m).image fun t ↦ (m * V + t) % B, Finset.card_image_le.trans (by simp),
    fun i hi ↦ ?_⟩
  set G := ⌊x * (b : ℝ) ^ i * (B : ℝ)⌋
  have hcode : blockCodeAt b k (x / m) i = G / m % B := by
    rw [blockCodeAt, show x / m * (b : ℝ) ^ i * ((b ^ k : ℕ) : ℝ) =
      x * (b : ℝ) ^ i * (B : ℝ) / m by ring, Int.floor_div_natCast]
  rw [hcode] at hi
  have ht0 : 0 ≤ G % (m : ℤ) := Int.emod_nonneg _ (by omega)
  have htm : G % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
  refine ⟨(m * V + (G % (m : ℤ)).toNat) % B,
    Finset.mem_image.2 ⟨(G % (m : ℤ)).toNat, Finset.mem_range.2 (by omega), rfl⟩, ?_⟩
  -- `G = (m * V + t) + B * (m * l)`
  have h1 := Int.emod_add_mul_ediv G m
  have h2 := Int.emod_add_mul_ediv (G / m) B
  rw [hi] at h2
  generalize G / m = Q at h1 h2
  generalize Q / B = l at h2
  change G % ((b ^ k : ℕ) : ℤ) = _
  generalize G % (m : ℤ) = t at h1 ht0 htm ⊢
  have hG : G = (m * V + t) + B * (m * l) := by linear_combination -h1 - m * h2
  rw [hG, Int.add_mul_emod_self_left]
  push_cast
  rw [Int.toNat_of_nonneg ht0]

/-- The digits of `-x` are the complements of those of `x`, for irrational `x`. -/
theorem digit_neg (hb : 0 < b) (hx : Irrational x) (n : ℕ) :
    digit b (-x) n = b - 1 - digit b x n := by
  have hy : x * (b : ℝ) ^ (n + 1) ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    have := (irrational_mul_natCast_iff (n := b ^ (n + 1))).2 ⟨by positivity, hx⟩
    push_cast at this
    exact this.ne_int z hz.symm
  have hfl : ⌊-x * (b : ℝ) ^ (n + 1)⌋ = -(⌊x * (b : ℝ) ^ (n + 1)⌋ + 1) := by
    rw [neg_mul, Int.floor_neg, (Int.ceil_eq_floor_add_one_iff_notMem _).2 hy]
  rw [digit, digit, hfl]
  generalize ⌊x * (b : ℝ) ^ (n + 1)⌋ = F
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hr0 := Int.emod_nonneg F hb'.ne'
  have hrb := Int.emod_lt_of_pos F hb'
  have hmod : -(F + 1) % (b : ℤ) = b - 1 - F % b := by
    have h := Int.emod_add_mul_ediv F b
    rw [show -(F + 1) = (b - 1 - F % b) + b * (-(F / b) - 1) by linarith,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [hmod]
  omega

theorem IsNormalIn.neg (hb : 2 ≤ b) (h : IsNormalIn b x) : IsNormalIn b (-x) := by
  have hb0 : 0 < b := by omega
  have hirr := h.irrational hb
  intro k w
  set w' : Fin k → Fin b := fun j ↦ ⟨b - 1 - w j, by omega⟩
  have key : ∀ N, blockCount b (-x) w N = blockCount b x w' N := by
    classical
    intro N
    unfold blockCount
    congr 1
    ext i
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ ↦ forall_congr' fun j ↦ ?_
    rw [digit_neg hb0 hirr]
    have := digit_lt hb0 x (i + j)
    have := (w j).isLt
    simp only [w']
    omega
  simp only [key]
  exact h k w'

theorem IsNormalIn.mul_intCast (hb : 2 ≤ b) (h : IsNormalIn b x) {n : ℤ} (hn : n ≠ 0) :
    IsNormalIn b (x * n) := by
  rcases lt_or_gt_of_ne hn with hn | hn
  · have := (h.neg hb).mul_natCast hb (n := n.natAbs) (by omega)
    convert this using 1
    rw [Nat.cast_natAbs, abs_of_neg (by exact_mod_cast hn)]
    push_cast
    ring
  · have := h.mul_natCast hb (n := n.natAbs) (by omega)
    convert this using 1
    rw [Nat.cast_natAbs, abs_of_pos (by exact_mod_cast hn)]

theorem IsNormalIn.mul_ratCast (hb : 2 ≤ b) (h : IsNormalIn b x) {q : ℚ} (hq : q ≠ 0) :
    IsNormalIn b (x * q) := by
  have := (h.mul_intCast hb (Rat.num_ne_zero.2 hq)).div_natCast hb q.den_pos
  convert this using 1
  rw [Rat.cast_def]
  ring

theorem IsNormalIn.add_ratCast (hb : 2 ≤ b) (h : IsNormalIn b x) (r : ℚ) :
    IsNormalIn b (x + r) := by
  have := ((isNormalIn_add_intCast_iff r.num).2 (h.mul_natCast hb r.den_pos)).div_natCast hb
    r.den_pos
  convert this using 1
  have : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [Rat.cast_def]
  field_simp

/-- **Wall's theorem**: normality in base `b` is invariant under `x ↦ q * x + r` for rationals
`q ≠ 0` and `r`. -/
theorem isNormalIn_mul_add_ratCast_iff (hb : 2 ≤ b) {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    IsNormalIn b (q * x + r) ↔ IsNormalIn b x := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [mul_comm]; exact (h.mul_ratCast hb hq).add_ratCast hb r⟩
  have := (h.mul_ratCast hb (inv_ne_zero hq)).add_ratCast hb (-r / q)
  convert this using 1
  have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  push_cast
  field_simp
  ring

end Real
