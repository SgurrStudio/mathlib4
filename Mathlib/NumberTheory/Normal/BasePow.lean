/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.PiatetskiShapiro
public import Mathlib.NumberTheory.Normal.Rational

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Imported.NormalNumbers.Pillai
import Mathlib.Imported.NormalNumbers.RealDefs

/-!
# Normality in bases `b` and `b ^ r`

We prove that normality in base `b` is the same as normality in base `b ^ r` (**Maxfield**, 1953),
and hence the same in any two multiplicatively dependent bases `b ^ m = c ^ n`. We also prove
**Pillai's theorem** (1940): `x` is normal in base `b` if and only if it is simply normal in every
base `b ^ r`, `r ≥ 1`. Since the base-`b ^ r` digits of `x` are its aligned, non-overlapping
blocks of `r` base-`b` digits, this is also the theorem of **Niven and Zuckerman** (1951) that
normality can be tested on aligned blocks.

## Main statements

* `Real.isNormalIn_pow_iff`: Maxfield's theorem.
* `Real.isNormalIn_iff_of_pow_eq_pow`: normality in multiplicatively dependent bases.
* `Real.isNormalIn_iff_forall_isSimplyNormalIn_pow`: Pillai's and Niven–Zuckerman's theorem.

## Proof

Maxfield's theorem is proved with Piatetski-Shapiro's criterion
(`Real.isNormalIn_of_eventually_le`): a block in base `b ^ r` is a block of `r` times the length
in base `b`, and a block in base `b` at position `r q + t` is a slice of the two-digit block at
position `q` in base `b ^ r`. Pillai's theorem is Trevor Morris's proof
`NormalNumbers.pillai`, imported in `Mathlib/Imported/NormalNumbers`, transferred to
`Real.IsNormalIn`.

## References

* [J. E. Maxfield, *Normal k-tuples*][Maxfield1953]
* [S. S. Pillai, *On normal numbers*][Pillai1940]
* [I. Niven, H. S. Zuckerman, *On the definition of normal numbers*][NivenZuckerman1951]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- The base-`b` block of length `k` at position `i` of `x`, as a natural number `< b ^ k`. -/
noncomputable def blockVal (b k : ℕ) (x : ℝ) (i : ℕ) : ℕ :=
  ⌊Int.fract (x * (b : ℝ) ^ i) * (b : ℝ) ^ k⌋₊

theorem blockVal_pow (b r k : ℕ) (x : ℝ) (q : ℕ) :
    blockVal (b ^ r) k x q = blockVal b (r * k) x (r * q) := by
  simp only [blockVal, Nat.cast_pow, ← pow_mul]

theorem blockVal_lt (hb : 0 < b) (k : ℕ) (x : ℝ) (i : ℕ) : blockVal b k x i < b ^ k := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  refine (Nat.floor_lt (by positivity)).2 ?_
  push_cast
  nlinarith [Int.fract_lt_one (x * (b : ℝ) ^ i)]

/-- A block at position `i + t` is a slice of a longer block at position `i`. -/
theorem blockVal_add (hb : 0 < b) {k m t : ℕ} (htk : t + k ≤ m) (x : ℝ) (i : ℕ) :
    blockVal b k x (i + t) = blockVal b m x i / b ^ (m - t - k) % b ^ k := by
  set z := Int.fract (x * (b : ℝ) ^ i) with hz
  have hz0 : 0 ≤ z := Int.fract_nonneg _
  have h1 : Int.fract (x * (b : ℝ) ^ (i + t)) = Int.fract (z * (b : ℝ) ^ t) := by
    have : x * (b : ℝ) ^ (i + t) = z * (b : ℝ) ^ t + ((⌊x * (b : ℝ) ^ i⌋ * b ^ t : ℤ) : ℝ) := by
      rw [hz, Int.fract]; push_cast; ring
    rw [this, Int.fract_add_intCast]
  have h2 : z * (b : ℝ) ^ t * ((b ^ k : ℕ) : ℝ) =
      z * (b : ℝ) ^ m / ((b ^ (m - t - k) : ℕ) : ℝ) := by
    have : (b : ℝ) ^ m = (b : ℝ) ^ t * (b : ℝ) ^ k * (b : ℝ) ^ (m - t - k) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this]; push_cast; field_simp
  have key := natCast_floor_fract_mul (z * (b : ℝ) ^ t) (B := b ^ k) (pow_pos hb k)
  rw [h2, ← Int.natCast_floor_eq_floor (by positivity), Nat.floor_div_natCast] at key
  simp only [blockVal, ← hz, h1]
  have : ((b ^ k : ℕ) : ℝ) = (b : ℝ) ^ k := by push_cast; ring
  rw [this] at key
  exact_mod_cast key

theorem blockCount_eq_card_blockVal (hb : 0 < b) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockCount b x w N = ((Finset.range N).filter fun i ↦ blockVal b k x i = blockCode w).card :=
  blockCount_eq_card_floor_fract hb w N

theorem tendsto_card_blockVal (hb : 0 < b) (h : IsNormalIn b x) (k : ℕ) {v : ℕ}
    (hv : v < b ^ k) : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ blockVal b k x i = v).card : ℝ) / N) atTop
        (𝓝 ((b : ℝ) ^ k)⁻¹) :=
  (isNormalIn_iff_tendsto_card_floor hb).1 h k v hv

/-- A number normal in base `b` is normal in base `b ^ r`. -/
theorem IsNormalIn.pow (hb : 2 ≤ b) (h : IsNormalIn b x) {r : ℕ} (hr : 0 < r) :
    IsNormalIn (b ^ r) x := by
  classical
  have hb0 : 0 < b := by omega
  have hB : 2 ≤ b ^ r := hb.trans (Nat.le_self_pow hr.ne' b)
  refine isNormalIn_of_eventually_le hB (C := r) fun k w ε hε ↦ ?_
  set V : ℕ := (blockCode w : ℕ)
  have hV : V < b ^ (r * k) := by rw [pow_mul]; exact (blockCode w).isLt
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have ht := (tendsto_card_blockVal hb0 h (r * k) hV).comp
    (tendsto_id.const_mul_atTop' hr)
  filter_upwards [ht.eventually (gt_mem_nhds (lt_add_of_pos_right _ (div_pos hε hr'))),
    eventually_gt_atTop 0] with Q hQ hQ0
  simp only [Function.comp, id] at hQ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ0
  rw [blockCount_eq_card_blockVal (pow_pos hb0 r)]
  have hsub : (((Finset.range Q).filter fun q ↦ blockVal (b ^ r) k x q = V).card) ≤
      ((Finset.range (r * Q)).filter fun i ↦ blockVal b (r * k) x i = V).card := by
    refine Finset.card_le_card_of_injOn (fun q ↦ r * q) (fun q hq ↦ ?_) ?_
    · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hq ⊢
      rw [← blockVal_pow]
      exact ⟨by nlinarith, hq.2⟩
    · intro q _ q' _ h; exact Nat.eq_of_mul_eq_mul_left hr h
  have hpow : (((b ^ r : ℕ) : ℝ) ^ k)⁻¹ = ((b : ℝ) ^ (r * k))⁻¹ := by
    rw [pow_mul]; push_cast; ring
  rw [hpow, div_le_iff₀ hQ']
  have hrQ : ((r * Q : ℕ) : ℝ) = r * Q := by push_cast; ring
  rw [hrQ, div_lt_iff₀ (by positivity)] at hQ
  calc (((Finset.range Q).filter fun q ↦ blockVal (b ^ r) k x q = V).card : ℝ)
      ≤ ((Finset.range (r * Q)).filter fun i ↦ blockVal b (r * k) x i = V).card := by
        exact_mod_cast hsub
    _ ≤ (((b : ℝ) ^ (r * k))⁻¹ + ε / r) * (r * Q) := hQ.le
    _ = (r * ((b : ℝ) ^ (r * k))⁻¹ + ε) * Q := by field_simp

/-- The number of `c < b ^ m` whose base-`b` digit slice at `(m - t - k, …)` is `v` is at most
`b ^ (m - k)`. -/
theorem card_filter_div_mod_eq_le {m t k : ℕ} (hb : 0 < b) (htk : t + k ≤ m) (v : ℕ) :
    ((Finset.range (b ^ m)).filter fun c ↦ c / b ^ (m - t - k) % b ^ k = v).card ≤
      b ^ (m - k) := by
  set D := b ^ (m - t - k)
  have hD : D * b ^ k = b ^ (m - t) := by
    simp only [D, ← pow_add]; congr 1; omega
  calc _ ≤ (Finset.range (b ^ t) ×ˢ Finset.range D).card := by
        refine Finset.card_le_card_of_injOn (fun c ↦ (c / b ^ (m - t), c % D)) (fun c hc ↦ ?_) ?_
        · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hc
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          refine ⟨Nat.div_lt_of_lt_mul ?_, Nat.mod_lt _ (pow_pos hb _)⟩
          rw [← pow_add, show m - t + t = m by omega]; exact hc.1
        · intro c hc c' hc' h
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hc hc'
          simp only [Prod.mk.injEq] at h
          have e : ∀ c, c / D = c / b ^ (m - t) * b ^ k + c / D % b ^ k := fun c ↦ by
            rw [← hD, ← Nat.div_div_eq_div_mul, Nat.div_add_mod']
          rw [← Nat.div_add_mod c D, ← Nat.div_add_mod c' D, e c, e c', hc.2, hc'.2, h.1, h.2]
    _ = b ^ (m - k) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range, ← pow_add]
        congr 1; omega

/-- A number normal in base `b ^ r` is normal in base `b`. -/
theorem IsNormalIn.of_pow (hb : 2 ≤ b) {r : ℕ} (hr : 0 < r) (h : IsNormalIn (b ^ r) x) :
    IsNormalIn b x := by
  classical
  have hb0 : 0 < b := by omega
  have hbr : 2 ≤ b ^ r := hb.trans (Nat.le_self_pow hr.ne' b)
  refine isNormalIn_of_eventually_le hb (C := 4) fun k w ε hε ↦ ?_
  set R := r * (k + 1) with hRdef
  have hR0 : 0 < R := by positivity
  have hkR : k < R := by nlinarith
  have hR : IsNormalIn (b ^ R) x := by
    have := h.pow hbr (r := k + 1) (by omega)
    rwa [← pow_mul] at this
  set m := R * 2
  set v : ℕ := (blockCode w : ℕ)
  set S : ℕ → Finset ℕ := fun t ↦
    (Finset.range (b ^ m)).filter fun c ↦ c / b ^ (m - t - k) % b ^ k = v
  set G : ℕ → ℕ → ℕ := fun c Q ↦
    ((Finset.range Q).filter fun q ↦ blockVal (b ^ R) 2 x q = c).card
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  -- each `G c` eventually has frequency at most `2 b⁻ᵐ`
  have hG : ∀ᶠ N : ℕ in atTop, ∀ c ∈ Finset.range (b ^ m),
      (G c (N / R + 1) : ℝ) ≤ 2 * ((b : ℝ) ^ m)⁻¹ * (N / R + 1 : ℕ) := by
    rw [Filter.eventually_all_finset]
    intro c hc
    have hc' : c < (b ^ R) ^ 2 := by rw [← pow_mul]; exact Finset.mem_range.1 hc
    have ht := (tendsto_card_blockVal (pow_pos hb0 R) hR 2 hc').comp
      ((tendsto_add_atTop_nat 1).comp (Nat.tendsto_div_const_atTop hR0.ne'))
    have hlim : (((b ^ R : ℕ) : ℝ) ^ 2)⁻¹ = ((b : ℝ) ^ m)⁻¹ := by
      simp only [m]; push_cast; rw [← pow_mul]
    rw [hlim] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (show ((b : ℝ) ^ m)⁻¹ < 2 * ((b : ℝ) ^ m)⁻¹ by
      have := inv_pos.2 hbm; linarith))] with N hN
    simp only [Function.comp] at hN
    have hpos : (0 : ℝ) < (N / R + 1 : ℕ) := by positivity
    rw [div_lt_iff₀ hpos] at hN
    exact hN.le
  filter_upwards [hG, eventually_ge_atTop R] with N hN hNR
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hR0.trans_le hNR
  set Q := N / R + 1
  -- decompose positions `i = R * q + t`
  have hsub : ((Finset.range N).filter fun i ↦ blockVal b k x i = v) ⊆
      (Finset.range R).biUnion fun t ↦ (S t).biUnion fun c ↦
        ((Finset.range Q).filter fun q ↦ blockVal (b ^ R) 2 x q = c).image fun q ↦ R * q + t := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hi' : R * (i / R) + i % R = i := Nat.div_add_mod i R
    refine Finset.mem_biUnion.2 ⟨i % R, Finset.mem_range.2 (Nat.mod_lt _ hR0),
      Finset.mem_biUnion.2 ⟨blockVal (b ^ R) 2 x (i / R), ?_, Finset.mem_image.2 ⟨i / R, ?_, hi'⟩⟩⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ?_⟩
      · exact (blockVal_lt (pow_pos hb0 R) 2 x _).trans_eq (by rw [← pow_mul])
      · have e := blockVal_add hb0 (k := k) (m := m) (t := i % R)
          (by have := Nat.mod_lt i hR0; omega) x (R * (i / R))
        rw [hi'] at e
        rw [blockVal_pow, ← hi.2, e]
    · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, rfl⟩
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hi.1.le)
  have hcard : (((Finset.range N).filter fun i ↦ blockVal b k x i = v).card : ℝ) ≤
      ∑ t ∈ Finset.range R, ∑ c ∈ S t, (G c Q : ℝ) := by
    refine (Nat.cast_le.2 ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)).trans ?_
    push_cast
    refine Finset.sum_le_sum fun t _ ↦ ?_
    exact_mod_cast Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun c _ ↦ Finset.card_image_le)
  have hS : ∀ t ∈ Finset.range R, ((S t).card : ℝ) ≤ (b : ℝ) ^ (m - k) := fun t ht ↦ by
    have := card_filter_div_mod_eq_le (m := m) (t := t) (k := k) hb0 (by
      have := Finset.mem_range.1 ht; omega) v
    exact_mod_cast this
  have hbound : ∀ t ∈ Finset.range R, ∑ c ∈ S t, (G c Q : ℝ) ≤
      (b : ℝ) ^ (m - k) * (2 * ((b : ℝ) ^ m)⁻¹ * Q) := fun t ht ↦ by
    calc ∑ c ∈ S t, (G c Q : ℝ) ≤ ∑ _c ∈ S t, 2 * ((b : ℝ) ^ m)⁻¹ * Q :=
          Finset.sum_le_sum fun c hc ↦ hN c (Finset.mem_of_mem_filter c hc)
      _ = (S t).card * (2 * ((b : ℝ) ^ m)⁻¹ * Q) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr; exact hS t ht
  have hpow : (b : ℝ) ^ (m - k) * ((b : ℝ) ^ m)⁻¹ = ((b : ℝ) ^ k)⁻¹ := by
    have : (b : ℝ) ^ m = (b : ℝ) ^ (m - k) * (b : ℝ) ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  have hRQ : (R : ℝ) * Q ≤ 2 * N := by
    have : R * Q ≤ N + R := by
      simp only [Q, mul_add, mul_one]; linarith [Nat.mul_div_le N R]
    have : ((R * Q : ℕ) : ℝ) ≤ N + R := by exact_mod_cast this
    push_cast at this
    have : (R : ℝ) ≤ N := by exact_mod_cast hNR
    linarith
  rw [blockCount_eq_card_blockVal hb0, div_le_iff₀ hN0]
  calc (((Finset.range N).filter fun i ↦ blockVal b k x i = v).card : ℝ)
      ≤ ∑ t ∈ Finset.range R, ∑ c ∈ S t, (G c Q : ℝ) := hcard
    _ ≤ ∑ _t ∈ Finset.range R, (b : ℝ) ^ (m - k) * (2 * ((b : ℝ) ^ m)⁻¹ * Q) :=
        Finset.sum_le_sum hbound
    _ = 2 * ((b : ℝ) ^ k)⁻¹ * (R * Q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hpow]; ring
    _ ≤ 2 * ((b : ℝ) ^ k)⁻¹ * (2 * N) := by gcongr
    _ ≤ (4 * ((b : ℝ) ^ k)⁻¹ + ε) * N := by nlinarith

/-- **Maxfield's theorem**: `x` is normal in base `b ^ r` if and only if it is normal in base
`b`. -/
theorem isNormalIn_pow_iff (hb : 2 ≤ b) {r : ℕ} (hr : 0 < r) :
    IsNormalIn (b ^ r) x ↔ IsNormalIn b x :=
  ⟨IsNormalIn.of_pow hb hr, fun h ↦ h.pow hb hr⟩

/-- Normality in two *multiplicatively dependent* bases, `b ^ m = c ^ n`, is equivalent. -/
theorem isNormalIn_iff_of_pow_eq_pow {c m n : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hm : 0 < m)
    (hn : 0 < n) (h : b ^ m = c ^ n) : IsNormalIn b x ↔ IsNormalIn c x := by
  rw [← isNormalIn_pow_iff hb hm, h, isNormalIn_pow_iff hc hn]

private theorem digitOf_fract (b : ℕ) (x : ℝ) (i : ℕ) :
    NormalNumbers.digitOf b (Int.fract x) i = digit b x i := by
  rw [← digit_fract, digit, NormalNumbers.digitOf,
    Int.toNat_emod (Int.floor_nonneg.2 (mul_nonneg (Int.fract_nonneg x) (by positivity)))
      (by positivity)]
  simp

/-- **Pillai's theorem**: if `x` is simply normal in every base `b ^ r`, `r ≥ 1`, then `x` is
normal in base `b`. -/
theorem isNormalIn_of_forall_isSimplyNormalIn_pow (hb : 2 ≤ b)
    (h : ∀ r : ℕ, 0 < r → IsSimplyNormalIn (b ^ r) x) : IsNormalIn b x := by
  classical
  have hseq := NormalNumbers.pillai b hb (Int.fract x) ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    fun r hr c hc ↦ by
      have := h r hr ⟨c, hc⟩
      have e : ∀ N, blockCount (b ^ r) x (fun _ : Fin 1 ↦ (⟨c, hc⟩ : Fin (b ^ r))) N =
          ((Finset.range N).filter fun q ↦ NormalNumbers.digitOf (b ^ r) (Int.fract x) q = c).card
          := fun N ↦ by
        unfold blockCount; congr 1; ext q; simp [digitOf_fract]
      simpa only [e, Nat.cast_pow] using this
  intro k w
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have e : ∀ N, blockCount b x w N = N := fun N ↦ by simp [blockCount]
    simp only [e, pow_zero, inv_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [div_self (by positivity)]
  set wl : List ℕ := List.ofFn fun j : Fin k ↦ (w j : ℕ)
  have hl := hseq wl (by simp [wl]; omega) (by simp [wl])
  simp only [wl, List.length_ofFn, NormalNumbers.countOccurrences_range_map] at hl
  set A : ℕ → ℕ := fun n ↦ ((Finset.range (n + 1)).filter fun i ↦ i + k ≤ n ∧
    NormalNumbers.MatchesAt (NormalNumbers.digitOf b (Int.fract x)) wl i).card
  have hM : ∀ i, NormalNumbers.MatchesAt (NormalNumbers.digitOf b (Int.fract x)) wl i ↔
      ∀ j : Fin k, digit b x (i + j) = w j := fun i ↦ by
    simp only [NormalNumbers.MatchesAt, wl, List.length_ofFn, digitOf_fract,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    constructor
    · intro hi j; simpa [j.isLt] using hi j j.isLt
    · intro hi j hj; simpa [hj] using hi ⟨j, hj⟩
  have hAB : ∀ n, A n ≤ blockCount b x w n := fun n ↦ by
    refine Finset.card_le_card fun i hi ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, (hM i).1 hi.2.2⟩
  have hBA : ∀ n, blockCount b x w n ≤ A n + k := fun n ↦ by
    have hsub : ((Finset.range n).filter fun i ↦ ∀ j : Fin k, digit b x (i + j) = w j) ⊆
        ((Finset.range (n + 1)).filter fun i ↦ i + k ≤ n ∧
          NormalNumbers.MatchesAt (NormalNumbers.digitOf b (Int.fract x)) wl i) ∪
          Finset.Ico (n - k) n := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      by_cases hik : i + k ≤ n
      · exact Or.inl ⟨by omega, hik, (hM i).2 hi.2⟩
      · exact Or.inr ⟨by omega, hi.1⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    simp only [Nat.card_Ico]
    exact Nat.add_le_add_left (by omega) _
  have hk0 : Tendsto (fun n : ℕ ↦ (k : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)
  have hup : Tendsto (fun n : ℕ ↦ (A n : ℝ) / n + k / n) atTop (𝓝 (((b : ℝ) ^ k)⁻¹ + 0)) :=
    hl.add hk0
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hup (fun n ↦ ?_) fun n ↦ ?_
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hAB n) (Nat.cast_nonneg _)
  · rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hBA n) (Nat.cast_nonneg _)

/-- **Pillai's theorem** and **Niven–Zuckerman's theorem**: `x` is normal in base `b` if and only
if it is simply normal in every base `b ^ r`, i.e. every aligned block of `r` base-`b` digits
occurs with frequency `b⁻ʳ`. -/
theorem isNormalIn_iff_forall_isSimplyNormalIn_pow (hb : 2 ≤ b) :
    IsNormalIn b x ↔ ∀ r : ℕ, 0 < r → IsSimplyNormalIn (b ^ r) x :=
  ⟨fun h _ hr ↦ (h.pow hb hr).isSimplyNormalIn, isNormalIn_of_forall_isSimplyNormalIn_pow hb⟩

end Real
