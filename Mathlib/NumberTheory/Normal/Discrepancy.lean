/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Normal.Wall

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Discrepancy, quantitative Wall's theorem, and Koksma's inequality

This file develops the discrepancy theory of sequences modulo one and its applications to
normal numbers and numerical integration:

* **Discrepancy and star discrepancy**: for a sequence `u : ℕ → ℝ` and `N : ℕ`, we define
  `Real.localDiscrepancy u N a c`, the star discrepancy `Real.starDiscrepancy u N`, and the
  extreme discrepancy `Real.discrepancy u N`, proving `D_N^*(u) ≤ D_N(u) ≤ 2 D_N^*(u)`,
  `IsEquidistributedModOne u ↔ Tendsto (starDiscrepancy u) atTop (𝓝 0)` (Kuipers–Niederreiter,
  Ch. 2, Theorem 1.1), and a quantitative version of Wall's theorem.
* **Koksma's inequality**: for every function `f : ℝ → ℝ` of bounded variation on `[0, 1]` and
  `N ≥ 1`,
  `|(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in 0..1, f t| ≤ V_0^1(f) * D_N^*(u)`
  with the sharp constant `1`, together with the differentiable (`C¹`) variant with
  `∫ t in 0..1, |f' t|`.

## References

* L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974, Ch. 2.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Real

/-! ### Definitions and basic bounds -/

/-- The signed discrepancy of the first `N` terms of `u` on the interval `[a, c) ⊆ [0, 1]`:
`#{n < N : Int.fract (u n) ∈ [a, c)} / N - (c - a)`. -/
noncomputable def localDiscrepancy (u : ℕ → ℝ) (N : ℕ) (a c : ℝ) : ℝ :=
  (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c).card : ℝ) / N - (c - a)

/-- The **star discrepancy** `D_N^*(u)` of the first `N` terms of `u`:
`sup_{t ∈ [0, 1]} |#{n < N : Int.fract (u n) < t} / N - t|`. -/
noncomputable def starDiscrepancy (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ t : Icc (0 : ℝ) 1, |localDiscrepancy u N 0 t|

/-- The **extreme discrepancy** `D_N(u)` of the first `N` terms of `u`:
`sup_{0 ≤ a ≤ c ≤ 1} |#{n < N : Int.fract (u n) ∈ [a, c)} / N - (c - a)|`. -/
noncomputable def discrepancy (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ p : {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}, |localDiscrepancy u N p.val.1 p.val.2|

lemma abs_localDiscrepancy_le_one (u : ℕ → ℝ) (N : ℕ) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    |localDiscrepancy u N a c| ≤ 1 := by
  have h0 : 0 ≤ (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c).card : ℝ) / N := by
    positivity
  have h1 : (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c).card : ℝ) / N ≤ 1 := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · rw [div_le_one (by positivity)]
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range N).le
  rw [localDiscrepancy, abs_le]
  constructor <;> linarith

lemma localDiscrepancy_zero_zero (u : ℕ → ℝ) (N : ℕ) :
    localDiscrepancy u N 0 0 = 0 := by
  simp [localDiscrepancy]

lemma localDiscrepancy_zero_one (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    localDiscrepancy u N 0 1 = 0 := by
  have hfilt : ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) 1) =
      Finset.range N :=
    Finset.filter_true_of_mem fun n _ ↦ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [localDiscrepancy, hfilt, Finset.card_range, div_self (by positivity), sub_zero, sub_self]

lemma localDiscrepancy_eq_sub (u : ℕ → ℝ) (N : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) :
    localDiscrepancy u N a c = localDiscrepancy u N 0 c - localDiscrepancy u N 0 a := by
  have hdisj : Disjoint
      ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) a)
      ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c) := by
    rw [Finset.disjoint_filter]
    intro _ _ h1 h2
    linarith [h1.2, h2.1]
  have hunion :
      ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) a) ∪
        ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c) =
      (Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) c := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, mem_Ico]
    constructor
    · rintro (⟨hn, h1, h2⟩ | ⟨hn, h1, h2⟩)
      · exact ⟨hn, h1, lt_of_lt_of_le h2 hac⟩
      · exact ⟨hn, le_trans ha h1, h2⟩
    · rintro ⟨hn, h1, h2⟩
      rcases lt_or_ge (Int.fract (u n)) a with hlt | hge
      · exact Or.inl ⟨hn, h1, hlt⟩
      · exact Or.inr ⟨hn, hge, h2⟩
  have hcard :
      (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) c).card : ℝ) =
        (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) a).card : ℝ) +
          (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c).card : ℝ) := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
  simp only [localDiscrepancy]
  rw [hcard, add_div]
  ring

private lemma bddAbove_starDiscrepancy (u : ℕ → ℝ) (N : ℕ) :
    BddAbove (range fun t : Icc (0 : ℝ) 1 ↦ |localDiscrepancy u N 0 t|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨⟨t, ht0, ht1⟩, rfl⟩
  exact abs_localDiscrepancy_le_one u N le_rfl ht0 ht1

private lemma bddAbove_discrepancy (u : ℕ → ℝ) (N : ℕ) :
    BddAbove (range fun p : {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} ↦
      |localDiscrepancy u N p.val.1 p.val.2|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨⟨⟨a, c⟩, ha, hac, hc⟩, rfl⟩
  exact abs_localDiscrepancy_le_one u N ha hac hc

lemma abs_localDiscrepancy_zero_le_starDiscrepancy (u : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |localDiscrepancy u N 0 t| ≤ starDiscrepancy u N :=
  le_ciSup (bddAbove_starDiscrepancy u N) ⟨t, ht0, ht1⟩

lemma abs_localDiscrepancy_le_discrepancy (u : ℕ → ℝ) (N : ℕ) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    |localDiscrepancy u N a c| ≤ discrepancy u N :=
  le_ciSup (bddAbove_discrepancy u N) ⟨(a, c), ha, hac, hc⟩

lemma starDiscrepancy_le {u : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, |localDiscrepancy u N 0 t| ≤ C) :
    starDiscrepancy u N ≤ C := by
  have : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun t ↦ hC t.val t.property

lemma discrepancy_le {u : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hC : ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 → |localDiscrepancy u N a c| ≤ C) :
    discrepancy u N ≤ C := by
  have : Nonempty {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} :=
    ⟨⟨(0, 0), le_rfl, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun ⟨⟨a, c⟩, ha, hac, hc⟩ ↦ hC a c ha hac hc

lemma starDiscrepancy_nonneg (u : ℕ → ℝ) (N : ℕ) : 0 ≤ starDiscrepancy u N :=
  le_trans (abs_nonneg _) (abs_localDiscrepancy_zero_le_starDiscrepancy u N le_rfl zero_le_one)

lemma starDiscrepancy_le_one (u : ℕ → ℝ) (N : ℕ) : starDiscrepancy u N ≤ 1 :=
  starDiscrepancy_le fun _ ht ↦ abs_localDiscrepancy_le_one u N le_rfl ht.1 ht.2

lemma starDiscrepancy_le_discrepancy (u : ℕ → ℝ) (N : ℕ) :
    starDiscrepancy u N ≤ discrepancy u N :=
  starDiscrepancy_le fun _ ht ↦ abs_localDiscrepancy_le_discrepancy u N le_rfl ht.1 ht.2

lemma discrepancy_nonneg (u : ℕ → ℝ) (N : ℕ) : 0 ≤ discrepancy u N :=
  le_trans (starDiscrepancy_nonneg u N) (starDiscrepancy_le_discrepancy u N)

lemma discrepancy_le_one (u : ℕ → ℝ) (N : ℕ) : discrepancy u N ≤ 1 :=
  discrepancy_le fun _ _ ha hac hc ↦ abs_localDiscrepancy_le_one u N ha hac hc

lemma discrepancy_le_two_mul_starDiscrepancy (u : ℕ → ℝ) (N : ℕ) :
    discrepancy u N ≤ 2 * starDiscrepancy u N :=
  discrepancy_le fun a c ha hac hc ↦ by
    rw [localDiscrepancy_eq_sub u N ha hac]
    have h1 := abs_localDiscrepancy_zero_le_starDiscrepancy u N (le_trans ha hac) hc
    have h2 := abs_localDiscrepancy_zero_le_starDiscrepancy u N ha (le_trans hac hc)
    linarith [abs_sub (localDiscrepancy u N 0 c) (localDiscrepancy u N 0 a)]

/-! ### Characterization of equidistribution modulo one and quantitative Wall's theorem -/

/-- A real sequence `u` is equidistributed modulo one iff its star discrepancy `D_N^*(u)` tends
to `0` (Kuipers–Niederreiter, Ch. 2, Theorem 1.1). -/
theorem isEquidistributedModOne_iff_tendsto_starDiscrepancy {u : ℕ → ℝ} :
    IsEquidistributedModOne u ↔ Tendsto (starDiscrepancy u) atTop (𝓝 0) := by
  constructor
  · intro hu
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / ε)
    have hm_pos : 0 < m := by
      have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
      exact_mod_cast this
    have hm_inv : (1 : ℝ) / m < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hε).1 hm
      linarith
    have hgrid : ∀ k ∈ Finset.range (m + 1),
        ∀ᶠ N in atTop, |localDiscrepancy u N 0 ((k : ℝ) / m)| < ε / 2 := by
      intro k hk
      have hkm : (k : ℝ) / m ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have htend := hu 0 ((k : ℝ) / m) le_rfl (by positivity) hkm
      have hsub : Tendsto (fun N ↦ localDiscrepancy u N 0 ((k : ℝ) / m)) atTop (𝓝 0) := by
        simpa only [localDiscrepancy, sub_self] using htend.sub_const ((k : ℝ) / m - 0)
      obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hsub (ε / 2) (half_pos hε)
      exact Filter.eventually_atTop.2 ⟨N₀, fun N hN ↦ by simpa [Real.dist_eq] using hN₀ N hN⟩
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ((Finset.eventually_all _).2 hgrid)
    refine ⟨N₀, fun N hN ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (starDiscrepancy_nonneg u N)]
    have hle : starDiscrepancy u N ≤ ε / 2 + (1 : ℝ) / m := by
      refine starDiscrepancy_le fun t ht ↦ ?_
      by_cases ht1 : t = 1
      · subst ht1
        have h1 := hN₀ N hN m (Finset.mem_range.2 (Nat.lt_succ_self m))
        rw [div_self (by positivity)] at h1
        linarith [show (0 : ℝ) ≤ 1 / m by positivity]
      · have ht_lt : t < 1 := lt_of_le_of_ne ht.2 ht1
        set k := ⌊t * m⌋₊
        have hkm_lt : k < m := by
          rw [Nat.floor_lt (mul_nonneg ht.1 (by positivity))]
          exact mul_lt_of_lt_one_left (by positivity) ht_lt
        have hk1 : (k : ℝ) / m ≤ t := by
          rw [div_le_iff₀ (by positivity)]
          exact Nat.floor_le (mul_nonneg ht.1 (by positivity))
        have hk2 : t ≤ ((k + 1 : ℕ) : ℝ) / m := by
          rw [le_div_iff₀ (by positivity)]
          exact (Nat.lt_floor_add_one (t * m)).le.trans_eq (by push_cast; rfl)
        have hcount_le :
            (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) ((k : ℝ) / m)).card :
                ℝ) / N ≤
              (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card : ℝ) / N := by
          gcongr
        have hcount_ge :
            (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card : ℝ) / N ≤
              (((Finset.range N).filter fun n ↦
                Int.fract (u n) ∈ Ico (0 : ℝ) (((k + 1 : ℕ) : ℝ) / m)).card : ℝ) / N := by
          gcongr
        have hA := hN₀ N hN k (Finset.mem_range.2 (by omega))
        have hB := hN₀ N hN (k + 1) (Finset.mem_range.2 (by omega))
        have hdiff : ((k + 1 : ℕ) : ℝ) / m - (k : ℝ) / m = 1 / m := by
          push_cast; ring
        rw [abs_lt] at hA hB
        rw [abs_le]
        simp only [localDiscrepancy, sub_zero] at hA hB ⊢
        constructor <;> linarith
    linarith
  · intro hD a c ha hac hc
    have hloc : Tendsto (fun N ↦ localDiscrepancy u N a c) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun N ↦ ?_) (by simpa using hD.const_mul 2)
      exact (abs_localDiscrepancy_le_discrepancy u N ha hac hc).trans
        (discrepancy_le_two_mul_starDiscrepancy u N)
    simpa only [localDiscrepancy, zero_add, sub_add_cancel] using hloc.add_const (c - a)

/-- A real sequence `u` is equidistributed modulo one iff its extreme discrepancy `D_N(u)` tends
to `0`. -/
theorem isEquidistributedModOne_iff_tendsto_discrepancy {u : ℕ → ℝ} :
    IsEquidistributedModOne u ↔ Tendsto (discrepancy u) atTop (𝓝 0) := by
  rw [isEquidistributedModOne_iff_tendsto_starDiscrepancy]
  constructor
  · intro h
    exact squeeze_zero (discrepancy_nonneg u) (discrepancy_le_two_mul_starDiscrepancy u)
      (by simpa using h.const_mul 2)
  · intro h
    exact squeeze_zero (starDiscrepancy_nonneg u) (starDiscrepancy_le_discrepancy u) h

/-- **Quantitative Wall's theorem**: the error in the frequency of any base-`b` digit block `w`
of length `k` is bounded by the extreme discrepancy `D_N((x * b ^ n))`. -/
theorem abs_blockCount_div_sub_le_discrepancy {b k : ℕ} (hb : 0 < b) (x : ℝ)
    (w : Fin k → Fin b) (N : ℕ) :
    |(blockCount b x w N : ℝ) / N - ((b : ℝ) ^ k)⁻¹| ≤
      discrepancy (fun n ↦ x * (b : ℝ) ^ n) N := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  set j : ℕ := (blockCode w : ℕ)
  have hj : j < b ^ k := (blockCode w).isLt
  have ha : 0 ≤ (j : ℝ) / (b : ℝ) ^ k := by positivity
  have hac : (j : ℝ) / (b : ℝ) ^ k ≤ ((j : ℝ) + 1) / (b : ℝ) ^ k := by
    gcongr; linarith
  have hc : ((j : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 := by
    rw [div_le_one hB]
    exact_mod_cast Nat.succ_le_of_lt hj
  have hcount : blockCount b x w N =
      ((Finset.range N).filter fun n ↦
        Int.fract (x * (b : ℝ) ^ n) ∈
          Ico ((j : ℝ) / (b : ℝ) ^ k) (((j : ℝ) + 1) / (b : ℝ) ^ k)).card := by
    rw [blockCount_eq_card_floor_fract hb]
    congr 1
    refine Finset.filter_congr fun n _ ↦ ?_
    exact floor_mul_eq_iff_mem_Ico (Int.fract_nonneg _) hB j
  have hlen : ((j : ℝ) + 1) / (b : ℝ) ^ k - (j : ℝ) / (b : ℝ) ^ k = ((b : ℝ) ^ k)⁻¹ := by
    rw [← sub_div, add_sub_cancel_left, one_div]
  rw [hcount, ← hlen]
  exact abs_localDiscrepancy_le_discrepancy (fun n ↦ x * (b : ℝ) ^ n) N ha hac hc

/-- Quantitative Wall's theorem in terms of star discrepancy: the error in the frequency of any
base-`b` digit block `w` is at most `2 * D_N^*((x * b ^ n))`. -/
theorem abs_blockCount_div_sub_le_two_mul_starDiscrepancy {b k : ℕ} (hb : 0 < b) (x : ℝ)
    (w : Fin k → Fin b) (N : ℕ) :
    |(blockCount b x w N : ℝ) / N - ((b : ℝ) ^ k)⁻¹| ≤
      2 * starDiscrepancy (fun n ↦ x * (b : ℝ) ^ n) N :=
  (abs_blockCount_div_sub_le_discrepancy hb x w N).trans
    (discrepancy_le_two_mul_starDiscrepancy _ N)

/-- `x` is normal in base `b ≥ 2` iff the star discrepancy of `(x * b ^ n)` tends to `0`. -/
theorem isNormalIn_iff_tendsto_starDiscrepancy {b : ℕ} (hb : 2 ≤ b) {x : ℝ} :
    IsNormalIn b x ↔
      Tendsto (starDiscrepancy fun n ↦ x * (b : ℝ) ^ n) atTop (𝓝 0) :=
  (isNormalIn_iff_isEquidistributedModOne hb).trans
    isEquidistributedModOne_iff_tendsto_starDiscrepancy

/-! ### Koksma's inequality -/

private lemma sum_integral_div_eq (F : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (hF : ∀ k < N, IntervalIntegrable F volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) :
    ∑ j : Fin N, ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), F t = ∫ t in (0 : ℝ)..1, F t := by
  have h1 : ∑ j : Fin N, ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), F t =
      ∑ k ∈ Finset.range N, ∫ t in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), F t := by
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ ∫ t in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), F t)]
    exact Finset.sum_congr rfl fun k _ ↦ by push_cast; rfl
  rw [h1]
  have h2 := intervalIntegral.sum_integral_adjacent_intervals
    (f := F) (a := fun k : ℕ ↦ (k : ℝ) / N) (n := N) hF
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simpa only [Nat.cast_zero, zero_div, div_self hN0] using h2

/-- **Koksma's inequality** for monotone functions on `[0, 1]`. -/
theorem koksma_inequality_of_monotoneOn {g : ℝ → ℝ} (hg : MonotoneOn g (Icc 0 1))
    (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, g (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, g t| ≤
      (g 1 - g 0) * starDiscrepancy u N := by
  set D := starDiscrepancy u N
  have hD0 : 0 ≤ D := starDiscrepancy_nonneg u N
  let G : ℝ → ℝ := fun t ↦ g (max 0 (min 1 t))
  have hG_mono : Monotone G := fun s t hst ↦
    hg ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
      (max_le_max_left 0 (min_le_min_left 1 hst))
  have hG_eq : ∀ t ∈ Icc (0 : ℝ) 1, G t = g t := fun t ⟨ht0, ht1⟩ ↦ by
    simp only [G, min_eq_right ht1, max_eq_right ht0]
  have hG_le0 : ∀ t ≤ (0 : ℝ), G t = g 0 := fun t ht ↦ by
    simp only [G, min_eq_right (le_trans ht zero_le_one), max_eq_left ht]
  have hG_ge1 : ∀ t, (1 : ℝ) ≤ t → G t = g 1 := fun t ht ↦ by
    simp only [G, min_eq_left ht, max_eq_right zero_le_one]
  let f : Fin N → ℝ := fun i ↦ Int.fract (u i)
  let σ : Equiv.Perm (Fin N) := Tuple.sort f
  let y : Fin N → ℝ := f ∘ σ
  have hy_mono : Monotone y := Tuple.monotone_sort f
  have hy_mem : ∀ j : Fin N, y j ∈ Ico (0 : ℝ) 1 := fun j ↦
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hcard_sort : ∀ t : ℝ,
      ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card =
        (Finset.univ.filter fun k : Fin N ↦ y k < t).card := fun t ↦ by
    refine Finset.card_bij (fun n hn ↦ σ.symm ⟨n, Finset.mem_range.1 (Finset.mem_filter.1 hn).1⟩)
      ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨Finset.mem_univ _, by simpa [y, f] using hn.2.2⟩
    · intro n₁ _ n₂ _ heq
      have := congrArg (fun k : Fin N ↦ (σ k : ℕ)) heq
      simpa using this
    · intro k hk
      rw [Finset.mem_filter] at hk
      exact ⟨(σ k : ℕ), Finset.mem_filter.2 ⟨Finset.mem_range.2 (σ k).isLt,
        Int.fract_nonneg _, hk.2⟩, by simp⟩
  have hy_upper : ∀ j : Fin N, y j - D ≤ (j : ℝ) / N := by
    intro j
    have hcard :
        ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) (y j)).card ≤ j := by
      rw [hcard_sort]
      calc (Finset.univ.filter fun k : Fin N ↦ y k < y j).card
          ≤ (Finset.univ.filter fun k : Fin N ↦ (k : ℕ) < (j : ℕ)).card := by
            refine Finset.card_le_card fun k hk ↦ ?_
            rw [Finset.mem_filter] at hk ⊢
            refine ⟨Finset.mem_univ _, ?_⟩
            by_contra hge
            push Not at hge
            exact not_lt_of_ge (hy_mono (Fin.le_def.2 hge)) hk.2
        _ = (Finset.range (j : ℕ)).card := by
            refine Finset.card_bij (fun k _ ↦ (k : ℕ)) ?_ ?_ ?_
            · intro k hk; exact Finset.mem_range.2 (Finset.mem_filter.1 hk).2
            · intro _ _ _ _ h; exact Fin.ext h
            · intro m hm
              have hmj : m < (j : ℕ) := Finset.mem_range.1 hm
              exact ⟨⟨m, lt_trans hmj j.isLt⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hmj⟩, rfl⟩
        _ = (j : ℕ) := Finset.card_range _
    have hD_j := abs_localDiscrepancy_zero_le_starDiscrepancy u N (hy_mem j).1 (hy_mem j).2.le
    rw [localDiscrepancy, sub_zero, abs_le] at hD_j
    have hcardR :
        (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) (y j)).card : ℝ) / N ≤
          (j : ℝ) / N := by gcongr
    linarith
  have hy_lower : ∀ j : Fin N, ((j : ℝ) + 1) / N ≤ y j + D := by
    intro j
    by_contra hlt
    push Not at hlt
    set δ := min (1 - y j) ((((j : ℝ) + 1) / N - (y j + D)) / 2)
    have hδ : 0 < δ := lt_min (sub_pos.2 (hy_mem j).2) (by linarith)
    set t := y j + δ
    have ht0 : 0 ≤ t := by linarith [(hy_mem j).1]
    have ht1 : t ≤ 1 := by linarith [min_le_left (1 - y j) ((((j : ℝ) + 1) / N - (y j + D)) / 2)]
    have hcard : (j : ℕ) + 1 ≤
        ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card := by
      rw [hcard_sort]
      calc (j : ℕ) + 1 = (Finset.range ((j : ℕ) + 1)).card := (Finset.card_range _).symm
        _ = (Finset.univ.filter fun k : Fin N ↦ (k : ℕ) ≤ (j : ℕ)).card := by
            symm
            refine Finset.card_bij (fun k _ ↦ (k : ℕ)) ?_ ?_ ?_
            · intro k hk; exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_filter.1 hk).2)
            · intro _ _ _ _ h; exact Fin.ext h
            · intro m hm
              have hmj : m ≤ (j : ℕ) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
              exact ⟨⟨m, lt_of_le_of_lt hmj j.isLt⟩,
                Finset.mem_filter.2 ⟨Finset.mem_univ _, hmj⟩, rfl⟩
        _ ≤ (Finset.univ.filter fun k : Fin N ↦ y k < t).card := by
            refine Finset.card_le_card fun k hk ↦ ?_
            rw [Finset.mem_filter] at hk ⊢
            exact ⟨Finset.mem_univ _, lt_of_le_of_lt (hy_mono (Fin.le_def.2 hk.2)) (by linarith)⟩
    have hD_t := abs_localDiscrepancy_zero_le_starDiscrepancy u N ht0 ht1
    rw [localDiscrepancy, sub_zero, abs_le] at hD_t
    have hcardR : ((j : ℝ) + 1) / N ≤
        (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card : ℝ) / N := by
      gcongr; exact_mod_cast hcard
    have hδ_le : δ ≤ (((j : ℝ) + 1) / N - (y j + D)) / 2 := min_le_right _ _
    linarith
  have hsum_eq : (∑ n ∈ Finset.range N, g (Int.fract (u n))) / N =
      ∑ j : Fin N, g (y j) / N := by
    rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
    exact (Equiv.sum_comp σ fun i : Fin N ↦ g (f i) / N).symm
  have hint_eq : ∫ t in (0 : ℝ)..1, g t = ∫ t in (0 : ℝ)..1, G t :=
    intervalIntegral.integral_congr fun t ht ↦
      (hG_eq t (by rwa [uIcc_of_le zero_le_one] at ht)).symm
  have hG_int : ∀ a b : ℝ, IntervalIntegrable G volume a b := fun a b ↦
    (hG_mono.monotoneOn _).intervalIntegrable
  have hG_add_int : ∀ a b : ℝ, IntervalIntegrable (fun t ↦ G (t + D)) volume a b := fun a b ↦
    ((hG_mono.comp fun _ _ h ↦ add_le_add_left h D).monotoneOn _).intervalIntegrable
  have hG_sub_int : ∀ a b : ℝ, IntervalIntegrable (fun t ↦ G (t - D)) volume a b := fun a b ↦
    ((hG_mono.comp fun _ _ h ↦ sub_le_sub_right h D).monotoneOn _).intervalIntegrable
  have hupper : (∑ n ∈ Finset.range N, g (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, g t ≤
      (g 1 - g 0) * D := by
    rw [hsum_eq, hint_eq]
    have hstep : ∀ j : Fin N, g (y j) / N ≤
        ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), G (t + D) := fun j ↦ by
      have hab : (j : ℝ) / N ≤ ((j : ℝ) + 1) / N := by gcongr; linarith
      calc g (y j) / N
          = ∫ _ in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), g (y j) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            field_simp [Nat.cast_ne_zero.2 hN.ne']; ring
        _ ≤ ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), G (t + D) := by
            refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
              (hG_add_int _ _) fun t ht ↦ ?_
            rw [← hG_eq (y j) ⟨(hy_mem j).1, (hy_mem j).2.le⟩]
            exact hG_mono (by linarith [hy_upper j, ht.1])
    have hsum_int : ∑ j : Fin N, ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), G (t + D) =
        ∫ t in (0 : ℝ)..1, G (t + D) :=
      sum_integral_div_eq (fun t ↦ G (t + D)) hN fun k _ ↦ hG_add_int _ _
    have hshift : ∫ t in (0 : ℝ)..1, G (t + D) = ∫ s in D..(1 + D), G s := by
      simp [zero_add]
    have hsplit : (∫ s in D..(1 + D), G s) - ∫ s in (0 : ℝ)..1, G s =
        (∫ s in (1 : ℝ)..(1 + D), G s) - ∫ s in (0 : ℝ)..D, G s := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals (hG_int 0 D) (hG_int D (1 + D))
      have h2 := intervalIntegral.integral_add_adjacent_intervals (hG_int 0 1) (hG_int 1 (1 + D))
      linarith
    have htail1 : ∫ s in (1 : ℝ)..(1 + D), G s = g 1 * D := by
      have hcongr : ∫ s in (1 : ℝ)..(1 + D), G s = ∫ _ in (1 : ℝ)..(1 + D), g 1 :=
        intervalIntegral.integral_congr fun s hs ↦
          hG_ge1 s (by rw [uIcc_of_le (by linarith)] at hs; exact hs.1)
      rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]; ring
    have htail0 : g 0 * D ≤ ∫ s in (0 : ℝ)..D, G s := by
      calc g 0 * D = ∫ _ in (0 : ℝ)..D, g 0 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ ≤ ∫ s in (0 : ℝ)..D, G s := by
            refine intervalIntegral.integral_mono_on hD0 intervalIntegrable_const (hG_int 0 D)
              fun s hs ↦ ?_
            rw [← hG_le0 0 le_rfl]
            exact hG_mono hs.1
    have hle := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ hstep j
    rw [hsum_int, hshift] at hle
    linarith
  have hlower : -((g 1 - g 0) * D) ≤
      (∑ n ∈ Finset.range N, g (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, g t := by
    rw [hsum_eq, hint_eq]
    have hstep : ∀ j : Fin N,
        ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), G (t - D) ≤ g (y j) / N := fun j ↦ by
      have hab : (j : ℝ) / N ≤ ((j : ℝ) + 1) / N := by gcongr; linarith
      calc ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), G (t - D)
          ≤ ∫ _ in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), g (y j) := by
            refine intervalIntegral.integral_mono_on hab (hG_sub_int _ _)
              intervalIntegrable_const fun t ht ↦ ?_
            rw [← hG_eq (y j) ⟨(hy_mem j).1, (hy_mem j).2.le⟩]
            exact hG_mono (by linarith [hy_lower j, ht.2])
        _ = g (y j) / N := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            field_simp [Nat.cast_ne_zero.2 hN.ne']; ring
    have hsum_int : ∑ j : Fin N, ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), G (t - D) =
        ∫ t in (0 : ℝ)..1, G (t - D) :=
      sum_integral_div_eq (fun t ↦ G (t - D)) hN fun k _ ↦ hG_sub_int _ _
    have hshift : ∫ t in (0 : ℝ)..1, G (t - D) = ∫ s in (-D)..(1 - D), G s := by
      simp [zero_sub]
    have hsplit : (∫ s in (-D)..(1 - D), G s) - ∫ s in (0 : ℝ)..1, G s =
        (∫ s in (-D)..(0 : ℝ), G s) - ∫ s in (1 - D)..1, G s := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals (hG_int (-D) 0) (hG_int 0 1)
      have h2 := intervalIntegral.integral_add_adjacent_intervals (hG_int (-D) (1 - D))
        (hG_int (1 - D) 1)
      linarith
    have htail0 : ∫ s in (-D)..(0 : ℝ), G s = g 0 * D := by
      have hcongr : ∫ s in (-D)..(0 : ℝ), G s = ∫ _ in (-D)..(0 : ℝ), g 0 :=
        intervalIntegral.integral_congr fun s hs ↦
          hG_le0 s (by rw [uIcc_of_le (by linarith)] at hs; exact hs.2)
      rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]; ring
    have htail1 : ∫ s in (1 - D)..1, G s ≤ g 1 * D := by
      calc ∫ s in (1 - D)..1, G s
          ≤ ∫ _ in (1 - D)..1, g 1 := by
            refine intervalIntegral.integral_mono_on (by linarith) (hG_int (1 - D) 1)
              intervalIntegrable_const fun s hs ↦ ?_
            rw [← hG_ge1 1 le_rfl]
            exact hG_mono hs.2
        _ = g 1 * D := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hge := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ hstep j
    rw [hsum_int, hshift] at hge
    linarith
  exact abs_le.2 ⟨hlower, hupper⟩

/-- **Koksma's inequality** (sharp form for functions of bounded variation on `[0, 1]`):
for any `f : ℝ → ℝ` with `BoundedVariationOn f (Icc 0 1)` and `N ≥ 1`,
`|(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in 0..1, f t| ≤ V_0^1(f) * D_N^*(u)`. -/
theorem koksma_inequality {f : ℝ → ℝ} (hf : BoundedVariationOn f (Icc 0 1))
    (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, f t| ≤
      (eVariationOn f (Icc 0 1)).toReal * starDiscrepancy u N := by
  let v : ℝ → ℝ := fun x ↦ (eVariationOn f (Icc 0 x)).toReal
  let p₁ : ℝ → ℝ := fun x ↦ (v x + f x) / 2
  let p₂ : ℝ → ℝ := fun x ↦ (v x - f x) / 2
  have hv_fin : ∀ x ∈ Icc (0 : ℝ) 1, eVariationOn f (Icc 0 x) ≠ ⊤ := fun x hx ↦
    ne_top_of_le_ne_top hf (eVariationOn.mono f (Icc_subset_Icc_right hx.2))
  have hv_add : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x ≤ y →
      v y - v x = (eVariationOn f (Icc x y)).toReal := by
    intro x hx y hy hxy
    have hsplit :
        eVariationOn f (Icc 0 x) + eVariationOn f (Icc x y) = eVariationOn f (Icc 0 y) := by
      simpa only [univ_inter] using eVariationOn.Icc_add_Icc f (s := univ) hx.1 hxy (mem_univ x)
    have hxy_fin : eVariationOn f (Icc x y) ≠ ⊤ :=
      ne_top_of_le_ne_top hf (eVariationOn.mono f (Icc_subset_Icc hx.1 hy.2))
    have := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add (hv_fin x hx) hxy_fin] at this
    dsimp only [v]
    linarith
  have hdist : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x ≤ y →
      |f y - f x| ≤ v y - v x := by
    intro x hx y hy hxy
    rw [hv_add x hx y hy hxy, ← Real.dist_eq]
    have hbv : BoundedVariationOn f (Icc x y) :=
      hf.mono (Icc_subset_Icc hx.1 hy.2)
    exact hbv.dist_le ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩
  have hp₁ : MonotoneOn p₁ (Icc 0 1) := fun x hx y hy hxy ↦ by
    have h := (abs_le.1 (hdist x hx y hy hxy)).1
    dsimp only [p₁]; linarith
  have hp₂ : MonotoneOn p₂ (Icc 0 1) := fun x hx y hy hxy ↦ by
    have h := (abs_le.1 (hdist x hx y hy hxy)).2
    dsimp only [p₂]; linarith
  have hf_eq : ∀ x, f x = p₁ x - p₂ x := fun x ↦ by dsimp only [p₁, p₂]; ring
  have hv0 : v 0 = 0 := by
    dsimp only [v]
    rw [Icc_self, eVariationOn.subsingleton f subsingleton_singleton, ENNReal.toReal_zero]
  have hp_sum : (p₁ 1 - p₁ 0) + (p₂ 1 - p₂ 0) = (eVariationOn f (Icc 0 1)).toReal := by
    dsimp only [p₁, p₂, v] at hv0 ⊢
    linarith
  have h1 := koksma_inequality_of_monotoneOn hp₁ u hN
  have h2 := koksma_inequality_of_monotoneOn hp₂ u hN
  have huIcc : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hint1 : IntervalIntegrable p₁ volume 0 1 := (huIcc.symm ▸ hp₁).intervalIntegrable
  have hint2 : IntervalIntegrable p₂ volume 0 1 := (huIcc.symm ▸ hp₂).intervalIntegrable
  have hdiff : (∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, f t =
      ((∑ n ∈ Finset.range N, p₁ (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, p₁ t) -
        ((∑ n ∈ Finset.range N, p₂ (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, p₂ t) := by
    simp_rw [hf_eq, Finset.sum_sub_distrib, sub_div, intervalIntegral.integral_sub hint1 hint2]
    ring
  rw [hdiff]
  calc |((∑ n ∈ Finset.range N, p₁ (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, p₁ t) -
          ((∑ n ∈ Finset.range N, p₂ (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, p₂ t)|
      ≤ |(∑ n ∈ Finset.range N, p₁ (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, p₁ t| +
          |(∑ n ∈ Finset.range N, p₂ (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, p₂ t| :=
        abs_sub _ _
    _ ≤ (p₁ 1 - p₁ 0) * starDiscrepancy u N + (p₂ 1 - p₂ 0) * starDiscrepancy u N :=
        add_le_add h1 h2
    _ = (eVariationOn f (Icc 0 1)).toReal * starDiscrepancy u N := by
        rw [← add_mul, hp_sum]

/-- **Koksma's inequality** for differentiable functions with integrable derivative on `[0, 1]`. -/
theorem koksma_inequality_of_hasDerivAt {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, f t| ≤
      (∫ t in (0 : ℝ)..1, |f' t|) * starDiscrepancy u N := by
  have hftc : ∀ x ∈ Icc (0 : ℝ) 1, f x = f 1 - ∫ t in x..1, f' t := fun x hx ↦ by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hderiv t (by
        rw [uIcc_of_le hx.2] at ht
        exact ⟨le_trans hx.1 ht.1, ht.2⟩))
      (hint.mono_set (uIcc_subset_uIcc (by simp [hx.1, hx.2]) (by simp)))
    linarith
  have hibp : ∫ t in (0 : ℝ)..1, f t = f 1 - ∫ t in (0 : ℝ)..1, t * f' t := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun t : ℝ ↦ t) (u' := fun _ ↦ (1 : ℝ)) (v := f) (v' := f')
      (fun t _ ↦ hasDerivAt_id t)
      (fun t ht ↦ hderiv t (by rwa [uIcc_of_le zero_le_one] at ht))
      intervalIntegrable_const hint
    simp only [one_mul, zero_mul, sub_zero] at h
    linarith
  have hind_int : ∀ x ∈ Ico (0 : ℝ) 1,
      IntervalIntegrable ((Ioi x).indicator f') volume 0 1 := fun x _ ↦ by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hint.1.indicator measurableSet_Ioi
  have hind : ∀ x ∈ Ico (0 : ℝ) 1,
      ∫ t in x..1, f' t = ∫ t in (0 : ℝ)..1, (Ioi x).indicator f' t := fun x hx ↦ by
    have h1 : IntervalIntegrable ((Ioi x).indicator f') volume 0 x :=
      (hind_int x hx).mono_set (uIcc_subset_uIcc (by simp) (by simp [hx.1, hx.2.le]))
    have h2 : IntervalIntegrable ((Ioi x).indicator f') volume x 1 :=
      (hind_int x hx).mono_set (uIcc_subset_uIcc (by simp [hx.1, hx.2.le]) (by simp))
    have h0 : ∫ t in (0 : ℝ)..x, (Ioi x).indicator f' t = 0 := by
      rw [intervalIntegral.integral_of_le hx.1]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦
        Set.indicator_of_notMem (not_lt.2 ht.2) _
    have h3 : ∫ t in x..1, (Ioi x).indicator f' t = ∫ t in x..1, f' t := by
      rw [intervalIntegral.integral_of_le hx.2.le, intervalIntegral.integral_of_le hx.2.le]
      exact setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ Set.indicator_of_mem ht.1 _
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, h0, zero_add, h3]
  have hsum_int : IntervalIntegrable
      (fun t : ℝ ↦ (∑ n ∈ Finset.range N, (Ioi (Int.fract (u n))).indicator f' t) / N)
      volume 0 1 := by
    have h1 : ∀ s : Finset ℕ, IntervalIntegrable
        (fun t : ℝ ↦ ∑ n ∈ s, (Ioi (Int.fract (u n))).indicator f' t) volume 0 1 := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simp
      | cons a s ha ih =>
        simpa only [Finset.sum_cons] using
          (hind_int _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩).add ih
    exact (h1 (Finset.range N)).div_const _
  have hcard_eq : ∀ t : ℝ,
      ∑ n ∈ Finset.range N, (Ioi (Int.fract (u n))).indicator f' t =
        (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico (0 : ℝ) t).card : ℝ) * f' t := by
    intro t
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hlt : Int.fract (u n) < t
    · simp [Int.fract_nonneg, hlt]
    · simp [hlt]
  have hmean :
      (∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, f t =
        -(∫ t in (0 : ℝ)..1, f' t * localDiscrepancy u N 0 t) := by
    have hsum : (∑ n ∈ Finset.range N, f (Int.fract (u n))) / N =
        f 1 - ∫ t in (0 : ℝ)..1,
          (∑ n ∈ Finset.range N, (Ioi (Int.fract (u n))).indicator f' t) / N := by
      have h1 : ∀ n ∈ Finset.range N,
          f (Int.fract (u n)) = f 1 - ∫ t in (0 : ℝ)..1, (Ioi (Int.fract (u n))).indicator f' t :=
        fun n _ ↦ by
          rw [hftc _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
            hind _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩]
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hN.ne'),
        ← intervalIntegral.integral_finsetSum fun n _ ↦
          hind_int _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
        ← intervalIntegral.integral_div]
    have htf' : IntervalIntegrable (fun t : ℝ ↦ t * f' t) volume 0 1 :=
      hint.continuousOn_mul continuousOn_id
    rw [hsum, hibp]
    have hsub_int : (∫ t in (0 : ℝ)..1, t * f' t) -
        ∫ t in (0 : ℝ)..1,
          (∑ n ∈ Finset.range N, (Ioi (Int.fract (u n))).indicator f' t) / N =
        -(∫ t in (0 : ℝ)..1, f' t * localDiscrepancy u N 0 t) := by
      rw [← intervalIntegral.integral_sub htf' hsum_int, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      rw [hcard_eq t, localDiscrepancy, sub_zero]
      ring
    linarith
  rw [hmean, abs_neg]
  have hprod_int : IntervalIntegrable (fun t : ℝ ↦ f' t * localDiscrepancy u N 0 t) volume 0 1 := by
    have h1 : IntervalIntegrable (fun t : ℝ ↦
        (∑ n ∈ Finset.range N, (Ioi (Int.fract (u n))).indicator f' t) / N - t * f' t) volume 0 1 :=
      hsum_int.sub (hint.continuousOn_mul continuousOn_id)
    refine h1.congr fun t _ ↦ ?_
    rw [hcard_eq t, localDiscrepancy, sub_zero]; ring
  calc |∫ t in (0 : ℝ)..1, f' t * localDiscrepancy u N 0 t|
      ≤ ∫ t in (0 : ℝ)..1, |f' t * localDiscrepancy u N 0 t| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, |f' t| * starDiscrepancy u N := by
        refine intervalIntegral.integral_mono_on zero_le_one hprod_int.abs
          (hint.abs.mul_const _) fun t ht ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_localDiscrepancy_zero_le_starDiscrepancy u N ht.1 ht.2) (abs_nonneg _)
    _ = (∫ t in (0 : ℝ)..1, |f' t|) * starDiscrepancy u N :=
        intervalIntegral.integral_mul_const _ _

end Real
