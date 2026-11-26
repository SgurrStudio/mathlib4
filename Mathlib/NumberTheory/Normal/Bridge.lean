/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.NormalNumbers.Counting
public import Mathlib.Imported.NormalNumbers.RealDefs
public import Mathlib.NumberTheory.Normal.Basic

/-!
# Morris's normality and `Real.IsNormalIn`

The files imported from Trevor Morris's `normal-numbers` project (`Mathlib/Imported/NormalNumbers`)
state normality as `NormalNumbers.IsNormal b x`: the digit sequence of `Int.fract x` is a normal
sequence, with blocks given as lists of naturals and counted by `NormalNumbers.countOccurrences`.
We show that this is the same as `Real.IsNormalIn b x`, so that each imported theorem becomes a
statement about `Real.IsNormalIn` in one line.

## Main statements

* `Real.digitOf_fract`: Morris's digit map on `Int.fract x` is `Real.digit`.
* `Real.isNormalIn_iff_isNormal`: the two notions of normality agree.

## References

* Trevor Morris, [normal-numbers](https://github.com/gotrevor/normal-numbers) (`RealDefs.lean`, `Counting.lean`)
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

theorem digitOf_fract (b : ℕ) (x : ℝ) (i : ℕ) :
    NormalNumbers.digitOf b (Int.fract x) i = digit b x i := by
  rw [← digit_fract, digit, NormalNumbers.digitOf,
    Int.toNat_emod (Int.floor_nonneg.2 (mul_nonneg (Int.fract_nonneg x) (by positivity)))
      (by positivity)]
  simp

/-- Morris's occurrence count of a nonempty block differs from `blockCount` by at most the block
length (occurrences overlapping the end of the prefix are counted only by `blockCount`). -/
theorem countOccurrences_le_blockCount {k : ℕ} (hk : 0 < k) (w : Fin k → Fin b)
    (N : ℕ) :
    NormalNumbers.countOccurrences (List.ofFn fun j ↦ (w j : ℕ))
        ((List.range N).map (NormalNumbers.digitOf b (Int.fract x))) ≤ blockCount b x w N ∧
      blockCount b x w N ≤ NormalNumbers.countOccurrences (List.ofFn fun j ↦ (w j : ℕ))
        ((List.range N).map (NormalNumbers.digitOf b (Int.fract x))) + k := by
  classical
  set wl : List ℕ := List.ofFn fun j : Fin k ↦ (w j : ℕ)
  rw [NormalNumbers.countOccurrences_range_map]
  simp only [wl, List.length_ofFn]
  have hM : ∀ i, NormalNumbers.MatchesAt (NormalNumbers.digitOf b (Int.fract x)) wl i ↔
      ∀ j : Fin k, digit b x (i + j) = w j := fun i ↦ by
    simp only [NormalNumbers.MatchesAt, wl, List.length_ofFn, digitOf_fract,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    constructor
    · intro hi j; simpa [j.isLt] using hi j j.isLt
    · intro hi j hj; simpa [hj] using hi ⟨j, hj⟩
  constructor
  · refine Finset.card_le_card fun i hi ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, (hM i).1 hi.2.2⟩
  · have hsub : ((Finset.range N).filter fun i ↦ ∀ j : Fin k, digit b x (i + j) = w j) ⊆
        ((Finset.range (N + 1)).filter fun i ↦ i + k ≤ N ∧
          NormalNumbers.MatchesAt (NormalNumbers.digitOf b (Int.fract x)) wl i) ∪
          Finset.Ico (N - k) N := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      by_cases hik : i + k ≤ N
      · exact Or.inl ⟨by omega, hik, (hM i).2 hi.2⟩
      · exact Or.inr ⟨by omega, hi.1⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    simp only [Nat.card_Ico]
    exact Nat.add_le_add_left (by omega) _

/-- **The bridge**: Morris's `NormalNumbers.IsNormal` is `Real.IsNormalIn`. -/
theorem isNormalIn_iff_isNormal (b : ℕ) (x : ℝ) :
    IsNormalIn b x ↔ NormalNumbers.IsNormal b x := by
  classical
  -- Counts within a bounded distance have the same limiting frequency.
  have key : ∀ {k : ℕ} (_ : 0 < k) (w : Fin k → Fin b) (L : ℝ),
      Tendsto (fun N : ℕ ↦ (blockCount b x w N : ℝ) / N) atTop (𝓝 L) ↔
      Tendsto (fun N : ℕ ↦ (NormalNumbers.countOccurrences (List.ofFn fun j ↦ (w j : ℕ))
        ((List.range N).map (NormalNumbers.digitOf b (Int.fract x))) : ℝ) / N) atTop (𝓝 L) := by
    intro k hk w L
    have hk0 : Tendsto (fun n : ℕ ↦ (k : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)
    have h1 := fun N ↦ (countOccurrences_le_blockCount (x := x) hk w N).1
    have h2 := fun N ↦ (countOccurrences_le_blockCount (x := x) hk w N).2
    constructor
    · intro h
      have hlo : Tendsto (fun n : ℕ ↦ (blockCount b x w n : ℝ) / n - k / n) atTop (𝓝 (L - 0)) :=
        h.sub hk0
      rw [sub_zero] at hlo
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo h (fun n ↦ ?_) fun n ↦ ?_
      · rw [← sub_div]
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have := h2 n; rw [sub_le_iff_le_add]; exact_mod_cast this
      · exact div_le_div_of_nonneg_right (by exact_mod_cast h1 n) (Nat.cast_nonneg _)
    · intro h
      have hup := h.add hk0
      rw [add_zero] at hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le h hup (fun n ↦ ?_) fun n ↦ ?_
      · exact div_le_div_of_nonneg_right (by exact_mod_cast h1 n) (Nat.cast_nonneg _)
      · rw [← add_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast h2 n) (Nat.cast_nonneg _)
  constructor
  · intro h wl hne hlt
    have hw : List.ofFn (fun j : Fin wl.length ↦
        ((⟨wl[j], hlt _ (List.getElem_mem _)⟩ : Fin b) : ℕ)) = wl := List.ofFn_getElem
    have := (key (List.length_pos_iff.2 hne) _ _).1
      (h wl.length fun j ↦ ⟨wl[j], hlt _ (List.getElem_mem _)⟩)
    rwa [hw] at this
  · intro h k w
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have e : ∀ N, blockCount b x w N = N := fun N ↦ by simp [blockCount]
      simp only [e, pow_zero, inv_one]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [div_self (by positivity)]
    refine (key hk w _).2 ?_
    have := h (List.ofFn fun j ↦ (w j : ℕ)) (by simp; omega) (by simp)
    simpa only [List.length_ofFn] using this

end Real
