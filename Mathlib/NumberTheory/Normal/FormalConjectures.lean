/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.FormalConjectures.Analysis.Equidistribution.ModOne
public import Mathlib.Imported.FormalConjectures.NumberTheory.NormalNumber
public import Mathlib.NumberTheory.Normal.Wall

/-!
# Formal Conjectures' normal numbers and `Real.IsNormalIn`

Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
project states Borel's conjecture (`FormalConjectures/Wikipedia/AlgebraicNormality.lean`) and
Wall's theorem (`FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean`) in terms
of its own definitions, imported in `Mathlib/Imported/FormalConjectures`: digits are
`NormalNumber.digitSeq`, blocks are words `Fin k → ℕ` with letters `< b`, and equidistribution
modulo one counts closed intervals `[c, d]`. We show that each of these notions agrees with ours,
so that results proved here answer the statements there and conversely.

## Main statements

* `Real.digitSeq_eq_digit`: `NormalNumber.digitSeq` is `Real.digit`.
* `Real.isNormalInBase_iff_isNormalIn`, `Real.isSimplyNormalInBase_iff_isSimplyNormalIn`,
  `Real.isAbsolutelyNormal_iff`, `Real.isRichInBase_iff_isDisjunctiveIn`: the notions of
  normality agree.
* `Real.isEquidistributedModuloOne_iff`: equidistribution with closed and with half-open
  intervals agree.
* `Real.isNormalInBase_iff_isEquidistributedModuloOne`: Wall's theorem in Formal Conjectures'
  form (stated there with `sorry`).
* `Real.borelConjecture_iff`: Formal Conjectures' statement of Borel's conjecture is the one in
  `Wanted/NumberTheory/Normal/Basic.lean`.

## References

* [D. D. Wall, *Normal numbers*, PhD thesis, UC Berkeley, 1949][Wall1949]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

@[expose] public section

open Filter Topology Set

namespace Real

variable {b : ℕ} {x : ℝ}

theorem digitSeq_eq_digit (b : ℕ) (x : ℝ) (n : ℕ) :
    NormalNumber.digitSeq b x n = digit b x n := by
  rw [← digit_fract, NormalNumber.digitSeq, digit, mul_comm,
    ← Int.natCast_floor_eq_floor (by positivity [Int.fract_nonneg x]), ← Int.natCast_mod,
    Int.toNat_natCast]

/-- Formal Conjectures' block counts are `Real.blockCount`. -/
theorem card_filter_digitSeq_eq_blockCount {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    ((Finset.range N).filter fun i ↦ ∀ j : Fin k,
      NormalNumber.digitSeq b x (i + j) = w j).card = blockCount b x w N := by
  classical
  simp only [blockCount, digitSeq_eq_digit]

theorem isNormalInBase_iff_isNormalIn :
    NormalNumber.IsNormalInBase b x ↔ IsNormalIn b x := by
  refine ⟨fun h k w ↦ ?_, fun h k w hw ↦ ?_⟩
  · simpa [one_div, card_filter_digitSeq_eq_blockCount] using
      h k (fun j ↦ w j) fun j ↦ (w j).isLt
  · simpa [one_div, ← card_filter_digitSeq_eq_blockCount] using
      h k fun j ↦ ⟨w j, hw j⟩

theorem isSimplyNormalInBase_iff_isSimplyNormalIn :
    NormalNumber.IsSimplyNormalInBase b x ↔ IsSimplyNormalIn b x := by
  refine ⟨fun h d ↦ ?_, fun h d hd ↦ ?_⟩
  · simpa [one_div, ← card_filter_digitSeq_eq_blockCount, Fin.forall_fin_one] using h d d.isLt
  · simpa [one_div, ← card_filter_digitSeq_eq_blockCount, Fin.forall_fin_one] using
      h ⟨d, hd⟩

theorem isAbsolutelyNormal_iff :
    NormalNumber.IsAbsolutelyNormal x ↔ IsAbsolutelyNormal x :=
  forall₂_congr fun _ _ ↦ isNormalInBase_iff_isNormalIn

theorem isRichInBase_iff_isDisjunctiveIn :
    NormalNumber.IsRichInBase b x ↔ IsDisjunctiveIn b x := by
  refine ⟨fun h k w ↦ ?_, fun h k w hw ↦ ?_⟩
  · simpa [digitSeq_eq_digit] using h k (fun j ↦ w j) fun j ↦ (w j).isLt
  · obtain ⟨i, hi⟩ := h k fun j ↦ ⟨w j, hw j⟩
    exact ⟨i, fun j ↦ by simpa [digitSeq_eq_digit] using hi j⟩

/-- The proportion of `n < N` with `Int.fract (u n) ∈ s`. -/
private noncomputable def freq (u : ℕ → ℝ) (s : Set ℝ) (N : ℕ) : ℝ :=
  open Classical in ((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ s).card / N

private theorem freq_eq (u : ℕ → ℝ) (s : Set ℝ) [DecidablePred fun n ↦ Int.fract (u n) ∈ s] :
    freq u s = fun N ↦ (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ s).card : ℝ) / N := by
  funext N; unfold freq; congr

private theorem freq_mono (u : ℕ → ℝ) {s t : Set ℝ} (hst : s ⊆ t) (N : ℕ) :
    freq u s N ≤ freq u t N := by
  classical
  unfold freq
  gcongr

/-- If `f` is squeezed between sequences tending to `L - ε` and `L + ε` for small `ε > 0`, then
`f` tends to `L`. -/
private theorem tendsto_of_squeeze {f : ℕ → ℝ} {L : ℝ}
    (hlow : ∀ l < L, ∃ g : ℕ → ℝ, ∃ L', l < L' ∧ Tendsto g atTop (𝓝 L') ∧ g ≤ f)
    (hup : ∀ l > L, ∃ g : ℕ → ℝ, ∃ L', L' < l ∧ Tendsto g atTop (𝓝 L') ∧ f ≤ g) :
    Tendsto f atTop (𝓝 L) := by
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · obtain ⟨g, L', hl', hg, hgf⟩ := hlow l hl
    exact (hg.eventually (lt_mem_nhds hl')).mono fun n hn ↦ hn.trans_le (hgf n)
  · obtain ⟨g, L', hl', hg, hfg⟩ := hup l hl
    exact (hg.eventually (gt_mem_nhds hl')).mono fun n hn ↦ (hfg n).trans_lt hn

/-- Equidistribution modulo one does not depend on whether closed or half-open intervals are
counted. -/
theorem isEquidistributedModuloOne_iff {u : ℕ → ℝ} :
    IsEquidistributedModuloOne u ↔ IsEquidistributedModOne u := by
  have hfr (n : ℕ) : Int.fract (u n) < 1 := Int.fract_lt_one _
  constructor
  · intro h a c ha hac hc
    have hcc (c' : ℝ) (hac' : a ≤ c') (hc' : c' ≤ 1) :
        Tendsto (freq u (Icc a c')) atTop (𝓝 (c' - a)) := by
      rw [freq_eq]; simpa using h a c' hac' (Icc_subset_Icc ha hc')
    rw [← freq_eq]
    rcases hac.eq_or_lt with rfl | hac
    · rw [freq_eq]; simp
    refine tendsto_of_squeeze (fun l hl ↦ ?_) fun l hl ↦
      ⟨_, _, by linarith, hcc c hac.le hc, freq_mono u Ico_subset_Icc_self⟩
    set c' := max (a + (c - a) / 2) (a + (l + (c - a)) / 2) with hc'
    have hc'c : c' < c := max_lt (by linarith) (by linarith)
    have h1 := le_max_left (a + (c - a) / 2) (a + (l + (c - a)) / 2)
    have h2 := le_max_right (a + (c - a) / 2) (a + (l + (c - a)) / 2)
    refine ⟨_, c' - a, by linarith, hcc c' (by linarith) (by linarith), freq_mono u ?_⟩
    exact Icc_subset_Ico_right hc'c
  · intro h c d hcd hsub
    obtain ⟨hc, hd⟩ : 0 ≤ c ∧ d ≤ 1 := by
      have := hsub ⟨le_rfl, hcd⟩; have := hsub ⟨hcd, le_rfl⟩; grind
    have hco (d' : ℝ) (hcd' : c ≤ d') (hd' : d' ≤ 1) :
        Tendsto (freq u (Ico c d')) atTop (𝓝 (d' - c)) := by rw [freq_eq]; exact h c d' hc hcd' hd'
    rw [show (fun n ↦ (((Finset.range n).filter fun m ↦ (fun n ↦ Int.fract (u n)) m ∈ Icc c d).card
      : ℝ) / n) = freq u (Icc c d) from (freq_eq u _).symm]
    rw [sub_zero, div_one]
    rcases hd.eq_or_lt with rfl | hd
    · have : freq u (Icc c 1) = freq u (Ico c 1) := by
        classical
        funext N; unfold freq; congr 3; ext n; simp [(hfr n).le, hfr n]
      exact this ▸ hco 1 hcd le_rfl
    refine tendsto_of_squeeze (fun l hl ↦
      ⟨_, _, hl, hco d hcd hd.le, freq_mono u Ico_subset_Icc_self⟩) fun l hl ↦ ?_
    set d' := min (d + (1 - d) / 2) (c + (l + (d - c)) / 2) with hd'
    have hdd' : d < d' := lt_min (by linarith) (by linarith)
    have h1 := min_le_left (d + (1 - d) / 2) (c + (l + (d - c)) / 2)
    have h2 := min_le_right (d + (1 - d) / 2) (c + (l + (d - c)) / 2)
    refine ⟨_, d' - c, by linarith, hco d' (by linarith) (by linarith), freq_mono u ?_⟩
    exact Icc_subset_Ico_right hdd'

/-- **Wall's theorem** in the form stated by Formal Conjectures
(`BugeaudNormalAndRich.isNormalInBase_iff_isEquidistributedModuloOne`, [Bug12, Theorem 4.14]). -/
theorem isNormalInBase_iff_isEquidistributedModuloOne (hb : 2 ≤ b) (ξ : ℝ) :
    NormalNumber.IsNormalInBase b ξ ↔ IsEquidistributedModuloOne fun n ↦ (b : ℝ) ^ n * ξ := by
  simp_rw [isNormalInBase_iff_isNormalIn, isEquidistributedModuloOne_iff, mul_comm _ ξ]
  exact isNormalIn_iff_isEquidistributedModOne hb

/-- Formal Conjectures' statement of **Borel's conjecture**
(`AlgebraicNormality.irrational_algebraic_absolutely_normal`) is
`Real.isAbsolutelyNormal_of_isAlgebraic` in `Wanted/NumberTheory/Normal/Basic.lean`. -/
theorem borelConjecture_iff :
    (∀ x : ℝ, IsAlgebraic ℚ x ∧ Irrational x → NormalNumber.IsAbsolutelyNormal x) ↔
      ∀ x : ℝ, IsAlgebraic ℚ x → Irrational x → IsAbsolutelyNormal x := by
  simp [isAbsolutelyNormal_iff]

end Real
