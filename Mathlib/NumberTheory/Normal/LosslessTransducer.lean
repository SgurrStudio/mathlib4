/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.PiatetskiShapiro
public import Mathlib.NumberTheory.Normal.Transducer

/-!
# Exact characterization of normality-preserving finite-state Mealy transducers

We establish the complete necessary-and-sufficient characterization of base-`b` normality
preservation for deterministic letter-to-letter finite-state Mealy transducers
`T : Real.MealyTransducer b Q` (Huffman / Schnorr–Stimm / Becher–Carton–Heiber):

* A Mealy transducer `T` is **information-lossless at state `p`** (`T.IsInformationLosslessAt p`)
  if no two distinct equal-length input words `u ≠ v : Fin k → Fin b` starting from `p` produce
  both the same output word `T.outputWord p u = T.outputWord p v` and the same ending state
  `T.toDFA.evalFrom p (List.ofFn u) = T.toDFA.evalFrom p (List.ofFn v)`.
* **Sufficiency (Piatetski-Shapiro + snake automaton):**
  For any strongly connected Mealy transducer `T`, the limiting frequency of any length-`k` output
  word `w` on a base-`b` normal input `x` is
  `∑ p, (μ p / b ^ k) * #{u | T.outputWord p u = w}`. When `T` is information-lossless, each fiber
  `{u | T.outputWord p u = w}` injects into `Q` via its ending state, so the limiting frequency is
  at most `|Q| * b⁻ᵏ`. By Piatetski-Shapiro's normality criterion
  (`Real.isNormalIn_of_eventually_le`), `mealyReal b T x` and `mealySeq b hb0 T x` are normal in
  base `b`. Passing to the recurrent strongly connected component entered by `x` extends this to
  arbitrary (not necessarily strongly connected) finite-state Mealy transducers that are
  information-lossless on every reachable recurrent state.
* **Necessity (forbidden-word counting obstruction):**
  If a strongly connected finite-state Mealy transducer `T` is *not* information-lossless, then by
  combining a collision of length `r` with shortest paths of length `< |Q|`, every state has a
  same-output same-end-state collision at length `L = |Q| + r`. Iterating `m` times shows that the
  number of distinct length-`m * L` output words producible from all states of `Q` is at most
  `|Q| * (b ^ L - 1) ^ m < b ^ (m * L)` for large `m`, yielding a finite **forbidden output word**
  `w` that can *never* appear in `mealySeq b hb0 T x` for *any* `x : ℝ`.
* **Zero-one dichotomy & exact characterization:**
  - For strongly connected `T`, `T.IsInformationLossless` holds iff `T` preserves base-`b`
    normality for *all* normal `x`, iff `T` preserves base-`b` normality for *some* normal `x`.
  - For *arbitrary* finite-state `T`, `T` preserves base-`b` normality for all `x` iff every
    reachable recurrent state of `T` is information-lossless.
* **Strict separation from output-bijectivity:**
  The 1-step delay transducer `Real.delayMealy` (`step _ a = a`, `out q _ = q`) is *not*
  output-bijective (`¬ T.IsOutputBijective`), yet *is* information-lossless and preserves base-`b`
  normality.

## Main statements

* `Real.isNormalIn_ofDigits_iff`: `IsNormalIn b (ofDigits d) ↔ IsNormalSeq b fun n ↦ (d n : ℕ)`.
* `Real.isNormalIn_mealyReal_iff`: `IsNormalIn b (mealyReal b T x) ↔ IsNormalSeq b (mealySeq ...)`.
* `Real.isNormalSeq_mealySeq_of_isInformationLossless`,
  `Real.isNormalIn_mealyReal_of_isInformationLossless`: every information-lossless Mealy
  transducer preserves base-`b` normality.
* `Real.exists_forbiddenWord_of_not_isInformationLossless`: every strongly connected lossy Mealy
  transducer omits some finite output word from every state.
* `Real.not_isNormalSeq_mealySeq_of_not_isInformationLossless`,
  `Real.not_isNormalIn_mealyReal_of_not_isInformationLossless`: every strongly connected lossy
  Mealy transducer destroys normality for *every* `x : ℝ`.
* `Real.mealySeq_preserves_isNormal_iff_isInformationLossless`,
  `Real.mealyReal_preserves_isNormal_iff_isInformationLossless`: zero-one dichotomy for strongly
  connected finite-state Mealy transducers.
* `Real.mealySeq_preserves_isNormal_iff_recurrent_isInformationLossless`,
  `Real.mealyReal_preserves_isNormal_iff_recurrent_isInformationLossless`: exact characterization
  for arbitrary finite-state Mealy transducers.
* `Real.delayMealy_isInformationLossless`, `Real.delayMealy_not_isOutputBijective`,
  `Real.isNormalSeq_delayMealy`, `Real.isNormalIn_delayMealy`: 1-step delay example.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-! ### Public definitions for information-lossless transducers -/

/-- The length-`k` output word produced by `T` starting in state `p` while reading `u`. -/
def MealyTransducer.outputWord {Q : Type*} (T : MealyTransducer b Q) (p : Q) {k : ℕ}
    (u : Fin k → Fin b) : Fin k → Fin b :=
  fun j ↦
    T.out (T.toDFA.evalFrom p
      (List.ofFn fun i : Fin j.val ↦ u ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)) (u j)

/-- A Mealy transducer `T` is *information-lossless at state `p`* if no two distinct equal-length
input words from `p` produce both the same output word and the same ending state. -/
def MealyTransducer.IsInformationLosslessAt {Q : Type*} (T : MealyTransducer b Q) (p : Q) : Prop :=
  ∀ (k : ℕ) (u v : Fin k → Fin b),
    T.outputWord p u = T.outputWord p v →
    T.toDFA.evalFrom p (List.ofFn u) = T.toDFA.evalFrom p (List.ofFn v) → u = v

/-- A Mealy transducer `T` is *information-lossless* if it is information-lossless at every
state. -/
def MealyTransducer.IsInformationLossless {Q : Type*} (T : MealyTransducer b Q) : Prop :=
  ∀ p : Q, T.IsInformationLosslessAt p

/-- A state `p` of `T` is *reachable* if some finite input word drives `T.start` to `p`. -/
def MealyTransducer.IsReachable {Q : Type*} (T : MealyTransducer b Q) (p : Q) : Prop :=
  ∃ u : List (Fin b), T.toDFA.eval u = p

/-- A state `p` of `T` is *recurrent* if every state reachable from `p` can return to `p`. -/
def MealyTransducer.IsRecurrent {Q : Type*} (T : MealyTransducer b Q) (p : Q) : Prop :=
  ∀ q : Q, (∃ u : List (Fin b), T.toDFA.evalFrom p u = q) →
    ∃ v : List (Fin b), T.toDFA.evalFrom q v = p

/-- The 1-step delay Mealy transducer over `Fin b`: stores the previous input digit as its state
and outputs the stored digit (`step _ a = a`, `out q _ = q`). -/
def delayMealy (b : ℕ) (init : Fin b) : MealyTransducer b (Fin b) where
  step := fun _ a ↦ a
  start := init
  out := fun q _ ↦ q

/-! ### Exact equivalence between `ofDigits` normality and digit-sequence normality -/

/-- A real number `ofDigits d` is normal in base `b ≥ 2` if and only if its digit sequence `d` is
normal in base `b`. -/
theorem isNormalIn_ofDigits_iff (hb : 2 ≤ b) (d : ℕ → Fin b) :
    IsNormalIn b (ofDigits d) ↔ IsNormalSeq b fun n ↦ (d n : ℕ) := by
  refine ⟨fun hx ↦ ?_, isNormalIn_ofDigits hb⟩
  have hd : ∀ n : ℕ, ∃ m : ℕ, n < m ∧ (d m : ℕ) + 1 < b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨N, hN⟩ := hcon
    have htail : (fun i ↦ d (i + (N + 1))) = fun _ ↦ (⟨b - 1, by omega⟩ : Fin b) := by
      funext i
      apply Fin.ext
      have h1 := hN (i + (N + 1)) (by omega)
      have h2 := (d (i + (N + 1))).isLt
      dsimp only
      omega
    have hval : ofDigits d =
        (((∑ i ∈ Finset.range (N + 1), (d i : ℚ) * ((b : ℚ) ^ (i + 1))⁻¹) +
          ((b : ℚ) ^ (N + 1))⁻¹ : ℚ) : ℝ) := by
      rw [ofDigits_eq_sum_add_ofDigits d (N + 1), htail,
        ofDigits_const_last_eq_one' (by omega : 1 < b), mul_one]
      push_cast
      rfl
    exact (hx.irrational hb).ne_rat _ hval
  have hdig : ∀ n : ℕ, digit b (ofDigits d) n = (d n : ℕ) :=
    digit_ofDigits (by omega : 1 < b) d hd
  intro k w
  have heq : ∀ N : ℕ, blockCount b (ofDigits d) w N =
      ((Finset.range N).filter fun i ↦ ∀ j : Fin k, (d (i + j.val) : ℕ) = (w j : ℕ)).card :=
    fun N ↦ by
      simp only [blockCount, hdig]
  simpa only [heq] using hx k w

/-- Real-number normality of `mealyReal b T x` is equivalent to digit-sequence normality of
`mealySeq b hb0 T x`. -/
theorem isNormalIn_mealyReal_iff {Q : Type*} (hb : 2 ≤ b) (T : MealyTransducer b Q) (x : ℝ) :
    IsNormalIn b (mealyReal b T x) ↔ IsNormalSeq b (mealySeq b (by omega) T x) := by
  have hb0 : 0 < b := by omega
  simp only [mealyReal, hb0, ↓reduceDIte]
  exact isNormalIn_ofDigits_iff hb _

/-! ### Helper lemmas for word concatenation, shifts, and snake-automaton frequencies -/

section Helpers

private def castWord {m n : ℕ} (h : m = n) (u : Fin m → Fin b) : Fin n → Fin b :=
  fun i ↦ u (Fin.cast h.symm i)

private lemma list_ofFn_castWord {m n : ℕ} (h : m = n) (u : Fin m → Fin b) :
    List.ofFn (castWord h u) = List.ofFn u := by
  subst h; rfl

private lemma outputWord_castWord {Q : Type*} (T : MealyTransducer b Q) (p : Q) {m n : ℕ}
    (h : m = n) (u : Fin m → Fin b) :
    T.outputWord p (castWord h u) = castWord h (T.outputWord p u) := by
  subst h; rfl

private lemma list_ofFn_append {k₁ k₂ : ℕ} (u : Fin k₁ → Fin b) (v : Fin k₂ → Fin b) :
    List.ofFn (Fin.append u v) = List.ofFn u ++ List.ofFn v := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split_ifs with h
    · exact Fin.append_left u v ⟨i, h⟩
    · have hi' : i - k₁ < k₂ := by simp only [List.length_ofFn] at hi₁; omega
      have hidx : (⟨i, by simp only [List.length_ofFn] at hi₁; exact hi₁⟩ : Fin (k₁ + k₂)) =
          Fin.natAdd k₁ ⟨i - k₁, hi'⟩ := by
        apply Fin.ext; simp only [Fin.val_natAdd]; omega
      rw [hidx, Fin.append_right]

private lemma outputWord_append {Q : Type*} (T : MealyTransducer b Q) (p : Q) {k₁ k₂ : ℕ}
    (u : Fin k₁ → Fin b) (v : Fin k₂ → Fin b) :
    T.outputWord p (Fin.append u v) =
      Fin.append (T.outputWord p u) (T.outputWord (T.toDFA.evalFrom p (List.ofFn u)) v) := by
  funext j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
  · simp only [Fin.append_left, MealyTransducer.outputWord]
    have hpre : (List.ofFn fun m : Fin (Fin.castAdd k₂ i).val ↦
          Fin.append u v ⟨m.val, Nat.lt_trans m.isLt (Fin.castAdd k₂ i).isLt⟩) =
        List.ofFn fun m : Fin i.val ↦ u ⟨m.val, Nat.lt_trans m.isLt i.isLt⟩ := by
      apply List.ext_getElem
      · simp
      · intro r hr₁ hr₂
        simp only [List.getElem_ofFn]
        have hr_lt : r < k₁ := Nat.lt_trans (by simpa using hr₂) i.isLt
        exact Fin.append_left u v ⟨r, hr_lt⟩
    rw [hpre]
  · simp only [Fin.append_right, MealyTransducer.outputWord]
    have hpre : (List.ofFn fun m : Fin (Fin.natAdd k₁ i).val ↦
          Fin.append u v ⟨m.val, Nat.lt_trans m.isLt (Fin.natAdd k₁ i).isLt⟩) =
        List.ofFn u ++ List.ofFn fun m : Fin i.val ↦ v ⟨m.val, Nat.lt_trans m.isLt i.isLt⟩ := by
      apply List.ext_getElem
      · simp
      · intro r hr₁ hr₂
        simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
        split_ifs with h
        · exact Fin.append_left u v ⟨r, h⟩
        · have hr_sub : r - k₁ < i.val := by simp at hr₁; omega
          have hidx : (⟨r, Nat.lt_trans (by simpa using hr₁) (Fin.natAdd k₁ i).isLt⟩ :
              Fin (k₁ + k₂)) = Fin.natAdd k₁ ⟨r - k₁, Nat.lt_trans hr_sub i.isLt⟩ := by
            apply Fin.ext; simp only [Fin.val_natAdd]; omega
          rw [hidx, Fin.append_right]
    rw [hpre, DFA.evalFrom_of_append]

private lemma tendsto_finset_sum_real {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ) (L : ι → ℝ)
    (hg : ∀ i ∈ s, Tendsto (g i) atTop (𝓝 (L i))) :
    Tendsto (fun n ↦ ∑ i ∈ s, g i n) atTop (𝓝 (∑ i ∈ s, L i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))

private lemma isNormalSeq_shift_lossless {d : ℕ → ℕ} (s : ℕ)
    (hd : IsNormalSeq b fun n ↦ d (n + s)) : IsNormalSeq b d := by
  intro k w
  have hlim := hd k w
  have hdiff : ∀ N : ℕ,
      (((Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j.val) = (w j : ℕ)).card : ℝ) / N -
      (((Finset.range N).filter fun i ↦
          ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)).card : ℝ) / N =
      ((((Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j.val) = (w j : ℕ)).card : ℝ) -
      (((Finset.range N).filter fun i ↦
          ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)).card : ℝ)) / N := fun N ↦ (sub_div _ _ _).symm
  have habs_le : ∀ N : ℕ,
      |(((Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j.val) = (w j : ℕ)).card : ℝ) -
      (((Finset.range N).filter fun i ↦
          ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)).card : ℝ)| ≤ s := by
    intro N
    set A := (Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j.val) = (w j : ℕ)
    set B := (Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)
    have hA_le : A.card ≤ B.card + s := by
      have hsub : A ⊆ B.image (· + s) ∪ Finset.range s := by
        intro i hi
        simp only [A, B, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
          Finset.mem_image] at hi ⊢
        by_cases his : i < s
        · exact Or.inr his
        · left
          refine ⟨i - s, ⟨by omega, fun j ↦ ?_⟩, by omega⟩
          rw [Nat.sub_add_cancel (by omega)]
          exact hi.2 j
      calc A.card ≤ (B.image (· + s) ∪ Finset.range s).card := Finset.card_le_card hsub
        _ ≤ (B.image (· + s)).card + (Finset.range s).card := Finset.card_union_le _ _
        _ ≤ B.card + s := by
          rw [Finset.card_range]
          exact Nat.add_le_add_right Finset.card_image_le s
    have hB_le : B.card ≤ A.card + s := by
      have hsub : B ⊆ (A.filter (s ≤ ·)).image (· - s) ∪ Finset.Ico (N - s) N := by
        intro i hi
        simp only [A, B, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
          Finset.mem_image, Finset.mem_Ico] at hi ⊢
        by_cases his : i + s < N
        · left
          refine ⟨i + s, ⟨⟨his, hi.2⟩, by omega⟩, by omega⟩
        · right; omega
      calc B.card
          ≤ ((A.filter (s ≤ ·)).image (· - s) ∪ Finset.Ico (N - s) N).card :=
            Finset.card_le_card hsub
        _ ≤ ((A.filter (s ≤ ·)).image (· - s)).card + (Finset.Ico (N - s) N).card :=
            Finset.card_union_le _ _
        _ ≤ (A.filter (s ≤ ·)).card + s := by
            rw [Nat.card_Ico]
            exact Nat.add_le_add Finset.card_image_le (by omega)
        _ ≤ A.card + s := Nat.add_le_add_right (Finset.card_filter_le _ _) s
    rw [abs_le]
    have hA_r : (A.card : ℝ) ≤ (B.card : ℝ) + s := by exact_mod_cast hA_le
    have hB_r : (B.card : ℝ) ≤ (A.card : ℝ) + s := by exact_mod_cast hB_le
    constructor <;> linarith
  have hzero : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j.val) = (w j : ℕ)).card : ℝ) / N -
      (((Finset.range N).filter fun i ↦
          ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)).card : ℝ) / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N : ℕ ↦ (s : ℝ) / N) (fun N ↦ ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (s : ℝ))
    rw [hdiff N, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (habs_le N) (Nat.cast_nonneg N)
  have hadd := hzero.add hlim
  rw [zero_add] at hadd
  refine hadd.congr fun N ↦ ?_
  simp only [show ∀ i j : ℕ, i + j + s = i + s + j from fun i j ↦ by omega]
  ring

private lemma isRecurrent_evalFrom {Q : Type*} (T : MealyTransducer b Q) {p : Q}
    (hp : T.IsRecurrent p) (u : List (Fin b)) : T.IsRecurrent (T.toDFA.evalFrom p u) := by
  intro q ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hp q ⟨u ++ v, by rw [DFA.evalFrom_of_append, hv]⟩
  exact ⟨w ++ u, by rw [DFA.evalFrom_of_append, hw]⟩

private lemma exists_word_isRecurrent {Q : Type*} [Finite Q] (T : MealyTransducer b Q) (p : Q) :
    ∃ u : List (Fin b), T.IsRecurrent (T.toDFA.evalFrom p u) := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let reach : Q → Finset Q := fun q ↦
    Finset.univ.filter fun r ↦ ∃ v : List (Fin b), T.toDFA.evalFrom q v = r
  have hne : (reach p).Nonempty := ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, ⟨[], rfl⟩⟩⟩
  obtain ⟨q, hq_mem, hq_min⟩ := Finset.exists_min_image (reach p) (fun r ↦ (reach r).card) hne
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hq_mem
  obtain ⟨u, rfl⟩ := hq_mem
  refine ⟨u, fun r ⟨v, hv⟩ ↦ ?_⟩
  have hsub : reach r ⊆ reach (T.toDFA.evalFrom p u) := by
    intro s hs
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    obtain ⟨w, hw⟩ := hs
    exact ⟨v ++ w, by rw [DFA.evalFrom_of_append, hv, hw]⟩
  have hr_mem : r ∈ reach p :=
    Finset.mem_filter.2 ⟨Finset.mem_univ r, ⟨u ++ v, by rw [DFA.evalFrom_of_append, hv]⟩⟩
  have heq : reach r = reach (T.toDFA.evalFrom p u) :=
    Finset.eq_of_subset_of_card_le hsub (hq_min r hr_mem)
  have hback : T.toDFA.evalFrom p u ∈ reach r := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨[], rfl⟩⟩
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hback
  exact hback

private lemma exists_universal_recurrent_word {Q : Type*} [Finite Q] (T : MealyTransducer b Q) :
    ∃ W : List (Fin b), ∀ p : Q, T.IsRecurrent (T.toDFA.evalFrom p W) := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  suffices h : ∀ S : Finset Q, ∃ W : List (Fin b), ∀ p ∈ S, T.IsRecurrent (T.toDFA.evalFrom p W) by
    obtain ⟨W, hW⟩ := h Finset.univ
    exact ⟨W, fun p ↦ hW p (Finset.mem_univ p)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨[], fun _ h ↦ absurd h (Finset.notMem_empty _)⟩
  | insert p S _ ih =>
    obtain ⟨W₁, hW₁⟩ := ih
    obtain ⟨W₂, hW₂⟩ := exists_word_isRecurrent T (T.toDFA.evalFrom p W₁)
    refine ⟨W₁ ++ W₂, fun q hq ↦ ?_⟩
    rw [DFA.evalFrom_of_append]
    rcases Finset.mem_insert.1 hq with rfl | hqS
    · exact hW₂
    · exact isRecurrent_evalFrom T (hW₁ q hqS) W₂

/-- Snake automaton with lookahead buffer of length `n ≥ 1` on `Q × (Fin n → Fin b)`. -/
private def lSnakeDFA {Q : Type*} (M : DFA (Fin b) Q) (n : ℕ) (hn : 1 ≤ n)
    (initBuf : Fin n → Fin b) : DFA (Fin b) (Q × (Fin n → Fin b)) where
  step pu a :=
    (M.step pu.1 (pu.2 ⟨0, by omega⟩),
      fun j : Fin n ↦ if h : j.val + 1 < n then pu.2 ⟨j.val + 1, h⟩ else a)
  start := (M.start, initBuf)
  accept := Set.univ

private lemma lSnakeDFA_evalFrom_spec {Q : Type*} (M : DFA (Fin b) Q) {n : ℕ} (hn : 1 ≤ n)
    (initBuf : Fin n → Fin b) (p : Q) (u : Fin n → Fin b) (v : List (Fin b)) :
    (lSnakeDFA M n hn initBuf).evalFrom (p, u) v =
      (M.evalFrom p ((List.ofFn u ++ v).take v.length),
        fun j : Fin n ↦ (List.ofFn u ++ v)[v.length + j.val]'(by simp; omega)) := by
  induction v generalizing p u with
  | nil =>
    ext <;> simp
  | cons a v ih =>
    have hstep_eq : (lSnakeDFA M n hn initBuf).evalFrom (p, u) (a :: v) =
        (lSnakeDFA M n hn initBuf).evalFrom
          (M.step p (u ⟨0, by omega⟩),
            fun j : Fin n ↦ if h : j.val + 1 < n then u ⟨j.val + 1, h⟩ else a) v := rfl
    rw [hstep_eq, ih]
    set u' : Fin n → Fin b :=
      fun j : Fin n ↦ if h : j.val + 1 < n then u ⟨j.val + 1, h⟩ else a
    have hlist : List.ofFn u ++ (a :: v) = u ⟨0, by omega⟩ :: (List.ofFn u' ++ v) := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi₁ hi₂
        cases i with
        | zero =>
          simp only [List.getElem_append_left (by simp; omega : 0 < (List.ofFn u).length),
            List.getElem_ofFn, List.getElem_cons_zero]
        | succ i =>
          simp only [List.getElem_cons_succ, List.getElem_append, List.length_ofFn]
          by_cases h1 : i + 1 < n
          · have h2 : i < n := by omega
            simp only [h1, h2, ↓reduceDIte, List.getElem_ofFn, u']
          · by_cases h2 : i < n
            · have heq : i + 1 = n := by omega
              simp only [h1, h2, ↓reduceDIte, List.getElem_ofFn, u']
              simp [heq]
            · simp only [h1, h2, ↓reduceDIte]
              have heq : i + 1 - n = (i - n) + 1 := by omega
              simp [heq]
    refine Prod.ext ?_ (funext fun j ↦ ?_)
    · dsimp only
      rw [hlist, List.length_cons, List.take_succ_cons, DFA.evalFrom_cons]
    · dsimp only
      apply Option.some_injective
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hlist, List.length_cons,
        show v.length + 1 + j.val = (v.length + j.val) + 1 by omega, List.getElem?_cons_succ]

private lemma lSnakeDFA_stronglyConnected {Q : Type*} (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M) {n : ℕ} (hn : 1 ≤ n) (initBuf : Fin n → Fin b) :
    IsStronglyConnected (lSnakeDFA M n hn initBuf) := by
  rintro ⟨p₁, u₁⟩ ⟨p₂, u₂⟩
  obtain ⟨v, hv⟩ := hconn (M.evalFrom p₁ (List.ofFn u₁)) p₂
  refine ⟨v ++ List.ofFn u₂, ?_⟩
  rw [lSnakeDFA_evalFrom_spec]
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · dsimp only
    have hlen : (v ++ List.ofFn u₂).length = (List.ofFn u₁ ++ v).length := by simp; omega
    have htake : (List.ofFn u₁ ++ (v ++ List.ofFn u₂)).take (v ++ List.ofFn u₂).length =
        List.ofFn u₁ ++ v := by
      rw [← List.append_assoc, hlen, List.take_left]
    rw [htake, DFA.evalFrom_of_append, hv]
  · dsimp only
    have hge : (List.ofFn u₁ ++ v).length ≤ (v ++ List.ofFn u₂).length + j.val := by simp; omega
    have hidx : (v ++ List.ofFn u₂).length + j.val - (List.ofFn u₁ ++ v).length = j.val := by
      simp; omega
    apply Option.some_injective
    rw [← List.getElem?_eq_getElem, ← List.append_assoc, List.getElem?_append_right hge, hidx,
      List.getElem?_ofFn]
    simp [j.isLt]

private lemma lSnakeDFA_stationary {Q : Type*} [Fintype Q] (hb : 0 < b) (M : DFA (Fin b) Q)
    {n : ℕ} (hn : 1 ≤ n) (initBuf : Fin n → Fin b) {μ : Q → ℝ} (hμ : IsStationary M μ) :
    IsStationary (lSnakeDFA M n hn initBuf)
      (fun pu : Q × (Fin n → Fin b) ↦ μ pu.1 / (b : ℝ) ^ n) := by
  classical
  constructor
  · refine ⟨fun pu ↦ div_nonneg (hμ.1.1 pu.1) (by positivity), ?_⟩
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, mul_div_cancel₀ _ (by positivity : (b : ℝ) ^ n ≠ 0), hμ.1.2]
  · rintro ⟨q, w⟩
    have hstep_snake : ∀ pu : Q × (Fin n → Fin b),
        stepProb (lSnakeDFA M n hn initBuf) 1 pu (q, w) =
          ((Finset.univ.filter fun a : Fin b ↦
            (lSnakeDFA M n hn initBuf).step pu a = (q, w)).card : ℝ) / b := fun pu ↦ by
      rw [stepProb_succ]
      congr 1
      simp_rw [stepProb_zero]
      convert Finset.sum_boole (fun a : Fin b ↦ (lSnakeDFA M n hn initBuf).step pu a = (q, w))
        Finset.univ
    simp_rw [hstep_snake, ← mul_div_assoc]
    have hstat_eq : ∀ p, stepProb M 1 p q =
        ((Finset.univ.filter fun c : Fin b ↦ M.step p c = q).card : ℝ) / b := fun p ↦ by
      rw [stepProb_succ]
      congr 1
      simp_rw [stepProb_zero]
      convert Finset.sum_boole (fun c : Fin b ↦ M.step p c = q) Finset.univ
    have hcard : ∀ (p : Q) (u : Fin n → Fin b),
        ((Finset.univ.filter fun a : Fin b ↦
          (lSnakeDFA M n hn initBuf).step (p, u) a = (q, w)).card : ℝ) =
        if M.step p (u ⟨0, by omega⟩) = q ∧
            (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j) then 1 else 0 := by
      intro p u
      by_cases hcond : M.step p (u ⟨0, by omega⟩) = q ∧
          (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j)
      · rw [ite_eq_left_iff.2 fun h ↦ absurd hcond h]
        have hsing : (Finset.univ.filter fun a : Fin b ↦
            (lSnakeDFA M n hn initBuf).step (p, u) a = (q, w)) = {w ⟨n - 1, by omega⟩} := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, lSnakeDFA,
            Prod.mk.injEq, funext_iff]
          constructor
          · rintro ⟨_, hfun⟩
            have hlast := hfun ⟨n - 1, by omega⟩
            have hnot : ¬ (n - 1) + 1 < n := by omega
            simpa [hnot] using hlast
          · rintro rfl
            refine ⟨hcond.1, fun j ↦ ?_⟩
            split_ifs with hj
            · exact hcond.2 j hj
            · have := j.isLt
              congr 1; exact Fin.ext (by dsimp only; omega)
        rw [hsing, Finset.card_singleton, Nat.cast_one]
      · rw [ite_eq_right_iff.2 fun h ↦ absurd h hcond]
        have hemp : (Finset.univ.filter fun a : Fin b ↦
            (lSnakeDFA M n hn initBuf).step (p, u) a = (q, w)) = ∅ := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            lSnakeDFA, Prod.mk.injEq, funext_iff]
          rintro ⟨h1, h2⟩
          apply hcond
          refine ⟨h1, fun j hj ↦ ?_⟩
          have := h2 j
          simpa [hj] using this
        rw [hemp, Finset.card_empty, Nat.cast_zero]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ p : Q,
        (∑ u : Fin n → Fin b,
          (μ p / (b : ℝ) ^ n) *
            ((Finset.univ.filter fun a : Fin b ↦
              (lSnakeDFA M n hn initBuf).step (p, u) a = (q, w)).card : ℝ) / b) =
        (μ p * stepProb M 1 p q) / (b : ℝ) ^ n := by
      intro p
      simp_rw [hcard p]
      have hcnt_u : (∑ u : Fin n → Fin b,
          if M.step p (u ⟨0, by omega⟩) = q ∧
            (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j) then (1 : ℝ) else 0) =
          ((Finset.univ.filter fun c : Fin b ↦ M.step p c = q).card : ℝ) := by
        rw [Finset.sum_boole]
        congr 1
        refine Finset.card_nbij' (fun u ↦ u ⟨0, by omega⟩)
          (fun c j ↦ if h : j.val = 0 then c else w ⟨j.val - 1, by omega⟩) ?_ ?_ ?_ ?_
        · intro u hu
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
          exact hu.1
        · intro c hc
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
          refine ⟨by simpa using hc, fun j hj ↦ ?_⟩
          simp
        · intro u hu
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
          funext j
          dsimp only
          split_ifs with h0
          · congr 1; exact Fin.ext h0.symm
          · have := hu.2 ⟨j.val - 1, by omega⟩ (by dsimp only; omega)
            rw [← this]
            congr 1; exact Fin.ext (by dsimp only; omega)
        · intro c _; simp
      calc ∑ u : Fin n → Fin b, (μ p / (b : ℝ) ^ n) *
              (if M.step p (u ⟨0, by omega⟩) = q ∧
                (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j)
                then (1 : ℝ) else 0) / b
          = (μ p / (b : ℝ) ^ n) * (∑ u : Fin n → Fin b,
              if M.step p (u ⟨0, by omega⟩) = q ∧
                (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j)
                then (1 : ℝ) else 0) / b := by
            rw [← Finset.sum_div, ← Finset.mul_sum]
        _ = (μ p / (b : ℝ) ^ n) *
              ((Finset.univ.filter fun c : Fin b ↦ M.step p c = q).card : ℝ) / b := by
            rw [hcnt_u]
        _ = (μ p * stepProb M 1 p q) / (b : ℝ) ^ n := by
            rw [hstat_eq p]; ring
    simp_rw [hinner, ← Finset.sum_div, hμ.2 q]

/-- For a strongly connected finite-state Mealy transducer `T` with stationary distribution `μ` and
any base-`b` normal input `x`, every length-`k` output block `w` has an exact limiting frequency
`∑_{(p, u) : outputWord p u = w} μ p / b ^ k`. -/
private lemma tendsto_mealySeq_blockFreq_of_stronglyConnected {Q : Type*} [Fintype Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    {μ : Q → ℝ} (hμ : IsStationary T.toDFA μ) (hx : IsNormalIn b x)
    (k : ℕ) (w : Fin k → Fin b) :
    letI : DecidableEq Q := Classical.decEq Q
    Tendsto (fun N : ℕ ↦
        (((Finset.range N).filter fun t ↦
          ∀ j : Fin k, mealySeq b (by omega) T x (t + j.val) = (w j : ℕ)).card : ℝ) / N)
      atTop
      (𝓝 (∑ pu ∈ Finset.univ.filter (fun pu : Q × (Fin k → Fin b) ↦ T.outputWord pu.1 pu.2 = w),
        μ pu.1 / (b : ℝ) ^ k)) := by
  classical
  have hb0 : 0 < b := by omega
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · have hlim : (∑ pu ∈ Finset.univ.filter
        (fun pu : Q × (Fin 0 → Fin b) ↦ T.outputWord pu.1 pu.2 = w), μ pu.1 / (b : ℝ) ^ 0) = 1 := by
      have hfilt : (Finset.univ.filter fun pu : Q × (Fin 0 → Fin b) ↦
          T.outputWord pu.1 pu.2 = w) = Finset.univ := by
        ext ⟨p, u⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        funext j; exact Fin.elim0 j
      rw [hfilt, Fintype.sum_prod_type]
      simp [pow_zero, div_one, hμ.1.2]
    rw [hlim]
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hfilt : ((Finset.range N).filter fun i ↦
        ∀ j : Fin 0, mealySeq b hb0 T x (i + j.val) = (w j : ℕ)) = Finset.range N := by
      ext i; simp
    rw [hfilt, Finset.card_range, div_self (by positivity : (N : ℝ) ≠ 0)]
  · have hk1 : 1 ≤ k := hk_pos
    let initBuf : Fin k → Fin b := fun j ↦ ⟨digit b x j.val, digit_lt hb0 x j.val⟩
    let Ms := lSnakeDFA T.toDFA k hk1 initBuf
    have hMs_conn : IsStronglyConnected Ms := lSnakeDFA_stronglyConnected T.toDFA hconn hk1 initBuf
    have hMs_stat := lSnakeDFA_stationary hb0 T.toDFA hk1 initBuf hμ
    have hxk : IsNormalIn b (x * (b : ℝ) ^ k) := (isNormalIn_mul_pow_iff k).2 hx
    have hMs_state : ∀ t : ℕ,
        Ms.eval (digitPrefix b hb0 (x * (b : ℝ) ^ k) t) =
          (T.toDFA.eval (digitPrefix b hb0 x t),
            fun j : Fin k ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩) := by
      intro t
      have hspec := lSnakeDFA_evalFrom_spec T.toDFA hk1 initBuf T.start initBuf
        (digitPrefix b hb0 (x * (b : ℝ) ^ k) t)
      change (lSnakeDFA T.toDFA k hk1 initBuf).evalFrom (T.start, initBuf)
        (digitPrefix b hb0 (x * (b : ℝ) ^ k) t) = _
      rw [hspec]
      have hlist : List.ofFn initBuf ++ digitPrefix b hb0 (x * (b : ℝ) ^ k) t =
          digitPrefix b hb0 x (k + t) := by
        apply List.ext_getElem
        · simp [digitPrefix, initBuf]
        · intro i hi₁ hi₂
          simp only [digitPrefix, initBuf, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
          split_ifs with h
          · rfl
          · apply Fin.ext
            dsimp only
            rw [← digit_add]
            congr 1; omega
      have hlen : (digitPrefix b hb0 (x * (b : ℝ) ^ k) t).length = t := by simp [digitPrefix]
      refine Prod.ext ?_ (funext fun j ↦ ?_)
      · dsimp only
        rw [hlist, hlen]
        congr 1
        apply List.ext_getElem
        · simp [digitPrefix]
        · intro i _ _
          simp [digitPrefix]
      · dsimp only
        apply Option.some_injective
        rw [← List.getElem?_eq_getElem, hlist, hlen,
          List.getElem?_eq_getElem (by simp [digitPrefix]; omega)]
        simp [digitPrefix]
    let goodPairs : Finset (Q × (Fin k → Fin b)) :=
      Finset.univ.filter fun pu ↦ T.outputWord pu.1 pu.2 = w
    have hcount_eq : ∀ N : ℕ,
        ((Finset.range N).filter fun t ↦
          ∀ j : Fin k, mealySeq b hb0 T x (t + j.val) = (w j : ℕ)).card =
        ∑ pu ∈ goodPairs, dfaStateCount b hb0 Ms (x * (b : ℝ) ^ k) pu N := by
      intro N
      simp_rw [dfaStateCount]
      rw [← Finset.card_biUnion]
      · refine congrArg Finset.card ?_
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, goodPairs,
          Finset.mem_univ, true_and, hMs_state t]
        constructor
        · rintro ⟨htN, hmatch⟩
          refine ⟨(T.toDFA.eval (digitPrefix b hb0 x t),
            fun j : Fin k ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩), ?_, htN, rfl⟩
          funext j
          apply Fin.ext
          have hj := hmatch j
          simp only [MealyTransducer.outputWord, mealySeq] at hj ⊢
          rw [digitPrefix_add hb0 x t j.val, DFA.eval, DFA.evalFrom_of_append] at hj
          exact hj
        · rintro ⟨pu, hpu, htN, heq⟩
          refine ⟨htN, fun j ↦ ?_⟩
          have hj := congrArg Fin.val (congrFun hpu j)
          rw [← heq] at hj
          simp only [MealyTransducer.outputWord, mealySeq] at hj ⊢
          rw [digitPrefix_add hb0 x t j.val, DFA.eval, DFA.evalFrom_of_append]
          exact hj
      · intro p₁ _ p₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    have hsum := tendsto_finset_sum_real goodPairs
      (fun pu N ↦ (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ k) pu N : ℝ) / N)
      (fun pu ↦ μ pu.1 / (b : ℝ) ^ k)
      fun pu _ ↦ tendsto_dfa_stateFreq hb Ms hMs_conn hMs_stat hxk pu
    refine hsum.congr fun N ↦ ?_
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hcount_eq N]

/-! ### Part 1: Sufficiency — information-lossless transducers preserve normality -/

private lemma isNormalSeq_mealySeq_of_stronglyConnected_lossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    (hloss : T.IsInformationLossless) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Nonempty Q := ⟨T.start⟩
  have hb0 : 0 < b := by omega
  obtain ⟨μ, hμ, _, _⟩ := exists_unique_stationary_and_tendsto_cesaro hb0 T.toDFA hconn
  -- Every length-`k` output block `w` has limiting frequency `≤ |Q| * b⁻ᵏ`
  have hfreq_bound : ∀ (k : ℕ) (w : Fin k → Fin b),
      ∃ L : ℝ, L ≤ (Fintype.card Q : ℝ) * ((b : ℝ) ^ k)⁻¹ ∧
        Tendsto (fun N : ℕ ↦
            (((Finset.range N).filter fun t ↦
              ∀ j : Fin k, mealySeq b hb0 T x (t + j.val) = (w j : ℕ)).card : ℝ) / N)
          atTop (𝓝 L) := by
    intro k w
    refine ⟨_, ?_, tendsto_mealySeq_blockFreq_of_stronglyConnected hb T hconn hμ hx k w⟩
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    have hinner : ∀ p : Q,
        (∑ u : Fin k → Fin b, if T.outputWord p u = w then μ p / (b : ℝ) ^ k else 0) ≤
        (Fintype.card Q : ℝ) * (μ p / (b : ℝ) ^ k) := fun p ↦ by
      have hsum_eq : (∑ u : Fin k → Fin b,
            if T.outputWord p u = w then μ p / (b : ℝ) ^ k else 0) =
          ((Finset.univ.filter fun u : Fin k → Fin b ↦ T.outputWord p u = w).card : ℝ) *
            (μ p / (b : ℝ) ^ k) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [hsum_eq]
      have hcard_le : (Finset.univ.filter fun u : Fin k → Fin b ↦ T.outputWord p u = w).card ≤
          Fintype.card Q := by
        have hinj : Set.InjOn (fun u : Fin k → Fin b ↦ T.toDFA.evalFrom p (List.ofFn u))
            (Finset.univ.filter fun u : Fin k → Fin b ↦ T.outputWord p u = w) := by
          intro u₁ hu₁ u₂ hu₂ heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu₁ hu₂
          exact hloss p k u₁ u₂ (hu₁.trans hu₂.symm) heq
        simpa [Finset.card_univ] using
          Finset.card_le_card_of_injOn (fun u ↦ T.toDFA.evalFrom p (List.ofFn u))
            (fun _ _ ↦ Finset.mem_univ _) hinj
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hcard_le)
        (div_nonneg (hμ.1.1 p) (by positivity))
    calc (∑ p : Q, ∑ u : Fin k → Fin b, if T.outputWord p u = w then μ p / (b : ℝ) ^ k else 0)
        ≤ ∑ p : Q, (Fintype.card Q : ℝ) * (μ p / (b : ℝ) ^ k) :=
          Finset.sum_le_sum fun p _ ↦ hinner p
      _ = (Fintype.card Q : ℝ) * ((b : ℝ) ^ k)⁻¹ := by
          rw [← Finset.mul_sum, ← Finset.sum_div, hμ.1.2, one_div]
  -- `mealySeq` does not end in all `(b - 1)`s
  have hnot_all : ∀ n : ℕ, ∃ m : ℕ, n < m ∧ mealySeq b hb0 T x m + 1 < b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨N₀, hN₀⟩ := hcon
    obtain ⟨k, hk⟩ := exists_nat_gt ((Fintype.card Q : ℝ))
    have hpow : (Fintype.card Q : ℝ) < (b : ℝ) ^ k := by
      have hk1 : (k : ℝ) < (b : ℝ) ^ k := by
        have hlt : k < b ^ k := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hb k)
        exact_mod_cast hlt
      exact hk.trans hk1
    let w : Fin k → Fin b := fun _ ↦ ⟨b - 1, by omega⟩
    obtain ⟨L, hL_le, hL_lim⟩ := hfreq_bound k w
    have hL_lt : L < 1 := by
      have hpos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      calc L ≤ (Fintype.card Q : ℝ) * ((b : ℝ) ^ k)⁻¹ := hL_le
        _ < (b : ℝ) ^ k * ((b : ℝ) ^ k)⁻¹ := by
            exact mul_lt_mul_of_pos_right hpow (inv_pos.2 hpos)
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    have hlim_one : Tendsto (fun N : ℕ ↦
        (((Finset.range N).filter fun t ↦
          ∀ j : Fin k, mealySeq b hb0 T x (t + j.val) = (w j : ℕ)).card : ℝ) / N)
        atTop (𝓝 1) := by
      have hlow : Tendsto (fun N : ℕ ↦ (1 : ℝ) - ((N₀ + 1 : ℕ) : ℝ) / N) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub
          (tendsto_const_div_atTop_nhds_zero_nat ((N₀ + 1 : ℕ) : ℝ))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
        have hsub : Finset.Ico (N₀ + 1) N ⊆ (Finset.range N).filter fun t ↦
            ∀ j : Fin k, mealySeq b hb0 T x (t + j.val) = (w j : ℕ) := by
          intro t ht
          simp only [Finset.mem_Ico] at ht
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨ht.2, fun j ↦ ?_⟩
          have h1 := hN₀ (t + j.val) (by omega)
          have h2 : mealySeq b hb0 T x (t + j.val) < b := (T.out _ _).isLt
          dsimp only [w]
          omega
        have hcard : N - (N₀ + 1) ≤ ((Finset.range N).filter fun t ↦
            ∀ j : Fin k, mealySeq b hb0 T x (t + j.val) = (w j : ℕ)).card := by
          simpa [Nat.card_Ico] using Finset.card_le_card hsub
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        rw [sub_div' hNpos.ne', one_mul]
        refine div_le_div_of_nonneg_right ?_ hNpos.le
        have : ((N - (N₀ + 1) : ℕ) : ℝ) ≤ _ := Nat.cast_le.2 hcard
        rw [Nat.cast_sub hN] at this
        exact this
      · filter_upwards [eventually_ge_atTop 1] with N hN
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        rw [div_le_one hNpos]
        exact_mod_cast (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    linarith [tendsto_nhds_unique hL_lim hlim_one]
  -- Identify `digit b (mealyReal b T x)` with `mealySeq b hb0 T x`
  have hdig : ∀ n : ℕ, digit b (mealyReal b T x) n = mealySeq b hb0 T x n := fun n ↦ by
    simp only [mealyReal, hb0, ↓reduceDIte]
    exact digit_ofDigits (by omega : 1 < b) _ hnot_all n
  -- Apply Piatetski-Shapiro's normality criterion with `C = |Q|`
  have hreal : IsNormalIn b (mealyReal b T x) := by
    refine isNormalIn_of_eventually_le hb (C := (Fintype.card Q : ℝ)) fun k w ε hε ↦ ?_
    obtain ⟨L, hL_le, hL_lim⟩ := hfreq_bound k w
    have hlt : L < (Fintype.card Q : ℝ) * ((b : ℝ) ^ k)⁻¹ + ε := by linarith
    filter_upwards [hL_lim.eventually (gt_mem_nhds hlt)] with N hN
    have hbc : blockCount b (mealyReal b T x) w N =
        ((Finset.range N).filter fun t ↦
          ∀ j : Fin k, mealySeq b hb0 T x (t + j.val) = (w j : ℕ)).card := by
      simp only [blockCount, hdig]
    rw [hbc]
    exact hN.le
  exact (isNormalIn_mealyReal_iff hb T x).1 hreal

/-- **Sufficiency for arbitrary finite-state Mealy transducers**: if every reachable recurrent
state of `T` is information-lossless, then `T` preserves base-`b` normality (digit sequences). -/
theorem isNormalSeq_mealySeq_of_recurrent_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q)
    (hloss : ∀ p : Q, T.IsReachable p → T.IsRecurrent p → T.IsInformationLosslessAt p)
    (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  classical
  have hb0 : 0 < b := by omega
  obtain ⟨W, hW⟩ := exists_universal_recurrent_word T
  -- `W` appears in the base-`b` expansion of `x`, driving `T` into a reachable recurrent state `q₀`
  let wFin : Fin W.length → Fin b := fun j ↦ W[j.val]
  have hw_pos : 0 < ((b : ℝ) ^ W.length)⁻¹ := by positivity
  have hocc : ∃ t : ℕ, ∀ j : Fin W.length, digit b x (t + j.val) = (wFin j : ℕ) := by
    by_contra hno
    push Not at hno
    have hzero : ∀ N : ℕ, blockCount b x wFin N = 0 := fun N ↦ by
      rw [blockCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _
      exact fun h ↦ by
        obtain ⟨j, hj⟩ := hno t
        exact hj (h j)
    have hlim := hx W.length wFin
    have h0 : Tendsto (fun N : ℕ ↦ (blockCount b x wFin N : ℝ) / N) atTop (𝓝 0) := by
      simp_rw [hzero, Nat.cast_zero, zero_div]
      exact tendsto_const_nhds
    linarith [tendsto_nhds_unique hlim h0]
  obtain ⟨t, ht⟩ := hocc
  let t₀ := t + W.length
  let q₀ : Q := T.toDFA.eval (digitPrefix b hb0 x t₀)
  have hq₀_rec : T.IsRecurrent q₀ := by
    have hpre : digitPrefix b hb0 x t₀ = digitPrefix b hb0 x t ++ W := by
      rw [show t₀ = t + W.length from rfl, digitPrefix_add hb0 x t W.length]
      congr 1
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        simp only [List.getElem_ofFn]
        apply Fin.ext
        exact ht ⟨i, hi₂⟩
    dsimp only [q₀]
    rw [hpre, DFA.eval, DFA.evalFrom_of_append]
    exact hW (T.toDFA.evalFrom T.start (digitPrefix b hb0 x t))
  -- Restrict `T` to the reachable recurrent SCC `C` of `q₀`
  let C : Type _ := {r : Q // ∃ v : List (Fin b), T.toDFA.evalFrom q₀ v = r}
  have hstep_closed : ∀ (r : C) (a : Fin b),
      ∃ v : List (Fin b), T.toDFA.evalFrom q₀ v = T.step r.val a := by
    rintro ⟨r, v, hv⟩ a
    exact ⟨v ++ [a], by rw [DFA.evalFrom_of_append, hv]; rfl⟩
  let Tc : MealyTransducer b C :=
    { step := fun r a ↦ ⟨T.step r.val a, hstep_closed r a⟩
      start := ⟨q₀, [], rfl⟩
      out := fun r a ↦ T.out r.val a }
  have hTc_evalFrom : ∀ (r : C) (v : List (Fin b)),
      (Tc.toDFA.evalFrom r v).val = T.toDFA.evalFrom r.val v := by
    intro r v
    induction v generalizing r with
    | nil => rfl
    | cons a v ih => exact ih (Tc.step r a)
  have hTc_outputWord : ∀ (r : C) {k : ℕ} (u : Fin k → Fin b),
      Tc.outputWord r u = T.outputWord r.val u := by
    intro r k u
    funext j
    simp only [MealyTransducer.outputWord, Tc, hTc_evalFrom]
  have hTc_conn : IsStronglyConnected Tc.toDFA := by
    rintro ⟨r₁, v₁, hv₁⟩ ⟨r₂, v₂, hv₂⟩
    obtain ⟨w₁, hw₁⟩ := hq₀_rec r₁ ⟨v₁, hv₁⟩
    refine ⟨w₁ ++ v₂, Subtype.ext ?_⟩
    rw [hTc_evalFrom, DFA.evalFrom_of_append, hw₁, hv₂]
  have hTc_loss : Tc.IsInformationLossless := by
    rintro ⟨r, v, hv⟩ k u₁ u₂ hout hend
    have hr_reach : T.IsReachable r :=
      ⟨digitPrefix b hb0 x t₀ ++ v, by rw [DFA.eval, DFA.evalFrom_of_append]; exact hv⟩
    have hr_rec : T.IsRecurrent r := hv ▸ isRecurrent_evalFrom T hq₀_rec v
    have hout' : T.outputWord r u₁ = T.outputWord r u₂ := by
      simpa only [hTc_outputWord] using hout
    have hend' : T.toDFA.evalFrom r (List.ofFn u₁) = T.toDFA.evalFrom r (List.ofFn u₂) := by
      have := congrArg Subtype.val hend
      simpa only [hTc_evalFrom] using this
    exact hloss r hr_reach hr_rec k u₁ u₂ hout' hend'
  have hx' : IsNormalIn b (x * (b : ℝ) ^ t₀) := (isNormalIn_mul_pow_iff t₀).2 hx
  have hnorm' : IsNormalSeq b (mealySeq b hb0 Tc (x * (b : ℝ) ^ t₀)) :=
    isNormalSeq_mealySeq_of_stronglyConnected_lossless hb Tc hTc_conn hTc_loss hx'
  have hseq_eq : (fun n : ℕ ↦ mealySeq b hb0 T x (n + t₀)) =
      mealySeq b hb0 Tc (x * (b : ℝ) ^ t₀) := by
    funext n
    simp only [mealySeq]
    have hpre_eq : digitPrefix b hb0 x (n + t₀) =
        digitPrefix b hb0 x t₀ ++ digitPrefix b hb0 (x * (b : ℝ) ^ t₀) n := by
      rw [add_comm, digitPrefix_add hb0 x t₀ n]
      congr 1
      apply List.ext_getElem
      · simp [digitPrefix]
      · intro i hi₁ hi₂
        simp only [digitPrefix, List.getElem_ofFn]
        apply Fin.ext
        dsimp only
        rw [digit_add]
    have hstate : T.toDFA.eval (digitPrefix b hb0 x (n + t₀)) =
        (Tc.toDFA.eval (digitPrefix b hb0 (x * (b : ℝ) ^ t₀) n)).val := by
      rw [hpre_eq, DFA.eval, DFA.evalFrom_of_append, DFA.eval, hTc_evalFrom]
      rfl
    have hdig : (⟨digit b x (n + t₀), digit_lt hb0 x (n + t₀)⟩ : Fin b) =
        ⟨digit b (x * (b : ℝ) ^ t₀) n, digit_lt hb0 _ n⟩ := by
      apply Fin.ext
      dsimp only
      rw [add_comm, digit_add]
    rw [hstate, hdig]
  exact isNormalSeq_shift_lossless t₀ (hseq_eq.symm ▸ hnorm')

/-- **Information-lossless finite-state Mealy transducers preserve normality (digit sequences)**,
strictly generalizing output-bijective transducers (`Real.isNormalSeq_mealySeq`) to allow
arbitrary finite-delay lossless encodings. -/
theorem isNormalSeq_mealySeq_of_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hloss : T.IsInformationLossless) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) :=
  isNormalSeq_mealySeq_of_recurrent_isInformationLossless hb T (fun p _ _ ↦ hloss p) hx

/-- **Information-lossless finite-state Mealy transducers preserve normality (real numbers)**. -/
theorem isNormalIn_mealyReal_of_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hloss : T.IsInformationLossless) (hx : IsNormalIn b x) :
    IsNormalIn b (mealyReal b T x) :=
  (isNormalIn_mealyReal_iff hb T x).2 (isNormalSeq_mealySeq_of_isInformationLossless hb T hloss hx)

/-! ### Part 2: Necessity — lossy transducers have a forbidden word and destroy normality -/

/-- In a strongly connected finite DFA, every pair of states is joined by a word of length
strictly less than `Fintype.card Q`. -/
private lemma exists_short_path {Q : Type*} [Fintype Q] (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M) (p q : Q) :
    ∃ v : List (Fin b), v.length < Fintype.card Q ∧ M.evalFrom p v = q := by
  classical
  have hex : ∃ n : ℕ, ∃ v : List (Fin b), v.length = n ∧ M.evalFrom p v = q := by
    obtain ⟨v, hv⟩ := hconn p q
    exact ⟨v.length, v, rfl, hv⟩
  set n := Nat.find hex
  obtain ⟨v, hv_len, hv_eq⟩ := Nat.find_spec hex
  refine ⟨v, ?_, hv_eq⟩
  by_contra hge
  push Not at hge
  let f : Fin (Fintype.card Q + 1) → Q := fun i ↦ M.evalFrom p (v.take i.val)
  have hlt : Fintype.card Q < Fintype.card (Fin (Fintype.card Q + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨i, j, hij, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  wlog hlt_ij : i.val < j.val generalizing i j
  · exact this j i hij.symm hfeq.symm (by omega)
  let v' := v.take i.val ++ v.drop j.val
  have hv'_len : v'.length < n := by
    have hj_le : j.val ≤ v.length := by omega
    simp only [v', List.length_append, List.length_take, List.length_drop]
    omega
  have hv'_eq : M.evalFrom p v' = q := by
    dsimp only [v']
    rw [DFA.evalFrom_of_append]
    change M.evalFrom (f i) (v.drop j.val) = q
    rw [hfeq]
    dsimp only [f]
    rw [← DFA.evalFrom_of_append, List.take_append_drop, hv_eq]
  exact Nat.find_min hex hv'_len ⟨v', rfl, hv'_eq⟩

/-- The set of `(outputWord, endState)` pairs reachable from state `p` in `k` steps. -/
private noncomputable def outStateSet {Q : Type*} (T : MealyTransducer b Q) (p : Q) (k : ℕ) :
    Finset ((Fin k → Fin b) × Q) := by
  classical
  exact Finset.univ.image fun u : Fin k → Fin b ↦
    (T.outputWord p u, T.toDFA.evalFrom p (List.ofFn u))

/-- **Forbidden-word obstruction**: every strongly connected finite-state Mealy transducer that is
not information-lossless admits a finite output word `w` that can *never* be produced from any
starting state. -/
theorem exists_forbiddenWord_of_not_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    (hnot : ¬ T.IsInformationLossless) :
    ∃ (M : ℕ) (w : Fin M → Fin b), ∀ (p : Q) (u : Fin M → Fin b), T.outputWord p u ≠ w := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Nonempty Q := ⟨T.start⟩
  have hb0 : 0 < b := by omega
  simp only [MealyTransducer.IsInformationLossless, MealyTransducer.IsInformationLosslessAt,
    not_forall] at hnot
  obtain ⟨q₀, r, u₁, u₂, hout_eq, hend_eq, hne_u⟩ := hnot
  have hr_pos : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    subst hr0
    exact hne_u (funext fun i ↦ Fin.elim0 i)
  set D := Fintype.card Q
  have hD_pos : 0 < D := Fintype.card_pos
  set L := D + r
  have hL_pos : 1 ≤ L := by omega
  -- Step 1: from every state `p`, there are two distinct length-`L` inputs with the same
  -- `(outputWord, endState)`, so `(outStateSet T p L).card ≤ b ^ L - 1`.
  have hstep_card : ∀ p : Q, (outStateSet T p L).card ≤ b ^ L - 1 := by
    intro p
    obtain ⟨v, hv_len, hv_eq⟩ := exists_short_path T.toDFA hconn p q₀
    set d := v.length
    have hd_lt : d < D := hv_len
    let vFin : Fin d → Fin b := fun i ↦ v[i.val]
    have hvFin_list : List.ofFn vFin = v := by
      apply List.ext_getElem
      · simp [d]
      · intro i hi₁ hi₂; simp [vFin]
    let pad : Fin (D - d) → Fin b := fun _ ↦ ⟨0, hb0⟩
    have hlen_eq : (d + r) + (D - d) = L := by omega
    let w₁ : Fin L → Fin b := castWord hlen_eq (Fin.append (Fin.append vFin u₁) pad)
    let w₂ : Fin L → Fin b := castWord hlen_eq (Fin.append (Fin.append vFin u₂) pad)
    have hw_ne : w₁ ≠ w₂ := by
      intro heq
      apply hne_u
      funext j
      have hidx : d + j.val < L := by omega
      have h := congrFun heq ⟨d + j.val, hidx⟩
      have hcast : Fin.cast hlen_eq.symm ⟨d + j.val, hidx⟩ =
          Fin.castAdd (D - d) (Fin.natAdd d j) := by
        apply Fin.ext; rfl
      simp only [w₁, w₂, castWord, hcast, Fin.append_left, Fin.append_right] at h
      exact h
    have hw_out : T.outputWord p w₁ = T.outputWord p w₂ := by
      simp only [w₁, w₂, outputWord_castWord, outputWord_append, list_ofFn_append,
        DFA.evalFrom_of_append, hvFin_list, hv_eq, hout_eq, hend_eq]
    have hw_end : T.toDFA.evalFrom p (List.ofFn w₁) = T.toDFA.evalFrom p (List.ofFn w₂) := by
      simp only [w₁, w₂, list_ofFn_castWord, list_ofFn_append, DFA.evalFrom_of_append,
        hvFin_list, hv_eq, hend_eq]
    let Φ : (Fin L → Fin b) → (Fin L → Fin b) × Q :=
      fun u ↦ (T.outputWord p u, T.toDFA.evalFrom p (List.ofFn u))
    have hΦ_eq : Φ w₁ = Φ w₂ := Prod.ext hw_out hw_end
    have hsub : outStateSet T p L ⊆ (Finset.univ.erase w₂).image Φ := by
      intro y hy
      simp only [outStateSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
      obtain ⟨u, rfl⟩ := hy
      by_cases hu : u = w₂
      · subst hu
        exact Finset.mem_image.2 ⟨w₁, Finset.mem_erase.2 ⟨hw_ne, Finset.mem_univ w₁⟩, hΦ_eq⟩
      · exact Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨hu, Finset.mem_univ u⟩, rfl⟩
    calc (outStateSet T p L).card
        ≤ ((Finset.univ.erase w₂).image Φ).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.erase w₂).card := Finset.card_image_le
      _ = b ^ L - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ w₂), Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin]
  -- Step 2: by induction on `m`, `(outStateSet T p (m * L)).card ≤ (b ^ L - 1) ^ m`.
  have hind : ∀ (m : ℕ) (p : Q), (outStateSet T p (m * L)).card ≤ (b ^ L - 1) ^ m := by
    intro m
    induction m with
    | zero =>
      intro p
      have h0 : (0 : ℕ) * L = 0 := zero_mul L
      rw [h0, pow_zero]
      have : (outStateSet T p 0).card ≤ (Finset.univ : Finset (Fin 0 → Fin b)).card :=
        Finset.card_image_le
      simpa using this
    | succ m ih =>
      intro p
      have hmul : m * L + L = (m + 1) * L := by ring
      let comb : ((Fin (m * L) → Fin b) × Q) → Finset ((Fin ((m + 1) * L) → Fin b) × Q) :=
        fun x ↦ (outStateSet T x.2 L).image fun y ↦ (castWord hmul (Fin.append x.1 y.1), y.2)
      have hsub : outStateSet T p ((m + 1) * L) ⊆ (outStateSet T p (m * L)).biUnion comb := by
        intro z hz
        simp only [outStateSet, Finset.mem_image, Finset.mem_univ, true_and] at hz
        obtain ⟨u, rfl⟩ := hz
        let u₁ : Fin (m * L) → Fin b := fun i ↦ u ⟨i.val, by omega⟩
        let u₂ : Fin L → Fin b := fun j ↦ u ⟨m * L + j.val, by omega⟩
        have hu_eq : u = castWord hmul (Fin.append u₁ u₂) := by
          funext i
          dsimp only [castWord]
          by_cases hi : i.val < m * L
          · have hcast : Fin.cast hmul.symm i = Fin.castAdd L ⟨i.val, hi⟩ := by
              apply Fin.ext; rfl
            rw [hcast, Fin.append_left]
          · have hsub_lt : i.val - m * L < L := by omega
            have hcast : Fin.cast hmul.symm i = Fin.natAdd (m * L) ⟨i.val - m * L, hsub_lt⟩ := by
              apply Fin.ext; simp only [Fin.val_cast, Fin.val_natAdd]; omega
            rw [hcast, Fin.append_right]
            congr 1; apply Fin.ext; simp only; omega
        rw [Finset.mem_biUnion]
        refine ⟨(T.outputWord p u₁, T.toDFA.evalFrom p (List.ofFn u₁)), ?_, ?_⟩
        · exact Finset.mem_image.2 ⟨u₁, Finset.mem_univ u₁, rfl⟩
        · simp only [comb, Finset.mem_image]
          refine ⟨(T.outputWord (T.toDFA.evalFrom p (List.ofFn u₁)) u₂,
            T.toDFA.evalFrom (T.toDFA.evalFrom p (List.ofFn u₁)) (List.ofFn u₂)),
            Finset.mem_image.2 ⟨u₂, Finset.mem_univ u₂, rfl⟩, ?_⟩
          refine Prod.ext ?_ ?_
          · conv_rhs => rw [hu_eq, outputWord_castWord, outputWord_append]
          · conv_rhs => rw [hu_eq, list_ofFn_castWord, list_ofFn_append, DFA.evalFrom_of_append]
      calc (outStateSet T p ((m + 1) * L)).card
          ≤ ((outStateSet T p (m * L)).biUnion comb).card := Finset.card_le_card hsub
        _ ≤ ∑ x ∈ outStateSet T p (m * L), (comb x).card := Finset.card_biUnion_le
        _ ≤ ∑ x ∈ outStateSet T p (m * L), (b ^ L - 1) :=
            Finset.sum_le_sum fun x _ ↦ Finset.card_image_le.trans (hstep_card x.2)
        _ = (outStateSet T p (m * L)).card * (b ^ L - 1) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (b ^ L - 1) ^ m * (b ^ L - 1) := Nat.mul_le_mul_right _ (ih p)
        _ = (b ^ L - 1) ^ (m + 1) := (pow_succ _ _).symm
  -- Step 3: choose `m` with `D * (b ^ L - 1) ^ m < b ^ (m * L)` and pick a missing word `w`.
  have hbL_pos : 1 ≤ b ^ L := Nat.one_le_pow L b hb0
  have hratio_lt : ((b ^ L - 1 : ℕ) : ℝ) / (b ^ L : ℝ) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < (b ^ L : ℝ))]
    have : b ^ L - 1 < b ^ L := by omega
    exact_mod_cast this
  have hratio_nonneg : 0 ≤ ((b ^ L - 1 : ℕ) : ℝ) / (b ^ L : ℝ) := by positivity
  have htend : Tendsto (fun m : ℕ ↦ (D : ℝ) * (((b ^ L - 1 : ℕ) : ℝ) / (b ^ L : ℝ)) ^ m)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt).const_mul (D : ℝ)
  obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds zero_lt_one)).exists
  have hnat_lt : D * (b ^ L - 1) ^ m < b ^ (m * L) := by
    have hmul_pos : (0 : ℝ) < ((b ^ L : ℝ) ^ m) := by positivity
    have h1 : (D : ℝ) * ((b ^ L - 1 : ℕ) : ℝ) ^ m < (b ^ L : ℝ) ^ m := by
      rw [div_pow, ← mul_div_assoc, div_lt_one hmul_pos] at hm
      exact hm
    have h2 : (b ^ L : ℝ) ^ m = ((b ^ (m * L) : ℕ) : ℝ) := by
      push_cast
      rw [← pow_mul, mul_comm]
    rw [h2] at h1
    exact_mod_cast h1
  let allOut : Finset (Fin (m * L) → Fin b) :=
    Finset.univ.biUnion fun p : Q ↦ (outStateSet T p (m * L)).image Prod.fst
  have hall_lt : allOut.card < (Finset.univ : Finset (Fin (m * L) → Fin b)).card := by
    calc allOut.card
        ≤ ∑ p : Q, ((outStateSet T p (m * L)).image Prod.fst).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : Q, (b ^ L - 1) ^ m :=
          Finset.sum_le_sum fun p _ ↦ Finset.card_image_le.trans (hind m p)
      _ = D * (b ^ L - 1) ^ m := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ < b ^ (m * L) := hnat_lt
      _ = (Finset.univ : Finset (Fin (m * L) → Fin b)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  obtain ⟨w, -, hw_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hall_lt
  refine ⟨m * L, w, fun p u hu ↦ hw_not ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨p, Finset.mem_univ p,
    Finset.mem_image.2 ⟨(T.outputWord p u, T.toDFA.evalFrom p (List.ofFn u)),
      Finset.mem_image.2 ⟨u, Finset.mem_univ u, rfl⟩, hu⟩⟩

/-- **Universal failure of strongly connected lossy transducers (digit sequences)**: if `T` is
strongly connected and not information-lossless, then `mealySeq b hb0 T x` is *never* normal in
base `b` (for *any* `x : ℝ`). -/
theorem not_isNormalSeq_mealySeq_of_not_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    (hnot : ¬ T.IsInformationLossless) (x : ℝ) :
    ¬ IsNormalSeq b (mealySeq b (by omega) T x) := by
  have hb0 : 0 < b := by omega
  obtain ⟨M, w, hw⟩ := exists_forbiddenWord_of_not_isInformationLossless hb T hconn hnot
  intro hnorm
  have hlim := hnorm M w
  have hzero : ∀ N : ℕ,
      ((Finset.range N).filter fun t ↦
        ∀ j : Fin M, mealySeq b hb0 T x (t + j.val) = (w j : ℕ)).card = 0 := fun N ↦ by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ hmatch
    let p := T.toDFA.eval (digitPrefix b hb0 x t)
    let u : Fin M → Fin b := fun j ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩
    apply hw p u
    funext j
    apply Fin.ext
    have hj := hmatch j
    simp only [MealyTransducer.outputWord, mealySeq, p, u] at hj ⊢
    rw [digitPrefix_add hb0 x t j.val, DFA.eval, DFA.evalFrom_of_append] at hj
    exact hj
  have h0 : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun t ↦
        ∀ j : Fin M, mealySeq b hb0 T x (t + j.val) = (w j : ℕ)).card : ℝ) / N)
      atTop (𝓝 0) := by
    simp_rw [hzero, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  have hpos : (0 : ℝ) < ((b : ℝ) ^ M)⁻¹ := by positivity
  linarith [tendsto_nhds_unique hlim h0]

/-- **Universal failure of strongly connected lossy transducers (real numbers)**: if `T` is
strongly connected and not information-lossless, then `mealyReal b T x` is *never* normal in
base `b` (for *any* `x : ℝ`). -/
theorem not_isNormalIn_mealyReal_of_not_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    (hnot : ¬ T.IsInformationLossless) (x : ℝ) :
    ¬ IsNormalIn b (mealyReal b T x) := by
  rw [isNormalIn_mealyReal_iff hb T x]
  exact not_isNormalSeq_mealySeq_of_not_isInformationLossless hb T hconn hnot x

/-! ### Part 3: Zero-one dichotomy and exact characterizations -/

/-- **Zero-one dichotomy for strongly connected finite-state Mealy transducers (digit sequences)**:
for a strongly connected finite-state Mealy transducer `T`, the following are equivalent:
1. `T` is information-lossless;
2. `T` preserves base-`b` normality for *every* base-`b` normal number `x`;
3. `T` preserves base-`b` normality for *some* base-`b` normal number `x`. -/
theorem mealySeq_preserves_isNormal_iff_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA) :
    T.IsInformationLossless ↔
      (∀ x : ℝ, IsNormalIn b x → IsNormalSeq b (mealySeq b (by omega) T x)) ∧
      (∃ x : ℝ, IsNormalIn b x ∧ IsNormalSeq b (mealySeq b (by omega) T x)) := by
  have : NeZero b := ⟨by omega⟩
  constructor
  · intro hloss
    refine ⟨fun x hx ↦ isNormalSeq_mealySeq_of_isInformationLossless hb T hloss hx,
      ⟨copelandErdos b, isNormalIn_copelandErdos hb,
        isNormalSeq_mealySeq_of_isInformationLossless hb T hloss (isNormalIn_copelandErdos hb)⟩⟩
  · rintro ⟨_, ⟨x, _, hseq⟩⟩
    by_contra hnot
    exact not_isNormalSeq_mealySeq_of_not_isInformationLossless hb T hconn hnot x hseq

/-- **Zero-one dichotomy for strongly connected finite-state Mealy transducers (real numbers)**. -/
theorem mealyReal_preserves_isNormal_iff_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA) :
    T.IsInformationLossless ↔
      (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (mealyReal b T x)) ∧
      (∃ x : ℝ, IsNormalIn b x ∧ IsNormalIn b (mealyReal b T x)) := by
  simp_rw [isNormalIn_mealyReal_iff hb T]
  exact mealySeq_preserves_isNormal_iff_isInformationLossless hb T hconn

/-- **Exact characterization for arbitrary finite-state Mealy transducers (digit sequences)**:
an arbitrary (not necessarily strongly connected) finite-state Mealy transducer `T` preserves
base-`b` normality for all `x` if and only if every reachable recurrent state of `T` is
information-lossless. -/
theorem mealySeq_preserves_isNormal_iff_recurrent_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalSeq b (mealySeq b (by omega) T x)) ↔
      (∀ p : Q, T.IsReachable p → T.IsRecurrent p → T.IsInformationLosslessAt p) := by
  have hb0 : 0 < b := by omega
  have : NeZero b := ⟨by omega⟩
  refine ⟨fun hpres q₀ hq₀_reach hq₀_rec ↦ ?_,
    fun hloss x hx ↦ isNormalSeq_mealySeq_of_recurrent_isInformationLossless hb T hloss hx⟩
  by_contra hnot_at
  -- Restrict `T` to the strongly connected recurrent SCC `C` of `q₀`
  let C : Type _ := {r : Q // ∃ v : List (Fin b), T.toDFA.evalFrom q₀ v = r}
  have hstep_closed : ∀ (r : C) (a : Fin b),
      ∃ v : List (Fin b), T.toDFA.evalFrom q₀ v = T.step r.val a := by
    rintro ⟨r, v, hv⟩ a
    exact ⟨v ++ [a], by rw [DFA.evalFrom_of_append, hv]; rfl⟩
  let Tc : MealyTransducer b C :=
    { step := fun r a ↦ ⟨T.step r.val a, hstep_closed r a⟩
      start := ⟨q₀, [], rfl⟩
      out := fun r a ↦ T.out r.val a }
  have hTc_evalFrom : ∀ (r : C) (v : List (Fin b)),
      (Tc.toDFA.evalFrom r v).val = T.toDFA.evalFrom r.val v := by
    intro r v
    induction v generalizing r with
    | nil => rfl
    | cons a v ih => exact ih (Tc.step r a)
  have hTc_outputWord : ∀ (r : C) {k : ℕ} (u : Fin k → Fin b),
      Tc.outputWord r u = T.outputWord r.val u := by
    intro r k u
    funext j
    simp only [MealyTransducer.outputWord, Tc, hTc_evalFrom]
  have hTc_conn : IsStronglyConnected Tc.toDFA := by
    rintro ⟨r₁, v₁, hv₁⟩ ⟨r₂, v₂, hv₂⟩
    obtain ⟨w₁, hw₁⟩ := hq₀_rec r₁ ⟨v₁, hv₁⟩
    refine ⟨w₁ ++ v₂, Subtype.ext ?_⟩
    rw [hTc_evalFrom, DFA.evalFrom_of_append, hw₁, hv₂]
  have hTc_not : ¬ Tc.IsInformationLossless := by
    intro hloss
    apply hnot_at
    intro k u₁ u₂ hout hend
    refine hloss ⟨q₀, [], rfl⟩ k u₁ u₂ ?_ (Subtype.ext ?_)
    · simpa only [hTc_outputWord] using hout
    · simpa only [hTc_evalFrom] using hend
  -- Construct a base-`b` normal `x` driving `T` to `q₀` and then following `copelandErdos b`
  obtain ⟨v, hv⟩ := hq₀_reach
  let y := copelandErdos b
  have hy : IsNormalIn b y := isNormalIn_copelandErdos hb
  let d : ℕ → Fin b := fun n ↦
    if h : n < v.length then v[n] else ⟨digit b y (n - v.length), digit_lt hb0 y _⟩
  let x := ofDigits d
  have hx_seq : IsNormalSeq b fun n ↦ (d n : ℕ) := by
    refine isNormalSeq_shift_lossless v.length ?_
    have hshift : (fun n : ℕ ↦ (d (n + v.length) : ℕ)) = fun n ↦ digit b y n := by
      funext n
      have hnot_lt : ¬ n + v.length < v.length := by omega
      simp [d, hnot_lt]
    rw [hshift]
    exact hy
  have hx_norm : IsNormalIn b x := isNormalIn_ofDigits hb hx_seq
  have hx_dig : ∀ n : ℕ, digit b x n = (d n : ℕ) := digit_ofDigits_of_isNormalSeq hb hx_seq
  have hpre_v : digitPrefix b hb0 x v.length = v := by
    apply List.ext_getElem
    · simp [digitPrefix]
    · intro i hi₁ hi₂
      simp only [digitPrefix, List.getElem_ofFn]
      apply Fin.ext
      simp [hx_dig i, d, hi₂]
  -- After step `v.length`, `T` on `x` agrees with `Tc` on `x * b ^ v.length`
  have hseq_tail : (fun n : ℕ ↦ mealySeq b hb0 T x (n + v.length)) =
      mealySeq b hb0 Tc (x * (b : ℝ) ^ v.length) := by
    funext n
    simp only [mealySeq]
    have hpre_eq : digitPrefix b hb0 x (n + v.length) =
        v ++ digitPrefix b hb0 (x * (b : ℝ) ^ v.length) n := by
      rw [add_comm, digitPrefix_add hb0 x v.length n, hpre_v]
      congr 1
      apply List.ext_getElem
      · simp [digitPrefix]
      · intro i hi₁ hi₂
        simp only [digitPrefix, List.getElem_ofFn]
        apply Fin.ext; dsimp only; rw [digit_add]
    have hstate : T.toDFA.eval (digitPrefix b hb0 x (n + v.length)) =
        (Tc.toDFA.eval (digitPrefix b hb0 (x * (b : ℝ) ^ v.length) n)).val := by
      rw [hpre_eq, DFA.eval, DFA.evalFrom_of_append, ← DFA.eval, hv, DFA.eval, hTc_evalFrom]
      rfl
    have hdig : (⟨digit b x (n + v.length), digit_lt hb0 x _⟩ : Fin b) =
        ⟨digit b (x * (b : ℝ) ^ v.length) n, digit_lt hb0 _ n⟩ := by
      apply Fin.ext; dsimp only; rw [add_comm, digit_add]
    rw [hstate, hdig]
  -- Yet `mealySeq b hb0 T x` is normal, so its shifted tail `mealySeq b hb0 Tc (x * b^|v|)` is
  -- also normal, contradicting universal failure of the strongly connected lossy transducer `Tc`!
  have hT_norm : IsNormalSeq b (mealySeq b hb0 T x) := hpres x hx_norm
  have hTc_norm : IsNormalSeq b (mealySeq b hb0 Tc (x * (b : ℝ) ^ v.length)) := by
    rw [← hseq_tail]
    intro k w
    have hlim := hT_norm k w
    set s := v.length
    have hdiff : ∀ N : ℕ,
        (((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + s + j.val) = (w j : ℕ)).card : ℝ) / N -
        (((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + j.val) = (w j : ℕ)).card : ℝ) / N =
        ((((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + s + j.val) = (w j : ℕ)).card : ℝ) -
        (((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + j.val) = (w j : ℕ)).card : ℝ)) / N :=
      fun N ↦ (sub_div _ _ _).symm
    have habs_le : ∀ N : ℕ,
        |(((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + s + j.val) = (w j : ℕ)).card : ℝ) -
        (((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + j.val) = (w j : ℕ)).card : ℝ)| ≤ s := by
      intro N
      set A := (Finset.range N).filter fun i ↦
        ∀ j : Fin k, mealySeq b hb0 T x (i + j.val) = (w j : ℕ)
      set B := (Finset.range N).filter fun i ↦
        ∀ j : Fin k, mealySeq b hb0 T x (i + s + j.val) = (w j : ℕ)
      have hA_le : A.card ≤ B.card + s := by
        have hsub : A ⊆ B.image (· + s) ∪ Finset.range s := by
          intro i hi
          simp only [A, B, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
            Finset.mem_image] at hi ⊢
          by_cases his : i < s
          · exact Or.inr his
          · left
            refine ⟨i - s, ⟨by omega, fun j ↦ ?_⟩, by omega⟩
            rw [Nat.sub_add_cancel (by omega)]
            exact hi.2 j
        calc A.card ≤ (B.image (· + s) ∪ Finset.range s).card := Finset.card_le_card hsub
          _ ≤ (B.image (· + s)).card + (Finset.range s).card := Finset.card_union_le _ _
          _ ≤ B.card + s := by
            rw [Finset.card_range]
            exact Nat.add_le_add_right Finset.card_image_le s
      have hB_le : B.card ≤ A.card + s := by
        have hsub : B ⊆ (A.filter (s ≤ ·)).image (· - s) ∪ Finset.Ico (N - s) N := by
          intro i hi
          simp only [A, B, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
            Finset.mem_image, Finset.mem_Ico] at hi ⊢
          by_cases his : i + s < N
          · left
            refine ⟨i + s, ⟨⟨his, hi.2⟩, by omega⟩, by omega⟩
          · right; omega
        calc B.card
            ≤ ((A.filter (s ≤ ·)).image (· - s) ∪ Finset.Ico (N - s) N).card :=
              Finset.card_le_card hsub
          _ ≤ ((A.filter (s ≤ ·)).image (· - s)).card + (Finset.Ico (N - s) N).card :=
              Finset.card_union_le _ _
          _ ≤ (A.filter (s ≤ ·)).card + s := by
              rw [Nat.card_Ico]
              exact Nat.add_le_add Finset.card_image_le (by omega)
          _ ≤ A.card + s := Nat.add_le_add_right (Finset.card_filter_le _ _) s
      rw [abs_le]
      have hA_r : (A.card : ℝ) ≤ (B.card : ℝ) + s := by exact_mod_cast hA_le
      have hB_r : (B.card : ℝ) ≤ (A.card : ℝ) + s := by exact_mod_cast hB_le
      constructor <;> linarith
    have hzero : Tendsto (fun N : ℕ ↦
        (((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + s + j.val) = (w j : ℕ)).card : ℝ) / N -
        (((Finset.range N).filter fun i ↦
            ∀ j : Fin k, mealySeq b hb0 T x (i + j.val) = (w j : ℕ)).card : ℝ) / N)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun N : ℕ ↦ (s : ℝ) / N) (fun N ↦ ?_)
        (tendsto_const_div_atTop_nhds_zero_nat (s : ℝ))
      rw [hdiff N, Real.norm_eq_abs, abs_div, Nat.abs_cast]
      exact div_le_div_of_nonneg_right (habs_le N) (Nat.cast_nonneg N)
    have hadd := hzero.add hlim
    rw [zero_add] at hadd
    refine hadd.congr fun N ↦ ?_
    simp only [show ∀ i j : ℕ, i + j + s = i + s + j from fun i j ↦ by omega]
    ring
  exact not_isNormalSeq_mealySeq_of_not_isInformationLossless hb Tc hTc_conn hTc_not
    (x * (b : ℝ) ^ v.length) hTc_norm

/-- **Exact characterization for arbitrary finite-state Mealy transducers (real numbers)**. -/
theorem mealyReal_preserves_isNormal_iff_recurrent_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (mealyReal b T x)) ↔
      (∀ p : Q, T.IsReachable p → T.IsRecurrent p → T.IsInformationLosslessAt p) := by
  simp_rw [isNormalIn_mealyReal_iff hb T]
  exact mealySeq_preserves_isNormal_iff_recurrent_isInformationLossless hb T

/-! ### Strict separation: 1-step delay is information-lossless yet not output-bijective -/

/-- Evaluating `delayMealy` on a nonempty word returns its last letter. -/
private lemma delayMealy_evalFrom_ofFn (init : Fin b) (p : Fin b) {k : ℕ} (u : Fin k → Fin b) :
    (delayMealy b init).toDFA.evalFrom p (List.ofFn u) =
      if h : k = 0 then p else u ⟨k - 1, by omega⟩ := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    have hlist : List.ofFn u = u 0 :: List.ofFn (fun i : Fin k ↦ u i.succ) := by
      simp [List.ofFn_succ]
    rw [hlist, DFA.evalFrom_cons]
    change (delayMealy b init).toDFA.evalFrom (u 0) (List.ofFn fun i : Fin k ↦ u i.succ) = _
    rw [ih (u 0)]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
    split_ifs with h0
    · subst h0; rfl
    · congr 1; apply Fin.ext; simp only [Fin.val_succ]; omega

/-- The 1-step delay transducer is information-lossless. -/
theorem delayMealy_isInformationLossless (init : Fin b) :
    (delayMealy b init).IsInformationLossless := by
  intro p k u v hout hend
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · funext i; exact Fin.elim0 i
  · funext i
    by_cases hi : i.val + 1 < k
    · have h := congrFun hout ⟨i.val + 1, hi⟩
      change (delayMealy b init).toDFA.evalFrom p
          (List.ofFn fun m : Fin (i.val + 1) ↦ u ⟨m.val, Nat.lt_trans m.isLt hi⟩) =
        (delayMealy b init).toDFA.evalFrom p
          (List.ofFn fun m : Fin (i.val + 1) ↦ v ⟨m.val, Nat.lt_trans m.isLt hi⟩) at h
      rw [delayMealy_evalFrom_ofFn, delayMealy_evalFrom_ofFn] at h
      simpa using h
    · have hik : i = ⟨k - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hik]
      rw [delayMealy_evalFrom_ofFn, delayMealy_evalFrom_ofFn] at hend
      have hk0 : k ≠ 0 := by omega
      simpa [hk0] using hend

/-- For `b ≥ 2`, the 1-step delay transducer is *not* output-bijective (`out q` is constant). -/
theorem delayMealy_not_isOutputBijective (hb : 2 ≤ b) (init : Fin b) :
    ¬ (delayMealy b init).IsOutputBijective := by
  intro hbij
  have h := (hbij init).1 (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩) rfl
  have hval := congrArg Fin.val h
  simp at hval

/-- The 1-step delay transducer preserves base-`b` normality (digit sequences), showing that
information-losslessness strictly generalizes output-bijectivity. -/
theorem isNormalSeq_delayMealy (hb : 2 ≤ b) (init : Fin b) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) (delayMealy b init) x) :=
  isNormalSeq_mealySeq_of_isInformationLossless hb (delayMealy b init)
    (delayMealy_isInformationLossless init) hx

/-- The 1-step delay transducer preserves base-`b` normality (real numbers). -/
theorem isNormalIn_delayMealy (hb : 2 ≤ b) (init : Fin b) (hx : IsNormalIn b x) :
    IsNormalIn b (mealyReal b (delayMealy b init) x) :=
  isNormalIn_mealyReal_of_isInformationLossless hb (delayMealy b init)
    (delayMealy_isInformationLossless init) hx

end Helpers

end Real
