/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.FiniteState

import Mathlib.Data.Nat.Nth

/-!
# Agafonov's theorem: finite-state selection preserves normality

We prove Agafonov's theorem (1968): if `x : ℝ` is normal in base `b ≥ 2` and a deterministic
finite automaton `M : DFA (Fin b) Q` (equivalently, any regular language `L : Language (Fin b)`)
selects infinitely many digits of `x` based on the prefix preceding each digit, then the selected
subsequence is normal in base `b`.

## Proof outline

Following Olivier Carton's direct combinatorial proof (`arXiv:2005.00255`, Section 4) and building
on the finite-state Markov ergodicity in `Mathlib.NumberTheory.Normal.FiniteState`:
1. **Oblivious selector balance (Carton Lemmas 5 & 9)**: By induction on `n`, at most `b ^ (n - k)`
   length-`n` words output a given length-`k` prefix `w`, and by `card_bad_stateCount_lt` at least
   `(1 - ε) b ^ (n - k)` do.
2. **Snake automaton**: Applying `tendsto_dfa_stateFreq` to the strongly connected snake automaton
   on `Q × (Fin n → Fin b)` yields Agafonov's theorem for strongly connected DFAs.
3. **Recurrent SCC entry (Carton Lemma 8)**: Every finite DFA has a single word steering every
   state into a recurrent strongly connected component; since `x` is disjunctive, the run enters
   and stays in a strongly connected sub-automaton after finitely many steps, reducing the general
   case to the strongly connected case.

## Main statements

* `Real.isNormalSeq_dfaSelect`, `Real.isNormalIn_dfaSelect`: Agafonov's theorem for any finite DFA.
* `Real.isNormalSeq_regularSelect`, `Real.isNormalIn_regularSelect`: Agafonov's theorem for any
  regular language.

## References

* [V. N. Agafonov, *Normal sequences and finite automata*, Dokl. Akad. Nauk SSSR 179 (1968),
  255–256][Agafonov1968]
* [O. Carton, *A direct proof of Agafonov's theorem and an extension to shifts of finite type*,
  arXiv:2005.00255][Carton2020]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- The set of indices `n` whose preceding base-`b` digit prefix of `x` is accepted by `M`. -/
def dfaSelectSet (b : ℕ) {Q : Type*} (M : DFA (Fin b) Q) (x : ℝ) : Set ℕ :=
  {n : ℕ | ∃ hb : 0 < b, M.eval (digitPrefix b hb x n) ∈ M.accept}

/-- The sequence of base-`b` digits of `x` selected by the DFA `M`. -/
noncomputable def dfaSelectSeq (b : ℕ) {Q : Type*} (M : DFA (Fin b) Q) (x : ℝ) (n : ℕ) : ℕ :=
  digit b x (Nat.nth (· ∈ dfaSelectSet b M x) n)

/-- The real number in `[0, 1)` formed from the base-`b` digits of `x` selected by `M`. -/
noncomputable def dfaSelect (b : ℕ) {Q : Type*} (M : DFA (Fin b) Q) (x : ℝ) : ℝ :=
  if hb : 0 < b then
    ofDigits fun n ↦ (⟨dfaSelectSeq b M x n, digit_lt hb x _⟩ : Fin b)
  else 0

/-- The set of indices `n` whose preceding base-`b` digit prefix of `x` belongs to `L`. -/
def regularSelectSet (b : ℕ) (L : Language (Fin b)) (x : ℝ) : Set ℕ :=
  {n : ℕ | ∃ hb : 0 < b, digitPrefix b hb x n ∈ L}

/-- The sequence of base-`b` digits of `x` selected by the language `L`. -/
noncomputable def regularSelectSeq (b : ℕ) (L : Language (Fin b)) (x : ℝ) (n : ℕ) : ℕ :=
  digit b x (Nat.nth (· ∈ regularSelectSet b L x) n)

/-- The real number in `[0, 1)` formed from the base-`b` digits of `x` selected by `L`. -/
noncomputable def regularSelect (b : ℕ) (L : Language (Fin b)) (x : ℝ) : ℝ :=
  if hb : 0 < b then
    ofDigits fun n ↦ (⟨regularSelectSeq b L x n, digit_lt hb x _⟩ : Fin b)
  else 0


section Agafonov

variable {Q : Type*} [Fintype Q]

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

/-! ### Oblivious selector output counting (Carton Lemmas 5 & 9) -/

/-- The digits output by the oblivious selector associated with `M` starting from state `p` while
reading `u`. -/
private noncomputable def selectWord (M : DFA (Fin b) Q) (p : Q) : List (Fin b) → List (Fin b)
  | [] => []
  | a :: u =>
    open Classical in
    if p ∈ M.accept then a :: selectWord M (M.step p a) u
    else selectWord M (M.step p a) u

omit [Fintype Q] in
private lemma selectWord_append (M : DFA (Fin b) Q) (p : Q) (u v : List (Fin b)) :
    selectWord M p (u ++ v) = selectWord M p u ++ selectWord M (M.evalFrom p u) v := by
  induction u generalizing p with
  | nil => simp [selectWord]
  | cons a u ih =>
    classical
    simp only [List.cons_append, selectWord, DFA.evalFrom_cons]
    split_ifs <;> simp [ih]

private lemma length_selectWord_eq_sum (M : DFA (Fin b) Q) (p : Q) (n : ℕ) (u : Fin n → Fin b) :
    (selectWord M p (List.ofFn u)).length =
      open Classical in
      ∑ q ∈ Finset.univ.filter (fun q : Q ↦ q ∈ M.accept), stateCount M p u q := by
  classical
  induction n generalizing p with
  | zero =>
    simp [selectWord, stateCount]
  | succ n ih =>
    rw [List.ofFn_succ, selectWord]
    have hsc : ∀ q : Q, stateCount M p u q =
        (if p = q then 1 else 0) + stateCount M (M.step p (u 0)) (fun i ↦ u i.succ) q := fun q ↦ by
      simp only [stateCount]
      let S := (Finset.univ : Finset (Fin (n + 1))).filter fun t ↦
        M.evalFrom p (List.ofFn fun i : Fin t.val ↦ u ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩) = q
      let S' := (Finset.univ : Finset (Fin n)).filter fun t ↦
        M.evalFrom (M.step p (u 0))
          (List.ofFn fun i : Fin t.val ↦ u (⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ : Fin n).succ) = q
      have hunion : S = (if p = q then {(0 : Fin (n + 1))} else ∅) ∪ S'.image Fin.succ := by
        ext t
        refine Fin.cases ?_ ?_ t
        · by_cases hpq : p = q <;> simp [S, S', hpq]
        · intro t'
          simp only [S, S', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_image, Fin.succ_inj, exists_eq_right]
          have hne0 : t'.succ ≠ 0 := Fin.succ_ne_zero t'
          have hnot : t'.succ ∉ (if p = q then ({(0 : Fin (n + 1))} : Finset _) else ∅) := by
            split_ifs <;> simp [hne0]
          simp only [hnot, false_or]
          have hof : (List.ofFn fun i : Fin t'.succ.val ↦
                u ⟨i.val, Nat.lt_trans i.isLt t'.succ.isLt⟩) =
              u 0 :: List.ofFn fun i : Fin t'.val ↦
                u (⟨i.val, Nat.lt_trans i.isLt t'.isLt⟩ : Fin n).succ := by
            apply List.ext_getElem
            · simp
            · intro i hi₁ hi₂
              cases i <;> simp
          rw [hof, DFA.evalFrom_cons]
      have hdisj : Disjoint (if p = q then ({(0 : Fin (n + 1))} : Finset _) else ∅)
          (S'.image Fin.succ) := by
        rw [Finset.disjoint_left]
        intro t ht1 ht2
        simp only [Finset.mem_image] at ht2
        obtain ⟨t', _, rfl⟩ := ht2
        split_ifs at ht1 <;> simp at ht1
      change S.card = (if p = q then 1 else 0) + S'.card
      rw [hunion, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (Fin.succ_injective n)]
      split_ifs <;> simp
    simp_rw [hsc, Finset.sum_add_distrib]
    have hsum_ite : (∑ q ∈ Finset.univ.filter (fun q : Q ↦ q ∈ M.accept),
        if p = q then (1 : ℕ) else 0) = if p ∈ M.accept then 1 else 0 := by
      simp [Finset.sum_ite_eq]
    rw [hsum_ite, ← ih (M.step p (u 0)) (fun i ↦ u i.succ)]
    split_ifs <;> simp [add_comm]

omit [Fintype Q] in
/-- Carton Lemma 5: from any state `p`, at most `b ^ (n - w.length)` words of length `n` produce an
output having `w` as a prefix. -/
private lemma card_prefix_selectWord_le (M : DFA (Fin b) Q) (p : Q) :
    ∀ (n : ℕ) (w : List (Fin b)), w.length ≤ n →
      ((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        w <+: selectWord M p (List.ofFn u)).card ≤ b ^ (n - w.length) := by
  classical
  intro n
  induction n generalizing p with
  | zero =>
    intro w hw
    have hwnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hwnil
    simp
  | succ n ih =>
    intro w hw
    by_cases hp : p ∈ M.accept
    · cases w with
      | nil =>
        calc ((Finset.univ : Finset (Fin (n + 1) → Fin b)).filter fun u ↦
              [] <+: selectWord M p (List.ofFn u)).card
            ≤ (Finset.univ : Finset (Fin (n + 1) → Fin b)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = b ^ (n + 1) := by simp
      | cons a w' =>
        have hsub : ((Finset.univ : Finset (Fin (n + 1) → Fin b)).filter fun u ↦
            a :: w' <+: selectWord M p (List.ofFn u)) ⊆
            ((Finset.univ : Finset (Fin n → Fin b)).filter fun v ↦
              w' <+: selectWord M (M.step p a) (List.ofFn v)).image (Fin.cons a) := by
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.ofFn_succ, selectWord, hp,
            ↓reduceIte, List.cons_prefix_cons, Finset.mem_image] at hu ⊢
          refine ⟨fun i ↦ u i.succ, ?_, ?_⟩
          · rw [hu.1]; exact hu.2
          · funext i
            refine Fin.cases ?_ ?_ i
            · simp [hu.1]
            · intro j; simp
        calc ((Finset.univ : Finset (Fin (n + 1) → Fin b)).filter fun u ↦
              a :: w' <+: selectWord M p (List.ofFn u)).card
            ≤ (((Finset.univ : Finset (Fin n → Fin b)).filter fun v ↦
                w' <+: selectWord M (M.step p a) (List.ofFn v)).image (Fin.cons a)).card :=
              Finset.card_le_card hsub
          _ ≤ ((Finset.univ : Finset (Fin n → Fin b)).filter fun v ↦
                w' <+: selectWord M (M.step p a) (List.ofFn v)).card := Finset.card_image_le
          _ ≤ b ^ (n - w'.length) := ih (M.step p a) w' (by simp at hw; omega)
          _ = b ^ (n + 1 - (a :: w').length) := by simp
    · by_cases hlen : w.length = n + 1
      · have hempty : ((Finset.univ : Finset (Fin (n + 1) → Fin b)).filter fun u ↦
            w <+: selectWord M p (List.ofFn u)) = ∅ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hpre
          have hle := hpre.length_le
          simp only [List.ofFn_succ, selectWord, hp, ↓reduceIte] at hle
          have hbound : ∀ (q : Q) (l : List (Fin b)), (selectWord M q l).length ≤ l.length := by
            intro q l
            induction l generalizing q with
            | nil => simp [selectWord]
            | cons c l ih' =>
              simp only [selectWord, List.length_cons]
              split_ifs
              · simp [Nat.succ_le_succ (ih' (M.step q c))]
              · exact (ih' (M.step q c)).trans (Nat.le_succ _)
          have := hle.trans (hbound (M.step p (u 0)) _)
          simp at this
          omega
        rw [hempty]
        simp
      · have hw' : w.length ≤ n := by omega
        let e : (Fin (n + 1) → Fin b) ≃ Fin b × (Fin n → Fin b) :=
          { toFun := fun u ↦ (u 0, fun i ↦ u i.succ)
            invFun := fun q ↦ Fin.cons q.1 q.2
            left_inv := fun u ↦ by funext i; refine Fin.cases ?_ ?_ i <;> simp
            right_inv := fun ⟨a, v⟩ ↦ by ext <;> simp }
        have hcard_eq : ((Finset.univ : Finset (Fin (n + 1) → Fin b)).filter fun u ↦
            w <+: selectWord M p (List.ofFn u)).card =
            ∑ a : Fin b, ((Finset.univ : Finset (Fin n → Fin b)).filter fun v ↦
              w <+: selectWord M (M.step p a) (List.ofFn v)).card := by
          simp_rw [Finset.card_filter]
          rw [Fintype.sum_equiv e _
            (fun q ↦ if w <+: selectWord M (M.step p q.1) (List.ofFn q.2) then (1 : ℕ) else 0)
            (fun u ↦ by simp [e, List.ofFn_succ, selectWord, hp]), Fintype.sum_prod_type]
        rw [hcard_eq]
        calc ∑ a : Fin b, ((Finset.univ : Finset (Fin n → Fin b)).filter fun v ↦
                w <+: selectWord M (M.step p a) (List.ofFn v)).card
            ≤ ∑ _a : Fin b, b ^ (n - w.length) := Finset.sum_le_sum fun a _ ↦ ih (M.step p a) w hw'
          _ = b * b ^ (n - w.length) := by simp
          _ = b ^ (n + 1 - w.length) := by
              rw [← pow_succ', show n - w.length + 1 = n + 1 - w.length by omega]

/-- Carton Lemma 9: for a strongly connected DFA with nonempty `M.accept`, for large `n` every
length-`k` word `w` is output as a prefix by between `(1 - ε) b ^ (n - k)` and `b ^ (n - k)` words
of length `n` from every state `p`, and fewer than `ε b ^ (n - k)` words output `< k` symbols. -/
private lemma card_selectWord_bounds (hb : 2 ≤ b) (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M) [Nonempty Q]
    {q₀ : Q} (hq₀ : q₀ ∈ M.accept)
    {μ : Q → ℝ} (hμ : IsStationary M μ)
    (hces : ∀ p q : Q, Tendsto (fun N ↦ cesaroProb M p N q) atTop (𝓝 (μ q)))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, k ≤ n ∧ 1 ≤ n ∧
      (∀ p : Q, (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        (selectWord M p (List.ofFn u)).length < k).card : ℝ) < ε * (b : ℝ) ^ (n - k)) ∧
      (∀ (p : Q) (w : Fin k → Fin b),
        (1 - ε) * (b : ℝ) ^ (n - k) ≤
          (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
            List.ofFn w <+: selectWord M p (List.ofFn u)).card : ℝ) ∧
        (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
            List.ofFn w <+: selectWord M p (List.ofFn u)).card : ℝ) ≤ (b : ℝ) ^ (n - k)) := by
  classical
  have hb0 : 0 < b := by omega
  have hμ0 : 0 < μ q₀ := stationary_pos hb0 M hconn hμ q₀
  have hεk : 0 < ε / (b : ℝ) ^ k := by positivity
  obtain ⟨N₀, hN₀⟩ := card_bad_stateCount_lt hb0 M hconn hμ hces hεk (by positivity : 0 < μ q₀ / 2)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * (k : ℝ) / μ q₀)
  set n : ℕ := max (max N₀ N₁) (max k 1)
  have hkn : k ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have hshort : ∀ p : Q, (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
      (selectWord M p (List.ofFn u)).length < k).card : ℝ) < ε * (b : ℝ) ^ (n - k) := by
    intro p
    have hsub : ((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        (selectWord M p (List.ofFn u)).length < k) ⊆
        (Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
          ∃ p' q' : Q, μ q₀ / 2 < |(stateCount M p' u q' : ℝ) / n - μ q'| := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      refine ⟨p, q₀, ?_⟩
      have hsc_le : stateCount M p u q₀ ≤ (selectWord M p (List.ofFn u)).length := by
        rw [length_selectWord_eq_sum]
        exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_filter.2 ⟨Finset.mem_univ q₀, hq₀⟩)
      have hlt_k : (stateCount M p u q₀ : ℝ) < k := by exact_mod_cast lt_of_le_of_lt hsc_le hu
      have hn_gt : 2 * (k : ℝ) / μ q₀ < n :=
        lt_of_lt_of_le hN₁ (by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _))
      have hkn_lt : (k : ℝ) / n < μ q₀ / 2 := by
        rw [div_lt_iff₀ (by positivity)]
        have := (div_lt_iff₀ hμ0).1 hn_gt
        linarith
      have hdiv_lt : (stateCount M p u q₀ : ℝ) / n < μ q₀ / 2 :=
        lt_trans (div_lt_div_of_pos_right hlt_k (by positivity)) hkn_lt
      rw [lt_abs]
      right
      linarith
    have hbd := hN₀ n (le_trans (le_max_left _ _) (le_max_left _ _)) (by omega)
    have hpow : (ε / (b : ℝ) ^ k) * (b : ℝ) ^ n = ε * (b : ℝ) ^ (n - k) := by
      have : (b : ℝ) ^ n = (b : ℝ) ^ k * (b : ℝ) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      rw [this]
      field_simp [show (b : ℝ) ^ k ≠ 0 by positivity]
    calc (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
            (selectWord M p (List.ofFn u)).length < k).card : ℝ)
        ≤ (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
            ∃ p' q' : Q, μ q₀ / 2 < |(stateCount M p' u q' : ℝ) / n - μ q'|).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ < (ε / (b : ℝ) ^ k) * (b : ℝ) ^ n := hbd
      _ = ε * (b : ℝ) ^ (n - k) := hpow
  refine ⟨n, hkn, hn1, hshort, fun p w ↦ ⟨?_, ?_⟩⟩
  · -- Lower bound by pigeonhole against all `w' ≠ w` and short outputs
    have hpart : (Finset.univ : Finset (Fin n → Fin b)).card =
        ((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
          (selectWord M p (List.ofFn u)).length < k).card +
        ∑ w' : Fin k → Fin b,
          ((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
            List.ofFn w' <+: selectWord M p (List.ofFn u)).card := by
      have hbi : (∑ w' : Fin k → Fin b,
          ((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
            List.ofFn w' <+: selectWord M p (List.ofFn u)).card) =
          ((Finset.univ : Finset (Fin k → Fin b)).biUnion fun w' ↦
            (Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
              List.ofFn w' <+: selectWord M p (List.ofFn u)).card := by
        rw [Finset.card_biUnion]
        intro w₁ _ w₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro u hu₁ hu₂
        simp only [Finset.mem_filter] at hu₁ hu₂
        have h1 : (selectWord M p (List.ofFn u)).take k = List.ofFn w₁ := by
          obtain ⟨t, ht⟩ := hu₁.2
          rw [← ht, List.take_left' (by simp)]
        have h2 : (selectWord M p (List.ofFn u)).take k = List.ofFn w₂ := by
          obtain ⟨t, ht⟩ := hu₂.2
          rw [← ht, List.take_left' (by simp)]
        exact hne (List.ofFn_injective (h1.symm.trans h2))
      rw [hbi, ← Finset.card_union_of_disjoint]
      · congr 1
        ext u
        simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and,
          Finset.mem_biUnion, true_iff]
        by_cases hlt : (selectWord M p (List.ofFn u)).length < k
        · exact Or.inl hlt
        · right
          push Not at hlt
          let w' : Fin k → Fin b := fun i ↦ (selectWord M p (List.ofFn u))[i.val]'(by omega)
          refine ⟨w', ?_⟩
          refine ⟨(selectWord M p (List.ofFn u)).drop k, ?_⟩
          have htake : List.ofFn w' = (selectWord M p (List.ofFn u)).take k := by
            apply List.ext_getElem
            · simp [hlt]
            · intro i hi₁ hi₂
              simp [w']
          rw [htake, List.take_append_drop]
      · rw [Finset.disjoint_left]
        intro u hu₁ hu₂
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and] at hu₁ hu₂
        obtain ⟨w', hw'⟩ := hu₂
        have := hw'.length_le
        simp at this
        omega
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun w' : Fin k → Fin b ↦ (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        List.ofFn w' <+: selectWord M p (List.ofFn u)).card : ℝ)) (Finset.mem_univ w)
    have hcast : (b : ℝ) ^ n =
        (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
          (selectWord M p (List.ofFn u)).length < k).card : ℝ) +
        ∑ w' : Fin k → Fin b, (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
          List.ofFn w' <+: selectWord M p (List.ofFn u)).card : ℝ) := by
      have := congrArg (Nat.cast (R := ℝ)) hpart
      simpa using this
    have hothers : ∑ w' ∈ Finset.univ.erase w,
        (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
          List.ofFn w' <+: selectWord M p (List.ofFn u)).card : ℝ) ≤
        (((b ^ k - 1 : ℕ) : ℝ)) * (b : ℝ) ^ (n - k) := by
      calc ∑ w' ∈ Finset.univ.erase w,
            (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
              List.ofFn w' <+: selectWord M p (List.ofFn u)).card : ℝ)
          ≤ ∑ _w' ∈ Finset.univ.erase w, (b : ℝ) ^ (n - k) := by
            refine Finset.sum_le_sum fun w' _ ↦ ?_
            have hle := card_prefix_selectWord_le M p n (List.ofFn w') (by simp [hkn])
            simp only [List.length_ofFn] at hle
            exact_mod_cast hle
        _ = ((b ^ k - 1 : ℕ) : ℝ) * (b : ℝ) ^ (n - k) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ,
              Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have hpow_sub : (b : ℝ) ^ n - ((b ^ k - 1 : ℕ) : ℝ) * (b : ℝ) ^ (n - k) =
        (b : ℝ) ^ (n - k) := by
      have h1 : 1 ≤ b ^ k := Nat.one_le_pow k b hb0
      rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_mul, one_mul, ← pow_add,
        Nat.add_sub_of_le hkn]
      ring
    linarith [hshort p]
  · have hle := card_prefix_selectWord_le M p n (List.ofFn w) (by simp [hkn])
    simp only [List.length_ofFn] at hle
    exact_mod_cast hle

/-! ### Snake automaton and strongly connected Agafonov -/

/-- The snake automaton `M_n` of window length `n ≥ 1`, whose state `(p, u)` records the current
state `p` of `M` together with the lookahead buffer `u : Fin n → Fin b`. -/
private def snakeDFA (M : DFA (Fin b) Q) (n : ℕ) (hn : 1 ≤ n) (initBuf : Fin n → Fin b) :
    DFA (Fin b) (Q × (Fin n → Fin b)) where
  step pu a :=
    (M.step pu.1 (pu.2 ⟨0, by omega⟩),
      fun j : Fin n ↦ if h : j.val + 1 < n then pu.2 ⟨j.val + 1, h⟩ else a)
  start := (M.start, initBuf)
  accept := Set.univ

omit [Fintype Q] in
private lemma snakeDFA_evalFrom_spec (M : DFA (Fin b) Q) {n : ℕ} (hn : 1 ≤ n)
    (initBuf : Fin n → Fin b) (p : Q) (u : Fin n → Fin b) (v : List (Fin b)) :
    (snakeDFA M n hn initBuf).evalFrom (p, u) v =
      (M.evalFrom p ((List.ofFn u ++ v).take v.length),
        fun j : Fin n ↦ (List.ofFn u ++ v)[v.length + j.val]'(by simp; omega)) := by
  induction v generalizing p u with
  | nil =>
    ext
    · simp
    · simp
  | cons a v ih =>
    have hstep_eq : (snakeDFA M n hn initBuf).evalFrom (p, u) (a :: v) =
        (snakeDFA M n hn initBuf).evalFrom
          (M.step p (u ⟨0, by omega⟩),
            fun j : Fin n ↦ if h : j.val + 1 < n then u ⟨j.val + 1, h⟩ else a) v := rfl
    rw [hstep_eq, ih]
    have happ : ∀ (u' : Fin n → Fin b),
        u' = (fun j : Fin n ↦ if h : j.val + 1 < n then u ⟨j.val + 1, h⟩ else a) →
        List.ofFn u ++ (a :: v) = u ⟨0, by omega⟩ :: (List.ofFn u' ++ v) := fun u' hu' ↦ by
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
            simp only [h1, h2, ↓reduceDIte, List.getElem_ofFn, hu']
          · by_cases h2 : i < n
            · have heq : i + 1 = n := by omega
              simp only [h1, h2, ↓reduceDIte, List.getElem_ofFn, hu']
              simp [heq]
            · simp only [h1, h2, ↓reduceDIte]
              have heq : i + 1 - n = (i - n) + 1 := by omega
              simp [heq]
    set u' : Fin n → Fin b :=
      fun j : Fin n ↦ if h : j.val + 1 < n then u ⟨j.val + 1, h⟩ else a
    have hlist := happ u' rfl
    refine Prod.ext ?_ (funext fun j ↦ ?_)
    · dsimp only
      rw [hlist, List.length_cons, List.take_succ_cons, DFA.evalFrom_cons]
    · dsimp only
      apply Option.some_injective
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hlist, List.length_cons,
        show v.length + 1 + j.val = (v.length + j.val) + 1 by omega, List.getElem?_cons_succ]

omit [Fintype Q] in
private lemma snakeDFA_stronglyConnected (M : DFA (Fin b) Q) (hconn : IsStronglyConnected M)
    {n : ℕ} (hn : 1 ≤ n) (initBuf : Fin n → Fin b) :
    IsStronglyConnected (snakeDFA M n hn initBuf) := by
  rintro ⟨p₁, u₁⟩ ⟨p₂, u₂⟩
  obtain ⟨v, hv⟩ := hconn (M.evalFrom p₁ (List.ofFn u₁)) p₂
  refine ⟨v ++ List.ofFn u₂, ?_⟩
  rw [snakeDFA_evalFrom_spec]
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

private lemma snakeDFA_stationary (hb : 0 < b) (M : DFA (Fin b) Q) {n : ℕ} (hn : 1 ≤ n)
    (initBuf : Fin n → Fin b) {μ : Q → ℝ} (hμ : IsStationary M μ) :
    IsStationary (snakeDFA M n hn initBuf)
      (fun pu : Q × (Fin n → Fin b) ↦ μ pu.1 / (b : ℝ) ^ n) := by
  classical
  constructor
  · refine ⟨fun pu ↦ div_nonneg (hμ.1.1 pu.1) (by positivity), ?_⟩
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, mul_div_cancel₀ _ (by positivity : (b : ℝ) ^ n ≠ 0), hμ.1.2]
  · rintro ⟨q, w⟩
    have hstep_snake : ∀ pu : Q × (Fin n → Fin b),
        stepProb (snakeDFA M n hn initBuf) 1 pu (q, w) =
          ((Finset.univ.filter fun a : Fin b ↦
            (snakeDFA M n hn initBuf).step pu a = (q, w)).card : ℝ) / b := fun pu ↦ by
      rw [stepProb_succ]
      congr 1
      simp_rw [stepProb_zero]
      convert Finset.sum_boole (fun a : Fin b ↦ (snakeDFA M n hn initBuf).step pu a = (q, w))
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
          (snakeDFA M n hn initBuf).step (p, u) a = (q, w)).card : ℝ) =
        if M.step p (u ⟨0, by omega⟩) = q ∧
            (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j) then 1 else 0 := by
      intro p u
      by_cases hcond : M.step p (u ⟨0, by omega⟩) = q ∧
          (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j)
      · rw [ite_eq_left_iff.2 fun h ↦ absurd hcond h]
        have hsing : (Finset.univ.filter fun a : Fin b ↦
            (snakeDFA M n hn initBuf).step (p, u) a = (q, w)) = {w ⟨n - 1, by omega⟩} := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, snakeDFA,
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
            (snakeDFA M n hn initBuf).step (p, u) a = (q, w)) = ∅ := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            snakeDFA, Prod.mk.injEq, funext_iff]
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
              (snakeDFA M n hn initBuf).step (p, u) a = (q, w)).card : ℝ) / b) =
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

omit [Fintype Q] in
private lemma selectWord_prefix_eq_nth (hb : 0 < b) (M : DFA (Fin b) Q) (x : ℝ)
    (_hinf : (dfaSelectSet b M x).Infinite) (t : ℕ) (_ht : t ∈ dfaSelectSet b M x)
    (n : ℕ) (k : ℕ) (w : Fin k → Fin b)
    (hpre : List.ofFn w <+:
      selectWord M (M.eval (digitPrefix b hb x t))
        (List.ofFn fun j : Fin n ↦ ⟨digit b x (t + j.val), digit_lt hb x _⟩)) :
    open Classical in
    ∀ j : Fin k, dfaSelectSeq b M x (Nat.count (· ∈ dfaSelectSet b M x) t + j.val) = (w j : ℕ) := by
  classical
  -- Relate `selectWord` on `[t, t + n)` to the list of selected digits in `[t, t + n)`
  have hsel_eq : ∀ (m : ℕ),
      selectWord M (M.eval (digitPrefix b hb x t))
        (List.ofFn fun j : Fin m ↦ ⟨digit b x (t + j.val), digit_lt hb x _⟩) =
      List.ofFn fun j : Fin ((Finset.Ico t (t + m)).filter (· ∈ dfaSelectSet b M x)).card ↦
        ⟨dfaSelectSeq b M x (Nat.count (· ∈ dfaSelectSet b M x) t + j.val), digit_lt hb x _⟩ := by
    intro m
    induction m with
    | zero =>
      simp [selectWord]
    | succ m ih =>
      have hlist : (List.ofFn fun j : Fin (m + 1) ↦
            (⟨digit b x (t + j.val), digit_lt hb x _⟩ : Fin b)) =
          (List.ofFn fun j : Fin m ↦ (⟨digit b x (t + j.val), digit_lt hb x _⟩ : Fin b)) ++
          [(⟨digit b x (t + m), digit_lt hb x _⟩ : Fin b)] := by
        rw [List.ofFn_succ', List.concat_eq_append]
        rfl
      rw [hlist, selectWord_append, ih]
      have heval : M.evalFrom (M.eval (digitPrefix b hb x t))
          (List.ofFn fun j : Fin m ↦ ⟨digit b x (t + j.val), digit_lt hb x _⟩) =
          M.eval (digitPrefix b hb x (t + m)) := by
        rw [digitPrefix_add hb x t m, DFA.eval, DFA.evalFrom_of_append]
      rw [heval, selectWord]
      have hmem_iff : M.eval (digitPrefix b hb x (t + m)) ∈ M.accept ↔
          t + m ∈ dfaSelectSet b M x := ⟨fun h ↦ ⟨hb, h⟩, fun ⟨_, h⟩ ↦ h⟩
      have hIco : Finset.Ico t (t + (m + 1)) = insert (t + m) (Finset.Ico t (t + m)) := by
        ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnotmem : t + m ∉ Finset.Ico t (t + m) := by simp
      have hcnt_tm : Nat.count (· ∈ dfaSelectSet b M x) (t + m) =
          Nat.count (· ∈ dfaSelectSet b M x) t +
            ((Finset.Ico t (t + m)).filter (· ∈ dfaSelectSet b M x)).card := by
        rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + m)) := by
          rw [Finset.disjoint_left]; intro i h1 h2; simp at h1 h2; omega
        have hunion : Finset.range (t + m) = Finset.range t ∪ Finset.Ico t (t + m) := by
          ext i; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
        rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint
          (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      by_cases htm : t + m ∈ dfaSelectSet b M x
      · have hacc : M.eval (digitPrefix b hb x (t + m)) ∈ M.accept := hmem_iff.2 htm
        simp only [hacc, ↓reduceIte, selectWord]
        have hcard_succ : ((Finset.Ico t (t + (m + 1))).filter (· ∈ dfaSelectSet b M x)).card =
            ((Finset.Ico t (t + m)).filter (· ∈ dfaSelectSet b M x)).card + 1 := by
          rw [hIco, Finset.filter_insert]
          simp only [htm, ↓reduceIte]
          rw [Finset.card_insert_of_notMem]
          simp [hnotmem]
        apply List.ext_getElem
        · simp [hcard_succ]
        · intro i hi₁ hi₂
          simp only [List.length_append, List.length_ofFn, List.length_singleton] at hi₁
          by_cases hlt : i < ((Finset.Ico t (t + m)).filter (· ∈ dfaSelectSet b M x)).card
          · rw [List.getElem_append_left (by simp [hlt]), List.getElem_ofFn, List.getElem_ofFn]
          · have heqi : i = ((Finset.Ico t (t + m)).filter (· ∈ dfaSelectSet b M x)).card := by
              omega
            rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
            simp only [List.length_ofFn, heqi, Nat.sub_self, List.getElem_singleton]
            apply Fin.ext
            simp only [dfaSelectSeq, ← hcnt_tm, Nat.nth_count htm]
      · have hacc : M.eval (digitPrefix b hb x (t + m)) ∉ M.accept := mt hmem_iff.1 htm
        simp only [hacc, ↓reduceIte, selectWord, List.append_nil]
        have hcard_eq : ((Finset.Ico t (t + (m + 1))).filter (· ∈ dfaSelectSet b M x)).card =
            ((Finset.Ico t (t + m)).filter (· ∈ dfaSelectSet b M x)).card := by
          rw [hIco, Finset.filter_insert]
          simp only [htm, ↓reduceIte]
        apply List.ext_getElem
        · simp [hcard_eq]
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
  rw [hsel_eq n] at hpre
  have hlen : k ≤ ((Finset.Ico t (t + n)).filter (· ∈ dfaSelectSet b M x)).card := by
    have := hpre.length_le
    simpa using this
  obtain ⟨rest, hrest⟩ := hpre
  intro j
  have hget : (List.ofFn w ++ rest)[j.val]'(by simp; omega) =
      (List.ofFn fun i : Fin ((Finset.Ico t (t + n)).filter (· ∈ dfaSelectSet b M x)).card ↦
        (⟨dfaSelectSeq b M x (Nat.count (· ∈ dfaSelectSet b M x) t + i.val),
          digit_lt hb x _⟩ : Fin b))[j.val]'(by simp; omega) := by
    apply Option.some_injective
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hrest]
  rw [List.getElem_append_left (by simp), List.getElem_ofFn, List.getElem_ofFn] at hget
  exact congrArg Fin.val hget.symm

omit [Fintype Q] in
/-- **Agafonov's theorem (strongly connected case)**. -/
private lemma isNormalSeq_dfaSelect_of_stronglyConnected [Finite Q] (hb : 2 ≤ b)
    (M : DFA (Fin b) Q) (hconn : IsStronglyConnected M) (hx : IsNormalIn b x)
    (hinf : (dfaSelectSet b M x).Infinite) :
    IsNormalSeq b (dfaSelectSeq b M x) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hb0 : 0 < b := by omega
  obtain ⟨t₀, ht₀⟩ := hinf.nonempty
  obtain ⟨_, hacc₀⟩ := ht₀
  set q₀ : Q := M.eval (digitPrefix b hb0 x t₀)
  have : Nonempty Q := ⟨q₀⟩
  obtain ⟨μ, hμ, hμ_pos, hces⟩ := exists_unique_stationary_and_tendsto_cesaro hb0 M hconn
  -- Asymptotic selection density `A = ∑_{p ∈ accept} μ p > 0`
  set A : ℝ := ∑ p ∈ Finset.univ.filter (fun p : Q ↦ p ∈ M.accept), μ p
  have hA_pos : 0 < A := by
    calc 0 < μ q₀ := hμ_pos q₀
      _ ≤ A := Finset.single_le_sum (fun p _ ↦ (hμ_pos p).le)
          (Finset.mem_filter.2 ⟨Finset.mem_univ q₀, hacc₀⟩)
  have hs_tendsto : Tendsto (fun T : ℕ ↦ (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ) / T)
      atTop (𝓝 A) := by
    have hcnt_eq : ∀ T, Nat.count (· ∈ dfaSelectSet b M x) T =
        ∑ p ∈ Finset.univ.filter (fun p : Q ↦ p ∈ M.accept), dfaStateCount b hb0 M x p T := by
      intro T
      rw [Nat.count_eq_card_filter_range]
      simp_rw [dfaStateCount]
      rw [← Finset.card_biUnion]
      · refine congrArg Finset.card ?_
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        simp only [dfaSelectSet, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨htT, _, hacc⟩
          exact ⟨M.eval (digitPrefix b hb0 x t), hacc, htT, rfl⟩
        · rintro ⟨p, hp, htT, heq⟩
          exact ⟨htT, hb0, by rwa [heq]⟩
      · intro p₁ _ p₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    have hsum := tendsto_finset_sum_real (Finset.univ.filter (fun p : Q ↦ p ∈ M.accept))
      (fun p T ↦ (dfaStateCount b hb0 M x p T : ℝ) / T) μ
      fun p _ ↦ tendsto_dfa_stateFreq hb M hconn hμ hx p
    refine hsum.congr fun T ↦ ?_
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hcnt_eq T]
  -- Prove block-frequency convergence for every `k` and `w : Fin k → Fin b`
  intro k w
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := min (δ * (b : ℝ) ^ k / 4) (1 / 2)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  obtain ⟨n, hkn, hn1, hshort, hbounds⟩ :=
    card_selectWord_bounds hb M hconn hacc₀ hμ hces k hε
  -- Build the snake automaton driven by `x * b ^ n`
  let initBuf : Fin n → Fin b := fun j ↦ ⟨digit b x j.val, digit_lt hb0 x j.val⟩
  let Ms := snakeDFA M n hn1 initBuf
  have hMs_conn : IsStronglyConnected Ms := snakeDFA_stronglyConnected M hconn hn1 initBuf
  have hMs_stat := snakeDFA_stationary hb0 M hn1 initBuf hμ
  have hxn : IsNormalIn b (x * (b : ℝ) ^ n) := (isNormalIn_mul_pow_iff n).2 hx
  -- Identify the state of `Ms` at time `t` on `x * b ^ n`
  have hMs_state : ∀ t : ℕ,
      Ms.eval (digitPrefix b hb0 (x * (b : ℝ) ^ n) t) =
        (M.eval (digitPrefix b hb0 x t),
          fun j : Fin n ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩) := by
    intro t
    have hspec := snakeDFA_evalFrom_spec M hn1 initBuf M.start initBuf
      (digitPrefix b hb0 (x * (b : ℝ) ^ n) t)
    change (snakeDFA M n hn1 initBuf).evalFrom (M.start, initBuf)
      (digitPrefix b hb0 (x * (b : ℝ) ^ n) t) = _
    rw [hspec]
    have hlist : List.ofFn initBuf ++ digitPrefix b hb0 (x * (b : ℝ) ^ n) t =
        digitPrefix b hb0 x (n + t) := by
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
    have hlen : (digitPrefix b hb0 (x * (b : ℝ) ^ n) t).length = t := by simp [digitPrefix]
    refine Prod.ext ?_ (funext fun j ↦ ?_)
    · dsimp only
      rw [hlist, hlen]
      congr 1
      apply List.ext_getElem
      · simp [digitPrefix]
      · intro i hi₁ hi₂
        simp [digitPrefix]
    · dsimp only
      apply Option.some_injective
      rw [← List.getElem?_eq_getElem, hlist, hlen,
        List.getElem?_eq_getElem (by simp [digitPrefix]; omega)]
      simp [digitPrefix]
  -- Define `goodPairs` (output prefix `w`) and `shortPairs` (output length `< k`)
  let goodPairs : Finset (Q × (Fin n → Fin b)) :=
    Finset.univ.filter fun pu ↦ pu.1 ∈ M.accept ∧ List.ofFn w <+: selectWord M pu.1 (List.ofFn pu.2)
  let shortPairs : Finset (Q × (Fin n → Fin b)) :=
    Finset.univ.filter fun pu ↦ pu.1 ∈ M.accept ∧ (selectWord M pu.1 (List.ofFn pu.2)).length < k
  have hgood_lim : Tendsto (fun T : ℕ ↦
      (∑ pu ∈ goodPairs, (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ)) / T)
      atTop (𝓝 (∑ pu ∈ goodPairs, μ pu.1 / (b : ℝ) ^ n)) := by
    have h := tendsto_finset_sum_real goodPairs
      (fun pu T ↦ (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ) / T)
      (fun pu ↦ μ pu.1 / (b : ℝ) ^ n)
      fun pu _ ↦ tendsto_dfa_stateFreq hb Ms hMs_conn hMs_stat hxn pu
    exact h.congr fun T ↦ (Finset.sum_div _ _ _).symm
  have hshort_lim : Tendsto (fun T : ℕ ↦
      (∑ pu ∈ shortPairs, (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ)) / T)
      atTop (𝓝 (∑ pu ∈ shortPairs, μ pu.1 / (b : ℝ) ^ n)) := by
    have h := tendsto_finset_sum_real shortPairs
      (fun pu T ↦ (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ) / T)
      (fun pu ↦ μ pu.1 / (b : ℝ) ^ n)
      fun pu _ ↦ tendsto_dfa_stateFreq hb Ms hMs_conn hMs_stat hxn pu
    exact h.congr fun T ↦ (Finset.sum_div _ _ _).symm
  -- Evaluate bounds on the limits `Lgood` and `Lshort`
  set Lgood : ℝ := ∑ pu ∈ goodPairs, μ pu.1 / (b : ℝ) ^ n
  set Lshort : ℝ := ∑ pu ∈ shortPairs, μ pu.1 / (b : ℝ) ^ n
  have hLgood_bounds : A * (1 - ε) * ((b : ℝ) ^ k)⁻¹ ≤ Lgood ∧ Lgood ≤ A * ((b : ℝ) ^ k)⁻¹ := by
    have hrewrite : Lgood = ∑ p ∈ Finset.univ.filter (fun p : Q ↦ p ∈ M.accept),
        (μ p / (b : ℝ) ^ n) * (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
          List.ofFn w <+: selectWord M p (List.ofFn u)).card : ℝ) := by
      dsimp only [Lgood, goodPairs]
      rw [Finset.sum_filter]
      have hprod : (∑ pu : Q × (Fin n → Fin b),
          if pu.1 ∈ M.accept ∧ List.ofFn w <+: selectWord M pu.1 (List.ofFn pu.2) then
            μ pu.1 / (b : ℝ) ^ n else 0) =
          ∑ p : Q, if p ∈ M.accept then
            (μ p / (b : ℝ) ^ n) * (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
              List.ofFn w <+: selectWord M p (List.ofFn u)).card : ℝ) else 0 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        by_cases hp : p ∈ M.accept
        · simp only [hp, true_and, ↓reduceIte, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
        · simp [hp]
      rw [hprod, ← Finset.sum_filter]
    have hpow : (b : ℝ) ^ (n - k) / (b : ℝ) ^ n = ((b : ℝ) ^ k)⁻¹ := by
      have : (b : ℝ) ^ n = (b : ℝ) ^ k * (b : ℝ) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      rw [this]
      field_simp [show (b : ℝ) ^ k ≠ 0 by positivity, show (b : ℝ) ^ (n - k) ≠ 0 by positivity]
    rw [hrewrite]
    constructor
    · calc A * (1 - ε) * ((b : ℝ) ^ k)⁻¹
          = ∑ p ∈ Finset.univ.filter (fun p : Q ↦ p ∈ M.accept),
              (μ p / (b : ℝ) ^ n) * ((1 - ε) * (b : ℝ) ^ (n - k)) := by
            rw [← Finset.sum_mul, ← Finset.sum_div]
            have : A / (b : ℝ) ^ n * ((1 - ε) * (b : ℝ) ^ (n - k)) =
                A * (1 - ε) * ((b : ℝ) ^ (n - k) / (b : ℝ) ^ n) := by ring
            rw [this, hpow]
        _ ≤ _ := Finset.sum_le_sum fun p _ ↦
            mul_le_mul_of_nonneg_left (hbounds p w).1 (div_nonneg (hμ_pos p).le (by positivity))
    · calc _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Q ↦ p ∈ M.accept),
              (μ p / (b : ℝ) ^ n) * (b : ℝ) ^ (n - k) :=
            Finset.sum_le_sum fun p _ ↦
              mul_le_mul_of_nonneg_left (hbounds p w).2 (div_nonneg (hμ_pos p).le (by positivity))
        _ = A * ((b : ℝ) ^ k)⁻¹ := by
            rw [← Finset.sum_mul, ← Finset.sum_div]
            have : A / (b : ℝ) ^ n * (b : ℝ) ^ (n - k) =
                A * ((b : ℝ) ^ (n - k) / (b : ℝ) ^ n) := by ring
            rw [this, hpow]
  have hLshort_le : Lshort ≤ A * ε * ((b : ℝ) ^ k)⁻¹ := by
    have hrewrite : Lshort = ∑ p ∈ Finset.univ.filter (fun p : Q ↦ p ∈ M.accept),
        (μ p / (b : ℝ) ^ n) * (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
          (selectWord M p (List.ofFn u)).length < k).card : ℝ) := by
      dsimp only [Lshort, shortPairs]
      rw [Finset.sum_filter]
      have hprod : (∑ pu : Q × (Fin n → Fin b),
          if pu.1 ∈ M.accept ∧ (selectWord M pu.1 (List.ofFn pu.2)).length < k then
            μ pu.1 / (b : ℝ) ^ n else 0) =
          ∑ p : Q, if p ∈ M.accept then
            (μ p / (b : ℝ) ^ n) * (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
              (selectWord M p (List.ofFn u)).length < k).card : ℝ) else 0 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        by_cases hp : p ∈ M.accept
        · simp only [hp, true_and, ↓reduceIte, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
        · simp [hp]
      rw [hprod, ← Finset.sum_filter]
    have hpow : (b : ℝ) ^ (n - k) / (b : ℝ) ^ n = ((b : ℝ) ^ k)⁻¹ := by
      have : (b : ℝ) ^ n = (b : ℝ) ^ k * (b : ℝ) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      rw [this]
      field_simp [show (b : ℝ) ^ k ≠ 0 by positivity, show (b : ℝ) ^ (n - k) ≠ 0 by positivity]
    rw [hrewrite]
    calc _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Q ↦ p ∈ M.accept),
            (μ p / (b : ℝ) ^ n) * (ε * (b : ℝ) ^ (n - k)) :=
          Finset.sum_le_sum fun p _ ↦
            mul_le_mul_of_nonneg_left (hshort p).le (div_nonneg (hμ_pos p).le (by positivity))
      _ = A * ε * ((b : ℝ) ^ k)⁻¹ := by
          rw [← Finset.sum_mul, ← Finset.sum_div]
          have : A / (b : ℝ) ^ n * (ε * (b : ℝ) ^ (n - k)) =
              A * ε * ((b : ℝ) ^ (n - k) / (b : ℝ) ^ n) := by ring
          rw [this, hpow]
  -- Sandwich `blockCount` of the selected sequence at `s(T)` between `goodPairs` and `good + short`
  have hsand : ∀ T : ℕ,
      (∑ pu ∈ goodPairs, dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T) ≤
        ((Finset.range (Nat.count (· ∈ dfaSelectSet b M x) T)).filter fun i ↦
          ∀ j : Fin k, dfaSelectSeq b M x (i + j.val) = (w j : ℕ)).card ∧
      ((Finset.range (Nat.count (· ∈ dfaSelectSet b M x) T)).filter fun i ↦
          ∀ j : Fin k, dfaSelectSeq b M x (i + j.val) = (w j : ℕ)).card ≤
        (∑ pu ∈ goodPairs, dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T) +
        (∑ pu ∈ shortPairs, dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T) := by
    intro T
    have hsum_card : ∀ (S : Finset (Q × (Fin n → Fin b))),
        (∑ pu ∈ S, dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T) =
        ((Finset.range T).filter fun t ↦
          (M.eval (digitPrefix b hb0 x t),
            fun j : Fin n ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩) ∈ S).card := by
      intro S
      simp_rw [dfaStateCount, hMs_state]
      rw [← Finset.card_biUnion]
      · congr 1
        ext t
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨pu, hpu, htT, heq⟩; exact ⟨htT, heq ▸ hpu⟩
        · rintro ⟨htT, hmem⟩; exact ⟨_, hmem, htT, rfl⟩
      · intro pu₁ _ pu₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    rw [hsum_card goodPairs, hsum_card shortPairs]
    -- Bijection between `i < count T` and `t < T` with `t ∈ dfaSelectSet`
    have hbij : ((Finset.range (Nat.count (· ∈ dfaSelectSet b M x) T)).filter fun i ↦
        ∀ j : Fin k, dfaSelectSeq b M x (i + j.val) = (w j : ℕ)).card =
        ((Finset.range T).filter fun t ↦
          t ∈ dfaSelectSet b M x ∧
            ∀ j : Fin k, dfaSelectSeq b M x (Nat.count (· ∈ dfaSelectSet b M x) t + j.val) =
              (w j : ℕ)).card := by
      have hinf_mem : {t : ℕ | t ∈ dfaSelectSet b M x}.Infinite := hinf
      refine Finset.card_nbij' (fun i ↦ Nat.nth (· ∈ dfaSelectSet b M x) i)
        (fun t ↦ Nat.count (· ∈ dfaSelectSet b M x) t) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
        have hmem : Nat.nth (· ∈ dfaSelectSet b M x) i ∈ dfaSelectSet b M x :=
          Nat.nth_mem_of_infinite hinf_mem i
        have hlt : Nat.nth (· ∈ dfaSelectSet b M x) i < T := by
          by_contra! hge
          have hle := Nat.count_monotone (· ∈ dfaSelectSet b M x) hge
          rw [Nat.count_nth_of_infinite hinf_mem] at hle
          omega
        refine ⟨hlt, hmem, ?_⟩
        rw [Nat.count_nth_of_infinite hinf_mem]
        exact hi.2
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht ⊢
        have hlt : Nat.count (· ∈ dfaSelectSet b M x) t < Nat.count (· ∈ dfaSelectSet b M x) T := by
          have h1 : Nat.count (· ∈ dfaSelectSet b M x) (t + 1) ≤
              Nat.count (· ∈ dfaSelectSet b M x) T :=
            Nat.count_monotone _ (by omega)
          rw [Nat.count_succ] at h1
          simp only [ht.2.1, ↓reduceIte] at h1
          omega
        exact ⟨hlt, ht.2.2⟩
      · intro i _; exact Nat.count_nth_of_infinite hinf_mem i
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht
        exact Nat.nth_count ht.2.1
    rw [hbij]
    constructor
    · refine Finset.card_le_card fun t ht ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_range, goodPairs, Finset.mem_univ, true_and] at ht ⊢
      refine ⟨ht.1, ⟨hb0, ht.2.1⟩, ?_⟩
      exact selectWord_prefix_eq_nth hb0 M x hinf t ⟨hb0, ht.2.1⟩ n k w ht.2.2
    · have hsub : ((Finset.range T).filter fun t ↦
          t ∈ dfaSelectSet b M x ∧
            ∀ j : Fin k, dfaSelectSeq b M x (Nat.count (· ∈ dfaSelectSet b M x) t + j.val) =
              (w j : ℕ)) ⊆
          ((Finset.range T).filter fun t ↦
            (M.eval (digitPrefix b hb0 x t),
              fun j : Fin n ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩) ∈ goodPairs) ∪
          ((Finset.range T).filter fun t ↦
            (M.eval (digitPrefix b hb0 x t),
              fun j : Fin n ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩) ∈ shortPairs) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, goodPairs, shortPairs,
          Finset.mem_univ, true_and] at ht ⊢
        obtain ⟨htT, ⟨_, hacc⟩, hmatch⟩ := ht
        by_cases hlen : (selectWord M (M.eval (digitPrefix b hb0 x t))
            (List.ofFn fun j : Fin n ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩)).length < k
        · exact Or.inr ⟨htT, hacc, hlen⟩
        · left
          push Not at hlen
          refine ⟨htT, hacc, ?_⟩
          -- Since output has length `≥ k`, its first `k` digits are `w`!
          set sw := selectWord M (M.eval (digitPrefix b hb0 x t))
            (List.ofFn fun j : Fin n ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩)
          let w' : Fin k → Fin b := fun j ↦ sw[j.val]'(by omega)
          have hpre' : List.ofFn w' <+: sw := by
            refine ⟨sw.drop k, ?_⟩
            have htake : List.ofFn w' = sw.take k := by
              apply List.ext_getElem
              · simp [hlen]
              · intro i hi₁ hi₂; simp [w']
            rw [htake, List.take_append_drop]
          have hmatch' := selectWord_prefix_eq_nth hb0 M x hinf t ⟨hb0, hacc⟩ n k w' hpre'
          have hw_eq : w = w' := funext fun j ↦ Fin.ext ((hmatch j).symm.trans (hmatch' j))
          rw [hw_eq]
          exact hpre'
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  -- Divide the sandwich by `s(T) / T → A` and evaluate at `T = Nat.nth N`
  have hratio_good : Tendsto (fun T : ℕ ↦
      (∑ pu ∈ goodPairs, (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ)) /
        (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ)) atTop (𝓝 (Lgood / A)) := by
    have h := hgood_lim.div hs_tendsto hA_pos.ne'
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : (T : ℝ) ≠ 0 := by positivity
    dsimp only [Pi.div_apply]
    field_simp [hT0]
  have hratio_short : Tendsto (fun T : ℕ ↦
      (∑ pu ∈ shortPairs, (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ)) /
        (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ)) atTop (𝓝 (Lshort / A)) := by
    have h := hshort_lim.div hs_tendsto hA_pos.ne'
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : (T : ℝ) ≠ 0 := by positivity
    dsimp only [Pi.div_apply]
    field_simp [hT0]
  have hgap : (Lgood / A) ∈ Set.Icc ((1 - ε) * ((b : ℝ) ^ k)⁻¹) ((b : ℝ) ^ k)⁻¹ := by
    constructor
    · rw [le_div_iff₀ hA_pos]; linarith [hLgood_bounds.1]
    · rw [div_le_iff₀ hA_pos]; linarith [hLgood_bounds.2]
  have hgap_short : Lshort / A ≤ ε * ((b : ℝ) ^ k)⁻¹ := by
    rw [div_le_iff₀ hA_pos]; linarith
  have hε_bound : ε * ((b : ℝ) ^ k)⁻¹ ≤ δ / 4 := by
    have hle : ε ≤ δ * (b : ℝ) ^ k / 4 := min_le_left _ _
    have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    calc ε * ((b : ℝ) ^ k)⁻¹
        ≤ (δ * (b : ℝ) ^ k / 4) * ((b : ℝ) ^ k)⁻¹ := by gcongr
      _ = δ / 4 := by field_simp [hbk.ne']
  have hevT : ∀ᶠ T : ℕ in atTop,
      |(((Finset.range (Nat.count (· ∈ dfaSelectSet b M x) T)).filter fun i ↦
          ∀ j : Fin k, dfaSelectSeq b M x (i + j.val) = (w j : ℕ)).card : ℝ) /
        (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ) - ((b : ℝ) ^ k)⁻¹| < δ := by
    filter_upwards [Metric.tendsto_nhds.1 hratio_good (δ / 4) (by positivity),
      Metric.tendsto_nhds.1 hratio_short (δ / 4) (by positivity)] with T hTg hTs
    rw [Real.dist_eq, abs_lt] at hTg hTs
    have hlo : (∑ pu ∈ goodPairs, (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ)) /
        (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ) ≤
        (((Finset.range (Nat.count (· ∈ dfaSelectSet b M x) T)).filter fun i ↦
          ∀ j : Fin k, dfaSelectSeq b M x (i + j.val) = (w j : ℕ)).card : ℝ) /
          (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast (hsand T).1
    have hhi : (((Finset.range (Nat.count (· ∈ dfaSelectSet b M x) T)).filter fun i ↦
          ∀ j : Fin k, dfaSelectSeq b M x (i + j.val) = (w j : ℕ)).card : ℝ) /
          (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ) ≤
        (∑ pu ∈ goodPairs, (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ)) /
          (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ) +
        (∑ pu ∈ shortPairs, (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ n) pu T : ℝ)) /
          (Nat.count (· ∈ dfaSelectSet b M x) T : ℝ) := by
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast (hsand T).2
    rw [abs_lt]
    constructor <;> linarith [hgap.1, hgap.2, hgap_short, hε_bound]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hevT
  have hinf_mem : {t : ℕ | t ∈ dfaSelectSet b M x}.Infinite := hinf
  refine ⟨T₀, fun N hN ↦ ?_⟩
  set T : ℕ := Nat.nth (· ∈ dfaSelectSet b M x) N
  have hT_ge : T₀ ≤ T := le_trans hN ((Nat.nth_strictMono hinf_mem).id_le N)
  have hspec := hT₀ T hT_ge
  rw [Nat.count_nth_of_infinite hinf_mem N] at hspec
  simpa [Real.dist_eq] using hspec

/-! ### Reduction to a recurrent strongly connected component (Carton Lemma 8) -/

/-- A state `p` is recurrent if every state reachable from `p` can reach `p` back. -/
private def IsRecurrent (M : DFA (Fin b) Q) (p : Q) : Prop :=
  ∀ q : Q, (∃ u : List (Fin b), M.evalFrom p u = q) → ∃ v : List (Fin b), M.evalFrom q v = p

omit [Fintype Q] in
private lemma isRecurrent_evalFrom (M : DFA (Fin b) Q) {p : Q} (hp : IsRecurrent M p)
    (u : List (Fin b)) : IsRecurrent M (M.evalFrom p u) := by
  intro q ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hp q ⟨u ++ v, by rw [DFA.evalFrom_of_append, hv]⟩
  exact ⟨w ++ u, by rw [DFA.evalFrom_of_append, hw]⟩

omit [Fintype Q] in
private lemma exists_word_isRecurrent [Finite Q] (M : DFA (Fin b) Q) (p : Q) :
    ∃ u : List (Fin b), IsRecurrent M (M.evalFrom p u) := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let reach : Q → Finset Q := fun q ↦
    Finset.univ.filter fun r ↦ ∃ v : List (Fin b), M.evalFrom q v = r
  have hne : (reach p).Nonempty := ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, ⟨[], rfl⟩⟩⟩
  obtain ⟨q, hq_mem, hq_min⟩ := Finset.exists_min_image (reach p) (fun r ↦ (reach r).card) hne
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hq_mem
  obtain ⟨u, rfl⟩ := hq_mem
  refine ⟨u, fun r ⟨v, hv⟩ ↦ ?_⟩
  have hsub : reach r ⊆ reach (M.evalFrom p u) := by
    intro s hs
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    obtain ⟨w, hw⟩ := hs
    exact ⟨v ++ w, by rw [DFA.evalFrom_of_append, hv, hw]⟩
  have hr_mem : r ∈ reach p :=
    Finset.mem_filter.2 ⟨Finset.mem_univ r, ⟨u ++ v, by rw [DFA.evalFrom_of_append, hv]⟩⟩
  have hle : (reach (M.evalFrom p u)).card ≤ (reach r).card := hq_min r hr_mem
  have heq : reach r = reach (M.evalFrom p u) := Finset.eq_of_subset_of_card_le hsub hle
  have hback : M.evalFrom p u ∈ reach r := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨[], rfl⟩⟩
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hback
  exact hback

omit [Fintype Q] in
private lemma exists_universal_recurrent_word [Finite Q] (M : DFA (Fin b) Q) :
    ∃ W : List (Fin b), ∀ p : Q, IsRecurrent M (M.evalFrom p W) := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  suffices h : ∀ S : Finset Q, ∃ W : List (Fin b), ∀ p ∈ S, IsRecurrent M (M.evalFrom p W) by
    obtain ⟨W, hW⟩ := h Finset.univ
    exact ⟨W, fun p ↦ hW p (Finset.mem_univ p)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨[], fun _ h ↦ absurd h (Finset.notMem_empty _)⟩
  | insert p S _ ih =>
    obtain ⟨W₁, hW₁⟩ := ih
    obtain ⟨W₂, hW₂⟩ := exists_word_isRecurrent M (M.evalFrom p W₁)
    refine ⟨W₁ ++ W₂, fun q hq ↦ ?_⟩
    rw [DFA.evalFrom_of_append]
    rcases Finset.mem_insert.1 hq with rfl | hqS
    · exact hW₂
    · exact isRecurrent_evalFrom M (hW₁ q hqS) W₂

private lemma isNormalSeq_shift {d : ℕ → ℕ} (s : ℕ)
    (hd : IsNormalSeq b fun n ↦ d (n + s)) : IsNormalSeq b d := by
  classical
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
    let A := (Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j.val) = (w j : ℕ)
    let B := ((Finset.range N).filter fun i ↦
      ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)).image (· + s)
    have hB : B.card = ((Finset.range N).filter fun i ↦
        ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)).card :=
      Finset.card_image_of_injective _ fun _ _ h ↦ by omega
    have hA_sub : A ⊆ B ∪ Finset.range s := by
      intro i hi
      simp only [A, B, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
        Finset.mem_image] at hi ⊢
      by_cases hlt : i < s
      · exact Or.inr hlt
      · left
        refine ⟨i - s, ⟨by omega, fun j ↦ ?_⟩, by omega⟩
        rw [show i - s + s + j.val = i + j.val by omega]
        exact hi.2 j
    have hB_sub : B ⊆ A ∪ Finset.Ico N (N + s) := by
      intro i hi
      simp only [A, B, Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
        Finset.mem_Ico] at hi ⊢
      obtain ⟨r, ⟨hrN, hr⟩, rfl⟩ := hi
      by_cases hlt : r + s < N
      · exact Or.inl ⟨hlt, hr⟩
      · exact Or.inr ⟨by omega, by omega⟩
    have h1 : A.card ≤ B.card + s :=
      (Finset.card_le_card hA_sub).trans ((Finset.card_union_le _ _).trans (by simp))
    have h2 : B.card ≤ A.card + s :=
      (Finset.card_le_card hB_sub).trans ((Finset.card_union_le _ _).trans (by simp))
    rw [← hB, abs_le]
    have h1R : (A.card : ℝ) ≤ (B.card : ℝ) + s := by exact_mod_cast h1
    have h2R : (B.card : ℝ) ≤ (A.card : ℝ) + s := by exact_mod_cast h2
    constructor <;> linarith
  have hzero : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ ∀ j : Fin k, d (i + j.val) = (w j : ℕ)).card : ℝ) / N -
      (((Finset.range N).filter fun i ↦
          ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ)).card : ℝ) / N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (s : ℝ))
    rw [hdiff N, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (habs_le N) (Nat.cast_nonneg N)
  have hsum := hzero.add hlim
  rw [zero_add] at hsum
  refine hsum.congr fun N ↦ ?_
  have heq : (fun i : ℕ ↦ ∀ j : Fin k, d (i + j.val + s) = (w j : ℕ)) =
      fun i : ℕ ↦ ∀ j : Fin k, d (i + s + j.val) = (w j : ℕ) := by
    funext i
    exact propext (forall_congr' fun j ↦ by rw [add_right_comm])
  simp only [heq, sub_add_cancel]

end Agafonov

/-! ### Main theorems: Agafonov's theorem for DFAs and regular languages -/

/-- **Agafonov's theorem (1968)** for deterministic finite automata (digit sequences):
if `x` is normal in base `b ≥ 2` and a finite DFA `M : DFA (Fin b) Q` selects infinitely many
digits of `x` based on the prefix preceding each digit, then the selected digit sequence is
normal in base `b`. -/
theorem isNormalSeq_dfaSelect {Q : Type*} [Finite Q] (hb : 2 ≤ b) (M : DFA (Fin b) Q)
    (hx : IsNormalIn b x) (hinf : (dfaSelectSet b M x).Infinite) :
    IsNormalSeq b (dfaSelectSeq b M x) := by
  classical
  have hb0 : 0 < b := by omega
  obtain ⟨W, hW⟩ := exists_universal_recurrent_word M
  let wVec : Fin W.length → Fin b := fun j ↦ W[j.val]'j.isLt
  obtain ⟨i₀, hi₀⟩ := hx.isDisjunctiveIn W.length wVec
  set t₀ : ℕ := i₀ + W.length
  set p₀ : Q := M.eval (digitPrefix b hb0 x t₀)
  have hp₀_rec : IsRecurrent M p₀ := by
    have hpre : digitPrefix b hb0 x t₀ = digitPrefix b hb0 x i₀ ++ W := by
      rw [digitPrefix_add hb0 x i₀ W.length]
      congr 1
      apply List.ext_getElem
      · simp
      · intro j hj₁ hj₂
        simp only [List.getElem_ofFn]
        exact Fin.ext (by simpa [wVec] using hi₀ ⟨j, by simpa using hj₁⟩)
    change IsRecurrent M (M.eval (digitPrefix b hb0 x t₀))
    rw [hpre, DFA.eval, DFA.evalFrom_of_append]
    exact hW (M.evalFrom M.start (digitPrefix b hb0 x i₀))
  -- Restrict `M` to the strongly connected recurrent component `C = {q | p₀ ⇝ q}`
  let C : Type _ := {q : Q // ∃ u : List (Fin b), M.evalFrom p₀ u = q}
  have hC_step : ∀ (q : C) (a : Fin b), ∃ u : List (Fin b), M.evalFrom p₀ u = M.step q.val a := by
    rintro ⟨q, u, hu⟩ a
    exact ⟨u ++ [a], by rw [DFA.evalFrom_append_singleton, hu]⟩
  let Mc : DFA (Fin b) C :=
    { step := fun q a ↦ ⟨M.step q.val a, hC_step q a⟩
      start := ⟨p₀, [], rfl⟩
      accept := {q : C | q.val ∈ M.accept} }
  have hMc_eval : ∀ (q : C) (u : List (Fin b)), (Mc.evalFrom q u).val = M.evalFrom q.val u := by
    intro q u
    induction u generalizing q with
    | nil => rfl
    | cons a u ih => exact ih ⟨M.step q.val a, hC_step q a⟩
  have hMc_conn : IsStronglyConnected Mc := by
    rintro ⟨q₁, u₁, hu₁⟩ ⟨q₂, u₂, hu₂⟩
    obtain ⟨v, hv⟩ := hp₀_rec q₁ ⟨u₁, hu₁⟩
    refine ⟨v ++ u₂, Subtype.ext ?_⟩
    rw [hMc_eval, DFA.evalFrom_of_append, hv, hu₂]
  set x' : ℝ := x * (b : ℝ) ^ t₀
  have hx' : IsNormalIn b x' := (isNormalIn_mul_pow_iff t₀).2 hx
  have hpre_shift : ∀ m : ℕ, digitPrefix b hb0 x (t₀ + m) =
      digitPrefix b hb0 x t₀ ++ digitPrefix b hb0 x' m := fun m ↦ by
    rw [digitPrefix_add hb0 x t₀ m]
    congr 1
    apply List.ext_getElem
    · simp [digitPrefix]
    · intro j hj₁ hj₂
      simp only [digitPrefix, List.getElem_ofFn, x']
      apply Fin.ext
      dsimp only
      exact digit_add b x t₀ j
  have hset_shift : ∀ m : ℕ, m ∈ dfaSelectSet b Mc x' ↔ t₀ + m ∈ dfaSelectSet b M x := by
    intro m
    simp only [dfaSelectSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, hm⟩
      refine ⟨hb0, ?_⟩
      rw [hpre_shift m, DFA.eval, DFA.evalFrom_of_append]
      change M.evalFrom p₀ (digitPrefix b hb0 x' m) ∈ M.accept
      rwa [← hMc_eval Mc.start]
    · rintro ⟨_, hm⟩
      refine ⟨hb0, ?_⟩
      rw [hpre_shift m, DFA.eval, DFA.evalFrom_of_append] at hm
      change (Mc.eval (digitPrefix b hb0 x' m)).val ∈ M.accept
      rw [DFA.eval, hMc_eval]
      exact hm
  have hinf' : (dfaSelectSet b Mc x').Infinite := by
    refine Set.Infinite.mono (s := (fun m ↦ t₀ + m) ⁻¹' dfaSelectSet b M x)
      (fun m hm ↦ (hset_shift m).2 hm) ?_
    have hinf_sub : (dfaSelectSet b M x \ Set.Iio t₀).Infinite :=
      hinf.sdiff (Set.finite_Iio t₀)
    have hmap : (fun t ↦ t - t₀) '' (dfaSelectSet b M x \ Set.Iio t₀) ⊆
        (fun m ↦ t₀ + m) ⁻¹' dfaSelectSet b M x := by
      rintro m ⟨t, ⟨ht, hge⟩, rfl⟩
      simp only [Set.mem_preimage]
      simp only [Set.mem_Iio, not_lt] at hge
      rwa [Nat.add_sub_of_le hge]
    refine (hinf_sub.image ?_).mono hmap
    intro t₁ ht₁ t₂ ht₂ heq
    simp only [Set.mem_sdiff, Set.mem_Iio, not_lt] at ht₁ ht₂
    dsimp only at heq
    omega
  have hnorm' : IsNormalSeq b (dfaSelectSeq b Mc x') :=
    isNormalSeq_dfaSelect_of_stronglyConnected hb Mc hMc_conn hx' hinf'
  -- `dfaSelectSeq b Mc x' n = dfaSelectSeq b M x (n + s)` where `s = count t₀`
  set s : ℕ := Nat.count (· ∈ dfaSelectSet b M x) t₀
  have hinf'_mem : {m : ℕ | m ∈ dfaSelectSet b Mc x'}.Infinite := hinf'
  have hnth_shift : ∀ n : ℕ,
      Nat.nth (· ∈ dfaSelectSet b M x) (n + s) = t₀ + Nat.nth (· ∈ dfaSelectSet b Mc x') n := by
    intro n
    have hcnt_eq : ∀ m : ℕ, Nat.count (· ∈ dfaSelectSet b M x) (t₀ + m) =
        s + Nat.count (· ∈ dfaSelectSet b Mc x') m := by
      intro m
      induction m with
      | zero => simp [s]
      | succ m ih =>
        rw [← Nat.add_assoc, Nat.count_succ, Nat.count_succ, ih, hset_shift m]
        split_ifs <;> omega
    have hmem : t₀ + Nat.nth (· ∈ dfaSelectSet b Mc x') n ∈ dfaSelectSet b M x :=
      (hset_shift _).1 (Nat.nth_mem_of_infinite hinf'_mem n)
    have hcnt : Nat.count (· ∈ dfaSelectSet b M x) (t₀ + Nat.nth (· ∈ dfaSelectSet b Mc x') n) =
        n + s := by
      rw [hcnt_eq, Nat.count_nth_of_infinite hinf'_mem n, add_comm]
    rw [← hcnt, Nat.nth_count hmem]
  have hseq_eq : (fun n ↦ dfaSelectSeq b M x (n + s)) = dfaSelectSeq b Mc x' := by
    funext n
    simp only [dfaSelectSeq, hnth_shift n, x', ← digit_add]
  exact isNormalSeq_shift s (hseq_eq.symm ▸ hnorm')

/-- **Agafonov's theorem (1968)** for deterministic finite automata (real numbers):
forming a real number from the digits of a base-`b` normal number selected by a finite DFA
preserves normality in base `b`. -/
theorem isNormalIn_dfaSelect {Q : Type*} [Finite Q] (hb : 2 ≤ b) (M : DFA (Fin b) Q)
    (hx : IsNormalIn b x) (hinf : (dfaSelectSet b M x).Infinite) :
    IsNormalIn b (dfaSelect b M x) := by
  have hb0 : 0 < b := by omega
  simp only [dfaSelect, hb0, ↓reduceDIte]
  exact isNormalIn_ofDigits hb (isNormalSeq_dfaSelect hb M hx hinf)

/-- **Agafonov's theorem (1968)** for regular languages (digit sequences):
if `x` is normal in base `b ≥ 2` and `L : Language (Fin b)` is a regular language selecting
infinitely many digits of `x` by prefix membership, then the selected digit sequence is normal in
base `b`. -/
theorem isNormalSeq_regularSelect (hb : 2 ≤ b) {L : Language (Fin b)} (hL : L.IsRegular)
    (hx : IsNormalIn b x) (hinf : (regularSelectSet b L x).Infinite) :
    IsNormalSeq b (regularSelectSeq b L x) := by
  obtain ⟨Q, _, M, rfl⟩ := hL
  have hset : regularSelectSet b M.accepts x = dfaSelectSet b M x := by
    ext n
    simp only [regularSelectSet, dfaSelectSet, Set.mem_ofPred_eq, DFA.mem_accepts]
  have hseq : regularSelectSeq b M.accepts x = dfaSelectSeq b M x := by
    funext n
    simp only [regularSelectSeq, dfaSelectSeq, hset]
  rw [hseq]
  exact isNormalSeq_dfaSelect hb M hx (hset ▸ hinf)

/-- **Agafonov's theorem (1968)** for regular languages (real numbers). -/
theorem isNormalIn_regularSelect (hb : 2 ≤ b) {L : Language (Fin b)} (hL : L.IsRegular)
    (hx : IsNormalIn b x) (hinf : (regularSelectSet b L x).Infinite) :
    IsNormalIn b (regularSelect b L x) := by
  have hb0 : 0 < b := by omega
  simp only [regularSelect, hb0, ↓reduceDIte]
  exact isNormalIn_ofDigits hb (isNormalSeq_regularSelect hb hL hx hinf)

end Real
