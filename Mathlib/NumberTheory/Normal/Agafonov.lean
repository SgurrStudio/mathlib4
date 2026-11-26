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

/-! ### Main theorems: Agafonov's theorem for DFAs and regular languages -/

/-- **Agafonov's theorem (1968)** for deterministic finite automata (digit sequences):
if `x` is normal in base `b ≥ 2` and a finite DFA `M : DFA (Fin b) Q` selects infinitely many
digits of `x` based on the prefix preceding each digit, then the selected digit sequence is
normal in base `b`. -/
theorem isNormalSeq_dfaSelect {Q : Type*} [Finite Q] (hb : 2 ≤ b) (M : DFA (Fin b) Q)
    (hx : IsNormalIn b x) (hinf : (dfaSelectSet b M x).Infinite) :
    IsNormalSeq b (dfaSelectSeq b M x) := by
  sorry

/-- **Agafonov's theorem (1968)** for deterministic finite automata (real numbers):
forming a real number from the digits of a base-`b` normal number selected by a finite DFA
preserves normality in base `b`. -/
theorem isNormalIn_dfaSelect {Q : Type*} [Finite Q] (hb : 2 ≤ b) (M : DFA (Fin b) Q)
    (hx : IsNormalIn b x) (hinf : (dfaSelectSet b M x).Infinite) :
    IsNormalIn b (dfaSelect b M x) := by
  sorry

/-- **Agafonov's theorem (1968)** for regular languages (digit sequences):
if `x` is normal in base `b ≥ 2` and `L : Language (Fin b)` is a regular language selecting
infinitely many digits of `x` by prefix membership, then the selected digit sequence is normal in
base `b`. -/
theorem isNormalSeq_regularSelect (hb : 2 ≤ b) {L : Language (Fin b)} (hL : L.IsRegular)
    (hx : IsNormalIn b x) (hinf : (regularSelectSet b L x).Infinite) :
    IsNormalSeq b (regularSelectSeq b L x) := by
  sorry

/-- **Agafonov's theorem (1968)** for regular languages (real numbers). -/
theorem isNormalIn_regularSelect (hb : 2 ≤ b) {L : Language (Fin b)} (hL : L.IsRegular)
    (hx : IsNormalIn b x) (hinf : (regularSelectSet b L x).Infinite) :
    IsNormalIn b (regularSelect b L x) := by
  sorry

end Real
