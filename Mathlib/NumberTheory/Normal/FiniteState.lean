/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.NumberTheory.Normal.DigitOperations

/-!
# Finite-state Markov ergodicity and DFA state frequencies on normal numbers

We prove the Schnorr–Stimm / Carton state-frequency theorem for strongly connected deterministic
finite automata driven by a base-`b` normal number: if `x : ℝ` is normal in base `b ≥ 2` and
`M : DFA (Fin b) Q` is a strongly connected finite automaton, then the uniform-input Markov chain
on `Q` admits a unique, strictly positive stationary distribution `μ : Q → ℝ`, and the asymptotic
frequency of visits to each state `q : Q` along the digit expansion of `x` converges to `μ q`.

This infrastructure is the main analytic/ergodic engine for Agafonov's theorem
(`Mathlib/NumberTheory/Normal/Agafonov.lean`).

## Main definitions and statements

* `Real.digitPrefix`: the length-`n` prefix of the base-`b` digit expansion of `x`.
* `Real.IsStronglyConnected`: every state of a DFA is reachable from every other state.
* `Real.stepProb`, `Real.probSimplex`, `Real.IsStationary`, `Real.cesaroProb`: transition
  probabilities, the probability simplex, stationary distributions, and Cesàro averages for a
  uniform-input DFA.
* `Real.exists_unique_stationary_and_tendsto_cesaro`: existence and uniqueness of a strictly
  positive stationary distribution `μ` and convergence of Cesàro transition averages to `μ`.
* `Real.card_bad_stateCount_lt`: Carton's Lemma 6 — all but an `ε`-fraction of length-`n` words
  visit every state `q` with frequency within `δ` of `μ q` from every starting state.
* `Real.tendsto_dfa_stateFreq`: visit frequencies of a strongly connected DFA on a base-`b` normal
  number converge to its stationary distribution.

## References

* [O. Carton, *A direct proof of Agafonov's theorem and an extension to shifts of finite type*,
  arXiv:2005.00255][Carton2020]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-! ### Prefix selection definitions -/

/-- The prefix of length `n` of the base-`b` digit sequence of `x`, as a list of `Fin b`. -/
noncomputable def digitPrefix (b : ℕ) (hb : 0 < b) (x : ℝ) (n : ℕ) : List (Fin b) :=
  List.ofFn fun i : Fin n ↦ ⟨digit b x i, digit_lt hb x i⟩

/-! ### Finite Markov chain associated with a strongly connected DFA -/

section Markov

variable {Q : Type*}

/-- A DFA is strongly connected if every state is reachable from every other state. -/
def IsStronglyConnected (M : DFA (Fin b) Q) : Prop :=
  ∀ p q : Q, ∃ w : List (Fin b), M.evalFrom p w = q

/-- `t`-step transition probability from state `p` to state `q` under i.i.d. uniform inputs. -/
noncomputable def stepProb (M : DFA (Fin b) Q) : ℕ → Q → Q → ℝ
  | 0, p, q => open Classical in if p = q then 1 else 0
  | t + 1, p, q => (∑ a : Fin b, stepProb M t (M.step p a) q) / (b : ℝ)

lemma stepProb_zero (M : DFA (Fin b) Q) (p q : Q) :
    stepProb M 0 p q = open Classical in if p = q then 1 else 0 := by
  sorry

lemma stepProb_succ (M : DFA (Fin b) Q) (t : ℕ) (p q : Q) :
    stepProb M (t + 1) p q = (∑ a : Fin b, stepProb M t (M.step p a) q) / (b : ℝ) := by
  sorry

variable [Fintype Q]

/-- The probability simplex on a finite state space `Q`. -/
def probSimplex (Q : Type*) [Fintype Q] : Set (Q → ℝ) :=
  {μ | (∀ q : Q, 0 ≤ μ q) ∧ ∑ q : Q, μ q = 1}

/-- Stationarity of a probability distribution `μ` for the uniform-input Markov chain of `M`. -/
def IsStationary (M : DFA (Fin b) Q) (μ : Q → ℝ) : Prop :=
  μ ∈ probSimplex Q ∧ ∀ q : Q, (∑ p : Q, μ p * stepProb M 1 p q) = μ q

/-- Cesàro average of transition probabilities `(1 / (N + 1)) ∑_{t ≤ N} P^t(p, q)`. -/
noncomputable def cesaroProb (M : DFA (Fin b) Q) (p : Q) (N : ℕ) (q : Q) : ℝ :=
  (∑ t ∈ Finset.range (N + 1), stepProb M t p q) / ((N : ℝ) + 1)

lemma stationary_pos (hb : 0 < b) (M : DFA (Fin b) Q) (hconn : IsStronglyConnected M)
    {μ : Q → ℝ} (hμ : IsStationary M μ) (q : Q) :
    0 < μ q := by
  sorry

lemma exists_unique_stationary_and_tendsto_cesaro (hb : 0 < b) (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M) [Nonempty Q] :
    ∃ μ : Q → ℝ, IsStationary M μ ∧ (∀ q, 0 < μ q) ∧
      (∀ ν, IsStationary M ν → ν = μ) ∧
      ∀ p q : Q, Tendsto (fun N ↦ cesaroProb M p N q) atTop (𝓝 (μ q)) := by
  sorry

/-! ### Second-moment concentration of state visit counts (Carton Lemma 6) -/

/-- Number of positions `t < n` where `M` (starting at `p` and reading `u`) is in state `q`. -/
noncomputable def stateCount (M : DFA (Fin b) Q) (p : Q) {n : ℕ} (u : Fin n → Fin b) (q : Q) : ℕ :=
  open Classical in
  (Finset.univ.filter fun t : Fin n ↦
    M.evalFrom p (List.ofFn fun i : Fin t.val ↦ u ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩) = q).card

/-- Carton Lemma 6: for a strongly connected finite DFA, all but an `ε`-fraction of length-`n`
words visit every state `q` with frequency within `δ` of `μ q` from every starting state `p`. -/
lemma card_bad_stateCount_lt (hb : 0 < b) (M : DFA (Fin b) Q)
    (_hconn : IsStronglyConnected M) [Nonempty Q] {μ : Q → ℝ}
    (hμ : IsStationary M μ)
    (hces : ∀ p q : Q, Tendsto (fun N ↦ cesaroProb M p N q) atTop (𝓝 (μ q)))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, 0 < n →
      (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        ∃ p q : Q, δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ) < ε * (b : ℝ) ^ n := by
  sorry

/-! ### State visit frequency on a normal number (Carton Corollary 7) -/

/-- Number of positions `i < N` at which the DFA `M` (reading base-`b` digits of `x` from `M.start`)
is in state `q`. -/
noncomputable def dfaStateCount (b : ℕ) (hb : 0 < b) (M : DFA (Fin b) Q) (x : ℝ) (q : Q) (N : ℕ) :
    ℕ :=
  open Classical in
  ((Finset.range N).filter fun i ↦ M.eval (digitPrefix b hb x i) = q).card

lemma digitPrefix_add (hb : 0 < b) (x : ℝ) (m k : ℕ) :
    digitPrefix b hb x (m + k) =
      digitPrefix b hb x m ++
        List.ofFn fun i : Fin k ↦ ⟨digit b x (m + i.val), digit_lt hb x _⟩ := by
  sorry

/-- **Schnorr–Stimm / Carton state-frequency theorem**: on a base-`b` normal number `x`, the
asymptotic fraction of prefixes landing in state `q` of a strongly connected finite DFA equals its
stationary probability `μ q`. -/
theorem tendsto_dfa_stateFreq (hb : 2 ≤ b) (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M) {μ : Q → ℝ} (hμ : IsStationary M μ)
    (hx : IsNormalIn b x) (q : Q) :
    Tendsto (fun N : ℕ ↦ (dfaStateCount b (by omega) M x q N : ℝ) / N) atTop (𝓝 (μ q)) := by
  sorry

end Markov

end Real
