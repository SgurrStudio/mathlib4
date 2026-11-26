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

/-- A real number `ofDigits d` is normal in base `b ≥ 2` if and only if its digit sequence `d` is
normal in base `b`. -/
theorem isNormalIn_ofDigits_iff (hb : 2 ≤ b) (d : ℕ → Fin b) :
    IsNormalIn b (ofDigits d) ↔ IsNormalSeq b fun n ↦ (d n : ℕ) := by
  sorry

/-- Real-number normality of `mealyReal b T x` is equivalent to digit-sequence normality of
`mealySeq b hb0 T x`. -/
theorem isNormalIn_mealyReal_iff {Q : Type*} (hb : 2 ≤ b) (T : MealyTransducer b Q) (x : ℝ) :
    IsNormalIn b (mealyReal b T x) ↔ IsNormalSeq b (mealySeq b (by omega) T x) := by
  sorry

/-- **Sufficiency for arbitrary finite-state Mealy transducers**: if every reachable recurrent
state of `T` is information-lossless, then `T` preserves base-`b` normality (digit sequences). -/
theorem isNormalSeq_mealySeq_of_recurrent_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q)
    (hloss : ∀ p : Q, T.IsReachable p → T.IsRecurrent p → T.IsInformationLosslessAt p)
    (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  sorry

/-- **Information-lossless finite-state Mealy transducers preserve normality (digit sequences)**,
strictly generalizing output-bijective transducers (`Real.isNormalSeq_mealySeq`) to allow
arbitrary finite-delay lossless encodings. -/
theorem isNormalSeq_mealySeq_of_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hloss : T.IsInformationLossless) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  sorry

/-- **Information-lossless finite-state Mealy transducers preserve normality (real numbers)**. -/
theorem isNormalIn_mealyReal_of_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hloss : T.IsInformationLossless) (hx : IsNormalIn b x) :
    IsNormalIn b (mealyReal b T x) := by
  sorry

/-- **Forbidden-word obstruction**: every strongly connected finite-state Mealy transducer that is
not information-lossless admits a finite output word `w` that can *never* be produced from any
starting state. -/
theorem exists_forbiddenWord_of_not_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    (hnot : ¬ T.IsInformationLossless) :
    ∃ (M : ℕ) (w : Fin M → Fin b), ∀ (p : Q) (u : Fin M → Fin b), T.outputWord p u ≠ w := by
  sorry

/-- **Universal failure of strongly connected lossy transducers (digit sequences)**: if `T` is
strongly connected and not information-lossless, then `mealySeq b hb0 T x` is *never* normal in
base `b` (for *any* `x : ℝ`). -/
theorem not_isNormalSeq_mealySeq_of_not_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    (hnot : ¬ T.IsInformationLossless) (x : ℝ) :
    ¬ IsNormalSeq b (mealySeq b (by omega) T x) := by
  sorry

/-- **Universal failure of strongly connected lossy transducers (real numbers)**: if `T` is
strongly connected and not information-lossless, then `mealyReal b T x` is *never* normal in
base `b` (for *any* `x : ℝ`). -/
theorem not_isNormalIn_mealyReal_of_not_isInformationLossless {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA)
    (hnot : ¬ T.IsInformationLossless) (x : ℝ) :
    ¬ IsNormalIn b (mealyReal b T x) := by
  sorry

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
  sorry

/-- **Zero-one dichotomy for strongly connected finite-state Mealy transducers (real numbers)**. -/
theorem mealyReal_preserves_isNormal_iff_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) (hconn : IsStronglyConnected T.toDFA) :
    T.IsInformationLossless ↔
      (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (mealyReal b T x)) ∧
      (∃ x : ℝ, IsNormalIn b x ∧ IsNormalIn b (mealyReal b T x)) := by
  sorry

/-- **Exact characterization for arbitrary finite-state Mealy transducers (digit sequences)**:
an arbitrary (not necessarily strongly connected) finite-state Mealy transducer `T` preserves
base-`b` normality for all `x` if and only if every reachable recurrent state of `T` is
information-lossless. -/
theorem mealySeq_preserves_isNormal_iff_recurrent_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalSeq b (mealySeq b (by omega) T x)) ↔
      (∀ p : Q, T.IsReachable p → T.IsRecurrent p → T.IsInformationLosslessAt p) := by
  sorry

/-- **Exact characterization for arbitrary finite-state Mealy transducers (real numbers)**. -/
theorem mealyReal_preserves_isNormal_iff_recurrent_isInformationLossless {Q : Type*} [Finite Q]
    (hb : 2 ≤ b) (T : MealyTransducer b Q) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (mealyReal b T x)) ↔
      (∀ p : Q, T.IsReachable p → T.IsRecurrent p → T.IsInformationLosslessAt p) := by
  sorry

/-- The 1-step delay transducer is information-lossless. -/
theorem delayMealy_isInformationLossless (init : Fin b) :
    (delayMealy b init).IsInformationLossless := by
  sorry

/-- For `b ≥ 2`, the 1-step delay transducer is *not* output-bijective (`out q` is constant). -/
theorem delayMealy_not_isOutputBijective (hb : 2 ≤ b) (init : Fin b) :
    ¬ (delayMealy b init).IsOutputBijective := by
  sorry

/-- The 1-step delay transducer preserves base-`b` normality (digit sequences), showing that
information-losslessness strictly generalizes output-bijectivity. -/
theorem isNormalSeq_delayMealy (hb : 2 ≤ b) (init : Fin b) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) (delayMealy b init) x) := by
  sorry

/-- The 1-step delay transducer preserves base-`b` normality (real numbers). -/
theorem isNormalIn_delayMealy (hb : 2 ≤ b) (init : Fin b) (hx : IsNormalIn b x) :
    IsNormalIn b (mealyReal b (delayMealy b init) x) := by
  sorry

end Real
