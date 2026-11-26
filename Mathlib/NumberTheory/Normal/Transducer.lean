/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Agafonov

import Mathlib.Data.Nat.Nth

/-!
# Bijective finite-state transducers and sharpness of Agafonov's theorem

We establish two complementary results building on `Mathlib.NumberTheory.Normal.FiniteState` and
`Mathlib.NumberTheory.Normal.Agafonov`:

1. **Output-bijective finite-state transducers (Mealy machines) preserve normality**:
   If `T : Real.MealyTransducer b Q` has a finite state space `Q` and its output map
   `T.out q : Fin b → Fin b` is bijective at every state `q` (a stateful, information-lossless
   stream cipher), then feeding the base-`b` digits of a base-`b` normal number `x` into `T`
   produces a base-`b` normal digit sequence `mealySeq` and real number `mealyReal`.

   This generalizes stateless digit permutations (`BlockCipher.lean`) and right-permutative
   sliding-block codes (`SlidingWindow.lean`) to unbounded-memory stateful transformations,
   including arbitrary finite-state additive stream/autokey ciphers and running prefix sums mod `b`
   (`n ↦ (∑ i ≤ n, digit b x i) % b`).

2. **Sharpness of Agafonov's theorem (non-regular prefix selection destroys normality)**:
   Dropping regularity causes Agafonov's theorem to fail both:
   * for every length-predicate language `L_S = {w | w.length ∈ S}` supported on an infinite
     asymptotic-density-`0` set `S` (in particular squares `{k ^ 2}` and powers of two `{2 ^ k}`,
     yielding direct proofs via Agafonov's theorem that these languages are not regular); and
   * pointwise at *every* base-`b` normal number `x` (there exists a non-regular language `L`
     selecting infinitely many digits of `x`—in fact a set of positive density `b⁻¹`—whose selected
     subsequence is identically `0` and hence not normal).

## Main statements

* `Real.isNormalSeq_mealySeq`, `Real.isNormalIn_mealyReal`: output-bijective finite-state Mealy
  transducers preserve base-`b` normality.
* `Real.isNormalSeq_statefulAddCipher`, `Real.isNormalIn_statefulAddCipher`: finite-state
  additive/autokey stream ciphers preserve normality.
* `Real.isNormalSeq_runningSum`, `Real.isNormalIn_runningSum`: running prefix sums mod `b`
  preserve normality.
* `Real.exists_isNormalIn_not_isNormalSeq_lengthSelect_of_density_zero`,
  `Real.exists_isNormalIn_not_isNormalSeq_sqLengthSelect`,
  `Real.exists_isNormalIn_not_isNormalSeq_powTwoLengthSelect`: non-regular length selection
  destroys normality.
* `Real.not_isRegular_sqLength`, `Real.not_isRegular_powTwoLength`: non-regularity of square-
  and power-of-two-length languages deduced directly from Agafonov's theorem.
* `Real.exists_language_not_isNormalSeq_regularSelect`: pointwise failure of prefix selection at
  every base-`b` normal number when regularity is dropped.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-! ### Finite-state Mealy transducers -/

/-- A deterministic finite-state Mealy transducer over the base-`b` alphabet `Fin b` with state
space `Q`. In state `q` on input digit `a`, it outputs `out q a` and transitions to `step q a`. -/
structure MealyTransducer (b : ℕ) (Q : Type*) where
  /-- State transition function. -/
  step : Q → Fin b → Q
  /-- Initial state. -/
  start : Q
  /-- State-dependent output digit map. -/
  out : Q → Fin b → Fin b

/-- The underlying DFA (with all states accepting) tracking the state of a Mealy transducer. -/
def MealyTransducer.toDFA {Q : Type*} (T : MealyTransducer b Q) : DFA (Fin b) Q where
  step := T.step
  start := T.start
  accept := Set.univ

/-- A Mealy transducer is output-bijective if `T.out q : Fin b → Fin b` is bijective at every
state `q`. -/
def MealyTransducer.IsOutputBijective {Q : Type*} (T : MealyTransducer b Q) : Prop :=
  ∀ q : Q, Function.Bijective (T.out q)

/-- The base-`b` digit sequence output by feeding the base-`b` digits of `x` into `T`. -/
noncomputable def mealySeq (b : ℕ) (hb : 0 < b) {Q : Type*} (T : MealyTransducer b Q)
    (x : ℝ) (n : ℕ) : ℕ :=
  (T.out (T.toDFA.eval (digitPrefix b hb x n)) ⟨digit b x n, digit_lt hb x n⟩ : ℕ)

/-- The real number in `[0, 1)` formed from the base-`b` digits output by `T` on `x`. -/
noncomputable def mealyReal (b : ℕ) {Q : Type*} (T : MealyTransducer b Q) (x : ℝ) : ℝ :=
  if hb : 0 < b then
    ofDigits fun n ↦ T.out (T.toDFA.eval (digitPrefix b hb x n)) ⟨digit b x n, digit_lt hb x n⟩
  else 0

/-- The cumulative running prefix sum mod `b` of the base-`b` digits of `x`:
`runningSumSeq b x n = (∑ i ∈ Finset.range (n + 1), digit b x i) % b`. -/
noncomputable def runningSumSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range (n + 1), digit b x i) % b

/-- The real number in `[0, 1)` formed from the running prefix sums mod `b` of `x`. -/
noncomputable def runningSumReal (b : ℕ) (x : ℝ) : ℝ :=
  if hb : 0 < b then
    ofDigits fun n ↦ (⟨runningSumSeq b x n, Nat.mod_lt _ hb⟩ : Fin b)
  else 0

/-- **Output-bijective finite-state transducers preserve normality (digit sequences)**:
for any finite-state Mealy transducer `T` whose output function `T.out q : Fin b → Fin b` is
bijective at every state `q`, feeding the base-`b` digit expansion of a base-`b` normal number `x`
into `T` yields a base-`b` normal digit sequence `mealySeq b hb0 T x`. -/
theorem isNormalSeq_mealySeq {Q : Type*} [Finite Q] (hb : 2 ≤ b) (T : MealyTransducer b Q)
    (hbij : T.IsOutputBijective) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  sorry

/-- **Output-bijective finite-state transducers preserve normality (real numbers)**. -/
theorem isNormalIn_mealyReal {Q : Type*} [Finite Q] (hb : 2 ≤ b) (T : MealyTransducer b Q)
    (hbij : T.IsOutputBijective) (hx : IsNormalIn b x) :
    IsNormalIn b (mealyReal b T x) := by
  sorry

/-- **Stateful additive / autokey stream ciphers preserve normality**:
for any finite state machine `(Q, step, start)` and keystream function `key : Q → Fin b`, adding
`key q_n` modulo `b` to each digit `d_n` preserves base-`b` normality. -/
theorem isNormalSeq_statefulAddCipher {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (step : Q → Fin b → Q) (start : Q) (key : Q → Fin b) (hx : IsNormalIn b x) :
    letI : NeZero b := ⟨by omega⟩
    let T : MealyTransducer b Q := { step := step, start := start, out := fun q a ↦ a + key q }
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  sorry

/-- **Stateful additive / autokey stream ciphers preserve normality (real numbers)**. -/
theorem isNormalIn_statefulAddCipher {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (step : Q → Fin b → Q) (start : Q) (key : Q → Fin b) (hx : IsNormalIn b x) :
    letI : NeZero b := ⟨by omega⟩
    let T : MealyTransducer b Q := { step := step, start := start, out := fun q a ↦ a + key q }
    IsNormalIn b (mealyReal b T x) := by
  sorry

/-- **Running prefix sums mod `b` preserve normality (digit sequences)**:
the unbounded-memory stateful map `n ↦ (∑ i ∈ Finset.range (n + 1), digit b x i) % b` preserves
base-`b` normality. -/
theorem isNormalSeq_runningSum (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalSeq b (runningSumSeq b x) := by
  sorry

/-- **Running prefix sums mod `b` preserve normality (real numbers)**. -/
theorem isNormalIn_runningSum (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalIn b (runningSumReal b x) := by
  sorry

/-! ### Sharpness of Agafonov's theorem: non-regular prefix selection destroys normality -/

/-- **Sharpness of Agafonov's theorem (general density-zero length languages)**:
for any infinite set `S : Set ℕ` of asymptotic density `0`, the length-predicate language
`L = {w : List (Fin b) | w.length ∈ S}` fails Agafonov's theorem: there exists a base-`b` normal
number `x` for which `regularSelectSet b L x` is infinite (in fact equals `S`), yet
`regularSelectSeq b L x` is identically `0` and hence not normal in base `b`. -/
theorem exists_isNormalIn_not_isNormalSeq_lengthSelect_of_density_zero (hb : 2 ≤ b)
    (S : Set ℕ) [DecidablePred (· ∈ S)] (hinf : S.Infinite)
    (hS : Tendsto (fun N : ℕ ↦ (((Finset.range N).filter (· ∈ S)).card : ℝ) / N) atTop (𝓝 0)) :
    let L : Language (Fin b) := {w | w.length ∈ S}
    ∃ x : ℝ, IsNormalIn b x ∧ (regularSelectSet b L x).Infinite ∧
      ¬ IsNormalSeq b (regularSelectSeq b L x) := by
  sorry

/-- Selecting digits whose preceding prefix has square length destroys normality for some base-`b`
normal number. -/
theorem exists_isNormalIn_not_isNormalSeq_sqLengthSelect (hb : 2 ≤ b) :
    let L : Language (Fin b) := {w | ∃ k : ℕ, w.length = k ^ 2}
    ∃ x : ℝ, IsNormalIn b x ∧ (regularSelectSet b L x).Infinite ∧
      ¬ IsNormalSeq b (regularSelectSeq b L x) := by
  sorry

/-- Direct corollary of Agafonov's theorem: the square-length language
`{w : List (Fin b) | ∃ k, w.length = k ^ 2}` is not regular for any alphabet size `b ≥ 2`. -/
theorem not_isRegular_sqLength (hb : 2 ≤ b) :
    ¬ Language.IsRegular ({w : List (Fin b) | ∃ k : ℕ, w.length = k ^ 2} : Language (Fin b)) := by
  sorry

/-- Selecting digits whose preceding prefix has power-of-two length destroys normality for some
base-`b` normal number. -/
theorem exists_isNormalIn_not_isNormalSeq_powTwoLengthSelect (hb : 2 ≤ b) :
    let L : Language (Fin b) := {w | ∃ k : ℕ, w.length = 2 ^ k}
    ∃ x : ℝ, IsNormalIn b x ∧ (regularSelectSet b L x).Infinite ∧
      ¬ IsNormalSeq b (regularSelectSeq b L x) := by
  sorry

/-- Direct corollary of Agafonov's theorem: the power-of-two-length language
`{w : List (Fin b) | ∃ k, w.length = 2 ^ k}` is not regular for any alphabet size `b ≥ 2`. -/
theorem not_isRegular_powTwoLength (hb : 2 ≤ b) :
    ¬ Language.IsRegular ({w : List (Fin b) | ∃ k : ℕ, w.length = 2 ^ k} : Language (Fin b)) := by
  sorry

/-- **Pointwise sharpness of Agafonov's theorem**: for *every* base-`b` normal number `x`, there
exists a (necessarily non-regular) language `L : Language (Fin b)` selecting infinitely many digits
of `x` whose selected subsequence is identically `0` and hence not normal in base `b`. -/
theorem exists_language_not_isNormalSeq_regularSelect (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ∃ L : Language (Fin b), (regularSelectSet b L x).Infinite ∧
      ¬ IsNormalSeq b (regularSelectSeq b L x) := by
  sorry

end Real
