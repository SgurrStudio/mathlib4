/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Rational

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.NumberTheory.Normal.Borel
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Finite-State Incompressibility and the Schnorr–Stimm / Becher–Heiber Characterization

We formalize variable-length deterministic finite-state transducers (`Real.FSTransducer`) and
establish the **Schnorr–Stimm / Becher–Heiber** characterization of base-`b` normality by
finite-state incompressibility: a real number `x` is normal in base `b ≥ 2` if and only if no
information-lossless finite-state transducer achieves asymptotic compression ratio `< 1` on its
base-`b` digit sequence.

## Main definitions

* `Real.FSTransducer b Q`: a variable-length deterministic finite-state transducer over `Fin b`
  with state space `Q`.
* `Real.FSTransducer.evalState`, `Real.FSTransducer.evalOut`: iterated state transition and
  concatenated output on a finite input word.
* `Real.FSTransducer.outputLenSeq`, `Real.FSTransducer.outputLen`: length of the transducer output
  on the first `N` digits of a sequence or real number.
* `Real.FSTransducer.IsInformationLossless`: no two distinct input words from the same state
  produce both the same ending state and the same output word.
* `Real.blockCompressor`: finite-state block-buffered compressor induced by a fixed-to-variable
  code `φ : (Fin K → Fin b) → List (Fin b)`.

## Main statements

* `Real.finiteStateIncompressible_of_isNormalIn`: every base-`b` normal number is finite-state
  incompressible by any information-lossless finite-state transducer.
* `Real.exists_prefixFree_code`: Kraft's prefix-free code construction.
* `Real.blockCompressor_isInformationLossless`: `blockCompressor` is information-lossless whenever
  its block code is prefix-free and nonempty.
* `Real.isNormalIn_iff_finiteStateIncompressible`: full Schnorr–Stimm / Becher–Heiber
  characterization of base-`b` normality.
* `Real.exists_compresses_rat`: every rational number can be compressed to an arbitrarily small
  asymptotic ratio `ε > 0` by an information-lossless finite-state transducer.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-! ### Variable-length deterministic finite-state transducers -/

/-- A variable-length deterministic finite-state transducer over the base-`b` alphabet `Fin b`
with state space `Q`. On state `q` and input digit `a`, it outputs the list `out q a` and
transitions to `step q a`. -/
structure FSTransducer (b : ℕ) (Q : Type*) where
  /-- State transition function. -/
  step : Q → Fin b → Q
  /-- Variable-length output word produced on a transition. -/
  out : Q → Fin b → List (Fin b)
  /-- Initial state. -/
  start : Q

namespace FSTransducer

variable {Q : Type*}

/-- The state reached by `T` starting from `q` after reading the input word `u`. -/
def evalState (T : FSTransducer b Q) (q : Q) : List (Fin b) → Q
  | [] => q
  | a :: u => T.evalState (T.step q a) u

/-- The concatenated output produced by `T` starting from `q` while reading `u`. -/
def evalOut (T : FSTransducer b Q) (q : Q) : List (Fin b) → List (Fin b)
  | [] => []
  | a :: u => T.out q a ++ T.evalOut (T.step q a) u

@[simp]
theorem evalState_nil (T : FSTransducer b Q) (q : Q) : T.evalState q [] = q := rfl

@[simp]
theorem evalState_cons (T : FSTransducer b Q) (q : Q) (a : Fin b) (u : List (Fin b)) :
    T.evalState q (a :: u) = T.evalState (T.step q a) u := rfl

@[simp]
theorem evalOut_nil (T : FSTransducer b Q) (q : Q) : T.evalOut q [] = [] := rfl

@[simp]
theorem evalOut_cons (T : FSTransducer b Q) (q : Q) (a : Fin b) (u : List (Fin b)) :
    T.evalOut q (a :: u) = T.out q a ++ T.evalOut (T.step q a) u := rfl

theorem evalState_append (T : FSTransducer b Q) (q : Q) (u v : List (Fin b)) :
    T.evalState q (u ++ v) = T.evalState (T.evalState q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih => exact ih (T.step q a)

theorem evalOut_append (T : FSTransducer b Q) (q : Q) (u v : List (Fin b)) :
    T.evalOut q (u ++ v) = T.evalOut q u ++ T.evalOut (T.evalState q u) v := by
  induction u generalizing q with
  | nil => simp
  | cons a u ih => simp [evalOut_cons, evalState_cons, ih, List.append_assoc]

theorem length_evalOut_append (T : FSTransducer b Q) (q : Q) (u v : List (Fin b)) :
    (T.evalOut q (u ++ v)).length =
      (T.evalOut q u).length + (T.evalOut (T.evalState q u) v).length := by
  rw [evalOut_append, List.length_append]

/-- Output length of `T` on the first `N` digits of a base-`b` digit sequence `d`. -/
def outputLenSeq (T : FSTransducer b Q) (d : ℕ → Fin b) (N : ℕ) : ℕ :=
  (T.evalOut T.start (List.ofFn fun i : Fin N ↦ d i)).length

/-- Output length of `T` on the first `N` base-`b` digits of a real number `x`. -/
noncomputable def outputLen (T : FSTransducer b Q) (hb : 0 < b) (x : ℝ) (N : ℕ) : ℕ :=
  T.outputLenSeq (fun i ↦ ⟨digit b x i, digit_lt hb x i⟩) N

/-- `T` is *information-lossless* if no two distinct input words from the same state `p` produce
both the same ending state and the same output word. -/
def IsInformationLossless (T : FSTransducer b Q) : Prop :=
  ∀ (p : Q) (u v : List (Fin b)),
    T.evalState p u = T.evalState p v → T.evalOut p u = T.evalOut p v → u = v

theorem outputLenSeq_mono (T : FSTransducer b Q) (d : ℕ → Fin b) {M N : ℕ} (hMN : M ≤ N) :
    T.outputLenSeq d M ≤ T.outputLenSeq d N := by
  sorry

theorem outputLen_mono (T : FSTransducer b Q) (hb : 0 < b) (x : ℝ) {M N : ℕ} (hMN : M ≤ N) :
    T.outputLen hb x M ≤ T.outputLen hb x N := by
  sorry

end FSTransducer

/-- **Finite-state incompressibility of normal numbers**: if `x` is normal in base `b ≥ 2`,
then every information-lossless finite-state transducer `T` over `Fin b` outputs at least
`(1 - ε) * N` digits on the first `N` digits of `x` for all sufficiently large `N`. -/
theorem finiteStateIncompressible_of_isNormalIn (hb : 2 ≤ b) {Q : Type*} [Fintype Q]
    (T : FSTransducer b Q) (hT : T.IsInformationLossless) (hx : IsNormalIn b x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1 - ε) * (N : ℝ) ≤ (T.outputLen (by omega) x N : ℝ) := by
  sorry

/-- **Kraft's prefix-free code construction**: given positive codeword lengths `L : α → ℕ` on a
finite alphabet `α` satisfying Kraft's inequality `∑ a, b ^ (-(L a : ℝ)) ≤ 1`, there exists a
prefix-free code `φ : α → List (Fin b)` with `(φ a).length = L a` for every `a`. -/
theorem exists_prefixFree_code {b : ℕ} (hb : 2 ≤ b) {α : Type*} [Fintype α]
    (L : α → ℕ) (hL_pos : ∀ a, 1 ≤ L a)
    (hkraft : ∑ a, (b : ℝ) ^ (-(L a : ℝ)) ≤ 1) :
    ∃ φ : α → List (Fin b),
      (∀ a, (φ a).length = L a) ∧
      (∀ a₁ a₂, φ a₁ <+: φ a₂ → a₁ = a₂) := by
  sorry

abbrev BufferState (b K : ℕ) : Type := {s : List (Fin b) // s.length < K}

instance instFintypeBufferState (b K : ℕ) : Fintype (BufferState b K) := by
  let e : BufferState b K ≃ Σ l : Fin K, (Fin l.val → Fin b) :=
    { toFun := fun s ↦ ⟨⟨s.val.length, s.2⟩, fun i ↦ s.val[i.val]⟩
      invFun := fun p ↦ ⟨List.ofFn p.2, by simp⟩
      left_inv := fun ⟨s, hs⟩ ↦ by
        apply Subtype.ext
        apply List.ext_getElem
        · simp
        · intro i h₁ h₂; simp
      right_inv := fun ⟨⟨l, hl⟩, f⟩ ↦ by
        refine Sigma.ext ?_ ?_
        · apply Fin.ext; simp
        · refine Function.hfunext (by simp) fun i j hij ↦ ?_
          have hlen : (List.ofFn f).length = l := List.length_ofFn
          have hij' : i.val = j.val := (Fin.heq_ext_iff hlen).1 hij
          refine heq_of_eq ?_
          simp only [List.getElem_ofFn]
          congr 1
          exact Fin.ext hij' }
  exact Fintype.ofEquiv _ e.symm

/-- The block-buffered finite-state transducer of block size `K ≥ 1` induced by a block code
`φ : (Fin K → Fin b) → List (Fin b)`. It buffers input digits until `K` digits accumulate, then
emits `φ` of the `K`-block and clears its buffer. -/
def blockCompressor (K : ℕ) (hK : 1 ≤ K) (φ : (Fin K → Fin b) → List (Fin b)) :
    FSTransducer b (BufferState b K) where
  step q a :=
    let s' := q.val ++ [a]
    if h : s'.length < K then ⟨s', h⟩ else ⟨[], by simp; omega⟩
  out q a :=
    let s' := q.val ++ [a]
    if h : s'.length < K then []
    else φ fun i : Fin K ↦ s'[i.val]'(by
      have hlen : s'.length = q.val.length + 1 := by simp [s']
      have hq := q.2
      omega)
  start := ⟨[], by simp; omega⟩

/-- A block-buffered compressor induced by a prefix-free code of nonempty codewords is
information-lossless. -/
theorem blockCompressor_isInformationLossless (K : ℕ) (hK : 1 ≤ K)
    (φ : (Fin K → Fin b) → List (Fin b))
    (hnonempty : ∀ w, φ w ≠ [])
    (hpre : ∀ w₁ w₂, φ w₁ <+: φ w₂ → w₁ = w₂) :
    (blockCompressor K hK φ).IsInformationLossless := by
  sorry

/-- Exact output length of `blockCompressor` on a multiple `M * K` of the block length `K`. -/
theorem blockCompressor_outputLenSeq_mul (K : ℕ) (hK : 1 ≤ K)
    (φ : (Fin K → Fin b) → List (Fin b)) (d : ℕ → Fin b) (M : ℕ) :
    (blockCompressor K hK φ).outputLenSeq d (M * K) =
      ∑ j ∈ Finset.range M, (φ fun i : Fin K ↦ d (j * K + i)).length := by
  sorry

/-- **Schnorr–Stimm / Becher–Heiber characterization of normal numbers**:
a real number `x` is normal in base `b ≥ 2` if and only if no information-lossless finite-state
transducer over `Fin b` compresses the base-`b` digit sequence of `x` below ratio `1`. -/
theorem isNormalIn_iff_finiteStateIncompressible (hb : 2 ≤ b) :
    IsNormalIn b x ↔
      ∀ (Q : Type) [Fintype Q] (T : FSTransducer b Q), T.IsInformationLossless →
        ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
          (1 - ε) * (N : ℝ) ≤ (T.outputLen (by omega) x N : ℝ) := by
  sorry

/-- Every rational number can be compressed to an arbitrarily small asymptotic ratio `ε > 0`
by an information-lossless finite-state transducer over `Fin b` (`b ≥ 2`). -/
theorem exists_compresses_rat (hb : 2 ≤ b) (r : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : Type) (_ : Fintype Q) (T : FSTransducer b Q),
      T.IsInformationLossless ∧
      ∀ᶠ N : ℕ in atTop, (T.outputLen (by omega) (r : ℝ) N : ℝ) ≤ ε * (N : ℝ) := by
  sorry

end Real
