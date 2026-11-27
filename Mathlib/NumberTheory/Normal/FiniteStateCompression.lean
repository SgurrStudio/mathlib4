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

private lemma tendsto_finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℕ → ℝ} {L : ι → ℝ}
    (hg : ∀ i ∈ s, Tendsto (g i) atTop (𝓝 (L i))) :
    Tendsto (fun n ↦ ∑ i ∈ s, g i n) atTop (𝓝 (∑ i ∈ s, L i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))

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
  have hsplit : (List.ofFn fun i : Fin N ↦ d i) =
      (List.ofFn fun i : Fin M ↦ d i) ++
        (List.ofFn fun i : Fin (N - M) ↦ d (M + i)) := by
    apply List.ext_getElem
    · simp; omega
    · intro i h₁ h₂
      simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
      split_ifs with hi
      · rfl
      · congr 1; omega
  simp only [outputLenSeq, hsplit, length_evalOut_append]
  exact Nat.le_add_right _ _

theorem outputLen_mono (T : FSTransducer b Q) (hb : 0 < b) (x : ℝ) {M N : ℕ} (hMN : M ≤ N) :
    T.outputLen hb x M ≤ T.outputLen hb x N :=
  T.outputLenSeq_mono _ hMN

end FSTransducer

/-! ### Forward direction: finite-state incompressibility of normal numbers -/

section Forward

private lemma length_evalOut_le_mul {Q : Type*} [Fintype Q] (T : FSTransducer b Q) (p : Q)
    (u : List (Fin b)) :
    (T.evalOut p u).length ≤
      u.length * (Finset.univ.sup fun q : Q ↦ Finset.univ.sup fun a : Fin b ↦ (T.out q a).length)
    := by
  set M := Finset.univ.sup fun q : Q ↦ Finset.univ.sup fun a : Fin b ↦ (T.out q a).length
  induction u generalizing p with
  | nil => simp
  | cons a u ih =>
    simp only [FSTransducer.evalOut_cons, List.length_append, List.length_cons]
    have h1 : (T.out p a).length ≤ M := by
      refine le_trans (Finset.le_sup (f := fun a : Fin b ↦ (T.out p a).length) (Finset.mem_univ a))
        (Finset.le_sup (f := fun q : Q ↦ Finset.univ.sup fun a : Fin b ↦ (T.out q a).length)
          (Finset.mem_univ p))
    have h2 := ih (T.step p a)
    nlinarith

private lemma kraft_sum_minLen_le {Q : Type*} [Fintype Q] (hb : 0 < b)
    (T : FSTransducer b Q) (hT : T.IsInformationLossless) (k : ℕ) :
    let M_out := Finset.univ.sup fun q : Q ↦ Finset.univ.sup fun a : Fin b ↦ (T.out q a).length
    let ℓ : (Fin k → Fin b) → ℕ := fun w ↦
      Finset.univ.inf' (Finset.univ_nonempty_iff.2 ⟨T.start⟩)
        (fun p : Q ↦ (T.evalOut p (List.ofFn w)).length)
    ∑ w : Fin k → Fin b, ((b : ℝ) ^ (ℓ w))⁻¹ ≤
      (Fintype.card Q : ℝ) ^ 2 * (k * M_out + 1) := by
  classical
  intro M_out ℓ
  have hQne : (Finset.univ : Finset Q).Nonempty := Finset.univ_nonempty_iff.2 ⟨T.start⟩
  -- For each `w`, pick a state `p_min w` attaining the minimum output length `ℓ w`.
  have hex : ∀ w : Fin k → Fin b, ∃ p : Q, (T.evalOut p (List.ofFn w)).length = ℓ w := fun w ↦ by
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_inf' hQne
      (fun p : Q ↦ (T.evalOut p (List.ofFn w)).length)
    exact ⟨p, hp.symm⟩
  choose p_min hp_min using hex
  let q_end : (Fin k → Fin b) → Q := fun w ↦ T.evalState (p_min w) (List.ofFn w)
  let tag : (Fin k → Fin b) → (Q × Q) × ℕ := fun w ↦ ((p_min w, q_end w), ℓ w)
  let Tset : Finset ((Q × Q) × ℕ) :=
    (Finset.univ ×ˢ Finset.univ) ×ˢ Finset.range (k * M_out + 1)
  have htag_mem : ∀ w ∈ (Finset.univ : Finset (Fin k → Fin b)), tag w ∈ Tset := fun w _ ↦ by
    refine Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    rw [Finset.mem_range]
    have hle := length_evalOut_le_mul T (p_min w) (List.ofFn w)
    rw [hp_min w, List.length_ofFn] at hle
    exact Nat.lt_succ_of_le hle
  rw [← Finset.sum_fiberwise_of_maps_to htag_mem]
  -- Bound each fiber `((p, q), L)` by `1`.
  have hfiber : ∀ t ∈ Tset,
      ∑ w ∈ Finset.univ.filter (fun w ↦ tag w = t), ((b : ℝ) ^ (ℓ w))⁻¹ ≤ 1 := by
    rintro ⟨⟨p, q⟩, L⟩ _
    set S := Finset.univ.filter fun w : Fin k → Fin b ↦ tag w = ((p, q), L)
    have hcard : S.card ≤ b ^ L := by
      have hinj : Set.InjOn (fun w : Fin k → Fin b ↦
          (fun i : Fin L ↦ if h : i.val < (T.evalOut p (List.ofFn w)).length
            then (T.evalOut p (List.ofFn w))[i.val] else ⟨0, hb⟩)) (S : Set (Fin k → Fin b)) := by
        intro w₁ hw₁ w₂ hw₂ heq
        simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
          tag, Prod.mk.injEq] at hw₁ hw₂
        obtain ⟨⟨hp₁, hq₁⟩, hL₁⟩ := hw₁
        obtain ⟨⟨hp₂, hq₂⟩, hL₂⟩ := hw₂
        have hlen₁ : (T.evalOut p (List.ofFn w₁)).length = L := by rw [← hp₁, hp_min w₁, hL₁]
        have hlen₂ : (T.evalOut p (List.ofFn w₂)).length = L := by rw [← hp₂, hp_min w₂, hL₂]
        have hout : T.evalOut p (List.ofFn w₁) = T.evalOut p (List.ofFn w₂) := by
          apply List.ext_getElem (hlen₁.trans hlen₂.symm)
          intro i hi₁ hi₂
          have hiL : i < L := by omega
          have := congrFun heq ⟨i, hiL⟩
          simp only [hi₁, hi₂, ↓reduceDIte] at this
          exact this
        have hst : T.evalState p (List.ofFn w₁) = T.evalState p (List.ofFn w₂) := by
          calc T.evalState p (List.ofFn w₁)
              = q_end w₁ := by dsimp only [q_end]; rw [hp₁]
            _ = q := hq₁
            _ = q_end w₂ := hq₂.symm
            _ = T.evalState p (List.ofFn w₂) := by dsimp only [q_end]; rw [hp₂]
        exact List.ofFn_injective (hT p _ _ hst hout)
      calc S.card ≤ (Finset.univ : Finset (Fin L → Fin b)).card :=
            Finset.card_le_card_of_injOn _ (fun _ _ ↦ Finset.mem_univ _) hinj
        _ = b ^ L := by simp
    have hsum : ∑ w ∈ S, ((b : ℝ) ^ (ℓ w))⁻¹ = (S.card : ℝ) * ((b : ℝ) ^ L)⁻¹ := by
      have hconst : ∀ w ∈ S, ((b : ℝ) ^ (ℓ w))⁻¹ = ((b : ℝ) ^ L)⁻¹ := fun w hw ↦ by
        simp only [S, Finset.mem_filter, tag, Prod.mk.injEq] at hw
        rw [hw.2.2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    calc (S.card : ℝ) * ((b : ℝ) ^ L)⁻¹ ≤ ((b : ℝ) ^ L) * ((b : ℝ) ^ L)⁻¹ := by
          gcongr; exact_mod_cast hcard
      _ = 1 := mul_inv_cancel₀ hbL.ne'
  calc ∑ t ∈ Tset, ∑ w ∈ Finset.univ.filter (fun w ↦ tag w = t), ((b : ℝ) ^ (ℓ w))⁻¹
      ≤ ∑ _t ∈ Tset, (1 : ℝ) := Finset.sum_le_sum hfiber
    _ = (Tset.card : ℝ) := by simp
    _ = (Fintype.card Q : ℝ) ^ 2 * (k * M_out + 1) := by
        simp only [Tset, Finset.card_product, Finset.card_univ, Finset.card_range]
        push_cast; ring

private lemma avg_minLen_lower_bound {Q : Type*} [Fintype Q] (hb : 2 ≤ b)
    (T : FSTransducer b Q) (hT : T.IsInformationLossless) {k : ℕ} (hk : 0 < k) :
    let M_out := Finset.univ.sup fun q : Q ↦ Finset.univ.sup fun a : Fin b ↦ (T.out q a).length
    let C : ℝ := (Fintype.card Q : ℝ) ^ 2 * (k * M_out + 1)
    let ℓ : (Fin k → Fin b) → ℕ := fun w ↦
      Finset.univ.inf' (Finset.univ_nonempty_iff.2 ⟨T.start⟩)
        (fun p : Q ↦ (T.evalOut p (List.ofFn w)).length)
    1 - Real.log C / ((k : ℝ) * Real.log b) ≤
      (1 / (k : ℝ)) * ((b : ℝ) ^ k)⁻¹ * ∑ w : Fin k → Fin b, (ℓ w : ℝ) := by
  intro M_out C ℓ
  have hb0 : 0 < b := by omega
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hbk_pos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have hQ_pos : 0 < Fintype.card Q := Fintype.card_pos_iff.2 ⟨T.start⟩
  have hC_pos : 0 < C := by positivity
  -- Apply Jensen's inequality to `Real.convexOn_exp`.
  let μ : (Fin k → Fin b) → ℝ := fun _ ↦ ((b : ℝ) ^ k)⁻¹
  let y : (Fin k → Fin b) → ℝ := fun w ↦ -(ℓ w : ℝ) * Real.log b
  have hμ_nonneg : ∀ w ∈ (Finset.univ : Finset (Fin k → Fin b)), 0 ≤ μ w := fun _ _ ↦ by
    dsimp only [μ]; positivity
  have hμ_sum : ∑ w ∈ (Finset.univ : Finset (Fin k → Fin b)), μ w = 1 := by
    simp only [μ, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    exact mul_inv_cancel₀ hbk_pos.ne'
  have hjensen := convexOn_exp.map_sum_le hμ_nonneg hμ_sum (fun _ _ ↦ Set.mem_univ _) (p := y)
  -- Identify `Real.exp (y w) = ((b : ℝ) ^ (ℓ w))⁻¹`.
  have hexp_y : ∀ w : Fin k → Fin b, Real.exp (y w) = ((b : ℝ) ^ (ℓ w))⁻¹ := fun w ↦ by
    dsimp only [y]
    rw [neg_mul, Real.exp_neg, Real.exp_natCast_mul, Real.exp_log (by positivity : (0 : ℝ) < b)]
  have hkraft := kraft_sum_minLen_le hb0 T hT k
  have hrhs : ∑ w : Fin k → Fin b, μ w * Real.exp (y w) ≤ ((b : ℝ) ^ k)⁻¹ * C := by
    simp_rw [hexp_y, μ, ← Finset.mul_sum]
    gcongr
  have hexp_le : Real.exp (∑ w : Fin k → Fin b, μ w * y w) ≤ ((b : ℝ) ^ k)⁻¹ * C :=
    hjensen.trans hrhs
  have hlog_le : ∑ w : Fin k → Fin b, μ w * y w ≤ Real.log (((b : ℝ) ^ k)⁻¹ * C) := by
    have := Real.log_le_log (Real.exp_pos _) hexp_le
    rwa [Real.log_exp] at this
  have hlog_rhs : Real.log (((b : ℝ) ^ k)⁻¹ * C) = -(k : ℝ) * Real.log b + Real.log C := by
    rw [Real.log_mul (inv_ne_zero hbk_pos.ne') hC_pos.ne', Real.log_inv, Real.log_pow]
    ring
  have hsum_lhs : ∑ w : Fin k → Fin b, μ w * y w =
      -(((b : ℝ) ^ k)⁻¹ * ∑ w : Fin k → Fin b, (ℓ w : ℝ)) * Real.log b := by
    simp only [μ, y]
    rw [← Finset.mul_sum]
    have : ∀ w : Fin k → Fin b, -(ℓ w : ℝ) * Real.log b = (ℓ w : ℝ) * (-Real.log b) :=
      fun _ ↦ by ring
    simp_rw [this, ← Finset.sum_mul]
    ring
  rw [hsum_lhs, hlog_rhs] at hlog_le
  have hklog : 0 < (k : ℝ) * Real.log b := mul_pos hk_pos hlogb
  refine le_of_mul_le_mul_right ?_ hklog
  have h1 : (1 - Real.log C / ((k : ℝ) * Real.log b)) * ((k : ℝ) * Real.log b) =
      (k : ℝ) * Real.log b - Real.log C := by field_simp
  have h2 : (1 / (k : ℝ) * ((b : ℝ) ^ k)⁻¹ * ∑ w : Fin k → Fin b, (ℓ w : ℝ)) *
      ((k : ℝ) * Real.log b) =
      (((b : ℝ) ^ k)⁻¹ * ∑ w : Fin k → Fin b, (ℓ w : ℝ)) * Real.log b := by field_simp
  linarith

private lemma outputLenSeq_mul_ge_sum_minLen {Q : Type*} [Fintype Q]
    (T : FSTransducer b Q) (d : ℕ → Fin b) (k M : ℕ) :
    let ℓ : (Fin k → Fin b) → ℕ := fun w ↦
      Finset.univ.inf' (Finset.univ_nonempty_iff.2 ⟨T.start⟩)
        (fun p : Q ↦ (T.evalOut p (List.ofFn w)).length)
    ∑ j ∈ Finset.range M, ℓ (fun i : Fin k ↦ d (j * k + i)) ≤ T.outputLenSeq d (M * k) := by
  intro ℓ
  induction M with
  | zero => simp [FSTransducer.outputLenSeq]
  | succ M ih =>
    have hsplit : (List.ofFn fun i : Fin ((M + 1) * k) ↦ d i) =
        (List.ofFn fun i : Fin (M * k) ↦ d i) ++
          (List.ofFn fun i : Fin k ↦ d (M * k + i)) := by
      apply List.ext_getElem
      · simp; ring
      · intro i h₁ h₂
        simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
        split_ifs with hi
        · rfl
        · congr 1; omega
    rw [Finset.sum_range_succ, FSTransducer.outputLenSeq, hsplit,
      FSTransducer.length_evalOut_append]
    have hmin : ℓ (fun i : Fin k ↦ d (M * k + i)) ≤
        (T.evalOut (T.evalState T.start (List.ofFn fun i : Fin (M * k) ↦ d i))
          (List.ofFn fun i : Fin k ↦ d (M * k + i))).length :=
      Finset.inf'_le _ (Finset.mem_univ _)
    exact Nat.add_le_add ih hmin

private lemma exists_nat_log_div_lt (hb : 2 ≤ b) (A : ℝ) (hA : 0 < A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 0 < k ∧ Real.log (A * (k : ℝ)) / ((k : ℝ) * Real.log b) < δ := by
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  have h1 : Tendsto (fun k : ℕ ↦ Real.log A / ((k : ℝ) * Real.log b)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log A / Real.log b)).congr fun _ ↦ by ring
  have h2 : Tendsto (fun k : ℕ ↦ 2 / (Real.sqrt (k : ℝ) * Real.log b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const hlogb)
  have hsum : Tendsto (fun k : ℕ ↦
      Real.log A / ((k : ℝ) * Real.log b) + 2 / (Real.sqrt (k : ℝ) * Real.log b))
      atTop (𝓝 0) := by simpa using h1.add h2
  obtain ⟨k, hk0, hbound⟩ := ((eventually_gt_atTop 0).and (hsum.eventually (gt_mem_nhds hδ))).exists
  refine ⟨k, hk0, ?_⟩
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hsq_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hk_pos
  have hlogk : Real.log (k : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
    calc Real.log (k : ℝ) = Real.log ((Real.sqrt (k : ℝ)) ^ 2) := by rw [Real.sq_sqrt hk_pos.le]
      _ = 2 * Real.log (Real.sqrt (k : ℝ)) := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * (Real.sqrt (k : ℝ) - 1) := by gcongr; exact Real.log_le_sub_one_of_pos hsq_pos
      _ ≤ 2 * Real.sqrt (k : ℝ) := by linarith
  calc Real.log (A * (k : ℝ)) / ((k : ℝ) * Real.log b)
      = Real.log A / ((k : ℝ) * Real.log b) + Real.log (k : ℝ) / ((k : ℝ) * Real.log b) := by
        rw [Real.log_mul hA.ne' hk_pos.ne', add_div]
    _ ≤ Real.log A / ((k : ℝ) * Real.log b) +
          (2 * Real.sqrt (k : ℝ)) / ((k : ℝ) * Real.log b) := by gcongr
    _ = Real.log A / ((k : ℝ) * Real.log b) + 2 / (Real.sqrt (k : ℝ) * Real.log b) := by
        congr 1; rw [div_eq_div_iff (by positivity) (by positivity)]
        nlinarith [Real.mul_self_sqrt hk_pos.le]
    _ < δ := hbound

/-- **Finite-state incompressibility of normal numbers**: if `x` is normal in base `b ≥ 2`,
then every information-lossless finite-state transducer `T` over `Fin b` outputs at least
`(1 - ε) * N` digits on the first `N` digits of `x` for all sufficiently large `N`. -/
theorem finiteStateIncompressible_of_isNormalIn (hb : 2 ≤ b) {Q : Type*} [Finite Q]
    (T : FSTransducer b Q) (hT : T.IsInformationLossless) (hx : IsNormalIn b x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1 - ε) * (N : ℝ) ≤ (T.outputLen (by omega) x N : ℝ) := by
  classical
  have := Fintype.ofFinite Q
  have hb0 : 0 < b := by omega
  set M_out := Finset.univ.sup fun q : Q ↦ Finset.univ.sup fun a : Fin b ↦ (T.out q a).length
  have hQ_pos : 0 < Fintype.card Q := Fintype.card_pos_iff.2 ⟨T.start⟩
  set A : ℝ := (Fintype.card Q : ℝ) ^ 2 * (M_out + 1)
  have hA : 0 < A := by positivity
  obtain ⟨k, hk, hk_log⟩ := exists_nat_log_div_lt hb A hA (show 0 < ε / 2 by positivity)
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  set ℓ : (Fin k → Fin b) → ℕ := fun w ↦
    Finset.univ.inf' (Finset.univ_nonempty_iff.2 ⟨T.start⟩)
      (fun p : Q ↦ (T.evalOut p (List.ofFn w)).length)
  -- Jensen lower bound on the average minimum length `L_avg`.
  set L_avg : ℝ := (1 / (k : ℝ)) * ((b : ℝ) ^ k)⁻¹ * ∑ w : Fin k → Fin b, (ℓ w : ℝ)
  have hL_avg : 1 - ε / 2 < L_avg := by
    have hjb := avg_minLen_lower_bound hb T hT hk
    have hCle : (Fintype.card Q : ℝ) ^ 2 * (k * M_out + 1) ≤ A * (k : ℝ) := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      dsimp only [A]
      nlinarith [sq_nonneg (Fintype.card Q : ℝ)]
    have hlog_le : Real.log ((Fintype.card Q : ℝ) ^ 2 * (k * M_out + 1)) /
        ((k : ℝ) * Real.log b) ≤ Real.log (A * (k : ℝ)) / ((k : ℝ) * Real.log b) := by
      gcongr
    linarith
  -- By `IsNormalIn.pow`, every aligned `k`-block occurs with frequency `b⁻ᵏ`.
  have hpow : IsNormalIn (b ^ k) x := hx.pow hb hk
  have hsimp : IsSimplyNormalIn (b ^ k) x := hpow.isSimplyNormalIn
  let d : ℕ → Fin b := fun i ↦ ⟨digit b x i, digit_lt hb0 x i⟩
  let blk : ℕ → Fin k → Fin b := fun j i ↦ d (j * k + i)
  have hcount_eq : ∀ (w : Fin k → Fin b) (M : ℕ),
      ((Finset.range M).filter fun j ↦ blk j = w).card =
        blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) M := fun w M ↦ by
    unfold blockCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Fin.forall_fin_one, Fin.val_zero, add_zero]
    refine and_congr_right fun _ ↦ ?_
    have hiff := forall_digit_eq_iff_digit_pow (x := x) hb0 w 0 j
    simp only [zero_add, pow_zero, mul_one] at hiff
    rw [← hiff]
    constructor
    · intro h i
      have := congrArg Fin.val (congrFun h i)
      exact this
    · intro h
      funext i
      exact Fin.ext (h i)
  -- The aligned-block lower bound divided by `N` tends to `L_avg`.
  have hM_tendsto : Tendsto (fun N : ℕ ↦ N / k) atTop atTop :=
    Nat.tendsto_div_const_atTop hk.ne'
  have hMk_div : Tendsto (fun N : ℕ ↦ ((N / k : ℕ) : ℝ) * k / N) atTop (𝓝 1) := by
    have hlow : ∀ᶠ N : ℕ in atTop, 1 - (k : ℝ) / N ≤ ((N / k : ℕ) : ℝ) * k / N := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hdiv : N < (N / k + 1) * k := by
        have := Nat.div_add_mod N k
        have := Nat.mod_lt N hk
        nlinarith
      have hdiv' : (N : ℝ) ≤ ((N / k : ℕ) : ℝ) * k + k := by
        have : (N : ℝ) < ((N / k + 1 : ℕ) : ℝ) * k := by exact_mod_cast hdiv
        push_cast at this; linarith
      rw [le_div_iff₀ hN', sub_mul, one_mul, div_mul_cancel₀ _ hN'.ne']
      linarith
    have hhigh : ∀ᶠ N : ℕ in atTop, ((N / k : ℕ) : ℝ) * k / N ≤ 1 := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_one hN']
      have : (N / k) * k ≤ N := Nat.div_mul_le_self N k
      exact_mod_cast this
    have hlim_low : Tendsto (fun N : ℕ ↦ 1 - (k : ℝ) / N) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_low tendsto_const_nhds hlow hhigh
  have hsum_tendsto : Tendsto (fun N : ℕ ↦
      ∑ w : Fin k → Fin b,
        ((blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) (N / k) : ℝ) / (N / k : ℕ)) *
          (ℓ w : ℝ))
      atTop (𝓝 (((b : ℝ) ^ k)⁻¹ * ∑ w : Fin k → Fin b, (ℓ w : ℝ))) := by
    have hterm : ∀ w : Fin k → Fin b,
        Tendsto (fun N : ℕ ↦
          ((blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) (N / k) : ℝ) / (N / k : ℕ)) *
            (ℓ w : ℝ))
          atTop (𝓝 (((b : ℝ) ^ k)⁻¹ * (ℓ w : ℝ))) := fun w ↦ by
      have ht := (hsimp (blockCode w)).comp hM_tendsto
      have hcast : (((b ^ k : ℕ) : ℝ))⁻¹ = ((b : ℝ) ^ k)⁻¹ := by push_cast; rfl
      rw [hcast] at ht
      exact ht.mul_const (ℓ w : ℝ)
    simpa only [Finset.mul_sum] using tendsto_finset_sum Finset.univ (fun w _ ↦ hterm w)
  have hlower_tendsto : Tendsto (fun N : ℕ ↦
      (1 / (k : ℝ)) * (((N / k : ℕ) : ℝ) * k / N) *
        ∑ w : Fin k → Fin b,
          ((blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) (N / k) : ℝ) / (N / k : ℕ)) *
            (ℓ w : ℝ))
      atTop (𝓝 L_avg) := by
    have := ((tendsto_const_nhds (x := (1 / (k : ℝ))).mul hMk_div).mul hsum_tendsto)
    simpa [L_avg, mul_assoc] using this
  filter_upwards [hlower_tendsto.eventually (lt_mem_nhds (show 1 - ε < L_avg by linarith)),
    eventually_ge_atTop k] with N hN hNk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hk.trans_le hNk
  have hM0 : (0 : ℝ) < (N / k : ℕ) := by
    exact_mod_cast Nat.div_pos hNk hk
  -- Relate the sum expression to `outputLen`.
  have hsum_eq : (∑ j ∈ Finset.range (N / k), (ℓ (blk j) : ℝ)) =
      ∑ w : Fin k → Fin b,
        (blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) (N / k) : ℝ) * (ℓ w : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := blk) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hconst : ∀ j ∈ (Finset.range (N / k)).filter (fun j ↦ blk j = w),
        (ℓ (blk j) : ℝ) = (ℓ w : ℝ) := fun j hj ↦ by
      rw [(Finset.mem_filter.1 hj).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcount_eq]
  have hle_out : (∑ j ∈ Finset.range (N / k), (ℓ (blk j) : ℝ)) ≤
      (T.outputLen hb0 x N : ℝ) := by
    have h1 : ∑ j ∈ Finset.range (N / k), ℓ (blk j) ≤ T.outputLenSeq d ((N / k) * k) :=
      outputLenSeq_mul_ge_sum_minLen T d k (N / k)
    have h2 : T.outputLenSeq d ((N / k) * k) ≤ T.outputLen hb0 x N :=
      T.outputLenSeq_mono d (Nat.div_mul_le_self N k)
    exact_mod_cast h1.trans h2
  have hrew : (1 / (k : ℝ)) * (((N / k : ℕ) : ℝ) * k / N) *
      (∑ w : Fin k → Fin b,
        ((blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) (N / k) : ℝ) / (N / k : ℕ)) *
          (ℓ w : ℝ)) =
      (∑ j ∈ Finset.range (N / k), (ℓ (blk j) : ℝ)) / N := by
    rw [hsum_eq]
    have hdiv_sum : ∑ w : Fin k → Fin b,
        ((blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) (N / k) : ℝ) / (N / k : ℕ)) *
          (ℓ w : ℝ) =
        (∑ w : Fin k → Fin b,
          (blockCount (b ^ k) x (fun _ : Fin 1 ↦ blockCode w) (N / k) : ℝ) * (ℓ w : ℝ)) /
            (N / k : ℕ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun w _ ↦ by ring
    rw [hdiv_sum]
    field_simp
  rw [hrew, lt_div_iff₀ hN0] at hN
  exact hN.le.trans hle_out

end Forward

/-! ### Kraft prefix-free code construction -/

section Kraft

private lemma exists_sorted_equiv {α : Type*} [Fintype α] (L : α → ℕ) :
    ∃ e : Fin (Fintype.card α) ≃ α, Monotone (L ∘ e) := by
  let e₀ := (Fintype.equivFin α).symm
  exact ⟨(Tuple.sort (L ∘ e₀)).trans e₀, Tuple.monotone_sort (L ∘ e₀)⟩

/-- Base-`b` digit list of length `L` representing `c < b ^ L` (most significant digit first). -/
private def natToDigits (b : ℕ) (hb : 0 < b) (L c : ℕ) : List (Fin b) :=
  List.ofFn fun t : Fin L ↦ ⟨c / b ^ (L - 1 - t) % b, Nat.mod_lt _ hb⟩

private lemma natToDigits_prefix_iff (hb : 0 < b) {L₁ L₂ c₁ c₂ : ℕ}
    (hc₁ : c₁ < b ^ L₁) (hc₂ : c₂ < b ^ L₂)
    (hpre : natToDigits b hb L₁ c₁ <+: natToDigits b hb L₂ c₂) :
    L₁ ≤ L₂ ∧ c₂ / b ^ (L₂ - L₁) = c₁ := by
  have hlen : L₁ ≤ L₂ := by
    have := hpre.length_le
    simpa [natToDigits] using this
  refine ⟨hlen, ?_⟩
  have hlt_div : c₂ / b ^ (L₂ - L₁) < b ^ L₁ := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hb _), ← pow_add, show L₁ + (L₂ - L₁) = L₂ by omega]
    exact hc₂
  let w : Fin L₁ → Fin b := fun t ↦ ⟨c₁ / b ^ (L₁ - 1 - t) % b, Nat.mod_lt _ hb⟩
  have hw₁ : c₁ % b ^ L₁ = blockCode w :=
    (forall_div_pow_mod_eq_iff hb c₁ w).1 (fun _ ↦ rfl)
  have hw₂ : (c₂ / b ^ (L₂ - L₁)) % b ^ L₁ = blockCode w := by
    refine (forall_div_pow_mod_eq_iff hb (c₂ / b ^ (L₂ - L₁)) w).1 fun t ↦ ?_
    obtain ⟨rest, hrest⟩ := hpre
    have hget : (natToDigits b hb L₁ c₁)[t.val]'(by simp [natToDigits]) =
        (natToDigits b hb L₂ c₂)[t.val]'(by simp [natToDigits]; omega) := by
      have h1 : (natToDigits b hb L₁ c₁)[t.val]'(by simp [natToDigits]) =
          (natToDigits b hb L₁ c₁ ++ rest)[t.val]'(by simp [natToDigits]; omega) :=
        (List.getElem_append_left (by simp [natToDigits])).symm
      rw [h1]
      congr 1
    simp only [natToDigits, List.getElem_ofFn, Fin.mk.injEq] at hget
    rw [Nat.div_div_eq_div_mul, ← pow_add, show L₂ - L₁ + (L₁ - 1 - t.val) = L₂ - 1 - t.val by
      omega]
    exact hget.symm
  rw [Nat.mod_eq_of_lt hc₁] at hw₁
  rw [Nat.mod_eq_of_lt hlt_div] at hw₂
  exact hw₂.trans hw₁.symm

/-- **Kraft's prefix-free code construction**: given positive codeword lengths `L : α → ℕ` on a
finite alphabet `α` satisfying Kraft's inequality `∑ a, b ^ (-(L a : ℝ)) ≤ 1`, there exists a
prefix-free code `φ : α → List (Fin b)` with `(φ a).length = L a` for every `a`. -/
theorem exists_prefixFree_code {b : ℕ} (hb : 2 ≤ b) {α : Type*} [Fintype α]
    (L : α → ℕ) (hL_pos : ∀ a, 1 ≤ L a)
    (hkraft : ∑ a, (b : ℝ) ^ (-(L a : ℝ)) ≤ 1) :
    ∃ φ : α → List (Fin b),
      (∀ a, (φ a).length = L a) ∧
      (∀ a₁ a₂, φ a₁ <+: φ a₂ → a₁ = a₂) := by
  classical
  have _ := hL_pos
  have hb0 : 0 < b := by omega
  obtain ⟨e, he⟩ := exists_sorted_equiv L
  let n := Fintype.card α
  let Ls : Fin n → ℕ := L ∘ e
  have hLs_mono : Monotone Ls := he
  set M : ℕ := Finset.univ.sup Ls
  have hle_M : ∀ i : Fin n, Ls i ≤ M := fun i ↦ Finset.le_sup (Finset.mem_univ i)
  -- Translate Kraft's inequality into natural numbers at precision `M`.
  have hkraft_nat : ∑ i : Fin n, b ^ (M - Ls i) ≤ b ^ M := by
    have hkraft' : ∑ i : Fin n, (b : ℝ) ^ (-(Ls i : ℝ)) ≤ 1 := by
      rw [show (∑ i : Fin n, (b : ℝ) ^ (-(Ls i : ℝ))) = ∑ a : α, (b : ℝ) ^ (-(L a : ℝ)) from
        Equiv.sum_comp e (fun a ↦ (b : ℝ) ^ (-(L a : ℝ)))]
      exact hkraft
    have hreal : (∑ i : Fin n, ((b ^ (M - Ls i) : ℕ) : ℝ)) ≤ ((b ^ M : ℕ) : ℝ) := by
      have hterm : ∀ i : Fin n, ((b ^ (M - Ls i) : ℕ) : ℝ) =
          (b : ℝ) ^ M * (b : ℝ) ^ (-(Ls i : ℝ)) := fun i ↦ by
        rw [Real.rpow_neg (Nat.cast_nonneg b), Real.rpow_natCast, Nat.cast_pow]
        have hpow : (b : ℝ) ^ M = (b : ℝ) ^ (M - Ls i) * (b : ℝ) ^ (Ls i) := by
          rw [← pow_add]; congr 1; have := hle_M i; omega
        rw [hpow, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      simp_rw [hterm, ← Finset.mul_sum, Nat.cast_pow]
      nlinarith [pow_pos (by exact_mod_cast hb0 : (0 : ℝ) < b) M]
    exact_mod_cast hreal
  -- Prefix sums `S i = ∑ j < i, b ^ (M - Ls j)`.
  let S : Fin n → ℕ := fun i ↦ ∑ j ∈ Finset.univ.filter (· < i), b ^ (M - Ls j)
  have hS_dvd : ∀ i : Fin n, b ^ (M - Ls i) ∣ S i := fun i ↦ by
    refine Finset.dvd_sum fun j hj ↦ ?_
    have hji : j < i := (Finset.mem_filter.1 hj).2
    exact pow_dvd_pow b (by have := hLs_mono hji.le; have := hle_M i; omega)
  have hS_add_le : ∀ i : Fin n, S i + b ^ (M - Ls i) ≤ b ^ M := fun i ↦ by
    have hsub : insert i (Finset.univ.filter (· < i)) ⊆ Finset.univ := Finset.subset_univ _
    have hnotmem : i ∉ Finset.univ.filter (· < i) := by simp
    calc S i + b ^ (M - Ls i)
        = ∑ j ∈ insert i (Finset.univ.filter (· < i)), b ^ (M - Ls j) := by
          rw [Finset.sum_insert hnotmem, add_comm]
      _ ≤ ∑ j : Fin n, b ^ (M - Ls j) := Finset.sum_le_sum_of_subset hsub
      _ ≤ b ^ M := hkraft_nat
  let c : Fin n → ℕ := fun i ↦ S i / b ^ (M - Ls i)
  have hc_mul : ∀ i : Fin n, c i * b ^ (M - Ls i) = S i := fun i ↦
    Nat.div_mul_cancel (hS_dvd i)
  have hc_lt : ∀ i : Fin n, c i < b ^ (Ls i) := fun i ↦ by
    have h1 : S i < b ^ M := by
      have := hS_add_le i
      have := pow_pos hb0 (M - Ls i)
      omega
    have h2 : c i * b ^ (M - Ls i) < b ^ (Ls i) * b ^ (M - Ls i) := by
      rw [hc_mul i, ← pow_add, show Ls i + (M - Ls i) = M by have := hle_M i; omega]
      exact h1
    exact Nat.lt_of_mul_lt_mul_right h2
  let ψ : Fin n → List (Fin b) := fun i ↦ natToDigits b hb0 (Ls i) (c i)
  refine ⟨fun a ↦ ψ (e.symm a), ?_, ?_⟩
  · intro a
    simp only [ψ, natToDigits, List.length_ofFn, Ls, Function.comp_apply, Equiv.apply_symm_apply]
  · intro a₁ a₂ hpre
    set i := e.symm a₁
    set j := e.symm a₂
    suffices hij : i = j by exact e.symm.injective hij
    obtain ⟨hLle, hdiv⟩ := natToDigits_prefix_iff hb0 (hc_lt i) (hc_lt j) hpre
    -- Hence `S i ≤ S j < S i + b ^ (M - Ls i)`.
    have hpow_split : b ^ (M - Ls i) = b ^ (Ls j - Ls i) * b ^ (M - Ls j) := by
      rw [← pow_add]; congr 1; have := hle_M j; omega
    have hlow : S i ≤ S j := by
      rw [← hc_mul i, ← hc_mul j, hpow_split, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (by rw [← hdiv]; exact Nat.div_mul_le_self _ _)
    have hhigh : S j < S i + b ^ (M - Ls i) := by
      rw [← hc_mul i, ← hc_mul j, hpow_split, show c i * (b ^ (Ls j - Ls i) * b ^ (M - Ls j)) +
        b ^ (Ls j - Ls i) * b ^ (M - Ls j) =
        ((c i + 1) * b ^ (Ls j - Ls i)) * b ^ (M - Ls j) by ring]
      refine Nat.mul_lt_mul_of_pos_right ?_ (pow_pos hb0 _)
      rw [← hdiv]
      have hpos : 0 < b ^ (Ls j - Ls i) := pow_pos hb0 _
      have := Nat.div_add_mod (c j) (b ^ (Ls j - Ls i))
      have := Nat.mod_lt (c j) hpos
      nlinarith
    have hstep : ∀ u v : Fin n, u < v → S u + b ^ (M - Ls u) ≤ S v := fun u v huv ↦ by
      have hsub : insert u (Finset.univ.filter (· < u)) ⊆ Finset.univ.filter (· < v) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        rcases ht with rfl | htu
        · exact huv
        · exact htu.trans huv
      calc S u + b ^ (M - Ls u)
          = ∑ t ∈ insert u (Finset.univ.filter (· < u)), b ^ (M - Ls t) := by
            rw [Finset.sum_insert (by simp), add_comm]
        _ ≤ S v := Finset.sum_le_sum_of_subset hsub
    rcases lt_trichotomy i j with hij | heq | hji
    · have := hstep i j hij; omega
    · exact heq
    · have := hstep j i hji; have := pow_pos hb0 (M - Ls j); omega

end Kraft

/-! ### Block-buffered compressor -/

section BlockCompressor

/-- The finite state space of a length-`K` block-buffered compressor: buffers of length `< K`. -/
abbrev BufferState (b K : ℕ) : Type := {s : List (Fin b) // s.length < K}

instance instFintypeBufferState (b K : ℕ) : Fintype (BufferState b K) := by
  let e : BufferState b K ≃ Σ l : Fin K, (Fin l.val → Fin b) :=
    { toFun := fun s ↦ ⟨⟨s.val.length, s.property⟩, fun i ↦ s.val[i.val]⟩
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
      have hq := q.property
      omega)
  start := ⟨[], by simp; omega⟩

/-- Extract the `j`-th aligned length-`K` block from a list `w`. -/
private def listBlock (K : ℕ) (w : List (Fin b)) (j : ℕ) (hj : (j + 1) * K ≤ w.length) :
    Fin K → Fin b :=
  fun i ↦ w[j * K + i.val]'(by
    have := i.isLt
    nlinarith)

/-- The list of all complete aligned length-`K` blocks of `w`. -/
private def listBlocks (K : ℕ) (w : List (Fin b)) : List (Fin K → Fin b) :=
  List.ofFn fun j : Fin (w.length / K) ↦
    listBlock K w j.val (by
      have hj : j.val + 1 ≤ w.length / K := j.isLt
      calc (j.val + 1) * K ≤ (w.length / K) * K := Nat.mul_le_mul_right K hj
        _ ≤ w.length := Nat.div_mul_le_self _ _)

private lemma list_eq_blocks_flatten_append_drop (K : ℕ) (w : List (Fin b)) :
    w = ((listBlocks K w).map List.ofFn).flatten ++ w.drop ((w.length / K) * K) := by
  have hK0 : K = 0 ∨ 0 < K := Nat.eq_zero_or_pos K
  rcases hK0 with rfl | hK
  · simp [listBlocks]
  have hflat_len : ((listBlocks K w).map List.ofFn).flatten.length = (w.length / K) * K := by
    rw [List.length_flatten, List.map_map]
    simp only [listBlocks, List.map_ofFn, Function.comp_def, List.length_ofFn, List.sum_ofFn,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hle : (w.length / K) * K ≤ w.length := Nat.div_mul_le_self _ _
  have htake : ((listBlocks K w).map List.ofFn).flatten = w.take ((w.length / K) * K) := by
    -- Prove by induction on `m = w.length / K` via a general statement for prefixes.
    suffices hgen : ∀ (m : ℕ) (hm : m * K ≤ w.length),
        (List.ofFn fun j : Fin m ↦
          List.ofFn (listBlock K w j.val (by
            have hj : j.val + 1 ≤ m := j.isLt
            calc (j.val + 1) * K ≤ m * K := Nat.mul_le_mul_right K hj
              _ ≤ w.length := hm))).flatten = w.take (m * K) by
      have h1 := hgen (w.length / K) hle
      simpa only [listBlocks, List.map_ofFn, Function.comp_def] using h1
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm' : m * K ≤ w.length := le_trans (Nat.mul_le_mul_right K (Nat.le_succ m)) hm
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_concat]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih hm']
      apply List.ext_getElem
      · simp only [List.length_append, List.length_take, List.length_ofFn,
          Nat.min_eq_left hm', Nat.min_eq_left hm]
        ring
      · intro i h₁ h₂
        simp only [List.getElem_append, List.length_take, Nat.min_eq_left hm',
          List.getElem_take, List.getElem_ofFn, listBlock]
        split_ifs with hi
        · rfl
        · congr 1; omega
  rw [htake, List.take_append_drop]

private lemma blockCompressor_eval (K : ℕ) (hK : 1 ≤ K) (φ : (Fin K → Fin b) → List (Fin b))
    (q : BufferState b K) (u : List (Fin b)) :
    ((blockCompressor K hK φ).evalState q u).val =
      (q.val ++ u).drop (((q.val ++ u).length / K) * K) ∧
    (blockCompressor K hK φ).evalOut q u =
      ((listBlocks K (q.val ++ u)).map φ).flatten := by
  have hK0 : 0 < K := by omega
  induction u using List.reverseRecOn with
  | nil =>
    have hdiv : q.val.length / K = 0 := Nat.div_eq_of_lt q.property
    simp [listBlocks, hdiv]
  | append_singleton u a ih =>
    obtain ⟨ihS, ihO⟩ := ih
    rw [FSTransducer.evalState_append, FSTransducer.evalOut_append]
    set q₁ := (blockCompressor K hK φ).evalState q u
    set w := q.val ++ u
    have hw_append : q.val ++ (u ++ [a]) = w ++ [a] := by simp [w]
    rw [hw_append]
    set m := w.length / K
    set r := w.length % K
    have hw_len : w.length = m * K + r := by
      have := Nat.div_add_mod w.length K; rw [mul_comm] at this; exact this.symm
    have hq₁_val : q₁.val = w.drop (m * K) := ihS
    have hq₁_len : q₁.val.length = r := by
      rw [hq₁_val, List.length_drop, hw_len]; omega
    have hstep_def : (blockCompressor K hK φ).evalState q₁ [a] =
        (blockCompressor K hK φ).step q₁ a := rfl
    have hout_def : (blockCompressor K hK φ).evalOut q₁ [a] =
        (blockCompressor K hK φ).out q₁ a := by simp [FSTransducer.evalOut_cons]
    rw [hstep_def, hout_def]
    by_cases hr : r + 1 < K
    · -- Buffer does not fill up.
      have hlen_lt : q₁.val.length + 1 < K := by omega
      have hdiv_eq : (w ++ [a]).length / K = m := by
        rw [List.length_append, List.length_singleton, hw_len, add_assoc, mul_comm m K,
          Nat.mul_add_div hK0, Nat.div_eq_of_lt hr, add_zero]
      have hstep_eq : ((blockCompressor K hK φ).step q₁ a).val = q₁.val ++ [a] := by
        simp [blockCompressor, hlen_lt]
      have hout_eq : (blockCompressor K hK φ).out q₁ a = [] := by
        simp [blockCompressor, hlen_lt]
      constructor
      · rw [hstep_eq, hq₁_val, hdiv_eq]
        have hle : m * K ≤ w.length := by omega
        rw [List.drop_append_of_le_length hle]
      · rw [ihO, hout_eq, List.append_nil]
        congr 2
        apply List.ext_getElem
        · rw [listBlocks, listBlocks, List.length_ofFn, List.length_ofFn, hdiv_eq]
        · intro j hj₁ hj₂
          simp only [listBlocks, List.getElem_ofFn]
          funext i
          simp only [listBlock]
          rw [List.getElem_append_left (as := w) (by
            have hj : j + 1 ≤ m := by
              simp only [listBlocks, List.length_ofFn] at hj₁
              exact hj₁
            have := i.isLt
            nlinarith)]
    · -- Buffer reaches length `K`, emits `φ` of the new block, and resets to `[]`.
      have hrK : r + 1 = K := by have := Nat.mod_lt w.length hK0; omega
      have hlen_eq : (q₁.val ++ [a]).length = K := by simp [hq₁_len, hrK]
      have hlen_nlt : ¬ q₁.val.length + 1 < K := by omega
      have hdiv_succ : (w ++ [a]).length / K = m + 1 := by
        rw [List.length_append, List.length_singleton, hw_len, add_assoc, hrK,
          show m * K + K = (m + 1) * K by ring, Nat.mul_div_cancel _ hK0]
      have hstep_eq : ((blockCompressor K hK φ).step q₁ a).val = [] := by
        simp [blockCompressor, hlen_nlt]
      have hout_eq : (blockCompressor K hK φ).out q₁ a =
          φ fun i : Fin K ↦ (q₁.val ++ [a])[i.val]'(by omega) := by
        simp [blockCompressor, hlen_nlt]
      constructor
      · rw [hstep_eq, hdiv_succ]
        symm
        rw [List.drop_eq_nil_iff, List.length_append, List.length_singleton, hw_len]
        nlinarith
      · rw [ihO, hout_eq]
        have hblocks_succ : listBlocks K (w ++ [a]) =
            listBlocks K w ++ [fun i : Fin K ↦ (q₁.val ++ [a])[i.val]'(by omega)] := by
          apply List.ext_getElem
          · rw [List.length_append, List.length_singleton]
            simp only [listBlocks, List.length_ofFn]
            exact hdiv_succ
          · intro j hj₁ hj₂
            simp only [listBlocks, List.getElem_ofFn, List.getElem_append, List.length_ofFn]
            split_ifs with hjm
            · funext i
              simp only [listBlock]
              have hle_w : (j + 1) * K ≤ w.length :=
                le_trans (Nat.mul_le_mul_right K hjm) (Nat.div_mul_le_self w.length K)
              rw [List.getElem_append_left (as := w) (by have := i.isLt; nlinarith)]
            · have hjeq : j = m := by
                rw [listBlocks, List.length_ofFn, hdiv_succ] at hj₁
                have : m ≤ j := Nat.le_of_not_lt hjm
                omega
              subst hjeq
              simp only [List.getElem_singleton]
              funext i
              simp only [listBlock, hq₁_val]
              by_cases hi : i.val < r
              · rw [List.getElem_append_left (as := w) (by omega)]
                have hlt : i.val < (w.drop (m * K)).length := by
                  rw [List.length_drop, hw_len]; omega
                simp only [hlt, ↓reduceDIte, List.getElem_drop]
              · have hir : i.val = r := by have := i.isLt; omega
                rw [List.getElem_append_right (as := w) (by omega)]
                have hnlt : ¬ i.val < (w.drop (m * K)).length := by
                  rw [List.length_drop, hw_len]; omega
                simp only [hnlt, ↓reduceDIte, List.getElem_singleton]
        rw [hblocks_succ, List.map_append, List.map_singleton, List.flatten_concat]

private lemma flatten_map_inj_of_prefixFree {α : Type*} (φ : α → List (Fin b))
    (hnonempty : ∀ a, φ a ≠ [])
    (hpre : ∀ a₁ a₂, φ a₁ <+: φ a₂ → a₁ = a₂) :
    Function.Injective (fun xs : List α ↦ (xs.map φ).flatten) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h.symm).1 (hnonempty y)
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h).1 (hnonempty x)
    | cons y ys =>
      simp only [List.map_cons, List.flatten_cons] at h
      have hxy : x = y := by
        rcases List.append_eq_append_iff.1 h with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
        · exact hpre x y ⟨s, hs.symm⟩
        · exact (hpre y x ⟨s, hs.symm⟩).symm
      subst hxy
      exact congrArg (x :: ·) (ih (List.append_cancel_left h))

/-- A block-buffered compressor induced by a prefix-free code of nonempty codewords is
information-lossless. -/
theorem blockCompressor_isInformationLossless (K : ℕ) (hK : 1 ≤ K)
    (φ : (Fin K → Fin b) → List (Fin b))
    (hnonempty : ∀ w, φ w ≠ [])
    (hpre : ∀ w₁ w₂, φ w₁ <+: φ w₂ → w₁ = w₂) :
    (blockCompressor K hK φ).IsInformationLossless := by
  intro q u v hst hout
  obtain ⟨hst_u, hout_u⟩ := blockCompressor_eval K hK φ q u
  obtain ⟨hst_v, hout_v⟩ := blockCompressor_eval K hK φ q v
  have hblocks : listBlocks K (q.val ++ u) = listBlocks K (q.val ++ v) := by
    apply flatten_map_inj_of_prefixFree φ hnonempty hpre
    dsimp only
    rw [← hout_u, ← hout_v, hout]
  have hrem : (q.val ++ u).drop (((q.val ++ u).length / K) * K) =
      (q.val ++ v).drop (((q.val ++ v).length / K) * K) := by
    rw [← hst_u, ← hst_v, hst]
  have hquv : q.val ++ u = q.val ++ v := by
    rw [list_eq_blocks_flatten_append_drop K (q.val ++ u),
      list_eq_blocks_flatten_append_drop K (q.val ++ v), hblocks, hrem]
  exact List.append_cancel_left hquv

/-- Exact output length of `blockCompressor` on a multiple `M * K` of the block length `K`. -/
theorem blockCompressor_outputLenSeq_mul (K : ℕ) (hK : 1 ≤ K)
    (φ : (Fin K → Fin b) → List (Fin b)) (d : ℕ → Fin b) (M : ℕ) :
    (blockCompressor K hK φ).outputLenSeq d (M * K) =
      ∑ j ∈ Finset.range M, (φ fun i : Fin K ↦ d (j * K + i)).length := by
  have hK0 : 0 < K := by omega
  have hev := (blockCompressor_eval K hK φ (blockCompressor K hK φ).start
    (List.ofFn fun i : Fin (M * K) ↦ d i)).2
  have hstart : (blockCompressor K hK φ).start.val = [] := rfl
  rw [hstart, List.nil_append] at hev
  rw [FSTransducer.outputLenSeq, hev, List.length_flatten, List.map_map]
  simp only [listBlocks, List.length_ofFn, Nat.mul_div_cancel _ hK0, List.map_ofFn,
    Function.comp_def, List.sum_ofFn, Fin.val_cast]
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (φ fun i : Fin K ↦ d (j * K + i)).length) M]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 2
  funext i
  simp [listBlock]

end BlockCompressor

/-! ### Converse and full Schnorr–Stimm / Becher–Heiber characterization -/

section Converse

/-- Extract a strictly increasing sequence from a `Frequently` predicate on `ℕ`. -/
private lemma exists_strictMono_of_frequently {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  rw [Filter.frequently_atTop] at h
  have hstep : ∀ N : ℕ, ∃ m, N ≤ m ∧ P m := h
  choose f hf_ge hfP using hstep
  let φ : ℕ → ℕ := Nat.rec (f 1) (fun _ prev ↦ f (prev + 1))
  refine ⟨φ, strictMono_nat_of_lt_succ fun n ↦ ?_, fun n ↦ ?_⟩
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (φ n)) (hf_ge (φ n + 1))
  · cases n with
    | zero => exact hfP 1
    | succ n => exact hfP (φ n + 1)

/-- Strict Gibbs inequality for the averaged distribution `q d = (p d + B⁻¹) / 2` when `p` is
non-uniform on `Fin B`. -/
private lemma strict_gibbs_avg {B : ℕ} (hB : 2 ≤ B) (p : Fin B → ℝ)
    (hp_nonneg : ∀ d, 0 ≤ p d) (hp_sum : ∑ d : Fin B, p d = 1)
    {d₀ : Fin B} (hd₀ : p d₀ ≠ (B : ℝ)⁻¹) :
    let q : Fin B → ℝ := fun d ↦ (p d + (B : ℝ)⁻¹) / 2
    (∀ d, 0 < q d) ∧ (∀ d, q d < 1) ∧ (∑ d : Fin B, q d = 1) ∧
      ∑ d : Fin B, p d * (-Real.log (q d)) < Real.log B := by
  intro q
  have hB_pos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hu_pos : (0 : ℝ) < (B : ℝ)⁻¹ := inv_pos.2 hB_pos
  have hu_le : (B : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hB)
  have hp_le_one : ∀ d : Fin B, p d ≤ 1 := fun d ↦ by
    calc p d ≤ ∑ c : Fin B, p c := Finset.single_le_sum (fun c _ ↦ hp_nonneg c) (Finset.mem_univ d)
      _ = 1 := hp_sum
  have hq_pos : ∀ d : Fin B, 0 < q d := fun d ↦ by dsimp only [q]; linarith [hp_nonneg d]
  have hq_lt : ∀ d : Fin B, q d < 1 := fun d ↦ by dsimp only [q]; linarith [hp_le_one d]
  have hq_sum : ∑ d : Fin B, q d = 1 := by
    simp only [q, ← Finset.sum_div, Finset.sum_add_distrib, hp_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hB_pos.ne']
    norm_num
  refine ⟨hq_pos, hq_lt, hq_sum, ?_⟩
  have halg : ∀ d : Fin B,
      p d * Real.log ((B : ℝ)⁻¹ / q d) ≤
        ((B : ℝ)⁻¹ - p d) / 2 - (p d - (B : ℝ)⁻¹) ^ 2 / (2 * (p d + (B : ℝ)⁻¹)) := fun d ↦ by
    have h1 : p d * Real.log ((B : ℝ)⁻¹ / q d) ≤ p d * ((B : ℝ)⁻¹ / q d - 1) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hu_pos (hq_pos d)))
        (hp_nonneg d)
    have hden : p d + (B : ℝ)⁻¹ ≠ 0 := by linarith [hp_nonneg d]
    have h2 : ∀ a u : ℝ, a + u ≠ 0 →
        a * (u / ((a + u) / 2) - 1) = (u - a) / 2 - (a - u) ^ 2 / (2 * (a + u)) := fun a u h ↦ by
      field_simp [h]; ring
    dsimp only [q] at h1 ⊢
    linarith [h2 (p d) (B : ℝ)⁻¹ hden]
  have hsum_lt : ∑ d : Fin B, p d * Real.log ((B : ℝ)⁻¹ / q d) <
      ∑ d : Fin B, ((B : ℝ)⁻¹ - p d) / 2 :=
    Finset.sum_lt_sum (fun d _ ↦ by
      have : 0 ≤ (p d - (B : ℝ)⁻¹) ^ 2 / (2 * (p d + (B : ℝ)⁻¹)) :=
        div_nonneg (sq_nonneg _) (by linarith [hp_nonneg d])
      linarith [halg d]) ⟨d₀, Finset.mem_univ d₀, by
      have : 0 < (p d₀ - (B : ℝ)⁻¹) ^ 2 / (2 * (p d₀ + (B : ℝ)⁻¹)) :=
        div_pos (sq_pos_of_ne_zero (sub_ne_zero.2 hd₀)) (by linarith [hp_nonneg d₀])
      linarith [halg d₀]⟩
  have hrhs_zero : ∑ d : Fin B, ((B : ℝ)⁻¹ - p d) / 2 = 0 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hp_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hB_pos.ne', sub_self, zero_div]
  have hlhs_eq : ∑ d : Fin B, p d * Real.log ((B : ℝ)⁻¹ / q d) =
      ∑ d : Fin B, p d * (-Real.log (q d)) - Real.log B := by
    have hterm : ∀ d : Fin B, p d * Real.log ((B : ℝ)⁻¹ / q d) =
        p d * (-Real.log (q d)) - p d * Real.log B := fun d ↦ by
      rw [Real.log_div hu_pos.ne' (hq_pos d).ne', Real.log_inv]; ring
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
  linarith

private lemma sum_range_mul_eq {α : Type*} [AddCommMonoid α] (N m : ℕ) (g : ℕ → α) :
    ∑ j ∈ Finset.range N, ∑ i : Fin m, g (j * m + i) = ∑ t ∈ Finset.range (N * m), g t := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ g (N * m + i)) m]

/-- **Schnorr–Stimm / Becher–Heiber characterization of normal numbers**:
a real number `x` is normal in base `b ≥ 2` if and only if no information-lossless finite-state
transducer over `Fin b` compresses the base-`b` digit sequence of `x` below ratio `1`. -/
theorem isNormalIn_iff_finiteStateIncompressible (hb : 2 ≤ b) :
    IsNormalIn b x ↔
      ∀ (Q : Type) [Fintype Q] (T : FSTransducer b Q), T.IsInformationLossless →
        ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
          (1 - ε) * (N : ℝ) ≤ (T.outputLen (by omega) x N : ℝ) := by
  classical
  have hb0 : 0 < b := by omega
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  refine ⟨fun hx _ _ T hT _ hε ↦ finiteStateIncompressible_of_isNormalIn hb T hT hx hε, ?_⟩
  intro hcomp
  by_contra hnot
  rw [isNormalIn_iff_forall_isSimplyNormalIn_pow hb] at hnot
  push Not at hnot
  obtain ⟨k, hk, hnot_simp⟩ := hnot
  set B := b ^ k
  have hB : 2 ≤ B := hb.trans (Nat.le_self_pow hk.ne' b)
  have hB0 : 0 < B := by omega
  have : NeZero B := ⟨hB0.ne'⟩
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  -- Extract `d₀ : Fin B` whose base-`B` frequency fails to converge to `B⁻¹`.
  unfold IsSimplyNormalIn at hnot_simp
  push Not at hnot_simp
  obtain ⟨d₀, hd₀_not⟩ := hnot_simp
  let freq : ℕ → Fin B → ℝ := fun M d ↦ (blockCount B x (fun _ : Fin 1 ↦ d) M : ℝ) / M
  rw [Metric.tendsto_atTop] at hd₀_not
  push Not at hd₀_not
  obtain ⟨δ, hδ, hfreq⟩ := hd₀_not
  have hfreq' : ∃ᶠ M in atTop, 1 ≤ M ∧ δ ≤ |freq M d₀ - (B : ℝ)⁻¹| := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨M, hMN, hMd⟩ := hfreq (max N 1)
    refine ⟨M, (le_max_left N 1).trans hMN, (le_max_right N 1).trans hMN, ?_⟩
    simpa only [Real.dist_eq, freq] using hMd
  obtain ⟨φ₁, hφ₁_mono, hφ₁_prop⟩ := exists_strictMono_of_frequently hfreq'
  -- Extract a subsequence along which the entire frequency vector `freq (φ₁ n)` converges.
  have hbox_cpt : IsCompact (Set.pi Set.univ fun _ : Fin B ↦ Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hmem_box : ∀ n : ℕ, freq (φ₁ n) ∈ Set.pi Set.univ fun _ : Fin B ↦ Set.Icc (0 : ℝ) 1 := by
    intro n d _
    have hM1 : 1 ≤ φ₁ n := (hφ₁_prop n).1
    have hMpos : (0 : ℝ) < φ₁ n := by exact_mod_cast hM1
    refine ⟨by dsimp only [freq]; positivity, ?_⟩
    dsimp only [freq]
    rw [div_le_one hMpos]
    exact_mod_cast blockCount_le B x _ (φ₁ n)
  obtain ⟨p, hp_mem, φ₂, hφ₂_mono, hp_tend⟩ := hbox_cpt.tendsto_subseq hmem_box
  set Mseq : ℕ → ℕ := fun n ↦ φ₁ (φ₂ n)
  have hMseq_mono : StrictMono Mseq := hφ₁_mono.comp hφ₂_mono
  have hMseq_top : Tendsto Mseq atTop atTop := hMseq_mono.tendsto_atTop
  have hMseq_pos : ∀ n, 1 ≤ Mseq n := fun n ↦ (hφ₁_prop (φ₂ n)).1
  have hp_coord : ∀ d : Fin B, Tendsto (fun n ↦ freq (Mseq n) d) atTop (𝓝 (p d)) := fun d ↦
    (continuous_apply d).continuousAt.tendsto.comp hp_tend
  have hp_nonneg : ∀ d : Fin B, 0 ≤ p d := fun d ↦ (hp_mem d (Set.mem_univ d)).1
  have hp_sum : ∑ d : Fin B, p d = 1 := by
    have hsum_one : ∀ n : ℕ, ∑ d : Fin B, freq (Mseq n) d = 1 := fun n ↦ by
      have hMpos : (0 : ℝ) < Mseq n := by exact_mod_cast hMseq_pos n
      simp only [freq, ← Finset.sum_div]
      have hbc : ∑ d : Fin B, blockCount B x (fun _ : Fin 1 ↦ d) (Mseq n) = Mseq n := by
        have h1 := sum_blockCount (b := B) (x := x) 1 (Mseq n)
        have heq := Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin B)).symm
          (fun w : Fin 1 → Fin B ↦ blockCount B x w (Mseq n))
        rw [← heq] at h1
        exact h1
      rw [← Nat.cast_sum, hbc, div_self hMpos.ne']
    have ht : Tendsto (fun n ↦ ∑ d : Fin B, freq (Mseq n) d) atTop (𝓝 (∑ d : Fin B, p d)) :=
      tendsto_finset_sum Finset.univ (fun d _ ↦ hp_coord d)
    simp_rw [hsum_one] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hp_ne : p d₀ ≠ (B : ℝ)⁻¹ := by
    have habs : Tendsto (fun n ↦ |freq (Mseq n) d₀ - (B : ℝ)⁻¹|) atTop (𝓝 |p d₀ - (B : ℝ)⁻¹|) :=
      ((hp_coord d₀).sub_const _).abs
    have hge : δ ≤ |p d₀ - (B : ℝ)⁻¹| :=
      ge_of_tendsto' habs fun n ↦ (hφ₁_prop (φ₂ n)).2
    intro heq
    rw [heq, sub_self, abs_zero] at hge
    linarith
  -- Apply strict Gibbs inequality to `q d = (p d + B⁻¹) / 2`.
  set q : Fin B → ℝ := fun d ↦ (p d + (B : ℝ)⁻¹) / 2
  obtain ⟨hq_pos, hq_lt, hq_sum, hgibbs⟩ := strict_gibbs_avg hB p hp_nonneg hp_sum hp_ne
  set H : ℝ := (∑ d : Fin B, p d * (-Real.log (q d))) / Real.log b
  have hH_lt : H < k := by
    dsimp only [H]
    rw [div_lt_iff₀ hlogb]
    have hlogB : Real.log B = (k : ℝ) * Real.log b := by
      simp only [B, Nat.cast_pow, Real.log_pow]
    linarith
  set ε : ℝ := (1 - H / k) / 4
  have hε : 0 < ε := by
    have : H / k < 1 := (div_lt_one hk_pos).2 hH_lt
    dsimp only [ε]; linarith
  -- Pick `m ≥ 1` large enough that `H / k + 1 / (m * k) < 1 - 2 * ε`.
  obtain ⟨m, hm_gt⟩ := exists_nat_gt (1 / (2 * ε * (k : ℝ)))
  have hm : 1 ≤ m := by
    have : 0 < 1 / (2 * ε * (k : ℝ)) := by positivity
    have : 0 < m := by exact_mod_cast this.trans hm_gt
    omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk_bound : H / k + 1 / ((m : ℝ) * k) < 1 - 2 * ε := by
    have h1 : 1 / ((m : ℝ) * k) < 2 * ε := by
      rw [div_lt_iff₀ (by positivity)] at hm_gt ⊢
      nlinarith
    dsimp only [ε] at h1 ⊢
    linarith
  -- Construct a Kraft prefix-free code of length `L` on `Fin (m * k) → Fin b`.
  let splitBlock : (Fin (m * k) → Fin b) → (Fin m → Fin B) := fun w i ↦
    blockCode fun t : Fin k ↦ w ⟨i.val * k + t.val, by
      have hi : i.val + 1 ≤ m := i.isLt
      have ht : t.val < k := t.isLt
      nlinarith⟩
  have hsplit_bij : Function.Bijective splitBlock := by
    have hbc_bij : Function.Bijective (blockCode (b := b) (k := k)) :=
      finFunctionFinEquiv.bijective.comp (Equiv.arrowCongr (Fin.revPerm) (Equiv.refl _)).bijective
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [B, ← pow_mul, mul_comm]⟩
    intro w₁ w₂ h
    funext r
    have hi : r.val / k < m := (Nat.div_lt_iff_lt_mul hk).2 r.isLt
    have ht : r.val % k < k := Nat.mod_lt _ hk
    have hblock := hbc_bij.1 (congrFun h ⟨r.val / k, hi⟩)
    have hval := congrFun hblock ⟨r.val % k, ht⟩
    have hidx : (⟨r.val / k * k + r.val % k, by
        have := Nat.div_add_mod r.val k; rw [mul_comm] at this; omega⟩ : Fin (m * k)) = r := by
      apply Fin.ext
      have := Nat.div_add_mod r.val k
      rw [mul_comm] at this
      exact this
    simpa [hidx] using hval
  let eSplit : (Fin (m * k) → Fin b) ≃ (Fin m → Fin B) := Equiv.ofBijective splitBlock hsplit_bij
  let L_B : (Fin m → Fin B) → ℕ := fun W ↦
    Nat.ceil (-(∑ i : Fin m, Real.log (q (W i))) / Real.log b)
  let L : (Fin (m * k) → Fin b) → ℕ := fun w ↦ L_B (eSplit w)
  have hneg_log_pos : ∀ d : Fin B, 0 < -Real.log (q d) := fun d ↦
    neg_pos.2 (Real.log_neg (hq_pos d) (hq_lt d))
  have hL_pos : ∀ w : Fin (m * k) → Fin b, 1 ≤ L w := fun w ↦ by
    dsimp only [L, L_B]
    have hpos : 0 < -(∑ i : Fin m, Real.log (q (eSplit w i))) / Real.log b := by
      rw [← Finset.sum_neg_distrib]
      refine div_pos (Finset.sum_pos (fun i _ ↦ hneg_log_pos _) ?_) hlogb
      exact Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
  have hkraft : ∑ w : Fin (m * k) → Fin b, (b : ℝ) ^ (-(L w : ℝ)) ≤ 1 := by
    rw [Equiv.sum_comp eSplit (fun W ↦ (b : ℝ) ^ (-(L_B W : ℝ)))]
    have hterm : ∀ W : Fin m → Fin B, (b : ℝ) ^ (-(L_B W : ℝ)) ≤ ∏ i : Fin m, q (W i) := fun W ↦ by
      have hceil : -(∑ i : Fin m, Real.log (q (W i))) / Real.log b ≤ (L_B W : ℝ) :=
        Nat.le_ceil _
      have hmul : -(L_B W : ℝ) * Real.log b ≤ ∑ i : Fin m, Real.log (q (W i)) := by
        rw [div_le_iff₀ hlogb] at hceil
        linarith
      calc (b : ℝ) ^ (-(L_B W : ℝ))
          = Real.exp (-(L_B W : ℝ) * Real.log b) := by
            rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < b), mul_comm]
        _ ≤ Real.exp (∑ i : Fin m, Real.log (q (W i))) := Real.exp_le_exp.2 hmul
        _ = ∏ i : Fin m, Real.exp (Real.log (q (W i))) := Real.exp_sum _ _
        _ = ∏ i : Fin m, q (W i) :=
            Finset.prod_congr rfl fun i _ ↦ Real.exp_log (hq_pos _)
    calc ∑ W : Fin m → Fin B, (b : ℝ) ^ (-(L_B W : ℝ))
        ≤ ∑ W : Fin m → Fin B, ∏ i : Fin m, q (W i) := Finset.sum_le_sum fun W _ ↦ hterm W
      _ = ∏ _i : Fin m, ∑ d : Fin B, q d := (Fintype.prod_sum fun _ d ↦ q d).symm
      _ = 1 := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [show ∑ d : Fin B, q d = 1 from hq_sum, one_pow]
  obtain ⟨φ, hφ_len, hφ_pre⟩ := exists_prefixFree_code hb L hL_pos hkraft
  have hφ_ne : ∀ w, φ w ≠ [] := fun w h ↦ by
    have := hL_pos w; rw [← hφ_len w, h] at this; simp at this
  -- Build the block compressor `T` of block size `K = m * k`.
  have hK : 1 ≤ m * k := Nat.mul_pos hm hk
  let T := blockCompressor (m * k) hK φ
  have hT_il : T.IsInformationLossless :=
    blockCompressor_isInformationLossless (m * k) hK φ hφ_ne hφ_pre
  have hincomp := hcomp (BufferState b (m * k)) T hT_il ε hε
  -- Evaluate `T` along the subsequence `Lseq n = (Mseq n / m) * (m * k)`.
  let Nseq : ℕ → ℕ := fun n ↦ Mseq n / m
  let Lseq : ℕ → ℕ := fun n ↦ Nseq n * (m * k)
  have hNseq_top : Tendsto Nseq atTop atTop :=
    (Nat.tendsto_div_const_atTop (by omega : m ≠ 0)).comp hMseq_top
  have hLseq_top : Tendsto Lseq atTop atTop :=
    (tendsto_id.atTop_mul_const' (show 0 < m * k by positivity)).comp hNseq_top
  -- Compute the upper bound on `outputLen T x (Lseq n) / Lseq n`.
  have hM_div_Nm : Tendsto (fun n ↦ (Mseq n : ℝ) / ((Nseq n : ℝ) * m)) atTop (𝓝 1) := by
    have hlow : ∀ᶠ n in atTop, (1 : ℝ) ≤ (Mseq n : ℝ) / ((Nseq n : ℝ) * m) := by
      filter_upwards [hNseq_top.eventually (eventually_gt_atTop 0)] with n hn
      have hpos : (0 : ℝ) < (Nseq n : ℝ) * m := by
        have : (0 : ℝ) < Nseq n := by exact_mod_cast hn
        positivity
      rw [one_le_div hpos]
      exact_mod_cast Nat.div_mul_le_self (Mseq n) m
    have hhigh : ∀ᶠ n in atTop, (Mseq n : ℝ) / ((Nseq n : ℝ) * m) ≤ 1 + 1 / (Nseq n : ℝ) := by
      filter_upwards [hNseq_top.eventually (eventually_gt_atTop 0)] with n hn
      have hNpos : (0 : ℝ) < Nseq n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (Nseq n : ℝ) * m := by positivity
      rw [div_le_iff₀ hpos]
      have hlt : Mseq n < (Nseq n + 1) * m := by
        have := Nat.div_add_mod (Mseq n) m
        have := Nat.mod_lt (Mseq n) (by omega : 0 < m)
        dsimp only [Nseq]; nlinarith
      have hlt' : (Mseq n : ℝ) ≤ ((Nseq n : ℝ) + 1) * m := by exact_mod_cast hlt.le
      have : (1 + 1 / (Nseq n : ℝ)) * ((Nseq n : ℝ) * m) = ((Nseq n : ℝ) + 1) * m := by
        field_simp
      linarith
    have hlim_high : Tendsto (fun n ↦ 1 + 1 / (Nseq n : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hNseq_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_high hlow hhigh
  have hub_tendsto : Tendsto (fun n ↦
      1 / ((m : ℝ) * k) + ((Mseq n : ℝ) / ((Nseq n : ℝ) * m)) * (1 / (k : ℝ)) *
        (∑ d : Fin B, freq (Mseq n) d * (-Real.log (q d))) / Real.log b)
      atTop (𝓝 (1 / ((m : ℝ) * k) + H / k)) := by
    have hsum_t : Tendsto (fun n ↦ ∑ d : Fin B, freq (Mseq n) d * (-Real.log (q d)))
        atTop (𝓝 (∑ d : Fin B, p d * (-Real.log (q d)))) :=
      tendsto_finset_sum Finset.univ fun d _ ↦ (hp_coord d).mul_const _
    have hprod := (((hM_div_Nm.mul (tendsto_const_nhds (x := 1 / (k : ℝ)))).mul hsum_t).div_const
      (Real.log b))
    have htot := (tendsto_const_nhds (x := 1 / ((m : ℝ) * k))).add hprod
    convert htot using 2
    dsimp only [H]
    ring
  have hev_incomp := hLseq_top.eventually hincomp
  obtain ⟨n, hn_incomp, hn_ub, hn_pos⟩ :=
    (hev_incomp.and ((hub_tendsto.eventually
      (gt_mem_nhds (show 1 / ((m : ℝ) * k) + H / k < 1 - 2 * ε by linarith))).and
      (hNseq_top.eventually (eventually_gt_atTop 0)))).exists
  -- Prove the upper bound at `n`.
  have hNpos : (0 : ℝ) < Nseq n := by exact_mod_cast hn_pos
  have hLpos : (0 : ℝ) < Lseq n := by
    simp only [Lseq, Nat.cast_mul]; positivity
  have hMpos : (0 : ℝ) < Mseq n := by exact_mod_cast hMseq_pos n
  let dSeq : ℕ → Fin b := fun i ↦ ⟨digit b x i, digit_lt hb0 x i⟩
  have hblock_digit : ∀ (j : ℕ) (i : Fin m),
      eSplit (fun r : Fin (m * k) ↦ dSeq (j * (m * k) + r)) i =
        ⟨digit B x (j * m + i), digit_lt hB0 x (j * m + i)⟩ := fun j i ↦ by
    apply Fin.ext
    have hiff := forall_digit_eq_iff_digit_pow (x := x) hb0
      (fun t : Fin k ↦ dSeq (j * (m * k) + (i.val * k + t.val))) 0 (j * m + i.val)
    simp only [zero_add, pow_zero, mul_one] at hiff
    have htrue : ∀ t : Fin k, digit b x ((j * m + i.val) * k + t.val) =
        (dSeq (j * (m * k) + (i.val * k + t.val)) : ℕ) := fun t ↦ by
      dsimp only [dSeq]
      congr 1; ring
    exact (hiff.1 htrue).symm
  have hout_le : (T.outputLen hb0 x (Lseq n) : ℝ) ≤
      (Nseq n : ℝ) +
        (∑ d : Fin B, (blockCount B x (fun _ : Fin 1 ↦ d) (Mseq n) : ℝ) * (-Real.log (q d))) /
          Real.log b := by
    have hform := blockCompressor_outputLenSeq_mul (m * k) hK φ dSeq (Nseq n)
    change (T.outputLenSeq dSeq (Nseq n * (m * k)) : ℝ) ≤ _
    rw [hform]
    push_cast
    have hstep1 : ∀ j ∈ Finset.range (Nseq n),
        ((φ fun r : Fin (m * k) ↦ dSeq (j * (m * k) + r)).length : ℝ) ≤
          1 + (∑ i : Fin m, -Real.log (q ⟨digit B x (j * m + i), digit_lt hB0 x _⟩)) /
            Real.log b := fun j _ ↦ by
      rw [hφ_len]
      dsimp only [L, L_B]
      have harg_nn : 0 ≤ -(∑ i : Fin m,
          Real.log (q (eSplit (fun r : Fin (m * k) ↦ dSeq (j * (m * k) + r)) i))) /
            Real.log b := by
        rw [← Finset.sum_neg_distrib]
        exact div_nonneg (Finset.sum_nonneg fun i _ ↦ (hneg_log_pos _).le) hlogb.le
      have hceil_le := (Nat.ceil_lt_add_one harg_nn).le
      simp_rw [hblock_digit, ← Finset.sum_neg_distrib] at hceil_le ⊢
      linarith
    calc ∑ j ∈ Finset.range (Nseq n),
            ((φ fun r : Fin (m * k) ↦ dSeq (j * (m * k) + r)).length : ℝ)
        ≤ ∑ j ∈ Finset.range (Nseq n),
            (1 + (∑ i : Fin m, -Real.log (q ⟨digit B x (j * m + i), digit_lt hB0 x _⟩)) /
              Real.log b) := Finset.sum_le_sum hstep1
      _ = (Nseq n : ℝ) +
            (∑ t ∈ Finset.range (Nseq n * m),
              -Real.log (q ⟨digit B x t, digit_lt hB0 x t⟩)) / Real.log b := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
            ← Finset.sum_div,
            sum_range_mul_eq (Nseq n) m (fun t ↦ -Real.log (q ⟨digit B x t, digit_lt hB0 x t⟩))]
      _ ≤ (Nseq n : ℝ) +
            (∑ t ∈ Finset.range (Mseq n),
              -Real.log (q ⟨digit B x t, digit_lt hB0 x t⟩)) / Real.log b := by
          refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hlogb.le)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.div_mul_le_self (Mseq n) m))
            (fun t _ _ ↦ (hneg_log_pos _).le)
      _ = (Nseq n : ℝ) +
            (∑ d : Fin B, (blockCount B x (fun _ : Fin 1 ↦ d) (Mseq n) : ℝ) *
              (-Real.log (q d))) / Real.log b := by
          congr 2
          rw [← Finset.sum_fiberwise_of_maps_to
            (g := fun t ↦ (⟨digit B x t, digit_lt hB0 x t⟩ : Fin B))
            (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)]
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          have hconst : ∀ t ∈ (Finset.range (Mseq n)).filter
              (fun t ↦ (⟨digit B x t, digit_lt hB0 x t⟩ : Fin B) = d),
              -Real.log (q ⟨digit B x t, digit_lt hB0 x t⟩) = -Real.log (q d) := fun t ht ↦ by
            rw [(Finset.mem_filter.1 ht).2]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
          congr 2
          unfold blockCount
          congr 1
          ext t
          simp [Fin.ext_iff]
  -- Divide by `Lseq n = Nseq n * m * k` and derive a contradiction.
  have hdiv_ub : (T.outputLen hb0 x (Lseq n) : ℝ) / (Lseq n : ℝ) ≤
      1 / ((m : ℝ) * k) + ((Mseq n : ℝ) / ((Nseq n : ℝ) * m)) * (1 / (k : ℝ)) *
        (∑ d : Fin B, freq (Mseq n) d * (-Real.log (q d))) / Real.log b := by
    have hrew : ((Nseq n : ℝ) +
        (∑ d : Fin B, (blockCount B x (fun _ : Fin 1 ↦ d) (Mseq n) : ℝ) * (-Real.log (q d))) /
          Real.log b) / (Lseq n : ℝ) =
        1 / ((m : ℝ) * k) + ((Mseq n : ℝ) / ((Nseq n : ℝ) * m)) * (1 / (k : ℝ)) *
          (∑ d : Fin B, freq (Mseq n) d * (-Real.log (q d))) / Real.log b := by
      have hsum_f : ∑ d : Fin B, freq (Mseq n) d * (-Real.log (q d)) =
          (∑ d : Fin B, (blockCount B x (fun _ : Fin 1 ↦ d) (Mseq n) : ℝ) * (-Real.log (q d))) /
            (Mseq n : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun d _ ↦ by dsimp only [freq]; ring
      rw [hsum_f]
      simp only [Lseq, Nat.cast_mul]
      field_simp
    rw [← hrew]
    exact div_le_div_of_nonneg_right hout_le hLpos.le
  have hdiv_lb : 1 - ε ≤ (T.outputLen hb0 x (Lseq n) : ℝ) / (Lseq n : ℝ) := by
    rw [le_div_iff₀ hLpos]
    exact hn_incomp
  linarith

end Converse

/-! ### Arbitrary compressibility of rational numbers -/

section RationalCompression

/-- Every rational number can be compressed to an arbitrarily small asymptotic ratio `ε > 0`
by an information-lossless finite-state transducer over `Fin b` (`b ≥ 2`). -/
theorem exists_compresses_rat (hb : 2 ≤ b) (r : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : Type) (_ : Fintype Q) (T : FSTransducer b Q),
      T.IsInformationLossless ∧
      ∀ᶠ N : ℕ in atTop, (T.outputLen (by omega) (r : ℝ) N : ℝ) ≤ ε * (N : ℝ) := by
  classical
  have hb0 : 0 < b := by omega
  set D := r.den with hD
  have hD_pos : 0 < D := r.pos
  set L₀ : ℕ := 2 * D
  have hL₀_pos : 1 ≤ L₀ := by omega
  -- Pick block length `K ≥ 1` so that `L₀ / K < ε / 2`.
  obtain ⟨K, hK_gt⟩ := exists_nat_gt (2 * (L₀ : ℝ) / ε)
  have hK : 1 ≤ K := by
    have : 0 < 2 * (L₀ : ℝ) / ε := by positivity
    have : 0 < K := by exact_mod_cast this.trans hK_gt
    omega
  have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK
  -- Collect the at most `D` distinct length-`K` blocks appearing in `r`.
  let blkOf : ℝ → Fin K → Fin b := fun y j ↦ ⟨digit b y j, digit_lt hb0 y j⟩
  set S : Finset (Fin K → Fin b) := (Finset.range D).image fun t : ℕ ↦ blkOf ((t : ℝ) / D)
  have hS_card : S.card ≤ D := Finset.card_image_le.trans (by simp)
  have hmem_S : ∀ i : ℕ, (fun j : Fin K ↦ (⟨digit b (r : ℝ) (i + j), digit_lt hb0 _ _⟩ : Fin b)) ∈
      S := by
    intro i
    have hq0 : (0 : ℤ) < D := by exact_mod_cast hD_pos
    have hrem_nn : (0 : ℤ) ≤ (r.num * (b : ℤ) ^ i) % (D : ℤ) := Int.emod_nonneg _ hq0.ne'
    set t := ((r.num * (b : ℤ) ^ i) % (D : ℤ)).toNat
    have ht_lt : t < D := by
      rw [← Int.ofNat_lt, Int.toNat_of_nonneg hrem_nn]
      exact Int.emod_lt_of_pos _ hq0
    refine Finset.mem_image.2 ⟨t, Finset.mem_range.2 ht_lt, ?_⟩
    funext j
    apply Fin.ext
    have hfr : Int.fract ((r : ℝ) * (b : ℝ) ^ i) = (t : ℝ) / D := by
      have : (r : ℝ) * (b : ℝ) ^ i = ((r.num * (b : ℤ) ^ i : ℤ) : ℝ) / (D : ℕ) := by
        rw [hD]; push_cast; rw [Rat.cast_def]; ring
      rw [this, Int.fract_div_intCast_eq_div_intCast_mod]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg hrem_nn).symm
    simp only [blkOf]
    rw [digit_add_eq_digit_fract, hfr]
  -- Assign length `L₀` to blocks in `S`, and `K + 1` to all other blocks.
  let L : (Fin K → Fin b) → ℕ := fun w ↦ if w ∈ S then L₀ else K + 1
  have hL_pos : ∀ w, 1 ≤ L w := fun w ↦ by
    dsimp only [L]; split_ifs <;> omega
  have hkraft : ∑ w : Fin K → Fin b, (b : ℝ) ^ (-(L w : ℝ)) ≤ 1 := by
    have hsplit : ∑ w : Fin K → Fin b, (b : ℝ) ^ (-(L w : ℝ)) =
        (∑ w ∈ S, (b : ℝ) ^ (-(L₀ : ℝ))) +
          (∑ w ∈ Sᶜ, (b : ℝ) ^ (-((K + 1 : ℕ) : ℝ))) := by
      rw [← Finset.sum_add_sum_compl S (fun w ↦ (b : ℝ) ^ (-(L w : ℝ)))]
      congr 1
      · refine Finset.sum_congr rfl fun w hw ↦ by simp [L, hw]
      · refine Finset.sum_congr rfl fun w hw ↦ by
          have : w ∉ S := Finset.mem_compl.1 hw
          simp [L, this]
    rw [hsplit, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hpart1 : (S.card : ℝ) * (b : ℝ) ^ (-(L₀ : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg (Nat.cast_nonneg b), Real.rpow_natCast]
      have hpow : 2 * D ≤ b ^ L₀ := by
        calc 2 * D ≤ 2 ^ (2 * D) := Nat.lt_two_pow_self.le
          _ ≤ b ^ L₀ := Nat.pow_le_pow_left hb L₀
      have hpow' : (2 : ℝ) * D ≤ (b : ℝ) ^ L₀ := by exact_mod_cast hpow
      have hSc : (S.card : ℝ) ≤ D := by exact_mod_cast hS_card
      have hbL : (0 : ℝ) < (b : ℝ) ^ L₀ := by positivity
      rw [← div_eq_mul_inv, div_le_div_iff₀ hbL (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hpart2 : (Sᶜ.card : ℝ) * (b : ℝ) ^ (-((K + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg (Nat.cast_nonneg b), Real.rpow_natCast]
      have hSc : (Sᶜ.card : ℝ) ≤ (b : ℝ) ^ K := by
        have h1 : Sᶜ.card ≤ (Finset.univ : Finset (Fin K → Fin b)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        simpa using (Nat.cast_le (α := ℝ)).2 h1
      have hpow : (b : ℝ) ^ (K + 1) = (b : ℝ) ^ K * (b : ℝ) := pow_succ (b : ℝ) K
      have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
      have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
      calc (Sᶜ.card : ℝ) * ((b : ℝ) ^ (K + 1))⁻¹
          ≤ (b : ℝ) ^ K * ((b : ℝ) ^ K * (b : ℝ))⁻¹ := by rw [hpow]; gcongr
        _ = (b : ℝ)⁻¹ := by
            rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hbK.ne', one_mul]
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hb2
    linarith
  obtain ⟨φ, hφ_len, hφ_pre⟩ := exists_prefixFree_code hb L hL_pos hkraft
  have hφ_ne : ∀ w, φ w ≠ [] := fun w h ↦ by
    have := hL_pos w; rw [← hφ_len w, h] at this; simp at this
  let T := blockCompressor K hK φ
  refine ⟨BufferState b K, inferInstance, T,
    blockCompressor_isInformationLossless K hK φ hφ_ne hφ_pre, ?_⟩
  -- For every `N`, `outputLen T r N ≤ (N / K + 1) * L₀ ≤ (ε / 2) * N + L₀`.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (L₀ : ℝ) / ε)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hle_mul : N ≤ (N / K + 1) * K := by
    have := Nat.div_add_mod N K; have := Nat.mod_lt N (by omega : 0 < K); nlinarith
  have hout_le : T.outputLen hb0 (r : ℝ) N ≤ (N / K + 1) * L₀ := by
    calc T.outputLen hb0 (r : ℝ) N
        ≤ T.outputLen hb0 (r : ℝ) ((N / K + 1) * K) := T.outputLen_mono hb0 (r : ℝ) hle_mul
      _ = ∑ j ∈ Finset.range (N / K + 1),
            (φ fun i : Fin K ↦ ⟨digit b (r : ℝ) (j * K + i), digit_lt hb0 _ _⟩).length :=
          blockCompressor_outputLenSeq_mul K hK φ _ (N / K + 1)
      _ = ∑ _j ∈ Finset.range (N / K + 1), L₀ :=
          Finset.sum_congr rfl fun j _ ↦ by rw [hφ_len]; simp [L, hmem_S (j * K)]
      _ = (N / K + 1) * L₀ := by simp
  have h1 : (L₀ : ℝ) / K < ε / 2 := by
    rw [div_lt_iff₀ hε] at hK_gt; rw [div_lt_iff₀ hK_pos]; linarith
  have h2 : (L₀ : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    rw [div_lt_iff₀ hε] at hN₀; have hN' : (N₀ : ℝ) ≤ N := Nat.cast_le.2 hN; nlinarith
  have hdiv : ((N / K : ℕ) : ℝ) ≤ (N : ℝ) / K := by
    rw [le_div_iff₀ hK_pos]; exact_mod_cast Nat.div_mul_le_self N K
  have hout_real : (T.outputLen hb0 (r : ℝ) N : ℝ) ≤ ((N / K : ℕ) : ℝ) * L₀ + L₀ := by
    have : (T.outputLen hb0 (r : ℝ) N : ℝ) ≤ ((N / K + 1 : ℕ) : ℝ) * L₀ := by exact_mod_cast hout_le
    push_cast at this; linarith
  calc (T.outputLen hb0 (r : ℝ) N : ℝ)
      ≤ ((N / K : ℕ) : ℝ) * L₀ + L₀ := hout_real
    _ ≤ ((N : ℝ) / K) * L₀ + L₀ := by gcongr
    _ = ((L₀ : ℝ) / K) * N + L₀ := by ring
    _ ≤ (ε / 2) * N + (ε / 2) * N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    _ = ε * N := by ring

end RationalCompression

end Real
