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

section MealyProof

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

/-- The length-`k` output block produced by `T` starting in state `p` while reading `u`. -/
private def mealyWord {Q : Type*} (T : MealyTransducer b Q) (p : Q) {k : ℕ}
    (u : Fin k → Fin b) : Fin k → Fin b :=
  fun j ↦
    T.out (T.toDFA.evalFrom p
      (List.ofFn fun i : Fin j.val ↦ u ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)) (u j)

private lemma mealyWord_bijective {Q : Type*} (T : MealyTransducer b Q)
    (hbij : T.IsOutputBijective) :
    ∀ (k : ℕ) (p : Q), Function.Bijective (mealyWord T p (k := k)) := by
  intro k
  induction k with
  | zero =>
    intro p
    refine ⟨fun u v _ ↦ funext fun i ↦ Fin.elim0 i, fun w ↦ ⟨w, funext fun i ↦ Fin.elim0 i⟩⟩
  | succ k ih =>
    intro p
    rw [← Finite.injective_iff_bijective]
    intro u v huv
    have h0 : T.out p (u 0) = T.out p (v 0) := by
      have := congrFun huv 0
      simpa [mealyWord] using this
    have hu0 : u 0 = v 0 := (hbij p).1 h0
    have htail : mealyWord T (T.step p (u 0)) (fun i : Fin k ↦ u i.succ) =
        mealyWord T (T.step p (u 0)) (fun i : Fin k ↦ v i.succ) := by
      funext j
      have hsucc := congrFun huv j.succ
      have hof : ∀ (w : Fin (k + 1) → Fin b),
          (List.ofFn fun i : Fin j.succ.val ↦ w ⟨i.val, Nat.lt_trans i.isLt j.succ.isLt⟩) =
          w 0 :: List.ofFn fun i : Fin j.val ↦
            w (⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ : Fin k).succ := fun w ↦ by
        apply List.ext_getElem
        · simp
        · intro i _ _
          cases i <;> simp
      simp only [mealyWord] at hsucc ⊢
      rw [hof u, hof v, DFA.evalFrom_cons, DFA.evalFrom_cons] at hsucc
      change T.out (T.toDFA.evalFrom (T.step p (u 0))
        (List.ofFn fun i : Fin j.val ↦ u (⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ : Fin k).succ))
        (u j.succ) =
        T.out (T.toDFA.evalFrom (T.step p (v 0))
          (List.ofFn fun i : Fin j.val ↦ v (⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ : Fin k).succ))
          (v j.succ) at hsucc
      rw [← hu0] at hsucc
      exact hsucc
    have hrest : (fun i : Fin k ↦ u i.succ) = (fun i : Fin k ↦ v i.succ) :=
      (ih (T.step p (u 0))).1 htail
    funext i
    refine Fin.cases hu0 (fun j ↦ congrFun hrest j) i

/-- Local snake automaton with lookahead buffer of length `n ≥ 1` on `Q × (Fin n → Fin b)`. -/
private def mSnakeDFA {Q : Type*} (M : DFA (Fin b) Q) (n : ℕ) (hn : 1 ≤ n)
    (initBuf : Fin n → Fin b) : DFA (Fin b) (Q × (Fin n → Fin b)) where
  step pu a :=
    (M.step pu.1 (pu.2 ⟨0, by omega⟩),
      fun j : Fin n ↦ if h : j.val + 1 < n then pu.2 ⟨j.val + 1, h⟩ else a)
  start := (M.start, initBuf)
  accept := Set.univ

private lemma mSnakeDFA_evalFrom_spec {Q : Type*} (M : DFA (Fin b) Q) {n : ℕ} (hn : 1 ≤ n)
    (initBuf : Fin n → Fin b) (p : Q) (u : Fin n → Fin b) (v : List (Fin b)) :
    (mSnakeDFA M n hn initBuf).evalFrom (p, u) v =
      (M.evalFrom p ((List.ofFn u ++ v).take v.length),
        fun j : Fin n ↦ (List.ofFn u ++ v)[v.length + j.val]'(by simp; omega)) := by
  induction v generalizing p u with
  | nil =>
    ext <;> simp
  | cons a v ih =>
    have hstep_eq : (mSnakeDFA M n hn initBuf).evalFrom (p, u) (a :: v) =
        (mSnakeDFA M n hn initBuf).evalFrom
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

private lemma mSnakeDFA_stronglyConnected {Q : Type*} (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M) {n : ℕ} (hn : 1 ≤ n) (initBuf : Fin n → Fin b) :
    IsStronglyConnected (mSnakeDFA M n hn initBuf) := by
  rintro ⟨p₁, u₁⟩ ⟨p₂, u₂⟩
  obtain ⟨v, hv⟩ := hconn (M.evalFrom p₁ (List.ofFn u₁)) p₂
  refine ⟨v ++ List.ofFn u₂, ?_⟩
  rw [mSnakeDFA_evalFrom_spec]
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

private lemma mSnakeDFA_stationary {Q : Type*} [Fintype Q] (hb : 0 < b) (M : DFA (Fin b) Q)
    {n : ℕ} (hn : 1 ≤ n) (initBuf : Fin n → Fin b) {μ : Q → ℝ} (hμ : IsStationary M μ) :
    IsStationary (mSnakeDFA M n hn initBuf)
      (fun pu : Q × (Fin n → Fin b) ↦ μ pu.1 / (b : ℝ) ^ n) := by
  classical
  constructor
  · refine ⟨fun pu ↦ div_nonneg (hμ.1.1 pu.1) (by positivity), ?_⟩
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, mul_div_cancel₀ _ (by positivity : (b : ℝ) ^ n ≠ 0), hμ.1.2]
  · rintro ⟨q, w⟩
    have hstep_snake : ∀ pu : Q × (Fin n → Fin b),
        stepProb (mSnakeDFA M n hn initBuf) 1 pu (q, w) =
          ((Finset.univ.filter fun a : Fin b ↦
            (mSnakeDFA M n hn initBuf).step pu a = (q, w)).card : ℝ) / b := fun pu ↦ by
      rw [stepProb_succ]
      congr 1
      simp_rw [stepProb_zero]
      convert Finset.sum_boole (fun a : Fin b ↦ (mSnakeDFA M n hn initBuf).step pu a = (q, w))
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
          (mSnakeDFA M n hn initBuf).step (p, u) a = (q, w)).card : ℝ) =
        if M.step p (u ⟨0, by omega⟩) = q ∧
            (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j) then 1 else 0 := by
      intro p u
      by_cases hcond : M.step p (u ⟨0, by omega⟩) = q ∧
          (∀ j : Fin n, ∀ hj : j.val + 1 < n, u ⟨j.val + 1, hj⟩ = w j)
      · rw [ite_eq_left_iff.2 fun h ↦ absurd hcond h]
        have hsing : (Finset.univ.filter fun a : Fin b ↦
            (mSnakeDFA M n hn initBuf).step (p, u) a = (q, w)) = {w ⟨n - 1, by omega⟩} := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, mSnakeDFA,
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
            (mSnakeDFA M n hn initBuf).step (p, u) a = (q, w)) = ∅ := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            mSnakeDFA, Prod.mk.injEq, funext_iff]
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
              (mSnakeDFA M n hn initBuf).step (p, u) a = (q, w)).card : ℝ) / b) =
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

private lemma isNormalSeq_mealySeq_of_stronglyConnected {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (T : MealyTransducer b Q) (hbij : T.IsOutputBijective)
    (hconn : IsStronglyConnected T.toDFA) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Nonempty Q := ⟨T.start⟩
  have hb0 : 0 < b := by omega
  obtain ⟨μ, hμ, _, _⟩ := exists_unique_stationary_and_tendsto_cesaro hb0 T.toDFA hconn
  intro k w
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [pow_zero, inv_one]
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hfilt : ((Finset.range N).filter fun i ↦
        ∀ j : Fin 0, mealySeq b hb0 T x (i + j.val) = (w j : ℕ)) = Finset.range N := by
      ext i; simp
    rw [hfilt, Finset.card_range, div_self (by positivity : (N : ℝ) ≠ 0)]
  · have hk1 : 1 ≤ k := hk_pos
    let initBuf : Fin k → Fin b := fun j ↦ ⟨digit b x j.val, digit_lt hb0 x j.val⟩
    let Ms := mSnakeDFA T.toDFA k hk1 initBuf
    have hMs_conn : IsStronglyConnected Ms := mSnakeDFA_stronglyConnected T.toDFA hconn hk1 initBuf
    have hMs_stat := mSnakeDFA_stationary hb0 T.toDFA hk1 initBuf hμ
    have hxk : IsNormalIn b (x * (b : ℝ) ^ k) := (isNormalIn_mul_pow_iff k).2 hx
    have hMs_state : ∀ t : ℕ,
        Ms.eval (digitPrefix b hb0 (x * (b : ℝ) ^ k) t) =
          (T.toDFA.eval (digitPrefix b hb0 x t),
            fun j : Fin k ↦ ⟨digit b x (t + j.val), digit_lt hb0 x _⟩) := by
      intro t
      have hspec := mSnakeDFA_evalFrom_spec T.toDFA hk1 initBuf T.start initBuf
        (digitPrefix b hb0 (x * (b : ℝ) ^ k) t)
      change (mSnakeDFA T.toDFA k hk1 initBuf).evalFrom (T.start, initBuf)
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
      Finset.univ.filter fun pu ↦ mealyWord T pu.1 pu.2 = w
    -- Count of matching positions equals sum of `Ms` state counts over `goodPairs`
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
          simp only [mealyWord, mealySeq] at hj ⊢
          rw [digitPrefix_add hb0 x t j.val, DFA.eval, DFA.evalFrom_of_append] at hj
          exact hj
        · rintro ⟨pu, hpu, htN, heq⟩
          refine ⟨htN, fun j ↦ ?_⟩
          have hj := congrArg Fin.val (congrFun hpu j)
          rw [← heq] at hj
          simp only [mealyWord, mealySeq] at hj ⊢
          rw [digitPrefix_add hb0 x t j.val, DFA.eval, DFA.evalFrom_of_append]
          exact hj
      · intro p₁ _ p₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    -- Evaluate `∑ pu ∈ goodPairs, μ pu.1 / b ^ k = (b ^ k)⁻¹` via bijectivity of `mealyWord T p`
    have hlim_val : (∑ pu ∈ goodPairs, μ pu.1 / (b : ℝ) ^ k) = ((b : ℝ) ^ k)⁻¹ := by
      dsimp only [goodPairs]
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      have hinner : ∀ p : Q,
          (∑ u : Fin k → Fin b, if mealyWord T p u = w then μ p / (b : ℝ) ^ k else 0) =
          μ p / (b : ℝ) ^ k := fun p ↦ by
        obtain ⟨u₀, hu₀⟩ := (mealyWord_bijective T hbij k p).2 w
        rw [Finset.sum_eq_single u₀]
        · simp [hu₀]
        · intro u _ hne
          have : mealyWord T p u ≠ w := fun h ↦
            hne ((mealyWord_bijective T hbij k p).1 (h.trans hu₀.symm))
          simp [this]
        · intro h; exact absurd (Finset.mem_univ u₀) h
      simp_rw [hinner, ← Finset.sum_div, hμ.1.2, one_div]
    have hsum := tendsto_finset_sum_real goodPairs
      (fun pu N ↦ (dfaStateCount b hb0 Ms (x * (b : ℝ) ^ k) pu N : ℝ) / N)
      (fun pu ↦ μ pu.1 / (b : ℝ) ^ k)
      fun pu _ ↦ tendsto_dfa_stateFreq hb Ms hMs_conn hMs_stat hxk pu
    rw [hlim_val] at hsum
    refine hsum.congr fun N ↦ ?_
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hcount_eq N]

private def MIsRecurrent {Q : Type*} (M : DFA (Fin b) Q) (p : Q) : Prop :=
  ∀ q : Q, (∃ u : List (Fin b), M.evalFrom p u = q) → ∃ v : List (Fin b), M.evalFrom q v = p

private lemma mIsRecurrent_evalFrom {Q : Type*} (M : DFA (Fin b) Q) {p : Q}
    (hp : MIsRecurrent M p) (u : List (Fin b)) : MIsRecurrent M (M.evalFrom p u) := by
  intro q ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hp q ⟨u ++ v, by rw [DFA.evalFrom_of_append, hv]⟩
  exact ⟨w ++ u, by rw [DFA.evalFrom_of_append, hw]⟩

private lemma exists_word_mIsRecurrent {Q : Type*} [Finite Q] (M : DFA (Fin b) Q) (p : Q) :
    ∃ u : List (Fin b), MIsRecurrent M (M.evalFrom p u) := by
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
  have heq : reach r = reach (M.evalFrom p u) :=
    Finset.eq_of_subset_of_card_le hsub (hq_min r hr_mem)
  have hback : M.evalFrom p u ∈ reach r := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨[], rfl⟩⟩
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hback
  exact hback

private lemma exists_universal_mRecurrent_word {Q : Type*} [Finite Q] (M : DFA (Fin b) Q) :
    ∃ W : List (Fin b), ∀ p : Q, MIsRecurrent M (M.evalFrom p W) := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  suffices h : ∀ S : Finset Q, ∃ W : List (Fin b), ∀ p ∈ S, MIsRecurrent M (M.evalFrom p W) by
    obtain ⟨W, hW⟩ := h Finset.univ
    exact ⟨W, fun p ↦ hW p (Finset.mem_univ p)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨[], fun _ h ↦ absurd h (Finset.notMem_empty _)⟩
  | insert p S _ ih =>
    obtain ⟨W₁, hW₁⟩ := ih
    obtain ⟨W₂, hW₂⟩ := exists_word_mIsRecurrent M (M.evalFrom p W₁)
    refine ⟨W₁ ++ W₂, fun q hq ↦ ?_⟩
    rw [DFA.evalFrom_of_append]
    rcases Finset.mem_insert.1 hq with rfl | hqS
    · exact hW₂
    · exact mIsRecurrent_evalFrom M (hW₁ q hqS) W₂

private lemma isNormalSeq_shift_transducer {d : ℕ → ℕ} (s : ℕ)
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
            have hico : (Finset.Ico (N - s) N).card ≤ s := by simp; omega
            exact Nat.add_le_add Finset.card_image_le hico
        _ ≤ A.card + s := Nat.add_le_add_right (Finset.card_filter_le _ _) s
    rw [abs_le]
    have hA' : (A.card : ℝ) ≤ B.card + s := by exact_mod_cast hA_le
    have hB' : (B.card : ℝ) ≤ A.card + s := by exact_mod_cast hB_le
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

end MealyProof

/-! ### Main theorems for output-bijective Mealy transducers -/

/-- **Output-bijective finite-state transducers preserve normality (digit sequences)**:
feeding a base-`b` normal number `x` into any finite-state Mealy transducer `T` whose output map
`T.out q : Fin b → Fin b` is bijective at every state `q` yields a base-`b` normal digit
sequence. -/
theorem isNormalSeq_mealySeq {Q : Type*} [Finite Q] (hb : 2 ≤ b) (T : MealyTransducer b Q)
    (hbij : T.IsOutputBijective) (hx : IsNormalIn b x) :
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  classical
  have hb0 : 0 < b := by omega
  obtain ⟨W, hW⟩ := exists_universal_mRecurrent_word T.toDFA
  let wVec : Fin W.length → Fin b := fun j ↦ W[j.val]'j.isLt
  obtain ⟨i₀, hi₀⟩ := hx.isDisjunctiveIn W.length wVec
  set t₀ : ℕ := i₀ + W.length
  set p₀ : Q := T.toDFA.eval (digitPrefix b hb0 x t₀)
  have hp₀_rec : MIsRecurrent T.toDFA p₀ := by
    have hpre : digitPrefix b hb0 x t₀ = digitPrefix b hb0 x i₀ ++ W := by
      rw [digitPrefix_add hb0 x i₀ W.length]
      congr 1
      apply List.ext_getElem
      · simp
      · intro j hj₁ _
        simp only [List.getElem_ofFn]
        exact Fin.ext (by simpa [wVec] using hi₀ ⟨j, by simpa using hj₁⟩)
    change MIsRecurrent T.toDFA (T.toDFA.eval (digitPrefix b hb0 x t₀))
    rw [hpre, DFA.eval, DFA.evalFrom_of_append]
    exact hW (T.toDFA.evalFrom T.toDFA.start (digitPrefix b hb0 x i₀))
  let C : Type _ := {q : Q // ∃ u : List (Fin b), T.toDFA.evalFrom p₀ u = q}
  have hC_step : ∀ (q : C) (a : Fin b),
      ∃ u : List (Fin b), T.toDFA.evalFrom p₀ u = T.step q.val a := by
    rintro ⟨q, u, hu⟩ a
    exact ⟨u ++ [a], by rw [DFA.evalFrom_append_singleton, hu]; rfl⟩
  let Tc : MealyTransducer b C :=
    { step := fun q a ↦ ⟨T.step q.val a, hC_step q a⟩
      start := ⟨p₀, [], rfl⟩
      out := fun q a ↦ T.out q.val a }
  have hTc_eval : ∀ (q : C) (u : List (Fin b)),
      (Tc.toDFA.evalFrom q u).val = T.toDFA.evalFrom q.val u := by
    intro q u
    induction u generalizing q with
    | nil => rfl
    | cons a u ih => exact ih ⟨T.step q.val a, hC_step q a⟩
  have hTc_conn : IsStronglyConnected Tc.toDFA := by
    rintro ⟨q₁, u₁, hu₁⟩ ⟨q₂, u₂, hu₂⟩
    obtain ⟨v, hv⟩ := hp₀_rec q₁ ⟨u₁, hu₁⟩
    refine ⟨v ++ u₂, Subtype.ext ?_⟩
    rw [hTc_eval, DFA.evalFrom_of_append, hv, hu₂]
  have hTc_bij : Tc.IsOutputBijective := fun q ↦ hbij q.val
  set x' : ℝ := x * (b : ℝ) ^ t₀
  have hx' : IsNormalIn b x' := (isNormalIn_mul_pow_iff t₀).2 hx
  have hnorm' : IsNormalSeq b (mealySeq b hb0 Tc x') :=
    isNormalSeq_mealySeq_of_stronglyConnected hb Tc hTc_bij hTc_conn hx'
  have hseq_eq : (fun n ↦ mealySeq b hb0 T x (n + t₀)) = mealySeq b hb0 Tc x' := by
    funext n
    simp only [mealySeq, Tc, x']
    have hpre : digitPrefix b hb0 x (n + t₀) =
        digitPrefix b hb0 x t₀ ++ digitPrefix b hb0 (x * (b : ℝ) ^ t₀) n := by
      rw [add_comm, digitPrefix_add hb0 x t₀ n]
      congr 1
      apply List.ext_getElem
      · simp [digitPrefix]
      · intro j _ _
        simp only [digitPrefix, List.getElem_ofFn]
        exact Fin.ext (digit_add b x t₀ j)
    have hstate : T.toDFA.eval (digitPrefix b hb0 x (n + t₀)) =
        (Tc.toDFA.eval (digitPrefix b hb0 (x * (b : ℝ) ^ t₀) n)).val := by
      rw [hpre, DFA.eval, DFA.evalFrom_of_append, DFA.eval, hTc_eval]
      rfl
    have hdig : (⟨digit b x (n + t₀), digit_lt hb0 x (n + t₀)⟩ : Fin b) =
        ⟨digit b (x * (b : ℝ) ^ t₀) n, digit_lt hb0 _ n⟩ := by
      apply Fin.ext
      dsimp only
      rw [add_comm, digit_add]
    rw [hstate, hdig]
  exact isNormalSeq_shift_transducer t₀ (hseq_eq.symm ▸ hnorm')

/-- **Output-bijective finite-state transducers preserve normality (real numbers)**. -/
theorem isNormalIn_mealyReal {Q : Type*} [Finite Q] (hb : 2 ≤ b) (T : MealyTransducer b Q)
    (hbij : T.IsOutputBijective) (hx : IsNormalIn b x) :
    IsNormalIn b (mealyReal b T x) := by
  have hb0 : 0 < b := by omega
  simp only [mealyReal, hb0, ↓reduceDIte]
  exact isNormalIn_ofDigits hb (isNormalSeq_mealySeq hb T hbij hx)

/-- **Stateful additive / autokey stream ciphers preserve normality**:
for any finite state machine `(Q, step, start)` and keystream function `key : Q → Fin b`, adding
`key q_n` modulo `b` to each digit `d_n` preserves base-`b` normality. -/
theorem isNormalSeq_statefulAddCipher {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (step : Q → Fin b → Q) (start : Q) (key : Q → Fin b) (hx : IsNormalIn b x) :
    letI : NeZero b := ⟨by omega⟩
    let T : MealyTransducer b Q := { step := step, start := start, out := fun q a ↦ a + key q }
    IsNormalSeq b (mealySeq b (by omega) T x) := by
  have : NeZero b := ⟨by omega⟩
  let T : MealyTransducer b Q := { step := step, start := start, out := fun q a ↦ a + key q }
  exact isNormalSeq_mealySeq hb T (fun q ↦ (Equiv.addRight (key q)).bijective) hx

/-- **Stateful additive / autokey stream ciphers preserve normality (real numbers)**. -/
theorem isNormalIn_statefulAddCipher {Q : Type*} [Finite Q] (hb : 2 ≤ b)
    (step : Q → Fin b → Q) (start : Q) (key : Q → Fin b) (hx : IsNormalIn b x) :
    letI : NeZero b := ⟨by omega⟩
    let T : MealyTransducer b Q := { step := step, start := start, out := fun q a ↦ a + key q }
    IsNormalIn b (mealyReal b T x) := by
  have : NeZero b := ⟨by omega⟩
  let T : MealyTransducer b Q := { step := step, start := start, out := fun q a ↦ a + key q }
  exact isNormalIn_mealyReal hb T (fun q ↦ (Equiv.addRight (key q)).bijective) hx

/-- **Running prefix sums mod `b` preserve normality (digit sequences)**:
the unbounded-memory stateful map `n ↦ (∑ i ∈ Finset.range (n + 1), digit b x i) % b` preserves
base-`b` normality. -/
theorem isNormalSeq_runningSum (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalSeq b (runningSumSeq b x) := by
  have hb0 : 0 < b := by omega
  have : NeZero b := ⟨by omega⟩
  let T : MealyTransducer b (Fin b) :=
    { step := fun s a ↦ s + a
      start := 0
      out := fun s a ↦ s + a }
  have hbij : T.IsOutputBijective := fun s ↦ (Equiv.addLeft s).bijective
  have heval : ∀ n : ℕ, (T.toDFA.eval (digitPrefix b hb0 x n) : ℕ) =
      (∑ i ∈ Finset.range n, digit b x i) % b := by
    intro n
    induction n with
    | zero =>
      simp [T, MealyTransducer.toDFA, DFA.eval, digitPrefix]
    | succ n ih =>
      have hpre : digitPrefix b hb0 x (n + 1) =
          digitPrefix b hb0 x n ++ [⟨digit b x n, digit_lt hb0 x n⟩] := by
        rw [digitPrefix_add hb0 x n 1]
        simp [digitPrefix, List.ofFn_succ]
      rw [hpre, DFA.eval, DFA.evalFrom_append_singleton]
      change ((T.toDFA.eval (digitPrefix b hb0 x n) +
        ⟨digit b x n, digit_lt hb0 x n⟩ : Fin b) : ℕ) =
        (∑ i ∈ Finset.range (n + 1), digit b x i) % b
      rw [Fin.val_add, ih, Finset.sum_range_succ, Nat.mod_add_mod]
  have hseq : mealySeq b hb0 T x = runningSumSeq b x := by
    funext n
    simp only [mealySeq, runningSumSeq, T, Fin.val_add, heval n, Finset.sum_range_succ,
      Nat.mod_add_mod]
  rw [← hseq]
  exact isNormalSeq_mealySeq hb T hbij hx

/-- **Running prefix sums mod `b` preserve normality (real numbers)**. -/
theorem isNormalIn_runningSum (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalIn b (runningSumReal b x) := by
  have hb0 : 0 < b := by omega
  simp only [runningSumReal, hb0, ↓reduceDIte]
  exact isNormalIn_ofDigits hb (isNormalSeq_runningSum hb hx)

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
  dsimp only
  have hb0 : 0 < b := by omega
  obtain ⟨x, hx, h0⟩ := exists_isNormalIn_digit_eq_zero_on_density_zero hb (· ∈ S) hS
  have hset : regularSelectSet b ({w : List (Fin b) | w.length ∈ S} : Language (Fin b)) x = S := by
    ext n
    change (∃ h : 0 < b, (digitPrefix b h x n).length ∈ S) ↔ n ∈ S
    simp only [digitPrefix, List.length_ofFn]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hb0, h⟩⟩
  have hinf_mem : {n : ℕ | n ∈ S}.Infinite := hinf
  refine ⟨x, hx, hset.symm ▸ hinf, not_isNormalSeq_of_forall_eq_zero hb fun n ↦ ?_⟩
  simp only [regularSelectSeq, hset]
  exact h0 _ (Nat.nth_mem_of_infinite hinf_mem n)

/-- Selecting digits whose preceding prefix has square length destroys normality for some base-`b`
normal number. -/
theorem exists_isNormalIn_not_isNormalSeq_sqLengthSelect (hb : 2 ≤ b) :
    let L : Language (Fin b) := {w | ∃ k : ℕ, w.length = k ^ 2}
    ∃ x : ℝ, IsNormalIn b x ∧ (regularSelectSet b L x).Infinite ∧
      ¬ IsNormalSeq b (regularSelectSeq b L x) := by
  dsimp only
  classical
  have hb0 : 0 < b := by omega
  obtain ⟨x, hx, hnot⟩ := exists_isNormalIn_not_isNormalSeq_sq hb
  have hset : regularSelectSet b ({w : List (Fin b) | ∃ k : ℕ, w.length = k ^ 2} :
      Language (Fin b)) x = Set.range fun k : ℕ ↦ k ^ 2 := by
    ext n
    change (∃ h : 0 < b, ∃ k : ℕ, (digitPrefix b h x n).length = k ^ 2) ↔
      n ∈ Set.range fun k : ℕ ↦ k ^ 2
    simp only [digitPrefix, List.length_ofFn, Set.mem_range]
    exact ⟨fun ⟨_, k, hk⟩ ↦ ⟨k, hk.symm⟩, fun ⟨k, hk⟩ ↦ ⟨hb0, k, hk.symm⟩⟩
  have hmono : StrictMono fun k : ℕ ↦ k ^ 2 := fun i j hij ↦
    Nat.pow_lt_pow_left hij (by norm_num)
  have hinf : (Set.range fun k : ℕ ↦ k ^ 2).Infinite :=
    Set.infinite_range_of_injective hmono.injective
  have hnth : ∀ n : ℕ, Nat.nth (· ∈ Set.range fun k : ℕ ↦ k ^ 2) n = n ^ 2 := by
    intro n
    have hmem : n ^ 2 ∈ Set.range fun k : ℕ ↦ k ^ 2 := ⟨n, rfl⟩
    have hcnt : Nat.count (· ∈ Set.range fun k : ℕ ↦ k ^ 2) (n ^ 2) = n := by
      rw [Nat.count_eq_card_filter_range]
      have heq : ((Finset.range (n ^ 2)).filter fun m ↦ m ∈ Set.range fun k : ℕ ↦ k ^ 2) =
          (Finset.range n).image fun k ↦ k ^ 2 := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hm, k, rfl⟩
          exact ⟨k, hmono.lt_iff_lt.1 hm, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨hmono hk, k, rfl⟩
      rw [heq, Finset.card_image_of_injective _ hmono.injective, Finset.card_range]
    conv_lhs => rw [← hcnt]
    exact Nat.nth_count hmem
  have hseq : regularSelectSeq b ({w : List (Fin b) | ∃ k : ℕ, w.length = k ^ 2} :
      Language (Fin b)) x = fun n ↦ digit b x (n ^ 2) := by
    funext n
    simp only [regularSelectSeq, hset, hnth n]
  exact ⟨x, hx, hset.symm ▸ hinf, hseq.symm ▸ hnot⟩

/-- Direct corollary of Agafonov's theorem: the square-length language
`{w : List (Fin b) | ∃ k, w.length = k ^ 2}` is not regular for any alphabet size `b ≥ 2`. -/
theorem not_isRegular_sqLength (hb : 2 ≤ b) :
    ¬ Language.IsRegular ({w : List (Fin b) | ∃ k : ℕ, w.length = k ^ 2} : Language (Fin b)) := by
  intro hreg
  obtain ⟨x, hx, hinf, hnot⟩ := exists_isNormalIn_not_isNormalSeq_sqLengthSelect hb
  exact hnot (isNormalSeq_regularSelect hb hreg hx hinf)

/-- Selecting digits whose preceding prefix has power-of-two length destroys normality for some
base-`b` normal number. -/
theorem exists_isNormalIn_not_isNormalSeq_powTwoLengthSelect (hb : 2 ≤ b) :
    let L : Language (Fin b) := {w | ∃ k : ℕ, w.length = 2 ^ k}
    ∃ x : ℝ, IsNormalIn b x ∧ (regularSelectSet b L x).Infinite ∧
      ¬ IsNormalSeq b (regularSelectSeq b L x) := by
  dsimp only
  classical
  have hb0 : 0 < b := by omega
  obtain ⟨x, hx, hnot⟩ := exists_isNormalIn_not_isNormalSeq_two_pow hb
  have hset : regularSelectSet b ({w : List (Fin b) | ∃ k : ℕ, w.length = 2 ^ k} :
      Language (Fin b)) x = Set.range fun k : ℕ ↦ 2 ^ k := by
    ext n
    change (∃ h : 0 < b, ∃ k : ℕ, (digitPrefix b h x n).length = 2 ^ k) ↔
      n ∈ Set.range fun k : ℕ ↦ 2 ^ k
    simp only [digitPrefix, List.length_ofFn, Set.mem_range]
    exact ⟨fun ⟨_, k, hk⟩ ↦ ⟨k, hk.symm⟩, fun ⟨k, hk⟩ ↦ ⟨hb0, k, hk.symm⟩⟩
  have hmono : StrictMono fun k : ℕ ↦ 2 ^ k := fun _ _ hij ↦
    Nat.pow_lt_pow_right (by norm_num) hij
  have hinf : (Set.range fun k : ℕ ↦ 2 ^ k).Infinite :=
    Set.infinite_range_of_injective hmono.injective
  have hnth : ∀ n : ℕ, Nat.nth (· ∈ Set.range fun k : ℕ ↦ 2 ^ k) n = 2 ^ n := by
    intro n
    have hmem : 2 ^ n ∈ Set.range fun k : ℕ ↦ 2 ^ k := ⟨n, rfl⟩
    have hcnt : Nat.count (· ∈ Set.range fun k : ℕ ↦ 2 ^ k) (2 ^ n) = n := by
      rw [Nat.count_eq_card_filter_range]
      have heq : ((Finset.range (2 ^ n)).filter fun m ↦ m ∈ Set.range fun k : ℕ ↦ 2 ^ k) =
          (Finset.range n).image fun k ↦ 2 ^ k := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hm, k, rfl⟩
          exact ⟨k, hmono.lt_iff_lt.1 hm, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨hmono hk, k, rfl⟩
      rw [heq, Finset.card_image_of_injective _ hmono.injective, Finset.card_range]
    conv_lhs => rw [← hcnt]
    exact Nat.nth_count hmem
  have hseq : regularSelectSeq b ({w : List (Fin b) | ∃ k : ℕ, w.length = 2 ^ k} :
      Language (Fin b)) x = fun n ↦ digit b x (2 ^ n) := by
    funext n
    simp only [regularSelectSeq, hset, hnth n]
  exact ⟨x, hx, hset.symm ▸ hinf, hseq.symm ▸ hnot⟩

/-- Direct corollary of Agafonov's theorem: the power-of-two-length language
`{w : List (Fin b) | ∃ k, w.length = 2 ^ k}` is not regular for any alphabet size `b ≥ 2`. -/
theorem not_isRegular_powTwoLength (hb : 2 ≤ b) :
    ¬ Language.IsRegular ({w : List (Fin b) | ∃ k : ℕ, w.length = 2 ^ k} : Language (Fin b)) := by
  intro hreg
  obtain ⟨x, hx, hinf, hnot⟩ := exists_isNormalIn_not_isNormalSeq_powTwoLengthSelect hb
  exact hnot (isNormalSeq_regularSelect hb hreg hx hinf)

/-- **Pointwise sharpness of Agafonov's theorem**: for *every* base-`b` normal number `x`, there
exists a (necessarily non-regular) language `L : Language (Fin b)` selecting infinitely many digits
of `x` whose selected subsequence is identically `0` and hence not normal in base `b`. -/
theorem exists_language_not_isNormalSeq_regularSelect (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ∃ L : Language (Fin b), (regularSelectSet b L x).Infinite ∧
      ¬ IsNormalSeq b (regularSelectSeq b L x) := by
  have hb0 : 0 < b := by omega
  obtain ⟨s, hs_mono, _, hs_zero, _⟩ := exists_strictMono_positive_density_digit_eq_zero hb hx
  let L : Language (Fin b) := {w | ∃ k : ℕ, w = digitPrefix b hb0 x (s k)}
  have hset : regularSelectSet b L x = Set.range s := by
    ext n
    change (∃ h : 0 < b, ∃ k : ℕ, digitPrefix b h x n = digitPrefix b hb0 x (s k)) ↔
      n ∈ Set.range s
    simp only [Set.mem_range]
    constructor
    · rintro ⟨_, k, hk⟩
      have hlen := congrArg List.length hk
      simp only [digitPrefix, List.length_ofFn] at hlen
      exact ⟨k, hlen.symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨hb0, k, rfl⟩
  have hinf : (Set.range s).Infinite := Set.infinite_range_of_injective hs_mono.injective
  have hinf_mem : {m : ℕ | m ∈ Set.range s}.Infinite := hinf
  refine ⟨L, hset.symm ▸ hinf, not_isNormalSeq_of_forall_eq_zero hb fun n ↦ ?_⟩
  simp only [regularSelectSeq, hset]
  obtain ⟨k, hk⟩ := Nat.nth_mem_of_infinite hinf_mem n
  rw [← hk]
  exact hs_zero k

end Real
