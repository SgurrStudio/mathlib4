/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.NumberTheory.Normal.DigitOperations

import Mathlib.NumberTheory.Normal.BasePow
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Sequences

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

/-- `M` is strongly connected if every state can reach every other state. -/
def IsStronglyConnected (M : DFA (Fin b) Q) : Prop :=
  ∀ p q : Q, ∃ u : List (Fin b), M.evalFrom p u = q

/-- `t`-step transition probability from `p` to `q` under uniform i.i.d. inputs in `Fin b`. -/
noncomputable def stepProb (M : DFA (Fin b) Q) : ℕ → Q → Q → ℝ
  | 0, p, q => open Classical in if p = q then 1 else 0
  | t + 1, p, q => (∑ a : Fin b, stepProb M t (M.step p a) q) / b

lemma stepProb_zero (M : DFA (Fin b) Q) (p q : Q) :
    stepProb M 0 p q = open Classical in if p = q then 1 else 0 := rfl

lemma stepProb_succ (M : DFA (Fin b) Q) (t : ℕ) (p q : Q) :
    stepProb M (t + 1) p q = (∑ a : Fin b, stepProb M t (M.step p a) q) / b := rfl

private lemma stepProb_nonneg (M : DFA (Fin b) Q) (t : ℕ) (p q : Q) :
    0 ≤ stepProb M t p q := by
  induction t generalizing p with
  | zero =>
    classical
    simp only [stepProb_zero]
    split_ifs <;> norm_num
  | succ t ih =>
    rw [stepProb_succ]
    exact div_nonneg (Finset.sum_nonneg fun a _ ↦ ih (M.step p a)) (Nat.cast_nonneg b)

private lemma stepProb_one_pos_of_step (hb : 0 < b) (M : DFA (Fin b) Q) (p : Q) (a : Fin b) :
    (b : ℝ)⁻¹ ≤ stepProb M 1 p (M.step p a) := by
  classical
  rw [stepProb_succ, div_eq_mul_inv]
  have h1 : (1 : ℝ) ≤ ∑ c : Fin b, stepProb M 0 (M.step p c) (M.step p a) := by
    calc (1 : ℝ) = stepProb M 0 (M.step p a) (M.step p a) := by simp [stepProb_zero]
      _ ≤ ∑ c : Fin b, stepProb M 0 (M.step p c) (M.step p a) :=
          Finset.single_le_sum (fun c _ ↦ stepProb_nonneg M 0 (M.step p c) (M.step p a))
            (Finset.mem_univ a)
  exact le_mul_of_one_le_left (by positivity) h1

private lemma stepProb_le_one (hb : 0 < b) (M : DFA (Fin b) Q) (t : ℕ) (p q : Q) :
    stepProb M t p q ≤ 1 := by
  induction t generalizing p with
  | zero =>
    rw [stepProb_zero]
    split_ifs <;> norm_num
  | succ t ih =>
    rw [stepProb_succ, div_le_one (by positivity : (0 : ℝ) < b)]
    calc ∑ a : Fin b, stepProb M t (M.step p a) q
        ≤ ∑ _a : Fin b, (1 : ℝ) := Finset.sum_le_sum fun a _ ↦ ih (M.step p a)
      _ = b := by simp

variable [Fintype Q]

private lemma continuous_finset_sum_real {ι X : Type*} [TopologicalSpace X] (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    convert h1.add h2 using 1
    ext x
    exact Finset.sum_insert ha

private lemma tendsto_finset_sum_real {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ) (L : ι → ℝ)
    (h : ∀ i ∈ s, Tendsto (g i) atTop (𝓝 (L i))) :
    Tendsto (fun N ↦ ∑ i ∈ s, g i N) atTop (𝓝 (∑ i ∈ s, L i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using h1.add h2

/-- The probability simplex on `Q`: nonnegative functions summing to `1`. -/
def probSimplex (Q : Type*) [Fintype Q] : Set (Q → ℝ) :=
  {μ : Q → ℝ | (∀ q, 0 ≤ μ q) ∧ ∑ q : Q, μ q = 1}

private lemma isCompact_probSimplex (Q : Type*) [Fintype Q] : IsCompact (probSimplex Q) := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Q ↦ Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hsub : probSimplex Q ⊆ Set.pi Set.univ fun _ : Q ↦ Set.Icc (0 : ℝ) 1 := by
    intro μ hμ q _
    refine ⟨hμ.1 q, ?_⟩
    calc μ q ≤ ∑ r : Q, μ r := Finset.single_le_sum (fun r _ ↦ hμ.1 r) (Finset.mem_univ q)
      _ = 1 := hμ.2
  have hclosed : IsClosed (probSimplex Q) := by
    have h1 : IsClosed {μ : Q → ℝ | ∀ q, 0 ≤ μ q} := by
      have : {μ : Q → ℝ | ∀ q, 0 ≤ μ q} = ⋂ q : Q, (fun μ : Q → ℝ ↦ μ q) ⁻¹' Set.Ici 0 := by
        ext μ; simp
      rw [this]
      exact isClosed_iInter fun q ↦ isClosed_Ici.preimage (continuous_apply q)
    have h2 : IsClosed {μ : Q → ℝ | ∑ q : Q, μ q = 1} :=
      isClosed_eq (continuous_finset_sum_real _ _ fun q _ ↦ continuous_apply q) continuous_const
    exact h1.inter h2
  exact hbox.of_isClosed_subset hclosed hsub

/-- `μ` is a stationary probability distribution for `M` under uniform inputs in `Fin b`. -/
def IsStationary (M : DFA (Fin b) Q) (μ : Q → ℝ) : Prop :=
  μ ∈ probSimplex Q ∧ ∀ q : Q, (∑ p : Q, μ p * stepProb M 1 p q) = μ q

private lemma sum_stepProb (hb : 0 < b) (M : DFA (Fin b) Q) (t : ℕ) (p : Q) :
    ∑ q : Q, stepProb M t p q = 1 := by
  induction t generalizing p with
  | zero =>
    classical
    simp [stepProb_zero]
  | succ t ih =>
    simp_rw [stepProb_succ, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp [ih, div_self (by positivity : (b : ℝ) ≠ 0)]

private lemma stepProb_add (M : DFA (Fin b) Q) (s t : ℕ) (p q : Q) :
    stepProb M (s + t) p q = ∑ r : Q, stepProb M s p r * stepProb M t r q := by
  induction s generalizing p with
  | zero =>
    classical
    simp [stepProb_zero]
  | succ s ih =>
    rw [Nat.succ_add, stepProb_succ]
    simp_rw [ih, stepProb_succ, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_comm

private lemma stepProb_eval_sum (_hb : 0 < b) (M : DFA (Fin b) Q) (n : ℕ) (p : Q) (g : Q → ℝ) :
    (∑ u : Fin n → Fin b, g (M.evalFrom p (List.ofFn u))) / (b : ℝ) ^ n =
      ∑ r : Q, stepProb M n p r * g r := by
  induction n generalizing p with
  | zero =>
    classical
    simp [stepProb_zero, Unique.eq_default]
  | succ n ih =>
    have hsplit : (∑ u : Fin (n + 1) → Fin b, g (M.evalFrom p (List.ofFn u))) =
        ∑ a : Fin b, ∑ v : Fin n → Fin b, g (M.evalFrom (M.step p a) (List.ofFn v)) := by
      let e : (Fin (n + 1) → Fin b) ≃ Fin b × (Fin n → Fin b) :=
        { toFun := fun u ↦ (u 0, fun i ↦ u i.succ)
          invFun := fun p ↦ Fin.cons p.1 p.2
          left_inv := fun u ↦ by funext i; refine Fin.cases ?_ ?_ i <;> simp
          right_inv := fun ⟨a, v⟩ ↦ by ext <;> simp }
      rw [Fintype.sum_equiv e (fun u ↦ g (M.evalFrom p (List.ofFn u)))
        (fun q ↦ g (M.evalFrom (M.step p q.1) (List.ofFn q.2)))
        (fun u ↦ by rw [List.ofFn_succ, DFA.evalFrom_cons]; rfl), Fintype.sum_prod_type]
    rw [hsplit, pow_succ, ← div_div, Finset.sum_div]
    simp_rw [ih, stepProb_succ, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_comm

/-- Cesàro average of the first `N + 1` rows of `stepProb` starting from `p`. -/
noncomputable def cesaroProb (M : DFA (Fin b) Q) (p : Q) (N : ℕ) (q : Q) : ℝ :=
  (∑ t ∈ Finset.range (N + 1), stepProb M t p q) / (N + 1 : ℝ)

private lemma cesaroProb_mem_probSimplex (hb : 0 < b) (M : DFA (Fin b) Q) (p : Q) (N : ℕ) :
    cesaroProb M p N ∈ probSimplex Q := by
  refine ⟨fun q ↦ div_nonneg (Finset.sum_nonneg fun t _ ↦ stepProb_nonneg M t p q) (by positivity),
    ?_⟩
  simp_rw [cesaroProb, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [sum_stepProb hb M]
  simp [div_self (by positivity : ((N : ℝ) + 1) ≠ 0)]

private lemma cesaroProb_step_sub (hb : 0 < b) (M : DFA (Fin b) Q) (p : Q) (N : ℕ) (q : Q) :
    |(∑ r : Q, cesaroProb M p N r * stepProb M 1 r q) - cesaroProb M p N q| ≤
      2 / (N + 1 : ℝ) := by
  have h1 : ∑ r : Q, cesaroProb M p N r * stepProb M 1 r q =
      (∑ t ∈ Finset.range (N + 1), stepProb M (t + 1) p q) / (N + 1 : ℝ) := by
    simp_rw [cesaroProb, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [← stepProb_add]
  rw [h1, cesaroProb, ← sub_div]
  have htel : (∑ t ∈ Finset.range (N + 1), stepProb M (t + 1) p q) -
      (∑ t ∈ Finset.range (N + 1), stepProb M t p q) =
      stepProb M (N + 1) p q - stepProb M 0 p q := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t ↦ stepProb M t p q)]
  rw [htel, abs_div, abs_of_pos (by positivity : (0 : ℝ) < N + 1)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h00 := stepProb_nonneg M 0 p q
  have h01 := stepProb_le_one hb M 0 p q
  have h10 := stepProb_nonneg M (N + 1) p q
  have h11 := stepProb_le_one hb M (N + 1) p q
  rw [abs_le]
  constructor <;> linarith

private lemma isStationary_of_tendsto_cesaro (hb : 0 < b) (M : DFA (Fin b) Q) (p : Q)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {μ : Q → ℝ}
    (hlim : Tendsto (fun k ↦ cesaroProb M p (φ k)) atTop (𝓝 μ)) :
    IsStationary M μ := by
  have hmem : μ ∈ probSimplex Q :=
    (isCompact_probSimplex Q).isClosed.mem_of_tendsto hlim
      (Eventually.of_forall fun k ↦ cesaroProb_mem_probSimplex hb M p (φ k))
  refine ⟨hmem, fun q ↦ ?_⟩
  have hcoord : ∀ r, Tendsto (fun k ↦ cesaroProb M p (φ k) r) atTop (𝓝 (μ r)) :=
    fun r ↦ (continuous_apply r).continuousAt.tendsto.comp hlim
  have hsub : Tendsto (fun k ↦
      |(∑ r : Q, cesaroProb M p (φ k) r * stepProb M 1 r q) - cesaroProb M p (φ k) q|)
      atTop (𝓝 |(∑ r : Q, μ r * stepProb M 1 r q) - μ q|) :=
    ((tendsto_finset_sum_real Finset.univ (fun r k ↦ cesaroProb M p (φ k) r * stepProb M 1 r q)
      (fun r ↦ μ r * stepProb M 1 r q) fun r _ ↦ (hcoord r).mul_const _).sub (hcoord q)).abs
  have hzero : Tendsto (fun k ↦
      |(∑ r : Q, cesaroProb M p (φ k) r * stepProb M 1 r q) - cesaroProb M p (φ k) q|)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ abs_nonneg _) (fun k ↦ cesaroProb_step_sub hb M p (φ k) q) ?_
    have h1 : Tendsto (fun n : ℕ ↦ (2 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
      exact this.comp (tendsto_add_atTop_nat 1) |>.congr fun n ↦ by simp
    exact h1.comp hφ.tendsto_atTop
  have heq := tendsto_nhds_unique hsub hzero
  exact sub_eq_zero.1 (abs_eq_zero.1 heq)

lemma stationary_pos (hb : 0 < b) (M : DFA (Fin b) Q) (hconn : IsStronglyConnected M)
    {μ : Q → ℝ} (hμ : IsStationary M μ) (q : Q) : 0 < μ q := by
  have hnn : ∀ r, 0 ≤ μ r := hμ.1.1
  have hsum : ∑ r : Q, μ r = 1 := hμ.1.2
  have hex : ∃ p₀ : Q, 0 < μ p₀ := by
    by_contra! hle
    have h0 : ∑ r : Q, μ r ≤ 0 := Finset.sum_nonpos fun r _ ↦ hle r
    linarith
  obtain ⟨p₀, hp₀⟩ := hex
  have hstep : ∀ p (a : Fin b), 0 < μ p → 0 < μ (M.step p a) := by
    intro p a hp
    rw [← hμ.2 (M.step p a)]
    calc 0 < μ p * (b : ℝ)⁻¹ := mul_pos hp (by positivity)
      _ ≤ μ p * stepProb M 1 p (M.step p a) :=
          mul_le_mul_of_nonneg_left (stepProb_one_pos_of_step hb M p a) (hnn p)
      _ ≤ ∑ r : Q, μ r * stepProb M 1 r (M.step p a) :=
          Finset.single_le_sum (fun r _ ↦ mul_nonneg (hnn r) (stepProb_nonneg M 1 r _))
            (Finset.mem_univ p)
  have hwalk : ∀ u : List (Fin b), ∀ p, 0 < μ p → 0 < μ (M.evalFrom p u) := by
    intro u
    induction u with
    | nil => intro p hp; exact hp
    | cons a u ih => intro p hp; exact ih (M.step p a) (hstep p a hp)
  obtain ⟨u, hu⟩ := hconn p₀ q
  rw [← hu]
  exact hwalk u p₀ hp₀

private lemma stationary_unique (hb : 0 < b) (M : DFA (Fin b) Q) (hconn : IsStronglyConnected M)
    [Nonempty Q] {μ₁ μ₂ : Q → ℝ} (h₁ : IsStationary M μ₁) (h₂ : IsStationary M μ₂) :
    μ₁ = μ₂ := by
  obtain ⟨q₀, _, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Q) (fun q ↦ μ₁ q / μ₂ q) Finset.univ_nonempty
  set c : ℝ := μ₁ q₀ / μ₂ q₀
  set η : Q → ℝ := fun q ↦ μ₁ q - c * μ₂ q
  have hη_nn : ∀ q, 0 ≤ η q := fun q ↦ by
    have hpos := stationary_pos hb M hconn h₂ q
    have hle : c ≤ μ₁ q / μ₂ q := hmin q (Finset.mem_univ q)
    have hmul : c * μ₂ q ≤ μ₁ q := (le_div_iff₀ hpos).1 hle
    dsimp only [η]
    linarith
  have hη_stat : ∀ q, ∑ p : Q, η p * stepProb M 1 p q = η q := fun q ↦ by
    simp_rw [η, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, h₁.2 q, h₂.2 q]
  have hη_q₀ : η q₀ = 0 := by
    have hpos := stationary_pos hb M hconn h₂ q₀
    dsimp only [η, c]
    rw [div_mul_cancel₀ _ hpos.ne', sub_self]
  have hback : ∀ p (a : Fin b), η (M.step p a) = 0 → η p = 0 := by
    intro p a h0
    have hle : η p * (b : ℝ)⁻¹ ≤ 0 := by
      calc η p * (b : ℝ)⁻¹
          ≤ η p * stepProb M 1 p (M.step p a) :=
            mul_le_mul_of_nonneg_left (stepProb_one_pos_of_step hb M p a) (hη_nn p)
        _ ≤ ∑ r : Q, η r * stepProb M 1 r (M.step p a) :=
            Finset.single_le_sum (fun r _ ↦ mul_nonneg (hη_nn r) (stepProb_nonneg M 1 r _))
              (Finset.mem_univ p)
        _ = η (M.step p a) := hη_stat _
        _ = 0 := h0
    have hle0 : η p ≤ 0 := nonpos_of_mul_nonpos_left hle (by positivity)
    linarith [hη_nn p]
  have hwalk_back : ∀ u : List (Fin b), ∀ p, η (M.evalFrom p u) = 0 → η p = 0 := by
    intro u
    induction u with
    | nil => intro p hp; exact hp
    | cons a u ih => intro p hp; exact hback p a (ih (M.step p a) hp)
  have hη_zero : ∀ p, η p = 0 := fun p ↦ by
    obtain ⟨u, hu⟩ := hconn p q₀
    exact hwalk_back u p (by rw [hu, hη_q₀])
  have hc : c = 1 := by
    have hsum : ∑ q : Q, η q = 0 := Finset.sum_eq_zero fun q _ ↦ hη_zero q
    simp_rw [η, Finset.sum_sub_distrib, ← Finset.mul_sum, h₁.1.2, h₂.1.2] at hsum
    linarith
  funext q
  have hq := hη_zero q
  dsimp only [η] at hq
  rw [hc, one_mul] at hq
  linarith

lemma exists_unique_stationary_and_tendsto_cesaro (hb : 0 < b) (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M) [Nonempty Q] :
    ∃ μ : Q → ℝ, IsStationary M μ ∧ (∀ q, 0 < μ q) ∧
      ∀ p q : Q, Tendsto (fun N ↦ cesaroProb M p N q) atTop (𝓝 (μ q)) := by
  have hcomp : IsCompact (probSimplex Q) := isCompact_probSimplex Q
  obtain ⟨p₀⟩ := ‹Nonempty Q›
  obtain ⟨μ, _, φ, hφ, hlim⟩ := hcomp.isSeqCompact fun N ↦ cesaroProb_mem_probSimplex hb M p₀ N
  have hμ : IsStationary M μ := isStationary_of_tendsto_cesaro hb M p₀ hφ hlim
  refine ⟨μ, hμ, stationary_pos hb M hconn hμ, fun p q ↦ ?_⟩
  have hvec : Tendsto (fun N ↦ cesaroProb M p N) atTop (𝓝 μ) := by
    by_contra hnot
    rw [Metric.tendsto_atTop] at hnot
    push Not at hnot
    obtain ⟨ε, hε, hfreq⟩ := hnot
    have hstep : ∀ n : ℕ, ∃ m ≥ n, ε ≤ dist (cesaroProb M p m) μ := hfreq
    choose next hnext_ge hnext_dist using hstep
    let ψ : ℕ → ℕ := Nat.rec (next 0) fun _ prev ↦ next (prev + 1)
    have hψ_mono : StrictMono ψ := strictMono_nat_of_lt_succ fun k ↦ by
      have := hnext_ge (ψ k + 1)
      dsimp only [ψ] at this ⊢
      omega
    have hψ_dist : ∀ k, ε ≤ dist (cesaroProb M p (ψ k)) μ := fun k ↦ by
      cases k with
      | zero => exact hnext_dist 0
      | succ k => exact hnext_dist (ψ k + 1)
    obtain ⟨μ', _, χ, hχ, hlim'⟩ :=
      hcomp.isSeqCompact fun k ↦ cesaroProb_mem_probSimplex hb M p (ψ k)
    have hμ' : IsStationary M μ' :=
      isStationary_of_tendsto_cesaro hb M p (hψ_mono.comp hχ) hlim'
    have heq : μ' = μ := stationary_unique hb M hconn hμ' hμ
    rw [heq] at hlim'
    have hdist0 : Tendsto (fun k ↦ dist (cesaroProb M p (ψ (χ k))) μ) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hlim'
    have hge : ε ≤ 0 := ge_of_tendsto hdist0 (Eventually.of_forall fun k ↦ hψ_dist (χ k))
    linarith
  exact (continuous_apply q).continuousAt.tendsto.comp hvec

/-! ### Second-moment (Chebyshev) concentration for Markov state counts -/

/-- Number of times `t < n` at which the run of `M` from `p` on `u` is in state `q`. -/
noncomputable def stateCount (M : DFA (Fin b) Q) (p : Q) {n : ℕ} (u : Fin n → Fin b) (q : Q) : ℕ :=
  letI := Classical.propDecidable
  ((Finset.univ : Finset (Fin n)).filter fun t ↦
    M.evalFrom p (List.ofFn fun i : Fin t.val ↦ u ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩) = q).card

private lemma evalFrom_take_expectation (hb : 0 < b) (M : DFA (Fin b) Q) (p : Q)
    {n : ℕ} (s : ℕ) (hs : s ≤ n) (g : Q → ℝ) :
    (∑ u : Fin n → Fin b, g (M.evalFrom p (List.ofFn fun i : Fin s ↦ u ⟨i.val, by omega⟩))) /
        (b : ℝ) ^ n = ∑ r : Q, stepProb M s p r * g r := by
  let e : (Fin n → Fin b) ≃ (Fin s → Fin b) × (Fin (n - s) → Fin b) :=
    { toFun := fun u ↦ (fun i ↦ u ⟨i.val, by omega⟩, fun j ↦ u ⟨s + j.val, by omega⟩)
      invFun := fun q i ↦ if h : i.val < s then q.1 ⟨i.val, h⟩ else q.2 ⟨i.val - s, by omega⟩
      left_inv := fun u ↦ by
        funext i; dsimp only; split_ifs with h
        · rfl
        · congr 1; exact Fin.ext (by dsimp only; omega)
      right_inv := fun ⟨u₁, u₂⟩ ↦ by
        ext i
        · simp [i.isLt]
        · have : ¬ s + i.val < s := by omega
          simp [this] }
  have hsum : (∑ u : Fin n → Fin b,
      g (M.evalFrom p (List.ofFn fun i : Fin s ↦ u ⟨i.val, by omega⟩))) =
      ((b : ℝ) ^ (n - s)) * ∑ u₁ : Fin s → Fin b, g (M.evalFrom p (List.ofFn u₁)) := by
    rw [Fintype.sum_equiv e
      (fun u ↦ g (M.evalFrom p (List.ofFn fun i : Fin s ↦ u ⟨i.val, by omega⟩)))
      (fun q ↦ g (M.evalFrom p (List.ofFn q.1))) (fun _ ↦ rfl), Fintype.sum_prod_type]
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, ← Finset.mul_sum]
  have hpow : (b : ℝ) ^ n = (b : ℝ) ^ (n - s) * (b : ℝ) ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hs]
  rw [hsum, hpow, mul_div_mul_left _ _ (by positivity), stepProb_eval_sum hb M s p g]

private lemma evalFrom_pair_expectation (hb : 0 < b) (M : DFA (Fin b) Q) (p : Q)
    {n : ℕ} (s t : ℕ) (hst : s ≤ t) (htn : t ≤ n) (f : Q → ℝ) :
    (∑ u : Fin n → Fin b,
        f (M.evalFrom p (List.ofFn fun i : Fin s ↦ u ⟨i.val, by omega⟩)) *
        f (M.evalFrom p (List.ofFn fun i : Fin t ↦ u ⟨i.val, by omega⟩))) / (b : ℝ) ^ n =
      ∑ r : Q, stepProb M s p r * f r * (∑ r' : Q, stepProb M (t - s) r r' * f r') := by
  let e : (Fin n → Fin b) ≃ (Fin s → Fin b) × (Fin (t - s) → Fin b) × (Fin (n - t) → Fin b) :=
    { toFun := fun u ↦ (fun i ↦ u ⟨i.val, by omega⟩,
        fun j ↦ u ⟨s + j.val, by omega⟩, fun k ↦ u ⟨t + k.val, by omega⟩)
      invFun := fun q i ↦
        if h₁ : i.val < s then q.1 ⟨i.val, h₁⟩
        else if h₂ : i.val < t then q.2.1 ⟨i.val - s, by omega⟩
        else q.2.2 ⟨i.val - t, by omega⟩
      left_inv := fun u ↦ by
        funext i; dsimp only; split_ifs with h₁ h₂
        · rfl
        · congr 1; exact Fin.ext (by dsimp only; omega)
        · congr 1; exact Fin.ext (by dsimp only; omega)
      right_inv := fun ⟨u₁, u₂, u₃⟩ ↦ by
        refine Prod.ext (funext fun i ↦ by simp [i.isLt])
          (Prod.ext (funext fun j ↦ ?_) (funext fun k ↦ ?_))
        · have h1 : ¬ s + j.val < s := by omega
          have h2 : s + j.val < t := by omega
          simp [h1, h2]
        · have h1 : ¬ t + k.val < s := by omega
          have h2 : ¬ t + k.val < t := by omega
          simp [h1, h2] }
  have happ : ∀ u : Fin n → Fin b,
      (List.ofFn fun i : Fin t ↦ u ⟨i.val, by omega⟩) =
        (List.ofFn fun i : Fin s ↦ u ⟨i.val, by omega⟩) ++
        (List.ofFn fun j : Fin (t - s) ↦ u ⟨s + j.val, by omega⟩) := fun u ↦ by
    apply List.ext_getElem
    · simp; omega
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
      split_ifs with h
      · rfl
      · congr 1; exact Fin.ext (by dsimp only; omega)
  have hsum : (∑ u : Fin n → Fin b,
      f (M.evalFrom p (List.ofFn fun i : Fin s ↦ u ⟨i.val, by omega⟩)) *
      f (M.evalFrom p (List.ofFn fun i : Fin t ↦ u ⟨i.val, by omega⟩))) =
      ((b : ℝ) ^ (n - t)) * ∑ u₁ : Fin s → Fin b,
        f (M.evalFrom p (List.ofFn u₁)) *
        (∑ u₂ : Fin (t - s) → Fin b,
          f (M.evalFrom (M.evalFrom p (List.ofFn u₁)) (List.ofFn u₂))) := by
    rw [Fintype.sum_equiv e
      (fun u ↦ f (M.evalFrom p (List.ofFn fun i : Fin s ↦ u ⟨i.val, by omega⟩)) *
        f (M.evalFrom p (List.ofFn fun i : Fin t ↦ u ⟨i.val, by omega⟩)))
      (fun q ↦ f (M.evalFrom p (List.ofFn q.1)) *
        f (M.evalFrom (M.evalFrom p (List.ofFn q.1)) (List.ofFn q.2.1)))
      (fun u ↦ by simp only [e, Equiv.coe_fn_mk, happ u, DFA.evalFrom_of_append]),
      Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← Finset.mul_sum]
  have hpow : (b : ℝ) ^ n = (b : ℝ) ^ (n - t) * ((b : ℝ) ^ (t - s) * (b : ℝ) ^ s) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hsum, hpow, mul_div_mul_left _ _ (by positivity), ← div_div, Finset.sum_div]
  simp_rw [mul_div_assoc, stepProb_eval_sum hb M (t - s) _ f]
  rw [stepProb_eval_sum hb M s p fun r ↦ f r * ∑ r' : Q, stepProb M (t - s) r r' * f r']
  simp_rw [mul_assoc]

private lemma sq_sum_fin {n : ℕ} (a : Fin n → ℝ) :
    (∑ t : Fin n, a t) ^ 2 =
      (∑ s : Fin n, a s ^ 2) +
      2 * ∑ s : Fin n, ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), a s * a t := by
  have hpart : ∀ s : Fin n, (∑ t : Fin n, a s * a t) =
      a s ^ 2 +
      (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), a s * a t) +
      (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ t.val < s.val), a s * a t) := fun s ↦ by
    have hunion : (Finset.univ : Finset (Fin n)) =
        {s} ∪ (Finset.univ.filter (fun t : Fin n ↦ s.val < t.val) ∪
          Finset.univ.filter (fun t : Fin n ↦ t.val < s.val)) := by
      ext t
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
        true_and, true_iff]
      rcases lt_trichotomy s.val t.val with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Fin.ext h.symm)
      · exact Or.inr (Or.inr h)
    have hd1 : Disjoint ({s} : Finset (Fin n))
        (Finset.univ.filter (fun t : Fin n ↦ s.val < t.val) ∪
          Finset.univ.filter (fun t : Fin n ↦ t.val < s.val)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [Finset.mem_singleton] at ht1
      subst ht1
      simp at ht2
    have hd2 : Disjoint (Finset.univ.filter (fun t : Fin n ↦ s.val < t.val))
        (Finset.univ.filter (fun t : Fin n ↦ t.val < s.val)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [Finset.mem_filter] at ht1 ht2
      omega
    conv_lhs => rw [hunion]
    rw [Finset.sum_union hd1, Finset.sum_singleton, Finset.sum_union hd2, ← add_assoc, ← sq]
  have hswap : (∑ s : Fin n, ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ t.val < s.val),
      a s * a t) =
      ∑ s : Fin n, ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), a s * a t := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
    split_ifs
    · exact mul_comm _ _
    · rfl
  calc (∑ t : Fin n, a t) ^ 2
      = ∑ s : Fin n, ∑ t : Fin n, a s * a t := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ ↦ Finset.mul_sum _ _ _
    _ = ∑ s : Fin n, (a s ^ 2 +
          (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), a s * a t) +
          (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ t.val < s.val), a s * a t)) :=
        Finset.sum_congr rfl fun s _ ↦ hpart s
    _ = (∑ s : Fin n, a s ^ 2) +
          (∑ s : Fin n, ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), a s * a t) +
          (∑ s : Fin n, ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ t.val < s.val), a s * a t) := by
        simp_rw [Finset.sum_add_distrib]
    _ = (∑ s : Fin n, a s ^ 2) +
          2 * ∑ s : Fin n, ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
            a s * a t := by
        rw [hswap]; ring

private lemma sum_stepProb_tail_abs_le (hb : 0 < b) (M : DFA (Fin b) Q)
    {M₀ : ℕ} (hM₀_pos : 1 ≤ M₀) {η : ℝ} (hη : 0 < η) (f : Q → ℝ)
    (hf_abs : ∀ r, |f r| ≤ 1)
    (hM₀ : ∀ (r : Q) (m : ℕ), M₀ ≤ m →
      |(∑ j ∈ Finset.range m, ∑ r' : Q, stepProb M j r r' * f r')| ≤ m * η)
    {n : ℕ} (s : Fin n) (r : Q) :
    |∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
      ∑ r' : Q, stepProb M (t.val - s.val) r r' * f r'| ≤ (M₀ : ℝ) + (n : ℝ) * η := by
  have hreindex : (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
      ∑ r' : Q, stepProb M (t.val - s.val) r r' * f r') =
      (∑ j ∈ Finset.range (n - s.val), ∑ r' : Q, stepProb M j r r' * f r') -
        (∑ r' : Q, stepProb M 0 r r' * f r') := by
    have hbij : (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
        ∑ r' : Q, stepProb M (t.val - s.val) r r' * f r') =
        ∑ j ∈ Finset.Ico 1 (n - s.val), ∑ r' : Q, stepProb M j r r' * f r' := by
      refine Finset.sum_nbij' (fun t ↦ t.val - s.val)
        (fun j ↦ if h : s.val + j < n then ⟨s.val + j, h⟩ else s) ?_ ?_ ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_Ico] at ht ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        have hlt : s.val + j < n := by omega
        simp only [hlt, ↓reduceDIte]
        omega
      · intro t ht
        simp only [Finset.mem_filter] at ht
        have hlt : s.val + (t.val - s.val) < n := by omega
        simp only [hlt, ↓reduceDIte]
        exact Fin.ext (by dsimp only; omega)
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        have hlt : s.val + j < n := by omega
        simp only [hlt, ↓reduceDIte]
        omega
      · intro t _; rfl
    rw [hbij]
    have hge1 : 1 ≤ n - s.val := by omega
    have hsp := Finset.sum_range_add_sum_Ico
      (fun j ↦ ∑ r' : Q, stepProb M j r r' * f r') hge1
    rw [Finset.sum_range_one] at hsp
    linarith
  rw [hreindex]
  have h0_le : |∑ r' : Q, stepProb M 0 r r' * f r'| ≤ 1 := by
    have heq : (∑ r' : Q, stepProb M 0 r r' * f r') = f r := by
      rw [Finset.sum_eq_single r]
      · simp [stepProb_zero]
      · intro r' _ hne
        simp [stepProb_zero, Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ r) h
    rw [heq]
    exact hf_abs r
  by_cases hbig : M₀ ≤ n - s.val
  · have hbd := hM₀ r (n - s.val) hbig
    have hsub : ((n - s.val : ℕ) : ℝ) * η ≤ (n : ℝ) * η := by
      gcongr; exact_mod_cast Nat.sub_le n s.val
    have h1M : (1 : ℝ) ≤ M₀ := by exact_mod_cast hM₀_pos
    calc |(∑ j ∈ Finset.range (n - s.val), ∑ r' : Q, stepProb M j r r' * f r') -
          ∑ r' : Q, stepProb M 0 r r' * f r'|
        ≤ |∑ j ∈ Finset.range (n - s.val), ∑ r' : Q, stepProb M j r r' * f r'| +
          |∑ r' : Q, stepProb M 0 r r' * f r'| := abs_sub _ _
      _ ≤ ((n - s.val : ℕ) : ℝ) * η + 1 := add_le_add hbd h0_le
      _ ≤ (M₀ : ℝ) + (n : ℝ) * η := by linarith
  · have htriv : |∑ j ∈ Finset.range (n - s.val),
        ∑ r' : Q, stepProb M j r r' * f r'| ≤ ((n - s.val : ℕ) : ℝ) := by
      calc |∑ j ∈ Finset.range (n - s.val), ∑ r' : Q, stepProb M j r r' * f r'|
          ≤ ∑ j ∈ Finset.range (n - s.val), |∑ r' : Q, stepProb M j r r' * f r'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range (n - s.val), (1 : ℝ) := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            calc |∑ r' : Q, stepProb M j r r' * f r'|
                ≤ ∑ r' : Q, |stepProb M j r r' * f r'| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ r' : Q, stepProb M j r r' * 1 := by
                  refine Finset.sum_le_sum fun r' _ ↦ ?_
                  rw [abs_mul, abs_of_nonneg (stepProb_nonneg M j r r')]
                  exact mul_le_mul_of_nonneg_left (hf_abs r') (stepProb_nonneg M j r r')
              _ = 1 := by simp [sum_stepProb hb M]
        _ = ((n - s.val : ℕ) : ℝ) := by simp
    have hlt : (n - s.val : ℕ) + 1 ≤ M₀ := by omega
    have hltR : ((n - s.val : ℕ) : ℝ) + 1 ≤ (M₀ : ℝ) := by exact_mod_cast hlt
    calc |(∑ j ∈ Finset.range (n - s.val), ∑ r' : Q, stepProb M j r r' * f r') -
          ∑ r' : Q, stepProb M 0 r r' * f r'|
        ≤ |∑ j ∈ Finset.range (n - s.val), ∑ r' : Q, stepProb M j r r' * f r'| +
          |∑ r' : Q, stepProb M 0 r r' * f r'| := abs_sub _ _
      _ ≤ ((n - s.val : ℕ) : ℝ) + 1 := add_le_add htriv h0_le
      _ ≤ (M₀ : ℝ) + (n : ℝ) * η := by nlinarith [show (0 : ℝ) ≤ n * η by positivity]

private lemma secondMoment_stateCount_le (hb : 0 < b) (M : DFA (Fin b) Q)
    {M₀ : ℕ} (hM₀_pos : 1 ≤ M₀) {η : ℝ} (hη : 0 < η) (p : Q) (f : Q → ℝ)
    (hf_abs : ∀ r, |f r| ≤ 1)
    (hM₀ : ∀ (r : Q) (m : ℕ), M₀ ≤ m →
      |(∑ j ∈ Finset.range m, ∑ r' : Q, stepProb M j r r' * f r')| ≤ m * η)
    {n : ℕ} (hn0 : 0 < n) :
    (∑ u : Fin n → Fin b,
      ((∑ t : Fin n, f (M.evalFrom p (List.ofFn fun i : Fin t.val ↦ u ⟨i.val, by omega⟩))) /
        (n : ℝ)) ^ 2) / (b : ℝ) ^ n ≤
      (1 + 2 * (M₀ : ℝ)) / (n : ℝ) + 2 * η := by
  let g : (Fin n → Fin b) → Fin n → ℝ := fun u t ↦
    f (M.evalFrom p (List.ofFn fun i : Fin t.val ↦ u ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩))
  have hdiag : (∑ u : Fin n → Fin b, ∑ s : Fin n, g u s ^ 2) / (b : ℝ) ^ n ≤ n := by
    rw [Finset.sum_comm, Finset.sum_div]
    calc ∑ s : Fin n, (∑ u : Fin n → Fin b, g u s ^ 2) / (b : ℝ) ^ n
        ≤ ∑ _s : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          dsimp only [g]
          rw [evalFrom_take_expectation hb M p s.val s.isLt.le (fun r ↦ f r ^ 2)]
          calc ∑ r : Q, stepProb M s.val p r * f r ^ 2
              ≤ ∑ r : Q, stepProb M s.val p r * 1 := by
                refine Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_left ?_
                  (stepProb_nonneg M s.val p r)
                nlinarith [abs_le.1 (hf_abs r)]
            _ = 1 := by simp [sum_stepProb hb M]
      _ = n := by simp
  have hoff : (∑ u : Fin n → Fin b, ∑ s : Fin n,
      ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), g u s * g u t) /
        (b : ℝ) ^ n ≤ (n : ℝ) * ((M₀ : ℝ) + (n : ℝ) * η) := by
    rw [Finset.sum_comm, Finset.sum_div]
    calc ∑ s : Fin n, (∑ u : Fin n → Fin b,
          ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), g u s * g u t) /
            (b : ℝ) ^ n
        ≤ ∑ _s : Fin n, ((M₀ : ℝ) + (n : ℝ) * η) := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          rw [Finset.sum_comm, Finset.sum_div]
          have hterm : ∀ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
              (∑ u : Fin n → Fin b, g u s * g u t) / (b : ℝ) ^ n =
              ∑ r : Q, stepProb M s.val p r * f r *
                (∑ r' : Q, stepProb M (t.val - s.val) r r' * f r') := fun t ht ↦ by
            simp only [Finset.mem_filter] at ht
            exact evalFrom_pair_expectation hb M p s.val t.val ht.2.le t.isLt.le f
          rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
          calc ∑ r : Q, ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
                stepProb M s.val p r * f r *
                  (∑ r' : Q, stepProb M (t.val - s.val) r r' * f r')
              = ∑ r : Q, stepProb M s.val p r * f r *
                  (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
                    ∑ r' : Q, stepProb M (t.val - s.val) r r' * f r') := by
                refine Finset.sum_congr rfl fun r _ ↦ (Finset.mul_sum _ _ _).symm
            _ ≤ ∑ r : Q, stepProb M s.val p r * ((M₀ : ℝ) + (n : ℝ) * η) := by
                refine Finset.sum_le_sum fun r _ ↦ ?_
                have hinner := sum_stepProb_tail_abs_le hb M hM₀_pos hη f hf_abs hM₀ s r
                have hmul := le_abs_self (f r *
                  ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
                    ∑ r' : Q, stepProb M (t.val - s.val) r r' * f r')
                rw [abs_mul] at hmul
                have hprod : f r *
                    (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
                      ∑ r' : Q, stepProb M (t.val - s.val) r r' * f r') ≤
                    (M₀ : ℝ) + (n : ℝ) * η := by
                  calc _ ≤ |f r| * |∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val),
                            ∑ r' : Q, stepProb M (t.val - s.val) r r' * f r'| := hmul
                    _ ≤ 1 * ((M₀ : ℝ) + (n : ℝ) * η) :=
                        mul_le_mul (hf_abs r) hinner (abs_nonneg _) zero_le_one
                    _ = (M₀ : ℝ) + (n : ℝ) * η := one_mul _
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left hprod (stepProb_nonneg M s.val p r)
            _ = (M₀ : ℝ) + (n : ℝ) * η := by
                rw [← Finset.sum_mul, sum_stepProb hb M, one_mul]
      _ = (n : ℝ) * ((M₀ : ℝ) + (n : ℝ) * η) := by simp; ring
  have hrewrite : (∑ u : Fin n → Fin b, ((∑ t : Fin n, g u t) / (n : ℝ)) ^ 2) / (b : ℝ) ^ n =
      ((∑ u : Fin n → Fin b, ∑ s : Fin n, g u s ^ 2) / (b : ℝ) ^ n +
        2 * ((∑ u : Fin n → Fin b, ∑ s : Fin n,
          ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), g u s * g u t) /
            (b : ℝ) ^ n)) / (n : ℝ) ^ 2 := by
    have hsq : (∑ u : Fin n → Fin b, (∑ t : Fin n, g u t) ^ 2) =
        (∑ u : Fin n → Fin b, ∑ s : Fin n, g u s ^ 2) +
        2 * ∑ u : Fin n → Fin b, ∑ s : Fin n,
          ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), g u s * g u t := by
      rw [Finset.sum_congr rfl fun u _ ↦ sq_sum_fin (g u), Finset.sum_add_distrib,
        ← Finset.mul_sum]
    simp_rw [div_pow, ← Finset.sum_div, div_right_comm _ ((n : ℝ) ^ 2)]
    rw [hsq, add_div, mul_div_assoc]
  have hn_pos : (0 : ℝ) < n := by positivity
  calc (∑ u : Fin n → Fin b, ((∑ t : Fin n, g u t) / (n : ℝ)) ^ 2) / (b : ℝ) ^ n
      = ((∑ u : Fin n → Fin b, ∑ s : Fin n, g u s ^ 2) / (b : ℝ) ^ n +
          2 * ((∑ u : Fin n → Fin b, ∑ s : Fin n,
            ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ s.val < t.val), g u s * g u t) /
              (b : ℝ) ^ n)) / (n : ℝ) ^ 2 := hrewrite
    _ ≤ ((n : ℝ) + 2 * ((n : ℝ) * ((M₀ : ℝ) + (n : ℝ) * η))) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right
          (add_le_add hdiag (mul_le_mul_of_nonneg_left hoff zero_le_two)) (sq_nonneg _)
    _ = (1 + 2 * (M₀ : ℝ)) / (n : ℝ) + 2 * η := by
        field_simp [hn_pos.ne']; ring

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
  classical
  set C : ℝ := (Fintype.card Q : ℝ)
  have hC : 0 < C := by
    have : 0 < Fintype.card Q := Fintype.card_pos
    positivity
  set η : ℝ := ε * δ ^ 2 / (8 * C ^ 2)
  have hη : 0 < η := by positivity
  -- Uniform Cesàro convergence for centered indicator functions `f_q r = (r = q) - μ q`
  have hunif : ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ (q r : Q) (m : ℕ), M₀ ≤ m →
      |(∑ j ∈ Finset.range m, ∑ r' : Q,
        stepProb M j r r' * ((if r' = q then (1 : ℝ) else 0) - μ q))| ≤
        m * η := by
    have hpair : ∀ pq : Q × Q, ∃ M₁ : ℕ, ∀ m ≥ M₁, 0 < m →
        |(∑ j ∈ Finset.range m, ∑ r' : Q,
          stepProb M j pq.2 r' * ((if r' = pq.1 then (1 : ℝ) else 0) - μ pq.1)) / (m : ℝ)| ≤ η := by
      rintro ⟨q, r⟩
      have ht : Tendsto (fun N : ℕ ↦
          ∑ r' : Q, cesaroProb M r N r' * ((if r' = q then (1 : ℝ) else 0) - μ q))
          atTop (𝓝 (∑ r' : Q, μ r' * ((if r' = q then (1 : ℝ) else 0) - μ q))) :=
        tendsto_finset_sum_real Finset.univ
          (fun r' N ↦ cesaroProb M r N r' * ((if r' = q then (1 : ℝ) else 0) - μ q))
          (fun r' ↦ μ r' * ((if r' = q then (1 : ℝ) else 0) - μ q))
          fun r' _ ↦ (hces r r').mul_const _
      have hlim0 : ∑ r' : Q, μ r' * ((if r' = q then (1 : ℝ) else 0) - μ q) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.sum_mul, hμ.1.2, one_mul,
          sub_self]
      rw [hlim0] at ht
      obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 ht η hη
      refine ⟨N₁ + 1, fun m hm _ ↦ ?_⟩
      have hspec := hN₁ (m - 1) (by omega)
      rw [Real.dist_eq, sub_zero] at hspec
      have heq : (∑ j ∈ Finset.range m, ∑ r' : Q,
          stepProb M j r r' * ((if r' = q then (1 : ℝ) else 0) - μ q)) / (m : ℝ) =
          ∑ r' : Q, cesaroProb M r (m - 1) r' * ((if r' = q then (1 : ℝ) else 0) - μ q) := by
        have hm1 : m - 1 + 1 = m := by omega
        have hm1R : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm1
        simp_rw [cesaroProb, hm1, hm1R, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
        congr 1
        rw [Finset.sum_comm]
      rw [heq]
      exact hspec.le
    choose Mf hMf using hpair
    refine ⟨(Finset.univ.sup Mf) + 1, by omega, fun q r m hm ↦ ?_⟩
    have hm' : Mf (q, r) ≤ m := le_trans (Finset.le_sup (Finset.mem_univ (q, r))) (by omega)
    have hm_pos : (0 : ℝ) < m := by
      have : 0 < m := by omega
      positivity
    have hdiv := hMf (q, r) m hm' (by omega)
    rw [abs_div, abs_of_pos hm_pos, div_le_iff₀ hm_pos] at hdiv
    linarith
  obtain ⟨M₀, hM₀_pos, hM₀⟩ := hunif
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((1 + 2 * (M₀ : ℝ)) / η)
  refine ⟨N₀ + 1, fun n hn hn0 ↦ ?_⟩
  have hsingle : ∀ (p q : Q),
      (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ) <
      (ε / C ^ 2) * (b : ℝ) ^ n := by
    intro p q
    set f : Q → ℝ := fun r ↦ (if r = q then (1 : ℝ) else 0) - μ q
    have hf_abs : ∀ r, |f r| ≤ 1 := fun r ↦ by
      have h0 := hμ.1.1 q
      have h1 : μ q ≤ 1 := by
        calc μ q ≤ ∑ r' : Q, μ r' :=
              Finset.single_le_sum (fun r' _ ↦ hμ.1.1 r') (Finset.mem_univ q)
          _ = 1 := hμ.1.2
      dsimp only [f]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    have havg_eq : ∀ u : Fin n → Fin b,
        (stateCount M p u q : ℝ) / n - μ q =
          (∑ t : Fin n, f (M.evalFrom p (List.ofFn fun i : Fin t.val ↦ u ⟨i.val, by omega⟩))) /
            (n : ℝ) := fun u ↦ by
      simp only [stateCount, f, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div]
      rw [mul_div_cancel_left₀ _ (by positivity : (n : ℝ) ≠ 0)]
    have h2mom : (∑ u : Fin n → Fin b, ((stateCount M p u q : ℝ) / n - μ q) ^ 2) / (b : ℝ) ^ n ≤
        (1 + 2 * (M₀ : ℝ)) / (n : ℝ) + 2 * η := by
      simp_rw [havg_eq]
      exact secondMoment_stateCount_le hb M hM₀_pos hη p f hf_abs (hM₀ q) hn0
    have hmarkov : δ ^ 2 * (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ) ≤
        ∑ u : Fin n → Fin b, ((stateCount M p u q : ℝ) / n - μ q) ^ 2 := by
      calc δ ^ 2 * (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
              δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ)
          = ∑ _u ∈ Finset.univ.filter (fun u : Fin n → Fin b ↦
              δ < |(stateCount M p u q : ℝ) / n - μ q|), δ ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin n → Fin b ↦
              δ < |(stateCount M p u q : ℝ) / n - μ q|),
              ((stateCount M p u q : ℝ) / n - μ q) ^ 2 := by
            refine Finset.sum_le_sum fun u hu ↦ ?_
            simp only [Finset.mem_filter] at hu
            rw [← sq_abs ((stateCount M p u q : ℝ) / n - μ q)]
            nlinarith [hu.2, hδ]
        _ ≤ ∑ u : Fin n → Fin b, ((stateCount M p u q : ℝ) / n - μ q) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    have hsmall : (1 + 2 * (M₀ : ℝ)) / (n : ℝ) + 2 * η < (ε / C ^ 2) * δ ^ 2 := by
      have hn_gt : (1 + 2 * (M₀ : ℝ)) / η < (n : ℝ) :=
        lt_of_lt_of_le hN₀ (by exact_mod_cast (show N₀ ≤ n by omega))
      have hdiv_lt : (1 + 2 * (M₀ : ℝ)) / (n : ℝ) < η := by
        rw [div_lt_iff₀ (by positivity)]
        have := (div_lt_iff₀ hη).1 hn_gt
        linarith
      have h3η : 3 * η < (ε / C ^ 2) * δ ^ 2 := by
        dsimp only [η]
        have hpos : 0 < ε * δ ^ 2 / C ^ 2 := by positivity
        linarith [show ε * δ ^ 2 / (8 * C ^ 2) = (ε * δ ^ 2 / C ^ 2) / 8 by ring,
          show (ε / C ^ 2) * δ ^ 2 = ε * δ ^ 2 / C ^ 2 by ring]
      linarith
    have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    have hcard_le : (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ) ≤
        ((1 + 2 * (M₀ : ℝ)) / (n : ℝ) + 2 * η) * (b : ℝ) ^ n / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
              δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ) * δ ^ 2
          ≤ ∑ u : Fin n → Fin b, ((stateCount M p u q : ℝ) / n - μ q) ^ 2 := by
            rw [mul_comm]; exact hmarkov
        _ ≤ ((1 + 2 * (M₀ : ℝ)) / (n : ℝ) + 2 * η) * (b : ℝ) ^ n :=
            (div_le_iff₀ hbn).1 h2mom
    calc (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
            δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ)
        ≤ ((1 + 2 * (M₀ : ℝ)) / (n : ℝ) + 2 * η) * (b : ℝ) ^ n / δ ^ 2 := hcard_le
      _ < ((ε / C ^ 2) * δ ^ 2) * (b : ℝ) ^ n / δ ^ 2 := by gcongr
      _ = (ε / C ^ 2) * (b : ℝ) ^ n := by field_simp [hδ.ne']
  -- Union bound over `(p, q) ∈ Q × Q`
  have hunion : (Finset.univ.filter fun u : Fin n → Fin b ↦
      ∃ p q : Q, δ < |(stateCount M p u q : ℝ) / n - μ q|) ⊆
      (Finset.univ : Finset (Q × Q)).biUnion fun pq ↦
        Finset.univ.filter fun u : Fin n → Fin b ↦
          δ < |(stateCount M pq.1 u pq.2 : ℝ) / n - μ pq.2| := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Prod.exists] at hu ⊢
    exact hu
  have hle : (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
      ∃ p q : Q, δ < |(stateCount M p u q : ℝ) / n - μ q|).card : ℝ) ≤
      ∑ pq : Q × Q, (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
        δ < |(stateCount M pq.1 u pq.2 : ℝ) / n - μ pq.2|).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hunion).trans Finset.card_biUnion_le
  have hlt : ∑ pq : Q × Q, (((Finset.univ : Finset (Fin n → Fin b)).filter fun u ↦
      δ < |(stateCount M pq.1 u pq.2 : ℝ) / n - μ pq.2|).card : ℝ) <
      ∑ _pq : Q × Q, (ε / C ^ 2) * (b : ℝ) ^ n :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun pq _ ↦ hsingle pq.1 pq.2
  have hsum_eq : (∑ _pq : Q × Q, (ε / C ^ 2) * (b : ℝ) ^ n) = ε * (b : ℝ) ^ n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
    dsimp only [C]
    field_simp [hC.ne']
  linarith

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
  apply List.ext_getElem
  · simp [digitPrefix]
  · intro i hi₁ hi₂
    simp only [digitPrefix, List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split_ifs with h
    · rfl
    · apply Fin.ext
      dsimp only
      congr 1
      omega

/-- **Schnorr–Stimm / Carton state-frequency theorem**: on a base-`b` normal number `x`, the
asymptotic fraction of prefixes landing in state `q` of a strongly connected finite DFA equals its
stationary probability `μ q`. -/
theorem tendsto_dfa_stateFreq (hb : 2 ≤ b) (M : DFA (Fin b) Q)
    (hconn : IsStronglyConnected M)
    {μ : Q → ℝ} (hμ : IsStationary M μ)
    (hx : IsNormalIn b x) (q : Q) :
    Tendsto (fun N : ℕ ↦ (dfaStateCount b (by omega) M x q N : ℝ) / N) atTop (𝓝 (μ q)) := by
  classical
  have hb0 : 0 < b := by omega
  have : Nonempty Q := ⟨q⟩
  obtain ⟨μ₀, hμ₀, _, hces⟩ := exists_unique_stationary_and_tendsto_cesaro hb0 M hconn
  have hμeq : μ₀ = μ := stationary_unique hb0 M hconn hμ₀ hμ
  subst hμeq
  -- First show `∀ q', ∀ η > 0, ∀ᶠ N, μ₀ q' - η ≤ dfaStateCount q' N / N`
  have hlower : ∀ (q' : Q) {η : ℝ}, 0 < η →
      ∀ᶠ N : ℕ in atTop, μ₀ q' - η ≤ (dfaStateCount b hb0 M x q' N : ℝ) / N := by
    intro q' η hη
    set ε : ℝ := min (η / 5) (1 / 2)
    have hε : 0 < ε := lt_min (by positivity) (by norm_num)
    have hε_le : ε ≤ η / 5 := min_le_left _ _
    obtain ⟨K₀, hK₀⟩ := card_bad_stateCount_lt hb0 M hconn hμ₀ hces hε hε
    set k : ℕ := max K₀ 1
    have hk : 1 ≤ k := le_max_right _ _
    have hbad : (((Finset.univ : Finset (Fin k → Fin b)).filter fun u ↦
        ∃ p r : Q, ε < |(stateCount M p u r : ℝ) / k - μ₀ r|).card : ℝ) < ε * (b : ℝ) ^ k :=
      hK₀ k (le_max_left _ _) (by omega)
    let G : Finset (Fin k → Fin b) := Finset.univ.filter fun u ↦
      ∀ p r : Q, |(stateCount M p u r : ℝ) / k - μ₀ r| ≤ ε
    have hG_card : (1 - ε) * (b : ℝ) ^ k ≤ (G.card : ℝ) := by
      have hcompl : G.card + ((Finset.univ : Finset (Fin k → Fin b)).filter fun u ↦
          ∃ p r : Q, ε < |(stateCount M p u r : ℝ) / k - μ₀ r|).card = b ^ k := by
        have hdisj : Disjoint G (Finset.univ.filter fun u : Fin k → Fin b ↦
            ∃ p r : Q, ε < |(stateCount M p u r : ℝ) / k - μ₀ r|) := by
          rw [Finset.disjoint_left]
          intro u hu1 hu2
          simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
          obtain ⟨p, r, hlt⟩ := hu2
          linarith [hu1 p r]
        have hunion : G ∪ (Finset.univ.filter fun u : Fin k → Fin b ↦
            ∃ p r : Q, ε < |(stateCount M p u r : ℝ) / k - μ₀ r|) = Finset.univ := by
          ext u
          simp only [G, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          by_contra! h
          obtain ⟨⟨p, r, hgt⟩, hle⟩ := h
          exact not_lt_of_ge (hle p r) hgt
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin]
      have hcast : (G.card : ℝ) + (((Finset.univ : Finset (Fin k → Fin b)).filter fun u ↦
          ∃ p r : Q, ε < |(stateCount M p u r : ℝ) / k - μ₀ r|).card : ℝ) = (b : ℝ) ^ k := by
        exact_mod_cast hcompl
      linarith
    -- `x` is normal in base `b ^ k`, so every aligned `k`-block occurs with frequency `b ^ (-k)`
    have hxk : IsNormalIn (b ^ k) x := (isNormalIn_pow_iff hb (by omega)).2 hx
    have hgood_freq : ∀ u ∈ G, ∀ᶠ m : ℕ in atTop,
        (1 - ε) * (m : ℝ) / (b : ℝ) ^ k ≤
          (((Finset.range m).filter fun j ↦
            ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card : ℝ) := by
      intro u _
      let code : Fin (b ^ k) := blockCode u
      have hlim := hxk.isSimplyNormalIn code
      have hcnt : ∀ m, blockCount (b ^ k) x (fun _ : Fin 1 ↦ code) m =
          ((Finset.range m).filter fun j ↦
            ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card := fun m ↦ by
        simp only [blockCount]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Fin.forall_fin_one, Fin.val_zero, add_zero]
        refine and_congr_right fun _ ↦ ?_
        have hiff := forall_digit_eq_iff_digit_pow (x := x) hb0 u 0 j
        simpa [code] using hiff.symm
      simp_rw [hcnt] at hlim
      have hpos : 0 < ε * (((b ^ k : ℕ) : ℝ))⁻¹ := by positivity
      filter_upwards [eventually_atTop.2 (Metric.tendsto_atTop.1 hlim (ε * (((b ^ k : ℕ) : ℝ))⁻¹)
        hpos), eventually_ge_atTop 1] with m hm hm1
      rw [Real.dist_eq] at hm
      have hle := (abs_lt.1 hm).1
      have hm_pos : (0 : ℝ) < m := by positivity
      have hmul := (lt_div_iff₀ hm_pos).1 (by linarith : (1 - ε) * (((b ^ k : ℕ) : ℝ))⁻¹ <
        (((Finset.range m).filter fun j ↦
          ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card : ℝ) / m)
      push_cast at hmul
      linarith [show (1 - ε) * ((b : ℝ) ^ k)⁻¹ * (m : ℝ) = (1 - ε) * (m : ℝ) / (b : ℝ) ^ k by ring]
    have hall : ∀ᶠ m : ℕ in atTop, ∀ u ∈ G,
        (1 - ε) * (m : ℝ) / (b : ℝ) ^ k ≤
          (((Finset.range m).filter fun j ↦
            ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card : ℝ) :=
      Filter.eventually_all_finset G |>.2 hgood_freq
    obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 hall
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((k : ℝ) / ε)
    refine eventually_atTop.2 ⟨max (M₁ * k) (max N₁ k), fun N hN ↦ ?_⟩
    set m : ℕ := N / k
    have hm_ge : M₁ ≤ m := by
      have : M₁ * k ≤ N := le_trans (le_max_left _ _) hN
      exact (Nat.le_div_iff_mul_le (by omega)).2 this
    -- Count visits to `q'` in `[0, m * k)` block-by-block
    have hcount_ge : (∑ u ∈ G,
        (((Finset.range m).filter fun j ↦
          ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card : ℝ) *
          ((k : ℝ) * (μ₀ q' - ε))) ≤ (dfaStateCount b hb0 M x q' N : ℝ) := by
      have hmk_le : m * k ≤ N := by
        rw [mul_comm]; exact Nat.mul_div_le N k
      have hstep1 : (∑ j ∈ Finset.range m,
          (stateCount M (M.eval (digitPrefix b hb0 x (j * k)))
            (fun i : Fin k ↦ ⟨digit b x (j * k + i.val), digit_lt hb0 x _⟩) q' : ℝ)) ≤
          (dfaStateCount b hb0 M x q' N : ℝ) := by
        have hnat : (∑ j ∈ Finset.range m,
            stateCount M (M.eval (digitPrefix b hb0 x (j * k)))
              (fun i : Fin k ↦ ⟨digit b x (j * k + i.val), digit_lt hb0 x _⟩) q') ≤
            dfaStateCount b hb0 M x q' N := by
          rw [dfaStateCount]
          let S : ℕ → Finset ℕ := fun j ↦
            ((Finset.univ : Finset (Fin k)).filter fun t ↦
              M.evalFrom (M.eval (digitPrefix b hb0 x (j * k)))
                (List.ofFn fun i : Fin t.val ↦ ⟨digit b x (j * k + i.val), digit_lt hb0 x _⟩) =
                  q').image fun t ↦ j * k + t.val
          have hcardS : ∀ j, (S j).card =
              stateCount M (M.eval (digitPrefix b hb0 x (j * k)))
                (fun i : Fin k ↦ ⟨digit b x (j * k + i.val), digit_lt hb0 x _⟩) q' := fun j ↦
            Finset.card_image_of_injective _ fun t₁ t₂ h ↦ Fin.ext (by omega)
          have hdisj : Set.PairwiseDisjoint (Finset.range m : Set ℕ) S := by
            intro j₁ _ j₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro r hr₁ hr₂
            simp only [S, Finset.mem_image] at hr₁ hr₂
            obtain ⟨t₁, _, rfl⟩ := hr₁
            obtain ⟨t₂, _, heq⟩ := hr₂
            have ht₁ := t₁.isLt
            have ht₂ := t₂.isLt
            have hq : j₁ = j₂ := by
              have h1 : (j₁ * k + t₁.val) / k = j₁ := by
                rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht₁, add_zero]
              have h2 : (j₂ * k + t₂.val) / k = j₂ := by
                rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht₂, add_zero]
              rw [← h1, ← heq, h2]
            exact hne hq
          have hsub : (Finset.range m).biUnion S ⊆
              (Finset.range N).filter fun i ↦ M.eval (digitPrefix b hb0 x i) = q' := by
            intro r hr
            simp only [Finset.mem_biUnion, Finset.mem_range, S, Finset.mem_image,
              Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            obtain ⟨j, hjm, t, ht_eq, rfl⟩ := hr
            refine ⟨by nlinarith [t.isLt], ?_⟩
            rw [digitPrefix_add hb0 x (j * k) t.val, DFA.eval, DFA.evalFrom_of_append]
            exact ht_eq
          calc ∑ j ∈ Finset.range m,
                stateCount M (M.eval (digitPrefix b hb0 x (j * k)))
                  (fun i : Fin k ↦ ⟨digit b x (j * k + i.val), digit_lt hb0 x _⟩) q'
              = ∑ j ∈ Finset.range m, (S j).card := Finset.sum_congr rfl fun j _ ↦ (hcardS j).symm
            _ = ((Finset.range m).biUnion S).card := (Finset.card_biUnion hdisj).symm
            _ ≤ ((Finset.range N).filter fun i ↦ M.eval (digitPrefix b hb0 x i) = q').card :=
                Finset.card_le_card hsub
        exact_mod_cast hnat
      have hstep2 : (∑ u ∈ G,
          (((Finset.range m).filter fun j ↦
            ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card : ℝ) *
            ((k : ℝ) * (μ₀ q' - ε))) ≤
          ∑ j ∈ Finset.range m,
            (stateCount M (M.eval (digitPrefix b hb0 x (j * k)))
              (fun i : Fin k ↦ ⟨digit b x (j * k + i.val), digit_lt hb0 x _⟩) q' : ℝ) := by
        let blk : ℕ → Fin k → Fin b := fun j i ↦ ⟨digit b x (j * k + i.val), digit_lt hb0 x _⟩
        have hfib : (∑ j ∈ Finset.range m,
            (stateCount M (M.eval (digitPrefix b hb0 x (j * k))) (blk j) q' : ℝ)) =
            ∑ u : Fin k → Fin b, ∑ j ∈ (Finset.range m).filter (fun j ↦ blk j = u),
              (stateCount M (M.eval (digitPrefix b hb0 x (j * k))) (blk j) q' : ℝ) := by
          rw [Finset.sum_fiberwise_of_maps_to (fun _ _ ↦ Finset.mem_univ _)]
        rw [hfib]
        calc ∑ u ∈ G,
              (((Finset.range m).filter fun j ↦
                ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card : ℝ) *
                ((k : ℝ) * (μ₀ q' - ε))
            ≤ ∑ u ∈ G, ∑ j ∈ (Finset.range m).filter (fun j ↦ blk j = u),
                (stateCount M (M.eval (digitPrefix b hb0 x (j * k))) (blk j) q' : ℝ) := by
              refine Finset.sum_le_sum fun u hu ↦ ?_
              have hfilt : ((Finset.range m).filter fun j ↦
                  ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)) =
                  (Finset.range m).filter (fun j ↦ blk j = u) := by
                ext j
                simp only [Finset.mem_filter, blk, funext_iff, Fin.ext_iff]
              rw [hfilt, ← nsmul_eq_mul, ← Finset.sum_const]
              refine Finset.sum_le_sum fun j hj ↦ ?_
              simp only [Finset.mem_filter] at hj
              rw [hj.2]
              simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hu
              have habs := (abs_le.1 (hu (M.eval (digitPrefix b hb0 x (j * k))) q')).1
              have hkpos : (0 : ℝ) < k := by positivity
              have := (le_div_iff₀ hkpos).1 (by linarith : μ₀ q' - ε ≤
                (stateCount M (M.eval (digitPrefix b hb0 x (j * k))) u q' : ℝ) / k)
              linarith
          _ ≤ ∑ u : Fin k → Fin b, ∑ j ∈ (Finset.range m).filter (fun j ↦ blk j = u),
                (stateCount M (M.eval (digitPrefix b hb0 x (j * k))) (blk j) q' : ℝ) :=
              Finset.sum_le_univ_sum_of_nonneg fun u ↦ Finset.sum_nonneg fun j _ ↦ by positivity
      exact hstep2.trans hstep1
    -- Combine bounds on `G`, block frequencies, and `m * k ≥ N - k`
    have h1ε : 0 ≤ 1 - ε := by linarith [min_le_right (η / 5) (1 / 2)]
    have hprod_le : (1 - ε) * (1 - ε) * ((m : ℝ) * k) * (μ₀ q' - ε) ≤
        (dfaStateCount b hb0 M x q' N : ℝ) := by
      by_cases hneg : μ₀ q' - ε ≤ 0
      · have h1 : (1 - ε) * (1 - ε) * ((m : ℝ) * k) * (μ₀ q' - ε) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
        exact h1.trans (by positivity)
      · push Not at hneg
        calc (1 - ε) * (1 - ε) * ((m : ℝ) * k) * (μ₀ q' - ε)
            = ((1 - ε) * (b : ℝ) ^ k) * ((1 - ε) * (m : ℝ) / (b : ℝ) ^ k) *
                ((k : ℝ) * (μ₀ q' - ε)) := by
              field_simp [show (b : ℝ) ^ k ≠ 0 by positivity]
          _ ≤ (G.card : ℝ) * ((1 - ε) * (m : ℝ) / (b : ℝ) ^ k) * ((k : ℝ) * (μ₀ q' - ε)) := by
              gcongr
          _ = ∑ _u ∈ G, ((1 - ε) * (m : ℝ) / (b : ℝ) ^ k) * ((k : ℝ) * (μ₀ q' - ε)) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
          _ ≤ ∑ u ∈ G,
                (((Finset.range m).filter fun j ↦
                  ∀ i : Fin k, digit b x (j * k + i.val) = (u i : ℕ)).card : ℝ) *
                  ((k : ℝ) * (μ₀ q' - ε)) := by
              refine Finset.sum_le_sum fun u hu ↦ mul_le_mul_of_nonneg_right (hM₁ m hm_ge u hu)
                (by positivity)
          _ ≤ (dfaStateCount b hb0 M x q' N : ℝ) := hcount_ge
    have hN_pos : (0 : ℝ) < N := by
      have hN_nat : 0 < N :=
        lt_of_lt_of_le (by omega : 0 < k)
          (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
      positivity
    have hmk_ratio : 1 - ε ≤ ((m : ℝ) * k) / N := by
      have hdiv_mod : m * k + N % k = N := by rw [mul_comm]; exact Nat.div_add_mod N k
      have hmod : N % k < k := Nat.mod_lt N (by omega)
      have hN_ge : (k : ℝ) / ε < N := lt_of_lt_of_le hN₁ (by
        exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
      have hkN : (k : ℝ) / N < ε := by
        rw [div_lt_iff₀ hN_pos]
        have := (div_lt_iff₀ hε).1 hN_ge
        linarith
      have hsub : (N : ℝ) - k ≤ (m : ℝ) * k := by
        have h1 : (m : ℝ) * k + (N % k : ℕ) = N := by exact_mod_cast hdiv_mod
        have h2 : ((N % k : ℕ) : ℝ) < k := by exact_mod_cast hmod
        linarith
      calc 1 - ε ≤ 1 - (k : ℝ) / N := by linarith
        _ = ((N : ℝ) - k) / N := by field_simp [hN_pos.ne']
        _ ≤ ((m : ℝ) * k) / N := div_le_div_of_nonneg_right hsub hN_pos.le
    have hμ_le1 : μ₀ q' ≤ 1 := by
      calc μ₀ q' ≤ ∑ r : Q, μ₀ r := Finset.single_le_sum (fun r _ ↦ hμ₀.1.1 r) (Finset.mem_univ q')
        _ = 1 := hμ₀.1.2
    have hμ_nn : 0 ≤ μ₀ q' := hμ₀.1.1 q'
    have hdiv_le : (1 - ε) * (1 - ε) * (((m : ℝ) * k) / N) * (μ₀ q' - ε) ≤
        (dfaStateCount b hb0 M x q' N : ℝ) / N := by
      rw [show (1 - ε) * (1 - ε) * (((m : ℝ) * k) / N) * (μ₀ q' - ε) =
          (1 - ε) * (1 - ε) * ((m : ℝ) * k) * (μ₀ q' - ε) / N by ring]
      exact div_le_div_of_nonneg_right hprod_le hN_pos.le
    by_cases hneg : μ₀ q' - ε ≤ 0
    · have : μ₀ q' - η ≤ 0 := by linarith
      exact this.trans (by positivity)
    · push Not at hneg
      have hcube : (1 - ε) ^ 3 * (μ₀ q' - ε) ≤ (dfaStateCount b hb0 M x q' N : ℝ) / N := by
        calc (1 - ε) ^ 3 * (μ₀ q' - ε)
            = (1 - ε) * (1 - ε) * (1 - ε) * (μ₀ q' - ε) := by ring
          _ ≤ (1 - ε) * (1 - ε) * (((m : ℝ) * k) / N) * (μ₀ q' - ε) := by gcongr
          _ ≤ (dfaStateCount b hb0 M x q' N : ℝ) / N := hdiv_le
      have h1cube : 1 - 3 * ε ≤ (1 - ε) ^ 3 := by nlinarith [sq_nonneg ε, hε]
      have hfin : μ₀ q' - 4 * ε ≤ (1 - ε) ^ 3 * (μ₀ q' - ε) := by
        nlinarith [h1cube, hμ_le1, hμ_nn, hε, hneg]
      linarith
  -- Deduce two-sided convergence from `∑_r dfaStateCount r N / N = 1 = ∑_r μ₀ r`
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set C : ℝ := (Fintype.card Q : ℝ)
  have hC : 1 ≤ C := by
    have : 1 ≤ Fintype.card Q := Fintype.card_pos
    dsimp only [C]
    exact_mod_cast this
  set η : ℝ := δ / (2 * C)
  have hη : 0 < η := by positivity
  have hall_low : ∀ᶠ N : ℕ in atTop, ∀ r : Q,
      μ₀ r - η ≤ (dfaStateCount b hb0 M x r N : ℝ) / N :=
    ((Filter.eventually_all_finset Finset.univ).2 fun r _ ↦ hlower r hη).mono fun N hN r ↦
      hN r (Finset.mem_univ r)
  filter_upwards [hall_low, eventually_ge_atTop 1] with N hN hN1
  have hsum_cnt : ∑ r : Q, (dfaStateCount b hb0 M x r N : ℝ) / N = 1 := by
    rw [← Finset.sum_div]
    have hnat : ∑ r : Q, dfaStateCount b hb0 M x r N = N := by
      simp_rw [dfaStateCount]
      rw [← Finset.card_biUnion]
      · have huniv : (Finset.univ : Finset Q).biUnion
            (fun r ↦ (Finset.range N).filter fun i ↦ M.eval (digitPrefix b hb0 x i) = r) =
            Finset.range N := by
          ext i; simp
        rw [huniv, Finset.card_range]
      · intro r₁ _ r₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro i hi₁ hi₂
        simp only [Finset.mem_filter] at hi₁ hi₂
        exact hne (hi₁.2.symm.trans hi₂.2)
    have hcast : ∑ r : Q, (dfaStateCount b hb0 M x r N : ℝ) = N := by exact_mod_cast hnat
    rw [hcast, div_self (by positivity : (N : ℝ) ≠ 0)]
  have hlow := hN q
  have hup : (dfaStateCount b hb0 M x q N : ℝ) / N ≤ μ₀ q + C * η := by
    have hrest : ∑ r ∈ Finset.univ.erase q, (μ₀ r - η) ≤
        ∑ r ∈ Finset.univ.erase q, (dfaStateCount b hb0 M x r N : ℝ) / N :=
      Finset.sum_le_sum fun r _ ↦ hN r
    have hsum1 := Finset.add_sum_erase Finset.univ
      (fun r ↦ (dfaStateCount b hb0 M x r N : ℝ) / N) (Finset.mem_univ q)
    have hsum2 := Finset.add_sum_erase Finset.univ μ₀ (Finset.mem_univ q)
    rw [hsum_cnt] at hsum1
    rw [hμ₀.1.2] at hsum2
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ q),
      Finset.card_univ, nsmul_eq_mul] at hrest
    have hcard_le : ((Fintype.card Q - 1 : ℕ) : ℝ) ≤ C := by
      dsimp only [C]
      exact_mod_cast Nat.sub_le (Fintype.card Q) 1
    nlinarith
  rw [Real.dist_eq, abs_lt]
  have hCη : C * η = δ / 2 := by dsimp only [η]; field_simp [show C ≠ 0 by linarith]
  constructor <;> nlinarith


end Markov

end Real
