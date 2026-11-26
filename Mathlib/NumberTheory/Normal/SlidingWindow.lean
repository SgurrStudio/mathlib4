/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.DigitOperations

/-!
# Sliding-window codes and cellular automata on normal numbers

We establish invariance of normality in base `b ≥ 2` under left-permutative and right-permutative
sliding-block codes of arbitrary radius `r`, deduce invariance for additive cellular automata,
linear shift-register codes, and differential coding modulo `b`, and contrast these with
non-balanced local rules (`min` and `max` of adjacent digits), which destroy even simple normality.

## Main statements

* `Real.isNormalSeq_leftPermutativeSliding`, `Real.isNormalIn_ofDigits_leftPermutativeSliding`:
  a left-permutative sliding-block code of radius `r` preserves normality in base `b`.
* `Real.isNormalSeq_rightPermutativeSliding`, `Real.isNormalIn_ofDigits_rightPermutativeSliding`:
  a right-permutative sliding-block code of radius `r` preserves normality in base `b`.
* `Real.isNormalSeq_add_shift_mod`, `Real.isNormalIn_ofDigits_add_shift_mod`:
  the additive cellular automaton `d_n ↦ (d_n + d_{n + 1}) % b` preserves normality in base `b`.
* `Real.isNormalSeq_linearSliding_mod`, `Real.isNormalIn_ofDigits_linearSliding_mod`:
  any linear shift-register code `d_n ↦ (d_n + ∑ j, c j * d_{n + 1 + j}) % b` preserves normality.
* `Real.isNormalSeq_sub_shift_mod`, `Real.isNormalIn_ofDigits_sub_shift_mod`:
  differential coding `d_n ↦ (d_n + b - d_{n + 1}) % b` preserves normality in base `b`.
* `Real.not_isSimplyNormalIn_ofDigits_min_shift`, `Real.not_isSimplyNormalIn_ofDigits_max_shift`:
  taking the adjacent minimum or maximum of digits destroys simple normality in base `b`.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- The sliding-window map on blocks induced by a local rule `f : (Fin (r + 1) → Fin b) → Fin b`,
sending a `(k + r)`-digit word to a `k`-digit word. -/
private def slidingBlockMap {r : ℕ} (f : (Fin (r + 1) → Fin b) → Fin b) (k : ℕ)
    (u : Fin (k + r) → Fin b) : Fin k → Fin b :=
  fun i ↦ f fun j : Fin (r + 1) ↦ u ⟨i.val + j.val, by omega⟩

/-- Finite sums of convergent real sequences converge to the sum of their limits. -/
private theorem tendsto_finset_sum_real {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ) (L : ι → ℝ)
    (h : ∀ u ∈ s, Tendsto (g u) atTop (𝓝 (L u))) :
    Tendsto (fun N ↦ ∑ u ∈ s, g u N) atTop (𝓝 (∑ u ∈ s, L u)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun u hu ↦ h u (Finset.mem_insert_of_mem hu)
    simpa [Finset.sum_insert ha] using h1.add h2

/-- For any local rule `f : (Fin (r + 1) → Fin b) → Fin b` applied to the base-`b` digits of a
normal number `x`, the asymptotic frequency of a length-`k` block `w` equals the fiber cardinality
of `slidingBlockMap f k` over `w` divided by `b ^ (k + r)`. -/
private theorem tendsto_slidingWindow_blockCount (hb : 2 ≤ b) (r : ℕ)
    (f : (Fin (r + 1) → Fin b) → Fin b) (hx : IsNormalIn b x) (k : ℕ) (w : Fin k → Fin b) :
    Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun i ↦ ∀ a : Fin k,
        (f (fun j : Fin (r + 1) ↦ ⟨digit b x (i + a + j), digit_lt (by omega) x _⟩) : ℕ) =
          (w a : ℕ)).card : ℝ) / N) atTop
      (𝓝 (((Finset.univ.filter fun u : Fin (k + r) → Fin b ↦
        slidingBlockMap f k u = w).card : ℝ) * ((b : ℝ) ^ (k + r))⁻¹)) := by
  classical
  have hb0 : 0 < b := by omega
  let d : ℕ → Fin b := fun n ↦ ⟨digit b x n, digit_lt hb0 x n⟩
  let F : Finset (Fin (k + r) → Fin b) :=
    Finset.univ.filter fun u ↦ slidingBlockMap f k u = w
  let T : (Fin (k + r) → Fin b) → ℕ → Finset ℕ := fun u N ↦
    (Finset.range N).filter fun i ↦ ∀ m : Fin (k + r), digit b x (i + m) = (u m : ℕ)
  have hcard : ∀ N : ℕ,
      ((Finset.range N).filter fun i ↦ ∀ a : Fin k,
        (f (fun j : Fin (r + 1) ↦ d (i + a + j)) : ℕ) = (w a : ℕ)).card =
      ∑ u ∈ F, (T u N).card := by
    intro N
    have hunion : ((Finset.range N).filter fun i ↦ ∀ a : Fin k,
        (f (fun j : Fin (r + 1) ↦ d (i + a + j)) : ℕ) = (w a : ℕ)) =
        F.biUnion (fun u ↦ T u N) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_univ,
        true_and, F, T]
      constructor
      · rintro ⟨hiN, hw⟩
        let u₀ : Fin (k + r) → Fin b := fun m ↦ d (i + m)
        refine ⟨u₀, ?_, hiN, fun m ↦ rfl⟩
        funext a
        apply Fin.ext
        have harg : (fun j : Fin (r + 1) ↦ u₀ ⟨a.val + j.val, by omega⟩) =
            fun j : Fin (r + 1) ↦ d (i + a + j) := by
          funext j
          exact Fin.ext (by simp [u₀, d, Nat.add_assoc])
        rw [slidingBlockMap, harg, hw a]
      · rintro ⟨u, hu, hiN, hdig⟩
        refine ⟨hiN, fun a ↦ ?_⟩
        have harg : (fun j : Fin (r + 1) ↦ d (i + a + j)) =
            fun j : Fin (r + 1) ↦ u ⟨a.val + j.val, by omega⟩ := by
          funext j
          apply Fin.ext
          simpa [d, Nat.add_assoc] using hdig ⟨a.val + j.val, by omega⟩
        rw [harg]
        exact congrArg Fin.val (congrFun hu a)
    have hdisj : Set.PairwiseDisjoint (F : Set (Fin (k + r) → Fin b)) (fun u ↦ T u N) := by
      intro u₁ _ u₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      simp only [Finset.mem_filter, T] at hi₁ hi₂
      exact hne (funext fun m ↦ Fin.ext ((hi₁.2 m).symm.trans (hi₂.2 m)))
    rw [hunion, Finset.card_biUnion hdisj]
  have hsum : Tendsto (fun N : ℕ ↦ ∑ u ∈ F, ((T u N).card : ℝ) / N) atTop
      (𝓝 (∑ _u ∈ F, ((b : ℝ) ^ (k + r))⁻¹)) :=
    tendsto_finset_sum_real F (fun u N ↦ ((T u N).card : ℝ) / N)
      (fun _ ↦ ((b : ℝ) ^ (k + r))⁻¹) fun u _ ↦ by
        simpa [blockCount, T] using hx (k + r) u
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  refine hsum.congr fun N ↦ ?_
  rw [← Finset.sum_div, ← Nat.cast_sum, ← hcard N]

/-- If every fiber of `slidingBlockMap f k` has cardinality `b ^ r`, then applying the local rule
`f` to the base-`b` digits of a normal number yields a normal digit sequence. -/
private theorem isNormalSeq_of_slidingBlockMap_fiber_card (hb : 2 ≤ b) (r : ℕ)
    (f : (Fin (r + 1) → Fin b) → Fin b) (hx : IsNormalIn b x)
    (hcard : ∀ (k : ℕ) (w : Fin k → Fin b),
      (Finset.univ.filter fun u : Fin (k + r) → Fin b ↦ slidingBlockMap f k u = w).card = b ^ r) :
    IsNormalSeq b fun n ↦
      (f (fun j : Fin (r + 1) ↦ ⟨digit b x (n + j), digit_lt (by omega) x _⟩) : ℕ) := by
  intro k w
  have h := tendsto_slidingWindow_blockCount hb r f hx k w
  rw [hcard k w] at h
  have hlim : ((b ^ r : ℕ) : ℝ) * ((b : ℝ) ^ (k + r))⁻¹ = ((b : ℝ) ^ k)⁻¹ := by
    have hbr : (b : ℝ) ^ r ≠ 0 := pow_ne_zero r (by positivity)
    rw [Nat.cast_pow, pow_add, mul_inv, mul_left_comm, mul_inv_cancel₀ hbr, mul_one]
  rwa [hlim] at h

/-- Every fiber of a left-permutative sliding-block map has cardinality `b ^ r`. -/
private theorem card_fiber_leftPermutativeSliding (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) :
    ∀ (k : ℕ) (w : Fin k → Fin b),
      (Finset.univ.filter fun u : Fin (k + r) → Fin b ↦
        slidingBlockMap (fun v ↦ σ (fun j : Fin r ↦ v ⟨1 + j.val, by omega⟩) (v ⟨0, by omega⟩))
          k u = w).card = b ^ r := by
  intro k
  induction k with
  | zero =>
    intro w
    have htriv : (Finset.univ.filter fun u : Fin (0 + r) → Fin b ↦
        slidingBlockMap (fun v ↦ σ (fun j : Fin r ↦ v ⟨1 + j.val, by omega⟩) (v ⟨0, by omega⟩))
          0 u = w) = Finset.univ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      funext a
      exact a.elim0
    rw [htriv, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, zero_add]
  | succ k ih =>
    intro w
    let w' : Fin k → Fin b := fun a ↦ w ⟨a.val + 1, by omega⟩
    rw [← ih w']
    refine Finset.card_nbij'
      (fun u m ↦ u ⟨m.val + 1, by omega⟩)
      (fun u' m ↦ if h : m.val = 0 then
        (σ (fun l : Fin r ↦ u' ⟨l.val, by omega⟩)).symm (w ⟨0, by omega⟩)
        else u' ⟨m.val - 1, by omega⟩) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
      funext a
      have ha := congrFun hu ⟨a.val + 1, by omega⟩
      simp only [slidingBlockMap] at ha ⊢
      convert ha using 1
      refine congrArg₂ (fun g y ↦ σ g y) ?_ rfl
      funext l
      congr 1
      exact Fin.ext (by dsimp only; omega)
    · intro u' hu'
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu' ⊢
      funext a
      simp only [slidingBlockMap]
      by_cases ha0 : a.val = 0
      · have harg : (fun l : Fin r ↦
            if h : a.val + (1 + l.val) = 0 then
              (σ (fun l' : Fin r ↦ u' ⟨l'.val, by omega⟩)).symm (w ⟨0, by omega⟩)
            else u' ⟨a.val + (1 + l.val) - 1, by omega⟩) =
            fun l : Fin r ↦ u' ⟨l.val, by omega⟩ := by
          funext l
          split_ifs with h
          · omega
          · congr 1
            exact Fin.ext (by dsimp only; omega)
        have hval : (if h : a.val + 0 = 0 then
            (σ (fun l' : Fin r ↦ u' ⟨l'.val, by omega⟩)).symm (w ⟨0, by omega⟩)
            else u' ⟨a.val + 0 - 1, by omega⟩) =
            (σ (fun l' : Fin r ↦ u' ⟨l'.val, by omega⟩)).symm (w ⟨0, by omega⟩) := by
          split_ifs with h
          · rfl
          · omega
        rw [harg, hval, Equiv.apply_symm_apply]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · let a' : Fin k := ⟨a.val - 1, by omega⟩
        have hstep := congrFun hu' a'
        simp only [slidingBlockMap] at hstep
        have harg : (fun l : Fin r ↦
            if h : a.val + (1 + l.val) = 0 then
              (σ (fun l' : Fin r ↦ u' ⟨l'.val, by omega⟩)).symm (w ⟨0, by omega⟩)
            else u' ⟨a.val + (1 + l.val) - 1, by omega⟩) =
            fun l : Fin r ↦ u' ⟨a'.val + (1 + l.val), by omega⟩ := by
          funext l
          split_ifs with h
          · omega
          · congr 1
            exact Fin.ext (by dsimp only [a']; omega)
        have hval : (if h : a.val + 0 = 0 then
            (σ (fun l' : Fin r ↦ u' ⟨l'.val, by omega⟩)).symm (w ⟨0, by omega⟩)
            else u' ⟨a.val + 0 - 1, by omega⟩) = u' ⟨a'.val + 0, by omega⟩ := by
          split_ifs with h
          · omega
          · rfl
        rw [harg, hval, hstep]
        dsimp only [w', a']
        congr 1
        exact Fin.ext (by dsimp only; omega)
    · intro u hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
      funext m
      dsimp only
      split_ifs with hm0
      · have h0 := congrFun hu ⟨0, by omega⟩
        simp only [slidingBlockMap] at h0
        have harg : (fun l : Fin r ↦ u ⟨l.val + 1, by omega⟩) =
            fun l : Fin r ↦ u ⟨0 + (1 + l.val), by omega⟩ := by
          funext l
          congr 1
          exact Fin.ext (by dsimp only; omega)
        rw [harg, ← h0, Equiv.symm_apply_apply]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · congr 1
        exact Fin.ext (by dsimp only; omega)
    · intro u' _
      funext m
      simp

/-- **Left-permutative sliding-block code invariance (digit sequences)**: applying any
radius-`r` family of digit permutations `σ : (Fin r → Fin b) → Equiv.Perm (Fin b)` to the current
digit `digit b x n` conditioned on the next `r` digits `digit b x (n + 1 + j)` preserves
normality in base `b ≥ 2`. -/
theorem isNormalSeq_leftPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦
      (σ (fun j ↦ ⟨digit b x (n + 1 + j), digit_lt (by omega) x _⟩)
        ⟨digit b x n, digit_lt (by omega) x n⟩ : ℕ) := by
  let f : (Fin (r + 1) → Fin b) → Fin b :=
    fun v ↦ σ (fun j : Fin r ↦ v ⟨1 + j.val, by omega⟩) (v ⟨0, by omega⟩)
  have h := isNormalSeq_of_slidingBlockMap_fiber_card hb r f hx
    (card_fiber_leftPermutativeSliding r σ)
  have heq : (fun n ↦ (f (fun j : Fin (r + 1) ↦
      ⟨digit b x (n + j), digit_lt (by omega) x _⟩) : ℕ)) =
      fun n ↦ (σ (fun j ↦ ⟨digit b x (n + 1 + j), digit_lt (by omega) x _⟩)
        ⟨digit b x n, digit_lt (by omega) x n⟩ : ℕ) := by
    funext n
    simp only [f]
    congr 1
    refine congrArg₂ (fun g a ↦ σ g a) ?_ (Fin.ext (by simp))
    funext j
    exact Fin.ext (by simp [Nat.add_assoc])
  rwa [heq] at h

/-- **Left-permutative sliding-block code invariance**: applying any radius-`r` left-permutative
sliding-block code to the base-`b` digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_leftPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      σ (fun j ↦ ⟨digit b x (n + 1 + j), digit_lt (by omega) x _⟩)
        ⟨digit b x n, digit_lt (by omega) x n⟩) :=
  isNormalIn_ofDigits hb (isNormalSeq_leftPermutativeSliding hb r σ hx)

/-- Every fiber of a right-permutative sliding-block map has cardinality `b ^ r`. -/
private theorem card_fiber_rightPermutativeSliding (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) :
    ∀ (k : ℕ) (w : Fin k → Fin b),
      (Finset.univ.filter fun u : Fin (k + r) → Fin b ↦
        slidingBlockMap (fun v ↦ σ (fun j : Fin r ↦ v ⟨j.val, by omega⟩) (v ⟨r, by omega⟩))
          k u = w).card = b ^ r := by
  intro k
  induction k with
  | zero =>
    intro w
    have htriv : (Finset.univ.filter fun u : Fin (0 + r) → Fin b ↦
        slidingBlockMap (fun v ↦ σ (fun j : Fin r ↦ v ⟨j.val, by omega⟩) (v ⟨r, by omega⟩))
          0 u = w) = Finset.univ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      funext a
      exact a.elim0
    rw [htriv, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, zero_add]
  | succ k ih =>
    intro w
    let w' : Fin k → Fin b := fun a ↦ w ⟨a.val, by omega⟩
    rw [← ih w']
    refine Finset.card_nbij'
      (fun u m ↦ u ⟨m.val, by omega⟩)
      (fun u' m ↦ if h : m.val < k + r then u' ⟨m.val, h⟩
        else (σ (fun l : Fin r ↦ u' ⟨k + l.val, by omega⟩)).symm (w ⟨k, by omega⟩)) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
      funext a
      exact congrFun hu ⟨a.val, by omega⟩
    · intro u' hu'
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu' ⊢
      funext a
      simp only [slidingBlockMap]
      by_cases hak : a.val < k
      · have hstep := congrFun hu' ⟨a.val, hak⟩
        simp only [slidingBlockMap] at hstep
        have harg : (fun l : Fin r ↦
            if h : a.val + l.val < k + r then u' ⟨a.val + l.val, h⟩
            else (σ (fun l' : Fin r ↦ u' ⟨k + l'.val, by omega⟩)).symm (w ⟨k, by omega⟩)) =
            fun l : Fin r ↦ u' ⟨a.val + l.val, by omega⟩ := by
          funext l
          split_ifs with h
          · rfl
          · omega
        have hval : (if h : a.val + r < k + r then u' ⟨a.val + r, h⟩
            else (σ (fun l' : Fin r ↦ u' ⟨k + l'.val, by omega⟩)).symm (w ⟨k, by omega⟩)) =
            u' ⟨a.val + r, by omega⟩ := by
          split_ifs with h
          · rfl
          · omega
        rw [harg, hval, hstep]
      · have harg : (fun l : Fin r ↦
            if h : a.val + l.val < k + r then u' ⟨a.val + l.val, h⟩
            else (σ (fun l' : Fin r ↦ u' ⟨k + l'.val, by omega⟩)).symm (w ⟨k, by omega⟩)) =
            fun l : Fin r ↦ u' ⟨k + l.val, by omega⟩ := by
          funext l
          split_ifs with h
          · congr 1
            exact Fin.ext (by dsimp only; omega)
          · omega
        have hval : (if h : a.val + r < k + r then u' ⟨a.val + r, h⟩
            else (σ (fun l' : Fin r ↦ u' ⟨k + l'.val, by omega⟩)).symm (w ⟨k, by omega⟩)) =
            (σ (fun l' : Fin r ↦ u' ⟨k + l'.val, by omega⟩)).symm (w ⟨k, by omega⟩) := by
          split_ifs with h
          · omega
          · rfl
        rw [harg, hval, Equiv.apply_symm_apply]
        congr 1
        exact Fin.ext (by dsimp only; omega)
    · intro u hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
      funext m
      dsimp only
      split_ifs with hlt
      · rfl
      · have hk := congrFun hu ⟨k, by omega⟩
        simp only [slidingBlockMap] at hk
        rw [← hk, Equiv.symm_apply_apply]
        congr 1
        exact Fin.ext (by dsimp only; omega)
    · intro u' _
      funext m
      dsimp only
      split_ifs with h
      · rfl
      · omega

/-- **Right-permutative sliding-block code invariance (digit sequences)**: applying any
radius-`r` family of digit permutations `σ : (Fin r → Fin b) → Equiv.Perm (Fin b)` to the digit
`digit b x (n + r)` conditioned on the preceding `r` digits `digit b x (n + j)` preserves
normality in base `b ≥ 2`. -/
theorem isNormalSeq_rightPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦
      (σ (fun j ↦ ⟨digit b x (n + j), digit_lt (by omega) x _⟩)
        ⟨digit b x (n + r), digit_lt (by omega) x _⟩ : ℕ) := by
  let f : (Fin (r + 1) → Fin b) → Fin b :=
    fun v ↦ σ (fun j : Fin r ↦ v ⟨j.val, by omega⟩) (v ⟨r, by omega⟩)
  exact isNormalSeq_of_slidingBlockMap_fiber_card hb r f hx
    (card_fiber_rightPermutativeSliding r σ)

/-- **Right-permutative sliding-block code invariance**: applying any radius-`r` right-permutative
sliding-block code to the base-`b` digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_rightPermutativeSliding (hb : 2 ≤ b) (r : ℕ)
    (σ : (Fin r → Fin b) → Equiv.Perm (Fin b)) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      σ (fun j ↦ ⟨digit b x (n + j), digit_lt (by omega) x _⟩)
        ⟨digit b x (n + r), digit_lt (by omega) x _⟩) :=
  isNormalIn_ofDigits hb (isNormalSeq_rightPermutativeSliding hb r σ hx)

/-- **Linear shift-register invariance (digit sequences)**: for any coefficients `c : Fin r → ℕ`,
the linear sliding-window code `n ↦ (digit b x n + ∑ j, c j * digit b x (n + 1 + j)) % b`
preserves normality in base `b ≥ 2`. -/
theorem isNormalSeq_linearSliding_mod (hb : 2 ≤ b) {r : ℕ} (c : Fin r → ℕ) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + ∑ j : Fin r, c j * digit b x (n + 1 + j)) % b := by
  have : NeZero b := ⟨by omega⟩
  let σ : (Fin r → Fin b) → Equiv.Perm (Fin b) :=
    fun v ↦ Equiv.addRight (Fin.ofNat b (∑ j : Fin r, c j * (v j : ℕ)))
  have h := isNormalSeq_leftPermutativeSliding hb r σ hx
  have heq : (fun n ↦ (σ (fun j ↦ ⟨digit b x (n + 1 + j), digit_lt (by omega) x _⟩)
      ⟨digit b x n, digit_lt (by omega) x n⟩ : ℕ)) =
      fun n ↦ (digit b x n + ∑ j : Fin r, c j * digit b x (n + 1 + j)) % b := by
    funext n
    simp only [σ, Equiv.coe_addRight, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
  rwa [heq] at h

/-- **Linear shift-register invariance**: for any coefficients `c : Fin r → ℕ`, the linear
sliding-window code `n ↦ (digit b x n + ∑ j, c j * digit b x (n + 1 + j)) % b` maps a base-`b`
normal number to a base-`b` normal real number. -/
theorem isNormalIn_ofDigits_linearSliding_mod (hb : 2 ≤ b) {r : ℕ} (c : Fin r → ℕ)
    (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨(digit b x n + ∑ j : Fin r, c j * digit b x (n + 1 + j)) % b,
        Nat.mod_lt _ (by omega)⟩ : Fin b)) :=
  isNormalIn_ofDigits hb (isNormalSeq_linearSliding_mod hb c hx)

/-- **Additive cellular automaton invariance (digit sequences)**: replacing each digit by
`(digit b x n + digit b x (n + 1)) % b` preserves normality in base `b ≥ 2`. -/
theorem isNormalSeq_add_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + digit b x (n + 1)) % b := by
  have h := isNormalSeq_linearSliding_mod hb (fun _ : Fin 1 ↦ 1) hx
  simpa using h

/-- **Additive cellular automaton invariance**: replacing each digit by
`(digit b x n + digit b x (n + 1)) % b` maps a base-`b` normal number to a base-`b` normal real
number. -/
theorem isNormalIn_ofDigits_add_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨(digit b x n + digit b x (n + 1)) % b, Nat.mod_lt _ (by omega)⟩ : Fin b)) :=
  isNormalIn_ofDigits hb (isNormalSeq_add_shift_mod hb hx)

/-- **Differential coding invariance (digit sequences)**: replacing each digit by
`(digit b x n + b - digit b x (n + 1)) % b` preserves normality in base `b ≥ 2`. -/
theorem isNormalSeq_sub_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + b - digit b x (n + 1)) % b := by
  have h := isNormalSeq_linearSliding_mod hb (fun _ : Fin 1 ↦ b - 1) hx
  have heq : (fun n ↦ (digit b x n + ∑ j : Fin 1, (b - 1) * digit b x (n + 1 + j)) % b) =
      fun n ↦ (digit b x n + b - digit b x (n + 1)) % b := by
    funext n
    simp only [Fin.sum_univ_one, Fin.val_zero, add_zero]
    set d₀ := digit b x n
    set d₁ := digit b x (n + 1)
    have hd₁ : d₁ < b := digit_lt (by omega) x (n + 1)
    have hmul : (b - 1) * d₁ + d₁ = b * d₁ := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel]
      exact Nat.le_mul_of_pos_left d₁ (by omega)
    have hid : d₀ + (b - 1) * d₁ + b = d₀ + b - d₁ + b * d₁ := by omega
    calc (d₀ + (b - 1) * d₁) % b
        = (d₀ + (b - 1) * d₁ + b) % b := (Nat.add_mod_right _ b).symm
      _ = (d₀ + b - d₁ + b * d₁) % b := by rw [hid]
      _ = (d₀ + b - d₁) % b := Nat.add_mul_mod_self_left _ b d₁
  rwa [heq] at h

/-- **Differential coding invariance**: replacing each digit by
`(digit b x n + b - digit b x (n + 1)) % b` maps a base-`b` normal number to a base-`b` normal
real number. -/
theorem isNormalIn_ofDigits_sub_shift_mod (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨(digit b x n + b - digit b x (n + 1)) % b, Nat.mod_lt _ (by omega)⟩ : Fin b)) :=
  isNormalIn_ofDigits hb (isNormalSeq_sub_shift_mod hb hx)

/-- Every block of two zeros occurs arbitrarily far out in the base-`b` expansion of a normal
number. -/
private theorem exists_gt_digit_zero_pair (hb : 2 ≤ b) (hx : IsNormalIn b x) (n : ℕ) :
    ∃ m, n < m ∧ digit b x m = 0 ∧ digit b x (m + 1) = 0 := by
  have hx' : IsNormalIn b (x * (b : ℝ) ^ (n + 1)) := (isNormalIn_mul_pow_iff (n + 1)).2 hx
  obtain ⟨i, hi⟩ := hx'.isDisjunctiveIn 2 (fun _ ↦ ⟨0, by omega⟩)
  refine ⟨n + 1 + i, by omega, ?_, ?_⟩
  · have h0 := hi 0
    rw [← digit_add] at h0
    simpa [Nat.add_assoc] using h0
  · have h1 := hi 1
    rw [← digit_add] at h1
    simpa [Nat.add_assoc] using h1

/-- Taking the adjacent minimum of base-`b` digits of a normal number destroys even simple
normality: digit `0` occurs with asymptotic frequency `(2 b - 1) / b ^ 2 ≠ 1 / b`. -/
theorem not_isSimplyNormalIn_ofDigits_min_shift (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsSimplyNormalIn b (ofDigits fun n ↦
      (⟨min (digit b x n) (digit b x (n + 1)),
        lt_of_le_of_lt (min_le_left _ _) (digit_lt (by omega) x n)⟩ : Fin b)) := by
  classical
  have hb0 : 0 < b := by omega
  let a : ℕ → Fin b := fun n ↦
    ⟨min (digit b x n) (digit b x (n + 1)),
      lt_of_le_of_lt (min_le_left _ _) (digit_lt hb0 x n)⟩
  have hdig : ∀ n, digit b (ofDigits a) n = min (digit b x n) (digit b x (n + 1)) := by
    refine digit_ofDigits (by omega) a fun n ↦ ?_
    obtain ⟨m, hm, h0, h1⟩ := exists_gt_digit_zero_pair hb hx n
    refine ⟨m, hm, ?_⟩
    simp only [a, h0, h1, min_self]
    omega
  let f : (Fin 2 → Fin b) → Fin b := fun v ↦ min (v 0) (v 1)
  let w0 : Fin 1 → Fin b := fun _ ↦ ⟨0, hb0⟩
  have hfreq := tendsto_slidingWindow_blockCount hb 1 f hx 1 w0
  have hcard_fiber :
      (Finset.univ.filter fun u : Fin (1 + 1) → Fin b ↦ slidingBlockMap f 1 u = w0).card =
        2 * b - 1 := by
    let A : Finset (Fin 2 → Fin b) := Finset.univ.filter fun u ↦ u 0 = ⟨0, hb0⟩
    let B : Finset (Fin 2 → Fin b) := Finset.univ.filter fun u ↦ u 1 = ⟨0, hb0⟩
    have hEq : (Finset.univ.filter fun u : Fin (1 + 1) → Fin b ↦
        slidingBlockMap f 1 u = w0) = A ∪ B := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, A, B,
        funext_iff, Fin.forall_fin_one, slidingBlockMap, f, w0, Fin.ext_iff, Fin.val_min,
        Nat.min_eq_zero_iff]
      rfl
    have hA : A.card = b := by
      calc A.card = (Finset.univ : Finset (Fin b)).card := by
            refine Finset.card_nbij' (fun u ↦ u 1) (fun c i ↦ if i = 0 then ⟨0, hb0⟩ else c)
              ?_ ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro c _; simp [A]
            · intro u hu
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, A] at hu
              funext i
              fin_cases i <;> simp [hu]
            · intro c _; simp
        _ = b := by simp
    have hB : B.card = b := by
      calc B.card = (Finset.univ : Finset (Fin b)).card := by
            refine Finset.card_nbij' (fun u ↦ u 0) (fun c i ↦ if i = 1 then ⟨0, hb0⟩ else c)
              ?_ ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro c _; simp [B]
            · intro u hu
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, B] at hu
              funext i
              fin_cases i <;> simp [hu]
            · intro c _; simp
        _ = b := by simp
    have hAB : (A ∩ B).card = 1 := by
      have hsing : A ∩ B = {fun _ : Fin 2 ↦ ⟨0, hb0⟩} := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, funext_iff, Fin.forall_fin_two, A, B]
      rw [hsing, Finset.card_singleton]
    have huni := Finset.card_union_add_card_inter A B
    rw [hEq]
    omega
  rw [hcard_fiber] at hfreq
  intro hsn
  have hsn0 := hsn ⟨0, hb0⟩
  have hcongr : Tendsto (fun N : ℕ ↦ (blockCount b (ofDigits a) w0 N : ℝ) / N) atTop
      (𝓝 (((2 * b - 1 : ℕ) : ℝ) * ((b : ℝ) ^ (1 + 1))⁻¹)) := by
    refine hfreq.congr fun N ↦ ?_
    congr 2
    rw [blockCount]
    refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
    simp only [Fin.forall_fin_one, Fin.val_zero, add_zero, hdig, f, w0, Fin.val_min]
    rfl
  have heq := tendsto_nhds_unique hsn0 hcongr
  have hcast : ((2 * b - 1 : ℕ) : ℝ) = 2 * (b : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hcast] at heq
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hb2 : (b : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hbR
  have hmul : (b : ℝ) = 2 * (b : ℝ) - 1 := by
    have h1 := congrArg (· * (b : ℝ) ^ 2) heq
    rw [show (1 : ℕ) + 1 = 2 by rfl] at h1
    rw [mul_assoc, inv_mul_cancel₀ hb2, mul_one, sq, ← mul_assoc, inv_mul_cancel₀ hbR, one_mul]
      at h1
    exact h1
  have hb_ge : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

/-- Taking the adjacent maximum of base-`b` digits of a normal number destroys even simple
normality: digit `0` occurs with asymptotic frequency `1 / b ^ 2 ≠ 1 / b`. -/
theorem not_isSimplyNormalIn_ofDigits_max_shift (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsSimplyNormalIn b (ofDigits fun n ↦
      (⟨max (digit b x n) (digit b x (n + 1)),
        max_lt (digit_lt (by omega) x n) (digit_lt (by omega) x (n + 1))⟩ : Fin b)) := by
  classical
  have hb0 : 0 < b := by omega
  let a : ℕ → Fin b := fun n ↦
    ⟨max (digit b x n) (digit b x (n + 1)),
      max_lt (digit_lt hb0 x n) (digit_lt hb0 x (n + 1))⟩
  have hdig : ∀ n, digit b (ofDigits a) n = max (digit b x n) (digit b x (n + 1)) := by
    refine digit_ofDigits (by omega) a fun n ↦ ?_
    obtain ⟨m, hm, h0, h1⟩ := exists_gt_digit_zero_pair hb hx n
    refine ⟨m, hm, ?_⟩
    simp only [a, h0, h1, max_self]
    omega
  let f : (Fin 2 → Fin b) → Fin b := fun v ↦ max (v 0) (v 1)
  let w0 : Fin 1 → Fin b := fun _ ↦ ⟨0, hb0⟩
  have hfreq := tendsto_slidingWindow_blockCount hb 1 f hx 1 w0
  have hcard_fiber :
      (Finset.univ.filter fun u : Fin (1 + 1) → Fin b ↦ slidingBlockMap f 1 u = w0).card = 1 := by
    have hsing : (Finset.univ.filter fun u : Fin (1 + 1) → Fin b ↦
        slidingBlockMap f 1 u = w0) = {fun _ : Fin 2 ↦ ⟨0, hb0⟩} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        funext_iff, Fin.forall_fin_one, slidingBlockMap, f, w0, Fin.ext_iff, Fin.val_max,
        Nat.max_eq_zero_iff]
      constructor
      · rintro ⟨h0, h1⟩ i
        fin_cases i
        · exact h0
        · exact h1
      · intro h
        exact ⟨h 0, h 1⟩
    rw [hsing, Finset.card_singleton]
  rw [hcard_fiber, Nat.cast_one] at hfreq
  intro hsn
  have hsn0 := hsn ⟨0, hb0⟩
  have hcongr : Tendsto (fun N : ℕ ↦ (blockCount b (ofDigits a) w0 N : ℝ) / N) atTop
      (𝓝 ((1 : ℝ) * ((b : ℝ) ^ (1 + 1))⁻¹)) := by
    refine hfreq.congr fun N ↦ ?_
    congr 2
    rw [blockCount]
    refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
    simp only [Fin.forall_fin_one, Fin.val_zero, add_zero, hdig, f, w0, Fin.val_max]
    rfl
  have heq := tendsto_nhds_unique hsn0 hcongr
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hb2 : (b : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hbR
  have hmul : (b : ℝ) = 1 := by
    have h1 := congrArg (· * (b : ℝ) ^ 2) heq
    rw [show (1 : ℕ) + 1 = 2 by rfl, one_mul] at h1
    rw [inv_mul_cancel₀ hb2, sq, ← mul_assoc, inv_mul_cancel₀ hbR, one_mul] at h1
    exact h1
  have hb_ge : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

end Real
