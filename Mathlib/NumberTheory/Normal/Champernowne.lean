/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.NumberTheory.Normal.Borel

/-!
# Champernowne's constant is normal

The base-`b` *Champernowne constant* is the real number `0.1 2 3 … (b-1) 10 11 …` obtained by
concatenating the base-`b` expansions of the positive integers `1, 2, 3, …`. In base ten it is
`0.12345678910111213…`. We prove **Champernowne's theorem** (D. G. Champernowne, 1933): this
number is normal in base `b` for every `b ≥ 2`.

## Main definitions

* `Real.champernowneStart b t`: the position (counted from `0`) at which the expansion of the
  integer `t + 1` starts, i.e. the total number of base-`b` digits of `1, …, t`.
* `Real.champernowneDigit b n`: the `n`-th digit of the concatenation.
* `Real.champernowne b`: the base-`b` Champernowne constant.

## Main statements

* `Real.digit_champernowne`: the base-`b` digits of `champernowne b` are `champernowneDigit b`.
* `Real.isNormalIn_champernowne`: Champernowne's theorem.

## Proof sketch

A block `w` of length `k` lying inside the expansion of an integer `m` with its last digit at
position `s` from the right occurs iff `⌊m / b ^ s⌋ ≡ code(w) [MOD b ^ k]`. For fixed `s`, the
integers `m ≤ T` that are long enough form an interval, on which this congruence holds with
frequency `b⁻ᵏ` up to an error `2 b ^ (s + k)`. Summing over `s` the total error is `O(T)`,
blocks straddling two integers contribute at most `(k - 1) T`, while the number of digits written
up to the integer `T` grows like `T log T`.

## References

* [D. G. Champernowne, *The construction of decimals normal in the scale of ten*][Champernowne1933]
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The position (counted from `0`) at which the base-`b` expansion of the integer `t + 1` starts in
the Champernowne word `1 2 3 …`, i.e. the total number of base-`b` digits of `1, …, t`. -/
def champernowneStart (b t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (Nat.log b (i + 1) + 1)

@[simp]
theorem champernowneStart_zero (b : ℕ) : champernowneStart b 0 = 0 := rfl

theorem champernowneStart_succ (b t : ℕ) :
    champernowneStart b (t + 1) = champernowneStart b t + (Nat.log b (t + 1) + 1) :=
  Finset.sum_range_succ _ _

theorem le_champernowneStart (b t : ℕ) : t ≤ champernowneStart b t := by
  induction t with
  | zero => simp
  | succ t ih => rw [champernowneStart_succ]; omega

theorem champernowneStart_mono (b : ℕ) : Monotone (champernowneStart b) :=
  monotone_nat_of_le_succ fun t ↦ by rw [champernowneStart_succ]; omega

theorem exists_lt_champernowneStart_succ (b n : ℕ) : ∃ t, n < champernowneStart b (t + 1) :=
  ⟨n, Nat.lt_of_lt_of_le n.lt_succ_self (le_champernowneStart b (n + 1))⟩

/-- The `n`-th digit (counted from `0`) of the base-`b` Champernowne word `1 2 3 …` obtained by
concatenating the base-`b` expansions of the positive integers. -/
noncomputable def champernowneDigit (b n : ℕ) : ℕ :=
  open Classical in
  let t := Nat.find (exists_lt_champernowneStart_succ b n)
  (t + 1) / b ^ (champernowneStart b (t + 1) - 1 - n) % b

/-- The base-`b` Champernowne constant `0.1 2 3 … (b-1) 10 11 …`. -/
noncomputable def champernowne (b : ℕ) [NeZero b] : ℝ :=
  ofDigits fun n ↦ Fin.ofNat b (champernowneDigit b n)

variable {b : ℕ}

theorem champernowneDigit_lt (hb : 0 < b) (n : ℕ) : champernowneDigit b n < b :=
  Nat.mod_lt _ hb

theorem champernowneStart_pos {t : ℕ} (ht : 1 ≤ t) : 0 < champernowneStart b t :=
  lt_of_lt_of_le ht (le_champernowneStart b t)

theorem champernowneStart_find_le (b n : ℕ) :
    champernowneStart b (Nat.find (exists_lt_champernowneStart_succ b n)) ≤ n := by
  rcases h : Nat.find (exists_lt_champernowneStart_succ b n) with _ | t
  · simp
  · have := Nat.find_min (exists_lt_champernowneStart_succ b n) (m := t) (by omega)
    omega

/-- Every position lies in the expansion of exactly one integer. -/
theorem exists_champernowneStart_le_lt (b n : ℕ) :
    ∃ t, champernowneStart b t ≤ n ∧ n < champernowneStart b (t + 1) :=
  ⟨_, champernowneStart_find_le b n, Nat.find_spec (exists_lt_champernowneStart_succ b n)⟩

/-- The digits of the Champernowne word at the positions occupied by the integer `t + 1`. -/
theorem champernowneDigit_eq {n t : ℕ} (ht : champernowneStart b t ≤ n)
    (hn : n < champernowneStart b (t + 1)) :
    champernowneDigit b n = (t + 1) / b ^ (champernowneStart b (t + 1) - 1 - n) % b := by
  classical
  have h : Nat.find (exists_lt_champernowneStart_succ b n) = t := by
    rw [Nat.find_eq_iff]
    refine ⟨hn, fun t' ht' ↦ ?_⟩
    have := champernowneStart_mono b (show t' + 1 ≤ t by omega)
    omega
  simp only [champernowneDigit]
  rw [h]

theorem ofDigits_lt_one {b : ℕ} (hb : 1 < b) (c : ℕ → Fin b) {m : ℕ} (hm : (c m : ℕ) + 1 < b) :
    ofDigits c < 1 := by
  rw [← ofDigits_const_last_eq_one' hb]
  refine Summable.tsum_lt_tsum_of_nonneg (i := m) (fun _ ↦ ofDigitsTerm_nonneg) (fun i ↦ ?_) ?_
    summable_ofDigitsTerm
  · exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by simp; omega)) (by positivity)
  · exact mul_lt_mul_of_pos_right (Nat.cast_lt.2 (by simp; omega)) (by positivity)

/-- If a digit sequence does not end in an infinite string of `b - 1`s, then it is the
base-`b` expansion of the real number it represents. -/
theorem digit_ofDigits {b : ℕ} (hb : 1 < b) (a : ℕ → Fin b)
    (ha : ∀ n, ∃ m, n < m ∧ (a m : ℕ) + 1 < b) (n : ℕ) : digit b (ofDigits a) n = a n := by
  set S : ℕ := ∑ i ∈ Finset.range (n + 1), (a i : ℕ) * b ^ (n - i) with hS_def
  have hS : (∑ i ∈ Finset.range (n + 1), ofDigitsTerm a i) * (b : ℝ) ^ (n + 1) = S := by
    rw [Finset.sum_mul, hS_def, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    rw [ofDigitsTerm, Nat.cast_mul, Nat.cast_pow,
      show (b : ℝ) ^ (n + 1) = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (n - i) by
        rw [← pow_add]; congr 1; omega]
    field_simp
  set y := ofDigits fun i ↦ a (i + (n + 1))
  have hy0 : 0 ≤ y := ofDigits_nonneg _
  have hy1 : y < 1 := by
    obtain ⟨m, hm, hm'⟩ := ha n
    exact ofDigits_lt_one hb _ (m := m - (n + 1)) (by rwa [Nat.sub_add_cancel hm])
  have hx : ofDigits a * (b : ℝ) ^ (n + 1) = S + y := by
    rw [ofDigits_eq_sum_add_ofDigits a (n + 1), add_mul, hS, mul_comm _ y, mul_assoc,
      inv_mul_cancel₀ (by positivity), mul_one]
  have hfl : ⌊ofDigits a * (b : ℝ) ^ (n + 1)⌋ = S := by
    rw [hx, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hmod : S % b = a n := by
    rw [hS_def, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    obtain ⟨q, hq⟩ : b ∣ ∑ i ∈ Finset.range n, (a i : ℕ) * b ^ (n - i) :=
      Finset.dvd_sum fun i hi ↦
        (dvd_pow_self b (by have := Finset.mem_range.1 hi; omega)).mul_left _
    rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt (a n).isLt]
  rw [digit, hfl, ← Int.natCast_mod, Int.toNat_natCast, hmod]

/-- The base-`b` digits of the Champernowne constant are the digits of the Champernowne word. -/
theorem digit_champernowne [NeZero b] (hb : 2 ≤ b) (n : ℕ) :
    digit b (champernowne b) n = champernowneDigit b n := by
  have hval : ∀ n, ((Fin.ofNat b (champernowneDigit b n) : Fin b) : ℕ) = champernowneDigit b n :=
    fun n ↦ by simp [Nat.mod_eq_of_lt (champernowneDigit_lt (b := b) (by omega) n)]
  rw [champernowne, digit_ofDigits (by omega), hval]
  intro n
  -- the last digit of the integer `b ^ (n + 1)` is `0`
  set t := b ^ (n + 1) - 1
  have ht : t + 1 = b ^ (n + 1) := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  have hlt : n + 1 < b ^ (n + 1) := Nat.lt_pow_self (by omega)
  have h1 := le_champernowneStart b (t + 1)
  have h2 := champernowneStart_succ b t
  refine ⟨champernowneStart b (t + 1) - 1, by omega, ?_⟩
  rw [hval, champernowneDigit_eq (t := t) (by omega) (by omega), Nat.sub_self, pow_zero,
    Nat.div_one, ht, Nat.pow_mod, Nat.mod_self, zero_pow (by omega), Nat.zero_mod]
  omega

section Counting

variable {k : ℕ}

/-- A block of `k` digits lying inside the expansion of the integer `t + 1`, ending `s` digits
before its end, is the word `w` iff `⌊(t + 1) / b ^ s⌋ ≡ blockCode w [MOD b ^ k]`. -/
theorem forall_champernowneDigit_eq_iff (hb : 0 < b) (w : Fin k → Fin b) {t s : ℕ}
    (hs : s + k ≤ Nat.log b (t + 1) + 1) :
    (∀ j : Fin k, champernowneDigit b (champernowneStart b (t + 1) - k - s + j) = w j) ↔
      (t + 1) / b ^ s % b ^ k = blockCode w := by
  rw [← forall_div_pow_mod_eq_iff hb]
  have h := champernowneStart_succ b t
  refine forall_congr' fun j ↦ ?_
  rw [champernowneDigit_eq (t := t) (by omega) (by omega),
    show champernowneStart b (t + 1) - 1 - (champernowneStart b (t + 1) - k - s + j) =
      s + (k - 1 - j) by omega, pow_add, Nat.div_div_eq_div_mul]

/-- The number of occurrences of the block `w` among the first `N` positions of the
Champernowne word. -/
noncomputable def champernowneOcc (b : ℕ) (w : Fin k → Fin b) (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range N).filter fun i ↦ ∀ j : Fin k, champernowneDigit b (i + j) = w j).card

/-- The number of occurrences of `w` lying inside the expansion of a single integer `≤ T`. -/
def champernowneInternal (b : ℕ) (w : Fin k → Fin b) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, ((Finset.range (Nat.log b (t + 1) + 1 + 1 - k)).filter fun s ↦
    (t + 1) / b ^ s % b ^ k = blockCode w).card

theorem champernowneOcc_mono (w : Fin k → Fin b) : Monotone (champernowneOcc b w) := by
  intro N N' h
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem blockCount_champernowne [NeZero b] (hb : 2 ≤ b) (w : Fin k → Fin b) (N : ℕ) :
    blockCount b (champernowne b) w N = champernowneOcc b w N := by
  simp only [blockCount, champernowneOcc, digit_champernowne hb]

theorem champernowneInternal_le_champernowneOcc (hk : 0 < k) (hb : 0 < b) (w : Fin k → Fin b)
    (T : ℕ) : champernowneInternal b w T ≤ champernowneOcc b w (champernowneStart b T) := by
  classical
  rw [champernowneInternal, ← Finset.card_sigma, champernowneOcc]
  refine Finset.card_le_card_of_injOn (fun p ↦ champernowneStart b (p.1 + 1) - k - p.2) ?_ ?_
  · rintro ⟨t, s⟩ hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨ht, hs, hQ⟩ := hp
    have h1 := champernowneStart_mono b (show t + 1 ≤ T by omega)
    have h2 := champernowneStart_succ b t
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨by omega, (forall_champernowneDigit_eq_iff hb w (by omega)).2 hQ⟩
  · rintro ⟨t, s⟩ hp ⟨t', s'⟩ hp' heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hp hp' heq
    have h1 := champernowneStart_succ b t
    have h2 := champernowneStart_succ b t'
    have htt : t = t' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := champernowneStart_mono b (show t + 1 ≤ t' by omega); omega
      · have := champernowneStart_mono b (show t' + 1 ≤ t by omega); omega
    subst htt
    have : s = s' := by omega
    subst this
    rfl

theorem champernowneOcc_le (hk : 0 < k) (hb : 0 < b) (w : Fin k → Fin b) (T : ℕ) :
    champernowneOcc b w (champernowneStart b T) ≤ champernowneInternal b w T + (k - 1) * T := by
  classical
  set σ := (Finset.range T).sigma fun t ↦ (Finset.range (Nat.log b (t + 1) + 1 + 1 - k)).filter
    fun s ↦ (t + 1) / b ^ s % b ^ k = blockCode w
  set g : (Σ _ : ℕ, ℕ) → ℕ := fun p ↦ champernowneStart b (p.1 + 1) - k - p.2
  set C := (Finset.range T).biUnion fun t ↦
    Finset.Ico (champernowneStart b (t + 1) + 1 - k) (champernowneStart b (t + 1))
  have hsub : ((Finset.range (champernowneStart b T)).filter fun i ↦
      ∀ j : Fin k, champernowneDigit b (i + j) = w j) ⊆ σ.image g ∪ C := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨t, ht1, ht2⟩ := exists_champernowneStart_le_lt b i
    have htT : t < T := by
      by_contra h
      have := champernowneStart_mono b (show T ≤ t by omega)
      omega
    have h1 := champernowneStart_succ b t
    rw [Finset.mem_union]
    by_cases hik : i + k ≤ champernowneStart b (t + 1)
    · left
      refine Finset.mem_image.2 ⟨⟨t, champernowneStart b (t + 1) - k - i⟩, ?_, ?_⟩
      · simp only [σ, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
        refine ⟨htT, by omega, (forall_champernowneDigit_eq_iff hb w (by omega)).1 ?_⟩
        rw [show champernowneStart b (t + 1) - k - (champernowneStart b (t + 1) - k - i) = i by
          omega]
        exact hi.2
      · simp only [g]
        omega
    · right
      simp only [C, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico]
      exact ⟨t, htT, by omega, ht2⟩
  rw [champernowneOcc]
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (add_le_add ?_ ?_))
  · rw [champernowneInternal, ← Finset.card_sigma]
    exact Finset.card_image_le
  · refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun t _ ↦
      (show _ ≤ k - 1 by rw [Nat.card_Ico]; omega)).trans ?_)
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

theorem geom_sum_le_pow (hb : 1 < b) (L : ℕ) : ∑ s ∈ Finset.range L, b ^ s ≤ b ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_pos (show 0 < b by omega) L]

/-- Swapping the order of summation: the positions `s` inside the integers `t + 1 ≤ T`
versus, for each `s`, the integers that are long enough to contain a block ending at `s`. -/
theorem sum_card_filter_comm (hb : 1 < b) (hk : 0 < k) (Q : ℕ → ℕ → Prop) [∀ m, DecidablePred (Q m)]
    (T : ℕ) :
    ∑ t ∈ Finset.range T, ((Finset.range (Nat.log b (t + 1) + 1 + 1 - k)).filter (Q (t + 1))).card =
      ∑ s ∈ Finset.range (Nat.log b T + 1),
        ((Finset.range T).filter fun t ↦ b ^ (s + k - 1) ≤ t + 1 ∧ Q (t + 1) s).card := by
  simp only [Finset.card_eq_sum_ones]
  refine Finset.sum_comm' fun t s ↦ ?_
  simp only [Finset.mem_range, Finset.mem_filter]
  have hlog : ∀ t, s < Nat.log b (t + 1) + 1 + 1 - k ↔ b ^ (s + k - 1) ≤ t + 1 := fun t ↦ by
    rw [← Nat.le_log_iff_pow_le hb (by omega)]
    omega
  constructor
  · rintro ⟨ht, hs, hq⟩
    have := Nat.log_mono_right (b := b) (show t + 1 ≤ T by omega)
    exact ⟨⟨ht, (hlog t).1 hs, hq⟩, by omega⟩
  · rintro ⟨⟨ht, hs, hq⟩, -⟩
    exact ⟨ht, (hlog t).2 hs, hq⟩

/-- The congruence `⌊m / b ^ s⌋ ≡ c [MOD b ^ k]` holds for a proportion `b⁻ᵏ` of the integers
`m < B`, up to an error `b ^ (s + k)`. -/
theorem abs_count_div_pow_mod_sub_le (hb : 0 < b) (s : ℕ) {c : ℕ} (hc : c < b ^ k) (B : ℕ) :
    |(b : ℝ) ^ k * Nat.count (fun m ↦ m / b ^ s % b ^ k = c) B - B| ≤ (b : ℝ) ^ (s + k) := by
  set p : ℕ → Prop := fun m ↦ m / b ^ s % b ^ k = c
  set P := b ^ s * b ^ k
  have hbs : 0 < b ^ s := pow_pos hb s
  have hbk : 0 < b ^ k := pow_pos hb k
  have hper : ∀ q j, p (q * P + j) ↔ p j := fun q j ↦ by
    simp only [p, P]
    rw [show q * (b ^ s * b ^ k) + j = j + b ^ s * (q * b ^ k) by ring,
      Nat.add_mul_div_left _ _ hbs, Nat.add_mul_mod_self_right]
  have hP : Nat.count p P = b ^ s := by
    rw [Nat.count_eq_card_filter_range]
    have : (Finset.range P).filter p = Finset.Ico (c * b ^ s) ((c + 1) * b ^ s) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, p, P]
      constructor
      · rintro ⟨hm, h⟩
        rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hm)] at h
        subst h
        exact ⟨Nat.div_mul_le_self m _, (Nat.div_lt_iff_lt_mul hbs).1 (Nat.lt_succ_self _)⟩
      · rintro ⟨h1, h2⟩
        have hdiv : m / b ^ s = c := by
          apply le_antisymm
          · exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hbs).2 h2)
          · exact (Nat.le_div_iff_mul_le hbs).2 h1
        refine ⟨?_, by rw [hdiv, Nat.mod_eq_of_lt hc]⟩
        calc m < (c + 1) * b ^ s := h2
          _ ≤ b ^ k * b ^ s := Nat.mul_le_mul_right _ hc
          _ = b ^ s * b ^ k := mul_comm _ _
    rw [this, Nat.card_Ico, ← Nat.sub_mul, Nat.add_sub_cancel_left, one_mul]
  have hshift : ∀ q n, Nat.count (fun j ↦ p (q * P + j)) n = Nat.count p n := fun q n ↦ by
    simp only [Nat.count_eq_card_filter_range]
    exact congrArg Finset.card (Finset.filter_congr fun j _ ↦ hper q j)
  have hq : ∀ q, Nat.count p (q * P) = q * b ^ s := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [add_mul, one_mul, Nat.count_add, ih, hshift, hP, add_mul, one_mul]
  have hB : B = B / P * P + B % P := (Nat.div_add_mod' B P).symm
  have hcount : Nat.count p B = B / P * b ^ s + Nat.count p (B % P) := by
    conv_lhs => rw [hB]
    rw [Nat.count_add, hq, hshift]
  have he : Nat.count p (B % P) ≤ b ^ s :=
    (Nat.count_monotone p (Nat.mod_lt B (Nat.mul_pos hbs hbk)).le).trans_eq hP
  have hr : B % P < P := Nat.mod_lt B (Nat.mul_pos hbs hbk)
  have he' : b ^ k * Nat.count p (B % P) ≤ P :=
    (Nat.mul_le_mul_left _ he).trans_eq (mul_comm _ _)
  set q := B / P
  set r := B % P
  set e := Nat.count p r
  have hBr : (B : ℝ) = q * P + r := by exact_mod_cast hB
  have hcr : (Nat.count p B : ℝ) = q * b ^ s + e := by exact_mod_cast hcount
  have hPr : (P : ℝ) = (b : ℝ) ^ s * (b : ℝ) ^ k := by simp [P]
  have he'r : (b : ℝ) ^ k * e ≤ P := by exact_mod_cast he'
  have hrr : (r : ℝ) < P := by exact_mod_cast hr
  have hsimp : (b : ℝ) ^ k * (q * (b : ℝ) ^ s + e) - (q * P + r) = (b : ℝ) ^ k * e - r := by
    rw [hPr]; ring
  have he0 : (0 : ℝ) ≤ (b : ℝ) ^ k * e := by positivity
  rw [hBr, hcr, hsimp, pow_add, ← hPr, abs_le]
  constructor <;> linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

/-- Counting `t < T` with `A ≤ t + 1` and `p (t + 1)` via `Nat.count`. -/
theorem card_filter_le_succ_add_count (p : ℕ → Prop) [DecidablePred p] {A : ℕ} (hA : 0 < A)
    {T : ℕ} (hAT : A ≤ T + 1) :
    ((Finset.range T).filter fun t ↦ A ≤ t + 1 ∧ p (t + 1)).card + Nat.count p A =
      Nat.count p (T + 1) := by
  set R : ℕ → Prop := fun m ↦ A ≤ m ∧ p m
  have h1 : ((Finset.range T).filter fun t ↦ A ≤ t + 1 ∧ p (t + 1)).card = Nat.count R (T + 1) := by
    rw [Nat.count_succ', Nat.count_eq_card_filter_range]
    simp [R, show ¬ A ≤ 0 by omega]
  have h2 : Nat.count R A = 0 := Nat.count_iff_forall_not.2 fun m hm h ↦ by simp [R] at h; omega
  obtain ⟨r, hr⟩ : ∃ r, T + 1 = A + r := ⟨T + 1 - A, by omega⟩
  rw [h1, hr, Nat.count_add, Nat.count_add, h2, zero_add, add_comm]
  congr 2
  funext j
  simp [R]

theorem card_filter_le_succ_eq_zero (p : ℕ → Prop) [DecidablePred p] {A T : ℕ}
    (hAT : T + 1 < A) :
    ((Finset.range T).filter fun t ↦ A ≤ t + 1 ∧ p (t + 1)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t ht h
  simp at ht
  omega

/-- The internal occurrences up to `T` are a proportion `b⁻ᵏ` of the internal positions, up to an
error `O(T)`. -/
theorem abs_champernowneInternal_sub_le (hb : 1 < b) (hk : 0 < k) (w : Fin k → Fin b) (T : ℕ) :
    |(b : ℝ) ^ k * champernowneInternal b w T -
        ∑ t ∈ Finset.range T, (Nat.log b (t + 1) + 1 + 1 - k : ℕ)| ≤
      2 * (b : ℝ) ^ (k + 1) * (T + 1) := by
  classical
  have hb0 : 0 < b := by omega
  set L := Nat.log b T + 1
  have hI : champernowneInternal b w T = ∑ s ∈ Finset.range L,
      ((Finset.range T).filter fun t ↦ b ^ (s + k - 1) ≤ t + 1 ∧
        (t + 1) / b ^ s % b ^ k = blockCode w).card :=
    sum_card_filter_comm hb hk (fun m s ↦ m / b ^ s % b ^ k = blockCode w) T
  have hP : ∑ t ∈ Finset.range T, (Nat.log b (t + 1) + 1 + 1 - k : ℕ) = ∑ s ∈ Finset.range L,
      ((Finset.range T).filter fun t ↦ b ^ (s + k - 1) ≤ t + 1 ∧ True).card := by
    rw [← sum_card_filter_comm hb hk (fun _ _ ↦ True) T]
    simp
  have hterm : ∀ s, |(b : ℝ) ^ k * ((Finset.range T).filter fun t ↦ b ^ (s + k - 1) ≤ t + 1 ∧
      (t + 1) / b ^ s % b ^ k = blockCode w).card -
      ((Finset.range T).filter fun t ↦ b ^ (s + k - 1) ≤ t + 1 ∧ True).card| ≤
      2 * (b : ℝ) ^ (s + k) := by
    intro s
    have hA : 0 < b ^ (s + k - 1) := pow_pos hb0 _
    by_cases hAT : b ^ (s + k - 1) ≤ T + 1
    · have h1 := card_filter_le_succ_add_count (fun m ↦ m / b ^ s % b ^ k = blockCode w) hA hAT
      have h2 := card_filter_le_succ_add_count (fun _ ↦ True) hA hAT
      rw [Nat.count_true, Nat.count_true] at h2
      have e1 := abs_count_div_pow_mod_sub_le hb0 s (blockCode w).isLt (T + 1)
      have e2 := abs_count_div_pow_mod_sub_le hb0 s (blockCode w).isLt (b ^ (s + k - 1))
      set N1 := ((Finset.range T).filter fun t ↦ b ^ (s + k - 1) ≤ t + 1 ∧
        (t + 1) / b ^ s % b ^ k = blockCode w).card
      set N0 := ((Finset.range T).filter fun t ↦ b ^ (s + k - 1) ≤ t + 1 ∧ True).card
      set cT := Nat.count (fun m ↦ m / b ^ s % b ^ k = blockCode w) (T + 1)
      set cA := Nat.count (fun m ↦ m / b ^ s % b ^ k = blockCode w) (b ^ (s + k - 1))
      have h1' : (N1 : ℝ) = cT - cA := by rw [← h1]; push_cast; ring
      have h2' : (N0 : ℝ) = (T + 1 : ℕ) - (b ^ (s + k - 1) : ℕ) := by rw [← h2]; push_cast; ring
      have : (b : ℝ) ^ k * N1 - N0 = ((b : ℝ) ^ k * cT - (T + 1 : ℕ)) -
          ((b : ℝ) ^ k * cA - (b ^ (s + k - 1) : ℕ)) := by rw [h1', h2']; ring
      rw [this]
      refine (abs_sub _ _).trans ?_
      linarith
    · rw [card_filter_le_succ_eq_zero (fun m ↦ m / b ^ s % b ^ k = blockCode w) (by omega),
        card_filter_le_succ_eq_zero (fun _ ↦ True) (by omega)]
      simp only [Nat.cast_zero, mul_zero, sub_zero, abs_zero]
      positivity
  rw [hI, hP]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun s _ ↦ hterm s).trans ?_)
  have hgeom : ∑ s ∈ Finset.range L, (b : ℝ) ^ s ≤ (b : ℝ) ^ L := by
    exact_mod_cast geom_sum_le_pow hb L
  have hL : (b : ℝ) ^ L ≤ b * (T + 1) := by
    rw [pow_succ, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp
    · have := Nat.pow_log_le_self b hT.ne'
      have : ((b ^ Nat.log b T : ℕ) : ℝ) ≤ T := by exact_mod_cast this
      push_cast at this
      linarith
  calc ∑ s ∈ Finset.range L, 2 * (b : ℝ) ^ (s + k)
      = 2 * (b : ℝ) ^ k * ∑ s ∈ Finset.range L, (b : ℝ) ^ s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ ↦ by ring
    _ ≤ 2 * (b : ℝ) ^ k * (b * (T + 1)) := by gcongr; exact hgeom.trans hL
    _ = 2 * (b : ℝ) ^ (k + 1) * (T + 1) := by ring

/-- The number of occurrences of `w` up to the end of the integer `T` is `b⁻ᵏ` times the number
of digits written, up to an error `O(T)`. -/
theorem abs_champernowneOcc_sub_le (hb : 1 < b) (hk : 0 < k) (w : Fin k → Fin b) (T : ℕ) :
    |(b : ℝ) ^ k * champernowneOcc b w (champernowneStart b T) - champernowneStart b T| ≤
      ((b : ℝ) ^ k * k + 2 * (b : ℝ) ^ (k + 1) + k) * (T + 1) := by
  have h1 := champernowneInternal_le_champernowneOcc hk (by omega) w T
  have h2 := champernowneOcc_le hk (by omega) w T
  have h3 := abs_champernowneInternal_sub_le hb hk w T
  have h4 : ∑ t ∈ Finset.range T, (Nat.log b (t + 1) + 1 + 1 - k : ℕ) ≤ champernowneStart b T :=
    Finset.sum_le_sum fun t _ ↦ by omega
  have h5 : champernowneStart b T ≤
      ∑ t ∈ Finset.range T, (Nat.log b (t + 1) + 1 + 1 - k : ℕ) + (k - 1) * T := by
    have : (k - 1) * T = ∑ _t ∈ Finset.range T, (k - 1) := by simp [mul_comm]
    rw [this, ← Finset.sum_add_distrib, champernowneStart]
    exact Finset.sum_le_sum fun t _ ↦ by omega
  set I := champernowneInternal b w T
  set O := champernowneOcc b w (champernowneStart b T)
  set P := ∑ t ∈ Finset.range T, (Nat.log b (t + 1) + 1 + 1 - k : ℕ)
  set S := champernowneStart b T
  have h1' : (I : ℝ) ≤ O := by exact_mod_cast h1
  have h2' : (O : ℝ) ≤ I + (k - 1 : ℕ) * T := by exact_mod_cast h2
  have h4' : (P : ℝ) ≤ S := by exact_mod_cast h4
  have h5' : (S : ℝ) ≤ P + (k - 1 : ℕ) * T := by exact_mod_cast h5
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hbk : (0 : ℝ) ≤ (b : ℝ) ^ k := by positivity
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  rw [abs_le] at h3 ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1' hbk, mul_le_mul_of_nonneg_left h2' hbk,
    mul_le_mul_of_nonneg_right hk1 hT,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk1 hT) hbk]

/-- Integers `≥ b ^ L` have at least `L + 1` digits. -/
theorem mul_le_champernowneStart (hb : 1 < b) (L T : ℕ) :
    (T - b ^ L) * (L + 1) ≤ champernowneStart b T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [champernowneStart_succ]
    by_cases h : b ^ L ≤ T
    · have hL : L ≤ Nat.log b (T + 1) := (Nat.le_log_iff_pow_le hb (by omega)).2 (by omega)
      rw [show T + 1 - b ^ L = (T - b ^ L) + 1 by omega, add_mul, one_mul]
      omega
    · rw [show T + 1 - b ^ L = 0 by omega, zero_mul]
      exact Nat.zero_le _

/-- The number of digits of `1, …, T` grows faster than `T`. -/
theorem tendsto_succ_div_champernowneStart (hb : 1 < b) :
    Tendsto (fun T : ℕ ↦ ((T : ℝ) + 1) / champernowneStart b T) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun T ↦ ha.trans_le (by positivity), fun a ha ↦ ?_⟩
  obtain ⟨L, hL⟩ := exists_nat_gt (4 / a)
  have hL' : 4 / ((L : ℝ) + 1) < a := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ ha] at hL
    nlinarith
  filter_upwards [eventually_ge_atTop (2 * b ^ L + 1)] with T hT
  have h1 := mul_le_champernowneStart hb L T
  have h2 : ((T - b ^ L : ℕ) : ℝ) = T - (b : ℝ) ^ L := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h3 : ((T : ℝ) + 1) / 4 * (L + 1) ≤ champernowneStart b T := by
    have : (((T - b ^ L) * (L + 1) : ℕ) : ℝ) ≤ champernowneStart b T := by exact_mod_cast h1
    push_cast at this
    rw [Nat.cast_sub (by omega)] at this
    have hT' : (2 : ℝ) * (b : ℝ) ^ L + 1 ≤ T := by exact_mod_cast hT
    push_cast at this
    nlinarith
  have hS : (0 : ℝ) < champernowneStart b T := by
    refine lt_of_lt_of_le ?_ h3
    have : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
    positivity
  refine lt_of_le_of_lt ?_ hL'
  rw [div_le_div_iff₀ hS (by positivity)]
  nlinarith

/-- The frequency of `w` at the end of the integer `T` tends to `b⁻ᵏ`. -/
theorem tendsto_champernowneOcc_champernowneStart (hb : 1 < b) (hk : 0 < k)
    (w : Fin k → Fin b) :
    Tendsto (fun T : ℕ ↦ (champernowneOcc b w (champernowneStart b T) : ℝ) /
      champernowneStart b T) atTop (𝓝 ((b : ℝ) ^ k)⁻¹) := by
  set C : ℝ := (b : ℝ) ^ k * k + 2 * (b : ℝ) ^ (k + 1) + k
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := (tendsto_succ_div_champernowneStart hb).const_mul (C / (b : ℝ) ^ k)
  rw [mul_zero] at h0
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hS : (0 : ℝ) < champernowneStart b T := by exact_mod_cast champernowneStart_pos hT
  have he := abs_champernowneOcc_sub_le hb hk w T
  simp only [Real.norm_eq_abs, abs_abs]
  have : (champernowneOcc b w (champernowneStart b T) : ℝ) / champernowneStart b T -
      ((b : ℝ) ^ k)⁻¹ = ((b : ℝ) ^ k * champernowneOcc b w (champernowneStart b T) -
        champernowneStart b T) / ((b : ℝ) ^ k * champernowneStart b T) := by
    field_simp
  rw [this, abs_div, abs_of_pos (mul_pos hbk hS), div_le_iff₀ (mul_pos hbk hS)]
  calc _ ≤ C * (T + 1) := he
    _ = C / (b : ℝ) ^ k * (((T : ℝ) + 1) / champernowneStart b T) *
        ((b : ℝ) ^ k * champernowneStart b T) := by field_simp

theorem tendsto_champernowneStart_succ_div (hb : 1 < b) :
    Tendsto (fun T : ℕ ↦ (champernowneStart b (T + 1) : ℝ) / champernowneStart b T) atTop
      (𝓝 1) := by
  have h0 := (tendsto_succ_div_champernowneStart hb).const_add 1
  rw [add_zero] at h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 ?_ ?_ <;>
    filter_upwards [eventually_ge_atTop 1] with T hT
  · have hS : (0 : ℝ) < champernowneStart b T := by exact_mod_cast champernowneStart_pos hT
    have h := champernowneStart_succ b T
    rw [le_div_iff₀ hS, one_mul]
    exact_mod_cast (show champernowneStart b T ≤ champernowneStart b (T + 1) by omega)
  · have hS : (0 : ℝ) < champernowneStart b T := by exact_mod_cast champernowneStart_pos hT
    have h := champernowneStart_succ b T
    have hlog : Nat.log b (T + 1) ≤ T :=
      Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by omega) (Nat.lt_pow_self hb))
    rw [div_le_iff₀ hS, add_mul, one_mul, div_mul_cancel₀ _ hS.ne']
    have : (champernowneStart b (T + 1) : ℝ) ≤ champernowneStart b T + (T + 1) := by
      exact_mod_cast (show champernowneStart b (T + 1) ≤ champernowneStart b T + (T + 1) by omega)
    linarith

end Counting

/-- **Champernowne's theorem**: the base-`b` Champernowne constant is normal in base `b`. -/
theorem isNormalIn_champernowne [NeZero b] (hb : 2 ≤ b) : IsNormalIn b (champernowne b) := by
  classical
  intro k w
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : ∀ N, blockCount b (champernowne b) w N = N := fun N ↦ by simp [blockCount]
    simp only [this, pow_zero, inv_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [div_self (by exact_mod_cast hN.ne')]
  simp_rw [blockCount_champernowne hb]
  have hb1 : 1 < b := by omega
  -- `T N` is the integer whose expansion contains position `N`
  set T : ℕ → ℕ := fun N ↦ Nat.find (exists_lt_champernowneStart_succ b N)
  have hT1 : ∀ N, champernowneStart b (T N) ≤ N := fun N ↦ champernowneStart_find_le b N
  have hT2 : ∀ N, N < champernowneStart b (T N + 1) := fun N ↦
    Nat.find_spec (exists_lt_champernowneStart_succ b N)
  have hT : Tendsto T atTop atTop := by
    refine tendsto_atTop_atTop.2 fun M ↦ ⟨champernowneStart b (M + 1), fun N hN ↦ ?_⟩
    by_contra h
    have := champernowneStart_mono b (show T N + 1 ≤ M + 1 by omega)
    have := hT2 N
    omega
  set F : ℕ → ℝ := fun T ↦ (champernowneOcc b w (champernowneStart b T) : ℝ) /
    champernowneStart b T
  set R : ℕ → ℝ := fun T ↦ (champernowneStart b (T + 1) : ℝ) / champernowneStart b T
  have hF := tendsto_champernowneOcc_champernowneStart hb1 hk w
  have hR := tendsto_champernowneStart_succ_div hb1
  have hup : Tendsto (fun N ↦ F (T N + 1) * R (T N)) atTop (𝓝 (((b : ℝ) ^ k)⁻¹ * 1)) :=
    (hF.comp ((tendsto_add_atTop_nat 1).comp hT)).mul (hR.comp hT)
  have hlow : Tendsto (fun N ↦ F (T N) / R (T N)) atTop (𝓝 (((b : ℝ) ^ k)⁻¹ / 1)) :=
    (hF.comp hT).div (hR.comp hT) one_ne_zero
  rw [mul_one] at hup
  rw [div_one] at hlow
  have hTN : ∀ N, 1 ≤ N → 1 ≤ T N := fun N hN ↦ by
    rcases Nat.eq_zero_or_pos (T N) with h | h
    · have := hT2 N
      rw [h, champernowneStart_succ, champernowneStart_zero, Nat.log_one_right] at this
      omega
    · exact h
  have hS0 : ∀ N, 1 ≤ N → (0 : ℝ) < champernowneStart b (T N) := fun N hN ↦ by
    exact_mod_cast champernowneStart_pos (hTN N hN)
  have hS1 : ∀ N, (0 : ℝ) < champernowneStart b (T N + 1) := fun N ↦ by
    exact_mod_cast champernowneStart_pos (b := b) (Nat.le_add_left 1 (T N))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_ <;>
    filter_upwards [eventually_ge_atTop 1] with N hN
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have e : F (T N) / R (T N) = (champernowneOcc b w (champernowneStart b (T N)) : ℝ) /
        champernowneStart b (T N + 1) := by
      have := hS0 N hN
      have := hS1 N
      simp only [F, R]; field_simp
    rw [e]
    refine div_le_div₀ (Nat.cast_nonneg _) ?_ hN0 ?_
    · exact_mod_cast champernowneOcc_mono w (hT1 N)
    · exact_mod_cast (hT2 N).le
  · have e : F (T N + 1) * R (T N) = (champernowneOcc b w (champernowneStart b (T N + 1)) : ℝ) /
        champernowneStart b (T N) := by
      have := hS0 N hN
      have := hS1 N
      simp only [F, R]; field_simp
    rw [e]
    refine div_le_div₀ (Nat.cast_nonneg _) ?_ (hS0 N hN) ?_
    · exact_mod_cast champernowneOcc_mono w (hT2 N).le
    · exact_mod_cast hT1 N

/-- The decimal Champernowne constant `0.123456789101112…` is normal in base ten. -/
theorem isNormalIn_ten_champernowne : IsNormalIn 10 (champernowne 10) :=
  isNormalIn_champernowne (by norm_num)

end Real
