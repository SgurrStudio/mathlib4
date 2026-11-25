/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Count
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.Normal.Basic

/-!
# Piatetski-Shapiro's normality criterion

**Piatetski-Shapiro** (1951) proved that a real number `x` is normal in base `b` as soon as there
is a constant `C` such that every block `w` of `k` digits has upper asymptotic frequency at most
`C * b⁻ᵏ` in the base-`b` expansion of `x`. This is the basic tool for proving normality of numbers
obtained from normal numbers by simple transformations (such as rational multiples) and of
the Stoneham numbers.

## Main statements

* `Real.isNormalIn_of_eventually_le`: Piatetski-Shapiro's normality criterion.

## Proof sketch

Along a subsequence of `N`, all block frequencies converge to a family `p(w)` which is consistent
under extending a word on the left or on the right, and satisfies `p(w) ≤ C * b^(-|w|)`. The
quantity `Q(L) = b ^ L * ∑_{|w| = L} p(w) ^ 2` is nondecreasing and bounded by `C`. Viewing
`ρ_L(w) = b ^ L * p(w)` as a function on words with the uniform measure, both `ρ_L(v)` and
`ρ_L(w)` are conditional expectations of `ρ_{2L}(v w)`, so
`2 * (Q(L) - 1) = ‖ρ_L(v) - ρ_L(w)‖² ≤ 4 * (Q(2L) - Q(L)) → 0`.
Hence `Q(L) = 1` for every `L`, which by Cauchy–Schwarz forces `p(w) = b^(-|w|)`.

## References

* [I. I. Piatetski-Shapiro, *On the laws of distribution of the fractional parts of an
  exponential function*][PiatetskiShapiro1951]
* [N. G. Moshchevitin, I. D. Shkredov, *On the Pyatetskii-Shapiro criterion of
  normality*][MoshchevitinShkredov2003]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

section Words

variable [NeZero b]

/-- The word of `L` base-`b` digits of `x` starting at position `i`. -/
noncomputable def wordAt (b : ℕ) [NeZero b] (x : ℝ) (L i : ℕ) : Fin L → Fin b :=
  fun j ↦ Fin.ofNat b (digit b x (i + j))

theorem forall_digit_eq_iff_wordAt_eq {L : ℕ} (w : Fin L → Fin b) (i : ℕ) :
    (∀ j : Fin L, digit b x (i + j) = w j) ↔ wordAt b x L i = w := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  constructor
  · intro h
    funext j
    exact Fin.ext (by simp [wordAt, h j])
  · intro h j
    rw [← h]
    simp [wordAt, Nat.mod_eq_of_lt (digit_lt hb x _)]

theorem blockCount_eq_count {L : ℕ} (w : Fin L → Fin b) (N : ℕ) :
    blockCount b x w N = Nat.count (fun i ↦ wordAt b x L i = w) N := by
  classical
  rw [blockCount, Nat.count_eq_card_filter_range]
  exact congrArg Finset.card (Finset.filter_congr fun i _ ↦ forall_digit_eq_iff_wordAt_eq w i)

theorem sum_blockCount (M N : ℕ) : ∑ u : Fin M → Fin b, blockCount b x u N = N := by
  classical
  simp only [blockCount_eq_count, Nat.count_eq_card_filter_range]
  rw [← Finset.card_eq_sum_card_fiberwise (f := wordAt b x M) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _), Finset.card_range]

theorem wordAt_add_eq_append_iff {L₁ L₂ : ℕ} (v : Fin L₁ → Fin b) (w : Fin L₂ → Fin b) (i : ℕ) :
    wordAt b x (L₁ + L₂) i = Fin.append v w ↔ wordAt b x L₁ i = v ∧ wordAt b x L₂ (i + L₁) = w := by
  constructor
  · intro h
    refine ⟨funext fun j ↦ ?_, funext fun j ↦ ?_⟩
    · have := congrFun h (Fin.castAdd L₂ j)
      simpa [wordAt, Fin.append_left] using this
    · have := congrFun h (Fin.natAdd L₁ j)
      simpa [wordAt, Fin.append_right, add_assoc] using this
  · rintro ⟨rfl, rfl⟩
    funext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · simp [wordAt, Fin.append_left]
    · simp [wordAt, Fin.append_right, add_assoc]

/-- Summing over all extensions on the right recovers the count of a word. -/
theorem sum_blockCount_append_right {L₁ L₂ : ℕ} (v : Fin L₁ → Fin b) (N : ℕ) :
    ∑ w : Fin L₂ → Fin b, blockCount b x (Fin.append v w) N = blockCount b x v N := by
  classical
  simp only [blockCount_eq_count, Nat.count_eq_card_filter_range, wordAt_add_eq_append_iff]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i ↦ wordAt b x L₂ (i + L₁))
    (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.filter_filter]

/-- Summing over all extensions on the left recovers the count of a word, up to `L₁`. -/
theorem abs_sum_blockCount_append_left_sub {L₁ L₂ : ℕ} (w : Fin L₂ → Fin b) (N : ℕ) :
    |((∑ v : Fin L₁ → Fin b, blockCount b x (Fin.append v w) N : ℕ) : ℝ) -
      blockCount b x w N| ≤ L₁ := by
  classical
  set P : ℕ → Prop := fun i ↦ wordAt b x L₂ i = w
  have hsum : ∑ v : Fin L₁ → Fin b, blockCount b x (Fin.append v w) N =
      Nat.count (fun i ↦ P (L₁ + i)) N := by
    simp only [blockCount_eq_count, Nat.count_eq_card_filter_range, wordAt_add_eq_append_iff]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i ↦ wordAt b x L₁ i)
      (s := (Finset.range N).filter fun i ↦ P (L₁ + i)) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
    simp only [P, add_comm L₁ i]
    exact and_comm
  rw [hsum, blockCount_eq_count]
  have h1 := Nat.count_add P L₁ N
  have h2 := Nat.count_add P N L₁
  have h3 : Nat.count P L₁ ≤ L₁ := Nat.count_le _
  have h4 : Nat.count (fun k ↦ P (N + k)) L₁ ≤ L₁ := Nat.count_le _
  rw [add_comm L₁ N] at h1
  rw [abs_le]
  constructor
  · have : (Nat.count P N : ℝ) ≤ Nat.count (fun i ↦ P (L₁ + i)) N + L₁ := by
      exact_mod_cast (show Nat.count P N ≤ Nat.count (fun i ↦ P (L₁ + i)) N + L₁ by omega)
    linarith
  · have : (Nat.count (fun i ↦ P (L₁ + i)) N : ℝ) ≤ Nat.count P N + L₁ := by
      exact_mod_cast (show Nat.count (fun i ↦ P (L₁ + i)) N ≤ Nat.count P N + L₁ by omega)
    linarith

/-- The normalised second moment `b ^ M * ∑_{|u| = M} p(u) ^ 2` of the frequencies `p(u)` of the
words of length `M` among the first `N` positions. -/
noncomputable def freqMoment (b : ℕ) [NeZero b] (x : ℝ) (N M : ℕ) : ℝ :=
  (b : ℝ) ^ M * ∑ u : Fin M → Fin b, ((blockCount b x u N : ℝ) / N) ^ 2

omit [NeZero b] in
theorem card_words (L : ℕ) : (Fintype.card (Fin L → Fin b) : ℝ) = (b : ℝ) ^ L := by
  simp

theorem sum_freq (M : ℕ) {N : ℕ} (hN : 0 < N) :
    ∑ u : Fin M → Fin b, (blockCount b x u N : ℝ) / N = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_blockCount, div_self (by exact_mod_cast hN.ne')]

omit [NeZero b] in
theorem sum_append (L₁ L₂ : ℕ) (g : (Fin (L₁ + L₂) → Fin b) → ℝ) :
    ∑ u, g u = ∑ v : Fin L₁ → Fin b, ∑ w : Fin L₂ → Fin b, g (Fin.append v w) := by
  rw [← Fintype.sum_prod_type', ← (Fin.appendEquiv L₁ L₂).sum_comp]
  rfl

theorem one_le_freqMoment (M : ℕ) {N : ℕ} (hN : 0 < N) : 1 ≤ freqMoment b x N M := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun u : Fin M → Fin b ↦ (blockCount b x u N : ℝ) / N)
  rw [sum_freq M hN, Finset.card_univ, card_words] at h
  simpa [freqMoment] using h

theorem freqMoment_le_freqMoment_add (N L₁ L₂ : ℕ) :
    freqMoment b x N L₁ ≤ freqMoment b x N (L₁ + L₂) := by
  rw [freqMoment, freqMoment, sum_append L₁ L₂, pow_add, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Nat.cast_nonneg b) L₁)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ ↦ ?_
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun w : Fin L₂ → Fin b ↦ (blockCount b x (Fin.append v w) N : ℝ) / N)
  rw [Finset.card_univ, card_words, ← Finset.sum_div, ← Nat.cast_sum,
    sum_blockCount_append_right] at h
  exact h

theorem freqMoment_le (M N : ℕ) {D : ℝ} (hD : ∀ u : Fin M → Fin b, (blockCount b x u N : ℝ) / N ≤ D)
    (hN : 0 < N) : freqMoment b x N M ≤ (b : ℝ) ^ M * D := by
  rw [freqMoment]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∑ u : Fin M → Fin b, ((blockCount b x u N : ℝ) / N) ^ 2
      ≤ ∑ u : Fin M → Fin b, (blockCount b x u N : ℝ) / N * D :=
        Finset.sum_le_sum fun u _ ↦ by
          rw [sq]; exact mul_le_mul_of_nonneg_left (hD u) (by positivity)
    _ = D := by rw [← Finset.sum_mul, sum_freq M hN, one_mul]

/-- The key inequality: the excess `Q(L) - 1` is controlled by the increment `Q(2L) - Q(L)`. -/
theorem freqMoment_sub_one_le (L : ℕ) {N : ℕ} (hN : 0 < N) :
    freqMoment b x N L - 1 ≤
      2 * (freqMoment b x N (L + L) - freqMoment b x N L) + 2 * (b : ℝ) ^ L * L / N := by
  set B : ℝ := (b : ℝ) ^ L
  have hb0 : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne b)
  have hB : 0 < B := by positivity
  set p : (Fin L → Fin b) → ℝ := fun v ↦ (blockCount b x v N : ℝ) / N
  set a : (Fin L → Fin b) → (Fin L → Fin b) → ℝ :=
    fun v w ↦ (blockCount b x (Fin.append v w) N : ℝ) / N
  have hp0 : ∀ v, 0 ≤ p v := fun v ↦ by positivity
  have hpsum : ∑ v, p v = 1 := sum_freq L hN
  have hrow : ∀ v, ∑ w, a v w = p v := fun v ↦ by
    simp only [a, p]
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_blockCount_append_right]
  set e : (Fin L → Fin b) → ℝ := fun w ↦ ∑ v, a v w - p w
  have he : ∀ w, |e w| ≤ L / N := fun w ↦ by
    have h := abs_sum_blockCount_append_left_sub (x := x) (L₁ := L) w N
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [e, a, p]
    rw [← Finset.sum_div, ← sub_div, abs_div, abs_of_pos hN']
    push_cast at h
    exact div_le_div_of_nonneg_right h hN'.le
  have hcol : ∀ w, ∑ v, a v w = p w + e w := fun w ↦ by simp only [e]; ring
  set X := ∑ v, p v ^ 2
  set Y := ∑ v, ∑ w, a v w ^ 2
  set Z := ∑ w, p w * e w
  have hZ : -(L / N : ℝ) ≤ Z := by
    have : |Z| ≤ L / N := by
      calc |Z| ≤ ∑ w, |p w * e w| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ w, p w * (L / N) := Finset.sum_le_sum fun w _ ↦ by
            rw [abs_mul, abs_of_nonneg (hp0 w)]
            exact mul_le_mul_of_nonneg_left (he w) (hp0 w)
        _ = L / N := by rw [← Finset.sum_mul, hpsum, one_mul]
    exact (abs_le.1 this).1
  have hQ1 : freqMoment b x N L = B * X := rfl
  have hQ2 : freqMoment b x N (L + L) = B ^ 2 * Y := by
    rw [freqMoment, sum_append, pow_add, ← sq]
  have hcard : (Fintype.card (Fin L → Fin b) : ℝ) = B := card_words L
  -- the three sums
  have S1 : ∑ v, ∑ w, (B * p v - B * p w) ^ 2 = 2 * B ^ 3 * X - 2 * B ^ 2 := by
    have : ∀ v w, (B * p v - B * p w) ^ 2 =
        B ^ 2 * p v ^ 2 - 2 * B ^ 2 * p v * p w + B ^ 2 * p w ^ 2 := fun v w ↦ by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, hcard, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    simp only [mul_assoc, hpsum, X]
    ring
  have S2 : ∑ v, ∑ w, (B ^ 2 * a v w - B * p v) ^ 2 = B ^ 4 * Y - B ^ 3 * X := by
    have : ∀ v w, (B ^ 2 * a v w - B * p v) ^ 2 =
        B ^ 4 * a v w ^ 2 - 2 * B ^ 3 * p v * a v w + B ^ 2 * p v ^ 2 := fun v w ↦ by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, hcard, nsmul_eq_mul, ← Finset.mul_sum, hrow, Y, X]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring_nf
  have S3 : ∑ v, ∑ w, (B ^ 2 * a v w - B * p w) ^ 2 = B ^ 4 * Y - B ^ 3 * X - 2 * B ^ 3 * Z := by
    have : ∀ v w, (B ^ 2 * a v w - B * p w) ^ 2 =
        B ^ 4 * a v w ^ 2 - 2 * B ^ 3 * p w * a v w + B ^ 2 * p w ^ 2 := fun v w ↦ by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun v w ↦ 2 * B ^ 3 * p w * a v w)]
    simp only [← Finset.mul_sum, hcol, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
      Y, X, Z]
    simp only [mul_add, Finset.sum_add_distrib]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring_nf
  have hpt : ∑ v, ∑ w, (B * p v - B * p w) ^ 2 ≤
      ∑ v, ∑ w, (2 * (B ^ 2 * a v w - B * p v) ^ 2 + 2 * (B ^ 2 * a v w - B * p w) ^ 2) :=
    Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun w _ ↦ by
      nlinarith [sq_nonneg (B * p v + B * p w - 2 * (B ^ 2 * a v w))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hpt
  rw [S1, S2, S3] at hpt
  rw [hQ1, hQ2]
  have key : B * X - 1 ≤ 2 * B ^ 2 * Y - 2 * B * X - 2 * B * Z := by
    have h2 : (0 : ℝ) < 2 * B ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ h2
    nlinarith
  have hBZ : -(B * (L / N)) ≤ B * Z := by nlinarith
  have : 2 * B * (L / N : ℝ) = 2 * B * L / N := by ring
  nlinarith

end Words

/-- **Piatetski-Shapiro's normality criterion**: if there is a constant `C` such that every block
`w` of `k` digits eventually has frequency at most `C * b⁻ᵏ + ε` in the base-`b` expansion of `x`,
then `x` is normal in base `b`. -/
theorem isNormalIn_of_eventually_le (hb : 2 ≤ b) {C : ℝ}
    (h : ∀ (k : ℕ) (w : Fin k → Fin b) (ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop,
      (blockCount b x w N : ℝ) / N ≤ C * ((b : ℝ) ^ k)⁻¹ + ε) :
    IsNormalIn b x := by
  have : NeZero b := ⟨by omega⟩
  intro k w
  -- Step 1: the second moment of the `k`-block frequencies tends to `1`
  have hQ : Tendsto (fun N ↦ freqMoment b x N k) atTop (𝓝 1) := by
    rw [tendsto_order]
    refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact hc.trans_le (one_le_freqMoment k hN)
    set ε := c - 1
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨J, hJ⟩ := exists_nat_gt (4 * (|C| + 1) / ε)
    have hJ0 : 0 < J := by
      have : 0 < 4 * (|C| + 1) / ε := by positivity
      exact_mod_cast this.trans hJ
    set Lj : ℕ → ℕ := fun j ↦ 2 ^ j * k
    have hLsucc : ∀ j, Lj (j + 1) = Lj j + Lj j := fun j ↦ by simp only [Lj]; ring
    -- eventual bounds
    have hev1 : ∀ᶠ N : ℕ in atTop, freqMoment b x N (Lj J) ≤ |C| + 1 := by
      set M := Lj J
      have hbM : 0 < ((b : ℝ) ^ M)⁻¹ := by positivity
      have hall : ∀ᶠ N : ℕ in atTop, ∀ u : Fin M → Fin b,
          (blockCount b x u N : ℝ) / N ≤ C * ((b : ℝ) ^ M)⁻¹ + ((b : ℝ) ^ M)⁻¹ :=
        Filter.eventually_all.2 fun u ↦ h M u _ hbM
      filter_upwards [hall, eventually_gt_atTop 0] with N hN hN0
      refine (freqMoment_le M N hN hN0).trans ?_
      have hpos : (0 : ℝ) < (b : ℝ) ^ M := by positivity
      rw [show C * ((b : ℝ) ^ M)⁻¹ + ((b : ℝ) ^ M)⁻¹ = (C + 1) * ((b : ℝ) ^ M)⁻¹ by ring,
        ← mul_assoc, mul_comm _ (C + 1), mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
      linarith [le_abs_self C]
    have hev2 : ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.range J,
        2 * (b : ℝ) ^ Lj j * (Lj j : ℝ) / N ≤ ε / 2 := by
      rw [Filter.eventually_all_finset]
      intro j _
      exact ((tendsto_const_div_atTop_nhds_zero_nat _).eventually
        (gt_mem_nhds (by positivity))).mono fun N h ↦ h.le
    filter_upwards [hev1, hev2, eventually_gt_atTop 0] with N h1 h2 hN
    set Q := fun j ↦ freqMoment b x N (Lj j)
    have hmono : ∀ j, freqMoment b x N k ≤ Q j := by
      intro j
      induction j with
      | zero => simp [Q, Lj]
      | succ j ih =>
        refine ih.trans ?_
        simp only [Q]
        rw [hLsucc]
        exact freqMoment_le_freqMoment_add N _ _
    have hstep : ∀ j ∈ Finset.range J, freqMoment b x N k - 1 ≤
        2 * (Q (j + 1) - Q j) + ε / 2 := fun j hj ↦ by
      have := freqMoment_sub_one_le (b := b) (x := x) (Lj j) hN
      simp only [Q]
      rw [hLsucc]
      linarith [hmono j, h2 j hj]
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub, Finset.sum_const,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul] at hsum
    have hQ0 : 1 ≤ Q 0 := one_le_freqMoment _ hN
    have hJ' : (J : ℝ) * ε > 4 * (|C| + 1) := by
      rw [div_lt_iff₀ hε] at hJ
      linarith
    have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ0
    -- `J * (Q - 1) ≤ 2 (|C| + 1) + J ε / 2`
    have : (J : ℝ) * (freqMoment b x N k - 1) < J * ε := by nlinarith
    have := lt_of_mul_lt_mul_left this hJpos.le
    simp only [ε] at this
    linarith
  -- Step 2: the frequencies of all `k`-blocks tend to `b⁻ᵏ`
  set c := ((b : ℝ) ^ k)⁻¹
  have hc : 0 < c := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun N ↦ c * (freqMoment b x N k - 1)) atTop (𝓝 0) := by
    have := (hQ.sub_const 1).const_mul c
    rwa [sub_self, mul_zero] at this
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  refine squeeze_zero' (Eventually.of_forall fun N ↦ norm_nonneg _) ?_ hsqrt
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.norm_eq_abs, Function.comp_apply, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  -- `∑_u (p(u) - c) ^ 2 = c * (Q - 1)`
  have hbk : ((b : ℝ) ^ k) * c = 1 := mul_inv_cancel₀ (by positivity)
  have hcard := card_words (b := b) k
  have hsum : ∑ u : Fin k → Fin b, ((blockCount b x u N : ℝ) / N - c) ^ 2 =
      c * (freqMoment b x N k - 1) := by
    have : ∀ u : Fin k → Fin b, ((blockCount b x u N : ℝ) / N - c) ^ 2 =
        ((blockCount b x u N : ℝ) / N) ^ 2 - 2 * c * ((blockCount b x u N : ℝ) / N) + c ^ 2 :=
      fun u ↦ by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_freq k hN, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, freqMoment]
    rw [show c * ((b : ℝ) ^ k * ∑ u : Fin k → Fin b, ((blockCount b x u N : ℝ) / N) ^ 2 - 1) =
      (c * (b : ℝ) ^ k) * ∑ u : Fin k → Fin b, ((blockCount b x u N : ℝ) / N) ^ 2 - c by ring,
      mul_comm c, hbk]
    have : (b : ℝ) ^ k * c ^ 2 = c := by rw [sq, ← mul_assoc, hbk, one_mul]
    rw [this]
    ring
  rw [← hsum]
  exact Finset.single_le_sum (f := fun u : Fin k → Fin b ↦
    ((blockCount b x u N : ℝ) / N - c) ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ w)

end Real
