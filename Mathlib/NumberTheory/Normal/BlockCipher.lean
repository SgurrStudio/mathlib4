/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.DigitOperations

/-!
# Block-cipher and periodic-mask invariance vs. digit-doubling separation

We establish invariance of normality in base `b ≥ 2` under aligned block-level bijections,
periodic digit-wise modular shifts, and fixed-width block-coordinate permutations, and contrast
these with digit-doubling (self-interleaving), which preserves simple normality while destroying
full normality.

## Main statements

* `Real.isNormalIn_ofDigits_blockPerm`: permuting aligned `L`-digit blocks via any
  `σ : Equiv.Perm (Fin (b ^ L))` preserves normality in base `b`.
* `Real.isNormalSeq_add_periodic_mod`, `Real.isNormalIn_ofDigits_add_periodic_mod`: adding a
  periodic mask modulo `b` to the base-`b` digits of a normal number preserves normality.
* `Real.isNormalSeq_blockCoordPerm`, `Real.isNormalIn_ofDigits_blockCoordPerm`: permuting
  coordinates within each aligned `L`-digit block preserves normality in base `b`.
* `Real.isSimplyNormalIn_digitDouble`, `Real.not_isNormalIn_digitDouble`: repeating each digit
  of a base-`b` normal number twice produces a number that is simply normal in base `b` but not
  normal in base `b`.
* `Real.exists_isSimplyNormalIn_not_isNormalIn`: for every base `b ≥ 2`, there exists a real
  number that is simply normal in base `b` but not normal in base `b`.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b L : ℕ} {x : ℝ}

/-- **Block-cipher invariance**: permuting aligned `L`-digit blocks of a base-`b` normal number
via any permutation `σ : Equiv.Perm (Fin (b ^ L))` preserves normality in base `b`. -/
theorem isNormalIn_ofDigits_blockPerm (hb : 2 ≤ b) (hL : 1 ≤ L)
    (σ : Equiv.Perm (Fin (b ^ L))) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits (b := b ^ L) fun n ↦
      σ ⟨digit (b ^ L) x n, digit_lt (by positivity) x n⟩) := by
  have hbL : 2 ≤ b ^ L := hb.trans (Nat.le_self_pow (by omega) b)
  have hxL : IsNormalIn (b ^ L) x := (isNormalIn_pow_iff hb (by omega)).2 hx
  exact (isNormalIn_pow_iff hb (by omega)).1 (isNormalIn_ofDigits_comp_equiv hbL σ hxL)

/-- The bijection `blockCode : (Fin L → Fin b) ≃ Fin (b ^ L)` encoding `L`-digit blocks as
base-`b ^ L` digits. -/
private def blockCodeEquiv (b L : ℕ) : (Fin L → Fin b) ≃ Fin (b ^ L) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin b))).trans finFunctionFinEquiv

/-- Applying any bijection `f : Equiv.Perm (Fin L → Fin b)` to each aligned `L`-digit block of a
base-`b` normal number yields a base-`b` normal digit sequence. -/
theorem isNormalSeq_blockEquiv (hb : 2 ≤ b) (hL : 1 ≤ L)
    (f : Equiv.Perm (Fin L → Fin b)) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦
      (f (fun j ↦ ⟨digit b x ((n / L) * L + j), digit_lt (by omega) x _⟩)
        ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ) := by
  have hb0 : 0 < b := by omega
  have hbL : 2 ≤ b ^ L := hb.trans (Nat.le_self_pow (by omega) b)
  have hbL0 : 0 < b ^ L := by omega
  let σ : Equiv.Perm (Fin (b ^ L)) :=
    (blockCodeEquiv b L).symm.trans (f.trans (blockCodeEquiv b L))
  let a : ℕ → Fin (b ^ L) := fun m ↦ σ ⟨digit (b ^ L) x m, digit_lt hbL0 x m⟩
  let y : ℝ := ofDigits a
  have hxL : IsNormalIn (b ^ L) x := (isNormalIn_pow_iff hb (by omega)).2 hx
  have ha_norm : IsNormalSeq (b ^ L) fun m ↦ (a m : ℕ) := isNormalSeq_comp_equiv hbL σ hxL
  have hy_norm : IsNormalIn b y := isNormalIn_ofDigits_blockPerm hb hL σ hx
  have hdig : ∀ n, digit b y n =
      (f (fun j ↦ ⟨digit b x ((n / L) * L + j), digit_lt hb0 x _⟩)
        ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ) := by
    intro n
    set m := n / L
    set w : Fin L → Fin b := fun j ↦ ⟨digit b x (m * L + j), digit_lt hb0 x (m * L + j)⟩
    have hxm : digit (b ^ L) x m = blockCode w := by
      have := (forall_digit_eq_iff_digit_pow (x := x) hb0 w 0 m).1 fun j ↦ by simp [w]
      simpa using this
    have hym : digit (b ^ L) y m = blockCode (f w) := by
      rw [digit_ofDigits_of_isNormalSeq hbL ha_norm m]
      have hfin : (⟨digit (b ^ L) x m, digit_lt hbL0 x m⟩ : Fin (b ^ L)) = blockCodeEquiv b L w :=
        Fin.ext hxm
      simp only [a, hfin, σ, Equiv.trans_apply, Equiv.symm_apply_apply]
      rfl
    have hyblk : ∀ j : Fin L, digit b y (m * L + j) = (f w j : ℕ) := by
      have := (forall_digit_eq_iff_digit_pow (x := y) hb0 (f w) 0 m).2 (by simpa using hym)
      simpa using this
    have hn : m * L + n % L = n := by rw [mul_comm]; exact Nat.div_add_mod n L
    simpa [hn] using hyblk ⟨n % L, Nat.mod_lt n (by omega)⟩
  rw [← funext hdig]
  exact isNormalIn_iff_isNormalSeq.1 hy_norm

private theorem periodic_mod_eq {p : ℕ → ℕ} (hp : ∀ n, p (n + L) = p n) (n : ℕ) :
    p n = p (n % L) := by
  have hmul : ∀ q r, p (r + q * L) = p r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, ← add_assoc, hp, ih]
  have hn : n % L + n / L * L = n := by rw [mul_comm (n / L) L]; exact Nat.mod_add_div n L
  conv_lhs => rw [← hn]
  exact hmul (n / L) (n % L)

/-- **Periodic modular shift invariance (digit sequences)**: adding a periodic mask `p` modulo `b`
to the base-`b` digits of a normal number yields a normal digit sequence. -/
theorem isNormalSeq_add_periodic_mod (hb : 2 ≤ b) (hL : 1 ≤ L) {p : ℕ → ℕ}
    (hp : ∀ n, p (n + L) = p n) (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ (digit b x n + p n) % b := by
  have : NeZero b := ⟨by omega⟩
  let f : Equiv.Perm (Fin L → Fin b) :=
    Equiv.piCongrRight fun j ↦ Equiv.addRight (Fin.ofNat b (p j))
  have h := isNormalSeq_blockEquiv hb hL f hx
  have heq : (fun n ↦ (f (fun j ↦ ⟨digit b x ((n / L) * L + j), digit_lt (by omega) x _⟩)
      ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ)) = fun n ↦ (digit b x n + p n) % b := by
    funext n
    have hn : (n / L) * L + n % L = n := by rw [mul_comm]; exact Nat.div_add_mod n L
    simp only [f, Equiv.piCongrRight_apply, Equiv.coe_addRight, Pi.map_apply, Fin.val_add,
      Fin.val_ofNat, hn, Nat.add_mod_mod]
    rw [periodic_mod_eq hp n]
  rwa [heq] at h

/-- **Periodic modular shift invariance**: adding a periodic mask `p` modulo `b` to the base-`b`
digits of a normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_add_periodic_mod (hb : 2 ≤ b) (hL : 1 ≤ L) {p : ℕ → ℕ}
    (hp : ∀ n, p (n + L) = p n) (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦ (⟨(digit b x n + p n) % b, Nat.mod_lt _ (by omega)⟩ : Fin b)) :=
  isNormalIn_ofDigits hb (isNormalSeq_add_periodic_mod hb hL hp hx)

/-- **Block-coordinate permutation invariance (digit sequences)**: permuting the coordinates
within each aligned `L`-digit block of a base-`b` normal number yields a normal digit sequence. -/
theorem isNormalSeq_blockCoordPerm (hb : 2 ≤ b) (hL : 1 ≤ L) (τ : Equiv.Perm (Fin L))
    (hx : IsNormalIn b x) :
    IsNormalSeq b fun n ↦ digit b x ((n / L) * L + (τ ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ)) := by
  let f : Equiv.Perm (Fin L → Fin b) :=
    { toFun := fun w j ↦ w (τ j)
      invFun := fun w j ↦ w (τ.symm j)
      left_inv := fun w ↦ by funext j; simp
      right_inv := fun w ↦ by funext j; simp }
  exact isNormalSeq_blockEquiv hb hL f hx

/-- **Block-coordinate permutation invariance**: permuting the coordinates within each aligned
`L`-digit block of a base-`b` normal number produces a normal real number. -/
theorem isNormalIn_ofDigits_blockCoordPerm (hb : 2 ≤ b) (hL : 1 ≤ L) (τ : Equiv.Perm (Fin L))
    (hx : IsNormalIn b x) :
    IsNormalIn b (ofDigits fun n ↦
      (⟨digit b x ((n / L) * L + (τ ⟨n % L, Nat.mod_lt n (by omega)⟩ : ℕ)),
        digit_lt (by omega) x _⟩ : Fin b)) :=
  isNormalIn_ofDigits hb (isNormalSeq_blockCoordPerm hb hL τ hx)

/-- The digits of the digit-doubled expansion of a base-`b` normal number `x` are indeed
`n ↦ digit b x (n / 2)`. -/
theorem digit_ofDigits_digitDouble (hb : 2 ≤ b) (hx : IsNormalIn b x) (n : ℕ) :
    digit b (ofDigits fun k ↦ (⟨digit b x (k / 2), digit_lt (by omega) x (k / 2)⟩ : Fin b)) n =
      digit b x (n / 2) := by
  refine digit_ofDigits (by omega) _ (fun m ↦ ?_) n
  have hzero : ∃ r, m < r ∧ digit b x r = 0 := by
    by_contra! hcon
    have h0 := hx.isSimplyNormalIn ⟨0, by omega⟩
    have hle : ∀ N, (blockCount b x (fun _ : Fin 1 ↦ (⟨0, by omega⟩ : Fin b)) N : ℝ) ≤ m + 1 :=
      fun N ↦ by
        have hsub : ((Finset.range N).filter fun i ↦
            ∀ j : Fin 1, digit b x (i + j) = ((fun _ ↦ (⟨0, by omega⟩ : Fin b)) j : ℕ)) ⊆
            Finset.range (m + 1) := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range, Fin.forall_fin_one, Fin.val_zero,
            add_zero] at hi
          by_contra him
          exact hcon i (by simp at him; omega) hi.2
        rw [blockCount]
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_range _).le
    have h1 : Tendsto (fun N : ℕ ↦
        (blockCount b x (fun _ : Fin 1 ↦ (⟨0, by omega⟩ : Fin b)) N : ℝ) / N) atTop (𝓝 0) :=
      squeeze_zero (fun N ↦ by positivity) (fun N ↦ div_le_div_of_nonneg_right (hle N)
        (Nat.cast_nonneg N)) (tendsto_const_div_atTop_nhds_zero_nat _)
    have heq := tendsto_nhds_unique h0 h1
    simp only [inv_eq_zero, Nat.cast_eq_zero] at heq
    omega
  obtain ⟨r, hr, hdig0⟩ := hzero
  refine ⟨2 * r, by omega, ?_⟩
  simp only [Nat.mul_div_right r (by omega : 0 < 2), hdig0]
  omega

/-- Repeating each base-`b` digit of a normal number `x` twice preserves simple normality in
base `b`. -/
theorem isSimplyNormalIn_digitDouble (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    IsSimplyNormalIn b (ofDigits fun n ↦
      (⟨digit b x (n / 2), digit_lt (by omega) x (n / 2)⟩ : Fin b)) := by
  classical
  set z : ℝ := ofDigits fun n ↦ (⟨digit b x (n / 2), digit_lt (by omega) x (n / 2)⟩ : Fin b)
  intro c
  have hcard_even : ∀ M,
      ((Finset.range (2 * M)).filter fun i ↦ digit b x (i / 2) = c).card =
        2 * blockCount b x (fun _ : Fin 1 ↦ c) M := by
    intro M
    set A := (Finset.range M).filter fun j ↦ digit b x j = c
    have hA : blockCount b x (fun _ : Fin 1 ↦ c) M = A.card := by
      simp [blockCount, A]
    rw [hA]
    have hunion : ((Finset.range (2 * M)).filter fun i ↦ digit b x (i / 2) = c) =
        A.image (fun j ↦ 2 * j) ∪ A.image (fun j ↦ 2 * j + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image, A]
      constructor
      · rintro ⟨hi, hdig⟩
        rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
        · left
          refine ⟨j, ⟨by omega, ?_⟩, rfl⟩
          simpa using hdig
        · right
          refine ⟨j, ⟨by omega, ?_⟩, rfl⟩
          have : (2 * j + 1) / 2 = j := by omega
          rwa [this] at hdig
      · rintro (⟨j, ⟨hj, hdig⟩, rfl⟩ | ⟨j, ⟨hj, hdig⟩, rfl⟩)
        · exact ⟨by omega, by simpa using hdig⟩
        · have : (2 * j + 1) / 2 = j := by omega
          exact ⟨by omega, by rwa [this]⟩
    have hdisj : Disjoint (A.image fun j ↦ 2 * j) (A.image fun j ↦ 2 * j + 1) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [Finset.mem_image] at hi1 hi2
      obtain ⟨j₁, _, rfl⟩ := hi1
      obtain ⟨j₂, _, h⟩ := hi2
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h ↦ by omega),
      Finset.card_image_of_injective _ (fun _ _ h ↦ by omega), two_mul]
  have hbounds : ∀ N,
      2 * blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) ≤
        blockCount b z (fun _ : Fin 1 ↦ c) N ∧
      blockCount b z (fun _ : Fin 1 ↦ c) N ≤
        2 * blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) + 1 := by
    intro N
    have hbz : blockCount b z (fun _ : Fin 1 ↦ c) N =
        ((Finset.range N).filter fun i ↦ digit b x (i / 2) = c).card := by
      simp [blockCount, z, digit_ofDigits_digitDouble hb hx]
    rw [hbz, ← hcard_even (N / 2)]
    constructor
    · exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2
        (by omega)))
    · have hsub : ((Finset.range N).filter fun i ↦ digit b x (i / 2) = c) ⊆
          ((Finset.range (2 * (N / 2))).filter fun i ↦ digit b x (i / 2) = c) ∪ {2 * (N / 2)} := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
          Finset.mem_singleton] at hi ⊢
        by_cases hlt : i < 2 * (N / 2)
        · exact Or.inl ⟨hlt, hi.2⟩
        · exact Or.inr (by omega)
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by simp))
  have hratio : Tendsto (fun N : ℕ ↦ 2 * ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have h := (tendsto_div_natCast_div (k := 2) (by omega) 0).const_mul 2
    simp only [add_zero, Nat.cast_ofNat, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
    exact h.congr fun N ↦ by rw [mul_div_assoc]
  have hmain : Tendsto (fun N : ℕ ↦
      (2 * (blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) : ℝ)) / N) atTop (𝓝 (b : ℝ)⁻¹) := by
    have h1 := (hx.isSimplyNormalIn c).comp (Nat.tendsto_div_const_atTop (by omega : 2 ≠ 0))
    have h2 := h1.mul hratio
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hdiv : ((N / 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 0 < N / 2 by omega).ne'
    simp only [Function.comp_apply]
    field_simp
  have hup : Tendsto (fun N : ℕ ↦
      (2 * (blockCount b x (fun _ : Fin 1 ↦ c) (N / 2) : ℝ) + 1) / N) atTop (𝓝 (b : ℝ)⁻¹) := by
    have h := hmain.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    rw [add_zero] at h
    exact h.congr fun N ↦ (add_div _ _ _).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hup ?_ ?_ <;>
    refine Eventually.of_forall fun N ↦ div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  · exact_mod_cast (hbounds N).1
  · exact_mod_cast (hbounds N).2

/-- Repeating each base-`b` digit of a normal number `x` twice destroys normality in base `b`:
the length-`2` block `(0, 1)` cannot occur at even positions, so its asymptotic frequency is
`1 / (2 b ^ 2)` instead of `1 / b ^ 2`. -/
theorem not_isNormalIn_digitDouble (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    ¬ IsNormalIn b (ofDigits fun n ↦
      (⟨digit b x (n / 2), digit_lt (by omega) x (n / 2)⟩ : Fin b)) := by
  classical
  set z : ℝ := ofDigits fun n ↦ (⟨digit b x (n / 2), digit_lt (by omega) x (n / 2)⟩ : Fin b)
  intro hz
  let w : Fin 2 → Fin b := ![⟨0, by omega⟩, ⟨1, by omega⟩]
  have hbij : ∀ M, blockCount b z w (2 * M) = blockCount b x w M := by
    intro M
    simp only [blockCount]
    refine Finset.card_nbij' (fun i ↦ i / 2) (fun j ↦ 2 * j + 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      obtain ⟨hiM, hblk⟩ := hi
      have h0 := hblk 0
      have h1 := hblk 1
      simp only [Fin.val_zero, add_zero, Fin.val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        z, digit_ofDigits_digitDouble hb hx, w] at h0 h1
      have hodd : i % 2 = 1 := by
        by_contra hne
        have heven : i % 2 = 0 := by omega
        have heq : (i + 1) / 2 = i / 2 := by omega
        rw [heq, h0] at h1
        omega
      refine ⟨by omega, fun j ↦ ?_⟩
      fin_cases j
      · simpa [w] using h0
      · have hsucc : (i + 1) / 2 = i / 2 + 1 := by omega
        simpa [w, hsucc] using h1
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj ⊢
      obtain ⟨hjM, hblk⟩ := hj
      refine ⟨by omega, fun r ↦ ?_⟩
      fin_cases r
      · have h0 := hblk 0
        have hdiv : (2 * j + 1) / 2 = j := by omega
        simpa [z, digit_ofDigits_digitDouble hb hx, hdiv] using h0
      · have h1 := hblk 1
        have hdiv : (2 * j + 1 + 1) / 2 = j + 1 := by omega
        simpa [z, digit_ofDigits_digitDouble hb hx, hdiv] using h1
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
      have h0 := hi.2 0
      have h1 := hi.2 1
      simp only [Fin.val_zero, add_zero, Fin.val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        z, digit_ofDigits_digitDouble hb hx, w] at h0 h1
      have hodd : i % 2 = 1 := by
        by_contra hne
        have : (i + 1) / 2 = i / 2 := by omega
        rw [this, h0] at h1
        omega
      dsimp only
      omega
    · intro j _
      dsimp only
      omega
  have hz2 : Tendsto (fun M : ℕ ↦ (blockCount b z w (2 * M) : ℝ) / ((2 * M : ℕ) : ℝ))
      atTop (𝓝 ((b : ℝ) ^ 2)⁻¹) :=
    (hz 2 w).comp (tendsto_id.const_mul_atTop' (by omega : 0 < 2))
  have hx2 : Tendsto (fun M : ℕ ↦ (blockCount b z w (2 * M) : ℝ) / ((2 * M : ℕ) : ℝ))
      atTop (𝓝 (((b : ℝ) ^ 2)⁻¹ / 2)) := by
    have h := (hx 2 w).div_const 2
    refine h.congr fun M ↦ ?_
    rw [hbij M, Nat.cast_mul, Nat.cast_ofNat, div_div, mul_comm (M : ℝ) 2]
  have heq := tendsto_nhds_unique hz2 hx2
  have hpos : (0 : ℝ) < ((b : ℝ) ^ 2)⁻¹ := by positivity
  linarith

/-- For every base `b ≥ 2`, there exists a real number that is simply normal in base `b`
but not normal in base `b`. -/
theorem exists_isSimplyNormalIn_not_isNormalIn (hb : 2 ≤ b) :
    ∃ z : ℝ, IsSimplyNormalIn b z ∧ ¬ IsNormalIn b z := by
  obtain ⟨x, hx⟩ := exists_isAbsolutelyNormal
  exact ⟨_, isSimplyNormalIn_digitDouble hb (hx b hb), not_isNormalIn_digitDouble hb (hx b hb)⟩

end Real
