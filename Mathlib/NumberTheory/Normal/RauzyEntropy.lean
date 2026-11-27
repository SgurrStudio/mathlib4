/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Subadditive
public import Mathlib.NumberTheory.Normal.AdditivePreservers
public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Rational

/-!
# Rauzy empirical block entropy, Fekete's lemma, and additive normality preservers

Following Rauzy (1976) and Manai (arXiv:2609.24665, §3.1), we define the empirical base-`b` block
frequency, block entropy, upper/lower block entropy, and Rauzy entropy of a real number `x`, and
establish:

1. **Basic bounds**: `0 ≤ blockEntropy b x k N ≤ k`, `0 ≤ lowerBlockEntropy b x k ≤
   upperBlockEntropy b x k ≤ k`, and `0 ≤ rauzyEntropy b x ≤ 1`.
2. **Subadditivity and Manai Proposition 3.2 (Fekete's lemma)**:
   `upperBlockEntropy b x (k + l) ≤ upperBlockEntropy b x k + upperBlockEntropy b x l` and
   `upperBlockEntropy b x k / k → rauzyEntropy b x` as `k → ∞`.
3. **Entropic characterization of normal numbers**:
   `IsNormalIn b x ↔ ∀ k ≥ 1, blockEntropy b x k N → k`
   `↔ ∀ k ≥ 1, lowerBlockEntropy b x k = k`, and `IsNormalIn b x → rauzyEntropy b x = 1`.
4. **Zero Rauzy entropy for deterministic examples**:
   rationals (`rauzyEntropy b (q : ℝ) = 0`), numbers with zero-density nonzero digit support,
   sparse base-`b` series, and Mathlib's `liouvilleNumber (b : ℝ)`.
5. **Algebraic & base-power laws for additive preservers**:
   `normalAddPreservers` invariance under base powers, non-normality of additive preservers, and
   rational scaling closure of `absolutelyNormalAddPreservers`.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-! ### Section 1: Definitions -/

/-- The empirical frequency of the base-`b` block `w : Fin k → Fin b` among the first `N`
positions of `x`. -/
noncomputable def blockFreq (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) : ℝ :=
  (blockCount b x w N : ℝ) / (N : ℝ)

/-- The base-`b` empirical block entropy of `x` at block length `k` and prefix length `N`. -/
noncomputable def blockEntropy (b : ℕ) (x : ℝ) (k N : ℕ) : ℝ :=
  (∑ w : Fin k → Fin b, Real.negMulLog (blockFreq b x w N)) / Real.log b

/-- The upper asymptotic base-`b` block entropy of `x` at block length `k`. -/
noncomputable def upperBlockEntropy (b : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  Filter.limsup (fun N ↦ blockEntropy b x k N) Filter.atTop

/-- The lower asymptotic base-`b` block entropy of `x` at block length `k`. -/
noncomputable def lowerBlockEntropy (b : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  Filter.liminf (fun N ↦ blockEntropy b x k N) Filter.atTop

/-- The Rauzy entropy of `x` in base `b`, defined as `inf_{k ≥ 1} upperBlockEntropy b x k / k`. -/
noncomputable def rauzyEntropy (b : ℕ) (x : ℝ) : ℝ :=
  sInf ((fun k : ℕ ↦ upperBlockEntropy b x k / (k : ℝ)) '' Set.Ici 1)

theorem rauzyEntropy_eq_sInf_range_pnat (b : ℕ) (x : ℝ) :
    rauzyEntropy b x = sInf (Set.range fun k : ℕ+ ↦ upperBlockEntropy b x k / (k : ℝ)) := by
  unfold rauzyEntropy
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_Ici, Set.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.property, rfl⟩

/-! ### Finite Shannon entropy inequalities (Gibbs and subadditivity) -/

/-- **Gibbs' inequality**: the Shannon entropy of any probability distribution on a finite type `ι`
is at most `log (Fintype.card ι)`. -/
theorem sum_negMulLog_le_log_card {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (Fintype.card ι) := by
  have hcard_pos : 0 < Fintype.card ι := by
    by_contra h0
    have hzero : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos h0
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hzero
    simp at hsum
  set M : ℝ := (Fintype.card ι : ℝ)
  have hM : 0 < M := Nat.cast_pos.2 hcard_pos
  have hterm : ∀ i : ι, M * Real.negMulLog (p i) - M * Real.log M * p i ≤ 1 - M * p i := by
    intro i
    have h := Real.negMulLog_le_one_sub_self (mul_nonneg hM.le (hp i))
    rw [Real.negMulLog_mul] at h
    simp only [Real.negMulLog] at h ⊢
    linarith
  have hsum_le := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hterm i
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hsum] at hsum_le
  nlinarith

/-- **Strict Gibbs' inequality**: if a probability distribution `p` on a finite type `ι` is not
uniform, then its Shannon entropy is strictly less than `log (Fintype.card ι)`. -/
theorem sum_negMulLog_lt_log_card {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {i₀ : ι} (hi₀ : p i₀ ≠ (Fintype.card ι : ℝ)⁻¹) :
    ∑ i, Real.negMulLog (p i) < Real.log (Fintype.card ι) := by
  have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
  set M : ℝ := (Fintype.card ι : ℝ)
  have hM : 0 < M := Nat.cast_pos.2 hcard_pos
  have hterm : ∀ i : ι, M * Real.negMulLog (p i) - M * Real.log M * p i ≤ 1 - M * p i := by
    intro i
    have h := Real.negMulLog_le_one_sub_self (mul_nonneg hM.le (hp i))
    rw [Real.negMulLog_mul] at h
    simp only [Real.negMulLog] at h ⊢
    linarith
  have hstrict : M * Real.negMulLog (p i₀) - M * Real.log M * p i₀ < 1 - M * p i₀ := by
    have hne1 : M * p i₀ ≠ 1 := by
      intro heq
      apply hi₀
      have hM0 : M ≠ 0 := hM.ne'
      calc p i₀ = M⁻¹ * (M * p i₀) := by field_simp [hM0]
        _ = M⁻¹ * 1 := by rw [heq]
        _ = M⁻¹ := mul_one _
    have h := Real.negMulLog_lt_one_sub_self (mul_nonneg hM.le (hp i₀)) hne1
    rw [Real.negMulLog_mul] at h
    simp only [Real.negMulLog] at h ⊢
    linarith
  have hsum_lt :
      ∑ i : ι, (M * Real.negMulLog (p i) - M * Real.log M * p i) < ∑ i : ι, (1 - M * p i) :=
    Finset.sum_lt_sum (fun i _ ↦ hterm i) ⟨i₀, Finset.mem_univ i₀, hstrict⟩
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hsum] at hsum_lt
  nlinarith

/-- Gibbs' inequality restricted to a `Finset`. -/
theorem sum_negMulLog_finset_le_log_card {ι : Type*} {s : Finset ι} {p : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤ Real.log s.card := by
  have h := sum_negMulLog_le_log_card (ι := ↥s) (p := fun i ↦ p i.val)
    (fun i ↦ hp i.val i.property) (by rwa [Finset.sum_coe_sort])
  rw [Finset.sum_coe_sort s (fun i ↦ Real.negMulLog (p i)), Fintype.card_coe] at h
  exact h

private lemma negMulLog_add_mul_log_add_mul_log_le {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c) :
    Real.negMulLog a + a * Real.log b + a * Real.log c ≤ b * c - a := by
  rcases ha.eq_or_lt with rfl | hapos
  · simp [mul_nonneg hab hac]
  · have hb : 0 < b := hapos.trans_le hab
    have hc : 0 < c := hapos.trans_le hac
    have hbc : 0 < b * c := mul_pos hb hc
    have h := Real.negMulLog_le_one_sub_self (div_nonneg hapos.le hbc.le)
    have hmul := mul_le_mul_of_nonneg_right h hbc.le
    have hlog : Real.log (a / (b * c)) = Real.log a - (Real.log b + Real.log c) := by
      rw [Real.log_div hapos.ne' hbc.ne', Real.log_mul hb.ne' hc.ne']
    have hbc0 : b * c ≠ 0 := hbc.ne'
    have hlhs : Real.negMulLog (a / (b * c)) * (b * c) =
        Real.negMulLog a + a * Real.log b + a * Real.log c := by
      simp only [Real.negMulLog, hlog]
      field_simp [hbc0]
      ring
    have hrhs : (1 - a / (b * c)) * (b * c) = b * c - a := by
      field_simp [hbc0]
    linarith

/-- **Subadditivity of finite Shannon entropy**: for any joint probability distribution `p` on
`α × β`, the joint entropy is at most the sum of its two marginal entropies. -/
theorem sum_negMulLog_prod_le {α β : Type*} [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (hsum : ∑ ab, p ab = 1) :
    ∑ ab : α × β, Real.negMulLog (p ab) ≤
      (∑ a : α, Real.negMulLog (∑ b : β, p (a, b))) +
      (∑ b : β, Real.negMulLog (∑ a : α, p (a, b))) := by
  set pA : α → ℝ := fun a ↦ ∑ b : β, p (a, b)
  set pB : β → ℝ := fun b ↦ ∑ a : α, p (a, b)
  have hterm : ∀ ab : α × β,
      Real.negMulLog (p ab) + p ab * Real.log (pA ab.1) + p ab * Real.log (pB ab.2) ≤
        pA ab.1 * pB ab.2 - p ab := fun ⟨a, b⟩ ↦
    negMulLog_add_mul_log_add_mul_log_le (hp (a, b))
      (Finset.single_le_sum (fun b' _ ↦ hp (a, b')) (Finset.mem_univ b))
      (Finset.single_le_sum (fun a' _ ↦ hp (a', b)) (Finset.mem_univ a))
  have hsum_le := Finset.sum_le_sum fun ab (_ : ab ∈ Finset.univ) ↦ hterm ab
  have h1 : ∑ ab : α × β, p ab * Real.log (pA ab.1) = -∑ a : α, Real.negMulLog (pA a) := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.sum_mul, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  have h2 : ∑ ab : α × β, p ab * Real.log (pB ab.2) = -∑ b : β, Real.negMulLog (pB b) := by
    rw [Fintype.sum_prod_type_right]
    simp only [← Finset.sum_mul, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  have hA1 : ∑ a : α, pA a = 1 := by
    dsimp only [pA]
    rw [← Fintype.sum_prod_type, hsum]
  have hB1 : ∑ b : β, pB b = 1 := by
    dsimp only [pB]
    rw [← Fintype.sum_prod_type_right, hsum]
  have h3 : ∑ ab : α × β, pA ab.1 * pB ab.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hB1, mul_one, hA1]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, hsum] at hsum_le
  linarith

/-! ### Section 2: Basic properties and bounds -/

theorem blockFreq_nonneg (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    0 ≤ blockFreq b x w N := by
  unfold blockFreq
  positivity

theorem blockFreq_le_one (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockFreq b x w N ≤ 1 := by
  unfold blockFreq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    exact_mod_cast blockCount_le b x w N

theorem sum_blockFreq (hb : 0 < b) (x : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    ∑ w : Fin k → Fin b, blockFreq b x w N = 1 := by
  have : NeZero b := ⟨hb.ne'⟩
  simp only [blockFreq, ← Finset.sum_div, ← Nat.cast_sum, sum_blockCount]
  exact div_self (Nat.cast_ne_zero.2 hN.ne')

theorem blockEntropy_zero_right (b : ℕ) (x : ℝ) (k : ℕ) :
    blockEntropy b x k 0 = 0 := by
  simp [blockEntropy, blockFreq]

theorem blockEntropy_zero_left (b : ℕ) (x : ℝ) (N : ℕ) :
    blockEntropy b x 0 N = 0 := by
  unfold blockEntropy
  have hterm : ∀ w : Fin 0 → Fin b, Real.negMulLog (blockFreq b x w N) = 0 := fun w ↦ by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [blockFreq]
    · have hc : blockCount b x w N = N := by
        simp [blockCount]
      simp [blockFreq, hc, hN.ne']
  simp [hterm]

theorem blockEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) (k N : ℕ) :
    0 ≤ blockEntropy b x k N := by
  have hlog : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  unfold blockEntropy
  refine div_nonneg (Finset.sum_nonneg fun w _ ↦ ?_) hlog.le
  exact Real.negMulLog_nonneg (blockFreq_nonneg b x w N) (blockFreq_le_one b x w N)

theorem blockEntropy_le (hb : 2 ≤ b) (x : ℝ) (k N : ℕ) :
    blockEntropy b x k N ≤ k := by
  have hb0 : 0 < b := by omega
  have hlog : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [blockEntropy_zero_right]
    exact Nat.cast_nonneg k
  · unfold blockEntropy
    rw [div_le_iff₀ hlog]
    calc ∑ w : Fin k → Fin b, Real.negMulLog (blockFreq b x w N)
        ≤ Real.log (Fintype.card (Fin k → Fin b)) :=
          sum_negMulLog_le_log_card (fun w ↦ blockFreq_nonneg b x w N) (sum_blockFreq hb0 x k hN)
      _ = Real.log ((b : ℝ) ^ k) := by
          simp
      _ = (k : ℝ) * Real.log b := Real.log_pow (b : ℝ) k

private lemma isBoundedUnder_le_blockEntropy (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (fun N ↦ blockEntropy b x k N) :=
  ⟨k, eventually_map.2 (Eventually.of_forall fun N ↦ blockEntropy_le hb x k N)⟩

private lemma isCoboundedUnder_le_blockEntropy (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (fun N ↦ blockEntropy b x k N) :=
  isCoboundedUnder_le_of_le atTop (fun N ↦ blockEntropy_nonneg hb x k N)

private lemma isBoundedUnder_ge_blockEntropy (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (fun N ↦ blockEntropy b x k N) :=
  ⟨0, eventually_map.2 (Eventually.of_forall fun N ↦ blockEntropy_nonneg hb x k N)⟩

private lemma isCoboundedUnder_ge_blockEntropy (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    IsCoboundedUnder (· ≥ ·) atTop (fun N ↦ blockEntropy b x k N) :=
  isCoboundedUnder_ge_of_le atTop (fun N ↦ blockEntropy_le hb x k N)

theorem upperBlockEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    0 ≤ upperBlockEntropy b x k :=
  le_limsup_of_le (isBoundedUnder_le_blockEntropy hb x k) fun _ hc ↦
    let ⟨N, hN⟩ := hc.exists
    (blockEntropy_nonneg hb x k N).trans hN

theorem upperBlockEntropy_le (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    upperBlockEntropy b x k ≤ k :=
  limsup_le_of_le (isCoboundedUnder_le_blockEntropy hb x k)
    (Eventually.of_forall fun N ↦ blockEntropy_le hb x k N)

theorem lowerBlockEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    0 ≤ lowerBlockEntropy b x k :=
  le_liminf_of_le (isCoboundedUnder_ge_blockEntropy hb x k)
    (Eventually.of_forall fun N ↦ blockEntropy_nonneg hb x k N)

theorem lowerBlockEntropy_le_upperBlockEntropy (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    lowerBlockEntropy b x k ≤ upperBlockEntropy b x k :=
  liminf_le_limsup (isBoundedUnder_le_blockEntropy hb x k) (isBoundedUnder_ge_blockEntropy hb x k)

theorem lowerBlockEntropy_le (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    lowerBlockEntropy b x k ≤ k :=
  (lowerBlockEntropy_le_upperBlockEntropy hb x k).trans (upperBlockEntropy_le hb x k)

theorem upperBlockEntropy_zero (b : ℕ) (x : ℝ) : upperBlockEntropy b x 0 = 0 := by
  simp only [upperBlockEntropy, blockEntropy_zero_left]
  exact limsup_const 0

theorem rauzyEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) : 0 ≤ rauzyEntropy b x := by
  unfold rauzyEntropy
  refine le_csInf ⟨upperBlockEntropy b x 1 / (1 : ℕ), 1, Set.mem_Ici.2 le_rfl, rfl⟩ ?_
  rintro _ ⟨k, -, rfl⟩
  exact div_nonneg (upperBlockEntropy_nonneg hb x k) (Nat.cast_nonneg k)

theorem rauzyEntropy_le_div (hb : 2 ≤ b) (x : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    rauzyEntropy b x ≤ upperBlockEntropy b x k / (k : ℝ) := by
  unfold rauzyEntropy
  refine csInf_le ⟨0, ?_⟩ ⟨k, hk, rfl⟩
  rintro _ ⟨m, -, rfl⟩
  exact div_nonneg (upperBlockEntropy_nonneg hb x m) (Nat.cast_nonneg m)

theorem rauzyEntropy_le_one (hb : 2 ≤ b) (x : ℝ) : rauzyEntropy b x ≤ 1 := by
  calc rauzyEntropy b x ≤ upperBlockEntropy b x 1 / (1 : ℕ) := rauzyEntropy_le_div hb x le_rfl
    _ = upperBlockEntropy b x 1 := by simp
    _ ≤ 1 := by simpa using upperBlockEntropy_le hb x 1

/-! ### Section 3: Subadditivity & Manai Proposition 3.2 (Fekete's lemma) -/

private lemma limsup_add_le_of_bounds {f g : ℕ → ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (hf : ∀ N, a₁ ≤ f N ∧ f N ≤ b₁) (hg : ∀ N, a₂ ≤ g N ∧ g N ≤ b₂) :
    limsup (fun N ↦ f N + g N) atTop ≤ limsup f atTop + limsup g atTop := by
  have hfg_lo : IsCoboundedUnder (· ≤ ·) atTop (fun N ↦ f N + g N) :=
    isCoboundedUnder_le_of_le atTop fun N ↦ add_le_add (hf N).1 (hg N).1
  have hf_up : IsBoundedUnder (· ≤ ·) atTop f :=
    ⟨b₁, eventually_map.2 (Eventually.of_forall fun N ↦ (hf N).2)⟩
  have hg_up : IsBoundedUnder (· ≤ ·) atTop g :=
    ⟨b₂, eventually_map.2 (Eventually.of_forall fun N ↦ (hg N).2)⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have h1 : ∀ᶠ N in atTop, f N < limsup f atTop + ε / 2 :=
    eventually_lt_of_limsup_lt (lt_add_of_pos_right _ (half_pos hε)) hf_up
  have h2 : ∀ᶠ N in atTop, g N < limsup g atTop + ε / 2 :=
    eventually_lt_of_limsup_lt (lt_add_of_pos_right _ (half_pos hε)) hg_up
  refine limsup_le_of_le hfg_lo ?_
  filter_upwards [h1, h2] with N hN1 hN2
  linarith

private lemma limsup_eq_of_tendsto_sub_zero {f g : ℕ → ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (hf : ∀ N, a₁ ≤ f N ∧ f N ≤ b₁) (hg : ∀ N, a₂ ≤ g N ∧ g N ≤ b₂)
    (hdiff : Tendsto (fun N ↦ g N - f N) atTop (𝓝 0)) :
    limsup g atTop = limsup f atTop := by
  have hfg_lo : IsCoboundedUnder (· ≤ ·) atTop g :=
    isCoboundedUnder_le_of_le atTop fun N ↦ (hg N).1
  have hff_lo : IsCoboundedUnder (· ≤ ·) atTop f :=
    isCoboundedUnder_le_of_le atTop fun N ↦ (hf N).1
  have hf_up : IsBoundedUnder (· ≤ ·) atTop f :=
    ⟨b₁, eventually_map.2 (Eventually.of_forall fun N ↦ (hf N).2)⟩
  have hg_up : IsBoundedUnder (· ≤ ·) atTop g :=
    ⟨b₂, eventually_map.2 (Eventually.of_forall fun N ↦ (hg N).2)⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have h1 := eventually_lt_of_limsup_lt (lt_add_of_pos_right _ (half_pos hε)) hf_up
    have h2 := hdiff.eventually (gt_mem_nhds (half_pos hε))
    refine limsup_le_of_le hfg_lo ?_
    filter_upwards [h1, h2] with N hN1 hN2
    linarith
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have h1 := eventually_lt_of_limsup_lt (lt_add_of_pos_right _ (half_pos hε)) hg_up
    have h2 := hdiff.eventually (lt_mem_nhds (neg_lt_zero.2 (half_pos hε)))
    refine limsup_le_of_le hff_lo ?_
    filter_upwards [h1, h2] with N hN1 hN2
    linarith

/-- Equivalence between pairs of blocks `(u, v)` of lengths `k, l` and blocks of length `k + l`. -/
private def blockProdEquiv (b k l : ℕ) :
    (Fin k → Fin b) × (Fin l → Fin b) ≃ (Fin (k + l) → Fin b) where
  toFun uv := Fin.append uv.1 uv.2
  invFun w := (fun j ↦ w (Fin.castAdd l j), fun j ↦ w (Fin.natAdd k j))
  left_inv := fun ⟨u, v⟩ ↦
    Prod.ext (funext fun j ↦ Fin.append_left u v j) (funext fun j ↦ Fin.append_right u v j)
  right_inv _ := funext fun j ↦
    Fin.addCases (fun i ↦ Fin.append_left _ _ i) (fun i ↦ Fin.append_right _ _ i) j

private lemma blockCount_append_iff (b : ℕ) (x : ℝ) {k l : ℕ}
    (u : Fin k → Fin b) (v : Fin l → Fin b) (i : ℕ) :
    (∀ j : Fin (k + l), digit b x (i + j) = ((Fin.append u v j : Fin b) : ℕ)) ↔
      (∀ j : Fin k, digit b x (i + j) = (u j : ℕ)) ∧
        (∀ j : Fin l, digit b (x * (b : ℝ) ^ k) (i + j) = (v j : ℕ)) := by
  constructor
  · intro h
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · have hj := h (Fin.castAdd l j)
      simpa [Fin.append_left] using hj
    · have hj := h (Fin.natAdd k j)
      simp only [Fin.val_natAdd, Fin.append_right] at hj
      rw [← digit_add, show k + (i + (j : ℕ)) = i + (k + (j : ℕ)) by omega]
      exact hj
  · rintro ⟨hu, hv⟩ j
    refine Fin.addCases (fun j₁ ↦ ?_) (fun j₂ ↦ ?_) j
    · simpa [Fin.append_left] using hu j₁
    · simp only [Fin.val_natAdd, Fin.append_right]
      rw [show i + (k + (j₂ : ℕ)) = k + (i + (j₂ : ℕ)) by omega, digit_add]
      exact hv j₂

private lemma sum_blockCount_append_snd (hb : 0 < b) (x : ℝ) {k l : ℕ}
    (u : Fin k → Fin b) (N : ℕ) :
    ∑ v : Fin l → Fin b, blockCount b x (Fin.append u v) N = blockCount b x u N := by
  classical
  let f : ℕ → Fin l → Fin b := fun i j ↦
    ⟨digit b (x * (b : ℝ) ^ k) (i + j), digit_lt hb _ _⟩
  let S := (Finset.range N).filter fun i ↦ ∀ j : Fin k, digit b x (i + j) = u j
  have hfib := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)
  change ∑ v : Fin l → Fin b, blockCount b x (Fin.append u v) N = S.card
  rw [hfib]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  unfold blockCount
  congr 1
  ext i
  simp only [S, Finset.mem_filter, Finset.mem_range, f, blockCount_append_iff]
  constructor
  · rintro ⟨hiN, hu, hv⟩
    exact ⟨⟨hiN, hu⟩, funext fun j ↦ Fin.ext (hv j)⟩
  · rintro ⟨⟨hiN, hu⟩, hfv⟩
    exact ⟨hiN, hu, fun j ↦ congrArg (fun w : Fin l → Fin b ↦ (w j : ℕ)) hfv⟩

private lemma sum_blockCount_append_fst (hb : 0 < b) (x : ℝ) {k l : ℕ}
    (v : Fin l → Fin b) (N : ℕ) :
    ∑ u : Fin k → Fin b, blockCount b x (Fin.append u v) N =
      blockCount b (x * (b : ℝ) ^ k) v N := by
  classical
  let f : ℕ → Fin k → Fin b := fun i j ↦ ⟨digit b x (i + j), digit_lt hb _ _⟩
  let S := (Finset.range N).filter fun i ↦
    ∀ j : Fin l, digit b (x * (b : ℝ) ^ k) (i + j) = v j
  have hfib := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)
  change ∑ u : Fin k → Fin b, blockCount b x (Fin.append u v) N = S.card
  rw [hfib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  unfold blockCount
  congr 1
  ext i
  simp only [S, Finset.mem_filter, Finset.mem_range, f, blockCount_append_iff]
  constructor
  · rintro ⟨hiN, hu, hv⟩
    exact ⟨⟨hiN, hv⟩, funext fun j ↦ Fin.ext (hu j)⟩
  · rintro ⟨⟨hiN, hv⟩, hfu⟩
    exact ⟨hiN, fun j ↦ congrArg (fun w : Fin k → Fin b ↦ (w j : ℕ)) hfu, hv⟩

private lemma abs_blockFreq_mul_pow_sub_le (b : ℕ) (x : ℝ) {l : ℕ}
    (v : Fin l → Fin b) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    |blockFreq b (x * (b : ℝ) ^ k) v N - blockFreq b x v N| ≤ (k : ℝ) / (N : ℝ) := by
  have hadd := blockCount_add (b := b) (x := x) v N k
  have hle1 : blockCount b x v N ≤ blockCount b x v (N + k) := by
    classical
    unfold blockCount
    exact Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_add_right N k)))
  have hle2 : blockCount b x v (N + k) ≤ blockCount b x v N + k := by
    classical
    have hsub : ((Finset.range (N + k)).filter fun i ↦ ∀ j : Fin l, digit b x (i + j) = v j) ⊆
        ((Finset.range N).filter fun i ↦ ∀ j : Fin l, digit b x (i + j) = v j) ∪
          Finset.Ico N (N + k) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      by_cases hiN : i < N
      · exact Or.inl ⟨hiN, hi.2⟩
      · exact Or.inr ⟨by omega, hi.1⟩
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
    exact hcard
  have hk_le : blockCount b x v k ≤ k := blockCount_le b x v k
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (blockCount b x v (N + k) : ℝ) =
      (blockCount b x v k : ℝ) + (blockCount b (x * (b : ℝ) ^ k) v N : ℝ) := by
    exact_mod_cast hadd
  have h2 : (blockCount b x v N : ℝ) ≤ (blockCount b x v (N + k) : ℝ) := by exact_mod_cast hle1
  have h3 : (blockCount b x v (N + k) : ℝ) ≤ (blockCount b x v N : ℝ) + k := by exact_mod_cast hle2
  have h4 : (blockCount b x v k : ℝ) ≤ k := by exact_mod_cast hk_le
  have h5 : (0 : ℝ) ≤ (blockCount b x v k : ℝ) := Nat.cast_nonneg _
  have habs : |(blockCount b (x * (b : ℝ) ^ k) v N : ℝ) - (blockCount b x v N : ℝ)| ≤ k :=
    abs_le.2 ⟨by linarith, by linarith⟩
  unfold blockFreq
  rw [← sub_div, abs_div, abs_of_pos hNpos]
  exact div_le_div_of_nonneg_right habs hNpos.le

theorem tendsto_blockEntropy_mul_pow_sub (_hb : 2 ≤ b) (x : ℝ) (k l : ℕ) :
    Tendsto (fun N ↦ blockEntropy b (x * (b : ℝ) ^ k) l N - blockEntropy b x l N)
      atTop (𝓝 0) := by
  have huc : UniformContinuousOn Real.negMulLog (Set.Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_negMulLog.continuousOn
  have hterm : ∀ v : Fin l → Fin b,
      Tendsto (fun N ↦ Real.negMulLog (blockFreq b (x * (b : ℝ) ^ k) v N) -
        Real.negMulLog (blockFreq b x v N)) atTop (𝓝 0) := fun v ↦ by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδspec⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((k : ℝ) / δ)
    refine ⟨max N₀ 1, fun N hN ↦ ?_⟩
    have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hdist : dist (blockFreq b (x * (b : ℝ) ^ k) v N) (blockFreq b x v N) < δ := by
      rw [Real.dist_eq]
      refine lt_of_le_of_lt (abs_blockFreq_mul_pow_sub_le b x v k hN1) ?_
      rw [div_lt_iff₀ hNpos]
      have hgt : (k : ℝ) / δ < N :=
        lt_of_lt_of_le hN₀ (by exact_mod_cast le_trans (le_max_left _ _) hN)
      have := (div_lt_iff₀ hδ).1 hgt
      linarith
    have hspec := hδspec _ ⟨blockFreq_nonneg _ _ _ _, blockFreq_le_one _ _ _ _⟩
      _ ⟨blockFreq_nonneg _ _ _ _, blockFreq_le_one _ _ _ _⟩ hdist
    simpa [Real.dist_eq] using hspec
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin l → Fin b)) fun v _ ↦ hterm v
  simp only [Finset.sum_const_zero] at hsum
  have hdiv := hsum.div_const (Real.log b)
  rw [zero_div] at hdiv
  refine hdiv.congr fun N ↦ ?_
  unfold blockEntropy
  rw [Finset.sum_sub_distrib, sub_div]

theorem upperBlockEntropy_mul_pow (hb : 2 ≤ b) (x : ℝ) (k l : ℕ) :
    upperBlockEntropy b (x * (b : ℝ) ^ k) l = upperBlockEntropy b x l :=
  limsup_eq_of_tendsto_sub_zero
    (fun N ↦ ⟨blockEntropy_nonneg hb x l N, blockEntropy_le hb x l N⟩)
    (fun N ↦ ⟨blockEntropy_nonneg hb (x * (b : ℝ) ^ k) l N,
      blockEntropy_le hb (x * (b : ℝ) ^ k) l N⟩)
    (tendsto_blockEntropy_mul_pow_sub hb x k l)

theorem blockEntropy_add_le (hb : 2 ≤ b) (x : ℝ) (k l N : ℕ) :
    blockEntropy b x (k + l) N ≤
      blockEntropy b x k N + blockEntropy b (x * (b : ℝ) ^ k) l N := by
  have hb0 : 0 < b := by omega
  have hlog : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [blockEntropy_zero_right]
  · set p : (Fin k → Fin b) × (Fin l → Fin b) → ℝ :=
      fun uv ↦ blockFreq b x (blockProdEquiv b k l uv) N
    have hp : ∀ uv, 0 ≤ p uv := fun uv ↦ blockFreq_nonneg b x _ N
    have hsum : ∑ uv, p uv = 1 := by
      dsimp only [p]
      rw [Fintype.sum_equiv (blockProdEquiv b k l) _ (fun w ↦ blockFreq b x w N) (fun _ ↦ rfl)]
      exact sum_blockFreq hb0 x (k + l) hN
    have hsub := sum_negMulLog_prod_le hp hsum
    have hlhs : ∑ uv, Real.negMulLog (p uv) =
        ∑ w : Fin (k + l) → Fin b, Real.negMulLog (blockFreq b x w N) :=
      Fintype.sum_equiv (blockProdEquiv b k l) _ _ (fun _ ↦ rfl)
    have hmarg1 : ∀ u : Fin k → Fin b, ∑ v : Fin l → Fin b, p (u, v) = blockFreq b x u N := by
      intro u
      simp only [p, blockProdEquiv, Equiv.coe_fn_mk, blockFreq, ← Finset.sum_div, ← Nat.cast_sum,
        sum_blockCount_append_snd hb0 x u N]
    have hmarg2 : ∀ v : Fin l → Fin b,
        ∑ u : Fin k → Fin b, p (u, v) = blockFreq b (x * (b : ℝ) ^ k) v N := by
      intro v
      simp only [p, blockProdEquiv, Equiv.coe_fn_mk, blockFreq, ← Finset.sum_div, ← Nat.cast_sum,
        sum_blockCount_append_fst hb0 x v N]
    rw [hlhs] at hsub
    simp_rw [hmarg1, hmarg2] at hsub
    unfold blockEntropy
    rw [← add_div]
    exact div_le_div_of_nonneg_right hsub hlog.le

/-- Subadditivity of the upper block entropy: `H⁺(k + l) ≤ H⁺(k) + H⁺(l)`. -/
theorem upperBlockEntropy_add_le (hb : 2 ≤ b) (x : ℝ) (k l : ℕ) :
    upperBlockEntropy b x (k + l) ≤ upperBlockEntropy b x k + upperBlockEntropy b x l := by
  have h1 : upperBlockEntropy b x (k + l) ≤
      limsup (fun N ↦ blockEntropy b x k N + blockEntropy b (x * (b : ℝ) ^ k) l N) atTop :=
    limsup_le_limsup (Eventually.of_forall fun N ↦ blockEntropy_add_le hb x k l N)
      (isCoboundedUnder_le_blockEntropy hb x (k + l))
      ⟨(k : ℝ) + l, eventually_map.2 (Eventually.of_forall fun N ↦
        add_le_add (blockEntropy_le hb x k N) (blockEntropy_le hb (x * (b : ℝ) ^ k) l N))⟩
  have h2 := limsup_add_le_of_bounds
    (fun N ↦ ⟨blockEntropy_nonneg hb x k N, blockEntropy_le hb x k N⟩)
    (fun N ↦ ⟨blockEntropy_nonneg hb (x * (b : ℝ) ^ k) l N,
      blockEntropy_le hb (x * (b : ℝ) ^ k) l N⟩)
  calc upperBlockEntropy b x (k + l)
      ≤ limsup (fun N ↦ blockEntropy b x k N + blockEntropy b (x * (b : ℝ) ^ k) l N) atTop := h1
    _ ≤ upperBlockEntropy b x k + upperBlockEntropy b (x * (b : ℝ) ^ k) l := h2
    _ = upperBlockEntropy b x k + upperBlockEntropy b x l := by
        rw [upperBlockEntropy_mul_pow hb x k l]

/-- **Manai Proposition 3.2 (Fekete's lemma)**: the normalized upper block entropy
`upperBlockEntropy b x k / k` converges to `rauzyEntropy b x` as `k → ∞`. -/
theorem tendsto_upperBlockEntropy_div (hb : 2 ≤ b) (x : ℝ) :
    Tendsto (fun k : ℕ ↦ upperBlockEntropy b x k / (k : ℝ)) atTop (𝓝 (rauzyEntropy b x)) := by
  have hsub : Subadditive (fun k : ℕ ↦ upperBlockEntropy b x k) :=
    fun k l ↦ upperBlockEntropy_add_le hb x k l
  have hbdd : BddBelow (Set.range fun k : ℕ ↦ upperBlockEntropy b x k / (k : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact div_nonneg (upperBlockEntropy_nonneg hb x k) (Nat.cast_nonneg k)
  have hlim : hsub.lim = rauzyEntropy b x := by
    rw [Subadditive.lim]
    rfl
  simpa [hlim] using hsub.tendsto_lim hbdd

/-! ### Section 4: Entropic characterization of normal numbers -/

theorem tendsto_blockEntropy_of_isNormalIn (hb : 2 ≤ b) (hx : IsNormalIn b x) (k : ℕ) :
    Tendsto (fun N ↦ blockEntropy b x k N) atTop (𝓝 (k : ℝ)) := by
  have hlog : Real.log b ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < b by omega))).ne'
  have hterm : ∀ w : Fin k → Fin b,
      Tendsto (fun N ↦ Real.negMulLog (blockFreq b x w N)) atTop
        (𝓝 (Real.negMulLog (((b : ℝ) ^ k)⁻¹))) := fun w ↦
    (Real.continuous_negMulLog.continuousAt.tendsto).comp (hx k w)
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin b)) fun w _ ↦ hterm w
  have hdiv := hsum.div_const (Real.log b)
  have hlim : (∑ _w : Fin k → Fin b, Real.negMulLog (((b : ℝ) ^ k)⁻¹)) / Real.log b = (k : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Real.negMulLog, Real.log_inv, Real.log_pow]
    have hbk : (b : ℝ) ^ k ≠ 0 := pow_ne_zero k (by positivity)
    field_simp [hbk, hlog]
  rw [hlim] at hdiv
  exact hdiv

theorem rauzyEntropy_eq_one_of_isNormalIn (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    rauzyEntropy b x = 1 := by
  have h1 := tendsto_upperBlockEntropy_div hb x
  have h2 : Tendsto (fun k : ℕ ↦ upperBlockEntropy b x k / (k : ℝ)) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hlim : upperBlockEntropy b x k = (k : ℝ) :=
      (tendsto_blockEntropy_of_isNormalIn hb hx k).limsup_eq
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    rw [hlim, div_self hk0]
  exact tendsto_nhds_unique h1 h2

theorem isNormalIn_of_forall_lowerBlockEntropy_eq (hb : 2 ≤ b)
    (h : ∀ k : ℕ, 1 ≤ k → lowerBlockEntropy b x k = (k : ℝ)) : IsNormalIn b x := by
  have hb0 : 0 < b := by omega
  have hlog : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  intro k w₀
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hc : blockCount b x w₀ N = N := by simp [blockCount]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp [hc, div_self hN0]
  · by_contra hnot
    change ¬ Tendsto (fun N ↦ blockFreq b x w₀ N) atTop (𝓝 ((b : ℝ) ^ k)⁻¹) at hnot
    rw [Metric.tendsto_atTop] at hnot
    push Not at hnot
    obtain ⟨ε, hε, hfreq⟩ := hnot
    -- Build a strictly increasing sequence `φ : ℕ → ℕ` with `1 ≤ φ n` and `ε ≤ dist ...`
    have hstep : ∀ m : ℕ, ∃ N ≥ m, ε ≤ dist (blockFreq b x w₀ N) ((b : ℝ) ^ k)⁻¹ := hfreq
    let φ : ℕ → ℕ := Nat.rec (Classical.choose (hstep 1)) fun _ prev ↦
      Classical.choose (hstep (prev + 1))
    have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ fun n ↦ by
      have hge : φ n + 1 ≤ φ (n + 1) := (Classical.choose_spec (hstep (φ n + 1))).1
      omega
    have hφ_pos : ∀ n, 0 < φ n := fun n ↦ by
      cases n with
      | zero =>
        have h1 : 1 ≤ φ 0 := (Classical.choose_spec (hstep 1)).1
        omega
      | succ n =>
        have h1 : φ n + 1 ≤ φ (n + 1) := (Classical.choose_spec (hstep (φ n + 1))).1
        omega
    have hφ_dist : ∀ n, ε ≤ dist (blockFreq b x w₀ (φ n)) ((b : ℝ) ^ k)⁻¹ := fun n ↦ by
      cases n with
      | zero => exact (Classical.choose_spec (hstep 1)).2
      | succ n => exact (Classical.choose_spec (hstep (φ n + 1))).2
    -- Extract a convergent subsequence of empirical distributions in `[0, 1]^(Fin k → Fin b)`
    let K : Set ((Fin k → Fin b) → ℝ) := Set.pi Set.univ fun _ ↦ Set.Icc (0 : ℝ) 1
    have hK : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
    let P : ℕ → (Fin k → Fin b) → ℝ := fun n w ↦ blockFreq b x w (φ n)
    have hPK : ∀ n, P n ∈ K := fun n w _ ↦
      ⟨blockFreq_nonneg b x w (φ n), blockFreq_le_one b x w (φ n)⟩
    obtain ⟨p, hpK, ψ, hψ_mono, hψ_tendsto⟩ := hK.tendsto_subseq hPK
    have hp_coord : ∀ w, Tendsto (fun n ↦ blockFreq b x w (φ (ψ n))) atTop (𝓝 (p w)) :=
      fun w ↦ (continuous_apply w).continuousAt.tendsto.comp hψ_tendsto
    have hp_nn : ∀ w, 0 ≤ p w := fun w ↦ (hpK w (Set.mem_univ w)).1
    have hp_sum : ∑ w : Fin k → Fin b, p w = 1 := by
      have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin b)) fun w _ ↦ hp_coord w
      have h2 : Tendsto (fun n ↦ ∑ w : Fin k → Fin b, blockFreq b x w (φ (ψ n))) atTop (𝓝 1) :=
        tendsto_const_nhds.congr fun n ↦ (sum_blockFreq hb0 x k (hφ_pos (ψ n))).symm
      exact tendsto_nhds_unique h1 h2
    have hp_ne : p w₀ ≠ (Fintype.card (Fin k → Fin b) : ℝ)⁻¹ := by
      have hcard : (Fintype.card (Fin k → Fin b) : ℝ)⁻¹ = ((b : ℝ) ^ k)⁻¹ := by
        simp
      rw [hcard]
      intro heq
      have hd : Tendsto (fun n ↦ dist (blockFreq b x w₀ (φ (ψ n))) ((b : ℝ) ^ k)⁻¹)
          atTop (𝓝 0) := by
        simpa [heq] using (hp_coord w₀).dist (tendsto_const_nhds (x := ((b : ℝ) ^ k)⁻¹))
      have hge0 : ε ≤ 0 := ge_of_tendsto hd (Eventually.of_forall fun n ↦ hφ_dist (ψ n))
      linarith
    -- Strict Gibbs gives limit entropy `< k`
    set L : ℝ := (∑ w : Fin k → Fin b, Real.negMulLog (p w)) / Real.log b
    have hL_lt : L < (k : ℝ) := by
      dsimp only [L]
      rw [div_lt_iff₀ hlog]
      calc ∑ w : Fin k → Fin b, Real.negMulLog (p w)
          < Real.log (Fintype.card (Fin k → Fin b)) :=
            sum_negMulLog_lt_log_card hp_nn hp_sum hp_ne
        _ = Real.log ((b : ℝ) ^ k) := by simp
        _ = (k : ℝ) * Real.log b := Real.log_pow (b : ℝ) k
    have hEnt_sub : Tendsto (fun n ↦ blockEntropy b x k (φ (ψ n))) atTop (𝓝 L) := by
      have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin b)) fun w _ ↦
        Real.continuous_negMulLog.continuousAt.tendsto.comp (hp_coord w)
      exact hsum.div_const (Real.log b)
    -- Contradict `lowerBlockEntropy b x k = k`
    set M : ℝ := (L + k) / 2
    have hLM : L < M := by dsimp only [M]; linarith
    have hMk : M < (k : ℝ) := by dsimp only [M]; linarith
    have hlow_ev : ∀ᶠ N in atTop, M < blockEntropy b x k N := by
      refine eventually_lt_of_lt_liminf ?_ (isBoundedUnder_ge_blockEntropy hb x k)
      rwa [← lowerBlockEntropy, h k hk]
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlow_ev
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hEnt_sub.eventually (gt_mem_nhds hLM))
    set n := max N₀ n₀
    have hcomp_mono : StrictMono (φ ∘ ψ) := hφ_mono.comp hψ_mono
    have hge : N₀ ≤ φ (ψ n) := (le_max_left N₀ n₀).trans (hcomp_mono.id_le n)
    have h1 := hN₀ (φ (ψ n)) hge
    have h2 := hn₀ n (le_max_right N₀ n₀)
    linarith

/-- **Entropic characterization of normal numbers**: `x` is normal in base `b ≥ 2` iff for every
`k ≥ 1`, its empirical block entropy `blockEntropy b x k N` converges to `k` as `N → ∞`. -/
theorem isNormalIn_iff_tendsto_blockEntropy (hb : 2 ≤ b) :
    IsNormalIn b x ↔ ∀ k : ℕ, 1 ≤ k → Tendsto (fun N ↦ blockEntropy b x k N) atTop (𝓝 (k : ℝ)) :=
  ⟨fun hx k _ ↦ tendsto_blockEntropy_of_isNormalIn hb hx k,
    fun h ↦ isNormalIn_of_forall_lowerBlockEntropy_eq hb fun k hk ↦ (h k hk).liminf_eq⟩

/-- **Lower block entropy characterization of normal numbers**: `x` is normal in base `b ≥ 2` iff
`lowerBlockEntropy b x k = k` for every `k ≥ 1`. -/
theorem isNormalIn_iff_lowerBlockEntropy_eq (hb : 2 ≤ b) :
    IsNormalIn b x ↔ ∀ k : ℕ, 1 ≤ k → lowerBlockEntropy b x k = (k : ℝ) :=
  ⟨fun hx k _ ↦ (tendsto_blockEntropy_of_isNormalIn hb hx k).liminf_eq,
    isNormalIn_of_forall_lowerBlockEntropy_eq hb⟩

/-! ### Section 5: Zero Rauzy entropy for deterministic examples -/

/-- Every rational number has Rauzy entropy `0` in every base `b ≥ 2`. -/
theorem rauzyEntropy_ratCast (hb : 2 ≤ b) (q : ℚ) : rauzyEntropy b (q : ℝ) = 0 := by
  have hb0 : 0 < b := by omega
  have hlog : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  set d := q.den with hd
  have hd_pos : 0 < d := q.den_pos
  have hupper : ∀ k : ℕ, upperBlockEntropy b (q : ℝ) k ≤ Real.log d / Real.log b := by
    intro k
    let blk : ℝ → Fin k → Fin b := fun y j ↦ ⟨digit b y j, digit_lt hb0 y j⟩
    classical
    let S : Finset (Fin k → Fin b) := (Finset.range d).image fun t : ℕ ↦ blk ((t : ℝ) / d)
    have hS_card : S.card ≤ d :=
      Finset.card_image_le.trans (by rw [Finset.card_range])
    -- Every block appearing in `(q : ℝ)` belongs to `S`
    have hmem : ∀ i : ℕ, (fun j : Fin k ↦ (⟨digit b (q : ℝ) (i + j), digit_lt hb0 _ _⟩ : Fin b))
        ∈ S := by
      intro i
      refine Finset.mem_image.2 ⟨((q.num * (b : ℤ) ^ i) % (d : ℤ)).toNat, ?_, ?_⟩
      · have hdZ : (0 : ℤ) < d := by exact_mod_cast hd_pos
        rw [Finset.mem_range, ← Int.ofNat_lt,
          Int.toNat_of_nonneg (Int.emod_nonneg _ hdZ.ne')]
        exact Int.emod_lt_of_pos _ hdZ
      · ext j
        have hdZ0 : (0 : ℤ) ≤ (q.num * (b : ℤ) ^ i) % (d : ℤ) :=
          Int.emod_nonneg _ (by exact_mod_cast hd_pos.ne')
        have hfr : Int.fract ((q : ℝ) * (b : ℝ) ^ i) =
            (((q.num * (b : ℤ) ^ i) % (d : ℤ)).toNat : ℝ) / d := by
          have : (q : ℝ) * (b : ℝ) ^ i = ((q.num * (b : ℤ) ^ i : ℤ) : ℝ) / (d : ℕ) := by
            rw [hd]; push_cast; rw [Rat.cast_def]; ring
          rw [this, Int.fract_div_intCast_eq_div_intCast_mod]
          congr 1
          exact_mod_cast (Int.toNat_of_nonneg hdZ0).symm
        simp only [blk]
        rw [digit_add_eq_digit_fract, hfr]
    have hbound : ∀ N : ℕ, blockEntropy b (q : ℝ) k N ≤ Real.log d / Real.log b := by
      intro N
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · rw [blockEntropy_zero_right]
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd_pos)) hlog.le
      · have hzero : ∀ w : Fin k → Fin b, w ∉ S → blockFreq b (q : ℝ) w N = 0 := by
          intro w hw
          have hc0 : blockCount b (q : ℝ) w N = 0 := by
            rw [blockCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro i _ hi
            apply hw
            have heq : (fun j : Fin k ↦ (⟨digit b (q : ℝ) (i + j), digit_lt hb0 _ _⟩ : Fin b))
                = w := funext fun j ↦ Fin.ext (hi j)
            rw [← heq]
            exact hmem i
          simp [blockFreq, hc0]
        have hsum_S : ∑ w ∈ S, blockFreq b (q : ℝ) w N = 1 := by
          rw [← sum_blockFreq hb0 (q : ℝ) k hN]
          exact Finset.sum_subset (Finset.subset_univ S) fun w _ hw ↦ hzero w hw
        have hsum_ent : ∑ w : Fin k → Fin b, Real.negMulLog (blockFreq b (q : ℝ) w N) =
            ∑ w ∈ S, Real.negMulLog (blockFreq b (q : ℝ) w N) := by
          symm
          refine Finset.sum_subset (Finset.subset_univ S) fun w _ hw ↦ ?_
          rw [hzero w hw, Real.negMulLog_zero]
        have hS_pos : 0 < S.card := by
          by_contra h0
          have hSe : S = ∅ := Finset.card_eq_zero.1 (Nat.eq_zero_of_not_pos h0)
          simp [hSe] at hsum_S
        unfold blockEntropy
        rw [hsum_ent]
        refine div_le_div_of_nonneg_right ?_ hlog.le
        calc ∑ w ∈ S, Real.negMulLog (blockFreq b (q : ℝ) w N)
            ≤ Real.log (S.card : ℝ) :=
              sum_negMulLog_finset_le_log_card (fun w _ ↦ blockFreq_nonneg _ _ _ _) hsum_S
          _ ≤ Real.log (d : ℝ) :=
              Real.log_le_log (by exact_mod_cast hS_pos) (by exact_mod_cast hS_card)
    exact limsup_le_of_le (isCoboundedUnder_le_blockEntropy hb (q : ℝ) k)
      (Eventually.of_forall hbound)
  refine le_antisymm ?_ (rauzyEntropy_nonneg hb (q : ℝ))
  have h1 := tendsto_upperBlockEntropy_div hb (q : ℝ)
  have h2 : Tendsto (fun k : ℕ ↦ (Real.log d / Real.log b) / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  exact le_of_tendsto_of_tendsto h1 h2
    (Eventually.of_forall fun k ↦ div_le_div_of_nonneg_right (hupper k) (Nat.cast_nonneg k))

/-- If the nonzero base-`b` digits of `x` have asymptotic density `0`, then `blockEntropy b x k N`
tends to `0` for every `k : ℕ`. -/
theorem tendsto_blockEntropy_zero_of_density_zero_nonzero_digits (hb : 2 ≤ b)
    (hx : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card : ℝ) / N) atTop (𝓝 0))
    (k : ℕ) : Tendsto (fun N ↦ blockEntropy b x k N) atTop (𝓝 0) := by
  have hb0 : 0 < b := by omega
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [blockEntropy_zero_left]
  · let w₀ : Fin k → Fin b := fun _ ↦ ⟨0, hb0⟩
    set D : ℕ → Finset ℕ := fun M ↦ (Finset.range M).filter fun n ↦ digit b x n ≠ 0
    have hratio : Tendsto (fun N : ℕ ↦ ((N : ℝ) + k) / N) atTop (𝓝 1) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)).const_add 1
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [add_div, div_self (by exact_mod_cast hN.ne')]
    have hD_shift : Tendsto (fun N : ℕ ↦ ((D (N + k)).card : ℝ) / N) atTop (𝓝 0) := by
      have hcomp := hx.comp (tendsto_add_atTop_nat k)
      have hmul := hcomp.mul hratio
      rw [zero_mul] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hNk : (N : ℝ) + k ≠ 0 := by positivity
      dsimp only [Function.comp_apply, D]
      push_cast
      field_simp
    -- `1 - blockFreq b x w₀ N → 0`
    have h1_sub : Tendsto (fun N ↦ 1 - blockFreq b x w₀ N) atTop (𝓝 0) := by
      have hbd : Tendsto (fun N ↦ (k : ℝ) * (((D (N + k)).card : ℝ) / N)) atTop (𝓝 0) := by
        simpa using hD_shift.const_mul (k : ℝ)
      refine squeeze_zero' (Eventually.of_forall fun N ↦ by linarith [blockFreq_le_one b x w₀ N])
        ?_ hbd
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      -- Positions `i < N` where the `k`-block is not all zero are covered by shifted `D (N + k)`
      let B := (Finset.range N).filter fun i ↦ ¬ ∀ j : Fin k, digit b x (i + j) = (w₀ j : ℕ)
      let U := (Finset.range k).biUnion fun j ↦ (D (N + k)).image fun m ↦ m - j
      have hBU : B ⊆ U := by
        intro i hi
        simp only [B, Finset.mem_filter, Finset.mem_range] at hi
        push Not at hi
        obtain ⟨hiN, j, hj⟩ := hi
        simp only [U, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
        refine ⟨j, j.isLt, i + j, ?_, Nat.add_sub_cancel i j⟩
        simp only [D, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hj⟩
      have hU_card : U.card ≤ k * (D (N + k)).card := by
        refine Finset.card_biUnion_le.trans ?_
        calc ∑ j ∈ Finset.range k, ((D (N + k)).image fun m ↦ m - j).card
            ≤ ∑ _j ∈ Finset.range k, (D (N + k)).card :=
              Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le
          _ = k * (D (N + k)).card := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hpart : blockCount b x w₀ N + B.card = N := by
        classical
        have := Finset.card_filter_add_card_filter_not
          (s := Finset.range N) (p := fun i ↦ ∀ j : Fin k, digit b x (i + j) = (w₀ j : ℕ))
        simpa [blockCount, B, Finset.card_range] using this
      have hsub_eq : 1 - blockFreq b x w₀ N = (B.card : ℝ) / N := by
        have hcast : (blockCount b x w₀ N : ℝ) + (B.card : ℝ) = N := by exact_mod_cast hpart
        unfold blockFreq
        rw [eq_div_iff hNpos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hNpos.ne']
        linarith
      rw [hsub_eq, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (Finset.card_le_card hBU).trans hU_card)
        hNpos.le
    have hw₀ : Tendsto (fun N ↦ blockFreq b x w₀ N) atTop (𝓝 1) := by
      have := h1_sub.const_sub 1
      simpa using this
    have hne : ∀ w : Fin k → Fin b, w ≠ w₀ →
        Tendsto (fun N ↦ blockFreq b x w N) atTop (𝓝 0) := fun w hww₀ ↦ by
      refine squeeze_zero' (Eventually.of_forall fun N ↦ blockFreq_nonneg b x w N) ?_ h1_sub
      filter_upwards [eventually_gt_atTop 0] with N hN
      have h2le : blockFreq b x w N + blockFreq b x w₀ N ≤
          ∑ u : Fin k → Fin b, blockFreq b x u N := by
        have hsub : ({w, w₀} : Finset (Fin k → Fin b)) ⊆ Finset.univ := Finset.subset_univ _
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ ↦
          blockFreq_nonneg b x u N
        simpa [Finset.sum_pair hww₀] using hle
      rw [sum_blockFreq hb0 x k hN] at h2le
      linarith
    have hterm : ∀ w : Fin k → Fin b,
        Tendsto (fun N ↦ Real.negMulLog (blockFreq b x w N)) atTop (𝓝 0) := fun w ↦ by
      by_cases hww₀ : w = w₀
      · subst hww₀
        simpa [Real.negMulLog_one, Function.comp_def] using
          Real.continuous_negMulLog.continuousAt.tendsto.comp hw₀
      · simpa [Real.negMulLog_zero, Function.comp_def] using
          Real.continuous_negMulLog.continuousAt.tendsto.comp (hne w hww₀)
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin b)) fun w _ ↦ hterm w
    simp only [Finset.sum_const_zero] at hsum
    simpa [blockEntropy] using hsum.div_const (Real.log b)

/-- If the nonzero base-`b` digits of `x` have asymptotic density `0`, then `x` has Rauzy entropy
`0` in base `b`. -/
theorem rauzyEntropy_eq_zero_of_density_zero_nonzero_digits (hb : 2 ≤ b)
    (hx : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card : ℝ) / N) atTop (𝓝 0)) :
    rauzyEntropy b x = 0 := by
  have h1 := tendsto_upperBlockEntropy_div hb x
  have h2 : Tendsto (fun k : ℕ ↦ upperBlockEntropy b x k / (k : ℝ)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr fun k ↦ ?_
    have hlim : upperBlockEntropy b x k = 0 :=
      (tendsto_blockEntropy_zero_of_density_zero_nonzero_digits hb hx k).limsup_eq
    simp [hlim]
  exact tendsto_nhds_unique h1 h2

/-! #### Sparse base-`b` series and Liouville numbers -/

private lemma summable_sparseSeries_aux (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (c : ℕ → Bool) :
    Summable fun k : ℕ ↦ if c k then ((b : ℝ) ^ (a k + 1))⁻¹ else 0 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hgeom : Summable fun k : ℕ ↦ ((b : ℝ)⁻¹) ^ k :=
    summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)
  refine Summable.of_nonneg_of_le (fun k ↦ by split_ifs <;> positivity) (fun k ↦ ?_) hgeom
  split_ifs
  · rw [inv_pow]
    exact inv_anti₀ (by positivity)
      (pow_le_pow_right₀ hb1.le (Nat.le_succ_of_le (ha.id_le k)))
  · positivity

private lemma sparseSeries_tail_le_aux (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (c : ℕ → Bool) (k : ℕ) :
    (∑' r : ℕ, if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) ≤
      2 * ((b : ℝ) ^ (a k + 1))⁻¹ := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hterm : ∀ r : ℕ, (if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0) ≤
      ((b : ℝ) ^ (a k + 1))⁻¹ * ((b : ℝ)⁻¹) ^ r := fun r ↦ by
    have hle : a k + r ≤ a (k + r) := by
      induction r with
      | zero => simp
      | succ r ih =>
        have := ha (show k + r < k + (r + 1) by omega)
        omega
    split_ifs
    · rw [inv_pow, ← mul_inv, ← pow_add]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hb1.le (by omega))
    · positivity
  have hgeom : Summable fun r : ℕ ↦ ((b : ℝ) ^ (a k + 1))⁻¹ * ((b : ℝ)⁻¹) ^ r :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)).mul_left _
  have hsum_tail : Summable fun r : ℕ ↦
      if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0 := by
    have h := (summable_nat_add_iff k).2 (summable_sparseSeries_aux hb ha c)
    simpa [Nat.add_comm] using h
  calc (∑' r : ℕ, if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0)
      ≤ ∑' r : ℕ, ((b : ℝ) ^ (a k + 1))⁻¹ * ((b : ℝ)⁻¹) ^ r :=
        hsum_tail.tsum_le_tsum hterm hgeom
    _ = ((b : ℝ) ^ (a k + 1))⁻¹ * (1 - (b : ℝ)⁻¹)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)]
    _ ≤ 2 * ((b : ℝ) ^ (a k + 1))⁻¹ := by
        have hinv : (1 - (b : ℝ)⁻¹)⁻¹ ≤ 2 := by
          have hsub : (1 : ℝ) / 2 ≤ 1 - (b : ℝ)⁻¹ := by
            have : (b : ℝ)⁻¹ ≤ 1 / 2 := by
              rw [inv_eq_one_div]
              exact one_div_le_one_div_of_le (by norm_num) hb2
            linarith
          have hinv_le := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hsub
          norm_num at hinv_le
          exact hinv_le
        have hpos : 0 ≤ ((b : ℝ) ^ (a k + 1))⁻¹ := by positivity
        nlinarith

/-- Outside `Set.range a` and its immediate predecessors `{i | i + 1 ∈ Set.range a}`, every
base-`b` digit of `sparseSeries b a c` is `0`. -/
private lemma digit_sparseSeries_eq_zero_of_notMem (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (c : ℕ → Bool) {i : ℕ} (hi0 : i ∉ Set.range a) (hi1 : i + 1 ∉ Set.range a) :
    digit b (sparseSeries b a c) i = 0 := by
  have hb0 : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by positivity
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hex : ∃ m : ℕ, i < a m := ⟨i + 1, lt_of_lt_of_le (Nat.lt_succ_self i) (ha.id_le (i + 1))⟩
  let k := Nat.find hex
  have hk_gt : i < a k := Nat.find_spec hex
  have hk_ge2 : i + 2 ≤ a k := by
    have hne : a k ≠ i + 1 := fun h ↦ hi1 ⟨k, h⟩
    omega
  have hprev : ∀ m < k, a m < i := fun m hm ↦ by
    have hle : a m ≤ i := le_of_not_gt (Nat.find_min hex hm)
    have hne : a m ≠ i := fun h ↦ hi0 ⟨m, h⟩
    omega
  set t := sparseSeries b a c
  set P : ℝ := ∑ m ∈ Finset.range k, if c m then ((b : ℝ) ^ (a m + 1))⁻¹ else 0
  set R : ℝ := ∑' r : ℕ, if c (k + r) then ((b : ℝ) ^ (a (k + r) + 1))⁻¹ else 0
  have ht_eq : t = P + R := by
    have hsplit := (summable_sparseSeries_aux hb ha c).sum_add_tsum_nat_add k
    dsimp only [t, sparseSeries, P, R]
    rw [← hsplit]
    congr 1
    exact tsum_congr fun r ↦ by rw [Nat.add_comm]
  have hP_int : ∃ M : ℤ, P * (b : ℝ) ^ (i + 1) = (M : ℝ) * (b : ℝ) := by
    dsimp only [P]
    rw [Finset.sum_mul]
    have hterm : ∀ m ∈ Finset.range k,
        (if c m then ((b : ℝ) ^ (a m + 1))⁻¹ else 0) * (b : ℝ) ^ (i + 1) =
          (((if c m then b ^ (i - (a m + 1)) else 0 : ℕ) : ℤ) : ℝ) * (b : ℝ) := fun m hm ↦ by
      have ham : a m + 1 ≤ i := hprev m (Finset.mem_range.1 hm)
      split_ifs
      · have hpow : (b : ℝ) ^ (i + 1) =
            (b : ℝ) ^ (a m + 1) * (b : ℝ) ^ (i - (a m + 1)) * (b : ℝ) := by
          rw [← pow_add, ← pow_succ]
          congr 1; omega
        rw [hpow]
        have hpos : (b : ℝ) ^ (a m + 1) ≠ 0 := by positivity
        field_simp [hpos]
        norm_cast
      · simp
    refine ⟨∑ m ∈ Finset.range k, ((if c m then b ^ (i - (a m + 1)) else 0 : ℕ) : ℤ), ?_⟩
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    push_cast
    rfl
  have hR_nn : 0 ≤ R := tsum_nonneg fun r ↦ by split_ifs <;> positivity
  have hR_lt : R * (b : ℝ) ^ (i + 1) < 1 := by
    have hle := sparseSeries_tail_le_aux hb ha c k
    have hdiff : a k + 1 = (i + 1) + (a k - i) := by omega
    calc R * (b : ℝ) ^ (i + 1)
        ≤ (2 * ((b : ℝ) ^ (a k + 1))⁻¹) * (b : ℝ) ^ (i + 1) := by gcongr
      _ = 2 * ((b : ℝ) ^ (a k - i))⁻¹ := by
          rw [hdiff, pow_add]
          field_simp [hbR.ne']
      _ ≤ 2 * ((b : ℝ) ^ 2)⁻¹ := by
          gcongr
          · linarith
          · omega
      _ < 1 := by
          rw [mul_inv_lt_iff₀ (by positivity)]
          nlinarith
  obtain ⟨M, hM⟩ := hP_int
  have hfl : ⌊t * (b : ℝ) ^ (i + 1)⌋ = M * (b : ℤ) := by
    rw [ht_eq, add_mul, hM]
    have hcast : (M : ℝ) * (b : ℝ) = ((M * (b : ℤ) : ℤ) : ℝ) := by push_cast; rfl
    rw [hcast, Int.floor_intCast_add,
      Int.floor_eq_zero_iff.2 ⟨mul_nonneg hR_nn (by positivity), hR_lt⟩, add_zero]
  rw [digit, hfl, Int.mul_emod_left]
  rfl

private lemma sq_le_four_mul_two_pow : ∀ r : ℕ, r ^ 2 ≤ 4 * 2 ^ r
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | r + 4 => by
    have ih := sq_le_four_mul_two_pow (r + 3)
    have h1 : (r + 4) ^ 2 ≤ 2 * (r + 3) ^ 2 := by zify; nlinarith [Int.natCast_nonneg r]
    calc (r + 4) ^ 2 ≤ 2 * (r + 3) ^ 2 := h1
      _ ≤ 2 * (4 * 2 ^ (r + 3)) := Nat.mul_le_mul_left 2 ih
      _ = 4 * 2 ^ (r + 4) := by rw [pow_succ]; ring

open Classical in
private lemma tendsto_range_density_zero_of_ratio_zero {a : ℕ → ℕ} (ha : StrictMono a)
    (hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ n ∈ Set.range a).card : ℝ) / N) atTop (𝓝 0) := by
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 hratio (1 / 2) (by norm_num)
  set K := max K₀ 1
  have hdouble : ∀ k ≥ K, 2 * a k < a (k + 1) := fun k hk ↦ by
    have hspec := hK₀ k (le_trans (le_max_left _ _) hk)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hspec
    have hak1_pos : (0 : ℝ) < a (k + 1) := by
      have : 0 < a (k + 1) := lt_of_lt_of_le (Nat.succ_pos k) (ha.id_le (k + 1))
      positivity
    have hlt := (div_lt_iff₀ hak1_pos).1 hspec
    have : (2 : ℝ) * a k < a (k + 1) := by linarith
    exact_mod_cast this
  have hpow : ∀ r : ℕ, 2 ^ r ≤ a (K + r) := by
    intro r
    induction r with
    | zero =>
      simp only [pow_zero, add_zero]
      have : 1 ≤ K := le_max_right _ _
      exact this.trans (ha.id_le K)
    | succ r ih =>
      have hd := hdouble (K + r) (Nat.le_add_right K r)
      rw [show K + (r + 1) = (K + r) + 1 by omega]
      rw [pow_succ']
      omega
  have hsqrt : Tendsto (fun N : ℕ ↦ (2 * Real.sqrt N + K + 1) / (N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ 2 / Real.sqrt N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun N : ℕ ↦ ((K : ℝ) + 1) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    have hsq0 : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hNpos).ne'
    field_simp [hNpos.ne', hsq0]
    nlinarith
  refine squeeze_zero' (Eventually.of_forall fun N ↦ by positivity) ?_ hsqrt
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine div_le_div_of_nonneg_right ?_ hNpos.le
  -- Every `a m < N` satisfies `m ≤ K + ⌊2 * √N⌋₊`
  set M := K + ⌊2 * Real.sqrt N⌋₊ + 1
  have hsub : ((Finset.range N).filter fun n ↦ n ∈ Set.range a) ⊆ (Finset.range M).image a := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range] at hn
    obtain ⟨hnN, m, rfl⟩ := hn
    refine Finset.mem_image.2 ⟨m, Finset.mem_range.2 ?_, rfl⟩
    by_cases hm : m < K
    · omega
    · set r := m - K
      have hmr : m = K + r := by omega
      rw [hmr] at hnN
      have h2r : 2 ^ r < N := lt_of_le_of_lt (hpow r) hnN
      have hsq_nat : r ^ 2 ≤ 4 * N := (sq_le_four_mul_two_pow r).trans (by omega)
      have hsq_R : (r : ℝ) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := by
        have : (2 * Real.sqrt N) ^ 2 = 4 * (N : ℝ) := by
          rw [mul_pow, Real.sq_sqrt hNpos.le]; norm_num
        rw [this]
        exact_mod_cast hsq_nat
      have hr_le : (r : ℝ) ≤ 2 * Real.sqrt N := by
        nlinarith [Real.sqrt_nonneg N, (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
      have hr_fl : r ≤ ⌊2 * Real.sqrt N⌋₊ := Nat.le_floor hr_le
      omega
  have hcard : ((Finset.range N).filter fun n ↦ n ∈ Set.range a).card ≤ M :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (Finset.card_range M).le)
  have hcast : (((Finset.range N).filter fun n ↦ n ∈ Set.range a).card : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hcard
  have hfl_le : (⌊2 * Real.sqrt N⌋₊ : ℝ) ≤ 2 * Real.sqrt N :=
    Nat.floor_le (by positivity)
  dsimp only [M] at hcast
  push_cast at hcast
  linarith

/-- Any sparse base-`b` series whose exponent sequence satisfies `a k / a (k + 1) → 0` has
zero-density nonzero base-`b` digits. -/
theorem tendsto_nonzero_digits_sparseSeries (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0)) (c : ℕ → Bool) :
    Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b (sparseSeries b a c) n ≠ 0).card : ℝ) / N)
      atTop (𝓝 0) := by
  classical
  have hdens := tendsto_range_density_zero_of_ratio_zero ha hratio
  set S : ℕ → Finset ℕ := fun M ↦ (Finset.range M).filter fun n ↦ n ∈ Set.range a
  have hratio1 : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [add_div, div_self (by exact_mod_cast hN.ne')]
  have hS1 : Tendsto (fun N : ℕ ↦ ((S (N + 1)).card : ℝ) / N) atTop (𝓝 0) := by
    have hmul := (hdens.comp (tendsto_add_atTop_nat 1)).mul hratio1
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
    dsimp only [Function.comp_apply, S]
    push_cast
    field_simp
  have hbound : Tendsto (fun N : ℕ ↦ 2 * (((S (N + 1)).card : ℝ) / N)) atTop (𝓝 0) := by
    simpa using hS1.const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun N ↦ by positivity) ?_ hbound
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hNpos.le
  have hsub : ((Finset.range N).filter fun n ↦ digit b (sparseSeries b a c) n ≠ 0) ⊆
      S (N + 1) ∪ (S (N + 1)).image fun m ↦ m - 1 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_union, Finset.mem_image, S, Finset.mem_filter, Finset.mem_range]
    by_cases hi0 : i ∈ Set.range a
    · exact Or.inl ⟨by omega, hi0⟩
    · by_cases hi1 : i + 1 ∈ Set.range a
      · exact Or.inr ⟨i + 1, ⟨by omega, hi1⟩, by omega⟩
      · exact absurd (digit_sparseSeries_eq_zero_of_notMem hb ha c hi0 hi1) hi.2
  have hcard : ((Finset.range N).filter fun n ↦ digit b (sparseSeries b a c) n ≠ 0).card ≤
      2 * (S (N + 1)).card := by
    calc _ ≤ (S (N + 1)).card + ((S (N + 1)).image fun m ↦ m - 1).card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ (S (N + 1)).card + (S (N + 1)).card := Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * (S (N + 1)).card := by omega
  exact_mod_cast hcard

/-- Every sparse base-`b` series with `a k / a (k + 1) → 0` has Rauzy entropy `0` in base `b`. -/
theorem rauzyEntropy_sparseSeries (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0)) (c : ℕ → Bool) :
    rauzyEntropy b (sparseSeries b a c) = 0 :=
  rauzyEntropy_eq_zero_of_density_zero_nonzero_digits hb
    (tendsto_nonzero_digits_sparseSeries hb ha hratio c)

/-- Mathlib's base-`b` Liouville number `liouvilleNumber (b : ℝ)` has Rauzy entropy `0` in base
`b ≥ 2`. -/
theorem rauzyEntropy_liouvilleNumber (hb : 2 ≤ b) :
    rauzyEntropy b (liouvilleNumber (b : ℝ)) = 0 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  let a : ℕ → ℕ := fun k ↦ (k + 2).factorial - 1
  have ha : StrictMono a := strictMono_nat_of_lt_succ fun k ↦ by
    have h1 : 1 ≤ (k + 2).factorial := Nat.factorial_pos _
    have hsucc : (k + 1 + 2).factorial = (k + 3) * (k + 2).factorial := by
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.factorial_succ (k + 2)]
    have hlt : (k + 2).factorial < (k + 1 + 2).factorial := by nlinarith
    dsimp only [a]
    omega
  have hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun k ↦ by positivity) (fun k ↦ ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ) |>.comp (tendsto_add_atTop_nat 3))
    dsimp only [Function.comp_apply, a]
    have hfac_pos : 2 ≤ (k + 2).factorial :=
      (show 2 = Nat.factorial 2 by decide).le.trans (Nat.factorial_le (by omega))
    have hnum : (((k + 2).factorial - 1 : ℕ) : ℝ) ≤ ((k + 2).factorial : ℝ) := by
      exact_mod_cast Nat.sub_le _ 1
    have hsucc : (k + 1 + 2).factorial = (k + 3) * (k + 2).factorial := by
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.factorial_succ (k + 2)]
    have hden_nat : (k + 3) * (k + 2).factorial ≤ 2 * ((k + 1 + 2).factorial - 1) := by
      have : 2 ≤ (k + 3) * (k + 2).factorial := by nlinarith
      omega
    have hden : ((k + 3 : ℕ) : ℝ) * ((k + 2).factorial : ℝ) ≤
        2 * (((k + 1 + 2).factorial - 1 : ℕ) : ℝ) := by exact_mod_cast hden_nat
    have hden_pos : (0 : ℝ) < (((k + 1 + 2).factorial - 1 : ℕ) : ℝ) := by
      have : 1 < (k + 1 + 2).factorial := by nlinarith
      have : 0 < (k + 1 + 2).factorial - 1 := by omega
      positivity
    rw [div_le_div_iff₀ hden_pos (by positivity)]
    nlinarith
  -- `liouvilleNumber b = 2 / b + sparseSeries b a (fun _ ↦ true)`, agreeing on digits `n ≥ 1`
  have hsplit := (LiouvilleNumber.summable hb1).sum_add_tsum_nat_add 2
  have hrat : (∑ i ∈ Finset.range 2, 1 / (b : ℝ) ^ i.factorial) = 2 / (b : ℝ) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  have htail : (∑' i : ℕ, 1 / (b : ℝ) ^ (i + 2).factorial) = sparseSeries b a (fun _ ↦ true) := by
    refine tsum_congr fun k ↦ ?_
    have hpos : 1 ≤ (k + 2).factorial := Nat.factorial_pos _
    simp [a, Nat.sub_add_cancel hpos]
  have heq : liouvilleNumber (b : ℝ) = 2 / (b : ℝ) + sparseSeries b a (fun _ ↦ true) := by
    dsimp only [liouvilleNumber]
    rw [← hsplit, hrat, htail]
  have hdig_eq : ∀ n : ℕ, 1 ≤ n →
      digit b (liouvilleNumber (b : ℝ)) n = digit b (sparseSeries b a (fun _ ↦ true)) n := by
    intro n hn
    have hmul : liouvilleNumber (b : ℝ) * (b : ℝ) ^ (n + 1) =
        ((2 * (b : ℤ) ^ n : ℤ) : ℝ) + sparseSeries b a (fun _ ↦ true) * (b : ℝ) ^ (n + 1) := by
      rw [heq, add_mul]
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have h1 : 2 / (b : ℝ) * (b : ℝ) ^ (n + 1) = 2 * (b : ℝ) ^ n := by
        rw [pow_succ]; field_simp [hb0]
      rw [h1]
      push_cast
      rfl
    have hdvd : (b : ℤ) ∣ 2 * (b : ℤ) ^ n := (dvd_pow_self _ (by omega)).mul_left 2
    rw [digit, digit, hmul, Int.floor_intCast_add, Int.add_emod, Int.emod_eq_zero_of_dvd hdvd,
      zero_add, Int.emod_emod]
  refine rauzyEntropy_eq_zero_of_density_zero_nonzero_digits hb ?_
  have hsp := tendsto_nonzero_digits_sparseSeries hb ha hratio (fun _ ↦ true)
  have hbound : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b (sparseSeries b a (fun _ ↦ true)) n ≠ 0).card : ℝ)
        / N + 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa using hsp.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  refine squeeze_zero' (Eventually.of_forall fun N ↦ by positivity) ?_ hbound
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hNpos.le
  have hsub : ((Finset.range N).filter fun n ↦ digit b (liouvilleNumber (b : ℝ)) n ≠ 0) ⊆
      ((Finset.range N).filter fun n ↦ digit b (sparseSeries b a (fun _ ↦ true)) n ≠ 0) ∪ {0} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · exact Or.inr rfl
    · exact Or.inl ⟨hn.1, by rw [← hdig_eq n hn1]; exact hn.2⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_singleton] at hcard
  exact_mod_cast hcard

/-! ### Section 6: Algebraic & base-power laws for additive preservers -/

/-- The additive normality preservers in base `b ^ m` (`m ≥ 1`) coincide with those in base `b`. -/
theorem normalAddPreservers_pow (hb : 2 ≤ b) {m : ℕ} (hm : 0 < m)
    (hbm : 2 ≤ b ^ m := hb.trans (Nat.le_self_pow hm.ne' b)) :
    normalAddPreservers hbm = normalAddPreservers hb := by
  ext α
  change (∀ x : ℝ, IsNormalIn (b ^ m) x → IsNormalIn (b ^ m) (x + α)) ↔
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (x + α))
  simp_rw [isNormalIn_pow_iff hb hm]

/-- No additive normality preserver in base `b ≥ 2` is normal in base `b`. -/
theorem not_isNormalIn_of_mem_normalAddPreservers (hb : 2 ≤ b) {y : ℝ}
    (hy : y ∈ normalAddPreservers hb) : ¬ IsNormalIn b y :=
  fun hnorm ↦ not_preserves_isNormalIn_add_of_isNormalIn hb hnorm hy

/-- No additive preserver of absolute normality is absolutely normal. -/
theorem not_isAbsolutelyNormal_of_mem_absolutelyNormalAddPreservers {y : ℝ}
    (hy : y ∈ absolutelyNormalAddPreservers) : ¬ IsAbsolutelyNormal y :=
  fun hnorm ↦ not_preserves_isAbsolutelyNormal_add_of_isAbsolutelyNormal hnorm hy

/-- The additive preservers of absolute normality are closed under rational scaling. -/
theorem ratCast_mul_mem_absolutelyNormalAddPreservers (q : ℚ) {y : ℝ}
    (hy : y ∈ absolutelyNormalAddPreservers) :
    (q : ℝ) * y ∈ absolutelyNormalAddPreservers := by
  by_cases hq : q = 0
  · subst hq
    simp
  · intro x hx
    have h1 : IsAbsolutelyNormal ((q⁻¹ : ℚ) * x) := fun b hb ↦ by
      simpa using (isNormalIn_mul_add_ratCast_iff hb (inv_ne_zero hq) 0 (x := x)).2 (hx b hb)
    have h2 : IsAbsolutelyNormal ((q⁻¹ : ℚ) * x + y) := hy _ h1
    have h3 : IsAbsolutelyNormal ((q : ℝ) * ((q⁻¹ : ℚ) * x + y)) := fun b hb ↦ by
      simpa using (isNormalIn_mul_add_ratCast_iff hb hq 0
        (x := (q⁻¹ : ℚ) * x + y)).2 (h2 b hb)
    have heq : (q : ℝ) * ((q⁻¹ : ℚ) * x + y) = x + (q : ℝ) * y := by
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      push_cast
      field_simp [hqR]
    rwa [heq] at h3

end Real
