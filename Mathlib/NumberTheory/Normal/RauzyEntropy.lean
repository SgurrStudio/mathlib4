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
  sorry

/-! ### Finite Shannon entropy inequalities (Gibbs and subadditivity) -/

/-- **Gibbs' inequality**: the Shannon entropy of any probability distribution on a finite type `ι`
is at most `log (Fintype.card ι)`. -/
theorem sum_negMulLog_le_log_card {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (Fintype.card ι) := by
  sorry

/-- **Strict Gibbs' inequality**: if a probability distribution `p` on a finite type `ι` is not
uniform, then its Shannon entropy is strictly less than `log (Fintype.card ι)`. -/
theorem sum_negMulLog_lt_log_card {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {i₀ : ι} (hi₀ : p i₀ ≠ (Fintype.card ι : ℝ)⁻¹) :
    ∑ i, Real.negMulLog (p i) < Real.log (Fintype.card ι) := by
  sorry

/-- Gibbs' inequality restricted to a `Finset`. -/
theorem sum_negMulLog_finset_le_log_card {ι : Type*} {s : Finset ι} {p : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤ Real.log s.card := by
  sorry

/-- **Subadditivity of finite Shannon entropy**: for any joint probability distribution `p` on
`α × β`, the joint entropy is at most the sum of its two marginal entropies. -/
theorem sum_negMulLog_prod_le {α β : Type*} [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (hsum : ∑ ab, p ab = 1) :
    ∑ ab : α × β, Real.negMulLog (p ab) ≤
      (∑ a : α, Real.negMulLog (∑ b : β, p (a, b))) +
      (∑ b : β, Real.negMulLog (∑ a : α, p (a, b))) := by
  sorry

/-! ### Section 2: Basic properties and bounds -/

theorem blockFreq_nonneg (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    0 ≤ blockFreq b x w N := by
  sorry

theorem blockFreq_le_one (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) :
    blockFreq b x w N ≤ 1 := by
  sorry

theorem sum_blockFreq (hb : 0 < b) (x : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    ∑ w : Fin k → Fin b, blockFreq b x w N = 1 := by
  sorry

theorem blockEntropy_zero_right (b : ℕ) (x : ℝ) (k : ℕ) :
    blockEntropy b x k 0 = 0 := by
  sorry

theorem blockEntropy_zero_left (b : ℕ) (x : ℝ) (N : ℕ) :
    blockEntropy b x 0 N = 0 := by
  sorry

theorem blockEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) (k N : ℕ) :
    0 ≤ blockEntropy b x k N := by
  sorry

theorem blockEntropy_le (hb : 2 ≤ b) (x : ℝ) (k N : ℕ) :
    blockEntropy b x k N ≤ k := by
  sorry

theorem upperBlockEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    0 ≤ upperBlockEntropy b x k := by
  sorry

theorem upperBlockEntropy_le (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    upperBlockEntropy b x k ≤ k := by
  sorry

theorem lowerBlockEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    0 ≤ lowerBlockEntropy b x k := by
  sorry

theorem lowerBlockEntropy_le_upperBlockEntropy (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    lowerBlockEntropy b x k ≤ upperBlockEntropy b x k := by
  sorry

theorem lowerBlockEntropy_le (hb : 2 ≤ b) (x : ℝ) (k : ℕ) :
    lowerBlockEntropy b x k ≤ k := by
  sorry

theorem upperBlockEntropy_zero (b : ℕ) (x : ℝ) : upperBlockEntropy b x 0 = 0 := by
  sorry

theorem rauzyEntropy_nonneg (hb : 2 ≤ b) (x : ℝ) : 0 ≤ rauzyEntropy b x := by
  sorry

theorem rauzyEntropy_le_div (hb : 2 ≤ b) (x : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    rauzyEntropy b x ≤ upperBlockEntropy b x k / (k : ℝ) := by
  sorry

theorem rauzyEntropy_le_one (hb : 2 ≤ b) (x : ℝ) : rauzyEntropy b x ≤ 1 := by
  sorry

/-! ### Section 3: Subadditivity & Manai Proposition 3.2 (Fekete's lemma) -/

theorem tendsto_blockEntropy_mul_pow_sub (_hb : 2 ≤ b) (x : ℝ) (k l : ℕ) :
    Tendsto (fun N ↦ blockEntropy b (x * (b : ℝ) ^ k) l N - blockEntropy b x l N)
      atTop (𝓝 0) := by
  sorry

theorem upperBlockEntropy_mul_pow (hb : 2 ≤ b) (x : ℝ) (k l : ℕ) :
    upperBlockEntropy b (x * (b : ℝ) ^ k) l = upperBlockEntropy b x l := by
  sorry

theorem blockEntropy_add_le (hb : 2 ≤ b) (x : ℝ) (k l N : ℕ) :
    blockEntropy b x (k + l) N ≤
      blockEntropy b x k N + blockEntropy b (x * (b : ℝ) ^ k) l N := by
  sorry

/-- Subadditivity of the upper block entropy: `H⁺(k + l) ≤ H⁺(k) + H⁺(l)`. -/
theorem upperBlockEntropy_add_le (hb : 2 ≤ b) (x : ℝ) (k l : ℕ) :
    upperBlockEntropy b x (k + l) ≤ upperBlockEntropy b x k + upperBlockEntropy b x l := by
  sorry

/-- **Manai Proposition 3.2 (Fekete's lemma)**: the normalized upper block entropy
`upperBlockEntropy b x k / k` converges to `rauzyEntropy b x` as `k → ∞`. -/
theorem tendsto_upperBlockEntropy_div (hb : 2 ≤ b) (x : ℝ) :
    Tendsto (fun k : ℕ ↦ upperBlockEntropy b x k / (k : ℝ)) atTop (𝓝 (rauzyEntropy b x)) := by
  sorry

/-! ### Section 4: Entropic characterization of normal numbers -/

theorem tendsto_blockEntropy_of_isNormalIn (hb : 2 ≤ b) (hx : IsNormalIn b x) (k : ℕ) :
    Tendsto (fun N ↦ blockEntropy b x k N) atTop (𝓝 (k : ℝ)) := by
  sorry

theorem rauzyEntropy_eq_one_of_isNormalIn (hb : 2 ≤ b) (hx : IsNormalIn b x) :
    rauzyEntropy b x = 1 := by
  sorry

theorem isNormalIn_of_forall_lowerBlockEntropy_eq (hb : 2 ≤ b)
    (h : ∀ k : ℕ, 1 ≤ k → lowerBlockEntropy b x k = (k : ℝ)) : IsNormalIn b x := by
  sorry

/-- **Entropic characterization of normal numbers**: `x` is normal in base `b ≥ 2` iff for every
`k ≥ 1`, its empirical block entropy `blockEntropy b x k N` converges to `k` as `N → ∞`. -/
theorem isNormalIn_iff_tendsto_blockEntropy (hb : 2 ≤ b) :
    IsNormalIn b x ↔ ∀ k : ℕ, 1 ≤ k → Tendsto (fun N ↦ blockEntropy b x k N) atTop (𝓝 (k : ℝ)) := by
  sorry

/-- **Lower block entropy characterization of normal numbers**: `x` is normal in base `b ≥ 2` iff
`lowerBlockEntropy b x k = k` for every `k ≥ 1`. -/
theorem isNormalIn_iff_lowerBlockEntropy_eq (hb : 2 ≤ b) :
    IsNormalIn b x ↔ ∀ k : ℕ, 1 ≤ k → lowerBlockEntropy b x k = (k : ℝ) := by
  sorry

/-! ### Section 5: Zero Rauzy entropy for deterministic examples -/

/-- Every rational number has Rauzy entropy `0` in every base `b ≥ 2`. -/
theorem rauzyEntropy_ratCast (hb : 2 ≤ b) (q : ℚ) : rauzyEntropy b (q : ℝ) = 0 := by
  sorry

/-- If the nonzero base-`b` digits of `x` have asymptotic density `0`, then `blockEntropy b x k N`
tends to `0` for every `k : ℕ`. -/
theorem tendsto_blockEntropy_zero_of_density_zero_nonzero_digits (hb : 2 ≤ b)
    (hx : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card : ℝ) / N) atTop (𝓝 0))
    (k : ℕ) : Tendsto (fun N ↦ blockEntropy b x k N) atTop (𝓝 0) := by
  sorry

/-- If the nonzero base-`b` digits of `x` have asymptotic density `0`, then `x` has Rauzy entropy
`0` in base `b`. -/
theorem rauzyEntropy_eq_zero_of_density_zero_nonzero_digits (hb : 2 ≤ b)
    (hx : Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b x n ≠ 0).card : ℝ) / N) atTop (𝓝 0)) :
    rauzyEntropy b x = 0 := by
  sorry

/-! #### Sparse base-`b` series and Liouville numbers -/

/-- Any sparse base-`b` series whose exponent sequence satisfies `a k / a (k + 1) → 0` has
zero-density nonzero base-`b` digits. -/
theorem tendsto_nonzero_digits_sparseSeries (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0)) (c : ℕ → Bool) :
    Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ digit b (sparseSeries b a c) n ≠ 0).card : ℝ) / N)
      atTop (𝓝 0) := by
  sorry

/-- Every sparse base-`b` series with `a k / a (k + 1) → 0` has Rauzy entropy `0` in base `b`. -/
theorem rauzyEntropy_sparseSeries (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a)
    (hratio : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (a (k + 1) : ℝ)) atTop (𝓝 0)) (c : ℕ → Bool) :
    rauzyEntropy b (sparseSeries b a c) = 0 := by
  sorry

/-- Mathlib's base-`b` Liouville number `liouvilleNumber (b : ℝ)` has Rauzy entropy `0` in base
`b ≥ 2`. -/
theorem rauzyEntropy_liouvilleNumber (hb : 2 ≤ b) :
    rauzyEntropy b (liouvilleNumber (b : ℝ)) = 0 := by
  sorry

/-! ### Section 6: Algebraic & base-power laws for additive preservers -/

/-- The additive normality preservers in base `b ^ m` (`m ≥ 1`) coincide with those in base `b`. -/
theorem normalAddPreservers_pow (hb : 2 ≤ b) {m : ℕ} (hm : 0 < m)
    (hbm : 2 ≤ b ^ m := hb.trans (Nat.le_self_pow hm.ne' b)) :
    normalAddPreservers hbm = normalAddPreservers hb := by
  sorry

/-- No additive normality preserver in base `b ≥ 2` is normal in base `b`. -/
theorem not_isNormalIn_of_mem_normalAddPreservers (hb : 2 ≤ b) {y : ℝ}
    (hy : y ∈ normalAddPreservers hb) : ¬ IsNormalIn b y := by
  sorry

/-- No additive preserver of absolute normality is absolutely normal. -/
theorem not_isAbsolutelyNormal_of_mem_absolutelyNormalAddPreservers {y : ℝ}
    (hy : y ∈ absolutelyNormalAddPreservers) : ¬ IsAbsolutelyNormal y := by
  sorry

/-- The additive preservers of absolute normality are closed under rational scaling. -/
theorem ratCast_mul_mem_absolutelyNormalAddPreservers (q : ℚ) {y : ℝ}
    (hy : y ∈ absolutelyNormalAddPreservers) :
    (q : ℝ) * y ∈ absolutelyNormalAddPreservers := by
  sorry

end Real
