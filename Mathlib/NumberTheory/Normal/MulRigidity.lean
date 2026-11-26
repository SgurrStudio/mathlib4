/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.Normal.Borel
public import Mathlib.NumberTheory.Normal.NonPreservation
public import Mathlib.NumberTheory.Normal.Rational

/-!
# Multiplicative rigidity of normality in a fixed base

A real number `γ` preserves base-`b` normality under multiplication if and only if `γ` is a
nonzero rational (Dayan–Ganguly–Weiss). The reverse implication is Wall's theorem. For the
forward implication we follow the probabilistic proof of Manai (arXiv:2609.24665, §2): if
`θ` is irrational, then `θ Y` is normal in base `b ≥ 3` for almost every point `Y` of the base-`b`
Cantor law (digits in `{0, 1}`), while `Y` itself is never normal. Applying this with
`θ = γ⁻¹` and `B = b ^ 2` gives a base-`b` normal `x = γ⁻¹ Y` with `γ x = Y` not normal.

The almost sure normality is a martingale argument. Write `f_n = e(θ b^n Y)` and let `E_m`
average over all coins after the first `m` (`condE`). Then
`f_{K+t} = (f_{K+t} - E_{t+K+L} f_{K+t}) + ∑_{i < K+L} (E_{t+i+1} - E_{t+i}) f_{K+t} + E_t f_{K+t}`.
The first term is `O(|θ| b^{-L})`, the last has modulus `∏_{r<K} |cos(π θ b^r)|`, which tends to
`0` because `θ` is irrational, and for each `i` the middle terms are orthogonal bounded increments,
so their averages tend to `0` almost surely.

## Main statements

* `NormalNumbers.MulRigidity.ae_isNormal_mul_bReal`: `θ Y` is normal for a.e. Cantor point `Y`.
* `Real.exists_isNormalIn_not_isNormalIn_mul`: for irrational `γ` some base-`b` normal `x` has
  `γ x` not normal in base `b`.
* `Real.preserves_isNormalIn_mul_iff`: multiplication by `γ` preserves base-`b` normality iff
  `γ` is a nonzero rational.

## References

* Y. Dayan, A. Ganguly, B. Weiss, *Random walks on tori and normal numbers in self-similar sets*.
* C. Manai, *On normality preserving operations*, arXiv:2609.24665, §2.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Real ComplexConjugate

namespace NormalNumbers.MulRigidity

open ExplicitSquare CantorSelfSimilar DecayAeNormal BaseCantorDecay

/-! ### Splicing coin sequences and conditional expectations -/

/-- Keep the first `m` coins of `ω` and continue with `η`. -/
def splice (m : ℕ) (ω η : ℕ → Bool) : ℕ → Bool := fun i => if i < m then ω i else η (i - m)

theorem measurable_splice (m : ℕ) :
    Measurable fun p : (ℕ → Bool) × (ℕ → Bool) => splice m p.1 p.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i < m
  · simp only [splice, hi, ite_true]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [splice, hi, ite_false]
    exact (measurable_pi_apply (i - m)).comp measurable_snd

/-- Splicing two independent fair coin sequences gives a fair coin sequence. -/
theorem map_splice (m : ℕ) :
    (coinMeasure.prod coinMeasure).map (fun p => splice m p.1 p.2) = coinMeasure := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hpre : (fun p : (ℕ → Bool) × (ℕ → Bool) => splice m p.1 p.2) ⁻¹' Set.pi (↑s) t =
      Set.pi ↑(s.filter (· < m)) t ×ˢ
        Set.pi ↑(s.preimage (· + m) (add_left_injective m).injOn) (fun j => t (j + m)) := by
    ext ⟨ω, η⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_prod,
      Finset.coe_preimage, Finset.mem_coe, splice]
    constructor
    · intro h
      exact ⟨fun i ⟨hi, him⟩ => by simpa [him] using h i hi,
        fun j hj => by simpa using h (j + m) hj⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases him : i < m
      · simpa [him] using h1 i ⟨hi, him⟩
      · have := h2 (i - m) (by rwa [Nat.sub_add_cancel (not_lt.1 him)])
        simpa [him, Nat.sub_add_cancel (not_lt.1 him)] using this
  rw [Measure.map_apply (measurable_splice m)
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre, Measure.prod_prod]
  unfold coinMeasure
  rw [Measure.infinitePi_pi _ fun i _ => ht i, Measure.infinitePi_pi _ fun j _ => ht (j + m),
    ← Finset.prod_filter_mul_prod_filter_not s (· < m)]
  congr 1
  refine Finset.prod_nbij' (· + m) (· - m) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_preimage, Finset.mem_filter] at hj ⊢
    exact ⟨hj, by omega⟩
  · intro i hi
    simp only [Finset.mem_preimage, Finset.mem_filter] at hi ⊢
    simpa [Nat.sub_add_cancel (not_lt.1 hi.2)] using hi.1
  · intro j _; simp
  · intro i hi
    simp only [Finset.mem_filter] at hi
    exact Nat.sub_add_cancel (not_lt.1 hi.2)
  · intro j _; rfl

theorem integral_splice (m : ℕ) {g : (ℕ → Bool) → ℂ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, g ω ∂coinMeasure = ∫ ω, ∫ η, g (splice m ω η) ∂coinMeasure ∂coinMeasure := by
  have hi : Integrable (fun p : (ℕ → Bool) × (ℕ → Bool) => g (splice m p.1 p.2))
      (coinMeasure.prod coinMeasure) :=
    Integrable.of_bound (hg.comp (measurable_splice m)).aestronglyMeasurable C
      (Eventually.of_forall fun p => hC _)
  rw [← integral_prod _ hi]
  conv_lhs => rw [← map_splice m]
  rw [integral_map (measurable_splice m).aemeasurable hg.aestronglyMeasurable]

/-- Average over all coins after the first `m`. -/
def condE (m : ℕ) (g : (ℕ → Bool) → ℂ) (ω : ℕ → Bool) : ℂ :=
  ∫ η, g (splice m ω η) ∂coinMeasure

/-- `φ` depends only on the first `m` coins. -/
def DepOn (m : ℕ) (φ : (ℕ → Bool) → ℂ) : Prop :=
  ∀ ω ω' : ℕ → Bool, (∀ i < m, ω i = ω' i) → φ ω = φ ω'

theorem depOn_condE (m : ℕ) (g : (ℕ → Bool) → ℂ) : DepOn m (condE m g) := by
  intro ω ω' h
  unfold condE
  congr 1; funext η; congr 1; funext i
  unfold splice
  split_ifs with hi
  · exact h i hi
  · rfl

theorem DepOn.mono {m n : ℕ} {φ : (ℕ → Bool) → ℂ} (h : DepOn m φ) (hmn : m ≤ n) : DepOn n φ :=
  fun ω ω' hω => h ω ω' fun i hi => hω i (lt_of_lt_of_le hi hmn)

theorem DepOn.splice_eq {m : ℕ} {φ : (ℕ → Bool) → ℂ} (h : DepOn m φ) (ω η : ℕ → Bool) :
    φ (splice m ω η) = φ ω :=
  h _ _ fun i hi => by simp [splice, hi]

theorem DepOn.sub {m : ℕ} {φ ψ : (ℕ → Bool) → ℂ} (h : DepOn m φ) (h' : DepOn m ψ) :
    DepOn m (φ - ψ) := fun ω ω' hω => by simp [h ω ω' hω, h' ω ω' hω]

theorem DepOn.conj {m : ℕ} {φ : (ℕ → Bool) → ℂ} (h : DepOn m φ) :
    DepOn m fun ω => conj (φ ω) := fun ω ω' hω => by simp [h ω ω' hω]

theorem measurable_condE (m : ℕ) {g : (ℕ → Bool) → ℂ} (hg : Measurable g) :
    Measurable (condE m g) :=
  ((hg.comp (measurable_splice m)).stronglyMeasurable.integral_prod_right'
    (ν := coinMeasure)).measurable

theorem norm_condE_le (m : ℕ) {g : (ℕ → Bool) → ℂ} {C : ℝ} (hC : ∀ ω, ‖g ω‖ ≤ C)
    (ω : ℕ → Bool) : ‖condE m g ω‖ ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := coinMeasure)
    (f := fun η => g (splice m ω η)) (Eventually.of_forall fun η => hC _)
  simpa [condE] using this

/-- **Projection property**: `E_m` does not change integrals against functions of the first `m`
coins. -/
theorem integral_mul_condE {m : ℕ} {φ g : (ℕ → Bool) → ℂ} (hφ : Measurable φ) (hφd : DepOn m φ)
    {Cφ C : ℝ} (hφb : ∀ ω, ‖φ ω‖ ≤ Cφ) (hg : Measurable g) (hgb : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, φ ω * g ω ∂coinMeasure = ∫ ω, φ ω * condE m g ω ∂coinMeasure := by
  rw [integral_splice m (g := fun ω => φ ω * g ω) (hφ.mul hg) (Cφ * C) fun ω => by
    rw [norm_mul]
    exact mul_le_mul (hφb ω) (hgb ω) (norm_nonneg _) ((norm_nonneg _).trans (hφb ω))]
  congr 1; funext ω
  simp_rw [hφd.splice_eq]
  rw [integral_const_mul]
  rfl

/-- Increments `E_{m+1} g - E_m g` are orthogonal to functions of the first `m` coins. -/
theorem integral_mul_condE_sub {m : ℕ} {φ g : (ℕ → Bool) → ℂ} (hφ : Measurable φ)
    (hφd : DepOn m φ) {Cφ C : ℝ} (hφb : ∀ ω, ‖φ ω‖ ≤ Cφ) (hg : Measurable g)
    (hgb : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, φ ω * (condE (m + 1) g ω - condE m g ω) ∂coinMeasure = 0 := by
  have hφi : ∀ {ψ : (ℕ → Bool) → ℂ}, Measurable ψ → (∀ ω, ‖ψ ω‖ ≤ C) →
      Integrable (fun ω => φ ω * ψ ω) coinMeasure := fun hψ hψb =>
    Integrable.of_bound (hφ.mul hψ).aestronglyMeasurable (Cφ * C)
      (Eventually.of_forall fun ω => by
        rw [norm_mul]
        exact mul_le_mul (hφb ω) (hψb ω) (norm_nonneg _) ((norm_nonneg _).trans (hφb ω)))
  simp_rw [mul_sub]
  rw [integral_sub (hφi (measurable_condE _ hg) (norm_condE_le _ hgb))
    (hφi (measurable_condE _ hg) (norm_condE_le _ hgb)),
    ← integral_mul_condE hφ (hφd.mono (Nat.le_succ m)) hφb hg hgb,
    ← integral_mul_condE hφ hφd hφb hg hgb, sub_self]

/-! ### A strong law for orthogonal bounded increments -/

section StrongLaw

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : ℕ → Ω → ℂ) (hZm : ∀ n, Measurable (Z n)) (hZb : ∀ n ω, ‖Z n ω‖ ≤ 1)
  (horth : ∀ m n, m < n → ∫ ω, conj (Z m ω) * Z n ω ∂μ = 0)

include hZm hZb horth in
theorem integral_norm_sum_sq_le (N : ℕ) :
    ∫ ω, ‖∑ n ∈ Finset.range N, Z n ω‖ ^ 2 ∂μ ≤ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    set S : Ω → ℂ := fun ω => ∑ n ∈ Finset.range N, Z n ω with hS
    have hSm : Measurable S := Finset.measurable_sum _ fun n _ => hZm n
    have hSb : ∀ ω, ‖S ω‖ ≤ N := fun ω => (norm_sum_le _ _).trans (by
      simpa using Finset.sum_le_sum fun n (_ : n ∈ Finset.range N) => hZb n ω)
    have hcm : Measurable fun ω => S ω * conj (Z N ω) :=
      hSm.mul (Complex.continuous_conj.measurable.comp (hZm N))
    have hci : Integrable (fun ω => S ω * conj (Z N ω)) μ :=
      Integrable.of_bound hcm.aestronglyMeasurable N (Eventually.of_forall fun ω => by
        rw [norm_mul, Complex.norm_conj]
        nlinarith [hSb ω, hZb N ω, norm_nonneg (S ω), norm_nonneg (Z N ω)])
    have hcross : ∫ ω, S ω * conj (Z N ω) ∂μ = 0 := by
      simp only [hS, Finset.sum_mul]
      rw [integral_finsetSum _ (f := fun m ω => Z m ω * conj (Z N ω)) fun m _ => Integrable.of_bound
        ((hZm m).mul (Complex.continuous_conj.measurable.comp (hZm N))).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by
          rw [norm_mul, Complex.norm_conj]
          nlinarith [hZb m ω, hZb N ω, norm_nonneg (Z m ω), norm_nonneg (Z N ω)])]
      refine Finset.sum_eq_zero fun m hm => ?_
      have h := horth m N (Finset.mem_range.1 hm)
      have : ∫ ω, Z m ω * conj (Z N ω) ∂μ = conj (∫ ω, conj (Z m ω) * Z N ω ∂μ) := by
        rw [← integral_conj]; congr 1; funext ω; simp
      rw [this, h, map_zero]
    have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = Complex.normSq z := fun z => Complex.sq_norm z
    have hexp : ∀ ω, ‖∑ n ∈ Finset.range (N + 1), Z n ω‖ ^ 2 =
        ‖S ω‖ ^ 2 + ‖Z N ω‖ ^ 2 + 2 * (S ω * conj (Z N ω)).re := fun ω => by
      rw [Finset.sum_range_succ, hsq, hsq, hsq, Complex.normSq_add]
    have hi1 : Integrable (fun ω => ‖S ω‖ ^ 2) μ :=
      Integrable.of_bound ((hSm.norm.pow_const 2).aestronglyMeasurable) ((N : ℝ) ^ 2)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hSb ω) 2)
    have hi2 : Integrable (fun ω => ‖Z N ω‖ ^ 2) μ :=
      Integrable.of_bound (((hZm N).norm.pow_const 2).aestronglyMeasurable) 1
        (Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (by positivity)]
          nlinarith [hZb N ω, norm_nonneg (Z N ω)])
    have hi3 : Integrable (fun ω => 2 * (S ω * conj (Z N ω)).re) μ := hci.re.const_mul 2
    have hi12 : Integrable (fun ω => ‖S ω‖ ^ 2 + ‖Z N ω‖ ^ 2) μ := hi1.add hi2
    simp_rw [hexp]
    rw [integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul]
    have hre : ∫ ω, (S ω * conj (Z N ω)).re ∂μ = 0 := by
      have := integral_re (𝕜 := ℂ) hci
      simp only [RCLike.re_to_complex] at this
      rw [this, hcross, Complex.zero_re]
    have hZ2 : ∫ ω, ‖Z N ω‖ ^ 2 ∂μ ≤ 1 := by
      have := integral_mono hi2 (integrable_const (1 : ℝ)) fun ω => by
        simp only; nlinarith [hZb N ω, norm_nonneg (Z N ω)]
      simpa using this
    rw [hre]
    push_cast
    linarith [ih]

include hZm hZb horth in
/-- **Strong law of large numbers for orthogonal increments** bounded by `1`. -/
theorem ae_tendsto_avg_of_orthogonal :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, Z n ω) / (N : ℂ)) atTop (𝓝 0) := by
  set n : ℕ → ℕ := fun j => (j + 1) ^ 2 with hn
  have hnm : StrictMono n := fun i j hij => Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hratio : Tendsto (fun j => (n (j + 1) : ℝ) / n j) atTop (𝓝 1) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have : Tendsto (fun j : ℕ => (1 + 1 / ((j : ℝ) + 1)) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
      ((tendsto_const_nhds.add h0).pow 2)
    rw [add_zero, one_pow] at this
    refine this.congr fun j => ?_
    simp only [hn]
    push_cast
    field_simp
  set S : ℕ → Ω → ℂ := fun N ω => ∑ k ∈ Finset.range N, Z k ω with hSdef
  have hSm : ∀ N, Measurable (S N) := fun N => Finset.measurable_sum _ fun k _ => hZm k
  have hSb : ∀ N ω, ‖S N ω‖ ≤ N := fun N ω => (norm_sum_le _ _).trans (by
    simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) => hZb k ω)
  set f : ℕ → Ω → ℝ := fun j ω => ‖S (n j) ω‖ ^ 2 / ((n j : ℝ)) ^ 2 with hfdef
  have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by positivity
  have hfm : ∀ j, Measurable (f j) := fun j => (((hSm _).norm.pow_const 2).div_const _)
  have hfi : ∀ j, Integrable (f j) μ := fun j =>
    Integrable.of_bound (hfm j).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hf0 j ω)]
      have hpos' : (0 : ℝ) < n j := by simp only [hn]; positivity
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hSb _ ω) 2)
  have hfI : ∀ j, ∫ ω, f j ω ∂μ ≤ 1 / ((j + 1 : ℕ) : ℝ) ^ 2 := by
    intro j
    have hpos' : (0 : ℝ) < n j := by simp only [hn]; positivity
    simp only [f]
    rw [integral_div, div_le_iff₀ (by positivity)]
    refine (integral_norm_sum_sq_le μ Z hZm hZb horth (n j)).trans_eq ?_
    simp only [hn]; push_cast; field_simp
  have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
    have hs : Summable fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ 2 :=
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, 1 / ((j + 1 : ℕ) : ℝ) ^ 2)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
    refine tsum_le_tsum fun j => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
    exact ENNReal.ofReal_le_ofReal (hfI j)
  have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
    (hfm j).ennreal_ofReal.aemeasurable) hlin
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun j => ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun j => f j ω) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
  have h3 : Tendsto (fun j : ℕ => ‖S (n j) ω‖ / (n j : ℝ)) atTop (𝓝 0) := by
    have := h2.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun j => ?_
    simp only [hfdef]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (by positivity)]
  exact CantorLiouville.tendsto_of_tendsto_sched (fun k => Z k ω) (fun k => hZb k ω) n hnm
    hratio h3

end StrongLaw

/-! ### The cosine product for irrational `θ` -/

section CosProduct

variable {b : ℕ}

/-- For irrational `θ`, infinitely often `θ b^r` is at distance `≥ 1/(2b)` from every integer. -/
theorem exists_far (hb : 2 ≤ b) {θ : ℝ} (hθ : Irrational θ) (r0 : ℕ) :
    ∃ r ≥ r0, ∀ n : ℤ, 1 / (2 * b) ≤ |θ * b ^ r - n| := by
  by_contra hcon
  push Not at hcon
  choose! nr hnr using hcon
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  set e : ℕ → ℝ := fun r => θ * b ^ r - nr r with he
  have hstep : ∀ r ≥ r0, e (r + 1) = b * e r := by
    intro r hr
    have h1 := hnr r hr
    have h2 := hnr (r + 1) (by omega)
    have hz : nr (r + 1) - b * nr r = 0 := by
      have habs : |((nr (r + 1) - b * nr r : ℤ) : ℝ)| < 1 := by
        push_cast
        have : (nr (r + 1) : ℝ) - b * nr r = -(θ * b ^ (r + 1) - nr (r + 1)) +
            b * (θ * b ^ r - nr r) := by ring
        rw [this]
        have hq : 1 / (2 * (b : ℝ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        calc _ ≤ |θ * b ^ (r + 1) - nr (r + 1)| + b * |θ * b ^ r - nr r| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_neg, abs_mul, abs_of_pos hb0]
          _ < 1 / (2 * b) + b * (1 / (2 * b)) := by gcongr
          _ ≤ 1 := by
              rw [show (b : ℝ) * (1 / (2 * b)) = 1 / 2 by field_simp]
              linarith
      have : |nr (r + 1) - b * nr r| < 1 := by exact_mod_cast habs
      exact Int.abs_lt_one_iff.1 this
    have hz' : (nr (r + 1) : ℝ) = b * nr r := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hz
      push_cast at this
      linarith
    simp only [he, hz', pow_succ]
    ring
  have hpow : ∀ j, e (r0 + j) = (b : ℝ) ^ j * e r0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [← add_assoc, hstep _ (by omega), ih, pow_succ]; ring
  have he0 : e r0 = 0 := by
    by_contra hne
    have hpos : 0 < |e r0| := abs_pos.2 hne
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / |e r0|) hb1
    have hlt := hnr (r0 + j) (by omega)
    have : |e (r0 + j)| < 1 / (2 * b) := hlt
    rw [hpow, abs_mul, abs_of_pos (by positivity)] at this
    have h1 : 1 < (b : ℝ) ^ j * |e r0| := by rwa [div_lt_iff₀ hpos] at hj
    have h2 : 1 / (2 * (b : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  apply hθ.ne_rat ((nr r0 : ℚ) / (b : ℚ) ^ r0)
  have : θ * (b : ℝ) ^ r0 = nr r0 := by simp only [he] at he0; linarith
  push_cast
  field_simp
  linarith

/-- `|cos (π x)| ≤ cos (π δ)` when `x` is at distance `≥ δ` from every integer, `δ ≤ 1/2`. -/
theorem abs_cos_le_of_far {x δ : ℝ} (hδ : 0 ≤ δ) (hfar : ∀ n : ℤ, δ ≤ |x - n|) :
    |Real.cos (π * x)| ≤ Real.cos (π * δ) := by
  set t := x - round x with ht
  have ht1 : |t| ≤ 1 / 2 := abs_sub_round x
  have ht2 : δ ≤ |t| := hfar _
  have hcos : |Real.cos (π * x)| = Real.cos (π * |t|) := by
    have : π * x = π * t + (round x : ℤ) * π := by rw [ht]; ring
    rw [this, Real.cos_add_int_mul_pi, abs_mul]
    have h1 : |((-1 : ℝ) ^ (round x : ℤ))| = 1 := by simp
    rw [h1, one_mul]
    have hnn : 0 ≤ Real.cos (π * t) := by
      refine Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
        nlinarith [abs_le.1 ht1, Real.pi_pos]
    rw [abs_of_nonneg hnn]
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cos_neg]
  rw [hcos]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- **Lemma 2.2 of Manai**: for irrational `θ`, `∏_{r<K} |cos (π θ b^r)| → 0`. -/
theorem tendsto_prod_cos (hb : 2 ≤ b) {θ : ℝ} (hθ : Irrational θ) :
    Tendsto (fun K => ∏ r ∈ Finset.range K, |Real.cos (π * (θ * b ^ r))|) atTop (𝓝 0) := by
  set P : ℕ → ℝ := fun K => ∏ r ∈ Finset.range K, |Real.cos (π * (θ * b ^ r))| with hP
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set q := Real.cos (π * (1 / (2 * b))) with hq
  have hδ0 : (0 : ℝ) ≤ 1 / (2 * b) := by positivity
  have hδ1 : 1 / (2 * (b : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq0 : 0 ≤ q := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hq1 : q < 1 := by
    have : 0 < 1 / (2 * (b : ℝ)) := by positivity
    calc q < Real.cos 0 := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
            (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      _ = 1 := Real.cos_zero
  have hP0 : ∀ K, 0 ≤ P K := fun K => Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hanti : ∀ K K', K ≤ K' → P K' ≤ P K := fun K K' h =>
    QuarterCantorDecay.prod_le_prod_sub (Finset.range_subset_range.2 h) _
      (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
  have hM : ∀ M : ℕ, ∃ K, P K ≤ q ^ M := by
    intro M
    induction M with
    | zero => exact ⟨0, by simp [hP]⟩
    | succ M ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨r, hr, hfar⟩ := exists_far hb hθ K
      refine ⟨r + 1, ?_⟩
      have hc : |Real.cos (π * (θ * b ^ r))| ≤ q := abs_cos_le_of_far hδ0 hfar
      calc P (r + 1) = P r * |Real.cos (π * (θ * b ^ r))| := Finset.prod_range_succ _ _
        _ ≤ q ^ M * q := mul_le_mul ((hanti K r hr).trans hK) hc (abs_nonneg _)
            (pow_nonneg hq0 _)
        _ = q ^ (M + 1) := (pow_succ _ _).symm
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun K => lt_of_lt_of_le ha (hP0 K), fun a ha => ?_⟩
  obtain ⟨M, hMa⟩ := exists_pow_lt_of_lt_one ha hq1
  obtain ⟨K, hK⟩ := hM M
  exact eventually_atTop.2 ⟨K, fun K' hK' => ((hanti K K' hK').trans hK).trans_lt hMa⟩

end CosProduct

/-! ### Conditional expectations of `e(θ b^n Y)` -/

section Weyl

variable {b : ℕ}

/-- The contribution of the first `m` digits to `bReal b ω`. -/
def partB (b m : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ i ∈ Finset.range m, (bDigits ω i : ℝ) / (b : ℝ) ^ (i + 1)

theorem bReal_splice (hb : 2 ≤ b) (m : ℕ) (ω η : ℕ → Bool) :
    bReal b (splice m ω η) = partB b m ω + bReal b η / (b : ℝ) ^ m := by
  unfold bReal realOfDigits
  rw [← (summable_bReal hb (splice m ω η)).sum_add_tsum_nat_add m, ← tsum_div_const]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [bDigits, splice, Finset.mem_range.1 hi]
  · refine tsum_congr fun i => ?_
    simp only [bDigits, splice, show ¬ (i + m < m) by omega, ite_false, Nat.add_sub_cancel]
    rw [div_div, ← pow_add, show i + 1 + m = i + m + 1 by omega]

theorem splice_shift (m : ℕ) (ω : ℕ → Bool) : splice m ω (fun i => ω (i + m)) = ω := by
  funext i
  unfold splice
  split_ifs with hi
  · rfl
  · change ω (i - m + m) = ω i
    rw [Nat.sub_add_cancel (not_lt.1 hi)]

/-- `e(θ b^n Y)`. -/
def wf (b : ℕ) (θ : ℝ) (n : ℕ) (ω : ℕ → Bool) : ℂ := ee (θ * (b : ℝ) ^ n * bReal b ω)

theorem measurable_wf (θ : ℝ) (n : ℕ) : Measurable (wf b θ n) :=
  measurable_ee.comp (measurable_bReal.const_mul _)

theorem norm_wf (θ : ℝ) (n : ℕ) (ω : ℕ → Bool) : ‖wf b θ n ω‖ = 1 := norm_ee _

theorem condE_wf (hb : 2 ≤ b) (θ : ℝ) (n m : ℕ) (ω : ℕ → Bool) :
    condE m (wf b θ n) ω =
      ee (θ * (b : ℝ) ^ n * partB b m ω) * cF b (θ * (b : ℝ) ^ n / (b : ℝ) ^ m) := by
  unfold condE wf cF bFourier
  rw [← integral_const_mul]
  congr 1; funext η
  rw [bReal_splice hb]
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  simp only [id]
  push_cast
  ring

theorem norm_condE_wf (hb : 2 ≤ b) (θ : ℝ) (n m : ℕ) (ω : ℕ → Bool) :
    ‖condE m (wf b θ n) ω‖ = ‖cF b (θ * (b : ℝ) ^ n / (b : ℝ) ^ m)‖ := by
  rw [condE_wf hb, norm_mul, norm_ee, one_mul]

/-- Forgetting the coins after `n + L` moves `e(θ b^n Y)` by at most `2π|θ| b^{-L}`. -/
theorem norm_wf_sub_condE_le (hb : 2 ≤ b) (θ : ℝ) (n L : ℕ) (ω : ℕ → Bool) :
    ‖wf b θ n ω - condE (n + L) (wf b θ n) ω‖ ≤ 2 * π * |θ| / (b : ℝ) ^ L := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have key : ∀ η, ‖wf b θ n ω - wf b θ n (splice (n + L) ω η)‖ ≤ 2 * π * |θ| / (b : ℝ) ^ L := by
    intro η
    unfold wf ee
    refine (QuarterCantorDecay.norm_cexp_sub_le _ _).trans ?_
    have h1 := bReal_splice hb (n + L) ω η
    have h2 := bReal_splice hb (n + L) ω (fun i => ω (i + (n + L)))
    rw [splice_shift] at h2
    rw [h1, h2]
    have hm1 := bReal_mem hb (fun i => ω (i + (n + L)))
    have hm2 := bReal_mem hb η
    set A := bReal b (fun i => ω (i + (n + L)))
    set B := bReal b η
    have : θ * (b : ℝ) ^ n * (partB b (n + L) ω + A / (b : ℝ) ^ (n + L)) -
        θ * (b : ℝ) ^ n * (partB b (n + L) ω + B / (b : ℝ) ^ (n + L)) =
        θ * (A - B) / (b : ℝ) ^ L := by
      rw [pow_add]; field_simp; ring
    rw [this, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) ^ L)]
    have hAB : |A - B| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [hm1.2, hm2.1], by linarith [hm1.1, hm2.2]⟩
    calc 2 * π * (|θ| * |A - B| / (b : ℝ) ^ L) ≤ 2 * π * (|θ| * 1 / (b : ℝ) ^ L) := by
          gcongr
      _ = 2 * π * |θ| / (b : ℝ) ^ L := by ring
  have hint : Integrable (fun η => wf b θ n (splice (n + L) ω η)) coinMeasure :=
    Integrable.of_bound ((measurable_wf θ n).comp ((measurable_splice (n + L)).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1
      (Eventually.of_forall fun η => (norm_wf θ n _).le)
  have : wf b θ n ω - condE (n + L) (wf b θ n) ω =
      ∫ η, (wf b θ n ω - wf b θ n (splice (n + L) ω η)) ∂coinMeasure := by
    rw [integral_sub (integrable_const _) hint, integral_const]
    simp [condE]
  rw [this]
  simpa using norm_integral_le_of_norm_le_const (μ := coinMeasure) (Eventually.of_forall key)

/-- `‖E_t e(θ b^{K+t} Y)‖ ≤ ∏_{r<K} |cos(π θ b^r)|`. -/
theorem norm_condE_wf_le_prod (hb : 2 ≤ b) (θ : ℝ) (K t : ℕ) (ω : ℕ → Bool) :
    ‖condE t (wf b θ (K + t)) ω‖ ≤ ∏ r ∈ Finset.range K, |Real.cos (π * (θ * b ^ r))| := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  rw [norm_condE_wf hb, show θ * (b : ℝ) ^ (K + t) / (b : ℝ) ^ t = θ * (b : ℝ) ^ K by
    rw [pow_add]; field_simp]
  refine (norm_cF_le_prod hb _ K).trans_eq ?_
  rw [← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk := Finset.mem_range.1 hk
  have : (b : ℝ) ^ K = b * (b : ℝ) ^ k * (b : ℝ) ^ (K - 1 - k) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [this]
  congr 2
  field_simp

end Weyl

/-- A sequence whose partial sums grow at most like `ε N + C` for every `ε > 0` has Cesàro
means tending to `0`. -/
theorem tendsto_avg_of_bound {z : ℕ → ℂ}
    (h : ∀ ε > 0, ∃ C : ℝ, ∀ N : ℕ, ‖∑ n ∈ Finset.range N, z n‖ ≤ ε * N + C) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, z n) / (N : ℂ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC⟩ := h (ε / 2) (by positivity)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * |C| / ε)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN' : 2 * |C| / ε < N := lt_of_lt_of_le hN0 (by exact_mod_cast (show N0 ≤ N by omega))
  rw [dist_zero_right, norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos]
  have : 2 * |C| < ε * N := by rw [div_lt_iff₀ hε] at hN'; linarith
  linarith [hC N, le_abs_self C]

/-! ### Almost sure normality of `θ Y` -/

section AlmostSure

variable {b : ℕ}

/-- The increments `(E_{t+i+1} - E_{t+i}) e(θ b^{K+t} Y) / 2`. -/
def incr (b : ℕ) (θ : ℝ) (K i t : ℕ) (ω : ℕ → Bool) : ℂ :=
  (condE (t + i + 1) (wf b θ (K + t)) ω - condE (t + i) (wf b θ (K + t)) ω) / 2

theorem norm_incr_le (θ : ℝ) (K i t : ℕ) (ω : ℕ → Bool) : ‖incr b θ K i t ω‖ ≤ 1 := by
  have hwb : ∀ n ω, ‖wf b θ n ω‖ ≤ 1 := fun n ω => (norm_wf θ n ω).le
  unfold incr
  rw [norm_div, Complex.norm_ofNat]
  have := norm_sub_le (condE (t + i + 1) (wf b θ (K + t)) ω) (condE (t + i) (wf b θ (K + t)) ω)
  have h1 := norm_condE_le (t + i + 1) (hwb (K + t)) ω
  have h2 := norm_condE_le (t + i) (hwb (K + t)) ω
  rw [div_le_one (by norm_num)]
  linarith

theorem ae_tendsto_incr (θ : ℝ) (K i : ℕ) :
    ∀ᵐ ω ∂coinMeasure, Tendsto
      (fun N : ℕ => (∑ t ∈ Finset.range N, incr b θ K i t ω) / (N : ℂ)) atTop (𝓝 0) := by
  have hwb : ∀ n ω, ‖wf b θ n ω‖ ≤ 1 := fun n ω => (norm_wf θ n ω).le
  have hm : ∀ t, Measurable (incr b θ K i t) := fun t =>
    ((measurable_condE _ (measurable_wf θ _)).sub
      (measurable_condE _ (measurable_wf θ _))).div_const _
  refine ae_tendsto_avg_of_orthogonal coinMeasure (fun t => incr b θ K i t) hm
    (fun t ω => norm_incr_le θ K i t ω) (fun t t' htt' => ?_)
  set φ : (ℕ → Bool) → ℂ := fun ω => conj (incr b θ K i t ω) / 2 with hφ
  have hφm : Measurable φ := (Complex.continuous_conj.measurable.comp (hm t)).div_const _
  have hφd : DepOn (t' + i) φ := by
    intro ω ω' h
    simp only [φ, incr]
    rw [(depOn_condE (t + i + 1) _).mono (by omega) ω ω' h,
      (depOn_condE (t + i) _).mono (by omega) ω ω' h]
  have hφb : ∀ ω, ‖φ ω‖ ≤ 1 := fun ω => by
    simp only [φ, norm_div, Complex.norm_conj, Complex.norm_ofNat]
    have := norm_incr_le (b := b) θ K i t ω
    linarith
  have h := integral_mul_condE_sub (m := t' + i) hφm hφd hφb (measurable_wf θ (K + t'))
    (hwb (K + t'))
  rw [← h]
  congr 1; funext ω
  simp only [φ, incr]
  ring

/-- **Weyl sums of `θ Y`**: for irrational `θ`, `N⁻¹ ∑_{n<N} e(θ b^n Y) → 0` almost surely. -/
theorem ae_tendsto_weyl (hb : 2 ≤ b) {θ : ℝ} (hθ : Irrational θ) :
    ∀ᵐ ω ∂coinMeasure, Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, wf b θ n ω) / (N : ℂ)) atTop (𝓝 0) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have key : ∀ j : ℕ, ∀ᵐ ω ∂coinMeasure, ∃ C : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, wf b θ n ω‖ ≤ (1 / ((j : ℝ) + 1)) * N + C := by
    intro j
    set ε : ℝ := 1 / ((j : ℝ) + 1) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨K, hK⟩ := ((tendsto_prod_cos hb hθ).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).exists
    have hLt : Tendsto (fun L : ℕ => 2 * π * |θ| / (b : ℝ) ^ L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hb1)
    obtain ⟨L, hL⟩ := (hLt.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).exists
    have hall : ∀ᵐ ω ∂coinMeasure, ∀ i : ℕ, Tendsto
        (fun N : ℕ => (∑ t ∈ Finset.range N, incr b θ K i t ω) / (N : ℂ)) atTop (𝓝 0) :=
      ae_all_iff.2 fun i => ae_tendsto_incr θ K i
    filter_upwards [hall] with ω hω
    have hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (K + L),
        ‖(∑ t ∈ Finset.range N, incr b θ K i t ω) / (N : ℂ)‖) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.range (K + L)) fun i _ => (hω i).norm
    obtain ⟨M0, hM0⟩ := eventually_atTop.1
      (hsum.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 6 by positivity)))
    set C1 : ℝ := 2 * ((K + L : ℕ) : ℝ) * (M0 : ℝ) with hC1def
    have hC1 : 0 ≤ C1 := by positivity
    have hZ : ∀ M : ℕ, 2 * ∑ i ∈ Finset.range (K + L),
        ‖∑ t ∈ Finset.range M, incr b θ K i t ω‖ ≤ ε / 3 * M + C1 := by
      intro M
      by_cases hM : M0 ≤ M ∧ 0 < M
      · have h := hM0 M hM.1
        have hMpos : (0 : ℝ) < M := by exact_mod_cast hM.2
        have : ∑ i ∈ Finset.range (K + L), ‖∑ t ∈ Finset.range M, incr b θ K i t ω‖ =
            M * ∑ i ∈ Finset.range (K + L),
              ‖(∑ t ∈ Finset.range M, incr b θ K i t ω) / (M : ℂ)‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_div, Complex.norm_natCast]
          field_simp
        rw [this]
        nlinarith
      · have hMM : M ≤ M0 := by
          by_contra hc
          exact hM ⟨by omega, by omega⟩
        have hb' : ∀ i, ‖∑ t ∈ Finset.range M, incr b θ K i t ω‖ ≤ M0 := fun i =>
          ((norm_sum_le _ _).trans (by
            simpa using Finset.sum_le_sum fun t (_ : t ∈ Finset.range M) =>
              norm_incr_le (b := b) θ K i t ω)).trans (by exact_mod_cast hMM)
        have : ∑ i ∈ Finset.range (K + L), ‖∑ t ∈ Finset.range M, incr b θ K i t ω‖ ≤
            ((K + L : ℕ) : ℝ) * M0 := by
          simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.range (K + L)) => hb' i
        have : 0 ≤ ε / 3 * M := by positivity
        rw [hC1def]
        nlinarith
    have hshift : ∀ M : ℕ, ‖∑ t ∈ Finset.range M, wf b θ (K + t) ω‖ ≤ ε * M + C1 := by
      intro M
      have hdec : ∀ t, wf b θ (K + t) ω =
          (wf b θ (K + t) ω - condE (K + t + L) (wf b θ (K + t)) ω) +
            2 * ∑ i ∈ Finset.range (K + L), incr b θ K i t ω + condE t (wf b θ (K + t)) ω := by
        intro t
        have htel : ∑ i ∈ Finset.range (K + L), incr b θ K i t ω =
            (condE (t + (K + L)) (wf b θ (K + t)) ω - condE t (wf b θ (K + t)) ω) / 2 := by
          simp only [incr, ← Finset.sum_div]
          congr 1
          exact Finset.sum_range_sub (fun i => condE (t + i) (wf b θ (K + t)) ω) (K + L)
        rw [htel, show t + (K + L) = K + t + L by omega]
        ring
      rw [Finset.sum_congr rfl fun t _ => hdec t, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_comm]
      have h1 : ‖∑ t ∈ Finset.range M,
          (wf b θ (K + t) ω - condE (K + t + L) (wf b θ (K + t)) ω)‖ ≤ ε / 3 * M := by
        refine (norm_sum_le _ _).trans ?_
        have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range M) =>
          (norm_wf_sub_condE_le hb θ (K + t) L ω).trans hL.le
        simpa [mul_comm] using this
      have h3 : ‖∑ t ∈ Finset.range M, condE t (wf b θ (K + t)) ω‖ ≤ ε / 3 * M := by
        refine (norm_sum_le _ _).trans ?_
        have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range M) =>
          (norm_condE_wf_le_prod hb θ K t ω).trans hK.le
        simpa [mul_comm] using this
      have h2 : ‖2 * ∑ i ∈ Finset.range (K + L), ∑ t ∈ Finset.range M, incr b θ K i t ω‖ ≤
          ε / 3 * M + C1 := by
        rw [norm_mul, Complex.norm_ofNat]
        refine le_trans ?_ (hZ M)
        gcongr
        exact norm_sum_le _ _
      refine (norm_add_le _ _).trans ?_
      have := norm_add_le
        (∑ t ∈ Finset.range M, (wf b θ (K + t) ω - condE (K + t + L) (wf b θ (K + t)) ω))
        (2 * ∑ i ∈ Finset.range (K + L), ∑ t ∈ Finset.range M, incr b θ K i t ω)
      linarith [h1, h2, h3]
    refine ⟨C1 + K, fun N => ?_⟩
    have hεN : 0 ≤ ε * N := by positivity
    rcases le_or_gt N K with hNK | hNK
    · have : ‖∑ n ∈ Finset.range N, wf b θ n ω‖ ≤ N := (norm_sum_le _ _).trans (by
        simpa using Finset.sum_le_sum fun n (_ : n ∈ Finset.range N) => (norm_wf θ n ω).le)
      have : (N : ℝ) ≤ K := by exact_mod_cast hNK
      linarith
    · obtain ⟨M, rfl⟩ : ∃ M, N = K + M := ⟨N - K, by omega⟩
      rw [Finset.sum_range_add]
      have hK' : ‖∑ n ∈ Finset.range K, wf b θ n ω‖ ≤ K := (norm_sum_le _ _).trans (by
        simpa using Finset.sum_le_sum fun n (_ : n ∈ Finset.range K) => (norm_wf θ n ω).le)
      have hMN : ε * M ≤ ε * ((K + M : ℕ) : ℝ) := by gcongr; exact_mod_cast Nat.le_add_left M K
      linarith [norm_add_le (∑ n ∈ Finset.range K, wf b θ n ω)
        (∑ t ∈ Finset.range M, wf b θ (K + t) ω), hshift M]
  filter_upwards [ae_all_iff.2 key] with ω hω
  refine tendsto_avg_of_bound fun ε hε => ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨C, hC⟩ := hω j
  exact ⟨C, fun N => (hC N).trans (by gcongr)⟩

/-- **`θ Y` is normal for almost every Cantor point** `Y`, for irrational `θ`. -/
theorem ae_isNormal_mul_bReal (hb : 2 ≤ b) {θ : ℝ} (hθ : Irrational θ) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (θ * bReal b ω) := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * (θ * bReal b ω))) / (N : ℂ)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Eventually.of_forall fun ω hne => absurd hh hne
    · filter_upwards [ae_tendsto_weyl hb (hθ.intCast_mul hh)] with ω hω _
      refine hω.congr fun N => ?_
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold wf
      congr 1
      ring
  filter_upwards [hall] with ω hω
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  refine (hω h hh).congr fun N => ?_
  rw [LevinSparse.fourierMean_orbit]

end AlmostSure

end NormalNumbers.MulRigidity

namespace Real

open NormalNumbers NormalNumbers.MulRigidity NormalNumbers.BaseCantorDecay

/-- **Multiplication by an irrational breaks normality**: for every base `b ≥ 2` and irrational
`γ`, some base-`b` normal `x` has `γ x` not normal in base `b`. -/
theorem exists_isNormalIn_not_isNormalIn_mul {b : ℕ} (hb : 2 ≤ b) {γ : ℝ} (hγ : Irrational γ) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn b (γ * x) := by
  have hB : 2 ≤ b ^ 2 := by nlinarith
  have hB3 : 3 ≤ b ^ 2 := by nlinarith
  obtain ⟨ω, hω⟩ := (ae_isNormal_mul_bReal hB hγ.inv).exists
  refine ⟨γ⁻¹ * bReal (b ^ 2) ω, ((isNormalIn_iff_isNormal _ _).2 hω).of_pow hb two_pos, ?_⟩
  rw [← mul_assoc, mul_inv_cancel₀ hγ.ne_zero, one_mul]
  exact fun h => not_isNormal_bReal hB3 ω ((isNormalIn_iff_isNormal _ _).1 (h.pow hb two_pos))

/-- **Multiplicative rigidity in a fixed base** (Dayan–Ganguly–Weiss; Manai, arXiv:2609.24665):
multiplication by `α` preserves base-`b` normality (`b ≥ 2`) if and only if `α` is a nonzero
rational. -/
theorem preserves_isNormalIn_mul_iff {b : ℕ} (hb : 2 ≤ b) {α : ℝ} :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn b (α * x)) ↔ ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) = α := by
  constructor
  · intro h
    by_cases hirr : Irrational α
    · obtain ⟨x, hx, hx'⟩ := exists_isNormalIn_not_isNormalIn_mul hb hirr
      exact absurd (h x hx) hx'
    · obtain ⟨q, rfl⟩ : ∃ q : ℚ, (q : ℝ) = α := not_not.1 hirr
      refine ⟨q, fun hq => ?_, rfl⟩
      obtain ⟨x, hx⟩ := exists_isAbsolutelyNormal
      have := (h x (hx b hb)).irrational hb
      simp [hq] at this
  · rintro ⟨q, hq, rfl⟩ x hx
    simpa using (isNormalIn_mul_add_ratCast_iff hb hq 0).2 hx

end Real
