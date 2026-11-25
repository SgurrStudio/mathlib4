/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.Normal.Basic
public import Mathlib.Probability.StrongLaw

import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Borel's normal number theorem

We prove **Borel's normal number theorem** (É. Borel, 1909): Lebesgue-almost every real number is
absolutely normal. In particular absolutely normal numbers exist.

## Strategy

1. Under the uniform probability measure on `[0, 1)`, the events `{x | digit b x n = a}`
   (`n : ℕ`) are mutually independent and each has probability `1 / b`
   (`Real.iIndepSet_digit_eq`, `Real.volume_restrict_digit_eq`). This is a counting argument:
   the first `n` digits of `x` are determined by `⌊x * b ^ n⌋₊`, which is uniformly distributed
   on `{0, …, b ^ n - 1}`.
2. The strong law of large numbers applied to the indicators of these events shows that almost
   every `x ∈ [0, 1)` is simply normal in base `b`; since digits are invariant under integer
   translation this holds almost everywhere on `ℝ` (`Real.ae_isSimplyNormalIn`).
3. Splitting the positions `i` according to `i mod k`, a block of `k` base-`b` digits of `x`
   starting at position `r + m * k` is a single base-`b ^ k` digit of `x * b ^ r`. Hence if
   `x * b ^ r` is simply normal in base `b ^ k` for all `0 ≤ r < k`, then every block of length `k`
   has frequency `b⁻ᵏ` in base `b` (`Real.isNormalIn_of_isSimplyNormalIn_pow`).
4. Multiplication by `b ^ r` preserves null sets, and there are countably many bases, which gives
   `Real.ae_isAbsolutelyNormal`.

## References

* [É. Borel, *Les probabilités dénombrables et leurs applications arithmétiques*][Borel1909]
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Real

variable {b k : ℕ} {x : ℝ}

@[simp]
theorem isSimplyNormalIn_add_intCast_iff (m : ℤ) :
    IsSimplyNormalIn b (x + m) ↔ IsSimplyNormalIn b x := by
  simp [IsSimplyNormalIn]

@[fun_prop]
theorem measurable_digit (b n : ℕ) : Measurable fun x : ℝ ↦ digit b x n :=
  (measurable_from_top (f := fun z : ℤ ↦ (z % (b : ℤ)).toNat)).comp
    (Int.measurable_floor.comp (measurable_id.mul_const _))

/-- For `x ∈ [0, 1)`, the first `n` digits of `x` are the base-`b` digits of `⌊x * b ^ n⌋₊`. -/
theorem digit_eq_floor_div_mod (hb : 0 < b) (hx : x ∈ Ico (0 : ℝ) 1) {i n : ℕ} (hin : i < n) :
    digit b x i = ⌊x * (b : ℝ) ^ n⌋₊ / b ^ (n - 1 - i) % b := by
  have h0 : 0 ≤ x * (b : ℝ) ^ (i + 1) := mul_nonneg hx.1 (by positivity)
  have hn : n = (i + 1) + (n - 1 - i) := by omega
  have key : x * (b : ℝ) ^ (i + 1) = x * (b : ℝ) ^ n / ((b ^ (n - 1 - i) : ℕ) : ℝ) := by
    rw [Nat.cast_pow, eq_div_iff (by positivity), mul_assoc, ← pow_add, ← hn]
  rw [digit, ← Int.natCast_floor_eq_floor h0, ← Int.natCast_mod, Int.toNat_natCast, key,
    Nat.floor_div_natCast]

/-- Counting the integers `c < b ^ n` whose base-`b` digits satisfy prescribed constraints. -/
theorem card_filter_range_pow (hb : 0 < b) (n : ℕ) (P : ℕ → ℕ → Prop)
    [∀ i, DecidablePred (P i)] :
    ((Finset.range (b ^ n)).filter fun c ↦ ∀ i < n, P i (c / b ^ i % b)).card =
      ∏ i ∈ Finset.range n, ((Finset.range b).filter (P i)).card := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ', ← ih (fun i ↦ P (i + 1)), ← Finset.card_product]
    refine Finset.card_nbij' (fun c ↦ (c / b, c % b)) (fun p ↦ p.2 + b * p.1) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_range, mem_ofPred_eq] at hc
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_range, mem_prod,
        mem_ofPred_eq]
      refine ⟨⟨Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact hc.1), fun i hi ↦ ?_⟩,
        Nat.mod_lt _ hb, by simpa using hc.2 0 (by omega)⟩
      have := hc.2 (i + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this
    · rintro ⟨c, e⟩ hp
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_range, mem_prod,
        mem_ofPred_eq] at hp
      simp only [Finset.coe_filter, Finset.mem_range, mem_ofPred_eq]
      refine ⟨?_, fun i hi ↦ ?_⟩
      · calc e + b * c < b + b * c := by omega
          _ = b * (c + 1) := by ring
          _ ≤ b * b ^ n := Nat.mul_le_mul_left _ hp.1.1
          _ = b ^ (n + 1) := (pow_succ' _ _).symm
      · rcases i with _ | i
        · simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.2.1] using hp.2.2
        · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
            Nat.div_eq_of_lt hp.2.1, zero_add]
          exact hp.1.2 i (by omega)
    · intro c _
      exact Nat.mod_add_div c b
    · rintro ⟨c, e⟩ hp
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_range, mem_prod,
        mem_ofPred_eq] at hp
      simp [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hp.2.1, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hp.2.1]

/-- Under the uniform measure on `[0, 1)`, `⌊x * b ^ n⌋₊` is uniformly distributed on
`{0, …, b ^ n - 1}`. -/
theorem volume_restrict_floor_mul_pow_eq (hb : 0 < b) (n : ℕ) {c : ℕ} (hc : c < b ^ n) :
    volume.restrict (Ico (0 : ℝ) 1) {x | ⌊x * (b : ℝ) ^ n⌋₊ = c} = ((b : ℝ≥0∞) ^ n)⁻¹ := by
  have hB : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hc' : (c : ℝ) + 1 ≤ (b : ℝ) ^ n := by exact_mod_cast hc
  have hset : {x : ℝ | ⌊x * (b : ℝ) ^ n⌋₊ = c} ∩ Ico 0 1 =
      Ico ((c : ℝ) / (b : ℝ) ^ n) (((c : ℝ) + 1) / (b : ℝ) ^ n) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ico]
    constructor
    · rintro ⟨h, h0, -⟩
      rw [Nat.floor_eq_iff (mul_nonneg h0 hB.le)] at h
      exact ⟨(div_le_iff₀ hB).2 h.1, (lt_div_iff₀ hB).2 h.2⟩
    · rintro ⟨h0, h1⟩
      rw [div_le_iff₀ hB] at h0
      rw [lt_div_iff₀ hB] at h1
      have hx0 : 0 ≤ x * (b : ℝ) ^ n := (Nat.cast_nonneg c).trans h0
      refine ⟨(Nat.floor_eq_iff hx0).2 ⟨h0, h1⟩, nonneg_of_mul_nonneg_left hx0 hB, ?_⟩
      nlinarith
  rw [Measure.restrict_apply' measurableSet_Ico, hset, Real.volume_Ico, ← sub_div,
    add_sub_cancel_left, one_div, ENNReal.ofReal_inv_of_pos hB, ← Nat.cast_pow,
    ENNReal.ofReal_natCast, Nat.cast_pow]

/-- Under the uniform measure on `[0, 1)`, the probability that the digits at all positions
`i ∈ S` equal `a` is `b ^ (-#S)`. -/
theorem volume_restrict_biInter_digit_eq (hb : 0 < b) {a : ℕ} (ha : a < b) (S : Finset ℕ) :
    volume.restrict (Ico (0 : ℝ) 1) (⋂ i ∈ S, {x | digit b x i = a}) =
      ((b : ℝ≥0∞) ^ S.card)⁻¹ := by
  classical
  set n := S.sup id + 1 with hn_def
  have hS : ∀ i ∈ S, i < n := fun i hi ↦ Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have hSn : S ⊆ Finset.range n := fun i hi ↦ Finset.mem_range.2 (hS i hi)
  set G := (Finset.range (b ^ n)).filter fun c ↦ ∀ i < n, (n - 1 - i ∈ S → c / b ^ i % b = a)
  have hset : (⋂ i ∈ S, {x : ℝ | digit b x i = a}) ∩ Ico 0 1 =
      (⋃ c ∈ G, {x : ℝ | ⌊x * (b : ℝ) ^ n⌋₊ = c}) ∩ Ico 0 1 := by
    ext x
    by_cases hx : x ∈ Ico (0 : ℝ) 1
    · have hlt : ⌊x * (b : ℝ) ^ n⌋₊ < b ^ n := by
        rw [Nat.floor_lt (mul_nonneg hx.1 (by positivity))]
        push_cast
        exact mul_lt_of_lt_one_left (by positivity) hx.2
      simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_iUnion, hx, and_true,
        exists_prop, exists_eq_right', G, Finset.mem_filter, Finset.mem_range, hlt, true_and]
      constructor
      · intro h j hj hjS
        have := h _ hjS
        rwa [digit_eq_floor_div_mod (i := n - 1 - j) (n := n) hb hx (by omega),
          show n - 1 - (n - 1 - j) = j by omega] at this
      · intro h i hi
        rw [digit_eq_floor_div_mod hb hx (hS i hi)]
        exact h _ (by have := hS i hi; omega) (by rwa [show n - 1 - (n - 1 - i) = i by
          have := hS i hi; omega])
    · simp [hx]
  have hmeas : ∀ c : ℕ, MeasurableSet {x : ℝ | ⌊x * (b : ℝ) ^ n⌋₊ = c} := fun c ↦
    (Nat.measurable_floor.comp (measurable_id.mul_const _)) (measurableSet_singleton c)
  rw [Measure.restrict_apply' measurableSet_Ico, hset, ← Measure.restrict_apply' measurableSet_Ico,
    measure_biUnion_finset _ (fun c _ ↦ hmeas c)]
  swap
  · intro c _ c' _ hcc'
    exact Set.disjoint_left.2 fun x hx hx' ↦ hcc' (hx.symm.trans hx')
  rw [Finset.sum_congr rfl fun c hc ↦ volume_restrict_floor_mul_pow_eq hb n
    (Finset.mem_range.1 (Finset.mem_filter.1 hc).1), Finset.sum_const]
  have hG : G.card = b ^ (n - S.card) := by
    rw [card_filter_range_pow hb n (fun i d ↦ n - 1 - i ∈ S → d = a)]
    have : ∀ i, ((Finset.range b).filter fun d ↦ n - 1 - i ∈ S → d = a).card =
        if n - 1 - i ∈ S then 1 else b := by
      intro i
      split_ifs with h
      · simp [h, Finset.filter_eq', ha]
      · simp [h]
    simp_rw [this]
    rw [Finset.prod_range_reflect (fun i ↦ if i ∈ S then 1 else b) n, Finset.prod_ite,
      Finset.prod_const_one, one_mul, Finset.prod_const, ← Finset.sdiff_eq_filter,
      Finset.card_sdiff_of_subset hSn, Finset.card_range]
  have hcard : S.card ≤ n := by simpa using Finset.card_le_card hSn
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb.ne'
  have hpow : (b : ℝ≥0∞) ^ n = (b : ℝ≥0∞) ^ (n - S.card) * (b : ℝ≥0∞) ^ S.card := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  rw [hG, nsmul_eq_mul, Nat.cast_pow, hpow, ENNReal.mul_inv (Or.inl (pow_ne_zero _ hb0))
      (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top b))), ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ hb0) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top b)),
    one_mul]

/-- Under the uniform measure on `[0, 1)`, each base-`b` digit takes each value `a < b` with
probability `1 / b`. -/
theorem volume_restrict_digit_eq (hb : 0 < b) (n : ℕ) {a : ℕ} (ha : a < b) :
    volume.restrict (Ico (0 : ℝ) 1) {x | digit b x n = a} = (b : ℝ≥0∞)⁻¹ := by
  simpa using volume_restrict_biInter_digit_eq hb ha {n}

instance : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) :=
  ⟨by simp [Measure.restrict_apply MeasurableSet.univ]⟩

/-- Under the uniform measure on `[0, 1)`, the events "the `n`-th digit is `a`" are mutually
independent. -/
theorem iIndepSet_digit_eq (hb : 0 < b) {a : ℕ} (ha : a < b) :
    iIndepSet (fun n ↦ {x : ℝ | digit b x n = a}) (volume.restrict (Ico (0 : ℝ) 1)) := by
  rw [iIndepSet_iff_meas_biInter fun n ↦ show MeasurableSet {x : ℝ | digit b x n = a} from
    measurable_digit b n (measurableSet_singleton a)]
  intro S
  rw [volume_restrict_biInter_digit_eq hb ha S,
    Finset.prod_congr rfl fun n _ ↦ volume_restrict_digit_eq hb n ha, Finset.prod_const,
    ENNReal.inv_pow]

/-- A property of real numbers that is invariant under integer translations and holds almost
everywhere on `[0, 1)` holds almost everywhere. -/
theorem ae_of_ae_restrict_Ico {p : ℝ → Prop} (hp : ∀ x (m : ℤ), p (x + m) ↔ p x)
    (h : ∀ᵐ x ∂(volume.restrict (Ico (0 : ℝ) 1)), p x) : ∀ᵐ x : ℝ, p x := by
  rw [ae_restrict_iff' measurableSet_Ico, ae_iff] at h
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ m : ℤ, (fun y ↦ y + (-m : ℝ)) ⁻¹'
    {x | ¬(x ∈ Ico (0 : ℝ) 1 → p x)}) ?_
    (measure_iUnion_null fun m ↦ by rw [measure_preimage_add_right]; exact h)
  intro x hx
  simp only [mem_iUnion, mem_preimage, mem_ofPred_eq, not_imp]
  refine ⟨⌊x⌋, ?_, fun hpx ↦ hx ?_⟩
  · rw [← sub_eq_add_neg]
    exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  · have := (hp (x + -⌊x⌋) ⌊x⌋).2 hpx
    simpa using this

/-- The strong law of large numbers for the digits of `x ∈ [0, 1)`. -/
theorem ae_restrict_tendsto_blockCount_one (hb : 0 < b) (d : Fin b) :
    ∀ᵐ x ∂(volume.restrict (Ico (0 : ℝ) 1)),
      Tendsto (fun N : ℕ ↦ (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N) atTop
        (𝓝 (b : ℝ)⁻¹) := by
  set μ := volume.restrict (Ico (0 : ℝ) 1)
  set A : ℕ → Set ℝ := fun n ↦ {x | digit b x n = d}
  set X : ℕ → ℝ → ℝ := fun n ↦ (A n).indicator fun _ ↦ 1
  have hA : ∀ n, MeasurableSet (A n) := fun n ↦
    measurable_digit b n (measurableSet_singleton _)
  have hind : iIndepFun X μ := (iIndepSet_digit_eq hb d.isLt).iIndepFun_indicator
  -- the digits are identically distributed
  have hdig : ∀ n, IdentDistrib (fun x ↦ digit b x n) (fun x ↦ digit b x 0) μ μ := by
    intro n
    refine ⟨(measurable_digit b n).aemeasurable, (measurable_digit b 0).aemeasurable,
      Measure.ext_of_singleton fun c ↦ ?_⟩
    rw [Measure.map_apply (measurable_digit b n) (measurableSet_singleton c),
      Measure.map_apply (measurable_digit b 0) (measurableSet_singleton c)]
    by_cases hc : c < b
    · exact (volume_restrict_digit_eq hb n hc).trans (volume_restrict_digit_eq hb 0 hc).symm
    · have : ∀ m, (fun x ↦ digit b x m) ⁻¹' {c} = ∅ := fun m ↦ by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        exact fun h ↦ hc (h ▸ digit_lt hb x m)
      rw [this, this]
  have hX : ∀ n, X n = ({(d : ℕ)} : Set ℕ).indicator (fun _ ↦ (1 : ℝ)) ∘
      fun x ↦ digit b x n := by
    intro n
    ext x
    simp only [X, A, Set.indicator, Function.comp_apply, mem_ofPred_eq, mem_singleton_iff]
    by_cases h : digit b x n = (d : ℕ) <;> simp [h]
  have hident : ∀ n, IdentDistrib (X n) (X 0) μ μ := fun n ↦ by
    rw [hX n, hX 0]
    exact (hdig n).comp (measurable_from_top)
  have hint : Integrable (X 0) μ := (integrable_const (1 : ℝ)).indicator (hA 0)
  have hmean : μ[X 0] = (b : ℝ)⁻¹ := by
    rw [show X 0 = (A 0).indicator 1 from rfl, integral_indicator_one (hA 0), measureReal_def,
      volume_restrict_digit_eq hb 0 d.isLt, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have := strong_law_ae_real X hint (fun i j hij ↦ hind.indepFun hij) hident
  rw [hmean] at this
  filter_upwards [this] with x hx
  convert hx using 3 with N
  classical
  simp only [blockCount, Fin.forall_fin_one, Fin.val_zero, add_zero, X, A, Set.indicator,
    mem_ofPred_eq]
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs <;> simp_all

/-- **Borel's theorem on simply normal numbers**: almost every real number is simply normal in
base `b`. -/
theorem ae_isSimplyNormalIn (hb : 0 < b) : ∀ᵐ x : ℝ, IsSimplyNormalIn b x := by
  simp only [IsSimplyNormalIn]
  rw [ae_all_iff]
  intro d
  refine ae_of_ae_restrict_Ico (p := fun x ↦ Tendsto (fun N : ℕ ↦
    (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N) atTop (𝓝 (b : ℝ)⁻¹)) (fun x m ↦ ?_)
    (ae_restrict_tendsto_blockCount_one hb d)
  simp only [blockCount_add_intCast]

theorem digit_eq_floor_mod (hx : 0 ≤ x) (n : ℕ) : digit b x n = ⌊x * (b : ℝ) ^ (n + 1)⌋₊ % b := by
  rw [digit, ← Int.natCast_floor_eq_floor (by positivity), ← Int.natCast_mod, Int.toNat_natCast]

/-- The base-`b ^ k` digit encoding a block `w` of `k` base-`b` digits (most significant first). -/
def blockCode {k : ℕ} (w : Fin k → Fin b) : Fin (b ^ k) :=
  finFunctionFinEquiv (w ∘ Fin.rev)

/-- The base-`b` digits of `F` at positions `k - 1, …, 0` (most significant first) form the
word `w` iff `F ≡ blockCode w [MOD b ^ k]`. -/
theorem forall_div_pow_mod_eq_iff {k : ℕ} (hb : 0 < b) (F : ℕ) (w : Fin k → Fin b) :
    (∀ j : Fin k, F / b ^ (k - 1 - j) % b = w j) ↔ F % b ^ k = blockCode w := by
  have hlt : F % b ^ k < b ^ k := Nat.mod_lt _ (pow_pos hb k)
  have hkey : ∀ e < k, F / b ^ e % b = F % b ^ k / b ^ e % b := fun e he ↦ by
    rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
    rw [← pow_succ]
    exact pow_dvd_pow b he
  rw [blockCode, ← Fin.val_mk hlt, Fin.val_inj, ← Equiv.symm_apply_eq]
  constructor
  · intro h
    funext i
    apply Fin.ext
    have := h (Fin.rev i)
    rw [Fin.val_rev, hkey _ (by omega), show k - 1 - (k - (i + 1)) = (i : ℕ) by omega] at this
    change F % b ^ k / b ^ (i : ℕ) % b = (w (Fin.rev i) : ℕ)
    exact this
  · intro h j
    have := congrArg Fin.val (congrFun h (Fin.rev j))
    change F % b ^ k / b ^ ((Fin.rev j : Fin k) : ℕ) % b = (w (Fin.rev (Fin.rev j)) : ℕ) at this
    rw [Fin.rev_rev, Fin.val_rev] at this
    rw [hkey _ (by omega), ← this, show k - 1 - (j : ℕ) = k - (j + 1) by omega]

/-- A block of `k` base-`b` digits of `x` starting at position `r + m * k` is the `m`-th
base-`b ^ k` digit of `x * b ^ r`. -/
theorem forall_digit_eq_iff_digit_pow {k : ℕ} (hb : 0 < b) (w : Fin k → Fin b) (r m : ℕ) :
    (∀ j : Fin k, digit b x (r + m * k + j) = w j) ↔
      digit (b ^ k) (x * (b : ℝ) ^ r) m = blockCode w := by
  -- reduce to `0 ≤ x`
  wlog hx : 0 ≤ x generalizing x
  · have h := this (x := Int.fract x) (Int.fract_nonneg x)
    have e : Int.fract x * (b : ℝ) ^ r = x * (b : ℝ) ^ r + ((-⌊x⌋ * (b : ℤ) ^ r : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    simp only [digit_fract] at h
    rwa [e, digit_add_intCast] at h
  set F := ⌊x * (b : ℝ) ^ (r + m * k + k)⌋₊ with hF
  have hdig : ∀ j : Fin k, digit b x (r + m * k + j) = F / b ^ (k - 1 - j) % b := by
    intro j
    rw [digit_eq_floor_mod hx, ← Nat.floor_div_natCast]
    congr 2
    rw [Nat.cast_pow, eq_div_iff (by positivity), mul_assoc, ← pow_add]
    congr 2
    omega
  have hdigk : digit (b ^ k) (x * (b : ℝ) ^ r) m = F % b ^ k := by
    rw [digit_eq_floor_mod (by positivity), Nat.cast_pow, mul_assoc, ← pow_mul, ← pow_add, hF]
    congr 4
    ring
  rw [hdigk]
  simp_rw [hdig]
  exact forall_div_pow_mod_eq_iff hb F w

/-- Splitting positions according to their residue modulo `k`. -/
theorem blockCount_eq_sum {k : ℕ} (hk : 0 < k) (hb : 0 < b) (w : Fin k → Fin b) (N : ℕ) :
    blockCount b x w N = ∑ r ∈ Finset.range k, blockCount (b ^ k) (x * (b : ℝ) ^ r)
      (fun _ : Fin 1 ↦ blockCode w) ((N + (k - 1 - r)) / k) := by
  classical
  rw [blockCount, Finset.card_eq_sum_card_fiberwise (f := (· % k)) (t := Finset.range k)
    (fun i _ ↦ Finset.mem_range.2 (Nat.mod_lt i hk))]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [Finset.mem_range] at hr
  rw [blockCount]
  refine Finset.card_nbij' (fun i ↦ i / k) (fun m ↦ r + m * k) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, mem_ofPred_eq] at hi
    obtain ⟨⟨hiN, hblk⟩, hir⟩ := hi
    have hdiv : i % k + i / k * k = i := by rw [mul_comm]; exact Nat.mod_add_div i k
    simp only [Finset.coe_filter, Finset.mem_range, mem_ofPred_eq, Fin.forall_fin_one,
      Fin.val_zero, add_zero]
    refine ⟨?_, ?_⟩
    · rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hk, add_mul, one_mul]
      omega
    · rw [← forall_digit_eq_iff_digit_pow hb, ← hir, hdiv]
      exact hblk
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_range, mem_ofPred_eq, Fin.forall_fin_one,
      Fin.val_zero, add_zero] at hm
    obtain ⟨hmN, hblk⟩ := hm
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hk, add_mul, one_mul] at hmN
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, mem_ofPred_eq]
    refine ⟨⟨by omega, (forall_digit_eq_iff_digit_pow hb w r m).2 hblk⟩, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range,
      mem_ofPred_eq] at hi
    obtain ⟨-, rfl⟩ := hi
    simp only
    rw [mul_comm]
    exact Nat.mod_add_div i k
  · intro m _
    simp only
    rw [Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hr, zero_add]

theorem tendsto_div_natCast_div (hk : 0 < k) (a : ℕ) :
    Tendsto (fun N : ℕ ↦ (((N + a) / k : ℕ) : ℝ) / N) atTop (𝓝 (k : ℝ)⁻¹) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hlow : Tendsto (fun N : ℕ ↦ (k : ℝ)⁻¹ - 1 * (1 / (N : ℝ))) atTop
      (𝓝 ((k : ℝ)⁻¹ - 1 * 0)) :=
    tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat.const_mul 1)
  have hup : Tendsto (fun N : ℕ ↦ (k : ℝ)⁻¹ + (a / k : ℝ) * (1 / (N : ℝ))) atTop
      (𝓝 ((k : ℝ)⁻¹ + (a / k : ℝ) * 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul _)
  rw [mul_zero, sub_zero] at hlow
  rw [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((N + a : ℕ) : ℝ) / k - 1 < (((N + a) / k : ℕ) : ℝ) := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.sub_one_lt_floor _
    push_cast at h1
    rw [le_div_iff₀ hN']
    have h2 : (N : ℝ) / k ≤ ((N : ℝ) + a) / k :=
      div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]) hk'.le
    have h3 : ((k : ℝ)⁻¹ - 1 * (1 / (N : ℝ))) * N = N / k - 1 := by field_simp
    rw [h3]
    linarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : (((N + a) / k : ℕ) : ℝ) ≤ ((N + a : ℕ) : ℝ) / k := Nat.cast_div_le
    push_cast at h1
    rw [div_le_iff₀ hN']
    calc (((N + a) / k : ℕ) : ℝ) ≤ ((N : ℝ) + a) / k := h1
      _ = ((k : ℝ)⁻¹ + (a / k : ℝ) * (1 / (N : ℝ))) * N := by field_simp

/-- If `x * b ^ r` is simply normal in base `b ^ k` for all `0 ≤ r < k`, for every `k ≥ 1`, then
`x` is normal in base `b`. -/
theorem isNormalIn_of_isSimplyNormalIn_pow (hb : 0 < b)
    (h : ∀ k, 0 < k → ∀ r < k, IsSimplyNormalIn (b ^ k) (x * (b : ℝ) ^ r)) :
    IsNormalIn b x := by
  intro k w
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · classical
    have : ∀ N, blockCount b x w N = N := fun N ↦ by simp [blockCount]
    simp only [this, pow_zero, inv_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [div_self (by exact_mod_cast hN.ne')]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  set M : ℕ → ℕ → ℕ := fun r N ↦ (N + (k - 1 - r)) / k
  have hterm : ∀ r < k, Tendsto (fun N : ℕ ↦ (blockCount (b ^ k) (x * (b : ℝ) ^ r)
      (fun _ : Fin 1 ↦ blockCode w) (M r N) : ℝ) / N) atTop (𝓝 (((b : ℝ) ^ k)⁻¹ * (k : ℝ)⁻¹)) := by
    intro r hr
    have hM : Tendsto (M r) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun A ↦ ⟨A * k, fun N hN ↦ ?_⟩
      rw [Nat.le_div_iff_mul_le hk]
      omega
    have h1 := ((h k hk r hr) (blockCode w)).comp hM
    push_cast at h1
    have h2 := h1.mul (tendsto_div_natCast_div hk (k - 1 - r))
    refine h2.congr fun N ↦ ?_
    simp only [Function.comp_apply, M]
    rcases Nat.eq_zero_or_pos ((N + (k - 1 - r)) / k) with h0 | h0
    · have := blockCount_le (b ^ k) (x * (b : ℝ) ^ r) (fun _ : Fin 1 ↦ blockCode w)
        ((N + (k - 1 - r)) / k)
      rw [h0] at this ⊢
      simp [Nat.le_zero.1 this]
    · have : (((N + (k - 1 - r)) / k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
      field_simp
  have hsum := tendsto_finsetSum (Finset.range k) fun r hr ↦ hterm r (Finset.mem_range.1 hr)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    show (k : ℝ) * (((b : ℝ) ^ k)⁻¹ * (k : ℝ)⁻¹) = ((b : ℝ) ^ k)⁻¹ by field_simp] at hsum
  refine hsum.congr fun N ↦ ?_
  rw [blockCount_eq_sum hk hb w N, Nat.cast_sum, Finset.sum_div]

theorem ae_mul_of_ae {p : ℝ → Prop} {c : ℝ} (hc : c ≠ 0) (h : ∀ᵐ x : ℝ, p x) :
    ∀ᵐ x : ℝ, p (x * c) := by
  rw [ae_iff] at h ⊢
  change volume ((· * c) ⁻¹' {x | ¬p x}) = 0
  rw [Real.volume_preimage_mul_right hc, h, mul_zero]

/-- Almost every real number is normal in base `b`. -/
theorem ae_isNormalIn (hb : 0 < b) : ∀ᵐ x : ℝ, IsNormalIn b x := by
  have : ∀ᵐ x : ℝ, ∀ k r : ℕ, IsSimplyNormalIn (b ^ k) (x * (b : ℝ) ^ r) := by
    simp only [ae_all_iff]
    intro k r
    exact ae_mul_of_ae (by positivity) (ae_isSimplyNormalIn (pow_pos hb k))
  filter_upwards [this] with x hx
  exact isNormalIn_of_isSimplyNormalIn_pow hb fun k _ r _ ↦ hx k r

/-- **Borel's normal number theorem**: almost every real number is absolutely normal. -/
theorem ae_isAbsolutelyNormal : ∀ᵐ x : ℝ, IsAbsolutelyNormal x := by
  simp only [IsAbsolutelyNormal]
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · exact (ae_isNormalIn (by omega)).mono fun x hx _ ↦ hx
  · exact Eventually.of_forall fun x h ↦ absurd h hb

/-- Absolutely normal numbers exist. -/
theorem exists_isAbsolutelyNormal : ∃ x : ℝ, IsAbsolutelyNormal x :=
  ae_isAbsolutelyNormal.exists

/-- The set of real numbers that are not absolutely normal is a Lebesgue null set. -/
theorem volume_setOf_not_isAbsolutelyNormal : volume {x : ℝ | ¬ IsAbsolutelyNormal x} = 0 :=
  ae_iff.1 ae_isAbsolutelyNormal

end Real
