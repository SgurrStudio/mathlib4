/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Normal.Wall

/-!
# Discrepancy, quantitative Wall's theorem, and Koksma's inequality

This file develops the discrepancy theory of sequences modulo one and its applications to
normal numbers and numerical integration:

* **Discrepancy and star discrepancy**: for a sequence `u : ℕ → ℝ` and `N : ℕ`, we define
  `Real.localDiscrepancy u N a c`, the star discrepancy `Real.starDiscrepancy u N`, and the
  extreme discrepancy `Real.discrepancy u N`, proving `D_N^*(u) ≤ D_N(u) ≤ 2 D_N^*(u)`,
  `IsEquidistributedModOne u ↔ Tendsto (starDiscrepancy u) atTop (𝓝 0)` (Kuipers–Niederreiter,
  Ch. 2, Theorem 1.1), and a quantitative version of Wall's theorem.
* **Koksma's inequality**: for every function `f : ℝ → ℝ` of bounded variation on `[0, 1]` and
  `N ≥ 1`,
  `|(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in 0..1, f t| ≤ V_0^1(f) * D_N^*(u)`
  with the sharp constant `1`, together with the differentiable (`C¹`) variant with
  `∫ t in 0..1, |f' t|`.

## References

* L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974, Ch. 2.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Real

/-- The signed discrepancy of the first `N` terms of `u` on the interval `[a, c) ⊆ [0, 1]`:
`#{n < N : Int.fract (u n) ∈ [a, c)} / N - (c - a)`. -/
noncomputable def localDiscrepancy (u : ℕ → ℝ) (N : ℕ) (a c : ℝ) : ℝ :=
  (((Finset.range N).filter fun n ↦ Int.fract (u n) ∈ Ico a c).card : ℝ) / N - (c - a)

/-- The **star discrepancy** `D_N^*(u)` of the first `N` terms of `u`:
`sup_{t ∈ [0, 1]} |#{n < N : Int.fract (u n) < t} / N - t|`. -/
noncomputable def starDiscrepancy (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ t : Icc (0 : ℝ) 1, |localDiscrepancy u N 0 t|

/-- The **extreme discrepancy** `D_N(u)` of the first `N` terms of `u`:
`sup_{0 ≤ a ≤ c ≤ 1} |#{n < N : Int.fract (u n) ∈ [a, c)} / N - (c - a)|`. -/
noncomputable def discrepancy (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ p : {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}, |localDiscrepancy u N p.val.1 p.val.2|

lemma abs_localDiscrepancy_le_one (u : ℕ → ℝ) (N : ℕ) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    |localDiscrepancy u N a c| ≤ 1 := by sorry

lemma localDiscrepancy_zero_zero (u : ℕ → ℝ) (N : ℕ) :
    localDiscrepancy u N 0 0 = 0 := by sorry

lemma localDiscrepancy_zero_one (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    localDiscrepancy u N 0 1 = 0 := by sorry

lemma localDiscrepancy_eq_sub (u : ℕ → ℝ) (N : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) :
    localDiscrepancy u N a c = localDiscrepancy u N 0 c - localDiscrepancy u N 0 a := by sorry

lemma abs_localDiscrepancy_zero_le_starDiscrepancy (u : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |localDiscrepancy u N 0 t| ≤ starDiscrepancy u N := by sorry

lemma abs_localDiscrepancy_le_discrepancy (u : ℕ → ℝ) (N : ℕ) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    |localDiscrepancy u N a c| ≤ discrepancy u N := by sorry

lemma starDiscrepancy_le {u : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, |localDiscrepancy u N 0 t| ≤ C) :
    starDiscrepancy u N ≤ C := by sorry

lemma discrepancy_le {u : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hC : ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 → |localDiscrepancy u N a c| ≤ C) :
    discrepancy u N ≤ C := by sorry

lemma starDiscrepancy_nonneg (u : ℕ → ℝ) (N : ℕ) : 0 ≤ starDiscrepancy u N := by sorry

lemma starDiscrepancy_le_one (u : ℕ → ℝ) (N : ℕ) : starDiscrepancy u N ≤ 1 := by sorry

lemma starDiscrepancy_le_discrepancy (u : ℕ → ℝ) (N : ℕ) :
    starDiscrepancy u N ≤ discrepancy u N := by sorry

lemma discrepancy_nonneg (u : ℕ → ℝ) (N : ℕ) : 0 ≤ discrepancy u N := by sorry

lemma discrepancy_le_one (u : ℕ → ℝ) (N : ℕ) : discrepancy u N ≤ 1 := by sorry

lemma discrepancy_le_two_mul_starDiscrepancy (u : ℕ → ℝ) (N : ℕ) :
    discrepancy u N ≤ 2 * starDiscrepancy u N := by sorry

/-- A real sequence `u` is equidistributed modulo one iff its star discrepancy `D_N^*(u)` tends
to `0` (Kuipers–Niederreiter, Ch. 2, Theorem 1.1). -/
theorem isEquidistributedModOne_iff_tendsto_starDiscrepancy {u : ℕ → ℝ} :
    IsEquidistributedModOne u ↔ Tendsto (starDiscrepancy u) atTop (𝓝 0) := by sorry

/-- A real sequence `u` is equidistributed modulo one iff its extreme discrepancy `D_N(u)` tends
to `0`. -/
theorem isEquidistributedModOne_iff_tendsto_discrepancy {u : ℕ → ℝ} :
    IsEquidistributedModOne u ↔ Tendsto (discrepancy u) atTop (𝓝 0) := by sorry

/-- **Quantitative Wall's theorem**: the error in the frequency of any base-`b` digit block `w`
of length `k` is bounded by the extreme discrepancy `D_N((x * b ^ n))`. -/
theorem abs_blockCount_div_sub_le_discrepancy {b k : ℕ} (hb : 0 < b) (x : ℝ)
    (w : Fin k → Fin b) (N : ℕ) :
    |(blockCount b x w N : ℝ) / N - ((b : ℝ) ^ k)⁻¹| ≤
      discrepancy (fun n ↦ x * (b : ℝ) ^ n) N := by sorry

/-- Quantitative Wall's theorem in terms of star discrepancy: the error in the frequency of any
base-`b` digit block `w` is at most `2 * D_N^*((x * b ^ n))`. -/
theorem abs_blockCount_div_sub_le_two_mul_starDiscrepancy {b k : ℕ} (hb : 0 < b) (x : ℝ)
    (w : Fin k → Fin b) (N : ℕ) :
    |(blockCount b x w N : ℝ) / N - ((b : ℝ) ^ k)⁻¹| ≤
      2 * starDiscrepancy (fun n ↦ x * (b : ℝ) ^ n) N := by sorry

/-- `x` is normal in base `b ≥ 2` iff the star discrepancy of `(x * b ^ n)` tends to `0`. -/
theorem isNormalIn_iff_tendsto_starDiscrepancy {b : ℕ} (hb : 2 ≤ b) {x : ℝ} :
    IsNormalIn b x ↔
      Tendsto (starDiscrepancy fun n ↦ x * (b : ℝ) ^ n) atTop (𝓝 0) := by sorry

/-- **Koksma's inequality** for monotone functions on `[0, 1]`. -/
theorem koksma_inequality_of_monotoneOn {g : ℝ → ℝ} (hg : MonotoneOn g (Icc 0 1))
    (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, g (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, g t| ≤
      (g 1 - g 0) * starDiscrepancy u N := by sorry

/-- **Koksma's inequality** (sharp form for functions of bounded variation on `[0, 1]`):
for any `f : ℝ → ℝ` with `BoundedVariationOn f (Icc 0 1)` and `N ≥ 1`,
`|(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in 0..1, f t| ≤ V_0^1(f) * D_N^*(u)`. -/
theorem koksma_inequality {f : ℝ → ℝ} (hf : BoundedVariationOn f (Icc 0 1))
    (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, f t| ≤
      (eVariationOn f (Icc 0 1)).toReal * starDiscrepancy u N := by sorry

/-- **Koksma's inequality** for differentiable functions with integrable derivative on `[0, 1]`. -/
theorem koksma_inequality_of_hasDerivAt {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) (u : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Finset.range N, f (Int.fract (u n))) / N - ∫ t in (0 : ℝ)..1, f t| ≤
      (∫ t in (0 : ℝ)..1, |f' t|) * starDiscrepancy u N := by sorry

end Real
