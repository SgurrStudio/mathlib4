/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.NumberTheory.Normal.Wall

import Mathlib.Imported.TauCeti.NumberTheory.Equidistribution.Weyl

/-!
# Weyl's criterion

A real sequence `u` is equidistributed modulo one as soon as its *Weyl sums* are small: for every
nonzero integer `h`, `(1 / N) ∑_{n < N} e(h u n) → 0`, where `e(t) = exp(2 π i t)`. Combined with
Wall's theorem this gives the *exponential-sum criterion for normality*: `x` is normal in base `b`
as soon as `(1 / N) ∑_{n < N} e(h b ^ n x) → 0` for every `h ≠ 0`. This is the entry point of the
analytic proofs of normality (Davenport–Erdős, Besicovitch, Schmidt).

## Main statements

* `Real.isEquidistributedModOne_iff_tendsto_weylSum`: **Weyl's criterion**.
* `Real.isNormalIn_iff_tendsto_weylSum`: the exponential-sum characterization of normality.

## Proof

Both directions are Tau Ceti's Weyl criterion `TauCeti.uniformDistribution_mod_one_tfae`
(imported in `Mathlib/Imported/TauCeti`), restated for `IsEquidistributedModOne`, whose
frequencies are normalized by `N` rather than `N + 1`. An earlier version of this file ported the
sufficiency direction from Trevor Morris's `normal-numbers` repository instead.

## References

* [L. Kuipers, H. Niederreiter, *Uniform distribution of sequences*][KuipersNiederreiter1974]
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The Weyl mean of `u` in terms of the characters `AddCircle.fourier h` of `UnitAddCircle`. -/
theorem weylMean_eq_fourier (u : ℕ → ℝ) (h : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * h * u n)) / N =
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, AddCircle.fourier h (u n : UnitAddCircle) := by
  rw [div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [AddCircle.fourier_coe_apply]
  push_cast
  ring_nf

/-- **Weyl's criterion**: if every nonzero Weyl mean of `u` tends to `0`, then `u` is
equidistributed modulo one. -/
theorem isEquidistributedModOne_of_tendsto_weylSum (u : ℕ → ℝ)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * u n)) / N) atTop (𝓝 0)) :
    IsEquidistributedModOne u := by
  have e := (TauCeti.uniformDistribution_mod_one_tfae u).out 2 3
  have h2 := e.2 fun h hh ↦ by
    simpa only [weylMean_eq_fourier] using (tendsto_add_atTop_iff_nat 1).2 (hW h hh)
  exact fun a c ha hac hc ↦ (tendsto_add_atTop_iff_nat 1).1 (h2 a c ha hac hc)

/-- **Exponential-sum criterion for normality**: if `(1 / N) ∑_{n < N} e(h b ^ n x) → 0` for
every integer `h ≠ 0`, then `x` is normal in base `b`. -/
theorem isNormalIn_of_tendsto_weylSum {b : ℕ} {x : ℝ} (hb : 2 ≤ b)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n))) / N) atTop (𝓝 0)) :
    IsNormalIn b x :=
  (isNormalIn_iff_isEquidistributedModOne hb).2 <|
    isEquidistributedModOne_of_tendsto_weylSum _ fun h hh ↦ by
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast] using hW h hh

/-- **Weyl's criterion**, necessity: the nonzero Weyl means of an equidistributed sequence tend
to `0`. -/
theorem _root_.IsEquidistributedModOne.tendsto_weylSum {u : ℕ → ℝ} (hu : IsEquidistributedModOne u)
    {h : ℤ} (hh : h ≠ 0) : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * u n)) / N) atTop (𝓝 0) := by
  have e := (TauCeti.uniformDistribution_mod_one_tfae u).out 2 3
  have h3 := e.1 (fun a c ha hac hc ↦ (tendsto_add_atTop_iff_nat 1).2 (hu a c ha hac hc)) h hh
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [weylMean_eq_fourier] using h3

/-- **Weyl's criterion**: `u` is equidistributed modulo one iff all its nonzero Weyl means tend
to `0`. -/
theorem isEquidistributedModOne_iff_tendsto_weylSum (u : ℕ → ℝ) :
    IsEquidistributedModOne u ↔ ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * u n)) / N) atTop (𝓝 0) :=
  ⟨fun hu _ hh ↦ hu.tendsto_weylSum hh, isEquidistributedModOne_of_tendsto_weylSum u⟩

/-- **Exponential-sum characterization of normality**: `x` is normal in base `b` iff
`(1 / N) ∑_{n < N} e(h b ^ n x) → 0` for every integer `h ≠ 0`. -/
theorem isNormalIn_iff_tendsto_weylSum {b : ℕ} {x : ℝ} (hb : 2 ≤ b) :
    IsNormalIn b x ↔ ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * (x * (b : ℝ) ^ n))) / N) atTop (𝓝 0) := by
  refine ⟨fun hx h hh ↦ ?_, isNormalIn_of_tendsto_weylSum hb⟩
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast] using
    ((isNormalIn_iff_isEquidistributedModOne hb).1 hx).tendsto_weylSum hh

end Real
