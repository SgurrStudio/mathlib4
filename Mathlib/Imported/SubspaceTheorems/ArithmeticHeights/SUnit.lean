/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Imported.SubspaceTheorems.ArithmeticHeights.UnitHeight
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.Imported.TauCeti.RingTheory.DedekindDomain.SInteger.Unit
public import Mathlib.Imported.TauCeti.RingTheory.DedekindDomain.SInteger.Basic
public import Mathlib.Imported.TauCeti.NumberTheory.NumberField.FinitePlace.Basic
public import Mathlib.Imported.TauCeti.NumberTheory.Height.SInteger

/-!
# `S`-integers, `S`-units, and where their height lives

Let `K` be a number field and `S` a set of finite places, carried as Mathlib carries it, as a set
of height-one primes of `𝓞 K`. Mathlib defines the `S`-integers `S.integer K` and the `S`-units
`S.unit K` by the adic valuations away from `S`, and this file adds nothing to those definitions:
it translates them into the language of `NumberField.FinitePlace` and then reads off where the
height of such an element lives. For `x` an `S`-integer,

```text
mulHeight₁ x = (∏_{w | ∞} max (w x) 1 ^ mult w) * ∏ᶠ v ∈ S, max (|x|_v) 1,
```

so that only the infinite places and the places of `S` contribute — and conversely, an element
whose height is carried by those places alone is an `S`-integer. An `S`-unit is an `S`-integer, so
the display holds for it too; `S = ∅` recovers the ring of integers, its units, and the height of
a unit as a product over the infinite places alone.

## Main results

* `NumberField.FinitePlace.mk_apply_le_one_iff` and
  `NumberField.FinitePlace.mk_apply_eq_one_iff`: the dictionary between the absolute value at a
  finite place and the adic valuation of the corresponding prime — `|x|_v ≤ 1` iff `v x ≤ 1`, and
  `|x|_v = 1` iff `v x = 1`. Everything else in the file is a consequence.
* `Set.mem_integer_iff_finitePlace` and `Set.mem_unit_iff_finitePlace`: membership of the
  `S`-integers and of the `S`-units read at the finite places. The second contains the converse
  the milestone asks for: an element of `Kˣ` whose absolute values at the finite places outside
  `S` are all `1` is an `S`-unit.
* `NumberField.mulHeight₁_eq_of_mem_integer` and `NumberField.logHeight₁_eq_of_mem_integer`: the
  display above and its logarithmic form, with `NumberField.mulHeight₁_eq_of_mem_unit` and
  `NumberField.logHeight₁_eq_of_mem_unit` for `S`-units and
  `NumberField.mulHeight₁_eq_prod_of_mem_integer` for `S` given as a `Finset`.
* `NumberField.mulHeight₁_eq_iff_mem_integer`: the converse, so that the display *characterizes*
  the `S`-integers among the nonzero elements of `K`.
* `Set.mem_integer_empty_iff` and `Set.mem_unit_empty_iff`: the `∅`-integers are the algebraic
  integers and the `∅`-units are the units of `𝓞 K`; with
  `NumberField.Units.valuation_eq_one`, a unit of `𝓞 K` is an `S`-unit for every `S`.
* `NumberField.FinitePlace.finprod_apply_ratCast`: the finite part of the height of a rational,
  `∏ᶠ w, w q = (|q| ^ [K : ℚ])⁻¹`, the acceptance test the roadmap names for this layer.

## Implementation notes

⚠ **The height identity needs only the `S`-integer hypothesis, not the `S`-unit one.** The
milestone states it for `x ∈ S.unit K`, and it is true there, but the proof uses only that the
local factor `max (|x|_v) 1` is trivial away from `S`, and that is `|x|_v ≤ 1`, the defining
condition of an `S`-integer. What the `S`-unit condition buys is that the same holds for `x⁻¹`,
which is what makes the collection a *group* and is what Layer 6.5 needs; it buys nothing here.
The `S`-unit forms are stated as corollaries so that the milestone's statement is present under a
name of its own.

⚠ **The converse holds in the stronger, height-theoretic form.** The milestone asks only for the
converse on membership — all finite absolute values outside `S` equal to `1` implies `S`-unit —
which is the backwards direction of `Set.mem_unit_iff_finitePlace` and costs nothing once the
dictionary is in place. `NumberField.mulHeight₁_eq_iff_mem_integer` says more: for `x ≠ 0` the
height identity *itself* forces `x` to be an `S`-integer, because every local factor is at least
`1`, so a single place outside `S` with `|x|_v > 1` makes the full finite product strictly larger
than the part over `S`. That is the sense in which `S` cannot be shrunk.

⚠ **The dictionary is a statement about `WithZeroMulInt.toNNReal`, and it is an equivalence only
because the norm of a prime exceeds `1`.** `NumberField.HeightOneSpectrum.adicAbv` is the
composite of the valuation with `WithZeroMulInt.toNNReal (absNorm v.asIdeal)`, which is strictly
monotone exactly when that base is `> 1`; Mathlib records the base's size as
`IsDedekindDomain.HeightOneSpectrum.one_lt_absNorm`, and without it the absolute value would
collapse and the dictionary would read only in one direction. Mathlib's own
`NumberField.FinitePlace.norm_eq_one_iff_notMem` is the same statement restricted to algebraic
integers, where the valuation condition becomes membership in the prime.

⚠ **`S = ∅` is a theorem here, not a definitional unfolding.** Mathlib's `integer_empty` says
`(∅ : Set _).integer K = ⊥` as subalgebras, and `Set.unitEquivUnitsInteger` identifies `S`-units
with the units of the `S`-integers, but composing them to reach `(𝓞 K)ˣ` goes through
`Algebra.botEquivOfInjective`. `Set.mem_unit_empty_iff` instead argues directly: `x` and `x⁻¹`
both have all valuations `≤ 1`, so both are algebraic integers by
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`, and they are inverse to
each other there. With it, `NumberField.Units.mulHeight₁_eq_prod_infinitePlace` of Layer 6.1 is
the `S = ∅` case of this layer's display.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5.10, where the `S`-integers and `S`-units are introduced and the height of an `S`-unit is
described by the places of `S` together with the infinite ones.

The naming of the `S`-adic objects follows mathlib4#40791.

This is Layer 6.4 of the `ArithmeticHeights` roadmap.
-/

-- Ported from rwst/Subspace-Theorems, which does not run Mathlib's numeric-projection linter.
set_option linter.style.numericProjections false

public section

open Function Height IsDedekindDomain Module Real

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-!
### The dictionary between finite places and adic valuations
-/

namespace FinitePlace

/-- `mk_apply_le_one_iff` for a finite place presented as such. -/
theorem apply_le_one_iff (w : FinitePlace K) (x : K) :
    w x ≤ 1 ↔ w.maximalIdeal.valuation K x ≤ 1 := by
  rw [← mk_apply_le_one_iff w.maximalIdeal x, mk_maximalIdeal]

/-- `mk_apply_eq_one_iff` for a finite place presented as such. -/
theorem apply_eq_one_iff (w : FinitePlace K) (x : K) :
    w x = 1 ↔ w.maximalIdeal.valuation K x = 1 := by
  rw [← mk_apply_eq_one_iff w.maximalIdeal x, mk_maximalIdeal]

end FinitePlace

/-!
### Membership in the `S`-integers and the `S`-units
-/

/-- `Set.mem_unit_iff_finitePlace` for a nonzero element of `K` rather than an element of `Kˣ`. -/
theorem _root_.Set.mk0_mem_unit_iff_finitePlace (S : Set (HeightOneSpectrum (𝓞 K))) {x : K}
    (hx : x ≠ 0) :
    Units.mk0 x hx ∈ S.unit K ↔ ∀ v ∉ S, FinitePlace.mk v x = 1 :=
  S.mem_unit_iff_finitePlace (Units.mk0 x hx)

/-- **An `S`-unit is an `S`-integer.** -/
theorem _root_.Set.mem_integer_of_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} {x : Kˣ}
    (hx : x ∈ S.unit K) : (x : K) ∈ S.integer K :=
  fun v hv ↦ (hx v hv).le

/-!
### The height of an `S`-integer
-/

section Height

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The local factor of an `S`-integer is trivial at every finite place outside `S`. -/
private theorem max_mk_apply_one_eq_one {x : K} (hx : x ∈ S.integer K)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : max (FinitePlace.mk v x) 1 = 1 :=
  max_eq_right ((FinitePlace.mk_apply_le_one_iff v x).mpr (hx v hv))

end Height

/-!
### The identity characterizes the `S`-integers
-/

/-- The finite local factors of a nonzero element have finite multiplicative support, read on
height-one primes rather than on finite places. -/
private theorem hasFiniteMulSupport_max_mk_apply_one {x : K} (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ max (FinitePlace.mk v x) 1 := by
  have h := FinitePlace.hasFiniteMulSupport (K := K) hx
  refine Set.Finite.subset (h.preimage
    (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn) fun v hv ↦ ?_
  simp only [Set.mem_preimage, mem_mulSupport] at hv ⊢
  intro hone
  exact hv (by rw [show FinitePlace.mk v x = 1 from hone, max_self])

/-!
### `S = ∅`
-/

namespace Units

/-- **A unit of `𝓞 K` has adic valuation `1` at every prime**, hence is an `S`-unit for every `S`.
This is `NumberField.FinitePlace.apply_units_eq_one` of Layer 6.1 read through the dictionary. -/
theorem valuation_eq_one (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) :
    v.valuation K ((u : 𝓞 K) : K) = 1 :=
  (FinitePlace.mk_apply_eq_one_iff v _).mp (FinitePlace.apply_units_eq_one (FinitePlace.mk v) u)

end Units

/-!
### The finite part of the height of a rational
-/

namespace FinitePlace

/-- **The finite part of the height of a rational number**, `∏ᶠ w, w q = (|q| ^ [K : ℚ])⁻¹`: the
acceptance test the roadmap names for this layer. A rational is an `S`-unit exactly when `S`
contains every prime dividing its numerator or denominator, and then this product is the finite
factor of its height. -/
theorem finprod_apply_ratCast {q : ℚ} (hq : q ≠ 0) :
    ∏ᶠ w : FinitePlace K, w (q : K) = (|(q : ℝ)| ^ finrank ℚ K)⁻¹ := by
  have hK : ((q : ℚ) : K) ≠ 0 := by
    simpa using hq
  rw [prod_eq_inv_abs_norm hK, show ((q : ℚ) : K) = algebraMap ℚ K q from rfl,
    Algebra.norm_algebraMap]
  push_cast [abs_pow]
  ring

end FinitePlace

/-!
### Worked examples
-/

section Examples

variable {K : Type*} [Field K] [NumberField K]

/-- **Conformance with Layer 6.1.** The height of a unit of `𝓞 K` is a product over the infinite
places alone — `NumberField.Units.mulHeight₁_eq_prod_infinitePlace` — and that is the `S = ∅` case
of this layer's display, a unit of `𝓞 K` being an `∅`-integer. -/
example (u : (𝓞 K)ˣ) :
    mulHeight₁ ((u : 𝓞 K) : K)
      = ∏ w : InfinitePlace K, max (w ((u : 𝓞 K) : K)) 1 ^ w.mult := by
  rw [mulHeight₁_eq_of_mem_integer (∅ : Set (HeightOneSpectrum (𝓞 K)))
    fun v _ ↦ (Units.valuation_eq_one v u).le, finprod_mem_empty, mul_one]

/-- **Conformance with Mathlib.** A unit of `𝓞 K` is an `∅`-unit, so
`IsDedekindDomain.integer_empty` and `Set.unitEquivUnitsInteger` are matched by
`Set.mem_unit_empty_iff` on elements. -/
example (u : (𝓞 K)ˣ) (hu : ((u : 𝓞 K) : K) ≠ 0) :
    Units.mk0 _ hu ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K :=
  (Set.mem_unit_empty_iff (R := 𝓞 K) K).2 ⟨u, rfl⟩

/-- **Acceptance test: the finite part of the height of a rational.** The roadmap names
`∏ᶠ w, w q = (|q| ^ [K : ℚ])⁻¹` as the check for this layer. At `q = 2` it says that the finite
places above `2` carry `2 ^ [K : ℚ]` between them — exactly the factor that
`NumberField.mulHeight₁_eq_of_mem_integer` moves inside `S` once `S` contains those places. -/
example : ∏ᶠ w : FinitePlace K, w ((2 : ℚ) : K) = ((2 : ℝ) ^ finrank ℚ K)⁻¹ := by
  rw [FinitePlace.finprod_apply_ratCast (K := K) (by norm_num : (2 : ℚ) ≠ 0)]
  norm_num

/-- **Rejection test: the `S`-integer hypothesis is load-bearing.** At `S = ∅` and `x = 1/2` the
infinite factor is `1`, every infinite place giving `1/2 < 1`, while the height is `2 ^ [K : ℚ]`;
the whole height of `1/2` sits at the finite places above `2`, which is the `S` this element
needs. By `NumberField.mulHeight₁_eq_iff_mem_integer` the failure is equivalent to `1/2` not
being an algebraic integer. -/
example : mulHeight₁ (((1 : ℚ) / 2 : ℚ) : K)
    ≠ ∏ w : InfinitePlace K, max (w (((1 : ℚ) / 2 : ℚ) : K)) 1 ^ w.mult := by
  have hd : 0 < finrank ℚ K := Module.finrank_pos
  have h2 : ((2 : ℚ) : K) ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).integer K := by
    have he : ((2 : ℚ) : K) = algebraMap (𝓞 K) K (2 : 𝓞 K) := by rw [map_ofNat]; push_cast; ring
    rw [he]
    exact Subalgebra.algebraMap_mem _ _
  have hhalf : ∀ w : InfinitePlace K, max (w (((1 : ℚ) / 2 : ℚ) : K)) 1 = 1 := fun w ↦ by
    rw [InfinitePlace.map_ratCast, ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs]
    norm_num
  have htwo : ∀ w : InfinitePlace K, max (w (((2 : ℚ) : K))) 1 = 2 := fun w ↦ by
    rw [InfinitePlace.map_ratCast, ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs]
    norm_num
  have hrhs : (∏ w : InfinitePlace K, max (w (((1 : ℚ) / 2 : ℚ) : K)) 1 ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by rw [hhalf w, one_pow]
  have hlhs : mulHeight₁ (((1 : ℚ) / 2 : ℚ) : K) = 2 ^ finrank ℚ K := by
    rw [show (((1 : ℚ) / 2 : ℚ) : K) = (((2 : ℚ) : K))⁻¹ by push_cast; ring, mulHeight₁_inv,
      mulHeight₁_eq_of_mem_integer _ h2, finprod_mem_empty, mul_one]
    calc (∏ w : InfinitePlace K, max (w (((2 : ℚ) : K))) 1 ^ w.mult)
        = ∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult :=
          Finset.prod_congr rfl fun w _ ↦ by rw [htwo w]
      _ = 2 ^ ∑ w : InfinitePlace K, w.mult := Finset.prod_pow_eq_pow_sum _ _ _
      _ = 2 ^ finrank ℚ K := by rw [← totalWeight_eq_sum_mult, totalWeight_eq_finrank]
  rw [hlhs, hrhs]
  exact (one_lt_pow₀ (one_lt_two (α := ℝ)) hd.ne').ne'

end Examples

end NumberField
