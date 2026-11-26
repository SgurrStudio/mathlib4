/-
Copyright (c) 2026 Brigham Hall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brigham Hall
-/
module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-!
# Every irrational number is `LiouvilleWith p` for `p ≤ 2`

Imported verbatim from the mathlib4 fork
[localecho/mathlib4](https://github.com/localecho/mathlib4/tree/1a854568082fc8245baf6ac28fd360bbe8596e6a),
branch `liouville-with-gap` (Apache 2.0), where it is appended to
`Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean`.

`Irrational.liouvilleWith`: via Dirichlet's approximation theorem, an irrational `x` satisfies
`LiouvilleWith p x` for every `p ≤ 2`.
-/

@[expose] public section

open Filter Metric Real Set

open scoped Filter Topology

/-- For fixed denominator `n > 0`, the rationals within `1/n²` of `x` that have
denominator exactly `n` are finitely many — their numerators are confined to a
bounded interval around `n * x`. -/
private theorem finite_den_eq_and_close {x : ℝ} (n : ℕ) (hn : 0 < n) :
    {q : ℚ | q.den = n ∧ |x - q| < 1 / (q.den : ℝ) ^ 2}.Finite := by
  apply Set.Finite.of_finite_image (f := fun q : ℚ => q.num)
  · apply Set.Finite.subset (Set.finite_Icc ⌊(n : ℝ) * x - 1⌋ ⌈(n : ℝ) * x + 1⌉)
    rintro k ⟨q, ⟨hden, hclose⟩, rfl⟩
    have hn' : (0 : ℝ) < n := mod_cast hn
    have hqx : (q : ℝ) = (q.num : ℝ) / n := by
      rw [← hden]; exact_mod_cast (Rat.num_div_den q).symm
    rw [hden, hqx] at hclose
    have hbound : |(n : ℝ) * x - q.num| < 1 := by
      have heq : (n : ℝ) * (x - (q.num : ℝ) / n) = (n : ℝ) * x - q.num := by field_simp
      have hmul : (n : ℝ) * |x - (q.num : ℝ) / n| = |(n : ℝ) * x - q.num| := by
        rw [← heq, abs_mul, abs_of_pos hn']
      have h1 : (n : ℝ) * |x - (q.num : ℝ) / n| < (n : ℝ) * (1 / (n : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hclose hn'
      rw [hmul] at h1
      have h2 : (n : ℝ) * (1 / (n : ℝ) ^ 2) = 1 / n := by field_simp
      rw [h2] at h1
      have h3 : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact_mod_cast hn
      linarith
    have h2 := abs_lt.mp hbound
    exact ⟨le_of_lt (Int.floor_lt.mpr (by linarith [h2.1])),
           le_of_lt (Int.lt_ceil.mpr (by linarith [h2.2]))⟩
  · rintro q1 ⟨hden1, -⟩ q2 ⟨hden2, -⟩ heq
    exact Rat.ext heq (hden1.trans hden2.symm)

/-- Among rationals `q` with `|x - q| < 1/q.den²`, infinitely many denominators occur. -/
private theorem infinite_den_of_irrational {x : ℝ} (hx : Irrational x) :
    {n : ℕ | ∃ q : ℚ, q.den = n ∧ |x - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  intro hfin
  apply Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hcover : {q : ℚ | |x - q| < 1 / (q.den : ℝ) ^ 2} ⊆
      ⋃ n ∈ hfin.toFinset, {q : ℚ | q.den = n ∧ |x - q| < 1 / (q.den : ℝ) ^ 2} := by
    intro q hq
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨q.den, hfin.mem_toFinset.mpr ⟨q, rfl, hq⟩, rfl, hq⟩
  refine Set.Finite.subset ?_ hcover
  apply Set.Finite.biUnion hfin.toFinset.finite_toSet
  intro n _
  rcases Nat.eq_zero_or_pos n with rfl | hn'
  · apply Set.Finite.subset Set.finite_empty
    rintro q ⟨hden, -⟩
    exact absurd hden q.den_nz
  · exact finite_den_eq_and_close n hn'

/-- The reverse direction for `1 < p ≤ 2`: every irrational `x` is `LiouvilleWith p x`.
Via Dirichlet's approximation theorem
(`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`) rather than continued
fractions directly — the two are closely related but this route avoids re-deriving
convergent theory. -/
theorem Irrational.liouvilleWith {x : ℝ} (hx : Irrational x) {p : ℝ} (hp2 : p ≤ 2) :
    LiouvilleWith p x := by
  refine ⟨1, ?_⟩
  rw [Nat.frequently_atTop_iff_infinite]
  apply Set.Infinite.mono _ (infinite_den_of_irrational hx)
  rintro n ⟨q, hden, hclose⟩
  have hn' : (0 : ℝ) < n := by have := q.pos; rw [hden] at this; exact_mod_cast this
  have hqx : (q.num : ℝ) / (n : ℝ) = (q : ℝ) := by
    rw [← hden]; exact_mod_cast Rat.num_div_den q
  refine ⟨q.num, ?_, ?_⟩
  · simpa using hx.ne_rational q.num (n : ℤ)
  · rw [hqx, ← hden]
    have hn1 : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast q.pos
    have hstep : (q.den : ℝ) ^ p ≤ (q.den : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast (q.den : ℝ) 2]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by exact_mod_cast hp2)
    calc |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 := hclose
      _ ≤ 1 / (q.den : ℝ) ^ p :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) p) hstep
