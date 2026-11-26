/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.PiatetskiShapiro
public import Mathlib.NumberTheory.Normal.Rational

/-!
# Normality in bases `b` and `b ^ r`

We prove that normality in base `b` is the same as normality in base `b ^ r` (**Maxfield**, 1953),
and hence the same in any two multiplicatively dependent bases `b ^ m = c ^ n`. We also prove
**Pillai's theorem** (1940): `x` is normal in base `b` if and only if it is simply normal in every
base `b ^ r`, `r ≥ 1`. Since the base-`b ^ r` digits of `x` are its aligned, non-overlapping
blocks of `r` base-`b` digits, this is also the theorem of **Niven and Zuckerman** (1951) that
normality can be tested on aligned blocks.

## Main statements

* `Real.isNormalIn_pow_iff`: Maxfield's theorem.
* `Real.isNormalIn_iff_of_pow_eq_pow`: normality in multiplicatively dependent bases.
* `Real.isNormalIn_iff_forall_isSimplyNormalIn_pow`: Pillai's and Niven–Zuckerman's theorem.

## References

* [J. E. Maxfield, *Normal k-tuples*][Maxfield1953]
* [S. S. Pillai, *On normal numbers*][Pillai1940]
* [I. Niven, H. S. Zuckerman, *On the definition of normal numbers*][NivenZuckerman1951]
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ} {x : ℝ}

/-- A number normal in base `b` is normal in base `b ^ r`. -/
theorem IsNormalIn.pow (hb : 2 ≤ b) (h : IsNormalIn b x) {r : ℕ} (hr : 0 < r) :
    IsNormalIn (b ^ r) x := by
  sorry

/-- A number normal in base `b ^ r` is normal in base `b`. -/
theorem IsNormalIn.of_pow (hb : 2 ≤ b) {r : ℕ} (hr : 0 < r) (h : IsNormalIn (b ^ r) x) :
    IsNormalIn b x := by
  sorry

/-- **Maxfield's theorem**: `x` is normal in base `b ^ r` if and only if it is normal in base
`b`. -/
theorem isNormalIn_pow_iff (hb : 2 ≤ b) {r : ℕ} (hr : 0 < r) :
    IsNormalIn (b ^ r) x ↔ IsNormalIn b x :=
  ⟨IsNormalIn.of_pow hb hr, fun h ↦ h.pow hb hr⟩

/-- Normality in two *multiplicatively dependent* bases, `b ^ m = c ^ n`, is equivalent. -/
theorem isNormalIn_iff_of_pow_eq_pow {c m n : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hm : 0 < m)
    (hn : 0 < n) (h : b ^ m = c ^ n) : IsNormalIn b x ↔ IsNormalIn c x := by
  rw [← isNormalIn_pow_iff hb hm, h, isNormalIn_pow_iff hc hn]

/-- **Pillai's theorem**: if `x` is simply normal in every base `b ^ r`, `r ≥ 1`, then `x` is
normal in base `b`. -/
theorem isNormalIn_of_forall_isSimplyNormalIn_pow (hb : 2 ≤ b)
    (h : ∀ r : ℕ, 0 < r → IsSimplyNormalIn (b ^ r) x) : IsNormalIn b x := by
  sorry

/-- **Pillai's theorem** and **Niven–Zuckerman's theorem**: `x` is normal in base `b` if and only
if it is simply normal in every base `b ^ r`, i.e. every aligned block of `r` base-`b` digits
occurs with frequency `b⁻ʳ`. -/
theorem isNormalIn_iff_forall_isSimplyNormalIn_pow (hb : 2 ≤ b) :
    IsNormalIn b x ↔ ∀ r : ℕ, 0 < r → IsSimplyNormalIn (b ^ r) x :=
  ⟨fun h _ hr ↦ (h.pow hb hr).isSimplyNormalIn, isNormalIn_of_forall_isSimplyNormalIn_pow hb⟩

end Real
