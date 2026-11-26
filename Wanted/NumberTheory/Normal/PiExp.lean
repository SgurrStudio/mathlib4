/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Pi

/-!
# Normality conjectures for `π`, `e`, `log 2`, and Bailey–Crandall Hypothesis A

It is widely conjectured that the fundamental mathematical constants `π`, `e = exp 1`, and `log 2`
are absolutely normal, i.e. normal in every integer base `b ≥ 2`. All of these remain wide open;
it is not even known whether `π` or `e` is simply normal in base `2` or `10`.

We also state **Bailey–Crandall Hypothesis A** (2001), which predicts that every BBP dynamical
orbit `x₀ = 0`, `x_{n+1} = Int.fract (b * x_n + p (n + 1) / q (n + 1))` (for integer polynomials
`p, q` with `deg p < deg q` and `q (n + 1) ≠ 0`) either has a finite attractor modulo one or is
equidistributed modulo one. By `Real.isNormalIn_two_pi_of_hypothesisA`, even the single instance
`isEquidistributedModOne_bbpOrbit_pi` implies that `π` is normal in bases `2` and `16`.

## References

* [D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant
  expansions*][BaileyCrandall2001]
* [Y. Bugeaud, *Distribution modulo one and Diophantine approximation*][Bugeaud2012]
-/

namespace Real

/-- `π` is absolutely normal (normal in every base `b ≥ 2`). -/
proof_wanted isAbsolutelyNormal_pi : IsAbsolutelyNormal π

/-- `π` is normal in base `2`. -/
proof_wanted isNormalIn_two_pi : IsNormalIn 2 π

/-- `π` is normal in base `10`. -/
proof_wanted isNormalIn_ten_pi : IsNormalIn 10 π

/-- `e = exp 1` is absolutely normal (normal in every base `b ≥ 2`). -/
proof_wanted isAbsolutelyNormal_exp_one : IsAbsolutelyNormal (Real.exp 1)

/-- `e = exp 1` is normal in base `10`. -/
proof_wanted isNormalIn_ten_exp_one : IsNormalIn 10 (Real.exp 1)

/-- `log 2` is normal in base `2`. -/
proof_wanted isNormalIn_two_log_two : IsNormalIn 2 (Real.log 2)

/-- **Bailey–Crandall Hypothesis A** for the base-`16` BBP orbit of `π` (equivalent to
`IsNormalIn 2 π` by `Real.isNormalIn_two_pi_iff`). -/
proof_wanted isEquidistributedModOne_bbpOrbit_pi :
    IsEquidistributedModOne (bbpOrbit 16 bbpPiCoeff)

/-- **Bailey–Crandall Hypothesis A** (general rational BBP form): for every base `b ≥ 2` and
rational function `r n = p n / q n` with `p, q : ℤ[X]`, `deg p < deg q`, and `q n ≠ 0` for all
`n`, the Bailey–Crandall orbit either has a finite attractor or is equidistributed modulo one. -/
proof_wanted baileyCrandall_hypothesisA {b : ℕ} (hb : 2 ≤ b) (p q : Polynomial ℤ)
    (hdeg : p.natDegree < q.natDegree) (hq : ∀ n : ℕ, Polynomial.eval (n : ℤ) q ≠ 0) :
    HasFiniteAttractorModOne (bbpOrbit b fun n ↦
      ((Polynomial.eval (n : ℤ) p : ℤ) : ℝ) / ((Polynomial.eval (n : ℤ) q : ℤ) : ℝ)) ∨
    IsEquidistributedModOne (bbpOrbit b fun n ↦
      ((Polynomial.eval (n : ℤ) p : ℤ) : ℝ) / ((Polynomial.eval (n : ℤ) q : ℤ) : ℝ))

end Real
