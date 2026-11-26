/-
Copyright (c) 2026 Massimiliano Pablo Pianges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Massimiliano Pablo Pianges
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations

/-!
# A lower bound for the error of a continued-fraction convergent

Imported verbatim from the mathlib4 fork
[Kratostau/mathlib4](https://github.com/Kratostau/mathlib4/tree/f64e6951e30882d0a47f6d4e8ac70f51dcf1c99b),
branch `grok/one-div-lt-abs-sub-convs` (Apache 2.0), where it is appended to
`Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean`.

`GenContFract.one_div_lt_abs_sub_convs`: `1 / (Bₙ * (Bₙ₊₁ + Bₙ)) < |v - Aₙ / Bₙ|`, the lower half
of the classical two-sided estimate (the upper half is `GenContFract.abs_sub_convs_le`).
-/

@[expose] public section

open GenContFract

open GenContFract (of)

open Int Nat

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

namespace GenContFract

/-- Shows that `1 / (Bₙ * (Bₙ₊₁ + Bₙ)) < |v - Aₙ / Bₙ|`. Together with
`GenContFract.abs_sub_convs_le`, this gives the classical two-sided estimate for the
approximation of `v` by its convergents. -/
theorem one_div_lt_abs_sub_convs (not_terminatedAt_n : ¬(of v).TerminatedAt n) :
    1 / ((of v).dens n * ((of v).dens (n + 1) + (of v).dens n)) < |v - (of v).convs n| := by
  let g := of v
  let nextConts := g.contsAux (n + 2)
  set conts := contsAux g (n + 1) with conts_eq
  set pred_conts := contsAux g n with pred_conts_eq
  change 1 / (conts.b * (nextConts.b + conts.b)) < |v - convs g n|
  obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
    Option.ne_none_iff_exists'.1 not_terminatedAt_n
  have gp_a_eq_one : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a s_nth_eq)
  have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b := by
    simp [nextConts, contsAux_recurrence s_nth_eq pred_conts_eq conts_eq, gp_a_eq_one,
      pred_conts_eq.symm, conts_eq.symm, add_comm]
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
      ∃ ifp_succ_n, IntFractPair.stream v (n + 1) = some ifp_succ_n ∧ (ifp_succ_n.b : K) = gp.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, if_of_eq_ifp_succ_n⟩ :
    ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
      ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  let den' := conts.b * (pred_conts.b + ifp_n.fr⁻¹ * conts.b)
  have conts_b_ineq : (fib (n + 1) : K) ≤ conts.b :=
    haveI : ¬g.TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) not_terminatedAt_n
    fib_le_of_contsAux_b <| Or.inr this
  have zero_lt_conts_b : 0 < conts.b :=
    conts_b_ineq.trans_lt' <| mod_cast fib_pos.2 n.succ_pos
  have zero_le_pred_conts_b : 0 ≤ pred_conts.b :=
    haveI : (fib n : K) ≤ pred_conts.b :=
      haveI : ¬g.TerminatedAt (n - 2) :=
        mt (terminated_stable (n.sub_le 2)) not_terminatedAt_n
      fib_le_of_contsAux_b <| Or.inr this
    le_trans (mod_cast (fib n).zero_le) this
  have zero_lt_fr_inv : 0 < ifp_n.fr⁻¹ :=
    inv_pos.2 (lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg stream_nth_eq)
      stream_nth_fr_ne_zero.symm)
  have zero_lt_den' : 0 < den' := by positivity
  have abs_eq : |v - convs g n| = 1 / den' := by
    have : v - convs g n = (-1) ^ n / den' := by
      have tmp := sub_convs_eq stream_nth_eq
      simp only [stream_nth_fr_ne_zero, ite_false] at tmp
      rw [tmp]
      ring
    rw [this, abs_div, abs_neg_one_pow n, abs_of_pos zero_lt_den']
  rw [abs_eq]
  refine one_div_lt_one_div_of_lt zero_lt_den' ?_
  have fr_inv_lt : ifp_n.fr⁻¹ < gp.b + 1 := by
    have : (ifp_succ_n.b : K) = (⌊ifp_n.fr⁻¹⌋ : K) := by rw [← if_of_eq_ifp_succ_n]; rfl
    rw [← ifp_succ_n_b_eq_gp_b, this]
    exact Int.lt_floor_add_one _
  have : pred_conts.b + ifp_n.fr⁻¹ * conts.b < nextConts.b + conts.b := by
    rw [nextConts_b_eq]
    nlinarith
  exact mul_lt_mul_of_pos_left this zero_lt_conts_b

end GenContFract
