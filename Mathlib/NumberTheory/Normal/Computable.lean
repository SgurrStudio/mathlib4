/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.NumberTheory.Normal.Bridge

import Mathlib.Imported.NormalNumbers.Bridge
import Mathlib.Imported.NormalNumbers.ComputableNormalB
import Mathlib.Imported.NormalNumbers.LevinSparse

/-!
# A computable absolutely normal number

We show that there is an absolutely normal real number whose binary digits are computable
(**Becher and Figueira**, 2002; Turing had sketched such a construction in an unpublished
manuscript).

## Main statements

* `Real.exists_computable_isAbsolutelyNormal`: there is an absolutely normal `x` such that
  `n ↦ digit 2 x n` is computable.

## Proof

This is Trevor Morris's generic derandomization
`NormalNumbers.ComputableNormalB.exists_computable_absNormal`, imported in
`Mathlib/Imported/NormalNumbers`, applied to the binary expansion `ω ↦ ∑ ωᵢ 2⁻ⁱ⁻¹` of a sequence of
fair coins. Its law is the uniform measure on `[0, 1]`, whose Fourier transform at `ξ` has modulus
`∏ₖ |cos (π ξ / 2ᵏ⁺¹)| = |sin (π ξ) / (π ξ)| ≤ 1 / |ξ|` (Viète's product). Morris's theorem gives a
computable coin sequence `e` whose binary expansion `x` is normal in every base, and the binary
digits of `x` are the coins `e`, since a normal number is not a dyadic rational.

## References

* [V. Becher, S. Figueira,
  *An example of a computable absolutely normal number*][BecherFigueira2002]
-/

open MeasureTheory NormalNumbers NormalNumbers.Derandomize

namespace Real.BinaryCoins

/-! ### The binary expansion of a coin sequence and its computable approximations -/

/-- The binary expansion `∑ ωᵢ 2⁻ⁱ⁻¹` of a coin sequence `ω`. -/
noncomputable def binReal (ω : ℕ → Bool) : ℝ := realOfDigits 2 fun i ↦ (ω i).toNat

/-- `2 ^ |p|` times the binary expansion of the prefix `p`. -/
def binNum (p : List Bool) : ℕ :=
  ((List.range p.length).map fun i ↦ (p.getD i false).toNat * 2 ^ (p.length - 1 - i)).sum

/-- The binary expansion of the prefix `p`, a lower approximation of `binReal`. -/
noncomputable def binA (p : List Bool) : ℝ := (binNum p : ℝ) / 2 ^ p.length

/-- The base-`b` floors `⌊binA p * b ^ m⌋₊`. -/
def binΨ (b m : ℕ) (p : List Bool) : ℕ := binNum p * b ^ m / 2 ^ p.length

theorem primrec_toNat : Primrec Bool.toNat :=
  (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq fun c ↦ by cases c <;> rfl

theorem primrec_binNum : Primrec binNum := by
  have hg : Primrec₂ fun (p : List Bool) (i : ℕ) ↦
      (p.getD i false).toNat * 2 ^ (p.length - 1 - i) :=
    (Primrec.nat_mul.comp (primrec_toNat.comp ((Primrec.list_getD false).comp Primrec.fst
      Primrec.snd)) (ComputableNormal.primrec_pow.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst)
          (Primrec.const 1)) Primrec.snd))).to₂
  exact (primrec_sum_map (Primrec.list_range.comp Primrec.list_length) hg).of_eq fun p ↦ rfl

theorem primrec_binΨ : Primrec fun x : ℕ × ℕ × List Bool ↦ binΨ x.1 x.2.1 x.2.2 := by
  have hp : Primrec fun x : ℕ × ℕ × List Bool ↦ x.2.2 := Primrec.snd.comp Primrec.snd
  exact Primrec.nat_div.comp (Primrec.nat_mul.comp (primrec_binNum.comp hp)
    (ComputableNormal.primrec_pow.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
    (ComputableNormal.primrec_pow.comp (Primrec.const 2) (Primrec.list_length.comp hp))

theorem binΨ_eq (b m : ℕ) (p : List Bool) : binΨ b m p = ⌊binA p * (b : ℝ) ^ m⌋₊ := by
  rw [binA, show (binNum p : ℝ) / 2 ^ p.length * (b : ℝ) ^ m =
    ((binNum p * b ^ m : ℕ) : ℝ) / ((2 ^ p.length : ℕ) : ℝ) by push_cast; ring,
    Nat.floor_div_eq_div, binΨ]

theorem binA_nonneg (p : List Bool) : 0 ≤ binA p := by unfold binA; positivity

theorem binA_pre (ω : ℕ → Bool) (D : ℕ) :
    binA (pre ω D) = ∑ i ∈ Finset.range D, ((ω i).toNat : ℝ) / 2 ^ (i + 1) := by
  rw [binA, binNum, length_pre, ComputableNormalB.list_sum_range_map, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  rw [show (pre ω D).getD i false = ω i by simp [pre, List.getD_eq_getElem?_getD, hi']]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
    show D - 1 - i + (i + 1) = D by omega]

theorem summable_bin (ω : ℕ → Bool) : Summable fun i ↦ ((ω i).toNat : ℝ) / 2 ^ (i + 1) := by
  refine Summable.of_nonneg_of_le (fun i ↦ by positivity) (fun i ↦ ?_)
    (summable_geometric_two.mul_left (1 / 2))
  have : ((ω i).toNat : ℝ) ≤ 1 := by exact_mod_cast Bool.toNat_le _
  calc ((ω i).toNat : ℝ) / 2 ^ (i + 1) ≤ 1 / 2 ^ (i + 1) := by gcongr
    _ = 1 / 2 * (1 / 2) ^ i := by rw [pow_succ, one_div_pow]; field_simp

theorem tsum_one_div_two_pow (D : ℕ) : ∑' k : ℕ, (1 : ℝ) / 2 ^ (k + D + 1) = (1 / 2) ^ D := by
  have h : (fun k : ℕ ↦ (1 : ℝ) / 2 ^ (k + D + 1)) = fun k ↦ (1 / 2) ^ (D + 1) * (1 / 2) ^ k := by
    funext k; rw [← pow_add, one_div_pow]; ring_nf
  rw [h, tsum_mul_left, tsum_geometric_two, pow_succ]; ring

/-- The binary expansion splits into the prefix `binA (pre ω D)` and a tail. -/
theorem binReal_eq_binA_add (ω : ℕ → Bool) (D : ℕ) :
    binReal ω = binA (pre ω D) + ∑' k, ((ω (k + D)).toNat : ℝ) / 2 ^ (k + D + 1) := by
  rw [binA_pre, binReal, realOfDigits]
  simp only [Nat.cast_ofNat]
  exact ((summable_bin ω).sum_add_tsum_nat_add D).symm

theorem binA_bounds (ω : ℕ → Bool) (D : ℕ) :
    binA (pre ω D) ≤ binReal ω ∧ binReal ω ≤ binA (pre ω D) + (1 / 2 : ℝ) ^ D := by
  have ht0 : 0 ≤ ∑' k, ((ω (k + D)).toNat : ℝ) / 2 ^ (k + D + 1) :=
    tsum_nonneg fun k ↦ by positivity
  have ht1 : ∑' k, ((ω (k + D)).toNat : ℝ) / 2 ^ (k + D + 1) ≤ (1 / 2) ^ D := by
    rw [← tsum_one_div_two_pow]
    refine ((summable_bin ω).comp_injective (add_left_injective D)).tsum_le_tsum (fun k ↦ ?_)
      ?_
    · have : ((ω (k + D)).toNat : ℝ) ≤ 1 := by exact_mod_cast Bool.toNat_le _
      exact div_le_div_of_nonneg_right this (by positivity)
    · exact (summable_geometric_two.mul_left ((1 / 2) ^ (D + 1))).congr fun k ↦ by
        rw [← pow_add, one_div_pow]; ring_nf
  rw [binReal_eq_binA_add ω D]
  constructor <;> linarith

theorem binReal_eq_bldPoint (ω : ℕ → Bool) :
    binReal ω = LevinSparse.bldPoint Set.univ ω / 2 := by
  rw [LevinSparse.bldPoint, binReal, realOfDigits, ← tsum_div_const]
  congr 1
  funext k
  cases ω k <;> simp [pow_succ, div_eq_mul_inv, mul_comm]

theorem measurable_binReal : Measurable binReal := by
  simp_rw [funext binReal_eq_bldPoint]
  exact (LevinSparse.measurable_bldPoint _).div_const 2

/-! ### Fourier decay of the uniform measure -/

/-- Viète's finite product: `sin y = 2 ^ M sin (y / 2 ^ M) ∏_{0 < k ≤ M} cos (y / 2 ^ k)`. -/
theorem sin_eq_two_pow_mul_prod_cos (y : ℝ) (M : ℕ) :
    sin y = 2 ^ M * sin (y / 2 ^ M) * ∏ k ∈ Finset.Ioc 0 M, cos (y / 2 ^ k) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.prod_Ioc_succ_top (Nat.zero_le M), ih,
      show y / 2 ^ M = 2 * (y / 2 ^ (M + 1)) by rw [pow_succ]; field_simp, sin_two_mul]
    ring

/-- Jordan's inequality, two-sided. -/
theorem mul_abs_le_abs_sin {t : ℝ} (ht : |t| ≤ π / 2) : 2 / π * |t| ≤ |sin t| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact (mul_le_sin h ht).trans (le_abs_self _)
  · rw [abs_of_nonpos h] at ht ⊢
    have := mul_le_sin (neg_nonneg.2 h) ht
    rw [sin_neg] at this
    exact this.trans (neg_le_abs _)

/-- The Fourier transform of the uniform measure on `[0, 1]` decays like `1 / |ξ|`. -/
theorem norm_integral_ee_binReal_le (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖∫ ω, DecayAeNormal.ee (ξ * binReal ω) ∂coins‖ ≤ 1 * |ξ| ^ (-1 : ℝ) := by
  classical
  have hc : coins = ExplicitSquare.coinMeasure := rfl
  have h1 : (fun ω ↦ DecayAeNormal.ee (ξ * binReal ω)) =
      fun ω ↦ DecayAeNormal.ee (ξ / 2 * LevinSparse.bldPoint Set.univ ω) := by
    funext ω; rw [binReal_eq_bldPoint]; ring_nf
  rw [h1, hc, one_mul, rpow_neg_one]
  refine (LevinSparse.norm_integral_ee_bldPoint_le Set.univ (ξ / 2)).trans ?_
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt |ξ| (one_lt_two : (1 : ℝ) < 2)
  set y := π * (ξ / 2) with hy
  set P := ∏ k ∈ Finset.Ioc 0 M, cos (y / 2 ^ k)
  have hR : LevinSparse.rieszTail Set.univ 0 (ξ / 2) ≤ |P| := by
    rw [Finset.abs_prod]
    unfold LevinSparse.rieszTail
    refine (ciInf_le ⟨0, ?_⟩ M).trans_eq ?_
    · rintro _ ⟨N, rfl⟩
      exact Finset.prod_nonneg fun _ _ ↦ abs_nonneg _
    · simp [hy]
  refine hR.trans ?_
  have h2M : (0 : ℝ) < 2 ^ M := by positivity
  have ht : |y / 2 ^ M| ≤ π / 2 := by
    rw [abs_div, abs_of_pos h2M, div_le_iff₀ h2M, hy, abs_mul, abs_of_pos pi_pos, abs_div,
      abs_two]
    have := pi_pos
    nlinarith
  have hj := mul_abs_le_abs_sin ht
  have hv := congrArg abs (sin_eq_two_pow_mul_prod_cos y M)
  rw [abs_mul, abs_mul, abs_of_pos h2M] at hv
  have hξy : |ξ| = 2 ^ M * (2 / π * |y / 2 ^ M|) := by
    rw [abs_div, abs_of_pos h2M, hy, abs_mul, abs_of_pos pi_pos, abs_div, abs_two]
    field_simp
  have hle : |ξ| * |P| ≤ 1 := by
    calc |ξ| * |P| ≤ 2 ^ M * |sin (y / 2 ^ M)| * |P| := by
          rw [hξy]; gcongr
      _ = |sin y| := hv.symm
      _ ≤ 1 := abs_sin_le_one y
  rw [inv_eq_one_div, le_div_iff₀ (abs_pos.2 hξ)]
  linarith

end Real.BinaryCoins

public section

namespace Real

open BinaryCoins in
/-- There is a **computable absolutely normal number**: an absolutely normal real whose binary
digits are a computable sequence. -/
theorem exists_computable_isAbsolutelyNormal :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ Computable (fun n ↦ digit 2 x n) := by
  obtain ⟨e, hce, hn⟩ := ComputableNormalB.exists_computable_absNormal binΨ primrec_binΨ binA
    binΨ_eq binA_nonneg binReal measurable_binReal binA_bounds one_pos one_pos
    norm_integral_ee_binReal_le
  have habs : IsAbsolutelyNormal (binReal e) := fun b hb ↦ (isNormalIn_iff_isNormal b _).2 (hn b hb)
  have hlt : ∀ i, (e i).toNat < 2 := fun i ↦ Bool.toNat_lt _
  -- A normal number is irrational, so its binary digits do not end in `1, 1, 1, …`.
  have hp : ProperDigits 2 fun i ↦ (e i).toNat := by
    intro N
    by_contra! h
    refine (habs 2 le_rfl).irrational le_rfl ⟨binNum (pre e N) / 2 ^ N + (1 / 2) ^ N, ?_⟩
    have ht : ∑' k, ((e (k + N)).toNat : ℝ) / 2 ^ (k + N + 1) = (1 / 2) ^ N := by
      rw [← tsum_one_div_two_pow]
      refine tsum_congr fun k ↦ ?_
      rw [h (k + N) (by omega)]
      norm_num
    rw [binReal_eq_binA_add e N, ht, binA, length_pre]
    push_cast
    rfl
  have hdig : ∀ n, digit 2 (binReal e) n = (e n).toNat := fun n ↦ by
    rw [← digitOf_fract, binReal, Int.fract_eq_self.2 (Set.mem_Ico.1
      (realOfDigits_mem_Ico 2 le_rfl _ hlt hp)), digitOf_realOfDigits 2 le_rfl _ hlt hp]
  exact ⟨binReal e, habs, (primrec_toNat.to_comp.comp hce).of_eq fun n ↦ (hdig n).symm⟩

end Real

end
