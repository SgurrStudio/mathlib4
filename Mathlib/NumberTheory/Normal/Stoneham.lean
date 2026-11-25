/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.NumberTheory.Normal.PiatetskiShapiro
public import Mathlib.NumberTheory.Normal.Rational

/-!
# Stoneham numbers are normal

For coprime integers `b, c ≥ 2` the *Stoneham number* is
`α_{b,c} = ∑_{k ≥ 1} 1 / (c ^ k * b ^ (c ^ k))`.
**Stoneham** (1973) proved that `α_{b,c}` is normal in base `b` when `c` is an odd prime and `b`
is a primitive root modulo `c ^ 2`. **Bailey and Crandall** (2002) extended this to all coprime
`b, c ≥ 2`, and **Bailey and Misiurewicz** (2006) gave a short proof via a "hot spot" form of
**Piatetski-Shapiro's normality criterion**: `x` is normal in base `b` as soon as every block
of `k` digits has upper frequency at most `C * b⁻ᵏ` for a constant `C` independent of the block.

## Main definitions

* `Real.stoneham b c`: the Stoneham number `α_{b,c}`.

## Main statements

* `Real.isNormalIn_stoneham`: Stoneham numbers are normal (Bailey–Crandall).

## Proof

Write `α = α_{b,c}` and fix a level `j ≥ 1`. For `c ^ j ≤ n < c ^ (j + 1)`,
`b ^ n * α ≡ r_n / c ^ j + T_n (mod 1)`, where `r_n = stonehamNum b c j n mod c ^ j` satisfies
`r_{n + d} ≡ b ^ d * r_n` and is a unit modulo `c ^ j`, and the tail `T_n` is at most `2 b⁻ᴷ`
unless `n` is among the last `K` positions of the level. The lifting-the-exponent lemma shows that
the order of `b` modulo `c ^ j` is at least `c ^ j / E` for a constant `E`
(`Nat.exists_dvd_mul_of_dvd_pow_sub_one`), so each residue `r` recurs at most once every
`c ^ j / E` steps. A block of `k` digits forces `r_n / c ^ j` into an interval of length
about `b⁻ᵏ`, which holds about `c ^ j b⁻ᵏ` residues. Summing over levels, every block has upper
frequency at most `(E + 2) b⁻ᵏ`, and Piatetski-Shapiro's criterion concludes.

## References

* [R. G. Stoneham, *On absolute (j, ε)-normality in the rational fractions with applications to
  normal numbers*][Stoneham1973]
* [D. H. Bailey, R. E. Crandall, *Random generators and normal numbers*][BaileyCrandall2002]
* [D. H. Bailey, M. Misiurewicz, *A strong hot spot theorem*][BaileyMisiurewicz2006]
* [I. I. Piatetski-Shapiro, *On the laws of distribution of the fractional parts of an
  exponential function*][PiatetskiShapiro1951]
-/

@[expose] public section

open Filter Topology

namespace Nat

/-- Lifting the exponent: if `p ∣ g - 1` (and `4 ∣ g - 1` when `p = 2`), then `g ^ d - 1` and
`(g - 1) * d` have the same `p`-adic valuation. -/
theorem emultiplicity_pow_sub_one_eq {p g : ℕ} (hp : p.Prime) (hg : 1 ≤ g) (hpg : p ∣ g - 1)
    (h4 : p = 2 → 4 ∣ g - 1) (d : ℕ) :
    emultiplicity p (g ^ d - 1) = emultiplicity p ((g - 1) * d) := by
  have hpg' : ¬p ∣ g := fun h ↦ by
    have := (Nat.dvd_sub_iff_right (Nat.sub_le g 1) h).2 hpg
    rw [Nat.sub_sub_self hg] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rw [hp.emultiplicity_mul]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have h4' : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have := Int.natCast_dvd_natCast.2 (h4 rfl); push_cast [Nat.cast_sub hg] at this; exact this
    have h2 : ¬(2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hpg'
    have := Int.two_pow_sub_pow' (y := 1) d h4' h2
    rw [one_pow] at this
    rw [← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity,
      ← Int.natCast_emultiplicity]
    push_cast [Nat.cast_sub hg, Nat.cast_sub (Nat.one_le_pow d g hg)]
    exact this
  · simpa using Nat.emultiplicity_pow_sub_pow hp hodd (y := 1) (by simpa using hpg) hpg' d

/-- If `b` is coprime to `c`, there is `E > 0` such that `c ^ j ∣ b ^ d - 1` forces
`c ^ j ∣ E * d`: the multiplicative order of `b` modulo `c ^ j` is at least `c ^ j / E`. -/
theorem exists_dvd_mul_of_dvd_pow_sub_one {b c : ℕ} (hb : 2 ≤ b) (hc : 1 ≤ c)
    (hbc : b.Coprime c) : ∃ E : ℕ, 0 < E ∧ ∀ j d : ℕ, c ^ j ∣ b ^ d - 1 → c ^ j ∣ E * d := by
  set h := b ^ Nat.totient c
  have hh : 2 ≤ h := hb.trans (Nat.le_self_pow (Nat.totient_pos.2 hc).ne' b)
  have hg : 1 ≤ h ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcg : c ∣ h ^ 2 - 1 := by
    have : h ^ 2 ≡ 1 [MOD c] := by simpa using (Nat.ModEq.pow_totient hbc).pow 2
    exact (Nat.modEq_iff_dvd' hg).1 this.symm
  refine ⟨h ^ 2 - 1, by nlinarith [Nat.sub_add_cancel hg], fun j d hd ↦ ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp
  have hgd : c ^ j ∣ (h ^ 2) ^ d - 1 := by
    refine hd.trans ?_
    have := Nat.sub_dvd_pow_sub_pow (b ^ d) 1 (Nat.totient c * 2)
    convert this using 2
    · simp only [h, ← pow_mul]; ring_nf
    · simp
  have hE : (h ^ 2 - 1) * d ≠ 0 := mul_ne_zero (by nlinarith [Nat.sub_add_cancel hg]) hd0.ne'
  refine (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ (by omega)) hE).1 fun p hp ↦ ?_
  by_cases hpc : p ∣ c
  · refine (hp.pow_dvd_iff_le_factorization hE).1 ?_
    have h1 : p ^ (c ^ j).factorization p ∣ (h ^ 2) ^ d - 1 :=
      (Nat.ordProj_dvd _ _).trans hgd
    rw [pow_dvd_iff_le_emultiplicity, emultiplicity_pow_sub_one_eq hp hg (hpc.trans hcg) _ d] at h1
    · exact pow_dvd_iff_le_emultiplicity.2 h1
    rintro rfl
    have hodd : Odd h :=
      (Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right hpc hbc)).symm.odd_of_left
    exact Nat.dvd_trans (by norm_num) (Nat.eight_dvd_sq_sub_one_of_odd hodd)
  · simp [Nat.factorization_eq_zero_of_not_dvd hpc]

end Nat

namespace Real

variable {b c : ℕ}

/-- The *Stoneham number* `α_{b,c} = ∑_{k ≥ 1} 1 / (c ^ k * b ^ (c ^ k))`. -/
noncomputable def stoneham (b c : ℕ) : ℝ :=
  ∑' k : ℕ, ((c : ℝ) ^ (k + 1) * (b : ℝ) ^ (c ^ (k + 1)))⁻¹

/-- The numerator `∑_{i < j} c ^ (j - 1 - i) * b ^ (n - c ^ (i + 1))` of the first `j` terms of
`b ^ n * α_{b,c}`, which equal `stonehamNum b c j n / c ^ j`. -/
def stonehamNum (b c j n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, c ^ (j - 1 - i) * b ^ (n - c ^ (i + 1))

theorem stonehamNum_add (hc : 1 ≤ c) {j n : ℕ} (hn : c ^ j ≤ n) (d : ℕ) :
    stonehamNum b c j (n + d) = b ^ d * stonehamNum b c j n := by
  rw [stonehamNum, stonehamNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have : c ^ (i + 1) ≤ n :=
    (Nat.pow_le_pow_right hc (Finset.mem_range.1 hi)).trans hn
  rw [show n + d - c ^ (i + 1) = d + (n - c ^ (i + 1)) by omega, pow_add]
  ring

theorem coprime_stonehamNum (hbc : b.Coprime c) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    (stonehamNum b c j n).Coprime c := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have hdvd : c ∣ ∑ i ∈ Finset.range j, c ^ (j + 1 - 1 - i) * b ^ (n - c ^ (i + 1)) :=
    Finset.dvd_sum fun i hi ↦ Dvd.dvd.mul_right
      (dvd_pow_self c (by have := Finset.mem_range.1 hi; omega)) _
  obtain ⟨q, hq⟩ := hdvd
  rw [stonehamNum, Finset.sum_range_succ, hq, Nat.coprime_mul_left_add_left]
  simpa using hbc.pow_left _

/-- Two positions with the same residue `stonehamNum b c j n mod c ^ j` differ by a multiple of
the order of `b` modulo `c ^ j`. -/
theorem dvd_pow_sub_one_of_stonehamNum_mod_eq (hb : 1 ≤ b) (hbc : b.Coprime c) (hc : 1 ≤ c)
    {j n : ℕ}
    (hj : 1 ≤ j) (hn : c ^ j ≤ n) {d : ℕ}
    (h : stonehamNum b c j n % c ^ j = stonehamNum b c j (n + d) % c ^ j) :
    c ^ j ∣ b ^ d - 1 := by
  rw [stonehamNum_add hc hn] at h
  have h' : 1 * stonehamNum b c j n ≡ b ^ d * stonehamNum b c j n [MOD c ^ j] := by
    rw [one_mul]; exact h
  have := Nat.ModEq.cancel_right_of_coprime
    (Nat.Coprime.pow_right j (coprime_stonehamNum hbc hj n)).symm h'
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hb)).1 this

theorem stoneham_term_le (hb : 1 ≤ b) (hc : 2 ≤ c) (k : ℕ) :
    ((c : ℝ) ^ (k + 1) * (b : ℝ) ^ (c ^ (k + 1)))⁻¹ ≤ (1 / 2) ^ k := by
  rw [one_div, inv_pow]
  refine inv_anti₀ (by positivity) ?_
  have h1 : (1 : ℝ) ≤ (b : ℝ) ^ (c ^ (k + 1)) := one_le_pow₀ (by exact_mod_cast hb)
  have h2 : (2 : ℝ) ^ k ≤ (c : ℝ) ^ (k + 1) := by
    calc (2 : ℝ) ^ k ≤ (c : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hc) k
      _ ≤ (c : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by norm_cast; omega) (Nat.le_succ k)
  nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k]

theorem summable_stoneham (hb : 1 ≤ b) (hc : 2 ≤ c) :
    Summable fun k : ℕ ↦ ((c : ℝ) ^ (k + 1) * (b : ℝ) ^ (c ^ (k + 1)))⁻¹ :=
  summable_geometric_two.of_nonneg_of_le (fun _ ↦ by positivity) (stoneham_term_le hb hc)

/-- `b ^ n * α_{b,c}` splits as `stonehamNum b c j n / c ^ j` plus a tail. -/
theorem stoneham_mul_pow_eq (hb : 1 ≤ b) (hc : 2 ≤ c) {j n : ℕ} (hn : c ^ j ≤ n) :
    stoneham b c * (b : ℝ) ^ n = (stonehamNum b c j n : ℝ) / (c : ℝ) ^ j +
      ∑' k : ℕ, ((c : ℝ) ^ (k + j + 1) * (b : ℝ) ^ (c ^ (k + j + 1)))⁻¹ * (b : ℝ) ^ n := by
  have hs := summable_stoneham hb hc
  rw [stoneham, ← hs.sum_add_tsum_nat_add j, add_mul, Finset.sum_mul, ← tsum_mul_right]
  congr 1
  rw [stonehamNum, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have : c ^ (i + 1) ≤ n := (Nat.pow_le_pow_right (by omega) hi').trans hn
  have hc0 : (c : ℝ) ≠ 0 := by norm_cast; omega
  have hb0 : (b : ℝ) ≠ 0 := by norm_cast; omega
  rw [show (b : ℝ) ^ n = (b : ℝ) ^ (n - c ^ (i + 1)) * (b : ℝ) ^ (c ^ (i + 1)) by
      rw [← pow_add, Nat.sub_add_cancel this],
    show (c : ℝ) ^ j = (c : ℝ) ^ (j - 1 - i) * (c : ℝ) ^ (i + 1) by
      rw [← pow_add]; congr 1; omega]
  push_cast
  field_simp

/-- The tail of `b ^ n * α_{b,c}` is at most `2 * b⁻ᴷ` when `n + K ≤ c ^ (j + 1)`. -/
theorem stoneham_tail_le (hb : 2 ≤ b) (hc : 2 ≤ c) {j n K : ℕ} (hK : n + K ≤ c ^ (j + 1)) :
    ∑' k : ℕ, ((c : ℝ) ^ (k + j + 1) * (b : ℝ) ^ (c ^ (k + j + 1)))⁻¹ * (b : ℝ) ^ n ≤
      2 * ((b : ℝ) ^ K)⁻¹ := by
  have hs := ((summable_nat_add_iff j).2 (summable_stoneham (b := b) (by omega) hc)).mul_right
    ((b : ℝ) ^ n)
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hterm : ∀ k : ℕ, ((c : ℝ) ^ (k + j + 1) * (b : ℝ) ^ (c ^ (k + j + 1)))⁻¹ * (b : ℝ) ^ n ≤
      ((b : ℝ) ^ K)⁻¹ * (1 / 2) ^ k := fun k ↦ by
    have hck : n + K + k ≤ c ^ (k + j + 1) := by
      have h1 : k + 1 ≤ c ^ k := Nat.lt_pow_self (by omega)
      have h2 : 1 ≤ c ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
      rw [show k + j + 1 = k + (j + 1) by ring, pow_add]
      nlinarith
    have hX : (b : ℝ) ^ n * (b : ℝ) ^ K * 2 ^ k ≤
        (c : ℝ) ^ (k + j + 1) * (b : ℝ) ^ (c ^ (k + j + 1)) := by
      calc (b : ℝ) ^ n * (b : ℝ) ^ K * 2 ^ k ≤ (b : ℝ) ^ n * (b : ℝ) ^ K * (b : ℝ) ^ k := by
            gcongr
        _ = (b : ℝ) ^ (n + K + k) := by rw [pow_add, pow_add]
        _ ≤ (b : ℝ) ^ (c ^ (k + j + 1)) := pow_le_pow_right₀ (by linarith) hck
        _ ≤ (c : ℝ) ^ (k + j + 1) * (b : ℝ) ^ (c ^ (k + j + 1)) :=
            le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_cast; omega))
    calc ((c : ℝ) ^ (k + j + 1) * (b : ℝ) ^ (c ^ (k + j + 1)))⁻¹ * (b : ℝ) ^ n
        ≤ ((b : ℝ) ^ n * (b : ℝ) ^ K * 2 ^ k)⁻¹ * (b : ℝ) ^ n := by
          gcongr
      _ = ((b : ℝ) ^ K)⁻¹ * (1 / 2) ^ k := by
          have : (b : ℝ) ^ n ≠ 0 := by positivity
          rw [one_div, inv_pow]
          field_simp
  calc _ ≤ ∑' k : ℕ, ((b : ℝ) ^ K)⁻¹ * (1 / 2) ^ k :=
        hs.tsum_le_tsum hterm (summable_geometric_two.mul_left _)
    _ = 2 * ((b : ℝ) ^ K)⁻¹ := by rw [tsum_mul_left, tsum_geometric_two, mul_comm]


/-- An interval `[u, u + h)` contains at most `h + 1` natural numbers. -/
theorem card_filter_mem_Ico_le (M : ℕ) (u : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    (((Finset.range M).filter fun r : ℕ ↦ u ≤ r ∧ (r : ℝ) < u + h).card : ℝ) ≤ h + 1 := by
  have hsub : ((Finset.range M).filter fun r : ℕ ↦ u ≤ r ∧ (r : ℝ) < u + h) ⊆
      Finset.Ico ⌈u⌉₊ ⌈u + h⌉₊ := fun r hr ↦ by
    simp only [Finset.mem_filter] at hr
    exact Finset.mem_Ico.2 ⟨Nat.ceil_le.2 hr.2.1, Nat.lt_ceil.2 hr.2.2⟩
  refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
  rw [Nat.card_Ico]
  rcases le_or_gt ⌈u + h⌉₊ ⌈u⌉₊ with h1 | h1
  · rw [Nat.sub_eq_zero_of_le h1, Nat.cast_zero]; linarith
  · rw [Nat.cast_sub h1.le]
    have h2 : 0 < u + h := Nat.ceil_pos.1 (by omega)
    linarith [Nat.ceil_lt_add_one h2.le, Nat.le_ceil u]

/-- A set of naturals in `[a, N)` whose distinct elements are at distance at least `G / E` has
at most `(N - a) * E / G + 1` elements. -/
theorem card_le_of_le_mul_sub {s : Finset ℕ} {a N G E : ℕ} (hG : 0 < G)
    (hs : ∀ n ∈ s, a ≤ n ∧ n < N) (hgap : ∀ n ∈ s, ∀ m ∈ s, n < m → G ≤ E * (m - n)) :
    s.card ≤ (N - a) * E / G + 1 := by
  have key : ∀ n ∈ s, ∀ m ∈ s, n < m → (n - a) * E / G ≠ (m - a) * E / G := by
    intro n hn m hm hnm heq
    have h1 := hgap n hn m hm hnm
    have h2 : (m - a) * E = (n - a) * E + E * (m - n) := by
      rw [show m - a = (n - a) + (m - n) by have := (hs n hn).1; omega]; ring
    have h3 := Nat.lt_div_mul_add (a := (m - a) * E) hG
    have h4 := Nat.div_mul_le_self ((n - a) * E) G
    rw [← heq] at h3
    omega
  calc s.card ≤ (Finset.range ((N - a) * E / G + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun n ↦ (n - a) * E / G) (fun n hn ↦ ?_) ?_
        · simp only [Finset.coe_range, Set.mem_Iio]
          have := (hs n hn).2
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
        · intro n hn m hm hnm
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact key n hn m hm h hnm
          · exact key m hm n hn h hnm.symm
    _ = (N - a) * E / G + 1 := Finset.card_range _

open Classical in
/-- The residues `r < M` such that `r / M + t` lies in the `V`-th of `B` equal subintervals of
`[0, 1)` (mod `1`) for some `t ∈ [0, δ]` are at most `M * (1 / B + 2 δ) + 2` in number. -/
theorem card_filter_exists_floor_fract_le {M : ℕ} (hM : 0 < M) {B δ : ℝ} (hB : 0 < B)
    (hδ : 0 ≤ δ) (V : ℕ) :
    (((Finset.range M).filter fun r : ℕ ↦ ∃ t : ℝ, 0 ≤ t ∧ t ≤ δ ∧
      ⌊Int.fract ((r : ℝ) / M + t) * B⌋₊ = V).card : ℝ) ≤ M * (B⁻¹ + 2 * δ) + 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set u₁ : ℝ := M * (V / B - δ)
  set h₁ : ℝ := M * (B⁻¹ + δ)
  set u₂ : ℝ := M * (1 - δ)
  set h₂ : ℝ := M * δ
  have hsub : ((Finset.range M).filter fun r : ℕ ↦ ∃ t : ℝ, 0 ≤ t ∧ t ≤ δ ∧
      ⌊Int.fract ((r : ℝ) / M + t) * B⌋₊ = V) ⊆
      ((Finset.range M).filter fun r : ℕ ↦ u₁ ≤ r ∧ (r : ℝ) < u₁ + h₁) ∪
      ((Finset.range M).filter fun r : ℕ ↦ u₂ ≤ r ∧ (r : ℝ) < u₂ + h₂) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrM, t, ht0, htδ, hV⟩ := hr
    have hrM' : (r : ℝ) < M := by exact_mod_cast hrM
    set z := (r : ℝ) / M with hz
    have hrz : (r : ℝ) = z * M := by rw [hz, div_mul_cancel₀ _ hM'.ne']
    have hz0 : 0 ≤ z := by positivity
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    rcases lt_or_ge (z + t) 1 with h | h
    · left
      rw [Int.fract_eq_self.2 ⟨by positivity, h⟩,
        Nat.floor_eq_iff (by positivity)] at hV
      have h1 : (V : ℝ) / B ≤ z + t := (div_le_iff₀ hB).2 hV.1
      have h2 : z + t < (V + 1) / B := (lt_div_iff₀ hB).2 hV.2
      refine ⟨hrM, ?_, ?_⟩
      · simp only [u₁, hrz]; nlinarith
      · simp only [u₁, h₁, hrz]
        have : (V : ℝ) / B - δ + (B⁻¹ + δ) = (V + 1) / B := by field_simp; ring
        rw [← mul_add, this, mul_comm z]
        exact mul_lt_mul_of_pos_left (by linarith) hM'
    · right
      refine ⟨hrM, ?_, ?_⟩
      · simp only [u₂, hrz]; nlinarith
      · simp only [u₂, h₂]; linarith
  refine (Nat.cast_le.2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))).trans ?_
  push_cast
  have := card_filter_mem_Ico_le M u₁ (h := h₁) (by positivity)
  have := card_filter_mem_Ico_le M u₂ (h := h₂) (by positivity)
  simp only [h₁, h₂] at *
  nlinarith

open Classical in
/-- The positions `n ∈ [c ^ j, N)`, `N ≤ c ^ (j + 1)`, at which the base-`b` block of length `k`
of `α_{b,c}` is `V`: apart from the last `K` positions before `c ^ (j + 1)`, the residue of
`stonehamNum b c j n` modulo `c ^ j` lies in a set of at most `c ^ j * (b⁻ᵏ + 2 δ) + 2`
residues, and each residue recurs only after `c ^ j / E` steps. -/
theorem card_filter_Ico_blockCodeAt_le (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) {E : ℕ}
    (hE0 : 0 < E) (hE : ∀ j d : ℕ, c ^ j ∣ b ^ d - 1 → c ^ j ∣ E * d) (k V K : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hK : 2 * ((b : ℝ) ^ K)⁻¹ ≤ δ) {j N : ℕ} (hj : 1 ≤ j) (hN : N ≤ c ^ (j + 1)) :
    (((Finset.Ico (c ^ j) N).filter fun n ↦
      blockCodeAt b k (stoneham b c) n = (V : ℤ)).card : ℝ) ≤
      K + ((c : ℝ) ^ j * (((b : ℝ) ^ k)⁻¹ + 2 * δ) + 2) * (((N - c ^ j) * E / c ^ j : ℕ) + 1) := by
  set M := c ^ j with hMdef
  have hM : 0 < M := pow_pos (by omega) j
  have hMc : ((M : ℕ) : ℝ) = (c : ℝ) ^ j := by simp [M]
  set R := (Finset.range M).filter fun r : ℕ ↦ ∃ t : ℝ, 0 ≤ t ∧ t ≤ δ ∧
    ⌊Int.fract ((r : ℝ) / M + t) * (b : ℝ) ^ k⌋₊ = V
  set piece : ℕ → Finset ℕ := fun s ↦
    (Finset.Ico M N).filter fun n ↦ stonehamNum b c j n % M = s
  have hsub : ((Finset.Ico M N).filter fun n ↦ blockCodeAt b k (stoneham b c) n = (V : ℤ)) ⊆
      Finset.Ico (c ^ (j + 1) - K) (c ^ (j + 1)) ∪ R.biUnion piece := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨hn1, hn2⟩, hV⟩ := hn
    rcases lt_or_ge (c ^ (j + 1)) (n + K) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨stonehamNum b c j n % M, ?_,
      Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hn1, hn2⟩, rfl⟩⟩)
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hM), _,
      tsum_nonneg fun _ ↦ by positivity, (stoneham_tail_le hb hc h).trans hK, ?_⟩
    rw [blockCodeAt_eq (by omega), Nat.cast_inj, stoneham_mul_pow_eq (by omega) hc hn1] at hV
    have : (stonehamNum b c j n : ℝ) / (c : ℝ) ^ j = ((stonehamNum b c j n / M : ℕ) : ℝ) +
        ((stonehamNum b c j n % M : ℕ) : ℝ) / (M : ℝ) := by
      rw [← hMc]
      conv_lhs => rw [← Nat.div_add_mod (stonehamNum b c j n) M]
      have : (M : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
    rwa [this, add_assoc, Int.fract_natCast_add] at hV
  have hpiece : ∀ s, (piece s).card ≤ (N - M) * E / M + 1 := fun s ↦ by
    refine card_le_of_le_mul_sub hM (fun n hn ↦ ?_) fun n hn m hm hnm ↦ ?_
    · have := (Finset.mem_filter.1 hn).1; exact Finset.mem_Ico.1 this
    · simp only [piece, Finset.mem_filter, Finset.mem_Ico] at hn hm
      have hd := dvd_pow_sub_one_of_stonehamNum_mod_eq (by omega) hbc (by omega) hj hn.1.1
        (d := m - n) (by rw [Nat.add_sub_cancel' hnm.le, hn.2, hm.2])
      exact Nat.le_of_dvd (Nat.mul_pos hE0 (by omega)) (hE j _ hd)
  have hcard : ((Finset.Ico M N).filter fun n ↦
      blockCodeAt b k (stoneham b c) n = (V : ℤ)).card ≤ K + R.card * ((N - M) * E / M + 1) := by
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    gcongr
    · rw [Nat.card_Ico]; omega
    · exact Finset.card_biUnion_le.trans (Finset.sum_le_card_nsmul _ _ _ fun s _ ↦ hpiece s)
  have hR := card_filter_exists_floor_fract_le hM (B := (b : ℝ) ^ k) (by positivity) hδ V
  replace hR : (R.card : ℝ) ≤ (c : ℝ) ^ j * (((b : ℝ) ^ k)⁻¹ + 2 * δ) + 2 :=
    hR.trans_eq (by rw [hMc])
  refine (Nat.cast_le.2 hcard).trans ?_
  push_cast
  gcongr

/-- `(j + 1) / 2 ^ j → 0`. -/
theorem tendsto_succ_div_two_pow :
    Tendsto (fun j : ℕ ↦ ((j : ℝ) + 1) / 2 ^ j) atTop (𝓝 0) := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (r := 2) one_lt_two
  have h2 : Tendsto (fun j : ℕ ↦ 1 / (2 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa [one_div, inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  simpa [add_div] using h1.add h2

/-- **Bailey–Crandall**: for coprime `b, c ≥ 2` the Stoneham number `α_{b,c}` is normal in
base `b`. -/
theorem isNormalIn_stoneham (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) :
    IsNormalIn b (stoneham b c) := by
  classical
  obtain ⟨E, hE0, hE⟩ := Nat.exists_dvd_mul_of_dvd_pow_sub_one hb (by omega) hbc
  refine isNormalIn_of_eventually_le hb (C := E + 2) fun k w ε hε ↦ ?_
  set V : ℕ := (blockCode w : ℕ)
  set F : ℕ → ℕ := fun N ↦
    ((Finset.range N).filter fun n ↦ blockCodeAt b k (stoneham b c) n = (V : ℤ)).card
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  set β : ℝ := ((b : ℝ) ^ k)⁻¹
  have hβ : 0 < β := by positivity
  set δ : ℝ := ε / (6 * (E + 2))
  have hδ : 0 < δ := by positivity
  set ρ : ℝ := β + 3 * δ
  -- the tail cut-off `K` and the starting level `M₀`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * ((b : ℝ) ^ K)⁻¹ ≤ δ := by
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / δ)
    refine ⟨K, ?_⟩
    have : (K : ℝ) < (b : ℝ) ^ K := by exact_mod_cast Nat.lt_pow_self (by omega)
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hK
    nlinarith
  obtain ⟨M₀, hM₀1, hM₀⟩ : ∃ M₀ : ℕ, 1 ≤ M₀ ∧ 2 ≤ δ * (c : ℝ) ^ M₀ := by
    obtain ⟨M, hM⟩ := exists_nat_gt (2 / δ)
    refine ⟨M + 1, by omega, ?_⟩
    have : (M : ℝ) + 1 < (c : ℝ) ^ (M + 1) := by exact_mod_cast Nat.lt_pow_self (by omega)
    rw [div_lt_iff₀ hδ] at hM
    nlinarith
  have hsplit : ∀ a N, a ≤ N → (F N : ℝ) ≤ F a + ((Finset.Ico a N).filter fun n ↦
      blockCodeAt b k (stoneham b c) n = (V : ℤ)).card := fun a N h ↦ by
    simp only [F]
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) h, Finset.filter_union]
    exact_mod_cast Finset.card_union_le _ _
  -- the bound on one level `[c ^ j, N)`
  have hlevel : ∀ j N, M₀ ≤ j → c ^ j ≤ N → N ≤ c ^ (j + 1) →
      (F N : ℝ) ≤ F (c ^ j) + K + ρ * (E * (N - c ^ j : ℝ) + c ^ j) := fun j N hj h1 h2 ↦ by
    refine (hsplit _ _ h1).trans ?_
    have := card_filter_Ico_blockCodeAt_le hb hc hbc hE0 hE k V K hδ.le hK (by omega) h2
    have hX : (0 : ℝ) < (c : ℝ) ^ j := by positivity
    have hXM : δ * (c : ℝ) ^ M₀ ≤ δ * (c : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hj) hδ.le
    have hdiv : (((N - c ^ j) * E / c ^ j : ℕ) : ℝ) ≤ E * (N - c ^ j : ℝ) / (c : ℝ) ^ j := by
      refine Nat.cast_div_le.trans_eq ?_
      push_cast [Nat.cast_sub h1]
      ring_nf
    have hY : 0 ≤ E * (N - c ^ j : ℝ) := by
      have : ((c ^ j : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
      push_cast at this
      have : (0 : ℝ) ≤ E := by positivity
      nlinarith
    have key : ((c : ℝ) ^ j * (β + 2 * δ) + 2) * (E * (N - c ^ j : ℝ) / (c : ℝ) ^ j + 1) ≤
        ρ * (E * (N - c ^ j : ℝ) + c ^ j) := by
      rw [show ((c : ℝ) ^ j * (β + 2 * δ) + 2) * (E * (N - c ^ j : ℝ) / (c : ℝ) ^ j + 1) =
          (β + 2 * δ + 2 / (c : ℝ) ^ j) * (E * (N - c ^ j : ℝ) + c ^ j) by field_simp]
      have : 2 / (c : ℝ) ^ j ≤ δ := by rw [div_le_iff₀ hX]; linarith
      gcongr
      simp only [ρ]
      linarith
    have : (((Finset.Ico (c ^ j) N).filter fun n ↦
        blockCodeAt b k (stoneham b c) n = (V : ℤ)).card : ℝ) ≤
        K + ρ * (E * (N - c ^ j : ℝ) + c ^ j) := by
      refine this.trans ?_
      have : ((c : ℝ) ^ j * (β + 2 * δ) + 2) * ((((N - c ^ j) * E / c ^ j : ℕ) : ℝ) + 1) ≤
          ((c : ℝ) ^ j * (β + 2 * δ) + 2) * (E * (N - c ^ j : ℝ) / (c : ℝ) ^ j + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith [key]
    linarith
  have hρ : 0 ≤ ρ := by positivity
  have hF : ∀ N, (F N : ℝ) ≤ N := fun N ↦ by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range N).le
  -- summing over the levels `M₀ ≤ j`
  have hsum : ∀ j, M₀ ≤ j → ∀ N, c ^ M₀ ≤ N → N ≤ c ^ (j + 1) →
      (F N : ℝ) ≤ c ^ M₀ + (j + 1) * K + ρ * (E * N + 2 * c ^ j) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro N h1 h2
      have := hlevel M₀ N le_rfl h1 h2
      have := hF (c ^ M₀)
      have : (0 : ℝ) ≤ E * (c : ℝ) ^ M₀ := by positivity
      push_cast at *
      have : (0 : ℝ) ≤ M₀ * K := by positivity
      nlinarith
    | succ j hj ih =>
      intro N h1 h2
      rcases le_or_gt N (c ^ (j + 1)) with h | h
      · have := ih N h1 h
        have : (c : ℝ) ^ j ≤ (c : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
        have : (0 : ℝ) ≤ K := by positivity
        push_cast
        nlinarith
      · have h3 := hlevel (j + 1) N (by omega) h.le h2
        have h4 := ih (c ^ (j + 1)) ((Nat.pow_le_pow_right (by omega) (by omega)).trans le_rfl)
          le_rfl
        have : 2 * (c : ℝ) ^ j ≤ (c : ℝ) ^ (j + 1) := by
          rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < c by linarith) j]
        push_cast at *
        nlinarith
  -- eventually the error terms are at most `ε / 2`
  set η : ℝ := ε / (4 * (K + 1))
  have hη : 0 < η := by positivity
  have hlog : Tendsto (fun N : ℕ ↦ Nat.log c N) atTop atTop :=
    tendsto_atTop_atTop.2 fun M ↦ ⟨c ^ M, fun N hN ↦ Nat.le_log_of_pow_le (by omega) hN⟩
  have E1 := (tendsto_succ_div_two_pow.comp hlog).eventually (gt_mem_nhds hη)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 * (c : ℝ) ^ M₀ / ε)
  filter_upwards [E1, eventually_ge_atTop (c ^ M₀), eventually_ge_atTop N₁,
    eventually_gt_atTop 0] with N hE1 hN hN1 hN0
  simp only [Function.comp] at hE1
  set j := Nat.log c N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hjN : c ^ j ≤ N := Nat.pow_log_le_self c hN0.ne'
  have hjM : M₀ ≤ j := Nat.le_log_of_pow_le (by omega) hN
  have hNj : N < c ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) N
  have := hsum j hjM N hN hNj.le
  rw [blockCount_eq_card_blockCodeAt (by omega)]
  change (F N : ℝ) / N ≤ _
  have hcj : (c : ℝ) ^ j ≤ N := by exact_mod_cast hjN
  have h2j : (2 : ℝ) ^ j ≤ N := (pow_le_pow_left₀ (by norm_num) hc' j).trans hcj
  have hj1 : ((j : ℝ) + 1) ≤ η * N := by
    rw [div_lt_iff₀ (by positivity)] at hE1
    nlinarith
  have hcM : 4 * (c : ℝ) ^ M₀ ≤ ε * N := by
    rw [div_lt_iff₀ hε] at hN₁
    have : (N₁ : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  rw [div_le_iff₀ hN']
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hηK : η * (K + 1) = ε / 4 := by simp only [η]; field_simp
  have : ((j : ℝ) + 1) * K ≤ ε / 4 * N := by
    calc ((j : ℝ) + 1) * K ≤ η * N * (K + 1) := by nlinarith
      _ = ε / 4 * N := by rw [mul_right_comm, hηK]
  have hρE : ρ * (E + 2) = (E + 2) * β + ε / 2 := by
    simp only [ρ, δ]; field_simp; ring
  have : ρ * (E * N + 2 * c ^ j) ≤ ρ * (E + 2) * N := by
    rw [mul_assoc]; gcongr; linarith
  nlinarith

/-- `α_{2,3} = ∑ 1 / (3 ^ k * 2 ^ (3 ^ k))` is normal in base two. -/
theorem isNormalIn_two_stoneham_three : IsNormalIn 2 (stoneham 2 3) :=
  isNormalIn_stoneham le_rfl (by norm_num) (by norm_num)

end Real
