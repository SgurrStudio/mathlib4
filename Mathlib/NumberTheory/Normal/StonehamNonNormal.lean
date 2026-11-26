/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Stoneham

/-!
# Non-normality of Stoneham numbers in composite base `b * c`

For coprime integers `b, c ≥ 2`, `Real.isNormalIn_stoneham` establishes that the Stoneham number
`α_{b,c} = ∑_{k ≥ 1} 1 / (c ^ k * b ^ (c ^ k))` is normal in base `b`.
**Bailey and Borwein** (2012) proved that `α_{b,c}` is nevertheless **not** normal in base `b * c`
(and hence not absolutely normal): multiplying `α_{b,c}` by `(b * c) ^ (c ^ j)` makes the first
`j` terms an exact integer while the remaining tail is at most `2 * (c / b ^ (c - 1)) ^ (c ^ j)`.
Since `c < b ^ (c - 1)` for all coprime `b, c ≥ 2`, this forces a run of `Ω(c ^ j)` consecutive
base-`(b * c)` zero digits starting at position `c ^ j`, contradicting convergence of the `0`-digit
frequency to `(b * c)⁻¹`.

In particular, `stoneham 2 3` is an explicit constructive witness that base-`2` normality does not
imply base-`6` normality (or absolute normality).

## Main statements

* `Real.not_isNormalIn_mul_stoneham`: for coprime `b, c ≥ 2`, `¬ IsNormalIn (b * c) (stoneham b c)`.
* `Real.not_isNormalIn_six_stoneham_two_three`: `¬ IsNormalIn 6 (stoneham 2 3)`.
* `Real.not_isAbsolutelyNormal_stoneham`: for coprime `b, c ≥ 2`,
  `¬ IsAbsolutelyNormal (stoneham b c)`.

## References

* D. H. Bailey, J. M. Borwein, *Nonnormality of Stoneham constants*,
  Ramanujan J. 29 (2012), 409–422.
-/

@[expose] public section

open Filter Topology

namespace Real

private theorem lt_pow_pred_of_coprime {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) :
    c < b ^ (c - 1) := by
  by_cases hc2 : c = 2
  · subst hc2
    have hb3 : 3 ≤ b := by
      by_contra h
      have hb2 : b = 2 := by omega
      subst hb2
      norm_num at hbc
    simp only [Nat.reduceSub, pow_one]
    omega
  · have hc3 : 3 ≤ c := by omega
    have h2 : c < 2 ^ (c - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hc3
      clear hc3 hc2 hc hb hbc
      induction k with
      | zero => decide
      | succ k ih =>
        rw [show k + 1 + 3 - 1 = (k + 3 - 1) + 1 by omega, pow_succ]
        omega
    exact lt_of_lt_of_le h2 (Nat.pow_le_pow_left hb (c - 1))

private theorem digit_mul_stoneham_eq_zero {b c j L : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hL : 2 * ((c : ℝ) / (b : ℝ) ^ (c - 1)) ^ (c ^ j) * ((b * c : ℕ) : ℝ) ^ L < 1)
    {i : ℕ} (hi : i < L) :
    digit (b * c) (stoneham b c) (c ^ j + i) = 0 := by
  set B : ℕ := b * c
  set N : ℕ := c ^ j
  have hB1 : 1 ≤ B := by dsimp [B]; nlinarith
  have hjN : j ≤ N := (Nat.lt_pow_self (by omega : 1 < c)).le
  have hmul := stoneham_mul_pow_eq (b := b) (c := c) (by omega) hc (j := j) (n := N) le_rfl
  set T₀ : ℝ :=
    ∑' k : ℕ, ((c : ℝ) ^ (k + j + 1) * (b : ℝ) ^ (c ^ (k + j + 1)))⁻¹ * (b : ℝ) ^ N
  have hT₀_nonneg : 0 ≤ T₀ := tsum_nonneg fun _ ↦ by positivity
  have hK : N + (c - 1) * N ≤ c ^ (j + 1) := by
    have h1 : N + (c - 1) * N = c * N := by
      calc N + (c - 1) * N = (1 + (c - 1)) * N := by ring
        _ = c * N := by rw [Nat.add_sub_of_le (by omega)]
    rw [h1, pow_succ']
  have hT₀_le : T₀ ≤ 2 * ((b : ℝ) ^ ((c - 1) * N))⁻¹ := stoneham_tail_le hb hc hK
  set M : ℕ := stonehamNum b c j N * c ^ (N - j)
  set T : ℝ := (c : ℝ) ^ N * T₀
  have hsplit : stoneham b c * (B : ℝ) ^ N = (M : ℝ) + T := by
    have hBN : (B : ℝ) ^ N = (b : ℝ) ^ N * (c : ℝ) ^ N := by
      simp only [B, Nat.cast_mul, mul_pow]
    have hcN : (c : ℝ) ^ N = (c : ℝ) ^ (N - j) * (c : ℝ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjN]
    have hcj0 : (c : ℝ) ^ j ≠ 0 := by positivity
    calc stoneham b c * (B : ℝ) ^ N
        = (stoneham b c * (b : ℝ) ^ N) * (c : ℝ) ^ N := by rw [hBN]; ring
      _ = ((stonehamNum b c j N : ℝ) / (c : ℝ) ^ j + T₀) * (c : ℝ) ^ N := by rw [hmul]
      _ = (stonehamNum b c j N : ℝ) * (c : ℝ) ^ (N - j) + (c : ℝ) ^ N * T₀ := by
          rw [add_mul, hcN]; field_simp [hcj0]
      _ = (M : ℝ) + T := by simp only [M, T, Nat.cast_mul, Nat.cast_pow]
  have hT_nonneg : 0 ≤ T := mul_nonneg (by positivity) hT₀_nonneg
  have hT_le : T ≤ 2 * ((c : ℝ) / (b : ℝ) ^ (c - 1)) ^ N := by
    calc T = (c : ℝ) ^ N * T₀ := rfl
      _ ≤ (c : ℝ) ^ N * (2 * ((b : ℝ) ^ ((c - 1) * N))⁻¹) := by gcongr
      _ = 2 * ((c : ℝ) / (b : ℝ) ^ (c - 1)) ^ N := by
          rw [div_pow, ← pow_mul, div_eq_mul_inv]; ring
  have hTB_lt : T * (B : ℝ) ^ (i + 1) < 1 := by
    have hBi : (B : ℝ) ^ (i + 1) ≤ (B : ℝ) ^ L :=
      pow_le_pow_right₀ (by exact_mod_cast hB1) hi
    calc T * (B : ℝ) ^ (i + 1)
        ≤ (2 * ((c : ℝ) / (b : ℝ) ^ (c - 1)) ^ N) * (B : ℝ) ^ L := by gcongr
      _ < 1 := hL
  have hval : stoneham b c * (B : ℝ) ^ (N + i + 1) =
      ((M * B ^ (i + 1) : ℕ) : ℝ) + T * (B : ℝ) ^ (i + 1) := by
    rw [show N + i + 1 = N + (i + 1) by omega, pow_add, ← mul_assoc, hsplit, add_mul]
    push_cast
    rfl
  have hfl : ⌊stoneham b c * (B : ℝ) ^ (N + i + 1)⌋ = (M * B ^ (i + 1) : ℕ) := by
    rw [hval, Int.floor_eq_iff]
    push_cast
    constructor
    · linarith [mul_nonneg hT_nonneg (show (0 : ℝ) ≤ (B : ℝ) ^ (i + 1) by positivity)]
    · linarith
  rw [digit, hfl]
  have hdvd : (B : ℤ) ∣ ((M * B ^ (i + 1) : ℕ) : ℤ) := by
    exact_mod_cast (dvd_pow_self B (Nat.succ_ne_zero i)).mul_left M
  rw [Int.emod_eq_zero_of_dvd hdvd, Int.toNat_zero]

/-- **Bailey–Borwein (2012)**: for coprime `b, c ≥ 2`, the Stoneham number `stoneham b c` is not
normal in base `b * c`. -/
theorem not_isNormalIn_mul_stoneham {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) :
    ¬ IsNormalIn (b * c) (stoneham b c) := by
  intro hnorm
  set B : ℕ := b * c
  have hB4 : 4 ≤ B := by dsimp [B]; nlinarith
  have hBpos : (0 : ℝ) < B := by positivity
  set r : ℝ := (c : ℝ) / (b : ℝ) ^ (c - 1)
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast lt_pow_pred_of_coprime hb hc hbc
  obtain ⟨q₀, hq₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (B : ℝ)⁻¹ by positivity) hr1
  set q : ℕ := max q₀ 1
  have hq1 : 1 ≤ q := le_max_right _ _
  have hrq_lt : r ^ q < (B : ℝ)⁻¹ :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (le_max_left _ _)) hq₀
  have hrqB : r ^ q * (B : ℝ) ≤ 1 := by
    have := mul_lt_mul_of_pos_right hrq_lt hBpos
    rw [inv_mul_cancel₀ hBpos.ne'] at this
    exact this.le
  have hrq1 : r ^ q < 1 :=
    lt_of_lt_of_le hrq_lt (inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ B)))
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 2 by norm_num) hrq1
  have hm2 : 2 * r ^ (q * m) < 1 := by
    rw [pow_mul]
    linarith
  set w : Fin 1 → Fin B := fun _ ↦ ⟨0, by omega⟩
  have hlim : Tendsto (fun N : ℕ ↦ (blockCount B (stoneham b c) w N : ℝ) / N)
      atTop (𝓝 ((B : ℝ)⁻¹)) := by
    simpa only [pow_one] using hnorm 1 w
  set ε : ℝ := (1 - (B : ℝ)⁻¹) / (4 * (q : ℝ) + 2)
  have h1B : 0 < 1 - (B : ℝ)⁻¹ := by
    have : (B : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < B))
    linarith
  have hε : 0 < ε := div_pos h1B (by positivity)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N₀, hN₀⟩ := hlim ε hε
  set M₀ : ℕ := max N₀ (2 * q * (m + 1))
  have hM₀_lt : M₀ < c ^ M₀ := Nat.lt_pow_self (by omega : 1 < c)
  set N : ℕ := c ^ M₀
  set L : ℕ := N / q - m
  have hN_ge : M₀ ≤ N := hM₀_lt.le
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN_ge
  have hN_big : 2 * q * (m + 1) ≤ N := le_trans (le_max_right _ _) hN_ge
  have hqm : m ≤ N / q := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < q)]
    nlinarith
  have hqLm : q * (L + m) ≤ N := by
    have : L + m = N / q := Nat.sub_add_cancel hqm
    rw [this]
    exact Nat.mul_div_le N q
  have hL_ge : N ≤ 2 * q * L := by
    have hdiv : N < q * (N / q + 1) := by
      have := Nat.div_add_mod N q
      have := Nat.mod_lt N (by omega : 0 < q)
      nlinarith
    have hLm : N / q = L + m := (Nat.sub_add_cancel hqm).symm
    rw [hLm] at hdiv
    nlinarith
  have hLpos : 0 < L := by
    have hNpos : 0 < N := Nat.pow_pos (by omega : 0 < c)
    nlinarith
  have hL_cond : 2 * r ^ N * (B : ℝ) ^ L < 1 := by
    have hrN : r ^ N ≤ r ^ (q * (L + m)) := pow_le_pow_of_le_one hr0.le hr1.le hqLm
    calc 2 * r ^ N * (B : ℝ) ^ L
        ≤ 2 * r ^ (q * (L + m)) * (B : ℝ) ^ L := by gcongr
      _ = (2 * r ^ (q * m)) * (r ^ q * (B : ℝ)) ^ L := by
          rw [mul_add, pow_add, pow_mul, pow_mul, mul_pow]; ring
      _ ≤ (2 * r ^ (q * m)) * 1 ^ L := by gcongr
      _ = 2 * r ^ (q * m) := by simp
      _ < 1 := hm2
  have hzero : ∀ i < L, digit B (stoneham b c) (N + i) = 0 := fun i hi ↦
    digit_mul_stoneham_eq_zero hb hc hL_cond hi
  have hcount_ge : blockCount B (stoneham b c) w N + L ≤
      blockCount B (stoneham b c) w (N + L) := by
    simp only [blockCount]
    have hdisj : Disjoint
        ((Finset.range N).filter fun i ↦ ∀ j : Fin 1, digit B (stoneham b c) (i + j) = w j)
        (Finset.Ico N (N + L)) := by
      rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      simp only [Finset.mem_filter, Finset.mem_range] at hi₁
      simp only [Finset.mem_Ico] at hi₂
      omega
    have hsub : ((Finset.range N).filter fun i ↦
            ∀ j : Fin 1, digit B (stoneham b c) (i + j) = w j) ∪
          Finset.Ico N (N + L) ⊆
        (Finset.range (N + L)).filter fun i ↦
          ∀ j : Fin 1, digit B (stoneham b c) (i + j) = w j := by
      intro i hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hi ⊢
      rcases hi with ⟨hiN, hiw⟩ | ⟨hNi, hiNL⟩
      · exact ⟨by omega, hiw⟩
      · refine ⟨hiNL, fun j ↦ ?_⟩
        have hj0 : (j : ℕ) = 0 := Fin.eq_zero j ▸ rfl
        rw [hj0, add_zero, show i = N + (i - N) by omega]
        exact hzero (i - N) (by omega)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
    exact hcard
  have h1 := hN₀ N hN0
  have h2 := hN₀ (N + L) (le_trans hN0 (Nat.le_add_right N L))
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pow_pos (by omega : 0 < c))
  have hNLposR : (0 : ℝ) < (N + L : ℕ) := by positivity
  have hlo : ((B : ℝ)⁻¹ - ε) * (N : ℝ) < (blockCount B (stoneham b c) w N : ℝ) := by
    have := mul_lt_mul_of_pos_right h1.1 hNposR
    rw [sub_mul, div_mul_cancel₀ _ hNposR.ne'] at this
    linarith
  have hhi : (blockCount B (stoneham b c) w (N + L) : ℝ) <
      ((B : ℝ)⁻¹ + ε) * ((N + L : ℕ) : ℝ) := by
    have := mul_lt_mul_of_pos_right h2.2 hNLposR
    rw [sub_mul, div_mul_cancel₀ _ hNLposR.ne'] at this
    linarith
  have hcast : (blockCount B (stoneham b c) w N : ℝ) + (L : ℝ) ≤
      (blockCount B (stoneham b c) w (N + L) : ℝ) := by exact_mod_cast hcount_ge
  have hcomb : (1 - (B : ℝ)⁻¹) * (L : ℝ) < ε * (2 * (N : ℝ) + (L : ℝ)) := by
    push_cast at hhi
    linarith
  have hNL_bound : 2 * (N : ℝ) + (L : ℝ) ≤ (4 * (q : ℝ) + 1) * (L : ℝ) := by
    have hL_geR : (N : ℝ) ≤ 2 * (q : ℝ) * (L : ℝ) := by exact_mod_cast hL_ge
    nlinarith
  have hLposR : (0 : ℝ) < L := Nat.cast_pos.2 hLpos
  have hε_eq : ε * (4 * (q : ℝ) + 2) = 1 - (B : ℝ)⁻¹ :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

/-- The Stoneham constant `α_{2,3}` is not normal in base `6` (despite being normal in base `2`,
see `Real.isNormalIn_two_stoneham_three`). -/
theorem not_isNormalIn_six_stoneham_two_three : ¬ IsNormalIn 6 (stoneham 2 3) :=
  not_isNormalIn_mul_stoneham (b := 2) (c := 3) le_rfl (by decide) (by decide)

/-- No Stoneham number `stoneham b c` (`b, c ≥ 2` coprime) is absolutely normal. -/
theorem not_isAbsolutelyNormal_stoneham {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (hbc : b.Coprime c) :
    ¬ IsAbsolutelyNormal (stoneham b c) := fun h ↦
  not_isNormalIn_mul_stoneham hb hc hbc (h (b * c) (by nlinarith))

end Real
