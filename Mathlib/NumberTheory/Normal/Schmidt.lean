/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Bridge
public import Mathlib.NumberTheory.Normal.Cassels
public import Mathlib.NumberTheory.Normal.SchmidtGeneral
public import Mathlib.NumberTheory.Normal.SchmidtPrimePower
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic

/-!
# Schmidt's theorem: normality in one base need not imply normality in another

Normality in base `b` implies normality in base `c` when `b` and `c` are multiplicatively
dependent (`Real.isNormalIn_iff_of_pow_eq_pow`). **Schmidt** (1960) proved the converse: if
`bᵐ ≠ cⁿ` for all `m, n ≥ 1`, some real number is normal in base `b` and not in base `c`.

## Main statements

* `Real.exists_liouville_isNormalIn_iff_not_three_dvd`: a Liouville number in the middle-third
  Cantor set that is normal exactly in the bases not divisible by `3` (Trevor Morris's
  `CantorLiouvilleAll`).
* `Real.exists_isNormalIn_two_not_isNormalIn_three`: normality in base `2` does not imply
  normality in base `3`.
* `Real.exists_isNormalIn_not_isNormalIn_of_isPrimePow`: Schmidt's theorem when `c` is a prime
  power (`Real.SchmidtPrimePower`).
* `Real.forall_isNormalIn_imp_iff_of_isPrimePow`: for a prime power `c`, normality in base `b`
  implies normality in base `c` exactly when `b` and `c` are multiplicatively dependent.
* `Real.exists_isNormalIn_not_isNormalIn`: **Schmidt's theorem** for arbitrary bases
  (`Real.SchmidtGeneral`).
* `Real.exists_isNormalIn_forall_not_isNormalIn_pow`: the strong form, normal in base `b` and in
  no base `cʲ`.
* `Real.forall_isNormalIn_imp_iff`: normality in base `b` implies normality in base `c` exactly
  when `b` and `c` are multiplicatively dependent.
-/

@[expose] public section

namespace Real

/-- A Liouville number in the middle-third Cantor set that is normal in base `b` exactly when
`3 ∤ b` (Trevor Morris's `CantorLiouvilleAll`). -/
theorem exists_liouville_isNormalIn_iff_not_three_dvd :
    ∃ x : ℝ, x ∈ cantorSet ∧ Liouville x ∧ ∀ b : ℕ, 2 ≤ b → (IsNormalIn b x ↔ ¬ 3 ∣ b) := by
  obtain ⟨e, -, hK, hL, hN⟩ :=
    NormalNumbers.CantorLiouvilleAll.exists_computable_liouville_mem_cantorSet_normalProfile
  exact ⟨_, hK, hL, fun b hb ↦ (isNormalIn_iff_isNormal b _).trans (hN b hb)⟩

/-- Normality in base `2` does not imply normality in base `3`. -/
theorem exists_isNormalIn_two_not_isNormalIn_three :
    ∃ x : ℝ, IsNormalIn 2 x ∧ ¬ IsNormalIn 3 x := by
  obtain ⟨x, -, -, hx⟩ := exists_liouville_isNormalIn_iff_not_three_dvd
  exact ⟨x, (hx 2 le_rfl).2 (by norm_num), fun h ↦ (hx 3 (by norm_num)).1 h dvd_rfl⟩

/-- **Schmidt's theorem** when `c` is a prime power: if `bᵐ ≠ cⁿ` for all `m, n ≥ 1`, some real
number is normal in base `b` but not in base `c`. -/
theorem exists_isNormalIn_not_isNormalIn_of_isPrimePow {b c : ℕ} (hb : 2 ≤ b)
    (hc : IsPrimePow c) (h : ∀ m n : ℕ, 0 < m → 0 < n → b ^ m ≠ c ^ n) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn c x := by
  obtain ⟨p, j, hp, hj, rfl⟩ := hc
  have hp' : p.Prime := Nat.prime_iff.2 hp
  have hpow : ∀ i, b ≠ p ^ i := by
    rintro i rfl
    have hi : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp at hb
      · exact hi
    exact h j i hj hi (by rw [← pow_mul, ← pow_mul, mul_comm])
  obtain ⟨x, hx, hnot⟩ := SchmidtPrimePower.exists_isNormalIn_forall_not_isNormalIn_pow hp' hb hpow
  exact ⟨x, hx, hnot j hj⟩

/-- For a prime power `c`, normality in base `b` implies normality in base `c` if and only if `b`
and `c` are multiplicatively dependent. -/
theorem forall_isNormalIn_imp_iff_of_isPrimePow {b c : ℕ} (hb : 2 ≤ b) (hc : IsPrimePow c) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn c x) ↔ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ b ^ m = c ^ n := by
  constructor
  · intro H
    by_contra hdep
    push Not at hdep
    obtain ⟨x, hx, hnx⟩ := exists_isNormalIn_not_isNormalIn_of_isPrimePow hb hc
      fun m n hm hn ↦ hdep m n hm hn
    exact hnx (H x hx)
  · rintro ⟨m, n, hm, hn, hmn⟩ x hx
    exact (isNormalIn_iff_of_pow_eq_pow hb hc.two_le hm hn hmn).1 hx

/-- **Schmidt's theorem.** If `b, c ≥ 2` and `bᵐ ≠ cⁿ` for all `m, n ≥ 1`, some real number is
normal in base `b` but not in base `c`. -/
theorem exists_isNormalIn_not_isNormalIn {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : ∀ m n : ℕ, 0 < m → 0 < n → b ^ m ≠ c ^ n) :
    ∃ x : ℝ, IsNormalIn b x ∧ ¬ IsNormalIn c x := by
  obtain ⟨x, hx, hnot⟩ := SchmidtGeneral.exists_isNormalIn_forall_not_isNormalIn_pow hb hc h
  exact ⟨x, hx, by simpa using hnot 1 le_rfl⟩

/-- **Schmidt's theorem**, strong form. If `b, c ≥ 2` and `bᵐ ≠ cⁿ` for all `m, n ≥ 1`, some real
number is normal in base `b` and in no base `cʲ`, `j ≥ 1`. -/
theorem exists_isNormalIn_forall_not_isNormalIn_pow {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : ∀ m n : ℕ, 0 < m → 0 < n → b ^ m ≠ c ^ n) :
    ∃ x : ℝ, IsNormalIn b x ∧ ∀ j, 1 ≤ j → ¬ IsNormalIn (c ^ j) x :=
  SchmidtGeneral.exists_isNormalIn_forall_not_isNormalIn_pow hb hc h

/-- Normality in base `b` implies normality in base `c` if and only if `b` and `c` are
multiplicatively dependent. -/
theorem forall_isNormalIn_imp_iff {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) :
    (∀ x : ℝ, IsNormalIn b x → IsNormalIn c x) ↔ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ b ^ m = c ^ n := by
  constructor
  · intro H
    by_contra hdep
    push Not at hdep
    obtain ⟨x, hx, hnx⟩ := exists_isNormalIn_not_isNormalIn hb hc fun m n hm hn ↦ hdep m n hm hn
    exact hnx (H x hx)
  · rintro ⟨m, n, hm, hn, hmn⟩ x hx
    exact (isNormalIn_iff_of_pow_eq_pow hb hc hm hn hmn).1 hx

end Real
