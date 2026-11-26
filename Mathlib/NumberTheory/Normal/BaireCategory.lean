/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Borel
public import Mathlib.Topology.GDelta.Basic

import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Baire category of normal and disjunctive numbers

While Borel's normal number theorem (`Real.ae_isAbsolutelyNormal`) shows that almost every real
number (in the sense of Lebesgue measure) is absolutely normal, from the standpoint of Baire
category the situation is completely reversed:

* The set of numbers whose digit frequency converges for even a single digit in a single base
  `b ≥ 2` is meagre (`Real.isMeagre_setOf_tendsto_digitFreq`). Consequently, the sets of simply
  normal, normal, and absolutely normal numbers—and even the union of simply normal numbers across
  all bases `b ≥ 2`—are meagre in `ℝ` (Šalát 1966).
* By contrast, the set of disjunctive numbers in base `b ≥ 2` (`Real.IsDisjunctiveIn b`), as well
  as the set of *absolutely disjunctive* numbers (disjunctive in every base `b ≥ 2`), is a dense
  `Gδ` set, hence residual (comeagre) in `ℝ`.
* Combining these gives a sharp measure-versus-category dichotomy and a strong separation between
  disjunctivity and normality: a residual (hence dense and uncountable) Lebesgue-null set of real
  numbers is disjunctive in *every* base `b ≥ 2` yet simply normal in *no* base `b ≥ 2`.
* Moreover, every real number can be written as the sum of two absolutely disjunctive numbers that
  are not simply normal in any base `b ≥ 2`.

## Main statements

* `Real.isGδ_setOf_isDisjunctiveIn`, `Real.residual_setOf_isDisjunctiveIn`: for `2 ≤ b`,
  `{x : ℝ | IsDisjunctiveIn b x}` is a dense `Gδ` (hence residual) set.
* `Real.isGδ_setOf_forall_isDisjunctiveIn`, `Real.residual_setOf_forall_isDisjunctiveIn`: the set
  of absolutely disjunctive reals is a dense `Gδ` (hence residual) set.
* `Real.isMeagre_setOf_tendsto_digitFreq`: for `2 ≤ b` and any digit `d : Fin b`, the set of reals
  whose frequency of digit `d` converges is meagre.
* `Real.isMeagre_setOf_isSimplyNormalIn`, `Real.isMeagre_setOf_isNormalIn`,
  `Real.isMeagre_setOf_isAbsolutelyNormal`, `Real.isMeagre_setOf_exists_isSimplyNormalIn`:
  normality (even simple normality in some base `b ≥ 2`) is meagre.
* `Real.residual_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn`: generic reals are
  absolutely disjunctive yet simply normal in no base `b ≥ 2`.
* `Real.volume_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn`: this residual set has
  Lebesgue measure zero.
* `Real.exists_add_eq_forall_isDisjunctiveIn_and_not_isSimplyNormalIn`: every real is a sum of two
  such numbers.

## References

* T. Šalát, *A remark on normal numbers*, Rev. Roumaine Math. Pures Appl. 11 (1966), 53–56.
* J. C. Oxtoby, *Measure and Category*, Springer GTM 2, 2nd ed., 1980.
* C. S. Calude and T. Zamfirescu, *Most numbers obey no probability laws*, Publ. Math. Debrecen
  54 (1999), 619–623.
-/

@[expose] public section

open Filter Topology Set MeasureTheory

namespace Real

/-! ### Open `b`-adic intervals and digit prefixes -/

/-- The open `b`-adic interval `(m / b ^ N, (m + 1) / b ^ N)`. -/
private noncomputable def badicIoo (b N : ℕ) (m : ℤ) : Set ℝ :=
  Ioo ((m : ℝ) / (b : ℝ) ^ N) (((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ N)

private lemma isOpen_badicIoo (b N : ℕ) (m : ℤ) : IsOpen (badicIoo b N m) := isOpen_Ioo

private lemma nonempty_badicIoo {b : ℕ} (hb : 0 < b) (N : ℕ) (m : ℤ) :
    (badicIoo b N m).Nonempty := by
  refine nonempty_Ioo.2 (div_lt_div_of_pos_right ?_ (by positivity))
  exact_mod_cast Int.lt_succ m

/-- Every nonempty open interval `(u, v)` contains a `b`-adic open interval `badicIoo b K m`. -/
private lemma exists_badicIoo_subset {b : ℕ} (hb : 2 ≤ b) {u v : ℝ} (huv : u < v) :
    ∃ (K : ℕ) (m : ℤ), badicIoo b K m ⊆ Ioo u v := by
  have h1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hvu : 0 < v - u := sub_pos.2 huv
  obtain ⟨K, hK⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop
    ((2 : ℝ) / (v - u))).exists
  have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  have hgap : (2 : ℝ) / (b : ℝ) ^ K < v - u := by
    rw [div_lt_iff₀ hbK]
    have := (div_lt_iff₀ hvu).1 hK
    linarith
  refine ⟨K, ⌊u * (b : ℝ) ^ K⌋ + 1, fun x hx ↦ ?_⟩
  have hm1 : u < ((⌊u * (b : ℝ) ^ K⌋ + 1 : ℤ) : ℝ) / (b : ℝ) ^ K := by
    rw [lt_div_iff₀ hbK, Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one (u * (b : ℝ) ^ K)
  have hm2 : (((⌊u * (b : ℝ) ^ K⌋ + 1 + 1 : ℤ) : ℝ)) / (b : ℝ) ^ K < v := by
    rw [div_lt_iff₀ hbK]
    have hfl : (⌊u * (b : ℝ) ^ K⌋ : ℝ) ≤ u * (b : ℝ) ^ K := Int.floor_le _
    have hgap' : 2 < (v - u) * (b : ℝ) ^ K := (div_lt_iff₀ hbK).1 hgap
    push_cast
    linarith
  exact ⟨lt_trans hm1 hx.1, lt_trans hx.2 hm2⟩

/-- Appending the finite word `w : Fin L → Fin b` to a `b`-adic interval `badicIoo b K m` yields
a subinterval `badicIoo b (K + L) (m * b ^ L + blockCode w)` on which the digits at positions
`K, …, K + L - 1` equal `w`. -/
private lemma badicIoo_append_subset {b K L : ℕ} (hb : 0 < b) (m : ℤ) (w : Fin L → Fin b) :
    badicIoo b (K + L) (m * (b : ℤ) ^ L + (blockCode w : ℕ)) ⊆ badicIoo b K m := by
  intro x hx
  have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  have hbKL : (0 : ℝ) < (b : ℝ) ^ (K + L) := by positivity
  have hlt : (blockCode w : ℕ) < b ^ L := (blockCode w).isLt
  have h1 : (m : ℝ) * (b : ℝ) ^ L ≤
      ((m * (b : ℤ) ^ L + (blockCode w : ℕ) : ℤ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (blockCode w : ℕ)]
  have h2 : (((m * (b : ℤ) ^ L + (blockCode w : ℕ) + 1 : ℤ) : ℝ)) ≤
      ((m + 1 : ℤ) : ℝ) * (b : ℝ) ^ L := by
    have hlt' : ((blockCode w : ℕ) + 1 : ℝ) ≤ (b : ℝ) ^ L := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    push_cast
    linarith
  constructor
  · have hleft : (m : ℝ) / (b : ℝ) ^ K ≤
        ((m * (b : ℤ) ^ L + (blockCode w : ℕ) : ℤ) : ℝ) / (b : ℝ) ^ (K + L) := by
      rw [div_le_div_iff₀ hbK hbKL, pow_add]
      nlinarith
    exact lt_of_le_of_lt hleft hx.1
  · have hright : (((m * (b : ℤ) ^ L + (blockCode w : ℕ) + 1 : ℤ) : ℝ)) / (b : ℝ) ^ (K + L) ≤
        ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ K := by
      rw [div_le_div_iff₀ hbKL hbK, pow_add]
      nlinarith
    exact lt_of_lt_of_le hx.2 hright

private lemma digit_of_mem_badicIoo_append {b K L : ℕ} (hb : 0 < b) (m : ℤ) (w : Fin L → Fin b)
    {x : ℝ} (hx : x ∈ badicIoo b (K + L) (m * (b : ℤ) ^ L + (blockCode w : ℕ))) :
    ∀ j : Fin L, digit b x (K + j) = w j := by
  have hiff := forall_digit_eq_iff_digit_pow (x := x) hb w K 0
  simp only [zero_mul, add_zero] at hiff
  rw [hiff]
  have hbKL : (0 : ℝ) < (b : ℝ) ^ (K + L) := by positivity
  have hfl : ⌊x * (b : ℝ) ^ K * ((b ^ L : ℕ) : ℝ) ^ (0 + 1)⌋ =
      m * (b : ℤ) ^ L + (blockCode w : ℕ) := by
    have heq : x * (b : ℝ) ^ K * ((b ^ L : ℕ) : ℝ) ^ (0 + 1) = x * (b : ℝ) ^ (K + L) := by
      rw [zero_add, pow_one, Nat.cast_pow, mul_assoc, ← pow_add]
    rw [heq, Int.floor_eq_iff]
    refine ⟨(div_lt_iff₀ hbKL).1 hx.1 |>.le, ?_⟩
    have := (lt_div_iff₀ hbKL).1 hx.2
    rw [Int.cast_add, Int.cast_one] at this
    exact this
  rw [digit, hfl, Nat.cast_pow]
  have hmod : (m * (b : ℤ) ^ L + ((blockCode w : ℕ) : ℤ)) % ((b : ℤ) ^ L) =
      ((blockCode w : ℕ) : ℤ) := by
    rw [Int.mul_add_emod_self_right, Int.emod_eq_of_lt (Nat.cast_nonneg _)]
    exact_mod_cast (blockCode w).isLt
  rw [hmod, Int.toNat_natCast]

/-- No `b`-adic rational `m / b ^ n` is disjunctive in base `b ≥ 2`, since its digits are
eventually `0`. -/
private lemma not_isDisjunctiveIn_div_pow {b : ℕ} (hb : 2 ≤ b) (m : ℤ) (n : ℕ) :
    ¬ IsDisjunctiveIn b ((m : ℝ) / (b : ℝ) ^ n) := by
  intro hdisj
  let one : Fin b := ⟨1, by omega⟩
  obtain ⟨i, hi⟩ := hdisj (n + 1) (fun _ ↦ one)
  have h1 := hi ⟨n, Nat.lt_succ_self n⟩
  change digit b ((m : ℝ) / (b : ℝ) ^ n) (i + n) = 1 at h1
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hmul : ((m : ℝ) / (b : ℝ) ^ n) * (b : ℝ) ^ (i + n + 1) =
      ((m * (b : ℤ) ^ (i + 1) : ℤ) : ℝ) := by
    have hpow : (b : ℝ) ^ (i + n + 1) = (b : ℝ) ^ n * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, div_mul_eq_mul_div, mul_comm ((m : ℝ)), mul_assoc,
      mul_div_cancel_left₀ _ (pow_ne_zero n hb0), mul_comm]
    push_cast; rfl
  have hdvd : (b : ℤ) ∣ m * (b : ℤ) ^ (i + 1) :=
    (dvd_pow_self (b : ℤ) (Nat.succ_ne_zero i)).mul_left m
  have h0 : digit b ((m : ℝ) / (b : ℝ) ^ n) (i + n) = 0 := by
    rw [digit, hmul, Int.floor_intCast, Int.emod_eq_zero_of_dvd hdvd]
    rfl
  omega

/-- A set `U ⊆ ℝ` that meets every nonempty open interval `(u, v)` is dense. -/
private lemma dense_of_forall_Ioo_nonempty {U : Set ℝ}
    (h : ∀ u v : ℝ, u < v → (U ∩ Ioo u v).Nonempty) : Dense U := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨y, hyU, hy1, hy2⟩ := h (x - r) (x + r) (by linarith)
  refine ⟨y, ?_, hyU⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### Disjunctive numbers are dense `Gδ` and comeager -/

/-- The open set of real numbers lying in an open `b`-adic interval that forces the block `w` to
occur at some position `i`. -/
private noncomputable def disjunctiveOpen (b k : ℕ) (w : Fin k → Fin b) : Set ℝ :=
  ⋃ (i : ℕ) (m : ℤ), badicIoo b (i + k) (m * (b : ℤ) ^ k + (blockCode w : ℕ))

private lemma isOpen_disjunctiveOpen (b k : ℕ) (w : Fin k → Fin b) :
    IsOpen (disjunctiveOpen b k w) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_badicIoo _ _ _

private lemma dense_disjunctiveOpen {b : ℕ} (hb : 2 ≤ b) (k : ℕ) (w : Fin k → Fin b) :
    Dense (disjunctiveOpen b k w) := by
  refine dense_of_forall_Ioo_nonempty fun u v huv ↦ ?_
  obtain ⟨K, m, hsub⟩ := exists_badicIoo_subset hb huv
  obtain ⟨x, hx⟩ := nonempty_badicIoo (by omega : 0 < b) (K + k)
    (m * (b : ℤ) ^ k + (blockCode w : ℕ))
  refine ⟨x, ?_, hsub (badicIoo_append_subset (by omega : 0 < b) m w hx)⟩
  exact mem_iUnion.2 ⟨K, mem_iUnion.2 ⟨m, hx⟩⟩

/-- For `2 ≤ b`, the set of base-`b` disjunctive real numbers is a `Gδ` set. -/
theorem isGδ_setOf_isDisjunctiveIn {b : ℕ} (hb : 2 ≤ b) :
    IsGδ {x : ℝ | IsDisjunctiveIn b x} := by
  have hb0 : 0 < b := by omega
  let D : Set ℝ := ⋃ (m : ℤ) (n : ℕ), {(m : ℝ) / (b : ℝ) ^ n}
  have hDc : IsGδ Dᶜ := by
    rw [show Dᶜ = ⋂ (m : ℤ) (n : ℕ), ({(m : ℝ) / (b : ℝ) ^ n} : Set ℝ)ᶜ by
      simp only [D, compl_iUnion]]
    exact .iInter fun _ ↦ .iInter fun _ ↦ isOpen_compl_singleton.isGδ
  have hV : IsGδ (⋂ (k : ℕ) (w : Fin k → Fin b), disjunctiveOpen b k w) :=
    .iInter fun k ↦ .iInter fun w ↦ (isOpen_disjunctiveOpen b k w).isGδ
  have heq : {x : ℝ | IsDisjunctiveIn b x} =
      Dᶜ ∩ ⋂ (k : ℕ) (w : Fin k → Fin b), disjunctiveOpen b k w := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_iUnion, mem_singleton_iff,
      mem_iInter, not_exists, D]
    constructor
    · intro hx
      refine ⟨fun m n hmn ↦ ?_, fun k w ↦ ?_⟩
      · exact not_isDisjunctiveIn_div_pow hb m n (hmn ▸ hx)
      · obtain ⟨i, hi⟩ := hx k w
        set M : ℤ := ⌊x * (b : ℝ) ^ (i + k)⌋
        have hbik : (0 : ℝ) < (b : ℝ) ^ (i + k) := by positivity
        have hne : x ≠ (M : ℝ) / (b : ℝ) ^ (i + k) := fun h ↦
          not_isDisjunctiveIn_div_pow hb M (i + k) (h ▸ hx)
        have hgt : (M : ℝ) / (b : ℝ) ^ (i + k) < x := by
          refine lt_of_le_of_ne ?_ hne.symm
          rw [div_le_iff₀ hbik]
          exact Int.floor_le _
        have hlt : x < ((M + 1 : ℤ) : ℝ) / (b : ℝ) ^ (i + k) := by
          rw [lt_div_iff₀ hbik, Int.cast_add, Int.cast_one]
          exact Int.lt_floor_add_one (x * (b : ℝ) ^ (i + k))
        have hdig : digit (b ^ k) (x * (b : ℝ) ^ i) 0 = blockCode w := by
          have hiff := (forall_digit_eq_iff_digit_pow (x := x) hb0 w i 0).1
          exact hiff (by simpa only [zero_mul, add_zero] using hi)
        have hMmod : M % ((b : ℤ) ^ k) = ((blockCode w : ℕ) : ℤ) := by
          have hpow : x * (b : ℝ) ^ i * ((b ^ k : ℕ) : ℝ) ^ (0 + 1) = x * (b : ℝ) ^ (i + k) := by
            rw [zero_add, pow_one, Nat.cast_pow, mul_assoc, ← pow_add]
          rw [digit, hpow, Nat.cast_pow] at hdig
          have hnn : 0 ≤ M % ((b : ℤ) ^ k) := Int.emod_nonneg _ (by positivity)
          have := congrArg (Nat.cast (R := ℤ)) hdig
          rwa [Int.toNat_of_nonneg hnn] at this
        have hMdecomp : M = (M / (b : ℤ) ^ k) * (b : ℤ) ^ k + (blockCode w : ℕ) := by
          have hdiv := Int.mul_ediv_add_emod M ((b : ℤ) ^ k)
          rw [hMmod, mul_comm] at hdiv
          exact hdiv.symm
        refine mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨M / (b : ℤ) ^ k, ?_⟩⟩
        rw [badicIoo, ← hMdecomp]
        exact ⟨hgt, hlt⟩
    · rintro ⟨_, hx⟩ k w
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hx k w)
      obtain ⟨m, hm⟩ := mem_iUnion.1 hi
      exact ⟨i, digit_of_mem_badicIoo_append hb0 m w hm⟩
  rw [heq]
  exact hDc.inter hV

/-- For `2 ≤ b`, the set of base-`b` disjunctive real numbers is residual (comeagre) in `ℝ`. -/
theorem residual_setOf_isDisjunctiveIn {b : ℕ} (hb : 2 ≤ b) :
    {x : ℝ | IsDisjunctiveIn b x} ∈ residual ℝ := by
  have hb0 : 0 < b := by omega
  have hsub : (⋂ (k : ℕ) (w : Fin k → Fin b), disjunctiveOpen b k w) ⊆
      {x : ℝ | IsDisjunctiveIn b x} := by
    intro x hx k w
    obtain ⟨i, hi⟩ := mem_iUnion.1 (mem_iInter.1 (mem_iInter.1 hx k) w)
    obtain ⟨m, hm⟩ := mem_iUnion.1 hi
    exact ⟨i, digit_of_mem_badicIoo_append hb0 m w hm⟩
  refine Filter.mem_of_superset ?_ hsub
  exact countable_iInter_mem.2 fun k ↦ countable_iInter_mem.2 fun w ↦
    residual_of_dense_open (isOpen_disjunctiveOpen b k w) (dense_disjunctiveOpen hb k w)

/-- For `2 ≤ b`, the set of base-`b` disjunctive real numbers is dense in `ℝ`. -/
theorem dense_setOf_isDisjunctiveIn {b : ℕ} (hb : 2 ≤ b) :
    Dense {x : ℝ | IsDisjunctiveIn b x} :=
  dense_of_mem_residual (residual_setOf_isDisjunctiveIn hb)

/-- The set of *absolutely disjunctive* real numbers (disjunctive in every base `b ≥ 2`) is a
`Gδ` set in `ℝ`. -/
theorem isGδ_setOf_forall_isDisjunctiveIn :
    IsGδ {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} := by
  rw [show {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} =
      ⋂ b : ℕ, ⋂ (_ : 2 ≤ b), {x : ℝ | IsDisjunctiveIn b x} by ext; simp]
  exact .iInter fun b ↦ .iInter fun hb ↦ isGδ_setOf_isDisjunctiveIn hb

/-- The set of *absolutely disjunctive* real numbers is residual (comeagre) in `ℝ`. -/
theorem residual_setOf_forall_isDisjunctiveIn :
    {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} ∈ residual ℝ := by
  rw [show {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} =
      ⋂ b : ℕ, ⋂ (_ : 2 ≤ b), {x : ℝ | IsDisjunctiveIn b x} by ext; simp]
  exact countable_iInter_mem.2 fun b ↦ countable_iInter_mem.2 fun hb ↦
    residual_setOf_isDisjunctiveIn hb

/-- The set of *absolutely disjunctive* real numbers is dense in `ℝ`. -/
theorem dense_setOf_forall_isDisjunctiveIn :
    Dense {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x} :=
  dense_of_mem_residual residual_setOf_forall_isDisjunctiveIn

/-! ### Extreme digit-frequency oscillation and meagreness of normality (Šalát 1966) -/

/-- On a residual set of reals, the frequency of digit `d` in base `b ≥ 2` drops below `ε`
infinitely often. -/
theorem residual_setOf_frequently_digitFreq_lt {b : ℕ} (hb : 2 ≤ b) (d : Fin b)
    {ε : ℝ} (hε : 0 < ε) :
    {x : ℝ | ∃ᶠ N in atTop, (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N < ε} ∈ residual ℝ := by
  have hb0 : 0 < b := by omega
  obtain ⟨d', hd'⟩ : ∃ d' : Fin b, d' ≠ d := by
    by_cases h0 : (d : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h ↦ by simp [Fin.ext_iff, h0] at h⟩
    · exact ⟨⟨0, hb0⟩, fun h ↦ h0 (by simpa [Fin.ext_iff] using h.symm)⟩
  let U : ℕ → Set ℝ := fun M ↦
    ⋃ (N : ℕ) (_ : M ≤ N) (m : ℤ)
      (_ : ∀ x ∈ badicIoo b N m, (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N < ε),
      badicIoo b N m
  have hsub : (⋂ M : ℕ, U M) ⊆
      {x : ℝ | ∃ᶠ N in atTop, (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N < ε} := by
    intro x hx
    rw [mem_ofPred_eq, Filter.frequently_atTop]
    intro M
    have hM := mem_iInter.1 hx M
    simp only [U, mem_iUnion] at hM
    rcases hM with ⟨N, hMN, m, hbound, hxIoo⟩
    exact ⟨N, hMN, hbound x hxIoo⟩
  refine Filter.mem_of_superset (countable_iInter_mem.2 fun M ↦ ?_) hsub
  refine residual_of_dense_open ?_ ?_
  · exact isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦
      isOpen_iUnion fun _ ↦ isOpen_badicIoo _ _ _
  · refine dense_of_forall_Ioo_nonempty fun u v huv ↦ ?_
    obtain ⟨K, m, hKsub⟩ := exists_badicIoo_subset hb huv
    obtain ⟨L, hL⟩ := exists_nat_gt ((K : ℝ) / ε)
    let L' := max L M
    let N := K + L'
    have hMN : M ≤ N := le_trans (le_max_right L M) (Nat.le_add_left L' K)
    let w : Fin L' → Fin b := fun _ ↦ d'
    let m' : ℤ := m * (b : ℤ) ^ L' + (blockCode w : ℕ)
    have hbound : ∀ x ∈ badicIoo b N m', (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N < ε := by
      intro x hx
      have hdig := digit_of_mem_badicIoo_append hb0 m w hx
      have hcard : blockCount b x (fun _ : Fin 1 ↦ d) N ≤ K := by
        classical
        rw [blockCount]
        calc ((Finset.range N).filter fun i ↦ ∀ j : Fin 1, digit b x (i + j) = d).card
            ≤ (Finset.range K).card := by
              refine Finset.card_le_card fun i hi ↦ ?_
              rw [Finset.mem_filter, Finset.mem_range] at hi
              rw [Finset.mem_range]
              by_contra hge
              push Not at hge
              have hlt : i - K < L' := by omega
              have h1 := hi.2 0
              have h2 := hdig ⟨i - K, hlt⟩
              have heq : K + (i - K) = i := by omega
              simp only [Fin.val_zero, add_zero] at h1
              rw [heq] at h2
              exact hd' (Fin.ext (h2.symm.trans h1))
          _ = K := Finset.card_range K
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_le_of_lt (by positivity) hL
        have : 0 < L := by exact_mod_cast hLpos
        have : 0 < N := by omega
        exact_mod_cast this
      rw [div_lt_iff₀ hNpos]
      have hKL : (K : ℝ) / ε < (L : ℝ) := hL
      have hKlt : (K : ℝ) < ε * (L : ℝ) := (div_lt_iff₀ hε).1 hKL |>.trans_eq (mul_comm _ _)
      have hLN : (L : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast le_trans (le_max_left L M) (Nat.le_add_left L' K)
      calc (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ)
          ≤ (K : ℝ) := by exact_mod_cast hcard
        _ < ε * (L : ℝ) := hKlt
        _ ≤ ε * (N : ℝ) := mul_le_mul_of_nonneg_left hLN hε.le
    obtain ⟨x, hx⟩ := nonempty_badicIoo hb0 N m'
    refine ⟨x, ?_, hKsub (badicIoo_append_subset hb0 m w hx)⟩
    simp only [U, mem_iUnion]
    exact ⟨N, hMN, m', hbound, hx⟩

/-- On a residual set of reals, the frequency of digit `d` in base `b ≥ 2` exceeds `1 - ε`
infinitely often. -/
theorem residual_setOf_frequently_digitFreq_gt {b : ℕ} (hb : 2 ≤ b) (d : Fin b)
    {ε : ℝ} (hε : 0 < ε) :
    {x : ℝ | ∃ᶠ N in atTop,
      1 - ε < (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N} ∈ residual ℝ := by
  have hb0 : 0 < b := by omega
  let U : ℕ → Set ℝ := fun M ↦
    ⋃ (N : ℕ) (_ : M ≤ N) (m : ℤ)
      (_ : ∀ x ∈ badicIoo b N m, 1 - ε < (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N),
      badicIoo b N m
  have hsub : (⋂ M : ℕ, U M) ⊆
      {x : ℝ | ∃ᶠ N in atTop, 1 - ε < (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N} := by
    intro x hx
    rw [mem_ofPred_eq, Filter.frequently_atTop]
    intro M
    have hM := mem_iInter.1 hx M
    simp only [U, mem_iUnion] at hM
    rcases hM with ⟨N, hMN, m, hbound, hxIoo⟩
    exact ⟨N, hMN, hbound x hxIoo⟩
  refine Filter.mem_of_superset (countable_iInter_mem.2 fun M ↦ ?_) hsub
  refine residual_of_dense_open ?_ ?_
  · exact isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦
      isOpen_iUnion fun _ ↦ isOpen_badicIoo _ _ _
  · refine dense_of_forall_Ioo_nonempty fun u v huv ↦ ?_
    obtain ⟨K, m, hKsub⟩ := exists_badicIoo_subset hb huv
    obtain ⟨L, hL⟩ := exists_nat_gt ((K : ℝ) / ε)
    let L' := max L M
    let N := K + L'
    have hMN : M ≤ N := le_trans (le_max_right L M) (Nat.le_add_left L' K)
    let w : Fin L' → Fin b := fun _ ↦ d
    let m' : ℤ := m * (b : ℤ) ^ L' + (blockCode w : ℕ)
    have hbound : ∀ x ∈ badicIoo b N m',
        1 - ε < (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N := by
      intro x hx
      have hdig := digit_of_mem_badicIoo_append hb0 m w hx
      have hcard : L' ≤ blockCount b x (fun _ : Fin 1 ↦ d) N := by
        classical
        rw [blockCount]
        calc L' = (Finset.Ico K N).card := by simp [N]
          _ ≤ ((Finset.range N).filter fun i ↦ ∀ j : Fin 1, digit b x (i + j) = d).card := by
              refine Finset.card_le_card fun i hi ↦ ?_
              rw [Finset.mem_Ico] at hi
              rw [Finset.mem_filter, Finset.mem_range]
              refine ⟨hi.2, fun j ↦ ?_⟩
              have hj : (j : ℕ) = 0 := Fin.eq_zero j ▸ rfl
              rw [hj, add_zero]
              have h2 := hdig ⟨i - K, by omega⟩
              have heq : K + (i - K) = i := by omega
              rw [heq] at h2
              exact h2
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_le_of_lt (by positivity) hL
        have : 0 < L := by exact_mod_cast hLpos
        have : 0 < N := by omega
        exact_mod_cast this
      rw [lt_div_iff₀ hNpos]
      have hKlt : (K : ℝ) < ε * (L : ℝ) := (div_lt_iff₀ hε).1 hL |>.trans_eq (mul_comm _ _)
      have hLN : (L : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast le_trans (le_max_left L M) (Nat.le_add_left L' K)
      have hKltN : (K : ℝ) < ε * (N : ℝ) :=
        lt_of_lt_of_le hKlt (mul_le_mul_of_nonneg_left hLN hε.le)
      have hNsub : (N : ℝ) - (K : ℝ) = (L' : ℝ) := by
        have : (N : ℝ) = (K : ℝ) + (L' : ℝ) := by exact_mod_cast rfl
        linarith
      have hcard' : (L' : ℝ) ≤ (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) := by exact_mod_cast hcard
      linarith
    obtain ⟨x, hx⟩ := nonempty_badicIoo hb0 N m'
    refine ⟨x, ?_, hKsub (badicIoo_append_subset hb0 m w hx)⟩
    simp only [U, mem_iUnion]
    exact ⟨N, hMN, m', hbound, hx⟩

/-- For any base `b ≥ 2` and digit `d : Fin b`, the set of real numbers for which the asymptotic
frequency of digit `d` converges is meagre in `ℝ` (Šalát 1966). -/
theorem isMeagre_setOf_tendsto_digitFreq {b : ℕ} (hb : 2 ≤ b) (d : Fin b) :
    IsMeagre {x : ℝ | ∃ L : ℝ,
      Tendsto (fun N : ℕ ↦ (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N) atTop (𝓝 L)} := by
  rw [IsMeagre]
  have h1 := residual_setOf_frequently_digitFreq_lt hb d (ε := (1 : ℝ) / 4) (by norm_num)
  have h2 := residual_setOf_frequently_digitFreq_gt hb d (ε := (1 : ℝ) / 4) (by norm_num)
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro x ⟨hlow, hhigh⟩ ⟨L, hL⟩
  have hle : L ≤ 1 / 4 := by
    by_contra hgt
    push Not at hgt
    have hev : ∀ᶠ N in atTop, (1 : ℝ) / 4 < (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N :=
      hL.eventually (Ioi_mem_nhds hgt)
    exact (hlow.and_eventually hev).exists.elim fun _ ⟨h1, h2⟩ ↦ lt_asymm h1 h2
  have hge : 3 / 4 ≤ L := by
    by_contra hlt
    push Not at hlt
    have hev : ∀ᶠ N in atTop, (blockCount b x (fun _ : Fin 1 ↦ d) N : ℝ) / N < (3 : ℝ) / 4 :=
      hL.eventually (Iio_mem_nhds hlt)
    exact (hhigh.and_eventually hev).exists.elim fun _ ⟨h1, h2⟩ ↦ by linarith
  linarith

/-- For `2 ≤ b`, the set of base-`b` simply normal numbers is meagre in `ℝ`. -/
theorem isMeagre_setOf_isSimplyNormalIn {b : ℕ} (hb : 2 ≤ b) :
    IsMeagre {x : ℝ | IsSimplyNormalIn b x} := by
  refine (isMeagre_setOf_tendsto_digitFreq hb ⟨0, by omega⟩).mono ?_
  intro x hx
  exact ⟨(b : ℝ)⁻¹, hx ⟨0, by omega⟩⟩

/-- For `2 ≤ b`, the set of base-`b` normal numbers is meagre in `ℝ`. -/
theorem isMeagre_setOf_isNormalIn {b : ℕ} (hb : 2 ≤ b) :
    IsMeagre {x : ℝ | IsNormalIn b x} :=
  (isMeagre_setOf_isSimplyNormalIn hb).mono fun _ hx ↦ hx.isSimplyNormalIn

/-- The set of real numbers that are simply normal in *at least one* base `b ≥ 2` is meagre in
`ℝ`. -/
theorem isMeagre_setOf_exists_isSimplyNormalIn :
    IsMeagre {x : ℝ | ∃ b : ℕ, 2 ≤ b ∧ IsSimplyNormalIn b x} := by
  have heq : {x : ℝ | ∃ b : ℕ, 2 ≤ b ∧ IsSimplyNormalIn b x} =
      ⋃ b : ℕ, ⋃ (_ : 2 ≤ b), {x : ℝ | IsSimplyNormalIn b x} := by
    ext x; simp
  rw [heq]
  exact isMeagre_iUnion fun b ↦ isMeagre_iUnion fun hb ↦ isMeagre_setOf_isSimplyNormalIn hb

/-- The set of real numbers that are normal in *at least one* base `b ≥ 2` is meagre in `ℝ`. -/
theorem isMeagre_setOf_exists_isNormalIn :
    IsMeagre {x : ℝ | ∃ b : ℕ, 2 ≤ b ∧ IsNormalIn b x} := by
  refine isMeagre_setOf_exists_isSimplyNormalIn.mono ?_
  rintro x ⟨b, hb, hx⟩
  exact ⟨b, hb, hx.isSimplyNormalIn⟩

/-- The set of absolutely normal numbers is meagre in `ℝ`, in sharp contrast to Borel's theorem
(`Real.ae_isAbsolutelyNormal`) which states that it has full Lebesgue measure. -/
theorem isMeagre_setOf_isAbsolutelyNormal :
    IsMeagre {x : ℝ | IsAbsolutelyNormal x} :=
  (isMeagre_setOf_isNormalIn (b := 2) le_rfl).mono fun _ hx ↦ hx 2 le_rfl

/-! ### Generic reals: absolutely disjunctive yet nowhere simply normal -/

/-- The generic real number (in the sense of Baire category) is disjunctive in *every* base
`b ≥ 2` yet simply normal in *no* base `b ≥ 2` (Calude–Zamfirescu 1999). -/
theorem residual_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x} ∈ residual ℝ := by
  have h1 := residual_setOf_forall_isDisjunctiveIn
  have h2 : {x : ℝ | ∃ b : ℕ, 2 ≤ b ∧ IsSimplyNormalIn b x}ᶜ ∈ residual ℝ :=
    isMeagre_setOf_exists_isSimplyNormalIn
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro x ⟨hdisj, hnot⟩ b hb
  exact ⟨hdisj b hb, fun hsn ↦ hnot ⟨b, hb, hsn⟩⟩

/-- The set of absolutely disjunctive, nowhere simply normal reals is dense in `ℝ`. -/
theorem dense_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    Dense {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x} :=
  dense_of_mem_residual residual_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn

/-- Every countable subset of `ℝ` is meagre. -/
private lemma isMeagre_of_countable {s : Set ℝ} (hs : s.Countable) : IsMeagre s := by
  rw [← Set.biUnion_of_singleton s]
  refine isMeagre_biUnion hs fun x _ ↦ ?_
  rw [IsMeagre]
  exact residual_of_dense_open isOpen_compl_singleton (dense_compl_singleton x)

/-- The set of absolutely disjunctive, nowhere simply normal reals is uncountable. -/
theorem not_countable_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    ¬ {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x}.Countable := by
  intro hcount
  exact not_isMeagre_of_mem_residual
    residual_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn
    (isMeagre_of_countable hcount)

/-- There exists a real number that is disjunctive in every base `b ≥ 2` yet not simply normal in
any base `b ≥ 2`. -/
theorem exists_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    ∃ x : ℝ, ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x :=
  dense_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn.nonempty

/-- Measure-versus-category dichotomy: although the set of absolutely disjunctive, nowhere simply
normal numbers is residual (comeagre) in `ℝ`, it has Lebesgue measure zero. -/
theorem volume_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn :
    volume {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x} = 0 := by
  refine measure_mono_null ?_ volume_setOf_not_isAbsolutelyNormal
  intro x hx habs
  exact (hx 2 le_rfl).2 (habs 2 le_rfl).isSimplyNormalIn

/-- Every real number `y` can be written as a sum `x₁ + x₂ = y` of two real numbers that are both
disjunctive in every base `b ≥ 2` yet simply normal in no base `b ≥ 2`. -/
theorem exists_add_eq_forall_isDisjunctiveIn_and_not_isSimplyNormalIn (y : ℝ) :
    ∃ x₁ x₂ : ℝ, x₁ + x₂ = y ∧
      (∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x₁ ∧ ¬ IsSimplyNormalIn b x₁) ∧
      (∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x₂ ∧ ¬ IsSimplyNormalIn b x₂) := by
  let S : Set ℝ := {x : ℝ | ∀ b : ℕ, 2 ≤ b → IsDisjunctiveIn b x ∧ ¬ IsSimplyNormalIn b x}
  have hS : S ∈ residual ℝ := residual_setOf_forall_isDisjunctiveIn_and_not_isSimplyNormalIn
  let f : ℝ ≃ₜ ℝ := Homeomorph.subLeft y
  have hfS : f ⁻¹' S ∈ residual ℝ := by
    have hmap : (residual ℝ).map f = residual ℝ := f.residual_map_eq
    rwa [← Filter.mem_map, hmap]
  obtain ⟨x₁, hx₁, hx₂⟩ := (dense_of_mem_residual (Filter.inter_mem hS hfS)).nonempty
  exact ⟨x₁, y - x₁, add_sub_cancel _ _, hx₁, hx₂⟩

end Real
