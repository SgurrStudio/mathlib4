/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.Imported.NormalNumbers.CantorLiouvilleAll
public import Mathlib.NumberTheory.Normal.Bridge

/-!
# Cassels' theorem: almost every point of the Cantor set is normal in other bases

Let `μ` be the Cantor measure, the law of `∑ᵢ 2 εᵢ 3⁻ⁱ⁻¹` for independent fair coins `εᵢ`.
**Cassels** (1959) proved that `μ`-almost every point is normal in every base `b ≥ 2` that is not
a power of `3`. Such points lie in the middle-third Cantor set, so they are not normal in base `3`.

## Main statements

* `NormalNumbers.CantorLiouvilleAll.cassels1959`: Morris's statement
  `NormalNumbers.CantorLiouvilleAll.Literature.Cassels1959`.
* `Real.ae_isNormalIn_cantor`: the same statement with `Real.IsNormalIn`.

## Proof

By the Davenport–Erdős–LeVeque criterion (`CantorLiouvilleAll.ae_isNormal_of_secondMoment`) it is
enough to bound `∫ ‖∑_{k<N} e(h bᵏ x)‖² dμ(x)` by `N²` times a quantity summable along a
schedule with ratio tending to `1`. Expanding the square gives `μ̂(h(bⁿ − bᵐ))`, and
`|μ̂(ξ)| = ∏ₚ |cos(2πξ/3ᵖ⁺¹)|`.

* If `3 ∤ b`, this is Morris's `CantorLiouvilleAll.secondMoment_le_b` with every ternary position
  free.
* If `b = 3ᵃ m` with `a ≥ 1`, `m ≥ 2` and `3 ∤ m`, the frequency of the pair `(l + d, l)` is
  `3^{e + al} · c mᴸ` with `c = |h'| (bᵈ − 1)` prime to `3` (`h = 3ᵉ h'`). The factor `3^{e+al}`
  only removes the leading cosine factors, which are `1`, so the sum over `l` is the orbit sum
  `∑_l Hf (c mˡ)` that `CantorLiouvilleAll.sum_Hf_le_b` bounds for the base `m` prime to `3`.
  No `d` is exceptional, since `bᵈ − 1 ≡ 2 mod 3`.

## References

* [J. W. S. Cassels, *On a problem of Steinhaus about normal numbers*][Cassels1959]
* Trevor Morris, [normal-numbers](https://github.com/gotrevor/normal-numbers) (`CantorLiouvilleAll`)
-/

@[expose] public section

open MeasureTheory

namespace NormalNumbers.CantorLiouvilleAll

open CantorLiouville ExplicitSquare

namespace Cassels

open DecayAeNormal

/-- All ternary positions free: the Cantor measure. -/
abbrev allFree : ℕ → Bool := fun _ ↦ true

theorem posSet_allFree (v k : ℕ) : posSet allFree v k = Finset.Ico (v + 1) (v + k) := by
  ext p; simp [posSet]; omega

/-- With every position free, the majorant `Hf` does not depend on the offset. -/
theorem Hf_allFree (v k : ℕ) (u : ℝ) : Hf allFree v k u = Hf allFree 0 k u := by
  unfold Hf
  rw [posSet_allFree, posSet_allFree, show v + 1 = 1 + v by ring, show v + k = k + v by ring,
    ← Finset.prod_Ico_add']
  refine Finset.prod_congr (by simp) fun p _ ↦ ?_
  congr 2
  rw [pow_zero, one_mul, show p + v + 1 = (p + 1) + v by ring, pow_add]
  field_simp

theorem card_posSet_allFree (j : ℕ) : (posSet allFree 0 (j + 1)).card = j := by
  simp [posSet_allFree]

/-- The Fourier coefficient of the Cantor measure at `3ᵛ u` is bounded by the majorant of `u`. -/
theorem charFun_le_Hf (ξ : ℝ) (v j u : ℕ) (hξ : |ξ| = 3 ^ v * (u : ℝ)) :
    ‖∫ ω, ee (ξ * pt allFree ω) ∂coinMeasure‖ ≤ Hf allFree 0 (j + 1) u := by
  have h1 := charFun_real (v + (j + 1)) allFree ξ
  have h2 : Bf allFree (v + (j + 1)) ξ ≤ Hf allFree v (j + 1) u := by
    rw [← Bf_abs, hξ]; exact Bf_le_Hf allFree v (j + 1) u
  exact (h1.trans h2).trans (le_of_eq (Hf_allFree v (j + 1) u))

theorem charFun_le_one (ξ : ℝ) : ‖∫ ω, ee (ξ * pt allFree ω) ∂coinMeasure‖ ≤ 1 := by
  simpa using charFun_real 0 allFree ξ

/-- The second moment expanded into Fourier coefficients. -/
theorem secondMoment_expand (b : ℕ) (h : ℤ) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt allFree ω)‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * pt allFree ω) ∂coinMeasure‖ := by
  have hG := measurable_pt allFree
  have hint : ∀ ξ : ℝ, Integrable (fun ω ↦ ee (ξ * pt allFree ω)) coinMeasure := fun ξ ↦
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun ω ↦ (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt allFree ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * pt allFree ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k ↦ h * (b : ℝ) ^ k * pt allFree ω)]
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt allFree ω)‖ ^ 2
      ∂coinMeasure : ℝ) : ℂ) = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * pt allFree ω) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ ↦ integrable_finsetSum _ fun m _ ↦ hint _]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [integral_finsetSum _ fun m _ ↦ hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  exact Finset.sum_le_sum fun n _ ↦ norm_sum_le _ _

/-- **Second moment for `b = 3ᵃ m`**, `a ≥ 1`, `m ≥ 2`, `3 ∤ m`. -/
theorem secondMoment_le_three_dvd {b a m : ℕ} (hbam : b = 3 ^ a * m) (ha : 1 ≤ a) (hm : 2 ≤ m)
    (hm3 : ¬ 3 ∣ m) (h : ℤ) (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt allFree ω)‖ ^ 2 ∂coinMeasure ≤
      N + 6 * (N : ℝ) ^ 2 * (3 / 2 : ℝ) ^ tb m * (2 / 3 : ℝ) ^ (Nat.log 3 N / 2) := by
  obtain ⟨e, h', hh3, hhe⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hh) 3 (by norm_num)
  set j := Nat.log 3 N / 2
  have h3j : 3 ^ j ≤ N :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
      (Nat.pow_log_le_self 3 (by omega))
  have hb1 : 1 ≤ b := by subst hbam; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  set G : ℕ → ℕ → ℝ := fun d l ↦ Hf allFree 0 (j + 1) ((h' * (b ^ d - 1) * m ^ l : ℕ) : ℝ)
  have hfreq : ∀ l d : ℕ, |(h : ℝ) * ((b : ℝ) ^ (l + d) - (b : ℝ) ^ l)| =
      3 ^ (e + a * l) * ((h' * (b ^ d - 1) * m ^ l : ℕ) : ℝ) := by
    intro l d
    have hbd : (1 : ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hb1)
    have habs : |(h : ℝ)| = (3 : ℝ) ^ e * h' := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, hhe]; push_cast; ring
    rw [abs_mul, habs, show (b : ℝ) ^ (l + d) - (b : ℝ) ^ l = (b : ℝ) ^ l * ((b : ℝ) ^ d - 1) by
      ring, abs_of_nonneg (mul_nonneg (by positivity) (by linarith))]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow d b (by omega)), hbam]
    push_cast; ring
  have hΦ : ∀ l d : ℕ, ∀ ξ : ℝ, |ξ| = |(h : ℝ) * ((b : ℝ) ^ (l + d) - (b : ℝ) ^ l)| →
      ‖∫ ω, ee (ξ * pt allFree ω) ∂coinMeasure‖ ≤ G d l := fun l d ξ hξ ↦
    charFun_le_Hf ξ (e + a * l) j _ (hξ.trans (hfreq l d))
  have hpair := pair_sum_le
    (fun n m' ↦ ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m')) * pt allFree ω) ∂coinMeasure‖) G
    (fun d l ↦ Hf_nonneg _ _ _ _) (fun n ↦ charFun_le_one _)
    (fun n m' hmn ↦ hΦ m' (n - m') _ (by rw [show m' + (n - m') = n by omega]))
    (fun n m' hmn ↦ hΦ n (m' - n) _ (by
      rw [show n + (m' - n) = m' by omega, ← abs_neg]; congr 1; ring)) N
  set P := (2 / 3 : ℝ) ^ j
  set Tc := (3 / 2 : ℝ) ^ tb m
  have hd : ∀ d ∈ Finset.Ico 1 N, ∑ l ∈ Finset.range N, G d l ≤ 3 * N * Tc * P := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hc : ¬ 3 ∣ h' * (b ^ d - 1) := by
      intro hc
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hc with hc | hc
      · exact hh3 hc
      · have h3b : 3 ∣ b ^ d := dvd_pow (hbam ▸ dvd_mul_of_dvd_left (dvd_pow_self 3
          (by omega)) m) (by omega)
        have := Nat.dvd_sub h3b hc
        rw [Nat.sub_sub_self (Nat.one_le_pow d b (by omega))] at this
        omega
    have := sum_Hf_le_b allFree hm hm3 0 j (h' * (b ^ d - 1)) hc N
    rw [card_posSet_allFree] at this
    have h3j' : (2 * 3 ^ j : ℝ) ≤ 2 * N := by exact_mod_cast Nat.mul_le_mul_left 2 h3j
    calc _ ≤ _ := this
      _ ≤ (N + 2 * N) * Tc * P := by gcongr
      _ = _ := by ring
  have hsum : ∑ d ∈ Finset.Ico 1 N, ∑ l ∈ Finset.range N, G d l ≤ N * (3 * N * Tc * P) := by
    refine (Finset.sum_le_sum hd).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    gcongr
  refine (secondMoment_expand b h N).trans (hpair.trans ?_)
  nlinarith

/-- A bound of the shape used along Morris's schedule gives almost sure normality. -/
theorem ae_isNormal_of_bound {b : ℕ} (hb : 2 ≤ b)
    (H : ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt allFree ω)‖ ^ 2 ∂coinMeasure ≤
        C * (N : ℝ) ^ 2 * (Real.exp (-(Real.log (3 / 2) / 2) *
          freeCount isFree (Nat.log 3 N / 2)) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (pt allFree ω) := by
  refine ae_isNormal_of_secondMoment coinMeasure hb _ (measurable_pt allFree) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  obtain ⟨C, hC, hB⟩ := H h hh
  have hl : 0 < Real.log (3 / 2) / 2 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); linarith
  refine (summable_sched_bound _ _ hC hl).of_nonneg_of_le
    (fun j ↦ div_nonneg (integral_nonneg fun ω ↦ by positivity) (by positivity))
    (fun j ↦ ?_)
  have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := hB (sched j) (one_le_sched j)
    _ = _ := by ring

theorem exp_freeCount_le {F M : ℕ} (hFM : F ≤ M) :
    Real.exp (-(Real.log (3 / 2) / 2) * M) ≤ Real.exp (-(Real.log (3 / 2) / 2) * F) := by
  have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2)
  have : (F : ℝ) ≤ M := by exact_mod_cast hFM
  exact Real.exp_le_exp.2 (by nlinarith)

theorem freeCount_le_self (free : ℕ → Bool) (M : ℕ) : freeCount free M ≤ M := by
  unfold freeCount; exact (Finset.card_filter_le _ _).trans (by simp)

theorem freeCount_allFree (M : ℕ) : freeCount allFree M = M := by
  simp [freeCount]

theorem le_rpow_neg_half {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (N : ℝ) ^ 2 = N * N ^ (1 : ℝ) by rw [Real.rpow_one]; ring, mul_assoc,
      ← Real.rpow_add (by positivity)]
    norm_num
  rw [this]
  have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN0 (by norm_num)
  nlinarith

theorem ae_isNormal_of_not_three_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (pt allFree ω) := by
  refine ae_isNormal_of_bound hb fun h hh ↦ ⟨16 * (b : ℝ) ^ 6 * |(h : ℝ)|, ?_, fun N hN ↦ ?_⟩
  · have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have h1 : Real.exp (-(Real.log (3 / 2) / 2) * (freeCount allFree (Nat.log 3 N / 2) : ℝ)) ≤
      Real.exp (-(Real.log (3 / 2) / 2) * (freeCount isFree (Nat.log 3 N / 2) : ℝ)) := by
    rw [freeCount_allFree]; exact exp_freeCount_le (freeCount_le_self _ _)
  exact (secondMoment_le_b allFree hb h3 h hh N hN).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left h1 _) (by positivity))

theorem ae_isNormal_of_three_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hpow : ∀ k : ℕ, b ≠ 3 ^ k) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (pt allFree ω) := by
  obtain ⟨a, m, hm3, hbam⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : b ≠ 0) 3 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hbam; omega
  have hm1 : m ≠ 1 := by rintro rfl; exact hpow a (by simpa using hbam)
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [pow_zero, one_mul] at hbam; exact absurd (hbam ▸ h3) hm3
    · exact ha
  refine ae_isNormal_of_bound hb fun h hh ↦
    ⟨9 * (3 / 2 : ℝ) ^ tb m + 1, by positivity, fun N hN ↦ ?_⟩
  refine (secondMoment_le_three_dvd hbam ha (by omega) hm3 h hh N hN).trans ?_
  set M := Nat.log 3 N / 2
  set E := Real.exp (-(Real.log (3 / 2) / 2) * freeCount isFree M)
  set R := (N : ℝ) ^ (-(1 / 2 : ℝ))
  set Tc := (3 / 2 : ℝ) ^ tb m
  have hP : (2 / 3 : ℝ) ^ M ≤ 3 / 2 * E := by
    calc (2 / 3 : ℝ) ^ M ≤ (2 / 3 : ℝ) ^ (M / 2) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_self _ _)
      _ ≤ 3 / 2 * Real.exp (-(Real.log (3 / 2) / 2) * M) := pow_two_sub_le _ _ rfl
      _ ≤ 3 / 2 * E := by gcongr; exact exp_freeCount_le (freeCount_le_self isFree M)
  have hNR := le_rpow_neg_half hN
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hR : 0 ≤ R := by positivity
  have hT : 0 ≤ Tc := by positivity
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 6 * (N : ℝ) ^ 2 * Tc)
  have : (0 : ℝ) ≤ (N : ℝ) ^ 2 * E := by positivity
  have : (0 : ℝ) ≤ Tc * ((N : ℝ) ^ 2 * R) := by positivity
  nlinarith

end Cassels

/-- **Cassels' theorem** (1959), in Morris's terms: for fair coins `ω`, almost surely the point
`∑ᵢ 2 ωᵢ 3⁻ⁱ⁻¹` of the Cantor set is normal in every base that is not a power of `3`. -/
theorem cassels1959 : Literature.Cassels1959 := by
  unfold Literature.Cassels1959
  have key : ∀ b : ℕ, ∀ᵐ ω ∂coinMeasure, 2 ≤ b → (∀ k : ℕ, b ≠ 3 ^ k) →
      IsNormal b (pt (fun _ ↦ true) ω) := by
    intro b
    by_cases hb : 2 ≤ b
    · by_cases hpow : ∀ k : ℕ, b ≠ 3 ^ k
      · by_cases h3 : 3 ∣ b
        · filter_upwards [Cassels.ae_isNormal_of_three_dvd hb h3 hpow] with ω hω _ _ using hω
        · filter_upwards [Cassels.ae_isNormal_of_not_three_dvd hb h3] with ω hω _ _ using hω
      · exact Filter.Eventually.of_forall fun ω _ h ↦ absurd h hpow
    · exact Filter.Eventually.of_forall fun ω h ↦ absurd h hb
  filter_upwards [ae_all_iff.2 key] with ω hω b using hω b

end NormalNumbers.CantorLiouvilleAll

namespace Real

open NormalNumbers.CantorLiouville NormalNumbers.ExplicitSquare

/-- **Cassels' theorem** (1959): almost every point of the middle-third Cantor set, for the
Cantor measure, is normal in every base `b ≥ 2` that is not a power of `3`. The Cantor measure is
the law of `pt (fun _ ↦ true)` under fair coins. -/
theorem ae_isNormalIn_cantor :
    ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (∀ k : ℕ, b ≠ 3 ^ k) →
      IsNormalIn b (pt (fun _ ↦ true) ω) := by
  filter_upwards [NormalNumbers.CantorLiouvilleAll.cassels1959] with ω hω b hb hk
  rw [isNormalIn_iff_isNormal]
  exact hω b hb hk

end Real
