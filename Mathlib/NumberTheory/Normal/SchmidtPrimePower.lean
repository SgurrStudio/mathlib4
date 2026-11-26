/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.BasePow
public import Mathlib.NumberTheory.Normal.Cassels
public import Mathlib.NumberTheory.Normal.CopelandErdos
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Schmidt's theorem when one base is a prime power

Let `p` be a prime and `b ≥ 2` an integer that is not a power of `p`. We show that some real
number is normal in base `b` but not in base `p` (hence in no base `pʲ`).

## Proof

Fix `q = pᵏ ≥ 3` and let `X = ∑ᵢ εᵢ q⁻ⁱ⁻¹` for independent fair coins `εᵢ`. Every base-`q` digit of
`X` is `0` or `1`, so `X` is never normal in base `q`. Its Fourier transform satisfies
`|𝔼 e(ξX)| ≤ ∏_{i<K} |cos(πξ/qⁱ⁺¹)|` for every `K` (`charFun_le`), and we show that `X` is almost
surely normal in base `b` by the Davenport–Erdős–LeVeque criterion.

Write `b = pᵃ m` with `p ∤ m` and `m ≥ 2`. The frequency of a pair `(l + d, l)` in the second
moment is `h (bᵈ − 1) bˡ = p^v · w mˡ` with `p ∤ w`. Dropping the leading cosine factors, its
coefficient is at most `Ψ_K(pʳ w mˡ)` with `r = v mod k` (`charFun_le_rieszPsi`). For
`g = m^{2(p−1)}` and `t = v_p(g − 1)`, lifting the exponent shows that `l ↦ w gˡ` runs once
through the residues `≡ w mod pᵗ` modulo `p^{t+n}` as `l < pⁿ`. Averaging `Ψ_K` over a residue
class modulo `pᵗ` gains a factor `1/√2` for each further base-`q` digit, because
`∑_{r<q} |cos(θ + πr/q)| ≤ q/√2` (`sum_abs_cos_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Real.SchmidtPrimePower

open NormalNumbers NormalNumbers.CantorLiouville NormalNumbers.CantorLiouvilleAll
  NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare NormalNumbers.CantorSelfSimilar

/-! ### The random point -/

/-- The point `X = ∑ᵢ εᵢ q⁻ⁱ⁻¹` with base-`q` digits `εᵢ ∈ {0, 1}`. -/
noncomputable def coinPoint (q : ℕ) (ω : ℕ → Bool) : ℝ :=
  realOfDigits q fun i ↦ if ω i then 1 else 0

theorem measurable_coinPoint (q : ℕ) : Measurable (coinPoint q) := by
  unfold coinPoint realOfDigits
  refine Measurable.tsum fun i ↦ Measurable.div_const ?_ _
  refine Measurable.comp (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))) ?_
  exact (measurable_of_countable (fun b : Bool ↦ if b then 1 else 0)).comp (measurable_pi_apply i)

theorem summable_coinPoint (q : ℕ) (hq : 2 ≤ q) (ω : ℕ → Bool) :
    Summable fun i ↦ (((if ω i then 1 else 0 : ℕ)) : ℝ) / (q : ℝ) ^ (i + 1) := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  refine Summable.of_nonneg_of_le (fun i ↦ by positivity) (fun i ↦ ?_)
    ((summable_geometric_of_lt_one (r := (q : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hq')))
  have : (((if ω i then 1 else 0 : ℕ)) : ℝ) ≤ 1 := by split_ifs <;> simp
  rw [inv_pow, div_le_iff₀ (by positivity), pow_succ, inv_mul_cancel_left₀ (by positivity)]
  nlinarith [one_le_pow₀ hq'.le (n := i)]

theorem coinPoint_consB (q : ℕ) (hq : 2 ≤ q) (c : Bool) (ω : ℕ → Bool) :
    coinPoint q (consB c ω) = (if c then 1 else 0) / q + coinPoint q ω / q := by
  unfold coinPoint realOfDigits
  rw [(summable_coinPoint q hq (consB c ω)).tsum_eq_zero_add, ← tsum_div_const]
  congr 1
  · cases c <;> simp [consB]
  · refine tsum_congr fun i ↦ ?_
    simp only [consB]
    rw [pow_succ _ (i + 1), div_div]
    congr

/-- **Riesz-product bound** for the characteristic function of `X`. -/
theorem charFun_le (q : ℕ) (hq : 2 ≤ q) (M : ℕ) : ∀ ξ : ℝ,
    ‖∫ ω, ee (ξ * coinPoint q ω) ∂coinMeasure‖ ≤
      ∏ i ∈ Finset.range M, |Real.cos (Real.pi * ξ / q ^ (i + 1))| := by
  induction M with
  | zero =>
    intro ξ
    simp only [Finset.range_zero, Finset.prod_empty]
    refine (norm_integral_le_of_norm_le_const (C := 1)
      (Eventually.of_forall fun ω ↦ (norm_ee _).le)).trans ?_
    simp
  | succ M ih =>
    intro ξ
    set g : (ℕ → Bool) → ℂ := fun ω ↦ ee (ξ * coinPoint q ω)
    have hgm : Measurable g := measurable_ee.comp ((measurable_coinPoint q).const_mul ξ)
    have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ ↦
      Integrable.of_bound hgm.aestronglyMeasurable 1
        (Eventually.of_forall fun ω ↦ (norm_ee _).le)
    set I' := ∫ ω, ee (ξ / q * coinPoint q ω) ∂coinMeasure
    have hc : ∀ c, ∫ ω, g (consB c ω) ∂coinMeasure =
        ee (ξ * ((if c then 1 else 0) / q)) * I' := by
      intro c
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
      simp only [g, coinPoint_consB q hq, ← ee_add]
      congr 1; ring
    have hsplit : ∫ ω, g ω ∂coinMeasure =
        2⁻¹ * ∫ ω, g (consB true ω) ∂coinMeasure +
          2⁻¹ * ∫ ω, g (consB false ω) ∂coinMeasure := by
      conv_lhs => rw [coinMeasure_eq]
      rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
          ((hgi _ inferInstance).smul_measure (by simp)),
        integral_smul_measure, integral_smul_measure,
        integral_map (measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
        integral_map (measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
      simp [ENNReal.toReal_inv]
    have hI' := ih (ξ / q)
    change ‖∫ ω, g ω ∂coinMeasure‖ ≤ _
    rw [hsplit, hc, hc, Finset.prod_range_succ']
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hre : ∏ i ∈ Finset.range M, |Real.cos (Real.pi * ξ / q ^ (i + 1 + 1))| =
        ∏ i ∈ Finset.range M, |Real.cos (Real.pi * (ξ / q) / q ^ (i + 1))| := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      congr 2; rw [pow_succ]; field_simp
    rw [hre]
    have : 2⁻¹ * (ee (ξ * ((if true then 1 else 0) / q)) * I') +
        2⁻¹ * (ee (ξ * ((if false then 1 else 0) / q)) * I') = ((1 + ee (ξ / q)) / 2) * I' := by
      simp only [ite_true, Bool.false_eq_true, ite_false, zero_div, mul_zero]
      rw [show ξ * (1 / q) = ξ / q by ring]
      simp [ee]; ring
    rw [this, norm_mul, norm_one_add_ee_div_two, mul_comm,
      show Real.pi * ξ / (q : ℝ) ^ (0 + 1) = Real.pi * (ξ / q) by ring]
    exact mul_le_mul_of_nonneg_right hI' (abs_nonneg _)

/-! ### `X` is not normal in base `q` -/

/-- The base-`q` digits of `X`, as `Fin q`. -/
def digits (q : ℕ) (hq : 2 ≤ q) (ω : ℕ → Bool) (i : ℕ) : Fin q :=
  ⟨if ω i then 1 else 0, by split_ifs <;> omega⟩

theorem coinPoint_eq_ofDigits (q : ℕ) (hq : 2 ≤ q) (ω : ℕ → Bool) :
    coinPoint q ω = Real.ofDigits (digits q hq ω) := by
  unfold coinPoint realOfDigits Real.ofDigits Real.ofDigitsTerm
  refine tsum_congr fun i ↦ ?_
  simp only [digits, div_eq_mul_inv]

theorem digit_coinPoint (q : ℕ) (hq : 3 ≤ q) (ω : ℕ → Bool) (n : ℕ) :
    digit q (coinPoint q ω) n = if ω n then 1 else 0 := by
  rw [coinPoint_eq_ofDigits q (by omega), digit_ofDigits (by omega)]
  · rfl
  · intro n
    refine ⟨n + 1, by omega, ?_⟩
    simp only [digits]; split_ifs <;> omega

/-- `X` never shows the digit `q - 1 ≥ 2`, so it is not normal in base `q`. -/
theorem not_isNormalIn_coinPoint (q : ℕ) (hq : 3 ≤ q) (ω : ℕ → Bool) :
    ¬ IsNormalIn q (coinPoint q ω) := by
  intro h
  have h1 := h 1 fun _ ↦ ⟨q - 1, by omega⟩
  have h0 : ∀ N,
      blockCount q (coinPoint q ω) (fun _ : Fin 1 ↦ (⟨q - 1, by omega⟩ : Fin q)) N = 0 := by
    intro N
    classical
    simp only [blockCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    have := hi 0
    rw [digit_coinPoint q hq] at this
    split_ifs at this <;> omega
  simp only [h0, Nat.cast_zero, zero_div] at h1
  have := tendsto_nhds_unique tendsto_const_nhds h1
  have hq0 : (0 : ℝ) < (q : ℝ) ^ 1 := by positivity
  exact (inv_pos.2 hq0).ne this

/-! ### Averaging a cosine over `q` equally spaced shifts -/

theorem sum_cos_eq_zero (q : ℕ) (hq : 2 ≤ q) (α : ℝ) :
    ∑ r ∈ Finset.range q, Real.cos (α + 2 * Real.pi * r / q) = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp_of_coprime 1 q (by omega) (Nat.coprime_one_left q)
  have hg := hζ.geom_sum_eq_zero (by omega)
  have : ∑ r ∈ Finset.range q, (Complex.exp (α * Complex.I) *
      Complex.exp (2 * Real.pi * Complex.I * ((1 : ℕ) / q)) ^ r) = 0 := by
    rw [← Finset.mul_sum, hg, mul_zero]
  have h2 := congrArg Complex.re this
  rw [Complex.re_sum, Complex.zero_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Complex.exp_natCast_mul, ← Complex.exp_add,
    show (α : ℂ) * Complex.I + (r : ℂ) * (2 * Real.pi * Complex.I * ((1 : ℕ) / q)) =
      ((α + 2 * Real.pi * r / q : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- `∑_{r<q} |cos(θ + πr/q)| ≤ q/√2` for `q ≥ 2`. -/
theorem sum_abs_cos_le (q : ℕ) (hq : 2 ≤ q) (θ : ℝ) :
    ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * r / q)| ≤ q * Real.sqrt 2⁻¹ := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range q)
    (f := fun r : ℕ ↦ |Real.cos (θ + Real.pi * r / q)|)
  have hsq : ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * r / q)| ^ 2 = q / 2 := by
    have : ∀ r : ℕ, |Real.cos (θ + Real.pi * r / q)| ^ 2 =
        1 / 2 + Real.cos (2 * θ + 2 * Real.pi * r / q) / 2 := by
      intro r
      rw [sq_abs, Real.cos_sq]; congr 2; ring_nf
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_div (Finset.range q)
      (fun x : ℕ ↦ Real.cos (2 * θ + 2 * Real.pi * x / q)), sum_cos_eq_zero q hq]
    simp; ring
  rw [hsq, Finset.card_range] at hcs
  have h0 : 0 ≤ ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * r / q)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2⁻¹)
  have hs0 := Real.sqrt_nonneg (2⁻¹ : ℝ)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  set S := ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * r / q)|
  nlinarith [mul_nonneg hq0 hs0]

/-! ### The Riesz majorant `Ψ` -/

/-- `Ψ_K(u) = ∏_{i<K} |cos(πu/qⁱ⁺¹)|`, the Riesz majorant of the Fourier coefficient of `X` at
`u`. -/
noncomputable def rieszPsi (q K : ℕ) (u : ℝ) : ℝ :=
  ∏ i ∈ Finset.range K, |Real.cos (Real.pi * u / q ^ (i + 1))|

theorem rieszPsi_nonneg (q K : ℕ) (u : ℝ) : 0 ≤ rieszPsi q K u :=
  Finset.prod_nonneg fun _ _ ↦ abs_nonneg _

theorem rieszPsi_le_one (q K : ℕ) (u : ℝ) : rieszPsi q K u ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun _ _ ↦ Real.abs_cos_le_one _

theorem rieszPsi_succ (q K : ℕ) (u : ℝ) :
    rieszPsi q (K + 1) u = rieszPsi q K u * |Real.cos (Real.pi * u / q ^ (K + 1))| :=
  Finset.prod_range_succ _ _

theorem abs_cos_add_int_mul_pi (x : ℝ) (n : ℤ) : |Real.cos (x + n * Real.pi)| = |Real.cos x| := by
  rw [Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]

/-- `Ψ_K` has period `q^K`. -/
theorem rieszPsi_add (q K : ℕ) (hq : 1 ≤ q) (u : ℝ) (z : ℤ) :
    rieszPsi q K (u + q ^ K * z) = rieszPsi q K u := by
  unfold rieszPsi
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  simp only [Finset.mem_range] at hi
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : Real.pi * (u + q ^ K * z) / q ^ (i + 1) =
      Real.pi * u / q ^ (i + 1) + ((z * q ^ (K - (i + 1)) : ℤ) : ℝ) * Real.pi := by
    have hK : (q : ℝ) ^ K = q ^ (i + 1) * q ^ (K - (i + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [hK]; push_cast; field_simp
  rw [this, abs_cos_add_int_mul_pi]

theorem abs_cos_abs (x c : ℝ) : |Real.cos (Real.pi * |x| / c)| = |Real.cos (Real.pi * x / c)| := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  rw [show Real.pi * -x / c = -(Real.pi * x / c) by ring, Real.cos_neg]

/-- At a frequency `qˢ u`, the Fourier coefficient of `X` is at most `Ψ_K(u)` for every `K`. -/
theorem charFun_le_rieszPsi (q : ℕ) (hq : 2 ≤ q) (ξ : ℝ) (s K : ℕ) (u : ℝ)
    (hξ : |ξ| = q ^ s * u) :
    ‖∫ ω, ee (ξ * coinPoint q ω) ∂coinMeasure‖ ≤ rieszPsi q K u := by
  refine (charFun_le q hq (s + K) ξ).trans ?_
  rw [Finset.prod_range_add]
  have h1 : ∏ i ∈ Finset.range s, |Real.cos (Real.pi * ξ / q ^ (i + 1))| ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun _ _ ↦ Real.abs_cos_le_one _
  have h2 : ∏ i ∈ Finset.range K, |Real.cos (Real.pi * ξ / q ^ (s + i + 1))| = rieszPsi q K u := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← abs_cos_abs, hξ]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    congr 2
    rw [show s + i + 1 = s + (i + 1) by ring, pow_add]
    field_simp
  rw [h2]
  calc _ ≤ 1 * rieszPsi q K u := by gcongr; exact rieszPsi_nonneg _ _ _
    _ = _ := one_mul _

/-- **Averaging `Ψ` over a residue class.** If `τ + n₀ = k K₀` and `q = pᵏ`, the average of
`Ψ_{K₀+i}` over the class `c + pᵗ ℤ` (one period) is at most `2^{-i/2}`. -/
theorem sum_rieszPsi_class_le (p k q : ℕ) (hqk : q = p ^ k) (hq : 2 ≤ q) (τ n₀ K₀ : ℕ)
    (hK : τ + n₀ = k * K₀) (c : ℝ) (i : ℕ) :
    ∑ j ∈ Finset.range (p ^ n₀ * q ^ i), rieszPsi q (K₀ + i) (c + p ^ τ * j) ≤
      p ^ n₀ * q ^ i * Real.sqrt 2⁻¹ ^ i := by
  induction i with
  | zero =>
    simp only [pow_zero, mul_one, add_zero]
    refine (Finset.sum_le_sum fun j _ ↦ rieszPsi_le_one _ _ _).trans ?_
    simp
  | succ i ih =>
    set L := p ^ n₀ * q ^ i
    have hL : (p : ℝ) ^ τ * L = (q : ℝ) ^ (K₀ + i) := by
      simp only [L, hqk]; push_cast
      rw [← mul_assoc, ← pow_add, hK, pow_add, pow_mul]
    rw [show p ^ n₀ * q ^ (i + 1) = L * q by simp only [L]; ring, sum_range_mul_eq,
      Finset.sum_comm]
    have hterm : ∀ u t : ℕ, rieszPsi q (K₀ + (i + 1)) (c + p ^ τ * ((L * t + u : ℕ) : ℝ)) =
        rieszPsi q (K₀ + i) (c + p ^ τ * u) *
          |Real.cos (Real.pi * (c + p ^ τ * u) / q ^ (K₀ + i + 1) + Real.pi * t / q)| := by
      intro u t
      have e : c + (p : ℝ) ^ τ * ((L * t + u : ℕ) : ℝ) =
          (c + p ^ τ * u) + (q : ℝ) ^ (K₀ + i) * ((t : ℤ) : ℝ) := by
        push_cast; rw [← hL]; ring
      rw [← add_assoc, rieszPsi_succ, e, rieszPsi_add q _ (by omega)]
      simp only [Int.cast_natCast]
      congr 2
      have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [pow_succ]; field_simp
    simp_rw [hterm, ← Finset.mul_sum]
    have hρ : 0 ≤ Real.sqrt 2⁻¹ := Real.sqrt_nonneg _
    calc _ ≤ ∑ u ∈ Finset.range L, rieszPsi q (K₀ + i) (c + p ^ τ * u) * (q * Real.sqrt 2⁻¹) :=
          Finset.sum_le_sum fun u _ ↦ mul_le_mul_of_nonneg_left
            (sum_abs_cos_le q hq _) (rieszPsi_nonneg _ _ _)
      _ = (∑ u ∈ Finset.range L, rieszPsi q (K₀ + i) (c + p ^ τ * u)) * (q * Real.sqrt 2⁻¹) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (L * Real.sqrt 2⁻¹ ^ i) * (q * Real.sqrt 2⁻¹) := by
          gcongr; exact_mod_cast ih
      _ = _ := by simp only [L]; push_cast; ring

/-! ### Orbits of a unit modulo powers of `p` -/

/-- If `g ≡ 1 mod pᵗ` and no `g^d`, `0 < d < pⁿ`, is `≡ 1 mod p^{t+n}`, then `m ↦ u gᵐ`
(`m < pⁿ`) runs once through the residues `≡ u mod pᵗ` modulo `p^{t+n}`. -/
theorem orbit_sum_eq (p : ℕ) [hp : Fact p.Prime] (g t n u : ℕ) (hg1 : 1 ≤ g) (hgp : ¬ p ∣ g)
    (hgt : p ^ t ∣ g - 1) (hinj : ∀ d, 0 < d → d < p ^ n → ¬ p ^ (t + n) ∣ g ^ d - 1)
    (hu : ¬ p ∣ u) (F : ℕ → ℝ) (hF : ∀ w z, F (w + p ^ (t + n) * z) = F w) :
    ∑ m ∈ Finset.range (p ^ n), F (u * g ^ m) =
      ∑ j ∈ Finset.range (p ^ n), F (u % p ^ t + p ^ t * j) := by
  set Q := p ^ (t + n)
  have hp0 : 0 < p := hp.out.pos
  have hQ : Q = p ^ t * p ^ n := pow_add _ _ _
  have htQ : p ^ t ∣ Q := ⟨_, hQ⟩
  have hg : g ≡ 1 [MOD p ^ t] := ((Nat.modEq_iff_dvd' hg1).2 hgt).symm
  set φ : ℕ → ℕ := fun m ↦ (u * g ^ m % Q) / p ^ t
  have hmod : ∀ m, (u * g ^ m % Q) % p ^ t = u % p ^ t := by
    intro m
    rw [Nat.mod_mod_of_dvd _ htQ]
    have := (hg.pow m).mul_left u
    rwa [one_pow, mul_one] at this
  have hrec : ∀ m, u * g ^ m % Q = p ^ t * φ m + u % p ^ t := by
    intro m; rw [← hmod m]; exact (Nat.div_add_mod _ _).symm
  have hmaps : ∀ m ∈ Finset.range (p ^ n), φ m ∈ Finset.range (p ^ n) := by
    intro m _
    simp only [Finset.mem_range, φ]
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc _ < Q := Nat.mod_lt _ (by positivity)
      _ = _ := by rw [hQ, mul_comm]
  have hcopQ : ∀ m, Nat.Coprime Q (u * g ^ m) := by
    intro m
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h ↦ ?_)
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · exact hu h
    · exact hgp (hp.out.dvd_of_dvd_pow h)
  have hinj' : Set.InjOn φ (Finset.range (p ^ n) : Set ℕ) := by
    have key : ∀ m m', m < m' → m' < p ^ n → φ m ≠ φ m' := by
      intro m m' hmm' hm' heq
      have h1 : u * g ^ m ≡ u * g ^ m * g ^ (m' - m) [MOD Q] := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmm'.le]
        unfold Nat.ModEq; rw [hrec, hrec, heq]
      have h2 : 1 ≡ g ^ (m' - m) [MOD Q] :=
        Nat.ModEq.cancel_left_of_coprime (hcopQ m) (by simpa using h1)
      exact hinj (m' - m) (by omega) (by omega)
        ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h2)
    intro m hm m' hm' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hm hm'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key m m' h hm' heq
    · exact key m' m h hm heq.symm
  refine Finset.sum_nbij φ hmaps hinj'
    (Finset.surjOn_of_injOn_of_card_le _ hmaps hinj' le_rfl) ?_
  intro m _
  rw [← Nat.mod_add_div (u * g ^ m) Q, hF, hrec, add_comm]

/-! ### Lifting the exponent for `g = m^{2(p−1)}` -/

/-- The exponent `2(p − 1)`: `m^{2(p−1)} ≡ 1 mod p`, and mod `4` when `p = 2`. -/
def lteExp (p : ℕ) : ℕ := 2 * (p - 1)

/-- `t = v_p(m^{2(p−1)} − 1)`. -/
noncomputable def lteVal (p m : ℕ) : ℕ := multiplicity p (m ^ lteExp p - 1)

theorem two_le_pow_lteExp {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) : 2 ≤ m ^ lteExp p :=
  le_trans hm2 (Nat.le_self_pow (by unfold lteExp; have := hp.two_le; omega) m)

theorem lte_lteExp {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : ¬ p ∣ m) (hm2 : 2 ≤ m) {d : ℕ}
    (hd : d ≠ 0) : multiplicity p ((m ^ lteExp p) ^ d - 1) = lteVal p m + multiplicity p d := by
  rcases hp.out.eq_two_or_odd' with rfl | hodd
  · have hE : lteExp 2 = 2 := rfl
    unfold lteVal; rw [hE, ← pow_mul]
    have h1 := Nat.multiplicity_pow_two_sub_one (by omega : 1 < m) hm (n := 2 * d) (by omega)
      (even_two_mul d)
    have h2 := Nat.multiplicity_pow_two_sub_one (by omega : 1 < m) hm (n := 2) (by omega)
      even_two
    rw [Nat.multiplicity_mul (by norm_num) hd] at h1
    have h22 : multiplicity 2 2 = 1 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; exact Nat.Prime.multiplicity_self
    omega
  · have hg := two_le_pow_lteExp hp.out hm2 (p := p)
    have hcop : Nat.Coprime m p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
    have hferm : m ^ (p - 1) ≡ 1 [MOD p] := by
      simpa [Nat.totient_prime hp.out] using Nat.ModEq.pow_totient hcop
    have h1 : m ^ lteExp p ≡ 1 [MOD p] := by
      have := hferm.pow 2; rwa [one_pow, ← pow_mul, mul_comm] at this
    have hdvd : p ∣ m ^ lteExp p - 1 := (Nat.modEq_iff_dvd' (by omega)).1 h1.symm
    have hgp : ¬ p ∣ m ^ lteExp p := fun h ↦ hm (hp.out.dvd_of_dvd_pow h)
    have := Nat.multiplicity_pow_sub_pow hodd (x := m ^ lteExp p) (y := 1) (by omega) hdvd hgp hd
    simpa [lteVal] using this

theorem pow_lteVal_dvd (p m : ℕ) : p ^ lteVal p m ∣ m ^ lteExp p - 1 := pow_multiplicity_dvd _ _

theorem not_dvd_pow_lteExp_sub_one {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : ¬ p ∣ m) (hm2 : 2 ≤ m)
    (n d : ℕ) (hd0 : 0 < d) (hdn : d < p ^ n) :
    ¬ p ^ (lteVal p m + n) ∣ (m ^ lteExp p) ^ d - 1 := by
  intro h
  have hne : (m ^ lteExp p) ^ d - 1 ≠ 0 := by
    have := Nat.le_self_pow (by omega : d ≠ 0) (m ^ lteExp p)
    have := two_le_pow_lteExp hp.out hm2 (p := p); omega
  rw [multiplicity_dvd_iff_le hne, lte_lteExp hm hm2 (by omega)] at h
  have : p ^ n ∣ d := (multiplicity_dvd_iff_le (by omega)).2 (by omega)
  exact absurd (Nat.le_of_dvd hd0 this) (by omega)

theorem dvd_pow_lteExp_pow_sub_one {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : ¬ p ∣ m) (hm2 : 2 ≤ m)
    (n : ℕ) : p ^ (lteVal p m + n) ∣ (m ^ lteExp p) ^ (p ^ n) - 1 := by
  have hne : (m ^ lteExp p) ^ (p ^ n) - 1 ≠ 0 := by
    have := Nat.le_self_pow (pow_ne_zero n hp.out.ne_zero) (m ^ lteExp p)
    have := two_le_pow_lteExp hp.out hm2 (p := p); omega
  rw [multiplicity_dvd_iff_le hne, lte_lteExp hm hm2 (pow_ne_zero n hp.out.ne_zero),
    Nat.multiplicity_prime_pow]

/-! ### Orbit sums of `Ψ` -/

/-- One `g`-orbit: `∑_{s<S} Ψ_K(pʳ c gˢ) ≤ (S + pⁿ) 2^{-(K-t-1)/2}` with `g = m^{2(p−1)}`. -/
theorem sum_rieszPsi_g_le (p k q : ℕ) [hp : Fact p.Prime] (hqk : q = p ^ k) (hq : 2 ≤ q) {m : ℕ}
    (hm : ¬ p ∣ m) (hm2 : 2 ≤ m) (c : ℕ) (hc : ¬ p ∣ c) (r : ℕ) (hr : r < k) (K : ℕ)
    (hK : lteVal p m + 1 ≤ K) (S : ℕ) :
    ∑ s ∈ Finset.range S, rieszPsi q K ((p ^ r * c * (m ^ lteExp p) ^ s : ℕ) : ℝ) ≤
      (S + q ^ K) * Real.sqrt 2⁻¹ ^ (K - lteVal p m - 1) := by
  set t := lteVal p m
  set g := m ^ lteExp p
  set n := k * K - t - r
  have hk1 : 1 ≤ k := by omega
  have hkK : k * (t + 1) ≤ k * K := Nat.mul_le_mul_left k hK
  have hn : r + t + n = k * K := by
    have : k * (t + 1) = k * t + k := by ring
    have : t ≤ k * t := Nat.le_mul_of_pos_left t (by omega)
    omega
  have hQ : p ^ r * p ^ (t + n) = q ^ K := by rw [← pow_add, hqk, ← pow_mul]; congr 1; omega
  have hg2 : 2 ≤ g := two_le_pow_lteExp hp.out hm2
  set F : ℕ → ℝ := fun w ↦ rieszPsi q K ((p ^ r * w : ℕ) : ℝ)
  have hF : ∀ w z, F (w + p ^ (t + n) * z) = F w := by
    intro w z
    simp only [F]
    rw [show ((p ^ r * (w + p ^ (t + n) * z) : ℕ) : ℝ) =
      ((p ^ r * w : ℕ) : ℝ) + (q : ℝ) ^ K * ((z : ℤ) : ℝ) by
        have hQr : (p : ℝ) ^ r * (p : ℝ) ^ (t + n) = (q : ℝ) ^ K := by exact_mod_cast hQ
        push_cast; rw [← hQr]; ring]
    exact rieszPsi_add q K (by omega) _ _
  have hF0 : ∀ w, 0 ≤ F w := fun w ↦ rieszPsi_nonneg _ _ _
  have hper : ∀ s, F (c * g ^ (s + p ^ n)) = F (c * g ^ s) := by
    intro s
    obtain ⟨w, hw⟩ := dvd_pow_lteExp_pow_sub_one hm hm2 n
    have h1 : 1 ≤ g ^ p ^ n := Nat.one_le_pow _ _ (by omega)
    rw [pow_add, show g ^ p ^ n = p ^ (t + n) * w + 1 by
        rw [← hw]; exact (Nat.sub_add_cancel h1).symm,
      show c * (g ^ s * (p ^ (t + n) * w + 1)) = c * g ^ s + p ^ (t + n) * (c * g ^ s * w) by
        ring, hF]
  have hperiod : ∑ s ∈ Finset.range (p ^ n), F (c * g ^ s) ≤
      p ^ n * Real.sqrt 2⁻¹ ^ (K - t - 1) := by
    rw [orbit_sum_eq p g t n c (by omega) (fun h ↦ hm (hp.out.dvd_of_dvd_pow h))
      (pow_lteVal_dvd p m) (not_dvd_pow_lteExp_sub_one hm hm2 n) hc F hF]
    have := sum_rieszPsi_class_le p k q hqk hq (r + t) (k * (t + 1) - (r + t)) (t + 1)
      (by have : r + t ≤ k * (t + 1) := by nlinarith
          omega) ((p ^ r * (c % p ^ t) : ℕ) : ℝ) (K - t - 1)
    have hpn : p ^ (k * (t + 1) - (r + t)) * q ^ (K - t - 1) = p ^ n := by
      rw [hqk, ← pow_mul, ← pow_add]; congr 1
      have : k * (K - t - 1) = k * K - k * (t + 1) := by
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_add, mul_one, Nat.sub_sub]
      have : r + t ≤ k * (t + 1) := by nlinarith
      omega
    have hpn' : (p : ℝ) ^ (k * (t + 1) - (r + t)) * (q : ℝ) ^ (K - t - 1) = (p : ℝ) ^ n := by
      exact_mod_cast hpn
    rw [hpn, show t + 1 + (K - t - 1) = K by omega, hpn'] at this
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) this
    simp only [F]; congr 1; push_cast; ring
  have := sum_periodic_le (fun s ↦ F (c * g ^ s)) (fun s ↦ hF0 _) (p ^ n)
    (by have := hp.out.pos; positivity) hper (Real.sqrt 2⁻¹ ^ (K - t - 1))
    (by exact_mod_cast hperiod) S
  refine le_of_eq_of_le (Finset.sum_congr rfl fun s _ ↦ ?_) (this.trans ?_)
  · simp only [F]; congr 2; ring
  · gcongr
    have : p ^ n ≤ q ^ K := by
      rw [← hQ]; exact (Nat.le_mul_of_pos_left _ (by have := hp.out.pos; positivity)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.out.pos (by omega)))
    exact_mod_cast this

/-- The full orbit: `∑_{l<N} Ψ_K(pʳ c mˡ) ≤ (N + E (1 + q^K)) 2^{-(K-t-1)/2}`, `E = 2(p − 1)`. -/
theorem sum_rieszPsi_orbit_le (p k q : ℕ) [hp : Fact p.Prime] (hqk : q = p ^ k) (hq : 2 ≤ q) {m : ℕ}
    (hm : ¬ p ∣ m) (hm2 : 2 ≤ m) (c : ℕ) (hc : ¬ p ∣ c) (r : ℕ) (hr : r < k) (K : ℕ)
    (hK : lteVal p m + 1 ≤ K) (N : ℕ) :
    ∑ l ∈ Finset.range N, rieszPsi q K ((p ^ r * c * m ^ l : ℕ) : ℝ) ≤
      (N + lteExp p * (1 + q ^ K)) * Real.sqrt 2⁻¹ ^ (K - lteVal p m - 1) := by
  set E := lteExp p
  have hE : 1 ≤ E := by simp only [E, lteExp]; have := hp.out.two_le; omega
  set S := N / E + 1
  have hNS : N ≤ E * S := by
    have := Nat.lt_div_mul_add (a := N) (b := E) (by omega)
    simp only [S]; nlinarith [Nat.div_add_mod N E, Nat.mod_lt N (show E > 0 by omega)]
  calc ∑ l ∈ Finset.range N, rieszPsi q K ((p ^ r * c * m ^ l : ℕ) : ℝ)
      ≤ ∑ l ∈ Finset.range (E * S), rieszPsi q K ((p ^ r * c * m ^ l : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNS)
          (fun _ _ _ ↦ rieszPsi_nonneg _ _ _)
    _ = ∑ e ∈ Finset.range E, ∑ s ∈ Finset.range S,
          rieszPsi q K ((p ^ r * (c * m ^ e) * (m ^ E) ^ s : ℕ) : ℝ) := by
        rw [sum_range_mul_eq, Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
        congr 1; push_cast; ring
    _ ≤ ∑ e ∈ Finset.range E, ((S : ℝ) + q ^ K) * Real.sqrt 2⁻¹ ^ (K - lteVal p m - 1) := by
        refine Finset.sum_le_sum fun e _ ↦ sum_rieszPsi_g_le p k q hqk hq hm hm2 _ ?_ r hr K hK S
        intro h
        rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
        · exact hc h
        · exact hm (hp.out.dvd_of_dvd_pow h)
    _ = E * ((N / E : ℕ) + 1 + (q : ℝ) ^ K) * Real.sqrt 2⁻¹ ^ (K - lteVal p m - 1) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, S, Nat.cast_add, Nat.cast_one]
        ring
    _ ≤ _ := by
        gcongr
        have : E * (N / E) ≤ N := Nat.mul_div_le N E
        have : (E : ℝ) * ((N / E : ℕ) : ℝ) ≤ N := by exact_mod_cast this
        linarith

/-! ### The second moment -/

/-- The second moment of a Weyl sum, expanded into Fourier coefficients. -/
theorem secondMoment_expand (G : (ℕ → Bool) → ℝ) (hG : Measurable G) (b : ℕ) (h : ℤ) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂coinMeasure‖ := by
  have hint : ∀ ξ : ℝ, Integrable (fun ω ↦ ee (ξ * G ω)) coinMeasure := fun ξ ↦
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun ω ↦ (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k ↦ h * (b : ℝ) ^ k * G ω)]
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coinMeasure : ℝ) :
      ℂ) = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂coinMeasure := by
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

/-- **Second moment bound** for `b = pᵃ m`, `p ∤ m`, `m ≥ 2`. -/
theorem secondMoment_le (p k q : ℕ) [hp : Fact p.Prime] (hqk : q = p ^ k) (hq : 2 ≤ q)
    {b a m : ℕ} (hbam : b = p ^ a * m) (hm : ¬ p ∣ m) (hm2 : 2 ≤ m) (h : ℤ) (hh : h ≠ 0)
    (K : ℕ) (hK : lteVal p m + 1 ≤ K) (N : ℕ) :
    ∫ ω, ‖∑ n ∈ Finset.range N, ee (h * (b : ℝ) ^ n * coinPoint q ω)‖ ^ 2 ∂coinMeasure ≤
      N + 2 * N * (k * ((N + lteExp p * (1 + q ^ K)) * Real.sqrt 2⁻¹ ^ (K - lteVal p m - 1))) := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hqk] at hq
    · exact hk
  have hb2 : 2 ≤ b := by
    rw [hbam]; exact le_trans hm2 (Nat.le_mul_of_pos_left m (pow_pos hp.out.pos a))
  obtain ⟨e, h', hh', hhe⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hh) p hp.out.ne_one
  have hvw : ∀ d : ℕ, ∃ v w : ℕ, 1 ≤ d → ¬ p ∣ w ∧ b ^ d - 1 = p ^ v * w := by
    intro d
    by_cases hd : 1 ≤ d
    · have : b ^ d - 1 ≠ 0 := by
        have := Nat.le_self_pow (by omega : d ≠ 0) b; omega
      obtain ⟨v, w, hw, hvw⟩ := Nat.exists_eq_pow_mul_and_not_dvd this p hp.out.ne_one
      exact ⟨v, w, fun _ ↦ ⟨hw, hvw⟩⟩
    · exact ⟨0, 0, fun h ↦ absurd h hd⟩
  choose v w hw using hvw
  set B := (N + lteExp p * (1 + (q : ℝ) ^ K)) * Real.sqrt 2⁻¹ ^ (K - lteVal p m - 1)
  set G : ℕ → ℕ → ℝ := fun d l ↦
    ∑ r ∈ Finset.range k, rieszPsi q K ((p ^ r * (h' * w d) * m ^ l : ℕ) : ℝ)
  have hfreq : ∀ l d, 1 ≤ d → |(h : ℝ) * ((b : ℝ) ^ (l + d) - (b : ℝ) ^ l)| =
      (q : ℝ) ^ ((e + a * l + v d) / k) *
        ((p ^ ((e + a * l + v d) % k) * (h' * w d) * m ^ l : ℕ) : ℝ) := by
    intro l d hd
    obtain ⟨-, hbd⟩ := hw d hd
    have hbd1 : 1 ≤ b ^ d := Nat.one_le_pow _ _ (by omega)
    have hbdR : (b : ℝ) ^ d - 1 = (p : ℝ) ^ v d * w d := by
      have : ((b ^ d - 1 : ℕ) : ℝ) = ((p ^ v d * w d : ℕ) : ℝ) := by rw [hbd]
      push_cast [Nat.cast_sub hbd1] at this; exact this
    have habs : |(h : ℝ)| = (p : ℝ) ^ e * h' := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, hhe]; push_cast; ring
    have hV : (q : ℝ) ^ ((e + a * l + v d) / k) * (p : ℝ) ^ ((e + a * l + v d) % k) =
        (p : ℝ) ^ (e + a * l + v d) := by
      rw [hqk]; push_cast; rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hbl : (b : ℝ) ^ l = (p : ℝ) ^ (a * l) * (m : ℝ) ^ l := by
      rw [hbam]; push_cast; rw [mul_pow, pow_mul]
    rw [abs_mul, habs, show (b : ℝ) ^ (l + d) - (b : ℝ) ^ l = (b : ℝ) ^ l * ((b : ℝ) ^ d - 1) by
      ring, abs_of_nonneg (mul_nonneg (by positivity) (by rw [hbdR]; positivity)), hbdR, hbl]
    push_cast
    calc (p : ℝ) ^ e * h' * ((p : ℝ) ^ (a * l) * (m : ℝ) ^ l * ((p : ℝ) ^ v d * w d))
        = (p : ℝ) ^ (e + a * l + v d) * (h' * w d * (m : ℝ) ^ l) := by
          rw [pow_add, pow_add]; ring
      _ = _ := by rw [← hV]; ring
  have hΦ : ∀ l d, 1 ≤ d → ∀ ξ : ℝ, |ξ| = |(h : ℝ) * ((b : ℝ) ^ (l + d) - (b : ℝ) ^ l)| →
      ‖∫ ω, ee (ξ * coinPoint q ω) ∂coinMeasure‖ ≤ G d l := by
    intro l d hd ξ hξ
    refine (charFun_le_rieszPsi q hq ξ _ K _ (hξ.trans (hfreq l d hd))).trans ?_
    exact Finset.single_le_sum (f := fun r ↦ rieszPsi q K ((p ^ r * (h' * w d) * m ^ l : ℕ) : ℝ))
      (fun r _ ↦ rieszPsi_nonneg _ _ _) (Finset.mem_range.2 (Nat.mod_lt _ hk))
  have hpair := pair_sum_le
    (fun n m' ↦ ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m')) * coinPoint q ω) ∂coinMeasure‖) G
    (fun d l ↦ Finset.sum_nonneg fun _ _ ↦ rieszPsi_nonneg _ _ _)
    (fun n ↦ by simpa using charFun_le q hq 0 0)
    (fun n m' hmn ↦ hΦ m' (n - m') (by omega) _ (by rw [show m' + (n - m') = n by omega]))
    (fun n m' hmn ↦ hΦ n (m' - n) (by omega) _ (by
      rw [show n + (m' - n) = m' by omega, ← abs_neg]; congr 1; ring)) N
  have hd : ∀ d ∈ Finset.Ico 1 N, ∑ l ∈ Finset.range N, G d l ≤ k * B := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    obtain ⟨hwd, -⟩ := hw d hd.1
    have hc : ¬ p ∣ h' * w d := fun hc ↦
      ((Nat.Prime.dvd_mul hp.out).1 hc).elim hh' hwd
    simp only [G]
    rw [Finset.sum_comm]
    calc _ ≤ ∑ r ∈ Finset.range k, B := Finset.sum_le_sum fun r hr ↦
          sum_rieszPsi_orbit_le p k q hqk hq hm hm2 _ hc r (Finset.mem_range.1 hr) K hK N
      _ = _ := by simp
  have hB : 0 ≤ B := by positivity
  have hsum : ∑ d ∈ Finset.Ico 1 N, ∑ l ∈ Finset.range N, G d l ≤ N * (k * B) := by
    refine (Finset.sum_le_sum hd).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    gcongr
  refine (secondMoment_expand (coinPoint q) (measurable_coinPoint q) b h N).trans (hpair.trans ?_)
  linarith

/-! ### Almost sure normality in base `b` -/

theorem sqrt_inv_two_pow_le (q M : ℕ) (hq : 0 < q) :
    Real.sqrt 2⁻¹ ^ (M / q) ≤ (Real.sqrt 2⁻¹)⁻¹ *
      Real.exp (-(-Real.log (Real.sqrt 2⁻¹) / q) * M) := by
  set ρ := Real.sqrt 2⁻¹
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 (by norm_num)
  have hρ1 : ρ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set L := Real.log ρ
  have hL : L < 0 := Real.log_neg hρ0 hρ1
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hρ0,
    show ρ⁻¹ = Real.exp (-L) by rw [Real.exp_neg, Real.exp_log hρ0], ← Real.exp_add,
    Real.exp_le_exp]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hM : (M : ℝ) / q ≤ ((M / q : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hq']
    have : M < q * (M / q + 1) := by
      have := Nat.lt_div_mul_add (a := M) hq; nlinarith
    have : (M : ℝ) < q * ((M / q : ℕ) + 1) := by exact_mod_cast this
    linarith
  have := mul_le_mul_of_nonpos_left hM hL.le
  have e : -(-L / q) * M = L * (M / q) := by field_simp
  rw [e]; nlinarith

/-- `X` is almost surely normal in every base `b` that is not a power of `p`. -/
theorem ae_isNormal (p k q : ℕ) [hp : Fact p.Prime] (hqk : q = p ^ k) (hq : 2 ≤ q) {b : ℕ}
    (hb : 2 ≤ b) (hpow : ∀ i, b ≠ p ^ i) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (coinPoint q ω) := by
  obtain ⟨a, m, hm, hbam⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : b ≠ 0) p hp.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hbam; omega
  have hm1 : m ≠ 1 := by rintro rfl; exact hpow a (by simpa using hbam)
  have hm2 : 2 ≤ m := by omega
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hqk] at hq
    · exact hk
  set t := lteVal p m
  set E := lteExp p
  set ρ := Real.sqrt 2⁻¹
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 (by norm_num)
  have hρ1 : ρ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set c := -Real.log ρ / q
  have hc : 0 < c := div_pos (neg_pos.2 (Real.log_neg hρ0 hρ1)) (by positivity)
  refine ae_isNormal_of_secondMoment coinMeasure hb (coinPoint q) (measurable_coinPoint q) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  set C : ℝ := 1 + 2 * k * (1 + 2 * E * (q : ℝ) ^ (t + 1)) * ρ⁻¹
  have hC : 0 < C := by positivity
  refine (summable_sched_bound C c hC hc).of_nonneg_of_le
    (fun j ↦ div_nonneg (integral_nonneg fun ω ↦ by positivity) (by positivity)) (fun j ↦ ?_)
  set N := sched j
  have hN1 : 1 ≤ N := one_le_sched j
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [div_le_iff₀ (by positivity)]
  set M := Nat.log 3 N / 2
  obtain ⟨K, hKdef⟩ : ∃ K, K = t + 1 + M / q := ⟨_, rfl⟩
  have hmom := secondMoment_le p k q hqk hq hbam hm hm2 h hh K
    (by rw [hKdef]; exact Nat.le_add_right _ _) N
  rw [show K - t - 1 = M / q by rw [hKdef, Nat.add_assoc, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left]] at hmom
  -- `q ^ K ≤ q ^ (t + 1) * N`
  have hqM : q ^ (M / q) ≤ N := by
    calc q ^ (M / q) ≤ (3 ^ q) ^ (M / q) :=
          Nat.pow_le_pow_left (Nat.lt_pow_self (by norm_num)).le _
      _ = 3 ^ (q * (M / q)) := by rw [pow_mul]
      _ ≤ 3 ^ M := Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le M q)
      _ ≤ 3 ^ Nat.log 3 N := Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
      _ ≤ N := Nat.pow_log_le_self 3 (by omega)
  have hqK : (q : ℝ) ^ K ≤ (q : ℝ) ^ (t + 1) * N := by
    rw [hKdef, pow_add]
    gcongr; exact_mod_cast hqM
  have hρM := sqrt_inv_two_pow_le q M (by omega)
  have hFM : Real.exp (-c * M) ≤ Real.exp (-c * freeCount isFree M) := by
    have : (freeCount isFree M : ℝ) ≤ M := by
      exact_mod_cast NormalNumbers.CantorLiouvilleAll.Cassels.freeCount_le_self isFree M
    exact Real.exp_le_exp.2 (by nlinarith)
  have hNR := NormalNumbers.CantorLiouvilleAll.Cassels.le_rpow_neg_half hN1
  set Ex := Real.exp (-c * freeCount isFree M)
  set R := (N : ℝ) ^ (-(1 / 2 : ℝ))
  have hEx : 0 ≤ Ex := (Real.exp_pos _).le
  have hR : 0 ≤ R := by positivity
  have hP : ρ ^ (M / q) ≤ ρ⁻¹ * Ex := hρM.trans (by gcongr)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (t + 1) := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ q))
  have hinner : (N : ℝ) + E * (1 + (q : ℝ) ^ K) ≤ (1 + 2 * E * (q : ℝ) ^ (t + 1)) * N := by
    have hE0 : (0 : ℝ) ≤ E := by positivity
    have : (1 : ℝ) ≤ (q : ℝ) ^ (t + 1) * N := by nlinarith
    nlinarith
  have hρP : 0 ≤ ρ ^ (M / q) := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  calc _ ≤ _ := hmom
    _ ≤ N + 2 * N * (k * (((1 + 2 * E * (q : ℝ) ^ (t + 1)) * N) * (ρ⁻¹ * Ex))) := by
        gcongr
    _ ≤ (N : ℝ) ^ 2 * R + 2 * k * (1 + 2 * E * (q : ℝ) ^ (t + 1)) * ρ⁻¹ * ((N : ℝ) ^ 2 * Ex) := by
        nlinarith
    _ ≤ C * (Ex + R) * (N : ℝ) ^ 2 := by
        have h1 : (0 : ℝ) ≤ 2 * k * (1 + 2 * E * (q : ℝ) ^ (t + 1)) * ρ⁻¹ := by positivity
        have h2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
        simp only [C]; nlinarith [mul_nonneg h1 (mul_nonneg h2 hR), mul_nonneg h2 hEx]

/-- **Schmidt's theorem for a prime-power base.** If `b ≥ 2` is not a power of the prime `p`,
some real number is normal in base `b` and in no base `pʲ`, `j ≥ 1`. -/
theorem exists_isNormalIn_forall_not_isNormalIn_pow {p : ℕ} (hp : p.Prime) {b : ℕ} (hb : 2 ≤ b)
    (hpow : ∀ i, b ≠ p ^ i) :
    ∃ x : ℝ, IsNormalIn b x ∧ ∀ j, 1 ≤ j → ¬ IsNormalIn (p ^ j) x := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
  obtain ⟨ω, hω⟩ := (ae_isNormal p 2 (p ^ 2) rfl (by omega) hb hpow).exists
  refine ⟨coinPoint (p ^ 2) ω, (isNormalIn_iff_isNormal b _).2 hω, fun j hj hn ↦ ?_⟩
  have hpj : 2 ≤ p ^ j := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [isNormalIn_iff_of_pow_eq_pow (c := p ^ 2) hpj (by omega) (m := 2) (n := j) (by norm_num)
    (by omega) (by ring)] at hn
  exact not_isNormalIn_coinPoint (p ^ 2) (by omega) ω hn

end Real.SchmidtPrimePower
