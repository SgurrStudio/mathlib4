/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.SchmidtPrimePower

/-!
# Schmidt's theorem for arbitrary bases

Let `b, c ≥ 2` be multiplicatively independent (`bᵐ ≠ cⁿ` for all `m, n ≥ 1`). We show that some
real number is normal in base `b` but in no base `cʲ`, `j ≥ 1` (Schmidt 1960).

## Proof

Let `q = c²` and `X = ∑ᵢ εᵢ q⁻ⁱ⁻¹` for independent fair coins `εᵢ`, as in
`Real.SchmidtPrimePower`: `X` is never normal in base `q`, and we show it is almost surely normal
in base `b` by the Davenport–Erdős–LeVeque criterion.

Choose a prime `p ∣ q` minimising `v_p(b) / v_p(q)` and put `s = v_p(q)`, `r = v_p(b)`, so that
`bˢ = qʳ B` with `p ∤ B ≥ 2` (`exists_reduction`). Write `q = p^γ q'` with `p ∤ q'`. Writing
`l = s m + ε`, the frequency of the pair `(l + d, l)` is `q^{rm} · pᵉ Y Bᵐ` with `p ∤ Y`, and its
Fourier coefficient is at most `Ψ_K(pᵉ Y Bᵐ)`.

* By the Chinese remainder theorem, `1/q^{i+1}` splits into a `p`-part with a unit numerator and a
  `q'`-part (`exists_rieszPsi_le_rieszPhi`). Once `m ≥ K q'`, the `q'`-part is periodic in `m`
  with period `φ(q'ᴷ)` (`dvd_pow_mul_pow_totient_sub_one`), so on each residue class it is a
  fixed phase.
* Along the class, `Bᵐ` runs through a residue class modulo `pᵗ` with `t` bounded independently of
  `K` (lifting the exponent, `lteVal_pow_totient`), and averaging the `p`-part over such a class
  gains a factor `1/√2` for each further digit (`sum_rieszPhi_class_le`).
* The pairs where `v_p(bᵈ − 1)` is large are few (`card_bad_le`).

Together these give the second moment bound `secondMoment_le` and `ae_isNormal`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Real.SchmidtGeneral

open NormalNumbers NormalNumbers.CantorLiouville NormalNumbers.CantorLiouvilleAll
  NormalNumbers.DecayAeNormal NormalNumbers.ExplicitSquare NormalNumbers.CantorSelfSimilar
  Real.SchmidtPrimePower

/-! ### Cosine sums with a unit multiplier -/

theorem sum_cos_mul_eq_zero (q : ℕ) (hq : 1 ≤ q) (a : ℤ) (ha : ¬ (q : ℤ) ∣ a) (α : ℝ) :
    ∑ r ∈ Finset.range q, Real.cos (α + 2 * Real.pi * a * r / q) = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set w := Complex.exp (2 * Real.pi * Complex.I * a / q)
  have hwq : w ^ q = 1 := by
    rw [← Complex.exp_natCast_mul, show (q : ℂ) * (2 * Real.pi * Complex.I * a / q) =
      (a : ℂ) * (2 * Real.pi * Complex.I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I a
  have hw1 : w ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    apply ha
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp at hn
    exact ⟨n, by exact_mod_cast hn⟩
  have hg : ∑ r ∈ Finset.range q, w ^ r = 0 := by
    rw [geom_sum_eq hw1, hwq, sub_self, zero_div]
  have : ∑ r ∈ Finset.range q, Complex.exp (α * Complex.I) * w ^ r = 0 := by
    rw [← Finset.mul_sum, hg, mul_zero]
  have h2 := congrArg Complex.re this
  rw [Complex.re_sum, Complex.zero_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Complex.exp_natCast_mul, ← Complex.exp_add,
    show (α : ℂ) * Complex.I + (r : ℂ) * (2 * Real.pi * Complex.I * a / q) =
      ((α + 2 * Real.pi * a * r / q : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- `∑_{r<q} |cos(θ + πar/q)| ≤ q/√2` when `q ∤ a`. -/
theorem sum_abs_cos_mul_le (q : ℕ) (hq : 1 ≤ q) (a : ℤ) (ha : ¬ (q : ℤ) ∣ a) (θ : ℝ) :
    ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * a * r / q)| ≤ q * Real.sqrt 2⁻¹ := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range q)
    (f := fun r : ℕ ↦ |Real.cos (θ + Real.pi * a * r / q)|)
  have hsq : ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * a * r / q)| ^ 2 = q / 2 := by
    have : ∀ r : ℕ, |Real.cos (θ + Real.pi * a * r / q)| ^ 2 =
        1 / 2 + Real.cos (2 * θ + 2 * Real.pi * a * r / q) / 2 := by
      intro r
      rw [sq_abs, Real.cos_sq]; congr 2; ring_nf
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_div (Finset.range q)
      (fun x : ℕ ↦ Real.cos (2 * θ + 2 * Real.pi * a * x / q)), sum_cos_mul_eq_zero q hq a ha]
    simp; ring
  rw [hsq, Finset.card_range] at hcs
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2⁻¹)
  have hs0 := Real.sqrt_nonneg (2⁻¹ : ℝ)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have h0 : 0 ≤ ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * a * r / q)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  set S := ∑ r ∈ Finset.range q, |Real.cos (θ + Real.pi * a * r / q)|
  nlinarith [mul_nonneg hq0 hs0]

/-! ### Riesz products with unit multipliers and phases -/

/-- `Φ_K(z) = ∏_{i<K} |cos(π(aᵢ z / p^{γ(i+1)+δ} + βᵢ))|`. -/
noncomputable def rieszPhi (p γ δ : ℕ) (a : ℕ → ℤ) (β : ℕ → ℝ) (K : ℕ) (z : ℝ) : ℝ :=
  ∏ i ∈ Finset.range K, |Real.cos (Real.pi * (a i * z / (p : ℝ) ^ (γ * (i + 1) + δ) + β i))|

theorem rieszPhi_nonneg (p γ δ : ℕ) (a : ℕ → ℤ) (β : ℕ → ℝ) (K : ℕ) (z : ℝ) :
    0 ≤ rieszPhi p γ δ a β K z :=
  Finset.prod_nonneg fun _ _ ↦ abs_nonneg _

theorem rieszPhi_le_one (p γ δ : ℕ) (a : ℕ → ℤ) (β : ℕ → ℝ) (K : ℕ) (z : ℝ) :
    rieszPhi p γ δ a β K z ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun _ _ ↦ Real.abs_cos_le_one _

theorem rieszPhi_add (p γ δ : ℕ) (hp : 1 ≤ p) (a : ℕ → ℤ) (β : ℕ → ℝ) (K : ℕ) (z : ℝ) (w : ℤ) :
    rieszPhi p γ δ a β K (z + (p : ℝ) ^ (γ * K + δ) * w) = rieszPhi p γ δ a β K z := by
  unfold rieszPhi
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  simp only [Finset.mem_range] at hi
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hK : (p : ℝ) ^ (γ * K + δ) =
      (p : ℝ) ^ (γ * (i + 1) + δ) * (p : ℝ) ^ (γ * (K - (i + 1))) := by
    rw [← pow_add]; congr 1
    have : γ * (i + 1) ≤ γ * K := Nat.mul_le_mul_left γ hi
    rw [Nat.mul_sub]; omega
  have : Real.pi * (a i * (z + (p : ℝ) ^ (γ * K + δ) * w) / (p : ℝ) ^ (γ * (i + 1) + δ) + β i) =
      Real.pi * (a i * z / (p : ℝ) ^ (γ * (i + 1) + δ) + β i) +
        ((a i * w * p ^ (γ * (K - (i + 1))) : ℤ) : ℝ) * Real.pi := by
    rw [hK]; push_cast; field_simp; ring
  rw [this, abs_cos_add_int_mul_pi]

theorem rieszPhi_succ (p γ δ : ℕ) (a : ℕ → ℤ) (β : ℕ → ℝ) (K : ℕ) (z : ℝ) :
    rieszPhi p γ δ a β (K + 1) z = rieszPhi p γ δ a β K z *
      |Real.cos (Real.pi * (a K * z / (p : ℝ) ^ (γ * (K + 1) + δ) + β K))| :=
  Finset.prod_range_succ _ _

/-- **Averaging `Φ` over a residue class.** If `τ + n₀ = γ K₀ + δ`, the average of `Φ_{K₀+I}`
over one period of the class `c₀ + pᵗ ℤ` is at most `2^{-I/2}`. -/
theorem sum_rieszPhi_class_le (p γ δ : ℕ) (hp : 2 ≤ p) (hγ : 1 ≤ γ) (a : ℕ → ℤ)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (β : ℕ → ℝ) (τ n₀ K₀ : ℕ) (hK : τ + n₀ = γ * K₀ + δ)
    (c₀ : ℝ) (I : ℕ) :
    ∑ j ∈ Finset.range (p ^ n₀ * (p ^ γ) ^ I), rieszPhi p γ δ a β (K₀ + I) (c₀ + p ^ τ * j) ≤
      p ^ n₀ * (p ^ γ) ^ I * Real.sqrt 2⁻¹ ^ I := by
  set q := p ^ γ with hq
  have hq2 : 2 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  induction I with
  | zero =>
    simp only [pow_zero, mul_one, add_zero]
    refine (Finset.sum_le_sum fun j _ ↦ rieszPhi_le_one _ _ _ _ _ _ _).trans ?_
    simp
  | succ I ih =>
    set L := p ^ n₀ * q ^ I
    have hL : (p : ℝ) ^ τ * L = (p : ℝ) ^ (γ * (K₀ + I) + δ) := by
      simp only [L, hq]; push_cast
      rw [← mul_assoc, ← pow_add, ← pow_mul, ← pow_add]; congr 1; rw [Nat.mul_add]; omega
    rw [show p ^ n₀ * q ^ (I + 1) = L * q by simp only [L]; ring, sum_range_mul_eq,
      Finset.sum_comm]
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hterm : ∀ u t : ℕ, rieszPhi p γ δ a β (K₀ + (I + 1)) (c₀ + p ^ τ * ((L * t + u : ℕ) : ℝ)) =
        rieszPhi p γ δ a β (K₀ + I) (c₀ + p ^ τ * u) *
          |Real.cos (Real.pi * (a (K₀ + I) * (c₀ + p ^ τ * u) /
            (p : ℝ) ^ (γ * (K₀ + I + 1) + δ) + β (K₀ + I)) + Real.pi * a (K₀ + I) * t / q)| := by
      intro u t
      have e : c₀ + (p : ℝ) ^ τ * ((L * t + u : ℕ) : ℝ) =
          (c₀ + p ^ τ * u) + (p : ℝ) ^ (γ * (K₀ + I) + δ) * ((t : ℤ) : ℝ) := by
        push_cast; rw [← hL]; ring
      rw [← add_assoc, rieszPhi_succ, e, rieszPhi_add p γ δ (by omega)]
      simp only [Int.cast_natCast]
      congr 2
      have hpow : (p : ℝ) ^ (γ * (K₀ + I + 1) + δ) = (p : ℝ) ^ (γ * (K₀ + I) + δ) * q := by
        rw [hq]; push_cast; rw [← pow_add]; congr 1; ring
      rw [hpow]; field_simp; ring_nf
    simp_rw [hterm, ← Finset.mul_sum]
    have haq : ∀ i, ¬ ((q : ℕ) : ℤ) ∣ a i := fun i h ↦
      ha i ((Int.natCast_dvd_natCast.2 (dvd_pow_self p (by omega))).trans h)
    calc _ ≤ ∑ u ∈ Finset.range L, rieszPhi p γ δ a β (K₀ + I) (c₀ + p ^ τ * u) *
            (q * Real.sqrt 2⁻¹) :=
          Finset.sum_le_sum fun u _ ↦ mul_le_mul_of_nonneg_left
            (sum_abs_cos_mul_le q (by omega) _ (haq _) _) (rieszPhi_nonneg _ _ _ _ _ _ _)
      _ = (∑ u ∈ Finset.range L, rieszPhi p γ δ a β (K₀ + I) (c₀ + p ^ τ * u)) *
            (q * Real.sqrt 2⁻¹) := (Finset.sum_mul _ _ _).symm
      _ ≤ (L * Real.sqrt 2⁻¹ ^ I) * (q * Real.sqrt 2⁻¹) := by
          gcongr; exact_mod_cast ih
      _ = _ := by simp only [L, hq]; push_cast; ring

/-! ### Arithmetic reduction -/

/-- **Reduction to a base prime to one prime of `c`.** If `b, c ≥ 2` are multiplicatively
independent, there are `s ≥ 1`, `r` and a prime `p ∣ c` with `cʳ ∣ bˢ` and `p ∤ bˢ / cʳ ≥ 2`.
Take `p` minimising `v_p(b) / v_p(c)`, `s = v_p(c)` and `r = v_p(b)`. -/
theorem exists_reduction {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → b ^ m ≠ c ^ n) :
    ∃ p r s : ℕ, p.Prime ∧ p ∣ c ∧ 1 ≤ s ∧ c ^ r ∣ b ^ s ∧ ¬ p ∣ b ^ s / c ^ r ∧
      2 ≤ b ^ s / c ^ r := by
  have hne : c.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image c.primeFactors
    (fun q ↦ (b.factorization q : ℚ) / c.factorization q) hne
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpc : p ∣ c := Nat.dvd_of_mem_primeFactors hp
  set s := c.factorization p
  set r := b.factorization p
  have hs : 1 ≤ s := (hpp.factorization_pos_of_dvd (by omega) hpc)
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hdvd : c ^ r ∣ b ^ s := by
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hc0) (pow_ne_zero _ hb0)]
    intro q
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hq : q ∈ c.primeFactors
    · have h := hmin q hq
      have hq0 : (0 : ℚ) < c.factorization q := by
        have := (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd hc0
          (Nat.dvd_of_mem_primeFactors hq)
        exact_mod_cast this
      have hs0 : (0 : ℚ) < s := by exact_mod_cast hs
      rw [div_le_div_iff₀ hs0 hq0] at h
      exact_mod_cast (by linarith : (r : ℚ) * c.factorization q ≤ s * b.factorization q)
    · rw [Finsupp.notMem_support_iff.1 hq]; simp
  have hB0 : b ^ s / c ^ r ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (pow_pos (by omega) _) hdvd) (pow_pos (by omega) _)).ne'
  refine ⟨p, r, s, hpp, hpc, hs, hdvd, fun h ↦ ?_, ?_⟩
  · have h1 := (hpp.dvd_iff_one_le_factorization hB0).1 h
    rw [Nat.factorization_div hdvd] at h1
    simp only [Nat.factorization_pow, Finsupp.coe_tsub, Finsupp.coe_smul, nsmul_eq_mul,
      Pi.sub_apply, Pi.mul_apply, Pi.natCast_apply, Nat.cast_id, s, r] at h1
    rw [mul_comm] at h1
    omega
  · by_contra h2
    have h1 : b ^ s / c ^ r = 1 := by have := Nat.pos_of_ne_zero hB0; omega
    have heq : b ^ s = c ^ r := by
      have := Nat.div_mul_cancel hdvd; rw [h1, one_mul] at this; exact this.symm
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rw [hr, pow_zero] at heq
      have := Nat.one_lt_pow (by omega : s ≠ 0) (by omega : 1 < b)
      omega
    · exact hind s r (by omega) hr heq

/-- **Eventual periodicity.** For `m ≥ K c'`, `Bᵐ ≡ B^{m + φ(c'ᴷ)} (mod c'ᴷ)`. -/
theorem dvd_pow_mul_pow_totient_sub_one {B c' K : ℕ} (hB : 1 ≤ B) (hc' : 1 ≤ c') {m : ℕ}
    (hm : K * c' ≤ m) : c' ^ K ∣ B ^ m * (B ^ Nat.totient (c' ^ K) - 1) := by
  rcases eq_or_lt_of_le hB with hB1 | hB2
  · subst hB1; simp
  have hP : 1 ≤ Nat.totient (c' ^ K) := Nat.totient_pos.2 (pow_pos (by omega) _)
  have hX : B ^ Nat.totient (c' ^ K) - 1 ≠ 0 := by
    have := Nat.one_lt_pow (by omega : Nat.totient (c' ^ K) ≠ 0) hB2; omega
  have hBm : B ^ m ≠ 0 := pow_ne_zero _ (by omega)
  rw [← Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ (by omega)) (mul_ne_zero hBm hX)]
  intro q hq
  rw [Nat.factorization_mul hBm hX, Finsupp.add_apply, Nat.factorization_pow,
    Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases hqB : q ∣ B
  · have h1 : 1 ≤ B.factorization q := hq.factorization_pos_of_dvd (by omega) hqB
    have h2 : c'.factorization q ≤ c' := (Nat.factorization_lt q (by omega)).le
    have : K * c'.factorization q ≤ m * B.factorization q :=
      (Nat.mul_le_mul_left K h2).trans (hm.trans (Nat.le_mul_of_pos_right m h1))
    omega
  · obtain ⟨v, hvdef⟩ : ∃ v, v = K * c'.factorization q := ⟨_, rfl⟩
    rw [← hvdef]
    have hv : q ^ v ∣ c' ^ K := by
      have := Nat.ordProj_dvd (c' ^ K) q
      rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, ← hvdef] at this
    have hcop : Nat.Coprime B (q ^ v) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hq).2 hqB).symm
    have h1 : B ^ Nat.totient (q ^ v) ≡ 1 [MOD q ^ v] := Nat.ModEq.pow_totient hcop
    obtain ⟨k, hk⟩ := Nat.totient_dvd_of_dvd hv
    have h2 : B ^ Nat.totient (c' ^ K) ≡ 1 [MOD q ^ v] := by
      have := h1.pow k; rwa [← pow_mul, ← hk, one_pow] at this
    have h3 : q ^ v ∣ B ^ Nat.totient (c' ^ K) - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h2.symm
    have := (hq.pow_dvd_iff_le_factorization hX).1 h3
    omega

theorem totient_pow_eq (c' : ℕ) : ∀ K : ℕ, 1 ≤ K →
    Nat.totient (c' ^ K) = c' ^ (K - 1) * Nat.totient c'
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp
  | K + 2, _ => by
    rw [pow_succ', Nat.totient_mul_of_dvd (dvd_pow_self c' (by omega)),
      totient_pow_eq c' (K + 1) (by omega)]
    simp only [Nat.add_sub_cancel, show K + 2 - 1 = K + 1 by omega]; ring

theorem multiplicity_totient_pow {p c' : ℕ} [hp : Fact p.Prime] (hc' : 1 ≤ c') (hpc : ¬ p ∣ c')
    {K : ℕ} (hK : 1 ≤ K) :
    multiplicity p (Nat.totient (c' ^ K)) = multiplicity p (Nat.totient c') := by
  rw [totient_pow_eq c' K hK, Nat.multiplicity_mul (pow_ne_zero _ (by omega))
    (Nat.totient_pos.2 (by omega)).ne', Nat.multiplicity_pow,
    multiplicity_eq_zero_of_not_dvd hpc, mul_zero, zero_add]

/-! ### Splitting `Ψ` by the Chinese remainder theorem -/

theorem crt_identity {E P Q x y z z₁ w R : ℝ} (hE : E ≠ 0) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hxy : x * Q + y * P = 1) (hz : z = z₁ + Q * R * w) :
    Real.pi * (E * z) / (E * P * Q) = Real.pi * (x * z / P + y * z₁ / Q) + y * w * R * Real.pi := by
  calc Real.pi * (E * z) / (E * P * Q) = Real.pi * z / (P * Q) * (x * Q + y * P) := by
        rw [hxy]; field_simp
    _ = Real.pi * (x * z / P + y * z / Q) := by field_simp
    _ = _ := by rw [hz]; field_simp; ring

/-- **CRT splitting of `Ψ`.** With `q = p^γ q'`, `p ∤ q'` and `e + δ = γ i₁`, the factors
`i ≥ i₁` of `Ψ_{i₁+K'}(pᵉ z)` form a `Φ` whose phases only depend on `z mod q'^{i₁+K'}`. -/
theorem exists_rieszPsi_le_rieszPhi (p γ q' : ℕ) (hp : p.Prime) (hγ : 1 ≤ γ) (hq' : 1 ≤ q')
    (hpq : ¬ p ∣ q') (e δ i₁ K' : ℕ) (he : e + δ = γ * i₁) :
    ∃ a : ℕ → ℤ, (∀ i, ¬ (p : ℤ) ∣ a i) ∧ ∀ z₁ : ℤ, ∃ β : ℕ → ℝ, ∀ z : ℤ,
      (q' : ℤ) ^ (i₁ + K') ∣ z - z₁ →
      rieszPsi (p ^ γ * q') (i₁ + K') ((p : ℝ) ^ e * z) ≤ rieszPhi p γ δ a β K' z := by
  have hcop : ∀ i, ∃ u v : ℤ,
      u * (q' : ℤ) ^ (i₁ + i + 1) + v * (p : ℤ) ^ (γ * (i + 1) + δ) = 1 := fun i ↦
    IsCoprime.pow (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).symm)
  choose x y hxy using hcop
  refine ⟨x, fun i h ↦ ?_, fun z₁ ↦ ?_⟩
  · have hA : 1 ≤ γ * (i + 1) + δ := by nlinarith
    have h1 : (p : ℤ) ∣ y i * (p : ℤ) ^ (γ * (i + 1) + δ) :=
      Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    have h2 : (p : ℤ) ∣ 1 := by rw [← hxy i]; exact dvd_add (h.mul_right _) h1
    have : p ∣ 1 := by exact_mod_cast h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  refine ⟨fun i ↦ y i * z₁ / (q' : ℝ) ^ (i₁ + i + 1), fun z hz ↦ ?_⟩
  obtain ⟨w, hw⟩ := hz
  unfold rieszPsi rieszPhi
  rw [Finset.prod_range_add]
  have h1 : ∏ i ∈ Finset.range i₁,
      |Real.cos (Real.pi * ((p : ℝ) ^ e * z) / ((p ^ γ * q' : ℕ) : ℝ) ^ (i + 1))| ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun _ _ ↦ Real.abs_cos_le_one _
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hq0 : (q' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : ∀ i ∈ Finset.range K',
      |Real.cos (Real.pi * ((p : ℝ) ^ e * z) / ((p ^ γ * q' : ℕ) : ℝ) ^ (i₁ + i + 1))| =
        |Real.cos (Real.pi * (x i * z / (p : ℝ) ^ (γ * (i + 1) + δ) +
          y i * z₁ / (q' : ℝ) ^ (i₁ + i + 1)))| := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hxyR : (x i : ℝ) * (q' : ℝ) ^ (i₁ + i + 1) + y i * (p : ℝ) ^ (γ * (i + 1) + δ) = 1 := by
      exact_mod_cast hxy i
    have hzR : (z : ℝ) = z₁ + (q' : ℝ) ^ (i₁ + i + 1) * (q' : ℝ) ^ (K' - i - 1) * w := by
      have : (z : ℝ) = z₁ + (q' : ℝ) ^ (i₁ + K') * w := by
        have := congrArg (fun t : ℤ ↦ (t : ℝ)) hw; push_cast at this; linarith
      rw [this, ← pow_add]; congr 3; omega
    have hpow : ((p ^ γ * q' : ℕ) : ℝ) ^ (i₁ + i + 1) =
        (p : ℝ) ^ e * (p : ℝ) ^ (γ * (i + 1) + δ) * (q' : ℝ) ^ (i₁ + i + 1) := by
      push_cast; rw [mul_pow, ← pow_mul, ← pow_add]; congr 2; nlinarith
    have : Real.pi * ((p : ℝ) ^ e * z) / ((p ^ γ * q' : ℕ) : ℝ) ^ (i₁ + i + 1) =
        Real.pi * (x i * z / (p : ℝ) ^ (γ * (i + 1) + δ) + y i * z₁ / (q' : ℝ) ^ (i₁ + i + 1)) +
          ((y i * w * q' ^ (K' - i - 1) : ℤ) : ℝ) * Real.pi := by
      rw [hpow]; push_cast
      exact crt_identity (pow_ne_zero _ hp0) (pow_ne_zero _ hp0) (pow_ne_zero _ hq0) hxyR hzR
    rw [this, abs_cos_add_int_mul_pi]
  rw [Finset.prod_congr rfl h2]
  calc _ ≤ 1 * ∏ i ∈ Finset.range K', |Real.cos (Real.pi * (x i * z / (p : ℝ) ^ (γ * (i + 1) + δ) +
          y i * z₁ / (q' : ℝ) ^ (i₁ + i + 1)))| := by
        gcongr
    _ = _ := one_mul _

/-! ### Orbit sums -/

/-- `c'ᴷ ∣ Bᴹ (B^D − 1)` once `M ≥ K c'` and `φ(c'ᴷ) ∣ D`. -/
theorem dvd_pow_mul_pow_sub_one {B c' K : ℕ} (hB : 1 ≤ B) (hc' : 1 ≤ c') {M D : ℕ}
    (hM : K * c' ≤ M) (hD : Nat.totient (c' ^ K) ∣ D) : c' ^ K ∣ B ^ M * (B ^ D - 1) := by
  exact (dvd_pow_mul_pow_totient_sub_one hB hc' hM).trans
    (mul_dvd_mul_left _ (Nat.pow_sub_one_dvd_pow_sub_one B hD))

theorem lteVal_pow_totient {p : ℕ} [hp : Fact p.Prime] {B c' : ℕ} (hB : ¬ p ∣ B) (hB2 : 2 ≤ B)
    (hc' : 1 ≤ c') (hpc : ¬ p ∣ c') {K : ℕ} (hK : 1 ≤ K) :
    lteVal p (B ^ Nat.totient (c' ^ K)) = lteVal p B + multiplicity p (Nat.totient c') := by
  have hΦ : Nat.totient (c' ^ K) ≠ 0 := (Nat.totient_pos.2 (pow_pos (by omega) _)).ne'
  rw [← multiplicity_totient_pow hc' hpc hK, ← lte_lteExp hB hB2 hΦ]
  simp only [lteVal]; rw [← pow_mul, ← pow_mul, mul_comm]

/-- **Orbit sum.** With `q = p^γ q'`, `p ∤ q'B Y`, `e + δ = γ i₁` and `K' ≥ T + 1`,
`∑_{m<S} Ψ_{i₁+K'}(pᵉ Y Bᵐ) ≤ (i₁+K') q' + (S + E q^{i₁+K'}) 2^{-(K'-T-1)/2}`. -/
theorem sum_rieszPsi_orbit_le (p γ q' : ℕ) [hp : Fact p.Prime] (hγ : 1 ≤ γ) (hq' : 1 ≤ q')
    (hpq : ¬ p ∣ q') {B : ℕ} (hB : ¬ p ∣ B) (hB2 : 2 ≤ B) (Y : ℕ) (hY : ¬ p ∣ Y)
    (e δ i₁ K' : ℕ) (he : e + δ = γ * i₁)
    (hK' : lteVal p B + multiplicity p (Nat.totient q') + 1 ≤ K') (S : ℕ) :
    ∑ m ∈ Finset.range S, rieszPsi (p ^ γ * q') (i₁ + K') ((p : ℝ) ^ e * ((Y * B ^ m : ℕ) : ℝ)) ≤
      (i₁ + K') * q' + (S + lteExp p * ((p ^ γ * q' : ℕ) : ℝ) ^ (i₁ + K')) *
        Real.sqrt 2⁻¹ ^ (K' - (lteVal p B + multiplicity p (Nat.totient q')) - 1) := by
  obtain ⟨K, hKdef⟩ : ∃ K, K = i₁ + K' := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ γ * q' := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = lteVal p B + multiplicity p (Nat.totient q') := ⟨_, rfl⟩
  rw [← hKdef, ← hqdef, ← hTdef]
  rw [← hTdef] at hK'
  set ρ := Real.sqrt 2⁻¹
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hp2 := hp.out.two_le
  have hK1 : 1 ≤ K := by omega
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ, Φ = Nat.totient (q' ^ K) := ⟨_, rfl⟩
  have hΦ0 : 0 < Φ := hΦdef ▸ Nat.totient_pos.2 (pow_pos (by omega) _)
  obtain ⟨E, hEdef⟩ : ∃ E, E = lteExp p := ⟨_, rfl⟩
  have hE : 1 ≤ E := by rw [hEdef, lteExp]; omega
  obtain ⟨mB, hmBdef⟩ : ∃ mB, mB = B ^ Φ := ⟨_, rfl⟩
  have hmB2 : 2 ≤ mB := hmBdef ▸ le_trans hB2 (Nat.le_self_pow hΦ0.ne' B)
  have hmB : ¬ p ∣ mB := fun h ↦ hB (hp.out.dvd_of_dvd_pow (hmBdef ▸ h))
  obtain ⟨t, htdef⟩ : ∃ t, t = lteVal p mB := ⟨_, rfl⟩
  have ht : t = T := by rw [htdef, hmBdef, hΦdef, hTdef, lteVal_pow_totient hB hB2 hq' hpq hK1]
  obtain ⟨L, hLdef⟩ : ∃ L, L = Φ * E := ⟨_, rfl⟩
  have hgL : mB ^ lteExp p = B ^ L := by rw [hmBdef, hLdef, hEdef, ← pow_mul]
  have htK : t + 1 ≤ K' := by omega
  have htγ : t ≤ γ * K' := le_trans (by omega) (Nat.le_mul_of_pos_left K' (by omega))
  obtain ⟨n, hndef⟩ : ∃ n, n = γ * K' + δ - t := ⟨_, rfl⟩
  have htn : t + n = γ * K' + δ := by omega
  obtain ⟨P, hPdef⟩ : ∃ P, P = L * p ^ n := ⟨_, rfl⟩
  have hP0 : 0 < P := by
    rw [hPdef, hLdef]; exact Nat.mul_pos (Nat.mul_pos hΦ0 (by omega)) (pow_pos (by omega) _)
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ = K * q' := ⟨_, rfl⟩
  set f : ℕ → ℝ := fun m ↦ rieszPsi q K ((p : ℝ) ^ e * ((Y * B ^ m : ℕ) : ℝ)) with hf
  have hf0 : ∀ m, 0 ≤ f m := fun m ↦ rieszPsi_nonneg _ _ _
  -- the first `m₀` terms
  have h1 : ∑ m ∈ Finset.range S, f m ≤ m₀ + ∑ m ∈ Finset.range S, f (m₀ + m) := by
    calc ∑ m ∈ Finset.range S, f m ≤ ∑ m ∈ Finset.range (m₀ + S), f m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            (fun _ _ _ ↦ hf0 _)
      _ = ∑ m ∈ Finset.range m₀, f m + ∑ m ∈ Finset.range S, f (m₀ + m) :=
          Finset.sum_range_add _ _ _
      _ ≤ m₀ + ∑ m ∈ Finset.range S, f (m₀ + m) := by
          gcongr
          calc ∑ m ∈ Finset.range m₀, f m ≤ ∑ m ∈ Finset.range m₀, (1 : ℝ) :=
                Finset.sum_le_sum fun m _ ↦ rieszPsi_le_one _ _ _
            _ = m₀ := by simp
  -- divisibilities
  have hdvdq : ∀ M D, m₀ ≤ M → Φ ∣ D → q' ^ K ∣ B ^ M * (B ^ D - 1) := fun M D hM hD ↦
    dvd_pow_mul_pow_sub_one (by omega) hq' (hm₀ ▸ hM) (hΦdef ▸ hD)
  have hdvdp : p ^ (t + n) ∣ B ^ P - 1 := by
    have := dvd_pow_lteExp_pow_sub_one hmB hmB2 n
    rwa [hgL, ← pow_mul, ← htdef, ← hPdef] at this
  have hcopq : Nat.Coprime (p ^ (t + n)) (q' ^ K) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpq)
  have hqK : ((q : ℕ) : ℝ) ^ K = (p : ℝ) ^ e * (p : ℝ) ^ (t + n) * (q' : ℝ) ^ K := by
    rw [hqdef, ← pow_add, htn]; push_cast; rw [mul_pow, ← pow_mul]; congr 2
    rw [hKdef]; nlinarith
  have hper : ∀ m, f (m₀ + m + P) = f (m₀ + m) := by
    intro m
    have hΦP : Φ ∣ P := by rw [hPdef, hLdef]; exact (dvd_mul_right Φ E).mul_right _
    obtain ⟨w, hw⟩ := hcopq.mul_dvd_of_dvd_of_dvd (hdvdp.mul_left _)
      (hdvdq (m₀ + m) P (by omega) hΦP)
    have hB1 : 1 ≤ B ^ P := Nat.one_le_pow _ _ (by omega)
    have hBP : (B : ℝ) ^ P = 1 + ((B ^ P - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hB1]; ring
    have hwR : (B : ℝ) ^ (m₀ + m) * ((B ^ P - 1 : ℕ) : ℝ) =
        (p : ℝ) ^ (t + n) * (q' : ℝ) ^ K * w := by exact_mod_cast hw
    simp only [hf]
    have : (p : ℝ) ^ e * ((Y * B ^ (m₀ + m + P) : ℕ) : ℝ) =
        (p : ℝ) ^ e * ((Y * B ^ (m₀ + m) : ℕ) : ℝ) + (q : ℝ) ^ K * (((Y * w : ℕ) : ℤ) : ℝ) := by
      rw [hqK]; push_cast; rw [pow_add (B : ℝ) (m₀ + m) P, hBP, mul_add, mul_one]
      linear_combination (p : ℝ) ^ e * Y * hwR
    have hq1 : 1 ≤ q := by
      rw [hqdef]; exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero)
        (by omega))
    rw [this, rieszPsi_add q K hq1]
  -- one residue class of `m` modulo `L`
  obtain ⟨a, ha, hβ⟩ := exists_rieszPsi_le_rieszPhi p γ q' hp.out hγ hq' hpq e δ i₁ K' he
  have hclass : ∀ u, ∑ j ∈ Finset.range (p ^ n), f (m₀ + (L * j + u)) ≤
      p ^ n * ρ ^ (K' - t - 1) := by
    intro u
    obtain ⟨c, hcdef⟩ : ∃ c, c = Y * B ^ (m₀ + u) := ⟨_, rfl⟩
    have hc : ¬ p ∣ c := by
      intro h; rw [hcdef] at h
      rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
      · exact hY h
      · exact hB (hp.out.dvd_of_dvd_pow h)
    obtain ⟨β, hβ'⟩ := hβ (c : ℤ)
    have hfj : ∀ j, f (m₀ + (L * j + u)) ≤
        rieszPhi p γ δ a β K' ((c * (mB ^ lteExp p) ^ j : ℕ) : ℝ) := by
      intro j
      have heq : Y * B ^ (m₀ + (L * j + u)) = c * (mB ^ lteExp p) ^ j := by
        rw [hcdef, hgL, ← pow_mul, mul_assoc, ← pow_add]; congr 2; ring
      simp only [hf]; rw [heq]
      have hg1 : 1 ≤ B ^ (L * j) := Nat.one_le_pow _ _ (by omega)
      have hd := hdvdq (m₀ + u) (L * j) (by omega)
        (by rw [hLdef]; exact ((dvd_mul_right Φ E).mul_right j))
      have h2 : (q' : ℤ) ^ (i₁ + K') ∣ ((c * (mB ^ lteExp p) ^ j : ℕ) : ℤ) - (c : ℤ) := by
        have : ((c * (mB ^ lteExp p) ^ j : ℕ) : ℤ) - (c : ℤ) =
            ((Y * (B ^ (m₀ + u) * (B ^ (L * j) - 1)) : ℕ) : ℤ) := by
          rw [hcdef, hgL, ← pow_mul]; push_cast [Nat.cast_sub hg1]; ring
        rw [this, ← hKdef]; exact_mod_cast hd.mul_left Y
      have := hβ' _ h2
      rw [← hKdef, ← hqdef] at this
      exact_mod_cast this
    have hF : ∀ w z : ℕ, rieszPhi p γ δ a β K' (((w + p ^ (t + n) * z : ℕ) : ℝ)) =
        rieszPhi p γ δ a β K' ((w : ℕ) : ℝ) := by
      intro w z
      have := rieszPhi_add p γ δ (by omega) a β K' (w : ℝ) (z : ℤ)
      rw [← htn] at this; push_cast; exact_mod_cast this
    calc ∑ j ∈ Finset.range (p ^ n), f (m₀ + (L * j + u))
        ≤ ∑ j ∈ Finset.range (p ^ n), rieszPhi p γ δ a β K' ((c * (mB ^ lteExp p) ^ j : ℕ) : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ hfj j
      _ = ∑ j ∈ Finset.range (p ^ n), rieszPhi p γ δ a β K' ((c % p ^ t + p ^ t * j : ℕ) : ℝ) :=
          orbit_sum_eq p (mB ^ lteExp p) t n c
            (by have := two_le_pow_lteExp hp.out hmB2 (p := p); omega)
            (fun h ↦ hmB (hp.out.dvd_of_dvd_pow h)) (htdef ▸ pow_lteVal_dvd p mB)
            (htdef ▸ not_dvd_pow_lteExp_sub_one hmB hmB2 n) hc
            (fun w ↦ rieszPhi p γ δ a β K' (w : ℝ)) hF
      _ ≤ p ^ n * ρ ^ (K' - t - 1) := by
          have htt : t ≤ γ * (t + 1) := le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
          have h := sum_rieszPhi_class_le p γ δ hp2 hγ a ha β t (γ * (t + 1) + δ - t) (t + 1)
            (by omega) ((c % p ^ t : ℕ) : ℝ) (K' - t - 1)
          have hn : p ^ (γ * (t + 1) + δ - t) * (p ^ γ) ^ (K' - t - 1) = p ^ n := by
            rw [← pow_mul, ← pow_add]; congr 1
            have : γ * (K' - t - 1) + γ * (t + 1) = γ * K' := by
              rw [← Nat.mul_add]; congr 1; omega
            omega
          have hnR : (p : ℝ) ^ (γ * (t + 1) + δ - t) * ((p : ℝ) ^ γ) ^ (K' - t - 1) =
              (p : ℝ) ^ n := by exact_mod_cast hn
          rw [hn, show t + 1 + (K' - t - 1) = K' by omega, hnR] at h
          refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) h
          push_cast; ring_nf
  have hperiod : ∑ m ∈ Finset.range P, f (m₀ + m) ≤ P * ρ ^ (K' - t - 1) := by
    rw [hPdef, sum_range_mul_eq (fun m ↦ f (m₀ + m)) L (p ^ n), Finset.sum_comm]
    calc _ ≤ ∑ u ∈ Finset.range L, (p : ℝ) ^ n * ρ ^ (K' - t - 1) :=
          Finset.sum_le_sum fun u _ ↦ hclass u
      _ = _ := by simp; ring
  have h4 := sum_periodic_le (fun m ↦ f (m₀ + m)) (fun m ↦ hf0 _) P hP0
    (fun m ↦ show f (m₀ + (m + P)) = f (m₀ + m) by rw [← add_assoc]; exact hper m)
    (ρ ^ (K' - t - 1)) hperiod S
  have hPle : (P : ℝ) ≤ lteExp p * (q : ℝ) ^ K := by
    have hn : n ≤ γ * K := by rw [hKdef, Nat.mul_add]; omega
    have : P ≤ lteExp p * q ^ K := by
      rw [hPdef, hLdef, hqdef, mul_pow, ← pow_mul, ← hEdef, hΦdef]
      calc Nat.totient (q' ^ K) * E * p ^ n ≤ q' ^ K * E * p ^ (γ * K) := by
            gcongr
            exact Nat.totient_le _
        _ = _ := by ring
    exact_mod_cast this
  rw [← ht]
  calc ∑ m ∈ Finset.range S, f m ≤ m₀ + ((S : ℝ) + P) * ρ ^ (K' - t - 1) :=
        h1.trans (add_le_add (le_refl _) h4)
    _ ≤ _ := by
        rw [hm₀, hKdef]; push_cast
        gcongr
        rw [← hKdef]; exact hPle

/-! ### The second moment -/

/-- Few `d < N` have a large `v_p(bᵈ − 1)`: by lifting the exponent they are multiples of
`p^{J+1}`. -/
theorem card_bad_le {p : ℕ} [hp : Fact p.Prime] {b : ℕ} (hb : 2 ≤ b) (J N : ℕ) :
    ((Finset.Ico 1 N).filter fun d ↦ ¬ (b ^ d - 1).factorization p ≤ lteVal p b + J).card ≤
      N / p ^ (J + 1) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_le_card fun d hd ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hd ⊢
  obtain ⟨⟨hd1, hdN⟩, hbad⟩ := hd
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  have hpb : ¬ p ∣ b := by
    intro hpb
    apply hbad
    rw [Nat.factorization_eq_zero_of_not_dvd]
    · omega
    intro h
    have h1 : p ∣ b ^ d := dvd_pow hpb (by omega)
    have h2 : 1 ≤ b ^ d := Nat.one_le_pow _ _ (by omega)
    have : p ∣ 1 := by
      have := Nat.dvd_sub h1 h; rwa [Nat.sub_sub_self h2] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hne : (b ^ lteExp p) ^ d - 1 ≠ 0 := by
    have := Nat.le_self_pow (by omega : d ≠ 0) (b ^ lteExp p)
    have := two_le_pow_lteExp hp.out hb (p := p); omega
  have h1 : p ^ (lteVal p b + J + 1) ∣ (b ^ lteExp p) ^ d - 1 := by
    refine (pow_dvd_pow p (by omega)).trans ((Nat.ordProj_dvd (b ^ d - 1) p).trans ?_)
    rw [← pow_mul, mul_comm]
    exact Nat.pow_sub_one_dvd_pow_sub_one b (dvd_mul_right d _)
  rw [multiplicity_dvd_iff_le hne, lte_lteExp hpb hb (by omega)] at h1
  exact (multiplicity_dvd_iff_le (by omega)).2 (by omega)

/-- **Second moment bound** for `X_q`, `q = p^γ q'`, in a base `b` with `bˢ = qʳ B`, `p ∤ B`. -/
theorem secondMoment_le (p γ q' r s : ℕ) [hp : Fact p.Prime] (hγ : 1 ≤ γ) (hq' : 1 ≤ q')
    (hpq : ¬ p ∣ q') {b B : ℕ} (hb : 2 ≤ b) (hs : 1 ≤ s)
    (hbs : b ^ s = (p ^ γ * q') ^ r * B) (hB : ¬ p ∣ B) (hB2 : 2 ≤ B) (h : ℤ) (hh : h ≠ 0)
    (J K : ℕ) (hK : h.natAbs.factorization p + s * b.factorization p + (lteVal p b + J) +
      (lteVal p B + multiplicity p (Nat.totient q')) + 1 + J ≤ K) (N : ℕ) :
    ∫ ω, ‖∑ n ∈ Finset.range N, ee (h * (b : ℝ) ^ n * coinPoint (p ^ γ * q') ω)‖ ^ 2 ∂coinMeasure ≤
      N + 2 * (((N / p ^ (J + 1) : ℕ) : ℝ) * N + N * (s * (K * q' +
        (((N / s : ℕ) : ℝ) + 1 + lteExp p * ((p ^ γ * q' : ℕ) : ℝ) ^ K) * Real.sqrt 2⁻¹ ^ J))) := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ γ * q' := ⟨_, rfl⟩
  rw [← hqdef]
  have hp2 := hp.out.two_le
  have hq : 2 ≤ q := by
    rw [hqdef]
    exact le_trans hp2 (le_trans (Nat.le_self_pow (by omega) p) (Nat.le_mul_of_pos_right _
      (by omega)))
  set ρ := Real.sqrt 2⁻¹
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set T := lteVal p B + multiplicity p (Nat.totient q')
  set Y : ℕ → ℕ → ℕ := fun d ε ↦ h.natAbs * b ^ ε * (b ^ d - 1) with hYdef
  set v : ℕ → ℕ → ℕ := fun d ε ↦ (Y d ε).factorization p with hvdef
  set Y' : ℕ → ℕ → ℕ := fun d ε ↦ Y d ε / p ^ v d ε with hY'def
  have hYv : ∀ d ε, p ^ v d ε * Y' d ε = Y d ε := fun d ε ↦
    Nat.ordProj_mul_ordCompl_eq_self _ _
  have hbd0 : ∀ d, 1 ≤ d → b ^ d - 1 ≠ 0 := by
    intro d hd; have := Nat.le_self_pow (by omega : d ≠ 0) b; omega
  have hY0 : ∀ d ε, 1 ≤ d → Y d ε ≠ 0 := fun d ε hd ↦
    mul_ne_zero (mul_ne_zero (Int.natAbs_ne_zero.2 hh) (pow_ne_zero _ (by omega))) (hbd0 d hd)
  set G : ℕ → ℕ → ℝ := fun d l ↦
    rieszPsi q K ((p : ℝ) ^ v d (l % s) * ((Y' d (l % s) * B ^ (l / s) : ℕ) : ℝ)) with hGdef
  have hfreq : ∀ l d, 1 ≤ d → |(h : ℝ) * ((b : ℝ) ^ (l + d) - (b : ℝ) ^ l)| =
      (q : ℝ) ^ (r * (l / s)) *
        ((p : ℝ) ^ v d (l % s) * ((Y' d (l % s) * B ^ (l / s) : ℕ) : ℝ)) := by
    intro l d hd
    have hbd1 : 1 ≤ b ^ d := Nat.one_le_pow _ _ (by omega)
    have hpY : (p : ℝ) ^ v d (l % s) * (Y' d (l % s) : ℝ) =
        (h.natAbs : ℝ) * (b : ℝ) ^ (l % s) * ((b : ℝ) ^ d - 1) := by
      have := congrArg (fun n : ℕ ↦ (n : ℝ)) (hYv d (l % s))
      simp only [hYdef] at this; push_cast [Nat.cast_sub hbd1] at this; exact this
    have hbl : (b : ℝ) ^ l = ((q : ℝ) ^ r * B) ^ (l / s) * (b : ℝ) ^ (l % s) := by
      have : ((b ^ s : ℕ) : ℝ) = (((p ^ γ * q') ^ r * B : ℕ) : ℝ) := by rw [hbs]
      rw [← hqdef] at this; push_cast at this
      rw [← this, ← pow_mul, ← pow_add, Nat.div_add_mod]
    have habs : |(h : ℝ)| = (h.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    have hb1 : (1 : ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b))
    rw [abs_mul, habs, show (b : ℝ) ^ (l + d) - (b : ℝ) ^ l = (b : ℝ) ^ l * ((b : ℝ) ^ d - 1) by
      ring, abs_of_nonneg (mul_nonneg (by positivity) (by linarith)), hbl]
    push_cast
    rw [mul_pow, ← pow_mul]
    linear_combination (-(q : ℝ) ^ (r * (l / s)) * (B : ℝ) ^ (l / s)) * hpY
  have hΦ : ∀ l d, 1 ≤ d → ∀ ξ : ℝ, |ξ| = |(h : ℝ) * ((b : ℝ) ^ (l + d) - (b : ℝ) ^ l)| →
      ‖∫ ω, ee (ξ * coinPoint q ω) ∂coinMeasure‖ ≤ G d l := fun l d hd ξ hξ ↦
    charFun_le_rieszPsi q hq ξ _ K _ (hξ.trans (hfreq l d hd))
  have hpair := pair_sum_le
    (fun n m' ↦ ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m')) * coinPoint q ω) ∂coinMeasure‖) G
    (fun d l ↦ rieszPsi_nonneg _ _ _)
    (fun n ↦ by simpa using charFun_le q hq 0 0)
    (fun n m' hmn ↦ hΦ m' (n - m') (by omega) _ (by rw [show m' + (n - m') = n by omega]))
    (fun n m' hmn ↦ hΦ n (m' - n) (by omega) _ (by
      rw [show n + (m' - n) = m' by omega, ← abs_neg]; congr 1; ring)) N
  -- the bound for one `d`
  set A : ℝ := s * (K * q' + (((N / s : ℕ) : ℝ) + 1 + lteExp p * (q : ℝ) ^ K) * ρ ^ J) with hAdef
  have hA : 0 ≤ A := by positivity
  have hall : ∀ d, ∑ l ∈ Finset.range N, G d l ≤ N := fun d ↦
    (Finset.sum_le_sum fun l _ ↦ rieszPsi_le_one _ _ _).trans (by simp)
  have hgood : ∀ d, 1 ≤ d → (b ^ d - 1).factorization p ≤ lteVal p b + J →
      ∑ l ∈ Finset.range N, G d l ≤ A := by
    intro d hd hgd
    set S := N / s + 1
    have hNS : N ≤ s * S := by
      have := Nat.div_add_mod N s; have := Nat.mod_lt N (show s > 0 by omega)
      simp only [S]; rw [Nat.mul_add, mul_one]; omega
    calc ∑ l ∈ Finset.range N, G d l ≤ ∑ l ∈ Finset.range (s * S), G d l :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNS)
            (fun _ _ _ ↦ rieszPsi_nonneg _ _ _)
      _ = ∑ ε ∈ Finset.range s, ∑ m ∈ Finset.range S, G d (s * m + ε) := by
          rw [sum_range_mul_eq, Finset.sum_comm]
      _ ≤ ∑ ε ∈ Finset.range s,
            (K * q' + (((N / s : ℕ) : ℝ) + 1 + lteExp p * (q : ℝ) ^ K) * ρ ^ J) :=
          Finset.sum_le_sum fun ε hε ↦ ?_
      _ = A := by rw [hAdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hεs : ε < s := Finset.mem_range.1 hε
    have hG : ∀ m, G d (s * m + ε) =
        rieszPsi q K ((p : ℝ) ^ v d ε * ((Y' d ε * B ^ m : ℕ) : ℝ)) := by
      intro m
      have h1 : (s * m + ε) % s = ε := by
        rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hεs]
      have h2 : (s * m + ε) / s = m := by
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hεs, add_zero]
      simp only [hGdef, h1, h2]
    have hvle : v d ε ≤ h.natAbs.factorization p + s * b.factorization p + (lteVal p b + J) := by
      simp only [hvdef, hYdef]
      rw [Nat.factorization_mul (mul_ne_zero (Int.natAbs_ne_zero.2 hh) (pow_ne_zero _ (by omega)))
        (hbd0 d hd), Nat.factorization_mul (Int.natAbs_ne_zero.2 hh) (pow_ne_zero _ (by omega)),
        Nat.factorization_pow]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      have : ε * b.factorization p ≤ s * b.factorization p := Nat.mul_le_mul_right _ hεs.le
      omega
    have hvK : v d ε ≤ K := by omega
    have hY' : ¬ p ∣ Y' d ε := Nat.not_dvd_ordCompl hp.out (hY0 d ε hd)
    have he : v d ε + (γ - 1) * v d ε = γ * v d ε := by
      obtain ⟨g, rfl⟩ : ∃ g, γ = g + 1 := ⟨γ - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have := sum_rieszPsi_orbit_le p γ q' hγ hq' hpq hB hB2 (Y' d ε) hY' (v d ε) ((γ - 1) * v d ε)
      (v d ε) (K - v d ε) he (by omega) S
    have e2 : v d ε + (K - v d ε) = K := by omega
    have e1 : ((v d ε : ℕ) : ℝ) + ((K - v d ε : ℕ) : ℝ) = K := by exact_mod_cast e2
    rw [e2, e1, ← hqdef] at this
    simp_rw [hG]
    refine this.trans ?_
    have hJ : J ≤ K - v d ε - T - 1 := by omega
    simp only [S]; push_cast
    gcongr _ + _ * ?_
    exact pow_le_pow_of_le_one hρ0 hρ1 hJ
  -- summing over `d`
  have hsum : ∑ d ∈ Finset.Ico 1 N, ∑ l ∈ Finset.range N, G d l ≤
      ((N / p ^ (J + 1) : ℕ) : ℝ) * N + N * A := by
    calc ∑ d ∈ Finset.Ico 1 N, ∑ l ∈ Finset.range N, G d l
        ≤ ∑ d ∈ Finset.Ico 1 N,
            ((if ¬ (b ^ d - 1).factorization p ≤ lteVal p b + J then (N : ℝ) else 0) + A) := by
          refine Finset.sum_le_sum fun d hd ↦ ?_
          simp only [Finset.mem_Ico] at hd
          by_cases hbad : (b ^ d - 1).factorization p ≤ lteVal p b + J
          · simp only [hbad, not_true_eq_false, ite_false, zero_add]; exact hgood d hd.1 hbad
          · simp only [hbad, not_false_eq_true, ite_true]; linarith [hall d]
      _ = (((Finset.Ico 1 N).filter fun d ↦ ¬ (b ^ d - 1).factorization p ≤ lteVal p b + J).card :
            ℝ) * N + (N - 1 : ℕ) * A := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
            nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico]
      _ ≤ _ := by
          have h1 : ((((Finset.Ico 1 N).filter fun d ↦
              ¬ (b ^ d - 1).factorization p ≤ lteVal p b + J).card : ℕ) : ℝ) ≤
              ((N / p ^ (J + 1) : ℕ) : ℝ) := by exact_mod_cast card_bad_le hb J N
          have h2 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
          gcongr
  refine (secondMoment_expand (coinPoint q) (measurable_coinPoint q) b h N).trans (hpair.trans ?_)
  linarith

/-! ### Almost sure normality -/

theorem le_mul_rpow_neg_half {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : x ^ 2 ≤ N) :
    x ≤ N * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_neg hN0.le, show (1 / 2 : ℝ) = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have : (N : ℝ) * (Real.sqrt N)⁻¹ = Real.sqrt N := by
    field_simp; exact (Real.sq_sqrt hN0.le).symm
  rw [this]; exact (le_abs_self x).trans (Real.abs_le_sqrt hx)

/-- **Schmidt.** If `b` and `q ≥ 2` are multiplicatively independent, `X_q` is almost surely
normal in base `b`. -/
theorem ae_isNormal {q b : ℕ} (hq : 2 ≤ q) (hb : 2 ≤ b)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → b ^ m ≠ q ^ n) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (coinPoint q ω) := by
  obtain ⟨p, r, s, hp, hpq, hs, hdvd, hpB, hB2⟩ := exists_reduction hb hq hind
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = b ^ s / q ^ r := ⟨_, rfl⟩
  rw [← hBdef] at hpB hB2
  have hbs : b ^ s = q ^ r * B := by rw [hBdef]; exact (Nat.mul_div_cancel' hdvd).symm
  obtain ⟨γ, q', hq', hqγ⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : q ≠ 0) p hp.ne_one
  have hq'1 : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · rw [h, mul_zero] at hqγ; omega
    · exact h
  have hγ : 1 ≤ γ := by
    by_contra h0
    have : γ = 0 := by omega
    rw [this, pow_zero, one_mul] at hqγ
    exact hq' (hqγ ▸ hpq)
  rw [hqγ] at hbs hq ⊢
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = p ^ γ * q' := ⟨_, rfl⟩
  rw [← hQdef] at hq ⊢
  set ρ := Real.sqrt 2⁻¹
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 (by norm_num)
  have hρ1 : ρ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hρ2 : 1 ≤ 2 * ρ := by
    have : ρ ^ 2 = 2⁻¹ := Real.sq_sqrt (by norm_num); nlinarith
  set c := -Real.log ρ / ((2 * Q : ℕ) : ℝ)
  have hc : 0 < c := div_pos (neg_pos.2 (Real.log_neg hρ0 hρ1)) (by positivity)
  refine ae_isNormal_of_secondMoment coinMeasure hb (coinPoint Q) (measurable_coinPoint Q) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  set C1 := h.natAbs.factorization p + s * b.factorization p + lteVal p b +
    (lteVal p B + multiplicity p (Nat.totient q')) + 1
  set E := lteExp p
  set C : ℝ := 1 + 4 * ρ⁻¹ + 2 * s * q' * (C1 + 1) + 2 * s + 2 * s * E * (Q : ℝ) ^ C1
  have hC : 0 < C := by positivity
  refine (summable_sched_bound C c hC hc).of_nonneg_of_le
    (fun j ↦ div_nonneg (integral_nonneg fun ω ↦ by positivity) (by positivity)) (fun j ↦ ?_)
  set N := sched j
  have hN1 : 1 ≤ N := one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  set M := Nat.log 3 N / 2
  set J := M / (2 * Q)
  set K := C1 + 2 * J
  have hmom := secondMoment_le p γ q' r s hγ hq'1 hq' hb hs hbs hpB hB2 h hh J K
    (by simp only [K, C1]; omega) N
  rw [← hQdef] at hmom
  set R := (N : ℝ) ^ (-(1 / 2 : ℝ))
  set Ex := Real.exp (-c * freeCount isFree M)
  have hR : 0 ≤ R := by positivity
  have hEx : 0 ≤ Ex := (Real.exp_pos _).le
  set Rt := (N : ℝ) * R
  -- elementary estimates
  have h3M : 3 ^ M * 3 ^ M ≤ N := by
    rw [← pow_add]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      (Nat.pow_log_le_self 3 (by omega))
  have hRt1 : (1 : ℝ) ≤ Rt := le_mul_rpow_neg_half hN1 (by norm_num; exact_mod_cast hN1)
  have h3Rt : (3 : ℝ) ^ M ≤ Rt := le_mul_rpow_neg_half hN1 (by
    rw [sq, ← mul_pow]; exact_mod_cast (by rw [mul_pow]; exact h3M))
  have hMRt : (M : ℝ) ≤ Rt := le_trans (by exact_mod_cast (Nat.lt_pow_self (by norm_num)).le) h3Rt
  have hQK : (Q : ℝ) ^ K ≤ (Q : ℝ) ^ C1 * 3 ^ M := by
    have : Q ^ (2 * J) ≤ 3 ^ M :=
      calc Q ^ (2 * J) ≤ (3 ^ Q) ^ (2 * J) :=
            Nat.pow_le_pow_left (Nat.lt_pow_self (by norm_num)).le _
        _ = 3 ^ (2 * Q * J) := by rw [← pow_mul]; ring_nf
        _ ≤ 3 ^ M := Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le M (2 * Q))
    have : (Q : ℝ) ^ (2 * J) ≤ 3 ^ M := by exact_mod_cast this
    rw [pow_add]; gcongr
  have hKle : (K : ℝ) ≤ (C1 + 1) * Rt := by
    have hJM : 2 * J ≤ M :=
      calc 2 * J ≤ 2 * Q * J := Nat.mul_le_mul_right _ (by nlinarith)
        _ ≤ M := Nat.mul_div_le M (2 * Q)
    have : (K : ℝ) ≤ C1 + M := by exact_mod_cast (by omega : K ≤ C1 + M)
    have : (C1 : ℝ) ≤ C1 * Rt := le_mul_of_one_le_right (by positivity) hRt1
    nlinarith
  have hρJ : ρ ^ J ≤ ρ⁻¹ * Ex := by
    refine (sqrt_inv_two_pow_le (2 * Q) M (by omega)).trans ?_
    gcongr
    have : (freeCount isFree M : ℝ) ≤ M := by
      exact_mod_cast NormalNumbers.CantorLiouvilleAll.Cassels.freeCount_le_self isFree M
    exact Real.exp_le_exp.2 (show -c * (M : ℝ) ≤ -c * freeCount isFree M by nlinarith)
  have hρJ1 : ρ ^ J ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  have hρJ0 : 0 ≤ ρ ^ J := by positivity
  set X := ((N / p ^ (J + 1) : ℕ) : ℝ)
  have hX : X ≤ N * ρ ^ J := by
    have h1 : N / p ^ (J + 1) * 2 ^ J ≤ N :=
      le_trans (Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_left hp.two_le J)
        (Nat.pow_le_pow_right hp.pos (by omega)))) (Nat.div_mul_le_self N _)
    have h1 : X * 2 ^ J ≤ N := by simp only [X]; exact_mod_cast h1
    have h2 : 1 ≤ (2 : ℝ) ^ J * ρ ^ J := by rw [← mul_pow]; exact one_le_pow₀ hρ2
    have hX0 : 0 ≤ X := by positivity
    calc X ≤ X * (2 ^ J * ρ ^ J) := le_mul_of_one_le_right hX0 h2
      _ = (X * 2 ^ J) * ρ ^ J := by ring
      _ ≤ N * ρ ^ J := by gcongr
  have hNs : (s : ℝ) * ((N / s : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N s
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hq0 : (0 : ℝ) ≤ q' := by positivity
  have hE0 : (0 : ℝ) ≤ E := by positivity
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) ^ C1 := by positivity
  -- the five terms
  have t1 : (N : ℝ) ≤ N * Rt := le_mul_of_one_le_right hN0 hRt1
  have t2 : X * N ≤ ρ⁻¹ * (N * N * Ex) := by
    calc X * N ≤ (N * ρ ^ J) * N := by gcongr
      _ ≤ (N * (ρ⁻¹ * Ex)) * N := by gcongr
      _ = _ := by ring
  have t3 : (N : ℝ) * (s * (K * q')) ≤ s * q' * (C1 + 1) * (N * Rt) := by
    calc (N : ℝ) * (s * (K * q')) ≤ N * (s * (((C1 + 1) * Rt) * q')) := by gcongr
      _ = _ := by ring
  have t4 : (N : ℝ) * (s * (((N / s : ℕ) : ℝ) + 1) * ρ ^ J) ≤
      ρ⁻¹ * (N * N * Ex) + s * (N * Rt) := by
    have : (s : ℝ) * (((N / s : ℕ) : ℝ) + 1) ≤ N + s := by linarith
    calc (N : ℝ) * (s * (((N / s : ℕ) : ℝ) + 1) * ρ ^ J) ≤ N * ((N + s) * ρ ^ J) := by gcongr
      _ = N * N * ρ ^ J + s * (N * ρ ^ J) := by ring
      _ ≤ N * N * (ρ⁻¹ * Ex) + s * (N * Rt) := by
          gcongr
          exact hρJ1.trans hRt1
      _ = _ := by ring
  have t5 : (N : ℝ) * (s * (E * (Q : ℝ) ^ K * ρ ^ J)) ≤ s * E * (Q : ℝ) ^ C1 * (N * Rt) := by
    calc (N : ℝ) * (s * (E * (Q : ℝ) ^ K * ρ ^ J)) ≤ N * (s * (E * ((Q : ℝ) ^ C1 * Rt) * 1)) := by
          gcongr
          exact hQK.trans (by gcongr)
      _ = _ := by ring
  have hNRt : (N : ℝ) * Rt = N ^ 2 * R := by simp only [Rt]; ring
  calc _ ≤ _ := hmom
    _ = N + 2 * (X * N) + 2 * (N * (s * (K * q'))) +
          2 * (N * (s * (((N / s : ℕ) : ℝ) + 1) * ρ ^ J)) +
          2 * (N * (s * (E * (Q : ℝ) ^ K * ρ ^ J))) := by ring
    _ ≤ (1 + 2 * s * q' * (C1 + 1) + 2 * s + 2 * s * E * (Q : ℝ) ^ C1) * (N * Rt) +
          4 * ρ⁻¹ * (N * N * Ex) := by linarith [t1, t2, t3, t4, t5]
    _ ≤ C * (Ex + R) * (N : ℝ) ^ 2 := by
        rw [hNRt]
        have hN2 : 0 ≤ (N : ℝ) ^ 2 := by positivity
        have hρi : 0 ≤ ρ⁻¹ := by positivity
        have hA : 0 ≤ 1 + 2 * s * q' * ((C1 : ℝ) + 1) + 2 * s + 2 * s * E * (Q : ℝ) ^ C1 := by
          positivity
        have hC' : C = (1 + 2 * s * q' * ((C1 : ℝ) + 1) + 2 * s + 2 * s * E * (Q : ℝ) ^ C1) +
            4 * ρ⁻¹ := by simp only [C]; ring
        rw [hC']
        nlinarith [mul_nonneg hA (mul_nonneg hN2 hEx), mul_nonneg hρi (mul_nonneg hN2 hR)]

/-- **Schmidt's theorem.** If `b, c ≥ 2` are multiplicatively independent, some real number is
normal in base `b` and in no base `cʲ`, `j ≥ 1`. -/
theorem exists_isNormalIn_forall_not_isNormalIn_pow {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → b ^ m ≠ c ^ n) :
    ∃ x : ℝ, IsNormalIn b x ∧ ∀ j, 1 ≤ j → ¬ IsNormalIn (c ^ j) x := by
  have hq : 4 ≤ c ^ 2 := by nlinarith
  obtain ⟨ω, hω⟩ := (ae_isNormal (q := c ^ 2) (by omega) hb fun m n hm hn h ↦
    hind m (2 * n) hm (by omega) (by rw [h, ← pow_mul])).exists
  refine ⟨coinPoint (c ^ 2) ω, (isNormalIn_iff_isNormal b _).2 hω, fun j hj hn ↦ ?_⟩
  have hcj : 2 ≤ c ^ j := le_trans hc (Nat.le_self_pow (by omega) c)
  rw [isNormalIn_iff_of_pow_eq_pow (c := c ^ 2) hcj (by omega) (m := 2) (n := j) (by norm_num)
    (by omega) (by rw [← pow_mul, ← pow_mul, mul_comm])] at hn
  exact not_isNormalIn_coinPoint (c ^ 2) (by omega) ω hn

end Real.SchmidtGeneral
