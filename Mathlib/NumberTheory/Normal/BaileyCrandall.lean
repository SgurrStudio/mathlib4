/-
Copyright (c) 2026 Rob. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob
-/
module

public import Mathlib.NumberTheory.Normal.Weyl

/-!
# Bailey–Crandall dynamical reduction for BBP constants

For a base `b ≥ 2` and a real sequence `r : ℕ → ℝ` tending to `0`, consider the BBP-type series
`θ = ∑' k, r k / b ^ (k + 1)` and the associated Bailey–Crandall iteration on `[0, 1)`:
`x₀ = 0`, `x_{n+1} = Int.fract (b * x_n + r n)`.

We state and prove the two foundational unconditional theorems of Bailey and Crandall (2001):

1. **Shadowing / Normality Equivalence** (`Real.isNormalIn_bbpSum_iff_isEquidistributedModOne`):
   `θ` is normal in base `b` if and only if the Bailey–Crandall orbit `(x_n)` is equidistributed
   modulo one.
2. **Finite Attractor Theorem** (`Real.not_hasFiniteAttractorModOne_mul_pow`,
   `Real.not_hasFiniteAttractorModOne_bbpOrbit`):
   if `θ` is irrational, neither `(θ * b ^ n)` nor the shadowing orbit `(x_n)` can converge to a
   finite subset of `UnitAddCircle`. Thus Bailey–Crandall's **Hypothesis A** (that every BBP orbit
   either has a finite attractor or is equidistributed modulo one) immediately implies base-`b`
   normality of every irrational BBP constant (such as `π` in base `16`/`2` and `log 2` in base
   `2`).

## Main definitions

* `Real.bbpSum b r`: the BBP-type series `∑' k, r k / (b : ℝ) ^ (k + 1)`.
* `Real.bbpOrbit b r`: the Bailey–Crandall iteration `x₀ = 0`, `x_{n+1} = Int.fract (b * x_n + r n)`.
* `HasFiniteAttractorModOne u`: `u` approaches a finite subset of `UnitAddCircle`.

## References

* [D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant expansions*][BaileyCrandall2001]
* [J. C. Lagarias, *On the normality of arithmetical constants*][Lagarias2001]
-/

@[expose] public section

open Filter Topology

/-- A real sequence `u` has a *finite attractor modulo one* if its image in `UnitAddCircle`
approaches some finite set `S : Finset UnitAddCircle`. -/
def HasFiniteAttractorModOne (u : ℕ → ℝ) : Prop :=
  ∃ S : Finset UnitAddCircle, ∀ ε > 0, ∀ᶠ n in atTop,
    ∃ s ∈ S, dist (u n : UnitAddCircle) s < ε

namespace Real

/-- The BBP-type series `∑' k, r k / b ^ (k + 1)`. -/
noncomputable def bbpSum (b : ℕ) (r : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, r k / (b : ℝ) ^ (k + 1)

/-- The Bailey–Crandall dynamical orbit: `x₀ = 0`, `x_{n+1} = Int.fract (b * x_n + r n)`. -/
noncomputable def bbpOrbit (b : ℕ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => Int.fract ((b : ℝ) * bbpOrbit b r n + r n)

private lemma tendsto_cesaro_zero {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, a n) / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (half_pos hε)
  set S₀ : ℝ := ∑ n ∈ Finset.range N₀, a n
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * S₀ / ε)
  refine ⟨max N₀ (max N₁ 1), fun N hN ↦ ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun n _ ↦ ha₀ n) hNpos.le)]
  have hsplit : ∑ n ∈ Finset.range N, a n = S₀ + ∑ n ∈ Finset.Ico N₀ N, a n := by
    rw [← Finset.sum_range_add_sum_Ico a hN0]
  have htail : ∑ n ∈ Finset.Ico N₀ N, a n ≤ (N : ℝ) * (ε / 2) := by
    calc ∑ n ∈ Finset.Ico N₀ N, a n
        ≤ ∑ _ ∈ Finset.Ico N₀ N, (ε / 2) := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          have := hN₀ n (Finset.mem_Ico.1 hn).1
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha₀ n)] at this
          exact this.le
      _ = ((N - N₀ : ℕ) : ℝ) * (ε / 2) := by simp
      _ ≤ (N : ℝ) * (ε / 2) := by gcongr; exact Nat.sub_le N N₀
  have hhead : S₀ / N < ε / 2 := by
    rw [div_lt_iff₀ hNpos]
    have hlt : 2 * S₀ / ε < N := hN₁.trans_le (Nat.cast_le.2 hN1)
    have : 2 * S₀ < N * ε := (div_lt_iff₀ hε).1 hlt
    linarith
  rw [hsplit, add_div]
  have htail' : (∑ n ∈ Finset.Ico N₀ N, a n) / N ≤ ε / 2 :=
    (div_le_iff₀ hNpos).2 (by linarith)
  linarith

private lemma norm_unitAddCircle_coe_le_abs (x : ℝ) :
    ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [AddCircle.norm_eq' (p := (1 : ℝ)) one_pos]
  simpa using round_le x 0

private lemma coe_int_unitAddCircle (m : ℤ) : ((m : ℝ) : UnitAddCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨m, by simp⟩

private lemma norm_nsmul_unitAddCircle_eq {b : ℕ} (hb : 0 < b) {e : UnitAddCircle}
    (he : ‖e‖ < (2 * (b : ℝ))⁻¹) : ‖b • e‖ = (b : ℝ) * ‖e‖ := by
  obtain ⟨x₀, rfl⟩ := QuotientAddGroup.mk_surjective e
  set x : ℝ := x₀ - round x₀
  have hxcoe : (x : UnitAddCircle) = (x₀ : UnitAddCircle) := by
    change ((x₀ - (round x₀ : ℝ) : ℝ) : UnitAddCircle) = (x₀ : UnitAddCircle)
    rw [AddCircle.coe_sub, coe_int_unitAddCircle, sub_zero]
  have hxnorm : ‖(x₀ : UnitAddCircle)‖ = |x| := by
    rw [AddCircle.norm_eq' (p := (1 : ℝ)) one_pos]
    simp [x]
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbx : |(b : ℝ) * x| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_mul, abs_of_pos hb', abs_one]
    have h1 : (b : ℝ) * |x| < 1 / 2 := by
      rw [← hxnorm]
      have hmul := mul_lt_mul_of_pos_left he hb'
      have hcalc : (b : ℝ) * (2 * (b : ℝ))⁻¹ = 1 / 2 := by field_simp
      linarith
    linarith
  have hcoe : b • (x₀ : UnitAddCircle) = (((b : ℝ) * x : ℝ) : UnitAddCircle) := by
    rw [← hxcoe, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  change ‖b • (x₀ : UnitAddCircle)‖ = (b : ℝ) * ‖(x₀ : UnitAddCircle)‖
  rw [hcoe, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 hbx,
    abs_mul, abs_of_pos hb', ← hxnorm]

private lemma summable_bbp_shift {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (n : ℕ) : Summable (fun k : ℕ ↦ r (n + k) / (b : ℝ) ^ (k + 1)) := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr 1 one_pos
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hgeom : Summable (fun k : ℕ ↦ ((b : ℝ)⁻¹) ^ (k + 1)) :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)).comp_injective
      Nat.succ_injective
  refine Summable.of_norm_bounded_eventually_nat hgeom ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) ^ (k + 1)),
    div_eq_mul_inv, ← inv_pow]
  have hrk : |r (n + k)| ≤ 1 := by
    have := hN (n + k) (by omega)
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  calc |r (n + k)| * ((b : ℝ)⁻¹) ^ (k + 1)
      ≤ 1 * ((b : ℝ)⁻¹) ^ (k + 1) := mul_le_mul_of_nonneg_right hrk (by positivity)
    _ = ((b : ℝ)⁻¹) ^ (k + 1) := one_mul _

private lemma tendsto_bbpTail_zero {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ∑' k : ℕ, r (n + k) / (b : ℝ) ^ (k + 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb_sub : (1 : ℝ) ≤ (b : ℝ) - 1 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hgeom : HasSum (fun k : ℕ ↦ (ε / 2) * ((b : ℝ)⁻¹) ^ (k + 1)) ((ε / 2) * (b - 1 : ℝ)⁻¹) := by
    have h1 := hasSum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)
    have h2 : HasSum (fun k : ℕ ↦ ((b : ℝ)⁻¹) ^ (k + 1)) ((b : ℝ)⁻¹ * (1 - (b : ℝ)⁻¹)⁻¹) := by
      simpa only [pow_succ'] using h1.mul_left (b : ℝ)⁻¹
    have hval : (b : ℝ)⁻¹ * (1 - (b : ℝ)⁻¹)⁻¹ = (b - 1 : ℝ)⁻¹ := by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hb1' : (b : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [hval] at h2
    exact h2.mul_left (ε / 2)
  have hle : |∑' k : ℕ, r (n + k) / (b : ℝ) ^ (k + 1)| ≤ (ε / 2) * (b - 1 : ℝ)⁻¹ := by
    calc |∑' k : ℕ, r (n + k) / (b : ℝ) ^ (k + 1)|
        ≤ ∑' k : ℕ, |r (n + k) / (b : ℝ) ^ (k + 1)| :=
          norm_tsum_le_tsum_norm (summable_bbp_shift hb hr n).norm
      _ ≤ ∑' k : ℕ, (ε / 2) * ((b : ℝ)⁻¹) ^ (k + 1) := by
          refine Summable.tsum_le_tsum (fun k ↦ ?_) (summable_bbp_shift hb hr n).abs hgeom.summable
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) ^ (k + 1)),
            div_eq_mul_inv, ← inv_pow]
          have hrk : |r (n + k)| ≤ ε / 2 := by
            have := hN (n + k) (by omega)
            rw [Real.dist_eq, sub_zero] at this
            exact this.le
          exact mul_le_mul_of_nonneg_right hrk (by positivity)
      _ = (ε / 2) * (b - 1 : ℝ)⁻¹ := hgeom.tsum_eq
  have hinv : (b - 1 : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb_sub
  nlinarith

/-- Equidistribution modulo one is unchanged by perturbations that vanish modulo `ℤ`. -/
theorem isEquidistributedModOne_iff_of_tendsto_sub_int {u v ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, ∃ m : ℤ, u n = v n + ε n + m) :
    IsEquidistributedModOne u ↔ IsEquidistributedModOne v := by
  simp_rw [isEquidistributedModOne_iff_tendsto_weylSum]
  have hdiff : ∀ (h₀ : ℤ), Tendsto (fun N : ℕ ↦
      (∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * h₀ * u n)) / N -
      (∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * h₀ * v n)) / N) atTop (𝓝 0) := by
    intro h₀
    refine squeeze_zero_norm (a := fun N : ℕ ↦
      (∑ n ∈ Finset.range N, ‖Complex.exp (2 * π * Complex.I * h₀ * ε n) - 1‖) / N) ?_ ?_
    · intro N
      rw [← sub_div, norm_div, ← Finset.sum_sub_distrib, Complex.norm_natCast]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
      obtain ⟨m, hm⟩ := h n
      have hexp : Complex.exp (2 * π * Complex.I * h₀ * u n) =
          Complex.exp (2 * π * Complex.I * h₀ * v n) *
          Complex.exp (2 * π * Complex.I * h₀ * ε n) := by
        rw [hm, Complex.ofReal_add, Complex.ofReal_add, Complex.ofReal_intCast, mul_add, mul_add,
          Complex.exp_add, Complex.exp_add]
        have hint : Complex.exp (2 * π * Complex.I * h₀ * m) = 1 := by
          have : (2 * π * Complex.I * (h₀ : ℂ) * (m : ℂ)) =
              ((h₀ * m : ℤ) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
          rw [this, Complex.exp_int_mul_two_pi_mul_I]
        rw [hint, mul_one]
      rw [hexp, show Complex.exp (2 * π * Complex.I * h₀ * v n) *
            Complex.exp (2 * π * Complex.I * h₀ * ε n) -
            Complex.exp (2 * π * Complex.I * h₀ * v n) =
          Complex.exp (2 * π * Complex.I * h₀ * v n) *
            (Complex.exp (2 * π * Complex.I * h₀ * ε n) - 1) by ring, norm_mul]
      have hunit : ‖Complex.exp (2 * π * Complex.I * h₀ * v n)‖ = 1 := by
        have : (2 * π * Complex.I * (h₀ : ℂ) * (v n : ℂ)) =
            ((2 * π * (h₀ : ℝ) * v n : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [hunit, one_mul]
    · refine tendsto_cesaro_zero (fun n ↦ norm_nonneg _) ?_
      have hcont : Continuous fun t : ℝ ↦ ‖Complex.exp (2 * π * Complex.I * h₀ * t) - 1‖ := by
        fun_prop
      simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self,
        norm_zero] using (hcont.tendsto 0).comp hε
  constructor
  · intro hu h₀ hh₀
    have := (hu h₀ hh₀).sub (hdiff h₀)
    simpa only [sub_sub_cancel, sub_zero] using this
  · intro hv h₀ hh₀
    have := (hv h₀ hh₀).add (hdiff h₀)
    simpa only [add_sub_cancel, zero_add] using this

/-- Having a finite attractor modulo one is unchanged by perturbations vanishing modulo `ℤ`. -/
theorem hasFiniteAttractorModOne_iff_of_tendsto_sub_int {u v ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, ∃ m : ℤ, u n = v n + ε n + m) :
    HasFiniteAttractorModOne u ↔ HasFiniteAttractorModOne v := by
  have hdist : Tendsto (fun n ↦ dist (u n : UnitAddCircle) (v n : UnitAddCircle)) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) (by simpa using hε.abs)
    obtain ⟨m, hm⟩ := h n
    rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, hm,
      show v n + ε n + (m : ℝ) - v n = ε n + (m : ℤ) by ring,
      AddCircle.coe_add, coe_int_unitAddCircle, add_zero]
    exact norm_unitAddCircle_coe_le_abs (ε n)
  have hdir : ∀ {a b : ℕ → ℝ},
      Tendsto (fun n ↦ dist (a n : UnitAddCircle) (b n : UnitAddCircle)) atTop (𝓝 0) →
      HasFiniteAttractorModOne b → HasFiniteAttractorModOne a := by
    intro a b hab ⟨S, hS⟩
    refine ⟨S, fun δ hδ ↦ ?_⟩
    filter_upwards [hS (δ / 2) (half_pos hδ),
      hab.eventually (gt_mem_nhds (half_pos hδ))] with n ⟨s, hs, hns⟩ hnab
    exact ⟨s, hs, (dist_triangle _ _ _).trans_lt (by linarith)⟩
  exact ⟨hdir (by simpa only [dist_comm] using hdist), hdir hdist⟩

/-- Shadowing identity: `b ^ n * bbpSum b r` agrees with `bbpOrbit b r n` plus the tail
`∑' k, r (n + k) / b ^ (k + 1)` modulo `ℤ`. -/
theorem bbpOrbit_shadowing {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (n : ℕ) :
    ∃ m : ℤ, bbpSum b r * (b : ℝ) ^ n =
      bbpOrbit b r n + (∑' k : ℕ, r (n + k) / (b : ℝ) ^ (k + 1)) + m := by
  induction n with
  | zero => exact ⟨0, by simp [bbpSum, bbpOrbit]⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    have hsplit : ∑' k : ℕ, r (n + k) / (b : ℝ) ^ (k + 1) =
        r n / b + (∑' k : ℕ, r (n + 1 + k) / (b : ℝ) ^ (k + 1)) / b := by
      rw [(summable_bbp_shift hb hr n).tsum_eq_zero_add]
      simp only [add_zero, zero_add, pow_one, ← tsum_div_const]
      congr 1
      refine tsum_congr fun k ↦ ?_
      rw [div_div, ← pow_succ, show n + (k + 1) = n + 1 + k by omega]
    set M : ℤ := ⌊(b : ℝ) * bbpOrbit b r n + r n⌋
    refine ⟨M + b * m, ?_⟩
    have hstep : bbpSum b r * (b : ℝ) ^ (n + 1) = (b : ℝ) * (bbpSum b r * (b : ℝ) ^ n) := by
      rw [pow_succ]; ring
    rw [hstep, hm, hsplit]
    have hfract : (b : ℝ) * bbpOrbit b r n + r n = bbpOrbit b r (n + 1) + (M : ℝ) := by
      simp only [bbpOrbit, Int.fract, M]
      ring
    set T : ℝ := ∑' k : ℕ, r (n + 1 + k) / (b : ℝ) ^ (k + 1)
    have h1 : (b : ℝ) * (bbpOrbit b r n + (r n / b + T / b) + m) =
        ((b : ℝ) * bbpOrbit b r n + r n) + T + (b : ℝ) * m := by
      field_simp
      ring
    rw [h1, hfract]
    push_cast
    ring

/-- **Bailey–Crandall Theorem 1**: for `r n → 0`, the BBP constant `bbpSum b r` is normal in
base `b` if and only if its Bailey–Crandall orbit `bbpOrbit b r` is equidistributed modulo one. -/
theorem isNormalIn_bbpSum_iff_isEquidistributedModOne {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) :
    IsNormalIn b (bbpSum b r) ↔ IsEquidistributedModOne (bbpOrbit b r) := by
  rw [isNormalIn_iff_isEquidistributedModOne hb]
  exact isEquidistributedModOne_iff_of_tendsto_sub_int (tendsto_bbpTail_zero hb hr)
    (bbpOrbit_shadowing hb hr)

/-- **Bailey–Crandall / Lagarias finite-attractor theorem**: if `(x * b ^ n)` approaches a finite
subset of `UnitAddCircle`, then `x` is rational. -/
theorem not_hasFiniteAttractorModOne_mul_pow {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : Irrational x) :
    ¬ HasFiniteAttractorModOne (fun n ↦ x * (b : ℝ) ^ n) := by
  rintro ⟨S, hS⟩
  let y : ℕ → UnitAddCircle := fun n ↦ ((x * (b : ℝ) ^ n : ℝ) : UnitAddCircle)
  have hy_step : ∀ n, y (n + 1) = b • y n := fun n ↦ by
    simp only [y, ← AddCircle.coe_nsmul, nsmul_eq_mul, pow_succ]
    congr 1; ring
  let T : Finset (UnitAddCircle × UnitAddCircle) :=
    (S ×ˢ S).filter fun p ↦ b • p.1 ≠ p.2
  have hδ_exists : ∃ δ : ℝ, 0 < δ ∧ δ < (2 * (b : ℝ))⁻¹ ∧
      ∀ p ∈ T, ((b : ℝ) + 1) * δ < dist (b • p.1) p.2 := by
    by_cases hT : T.Nonempty
    · let m := T.inf' hT fun p ↦ dist (b • p.1) p.2
      have hm : 0 < m := by
        rw [Finset.lt_inf'_iff]
        intro p hp
        exact dist_pos.2 (Finset.mem_filter.1 hp).2
      refine ⟨min ((4 * (b : ℝ))⁻¹) (m / (2 * ((b : ℝ) + 1))), ?_, ?_, ?_⟩
      · exact lt_min (by positivity) (div_pos hm (by positivity))
      · refine (min_le_left _ _).trans_lt ?_
        have hb0 : (0 : ℝ) < b := by positivity
        field_simp
        norm_num
      · intro p hp
        have hpm : m ≤ dist (b • p.1) p.2 := Finset.inf'_le _ hp
        have h1 : ((b : ℝ) + 1) * min ((4 * (b : ℝ))⁻¹) (m / (2 * ((b : ℝ) + 1))) ≤
            ((b : ℝ) + 1) * (m / (2 * ((b : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        have h2 : ((b : ℝ) + 1) * (m / (2 * ((b : ℝ) + 1))) = m / 2 := by
          have : (b : ℝ) + 1 ≠ 0 := by positivity
          field_simp
        linarith
    · refine ⟨(4 * (b : ℝ))⁻¹, by positivity, ?_, fun p hp ↦ (hT ⟨p, hp⟩).elim⟩
      have hb0 : (0 : ℝ) < b := by positivity
      field_simp
      norm_num
  obtain ⟨δ, hδ₀, hδb, hδT⟩ := hδ_exists
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hS δ hδ₀)
  choose s hsS hsd using fun k : ℕ ↦ hN (N + k) (Nat.le_add_right N k)
  have hs_step : ∀ k : ℕ, b • s k = s (k + 1) := by
    intro k
    by_contra hne
    have hmem : (s k, s (k + 1)) ∈ T :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hsS k, hsS (k + 1)⟩, hne⟩
    have hdist_le : dist (b • s k) (s (k + 1)) < ((b : ℝ) + 1) * δ := by
      have h1 : dist (b • s k) (b • y (N + k)) ≤ (b : ℝ) * dist (s k) (y (N + k)) := by
        rw [dist_eq_norm, dist_eq_norm, ← smul_sub]
        exact norm_nsmul_le
      have h2 : dist (s k) (y (N + k)) < δ := by rw [dist_comm]; exact hsd k
      have h3 : dist (y (N + (k + 1))) (s (k + 1)) < δ := hsd (k + 1)
      have hyk : y (N + (k + 1)) = b • y (N + k) := by
        rw [show N + (k + 1) = (N + k) + 1 by omega, hy_step]
      calc dist (b • s k) (s (k + 1))
          ≤ dist (b • s k) (y (N + (k + 1))) + dist (y (N + (k + 1))) (s (k + 1)) :=
            dist_triangle _ _ _
        _ = dist (b • s k) (b • y (N + k)) + dist (y (N + (k + 1))) (s (k + 1)) := by
            rw [hyk]
        _ ≤ (b : ℝ) * dist (s k) (y (N + k)) + dist (y (N + (k + 1))) (s (k + 1)) := by
            linarith
        _ < (b : ℝ) * δ + δ := by nlinarith [show (0 : ℝ) < b by positivity]
        _ = ((b : ℝ) + 1) * δ := by ring
    exact not_lt_of_gt (hδT _ hmem) hdist_le
  have herr : ∀ k : ℕ, ‖y (N + k) - s k‖ = (b : ℝ) ^ k * ‖y N - s 0‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hek : ‖y (N + k) - s k‖ < (2 * (b : ℝ))⁻¹ := by
        rw [← dist_eq_norm]
        exact (hsd k).trans hδb
      have hstep : y (N + (k + 1)) - s (k + 1) = b • (y (N + k) - s k) := by
        rw [show N + (k + 1) = (N + k) + 1 by omega, hy_step, ← hs_step k, smul_sub]
      rw [hstep, norm_nsmul_unitAddCircle_eq (by omega) hek, ih, pow_succ]
      ring
  have he0 : ‖y N - s 0‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖y N - s 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (δ / ‖y N - s 0‖)
      (by exact_mod_cast hb : (1 : ℝ) < b)
    have hlt := hsd k
    rw [dist_eq_norm, herr k] at hlt
    have : δ < (b : ℝ) ^ k * ‖y N - s 0‖ := (div_lt_iff₀ hpos).1 hk
    linarith
  have hy_in_S : ∀ k : ℕ, y (N + k) ∈ S := fun k ↦ by
    have hk0 : ‖y (N + k) - s k‖ = 0 := by rw [herr k, he0, mul_zero]
    rw [sub_eq_zero.1 (norm_eq_zero.1 hk0)]
    exact hsS k
  let f : ℕ → S := fun k ↦ ⟨y (N + k), hy_in_S k⟩
  obtain ⟨i, j, hij, hfeq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hyeq : y (N + i) = y (N + j) := congrArg Subtype.val hfeq
  have hzero : ((x * (b : ℝ) ^ (N + i) - x * (b : ℝ) ^ (N + j) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact hyeq
  rw [AddCircle.coe_eq_zero_iff] at hzero
  obtain ⟨m, hm⟩ := hzero
  have hpow_ne : ((b : ℝ) ^ (N + i) - (b : ℝ) ^ (N + j)) ≠ 0 := by
    intro h0
    have hpow : (b : ℕ) ^ (N + i) = b ^ (N + j) := by
      have : ((b : ℝ) ^ (N + i)) = (b : ℝ) ^ (N + j) := sub_eq_zero.1 h0
      exact_mod_cast this
    exact hij (Nat.add_left_cancel (Nat.pow_right_injective hb hpow))
  have hrat : ((((m : ℚ) / (((b : ℚ) ^ (N + i) - (b : ℚ) ^ (N + j)))) : ℚ) : ℝ) = x := by
    push_cast
    rw [div_eq_iff hpow_ne]
    simp only [zsmul_eq_mul, mul_one] at hm
    linarith
  exact hx ⟨_, hrat⟩

/-- If `bbpSum b r` is irrational and `r n → 0`, its Bailey–Crandall orbit does not have a finite
attractor modulo one. -/
theorem not_hasFiniteAttractorModOne_bbpOrbit {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hirr : Irrational (bbpSum b r)) :
    ¬ HasFiniteAttractorModOne (bbpOrbit b r) := by
  rw [← hasFiniteAttractorModOne_iff_of_tendsto_sub_int (tendsto_bbpTail_zero hb hr)
    (bbpOrbit_shadowing hb hr)]
  exact not_hasFiniteAttractorModOne_mul_pow hb hirr

end Real
