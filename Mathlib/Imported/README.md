# Imported proofs

This folder holds proofs imported verbatim from other open-source Lean projects, so that the
normal-numbers development (`Mathlib/NumberTheory/Normal`) can reuse them instead of re-proving
them. Only module paths are rewritten (`TauCeti.X` becomes `Mathlib.Imported.TauCeti.X`); the
mathematics, namespaces and authorship are unchanged. Each subfolder records its source.

## `TauCeti/`

* Source: [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti), Apache 2.0,
  commit `4c5271c85dc84632e51fe333182fc9425688109e` (head of
  [pull request #43206](https://github.com/TauCetiProject/TauCeti/pull/43206), which adds the
  equidistribution files on top of `main`).
* Imported: the transitive closure (251 files) of
  * `TauCeti.NumberTheory.DiophantineApproximation.Roth.Theorem` (**Roth's theorem**),
  * `TauCeti.Probability.Ergodic.PointwiseErgodic` (**Birkhoff's pointwise ergodic theorem**),
  * `TauCeti.NumberTheory.Equidistribution.Polynomial` (**Weyl's criterion**, van der Corput's
    inequality and difference theorem, Weyl's polynomial equidistribution theorem).
* Also imported from `main` at commit
  [`3f8fe7e39a6021d79ff29476fca5b92b73861bf2`](https://github.com/TauCetiProject/TauCeti/tree/3f8fe7e39a6021d79ff29476fca5b92b73861bf2):
  the closure (16 new files; the 4 shared files are unchanged) of
  * `TauCeti.NumberTheory.CircleMethod.TypeISum` (the **type I bound**
    `∑_{m ≤ M} min(X / m, 1 / ‖mα‖) ≤ 16 (X / q + M + q) log (2Mq)`,
    `TauCeti.sum_min_inv_distInt_le`, the circle-method input to Weyl's inequality),
  * `TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds` (the **divisor bound**
    `d(n) ≪_ε n ^ ε`, `exists_pos_card_divisors_le_rpow`).
  These need no porting changes.
* Authors: the Tau Ceti contributors.

## `MathlibForks/`

Proofs found on branches of mathlib4 forks (not in upstream Mathlib), by the fork scan in
`scripts/fork_scan/`. All forks are of mathlib4 and so Apache 2.0. One subfolder per fork owner.
New files are copied verbatim; lemmas that the fork appends to an existing Mathlib file are moved
into a new file with the same namespace, `variable`s and `open`s.

| Subfolder | Source (branch, commit) | Content |
|---|---|---|
| `Mycaule/DigitsPeriodic` | [mycaule/mathlib4](https://github.com/mycaule/mathlib4/tree/fb2ddae6255b24bd385bb9572fd34ea68c356d4e) `feat/digits-eventually-periodic` | `Real.exists_ratCast_eq_iff_digits_eventually_periodic` (rational ⟺ eventually periodic `Real.digits`), `Real.digits_fract`, `Nat.mul_div_mod_eq_mod_mul_div` |
| `Kratostau/ConvergentLowerBound` | [Kratostau/mathlib4](https://github.com/Kratostau/mathlib4/tree/f64e6951e30882d0a47f6d4e8ac70f51dcf1c99b) `grok/one-div-lt-abs-sub-convs` | `GenContFract.one_div_lt_abs_sub_convs`: `1 / (Bₙ (Bₙ₊₁ + Bₙ)) < |v − Aₙ/Bₙ|` |
| `Localecho/IrrationalLiouvilleWith` | [localecho/mathlib4](https://github.com/localecho/mathlib4/tree/1a854568082fc8245baf6ac28fd360bbe8596e6a) `liouville-with-gap` | `Irrational.liouvilleWith`: irrational ⇒ `LiouvilleWith p` for `p ≤ 2` |
| `Kac3pro/GaussMap` | [kac3pro/mathlib4](https://github.com/kac3pro/mathlib4/tree/a239f9d58ba1d643b8f6c4237cf8db83a1246145) `gauss` | the Gauss map `x ↦ fract x⁻¹` and the Gauss measure |
| `BigOHunter/TrapezoidalRulePeriodic` | [BigO-Hunter/mathlib4-1](https://github.com/BigO-Hunter/mathlib4-1/tree/2b0a62c6f14f787528f88c97addd54d26f0444b2) `periodic-trap-char` | `PeriodicTrapezoidal.char_sum`: `∑_{j<n} e(mj/n) = n·[n ∣ m]`, exactness of the periodic trapezoidal rule on characters |
| `DavidFox998/Poussin` | [DavidFox998/mathlib4](https://github.com/DavidFox998/mathlib4/tree/5ce5b0e3d5bc8ee726f9c67c66c1add5a3f78946) `poussin-inequality` | `Real.three_add_four_mul_cos_add_cos_two_mul_nonneg` |
| `GoldenPhysicsProject/GaussSumModulus` | [GoldenPhysicsProject/mathlib4](https://github.com/GoldenPhysicsProject/mathlib4/tree/b6cc2b1509865939ddb4222ef4090dc0626e13ba) `gauss-sum-modulus` | `gaussSum_norm_eq_sqrt_card`: a quadratic Gauss sum has modulus `√q` |
| `JWhite/FourierEval` | [j-white/mathlib4](https://github.com/j-white/mathlib4/tree/136285cf266c8572f929751d4d7ddb05064d17e5) `fourier-eval-add` | `AddCircle.fourier_eval_add`/`_neg`/`_sub` (the branch's `fourier_sub` is upstream now) |

Authors are as in each file's header. No porting changes were needed; every file builds against
this branch's Mathlib.

## `NormalNumbers/`

* Source: [gotrevor/normal-numbers](https://github.com/gotrevor/normal-numbers), Apache 2.0,
  by Trevor Morris (`src/NormalNumbers/`).
* Imported: the closure (8 files) of `NormalNumbers.Pillai` (**Pillai's theorem**: simple
  normality in every base `b ^ r` implies normality in base `b`).
* Porting changes: the files are made into modules, `import Mathlib` is replaced by explicit
  imports, and three lemmas renamed upstream are restored (`List.getD_eq_getElem` as a local
  compatibility lemma, `tendsto_finsetSum`, a `positivity` call made explicit).
* Also imported, from commit
  [`6260625c6836d8bb172da4b011e089f63a728c41`](https://github.com/gotrevor/normal-numbers/tree/6260625c6836d8bb172da4b011e089f63a728c41):
  the closure (15 files, 11 new; the 4 shared files are unchanged) of
  `NormalNumbers.ComputableNormalB` (**a computable absolutely normal number**,
  `NormalNumbers.ComputableNormalB.exists_computable_absNormal`: for a coin-driven real `G` with
  polynomial Fourier decay there is a computable coin sequence `e` with `G e` normal in every
  base; by derandomisation with conditional expectations, after Becher–Figueira). It depends only
  on `propext`, `Classical.choice` and `Quot.sound`. Porting changes: the removed
  `PMF.uniformOfFintype` coin is replaced by `Measure.uniformOfFinset univ` (`Derandomize.coin`,
  with its probability instance), the deprecated root-namespace Fourier names become their
  `AddCircle.` versions, `List.getD_eq_getElem` is restated locally, one `convert` step is
  replaced by an explicit emptiness proof, and missing imports are added.
* Also imported, from the same commit: the closure (146 files, 131 new) of
  `NormalNumbers.CantorLiouvilleAll` (**a computable Liouville number in the middle-third Cantor
  set that is normal to every base not a power of 3**,
  `NormalNumbers.CantorLiouvilleAll.exists_computable_liouville_mem_cantorSet_normalProfile`,
  towards Bugeaud's Problem 10.37; the companion `NormalNumbers.CantorLiouville` handles base 2).
  The headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Three
  files in the closure contain `sorry`d side lemmas that the headline theorem does not use:
  `ExplicitSquareNonNormal`, `G4EntropyE0Down` and `LevinSparse`. Porting changes: the same coin
  replacement as above (`CantorSelfSimilar`, `LevinSparse`), `padicValNat` is replaced by
  `multiplicity` (Mathlib's `padicValNat` API is deprecated in favour of it, e.g.
  `Nat.multiplicity_pow_sub_pow` for lifting the exponent), `Finset.prod_le_prod` and
  `prod_le_one` become their `₀` versions, `measurable_pi_lambda` becomes `measurable_pi_iff.2`,
  `*_finset_sum` becomes `*_finsetSum`, a few `norm_num` and `convert` steps are re-closed, one
  `Computable.comp` gets explicit arguments, and missing imports are added.
* Also imported, from the same commit: `NormalNumbers.CantorCylinders` (the depth-`m` cylinder
  decomposition `pushFourier_cylinders` of the quarter-Cantor Fourier transform), made into a module
  like the files above. It is the first step of
  `Mathlib/NumberTheory/Normal/QuarterCantorDecay.lean`, which proves Kaufman-type polynomial
  decay and so discharges the `√` case of the cited `ExplicitSquare.BakerBanajiQuarterCantor`
  (`NormalNumbers.QuarterCantorDecay.polyDecay_sqrt`).

## Porting changes to `TauCeti/`

The Mathlib used here is newer than Tau Ceti's, so a few proofs were adjusted: the deprecated
root-namespace Fourier names (`fourier`, `fourierCoeff`, …) are replaced by their `AddCircle.`
versions, `universe u v w` is declared where Tau Ceti relied on auto-bound universes, two missing
imports are added (`Mathlib.Data.Pi.Interval`, `Mathlib.RingTheory.MvPolynomial.Tower`),
`AlgEquiv.ofRingEquiv` is replaced by `AlgEquiv.ofCommutes`, and two one-line proofs are
re-closed by `simp`.

## `SubspaceTheorems/`

* Source: [rwst/Subspace-Theorems](https://github.com/rwst/Subspace-Theorems), Apache 2.0,
  by Ralf Stephan, commit
  [`2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d`](https://github.com/rwst/Subspace-Theorems/tree/2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d).
* Imported: the transitive closure (145 files: 47 from `ArithmeticHeights/`, 98 from
  `DiophantineApproximation/`) of `DiophantineApproximation.ComplexityTranscendence`
  (**Adamczewski–Bugeaud 2007, Theorem 1**: if `ξ = ∑ aₖ b^-(k+1)` is an algebraic irrational,
  then the factor complexity `p(n)` of its base-`b` digits satisfies `p(n) / n → ∞`;
  `Real.tendsto_complexity_div_atTop`). The closure includes Roth's and Ridout's theorems and the
  Schmidt Subspace Theorem with their height and geometry-of-numbers machinery. The headline
  theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
* Authors: Ralf Stephan.

## Porting changes to `SubspaceTheorems/`

The source is on Lean `v4.35.0-rc3` with an older Mathlib. Module paths
(`ArithmeticHeights.X`, `DiophantineApproximation.X`) become `Mathlib.Imported.SubspaceTheorems.…`,
each file disables Mathlib's numeric-projection linter (`.1`/`.2`), which the source does not
run, and the following proofs are adjusted for the newer Mathlib:

* `AbsoluteValue.Completion` is now a one-field structure: `PlacesOverInfinite` goes through
  `AbsoluteValue.Completion.ofCompletion`, `Completion.map` and `Completion.isometry_map`, and
  `LocalExtension` installs `AbsoluteValue.Completion.algebraOfLiesOver` before
  `inertiaDeg_eq_finrank`.
* `Polynomial`/`MvPolynomial` coefficients are `AddMonoidAlgebra.coeff`: `coeff_smul` becomes
  `AddMonoidAlgebra.coeff_smul_apply`, and `Polynomial.coeff p n` becomes `p.coeff n`.
* `Matrix.rank` is no longer definitionally `finrank` of the range: rewrites go through
  `Matrix.finrank_range_mulVecLin` and `Matrix.finrank_span_range_row`.
* `AlgHom` gained a `map_smul'` field, so an anonymous constructor becomes a structure instance;
  `FinitePlace.hasFiniteMulSupport_fun_pow_multiplicity` lost its nonzero hypothesis;
  `Set.powersetCard.nontrivial_iff` is stated with `ENat.card`.
* Mathlib now has `ENNReal.geom_mean_le_arith_mean2_weighted` (with `ℝ≥0` weights), so the
  source's real-weight version is renamed `ENNReal.geom_mean_le_arith_mean2_weighted'`.
* Three definitions are marked `noncomputable`, four imports are added or replaced
  (`Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace`, `Mathlib.Data.Fin.Tuple.Sort`,
  `Mathlib.LinearAlgebra.Dimension.Torsion.Basic`, and the split
  `Mathlib.RingTheory.DedekindDomain.AdicValuation.*`), three lambdas whose binder type is no longer
  inferred become tactic blocks, and deprecated lemma names are replaced by their successors.

### Shared declarations with `TauCeti/`

Subspace-Theorems follows Tau Ceti's conventions and overlaps with it: 154 declarations have the
same name in both closures, so the two could not be imported together. The overlapping
declarations are deleted from `SubspaceTheorems/` and its files import the corresponding
`TauCeti/` modules instead (heights of tuples, affine heights, polynomial and `Finsupp` heights,
the box monomials and Hasse derivatives of `MvPolynomial`, generalized Wronskians, `S`-integers,
finite places, `AbsoluteValue.nonarchRpow`, `LiouvilleWith.inv`). Call sites are adapted to Tau
Ceti's argument order and to its unexposed definitions (`mulHeight_eq_finsupp`,
`mulHeightAff_def`, `hasseDerivRow_def`, `genWronskian_def` instead of unfolding).

Where Tau Ceti's statement is a different result rather than the same one, the Subspace-Theorems
version is kept under a new name:

| Source name | Kept as | Tau Ceti's declaration of the source name |
| --- | --- | --- |
| `MvPolynomial.hasseDeriv_comp` (applied) | `MvPolynomial.hasseDeriv_comp_apply` | the law for the linear maps |
| `MvPolynomial.coeff_taylor` | `MvPolynomial.coeff_aeval_C_X_add_X` | the expansion at a point |
| `Polynomial.mulHeight_mul_le`, `logHeight_mul_le` | `…_mul_le_two_pow` | constant `min (deg p) (deg q) + 1` |
| `Height.exists_logHeight_le_mul_logHeight₁_div` | `Height.exists_logHeight_le_card_erase_mul_logHeight₁_div` | both indices vary |
| `Set.unitValuation` | `Set.unitAddValuation` | multiplicative, over any Dedekind domain |
| `Set.unit_fg` | `Set.unit_fg_of_finite` | reduces to `S = ∅` |

`MvPolynomial.hasseDerivRow_eq_prod_mul` records the source's definition of `hasseDerivRow`.

## `FormalConjectures/`

* Source: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
  Apache 2.0, commit
  [`9097e2f90e66d2f6244209cb1c07f7120d17ec53`](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53)
  (`FormalConjecturesForMathlib/`).
* Imported: four definition files, with their proofs, so that the project's statements can be
  compared with ours:
  * `NumberTheory/NormalNumber.lean` (`NormalNumber.digitSeq`, `IsSimplyNormalInBase`,
    `IsNormalInBase`, `IsAbsolutelyNormal`, `IsRichInBase`), the definitions used by its
    statement of **Borel's conjecture** (`FormalConjectures/Wikipedia/AlgebraicNormality.lean`),
  * `Analysis/Equidistribution/ModOne.lean` (`IsEquidistributedModuloOne`, with closed intervals),
  * `Dynamics/SymbolicDynamics/BlockComplexity.lean` (`SymbolicDynamics.blockComplexity`,
    `blockEntropy`),
  * `NumberTheory/ExpansionEntropy.lean` (normal numbers have full block complexity and entropy).
* Porting changes: only module paths (`FormalConjecturesForMathlib.X` becomes
  `Mathlib.Imported.FormalConjectures.X`).
* Authors: the Formal Conjectures authors.
* Bridges: `Mathlib/NumberTheory/Normal/FormalConjectures.lean` proves that each definition agrees
  with ours (`Real.isNormalInBase_iff_isNormalIn`, `Real.isEquidistributedModuloOne_iff`, …), which
  proves the project's `sorry`d statement of Wall's theorem
  (`Real.isNormalInBase_iff_isEquidistributedModuloOne`).
  `Mathlib/NumberTheory/Normal/FormalConjecturesComplexity.lean` identifies `blockComplexity`
  with Subspace-Theorems' `Function.complexity` and restates Adamczewski–Bugeaud in its terms.
