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
* Authors: the Tau Ceti contributors.

## `NormalNumbers/`

* Source: [gotrevor/normal-numbers](https://github.com/gotrevor/normal-numbers), Apache 2.0,
  by Trevor Morris (`src/NormalNumbers/`).
* Imported: the closure (8 files) of `NormalNumbers.Pillai` (**Pillai's theorem**: simple
  normality in every base `b ^ r` implies normality in base `b`).
* Porting changes: the files are made into modules, `import Mathlib` is replaced by explicit
  imports, and three lemmas renamed upstream are restored (`List.getD_eq_getElem` as a local
  compatibility lemma, `tendsto_finsetSum`, a `positivity` call made explicit).

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
