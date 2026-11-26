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
