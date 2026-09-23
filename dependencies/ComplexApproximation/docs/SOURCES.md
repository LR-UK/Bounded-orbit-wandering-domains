# Sources and search policy

Search date: 16 September 2026. Search findings are not proofs of nonexistence.
These findings record the prior-art search preceding this project's completed
Lean development; they are not a claim of priority.

## Formalisation sources to check

- Mathlib source and documentation: https://github.com/leanprover-community/mathlib4
- Lean public benchmarks: https://lean-lang.org/eval/problems/runge_theorem/
- Math-Challenge: https://www.math-challenge.org/en/projects/runge_theorem
- EPFL reformalization project: https://github.com/epfl-lara/jordan-curve-theorem
- EPFL paper: https://arxiv.org/abs/2607.01734
- HOL Light: https://github.com/jrh13/hol-light
- Isabelle/HOL and Archive of Formal Proofs: https://www.isa-afp.org/
- Rocq/Coq, Mizar Mathematical Library, and Metamath.
- Cross-prover index: https://1000-plus.github.io/
- Public Lean repositories and Lean community discussion archives.

The user explicitly requests inclusion of the Swiss translation project and
other theorem provers. The project identified from the Jordan curve theorem
clue is at EPFL, Lausanne; it was initially recalled as being in Zurich.

## Findings relevant to this project

- The public Runge benchmark states rational approximation and has a placeholder
  proof. The statement does not impose a prescribed set of poles.
- The pinned Mathlib v4.34.0 source has no matches for Runge or Mergelyan.
- A prior direct search of the official HOL Light source archive found no
  `RUNGE`, `MERGELYAN`, `COMPLEX_APPROXIMATION`, or
  `HOLOMORPHIC_POLYNOMIAL_APPROXIMATION`. This refutes the specific identifiers
  suggested by Google AI; it does not rule out all external developments.
- EPFL's paper reports reformalizations of the Jordan curve theorem. No Runge
  proof has been located in that project.
- https://zenodo.org/records/21925332 reports Lean-verified pole-pushing lemmas.
  Its associated code was not obtained or independently checked in the search;
  it is not used as a trusted dependency here. This project's pole-shift proofs
  are developed directly in Lean against the pinned Mathlib.

## Mathlib infrastructure

- `Mathlib.Analysis.Complex.CauchyIntegral`: Cauchy-Goursat on rectangles,
  Cauchy formulas on circles, analyticity, and power series.
- `Mathlib.MeasureTheory.Integral.CircleIntegral`: parameterised circle integrals.
- `Mathlib.Analysis.SpecificLimits.Basic`: decay of geometric powers.
- `Mathlib.Analysis.Complex.Polynomial.Basic`: the fundamental theorem of algebra.
- `Mathlib.Geometry.Manifold.PartitionOfUnity`: smooth cutoffs.
- `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`: integration in
  spaces of continuous functions.

Dependency version: Lean 4.34.0; Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` (tag `v4.34.0`).
