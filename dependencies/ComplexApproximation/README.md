# ComplexApproximation

**Start here:** [Main results](MAIN_RESULTS.md) · [Exact Lean statements](ComplexApproximation/MainTheorems.lean) · [Proof map](PROOF_MAP.md) · [Classical results](CLASSICAL_RESULTS.md) · [Module index](docs/MODULE_INDEX.md)

Research version prepared for private review. See [PROVENANCE.md](PROVENANCE.md)
for development and review status.

A complex approximation library, currently containing a complete Lean 4
formalisation of Runge's approximation theorem against a pinned Mathlib
version, together with neighbourhood-holomorphic Arakelian approximation.
The development proves these results:

| Result | Lean theorem |
| --- | --- |
| Rational approximation on any compact set | `Runge.rational_approximation` |
| Approximation with prescribed poles | `Runge.prescribed_poles_approximation` |
| Polynomial approximation with connected complement | `Runge.polynomial_approximation` |
| Entire approximation on a closed Arakelian set, for neighbourhood-holomorphic data | `ComplexApproximation.arakelian_approximation` |
| Smooth compact-support Cauchy–Pompeiu formula | `ComplexApproximation.cauchyPompeiu_compact` |

Given a compact set `K`, an open neighbourhood `U`, and a function holomorphic on
`U`, the conclusions hold uniformly on `K` to every positive accuracy. In the
prescribed-pole form, the allowed set must meet every bounded connected component
of the complement. Every zero of the chosen denominator lies in that allowed
set, and the denominator is nonzero on `K`.

The main theorems use `AnalyticOnNhd ℂ f U`. Equivalent interfaces using the usual
`DifferentiableOn ℂ f U` hypothesis are provided in
[Runge/Holomorphic.lean](Runge/Holomorphic.lean), with names ending in
`_of_holomorphic`.

There are no proof placeholders or added axioms. All 160 selected audited results depend
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
The original target statements are checked against the completed proofs.

For the remaining Eremenko paper, the current neighbourhood-holomorphic
Arakelian theorem is the proposed approximation input to Section 5: choose
each approximation piece inside a domain where the model map is holomorphic,
with a buffer around the next compact set. This shrink and its margins still
need proof in that application. The full analysis is recorded in the sibling
EremenkosConjecture repository at `docs/FULL_PAPER_FEASIBILITY.md`.
The full continuous-data Arakelian theorem remains a separate stronger target.

## Read the proof

- [Arakelian approximation](ComplexApproximation/Arakelian.lean): filled-disk
  exhaustion, the Rosay–Rudin correction step, and an entire limit.
- [Cauchy–Pompeiu](ComplexApproximation/CauchyPompeiu.lean): rectangular Green
  integration, the exact normalization, and the Cauchy–Riemann solver.
- [Rational approximation](Runge/RationalApproximation.lean): smooth cutoffs,
  Cauchy–Green integration, and uniform rational closure.
- [Prescribed poles and polynomials](Runge/PrescribedPoles.lean): propagation
  through complement components, polynomial expansions at distant poles, and
  factorisation of denominators.
- [Proof architecture](docs/PROOF_PLAN.md): the mathematical argument and its
  correspondence with the Lean modules.
- [Verification record](STATUS.md): completed checks and pinned environment.
- [Axiom audit](verification/axioms.log): the dependency reports.

## Reproduce the checks

Lean **4.34.0** and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` are pinned in the project.

Keep the sibling `FunctionTheory` directory beside this project.
From this directory, with Lean/Elan installed:

```text
lake exe cache get
lake build
lake env lean scripts/Audit.lean
lake build RungeTargets
```

All commands must succeed. Neither library should report a proof placeholder.
Import `Runge` to use the results.

On Windows, `scripts/verify.ps1` runs these checks, rejects unexpected axioms and
forbidden proof constructs, and saves logs under `verification/`. Its optional
`-LeanBin` argument selects an installed toolchain's `bin` directory.

The [source register](docs/SOURCES.md) records the prior-art search, including
EPFL's Jordan curve reformalization project and other theorem provers. This
project makes no claim to be the first formalisation in any prover.

## Functions with their actual domain

`Runge.LocalDomain` provides all three approximation results for `f : U → ℂ`,
with `IsHolomorphicFunctionOn U f`, and for `f : K → ℂ`, with
`HasHolomorphicExtension K f`. Their names end in `_on_domain` and `_on_compact`.
The latter states the usual neighbourhood-extension hypothesis for a function
on a compact set. Values outside the given domain are not inputs.

Local representatives connect these interfaces to Mathlib calculus. An arbitrary
extension is used internally, where its values outside the domain do not matter.
The original public challenge statements remain available unchanged.

## Project name and future scope

This project was previously named Runge. The Lake package is now
`complexApproximation` and `import ComplexApproximation` is available.
Existing `import Runge`, `import Runge.LocalDomain`, and `Runge.*` theorem
names remain valid. Neighbourhood-holomorphic Arakelian approximation is now proved.

Run `python scripts/verify.py` for the portable build and audit. Apache 2.0;
see `LICENSE`, `PROVENANCE.md`, and `CONTRIBUTING.md`. `ROADMAP.md` separates
future mathematics from preparation for eventual Mathlib contributions.

## Classical function theory

Riemann mapping, reflection and kernel convergence now belong to the sibling
[FunctionTheory project](../FunctionTheory/README.md). Its attributed public
proofs retain their upstream statements and names. Existing
`ComplexApproximation.Conformal.*` modules remain as compatibility wrappers.
