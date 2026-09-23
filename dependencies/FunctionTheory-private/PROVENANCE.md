# Provenance and review status

This project was separated from ComplexApproximation on 17 September 2026 at
Lasse Rempe's request, to collect reusable classical complex analysis alongside
the separate ComplexDynamics library. It is a research development prepared
for review, not a Mathlib contribution already accepted upstream.

The Riemann mapping theorem was **reused**, not re-proved independently. The
selected source is [Tau Ceti](https://github.com/TauCetiProject/TauCeti), commit
`f441315d5d3c9ccc377a691d7a7da00613010718`. The 138 selected modules
include 137 identical copies after line-ending normalization. One newly
included measure-theory dependency, `LIntegralRpow.lean`, needs measurability
compatibility changes for our Mathlib version: two auxiliary declarations
gain explicit measurability assumptions, while its Fatou and Hölder theorem
statements remain unchanged. See the exact [compatibility record](third_party/TauCeti/COMPATIBILITY.md).
The headline Riemann mapping, Schwarz reflection, and Carathéodory statements
and proofs are unchanged. The upstream toolchain was Lean 4.34.0-rc2;
the selected sources compile with our pinned Lean 4.34.0 and Mathlib revision. See the [manifest](third_party/TauCeti/UPSTREAM.json).

The actual-domain interface, kernel limits, inverse estimates, bounded kernel
convergence, and halfplane local bounds are additional Lean development made
with automated assistance in this project. Their dependencies are checked by
Lean. Mathematical review of statement scope, usefulness, style, and suitability
for upstream contribution remains valuable and distinct from kernel checking.

Statement alignment follows the public source directly: use its `TauCeti.*`
declarations, add wrappers only for a useful alternative interface, and retain
the exact upstream assumptions. The subtype-domain formulation coexists with
the ambient-map formulation. The original `ComplexApproximation.*` names are
maintained as compatibility aliases in that sibling project.

Prior-art searches should continue to include other proof assistants and the
Swiss [EPFL reformalization project](https://github.com/epfl-lara/jordan-curve-theorem)
(initially recalled as a Zurich project). This repository makes no priority claim.

## Further public boundary results inspected

At the same pinned Tau Ceti revision,
[`Conformal/Caratheodory.lean`](https://github.com/TauCetiProject/TauCeti/blob/f441315d5d3c9ccc377a691d7a7da00613010718/TauCeti/Analysis/Complex/Conformal/Caratheodory.lean)
proves continuous extension of a conformal disk map onto a bounded Jordan
domain. It does **not** claim injectivity of the boundary extension.
`Reflection/Injective.lean` proves conformality of a reflected map with
injectivity on the closed initial half and the halfplane mapping property
as explicit hypotheses. Carathéodory and its dependency closure are now included and checked.
The separate `Reflection/Injective.lean` module is not imported.

The additional `ReflectionInjectivity` development uses the reused reflection
principle and Mathlib's open mapping theorem to prove boundary injectivity
from injectivity on the open half. It does not import the separate public
`Reflection/Injective.lean` theorem with its closed-half injectivity hypothesis.
This distinction is recorded to keep the two statement scopes clear.

Our boundary-normalization, Cayley coordinates, straight-boundary reflection
and inverse, and geometric strip-map construction are additional development.
The Jordan-curve hypothesis on the exponential image remains explicit;
these results do not assert existence of the decorated domains in Theorem 1.2.
The source-integrity scanner ignores nested Lean comments while retaining
code and strings, and kernel axiom reports check the selected proof dependencies.

## Inverse boundary clusters and monotone extensions

Five further modules from the same pinned source are included unchanged:
`ArcConstancy`, `Inverse/BoundaryCluster`, `MonotoneExtension`,
`Removability/Circle`, and `Topology/JordanCurve/Monotone`.
The public boundary-injectivity theorem explicitly assumes preconnected
approach regions in the image. Our relative-chart lemma helps the application
prove that hypothesis from the public Schoenflies chart of a Jordan interior.

The imported inverse-boundary-cluster file attributes its source to D. Cureton's
[sphere-six-complex](https://github.com/deancureton/sphere-six-complex), revision
`895c0a0`, under Apache 2.0. Those attribution and reference comments are retained.
The resulting full Jordan-domain Carathéodory theorem is currently in the
application, where the Schoenflies dependency is available. It is a candidate
for later extraction into this classical-analysis library.

## Vitali and circle reflection

Four further pinned modules are imported unchanged: `Conformal/Vitali` and
`Conformal/Reflection/Circle/{Basic,Conjugate,Principle}`. The original public
statements and proofs are retained and the Vitali and circle-reflection
principle declarations are audited. There are now 138 attributed modules,
137 identical after line-ending normalization, with the same single port.

The image-disk estimate, univalent outer-annulus bound, reflected-family bound,
symmetric circle collars, and shared-arc boundary-convergence theorem are
additional development. The uniform-boundary argument uses these public
analytic foundations and Mathlib's identity theorem.

## The Riemann sphere

The two-chart complex-manifold structure on `OnePoint ℂ` is adapted from
[Geoffrey Irving's Ray project](https://github.com/girving/ray/blob/753f7131cf96f4651294de4398368abf136c34de/Ray/Manifold/RiemannSphere.lean),
at commit `753f7131cf96f4651294de4398368abf136c34de`, under Apache 2.0.
The retained public definitions and statements follow the original. Imports
and reciprocal-limit helper proofs were adapted to our pinned Mathlib.
The atlas and its complex-manifold instance compile and have been audited.
See the [source record](third_party/Ray/README.md) and
[manifest](third_party/Ray/UPSTREAM.json). The chart and inversion holomorphy proofs in `RiemannSphere/Coordinates`
also adapt Ray's public proofs, using Mathlib's direct chart criterion.
Translation and the arbitrary omitted-point coordinate are additional
project development. The sphere-domain Riemann mapping theorem is then
derived from this coordinate and the unchanged public Tau Ceti plane theorem;
no separate uniformization theorem is assumed.

## Shared smooth cutoffs — 21 September 2026

The two proofs previously in ComplexApproximation/Runge/SmoothCutoff.lean
were moved without mathematical changes to FunctionTheory/Smooth/Cutoff.lean.
The old Runge imports and declaration names remain available through
compatibility exports. This is a move of existing project development,
not an additional independent formalisation of the same theorem.
