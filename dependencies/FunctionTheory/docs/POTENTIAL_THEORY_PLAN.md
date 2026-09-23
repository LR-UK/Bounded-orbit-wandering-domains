# Future classical analysis for the Eremenko paper

Planning record, 18 September 2026; **none of the new results below is claimed
as proved**. The completed application is Theorem 1.2. Further proof work is
paused while the four private repositories are shared and reviewed.

The detailed dependency analysis is in the sibling EremenkosConjecture
repository, `docs/FULL_PAPER_FEASIBILITY.md`, with search evidence in
`docs/FULL_PAPER_SOURCE_AUDIT.md`. Keep classical analysis here, approximation
in ComplexApproximation, and orbit/Fatou arguments in ComplexDynamics.

## First bounded task: finite logarithmic interpolation

Prove a reusable global-injectivity criterion for a holomorphic map on a convex
domain with strictly positive real part of its derivative, using integration
on a segment. Apply it, after rotation, to the finite logarithmic sum in the
second proof of Proposition 9.1. Prove its boundary limits and compose with
an explicitly normalized strip-to-half-strip map. Derive the finite version
of Proposition 5.6 by contraction inside the disc. No logarithmic capacity,
Evans theorem or Bishop theorem is needed for this first task.

For Lemma 5.4, first try the existing bounded inverse-Montel machinery and the
open mapping theorem, as detailed in the application plan. Disc hyperbolic
distance is present in the pinned Tau Ceti source; general boundary-density
estimates were not located. Do not infer Koebe's quarter theorem from the
filename of the Riemann-mapping construction.

## Harmonic measure

Mathlib's harmonic Poisson representations and kernel bounds are useful
starting points. No general rough-boundary harmonic-measure API was located
in the searched sources. Choose a standard construction and establish the
properties needed by Lemma 8.2: measurable boundary sets, basepoint-independent
null sets, domain comparison and holomorphic pullback. A radial-limit and
pushforward approach requires an almost-everywhere boundary-limit theorem;
a Perron approach requires its own existence and comparison theory.

Aim first at the exact simply connected domain estimate in Lemma 8.2. The
application's multiply connected wandering case belongs in ComplexDynamics.
General Brownian motion and Makarov's theorem are not proposed prerequisites.
Any replacement for Makarov in the dimension conclusion of 1.14 must still
prove the lower bound, not only containment in a smooth curve.

## Logarithmic capacity and Evans

Before implementation, read Garnett–Marshall Appendix E and decompose the
Evans proof. That full proof has not yet been audited in this project.
Use a standard logarithmic-energy/capacity definition, extended values at the
diagonal, compactly supported probability measures and the necessary limiting
arguments. Obtain the pointwise divergence at every point of a compact
capacity-zero set; almost-everywhere divergence is too weak here.

Then generalize the finite sum to a logarithmic integral, justifying
differentiation under the integral away from the support. This should supply
full Proposition 9.1, full Proposition 5.6, and the capacity input to Theorem
1.13. The elementary finite proof remains useful as an earlier standalone
result and a check on signs and normalizations.

Check new public sources before undertaking these developments, including
Mathlib, Tau Ceti, other provers and EPFL's reformalization project. Preserve
source attribution and exact statements. A mathematical plan is not a Lean
dependency and must never be encoded as an added axiom.
