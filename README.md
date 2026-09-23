# No bounded-orbit wandering domains

We prove that transcendental entire functions do not have bounded-orbit wandering domains.

This answers a major open question in the field. The proof builds upon Zihao Ye's new proof of Sullivan's No Wandering Domains theorem, and was obtained with assistance by generative AI, specifically ChatGPT 6 Astra. We also formalise a stronger theorem, which shows that locally defined holomorphic functions do not have wandering domains on which the iterates are univalent.

The formalisations are conditional on classical statements concerning the hyperbolic metrics of finitely punctured spheres which are well-known, but not yet formalised. Hence the theorems contain the existence of hyperbolic metrics on the corresponding punctures spheres as a hypothesis.

Start with **Challenge.lean**: both results are stated independently in about 180 lines with only Mathlib imports. **Solution.lean** and the accompanying modules contain the substantive formal development.

## Project layout

`Challenge.lean` and `Solution.lean` remain at the repository root.

The 55 supporting proof modules are under `BoundedWanderingDomains/`; `BoundedWanderingDomains.lean` imports that supporting development.

Supporting module paths have the prefix `BoundedWanderingDomains.`. Version 0.12 corrects the entire theorem to require only one bounded point orbit. Curvature remains −1.

The archive contains the full source tree, including its dependencies.

## Exact scope

Both theorems assume `ClassicalHyperbolicMetrics`: existence of curvature −1
metrics on finitely punctured planes with positivity, smoothness, the curvature
equation, sharp disc Schwarz inequality, extremal discs and classical total
area. This is an explicit hypothesis, not a new Lean axiom.
Area is divided by 2π.

1. **Local functions.** V is open with compact closure; f is analytic near its
   closure and has no constant germ there. Let T be the interior of the points
   whose iterates stay in V. The components U_n of T through f^n(z) cannot be
   pairwise disjoint if they are simply connected, all lie in one compact K
   contained in V, and satisfy eventual injectivity on each fixed intrinsic disc.
2. **Transcendental entire functions.** An orbit of actual Fatou components U_n
   cannot be pairwise disjoint if some z in U_0 has a bounded forward orbit:
   `Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))`.
   No bound on the union of the components is assumed. Simple connectivity of
   auxiliary trapped components and eventual injectivity on intrinsic discs
   are derived in the proof.

For every chart radius 0 < r < 1, there is a starting time N(r) after which f
is injective on the radius-r normalised Riemann-chart disc around f^n(z).
The curvature −1 intrinsic radius is 2 artanh(r). N may depend on r.
For the entire theorem these discs lie in auxiliary trapped components;
their eventual compact containment suffices for the area argument.

Simple connectivity and eventual disc injectivity are hypotheses only in
the local result.
The bounded-point-orbit theorem is proved subject to the explicit classical
metric hypothesis. The derived-singular-set statement is not included.

## Definitions and proof dependencies

Differentiability, analyticity, iteration, connected components, simple
connectivity, boundedness, integration and convergence use Mathlib definitions.
Transcendental entire is expressed as complex differentiability everywhere
and inequality to every complex polynomial.

Fatou components use normality of sphere-valued iterates, with sphere
`OnePoint ℂ` and its compact Hausdorff uniformity. No matching definitions
were found in the pinned Mathlib or supplied Tau Ceti sources, so the short
ComplexDynamics definitions are reproduced in the independent Challenge.
The Solution uses the supplied definitions. All nine public supporting
definitions are compared, including the uniform-space instance.

`PointOrbitBridge.lean` obtains a bounded neighbourhood from the bounded
point orbit using Schottky's estimate. `TrappedSimpleConnectivity.lean` and
the supplied planar topology theorem provide simply connected trapped
components inside the Fatou components. `LocalDiscInjectivity.lean` proves
the local inverse-branch argument on shrinking intrinsic discs.
`BoundedPointWandering.lean` joins these results to the uniform area
contradiction in `EventualCompactDiscs.lean`.

See `BOUNDED_POINT_PROOF.md` for the proof and its mapping to the Lean modules.
All four supplied dependencies remain included as real source directories,
with their licences and provenance. No new topology hypothesis or custom
axiom is introduced. See `NEXT_STEPS.md` for remaining metric obligations.

## Build and verify

With Lean 4.34.0, from the project root:

```sh
lake exe cache get
lake build Submission Challenge
python3 scripts/verify_submission.py
```

The default build target is the proved Solution development. Challenge has
exactly two intentional proof holes and is not imported by Solution.

The local verification compares exported elaborated declaration types and
definition bodies, and audits the final theorem axioms. It is not the official
Palomar Comparator or NanoDa. See VERIFICATION.md and PALOMAR_STATUS.md.
The current report is verification/submission.json.

## Submission and attribution

The package contains the metadata, Comparator configuration, pinned
dependencies and licences. Actual submission still needs a public repository
and its full commit SHA. No public submission has been made.

Mathematical direction: Lasse Rempe. AI-assisted formalisation: OpenAI
ChatGPT/Codex. The working argument was motivated by Zihao Ye's preprint
and the hyperbolic-density comparisons discussed with the author.
Precise sources and review limitations are in formalization.yaml.


## Licences and reused proofs

See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for the complete component
index, source authors, pinned revisions, adaptation records and links to all
included licences. Original upstream notices are retained. Run
`python3 scripts/audit_attribution.py` to check the packaged attribution material.
The packaging script also checks its presence and contents in the archive.
