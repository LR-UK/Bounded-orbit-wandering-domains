# Conditional absence of bounded wandering component orbits

Start with **Challenge.lean**: both results are stated independently in about
170 lines with only Mathlib imports. **Solution.lean** and the accompanying
modules contain the substantive formal development.

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
   cannot be pairwise disjoint if their union is bounded, they are simply
   connected, and the same eventual disc-injectivity condition holds.

For every chart radius 0 < r < 1, there is a starting time N(r) after which f
is injective on the radius-r normalised Riemann-chart disc around f^n(z).
The curvature −1 intrinsic radius is 2 artanh(r). N may depend on r.
The bound is uniform on the whole union of components, stronger than a
separate bound on each point orbit.

Simple connectivity and eventual disc injectivity remain hypotheses.
The unrestricted bounded-orbit conjecture and the derived-singular-set
statement are not claimed.

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

EntireFatouBridge.lean proves the identification of bounded Fatou-component
orbits with local trapped-component orbits. This bridge is not assumed.
Tau Ceti analytic foundations are reused through FunctionTheory where needed.
Both supplied dependencies are included as real source directories, with
licences and provenance. Challenge imports neither proof repository.

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

