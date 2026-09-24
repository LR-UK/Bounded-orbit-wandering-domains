# Riemann-surface extension — research branch

## Stable version

The verified version 1.3.0 is preserved at
`4a2c4b75c71541f569b7ae34bde616bcca66c07a`:

- Stable branch: `stable-v1.3.0`.
- Annotated release tag: `v1.3.0`.
- Original prepared branch: `formalise-spherical-singular-limits-recovered`.
- GitHub update archive: `bounded-orbit-github-update-1.3.0.zip`, unchanged.

The experimental work is on `research-riemann-surfaces`. It is not part of
the stable release or its Palomar submission. No branch has been pushed.
The stable verification report applies to the stable commit, not to the
unfinished geometric extension described here.

## Mathematical scope agreed with Lasse Rempe

Develop the area argument intrinsically on hyperbolic Riemann surfaces,
starting with a supplied holomorphic universal covering by the unit disc.
Use the curvature -1 area throughout; no area normalisation by 2π.

For essentially thick wandering domains, investigate a geometric limiting
surface. Initially assume that this limit has infinite hyperbolic area.
Whether infinite area follows from the dynamics, and whether it is necessary
for the final conclusion, remain questions rather than proved facts.

Geometric convergence must provide area convergence on an exhaustion, or a
suitable lower-semicontinuity statement. Mere convergence of underlying
pointed metric spaces is not silently identified with convergence of areas.

The proposed application also needs eventual injectivity on the relevant
large regions downstairs, compatible forward images, and the analytic
finite-model area estimates. Injectivity of normalised lifts alone is not
recorded as injectivity downstairs.

The suggested meromorphic class B statement about escaping multiply
connected wandering domains and eventual injectivity is a research
conjecture here. We do not use it as a proved theorem or add it as an axiom.

## Implemented foundation

`BoundedWanderingDomains/Surfaces/DiscCover.lean` supplies the interface
`AreaDeficit.Surfaces.DiscCover M` for a complex manifold M. Its data are
a holomorphic map from the disc, a topological covering proof, and explicit
surjectivity. The source is proved simply connected. The target is not
assumed simply connected. Hausdorffness and second countability should be
required explicitly when subsequent surface theorems need them.

`BoundedWanderingDomains/Surfaces/GeometricArea.lean` proves:

- `exists_eventually_large_area`: if increasing sets K_j exhaust a measured
  space of infinite total measure, and a(j,n) tends to the measure of K_j
  for each j, then for every finite C there is a fixed j such that
  a(j,n) > C for every sufficiently large n.
- `no_uniform_finite_area_bound`: consequently one common finite bound C
  cannot hold eventually for each j, even when the required starting time
  depends on j.

These results resolve the order-of-limits issue conditional on the stated
area convergence and infinite-area hypotheses. They are formulated on
arbitrary measured spaces, so apply directly to Riemann surfaces. They
do not construct a geometric limit or its area measure.

The existing `AreaDeficit.finite_area_cancellation` was already formulated
for arbitrary measured spaces, and is available here unchanged.

## Next geometric obligations

`SURFACE_AREA_PROOFS.md` now gives mathematical proofs of the arbitrary-surface
2π puncture bound and the uniform remote-removal estimate, with an explicit
cutoff constant in a hyperbolic ambient surface. These are mathematical proof
notes, not completed Lean ports. They refine the plan below; the geometric
formalisation obligations remain explicit. The remote-removal proof also
covers disjoint closed K and L accumulating on disjoint sets of Freudenthal
ends, even if both sets are noncompact. Its analytic criterion is a smooth
separating cutoff with compactly supported differential. This extension
is recorded in the proof notes and has not yet been formalised in Lean.

1. Descend the disc's curvature -1 metric and area through a supplied cover;
   prove independence of local inverse branches and of the supplied cover.
2. Formulate Schwarz–Pick and covering area transport on these surfaces.
3. Identify the correct surface versions of the puncture-cost and area-gain
   statements, including all finite/infinite-area hypotheses. Do not assume
   that every planar statement transfers unchanged to every surface.
4. Connect a precise geometric-convergence notion to the area-exhaustion
   theorem; establish eventual injectivity on the needed regions.
5. Apply the conditional result to the meromorphic setting, then investigate
   removal of the infinite-limit-area assumption and the essentially thin case.

General uniformisation is not a dependency of this initial interface.
External Riemann-surface libraries may be reused only after checking their
exact definitions, theorem hypotheses, axiom dependencies, licences and
compatibility with the pinned Lean/mathlib versions.

## Verification

Build the two research modules with:

```sh
lake build BoundedWanderingDomains.Surfaces.DiscCover BoundedWanderingDomains.Surfaces.GeometricArea
```

The new results have axiom-printing commands. The stable Challenge files,
solutions, metadata, dependencies and verification scripts are unchanged.
