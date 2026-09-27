# Proof guide for the completed paper

The main surface arguments live in `BoundedWanderingDomains/Surfaces/`.

## Components and their forward images

For a local map `f : O -> X`, the normality locus `omega` consists of points
with an open neighbourhood whose entire forward orbit stays in `O` and on
which the iterates form a normal family, using the one-point compactification
of `X` as target. A normality component is a connected component of this open
locus. A "full normality component" means the whole connected component;
"full" here does not mean that a planar domain has no holes.

Let `U_n` be the component containing `f^n(U)`. The forward-containment property
is `f(U_n) ⊆ U_(n+1)`, even for points of `U_n` outside `f^n(U)`. Neither
`f(U_n) = U_(n+1)` nor `f^n(U) = U_n` is required. Wandering means these
components are pairwise distinct (and hence disjoint). The simple-connectivity
hypothesis of Theorem 1.5 concerns these whole components.

`OmegaDynamics.lean` proves forward invariance of the normality locus in
`LocalMap.totalize_mapsTo_omega`, and then component containment in
`LocalMap.mapsTo_component_of_imageAt`. The first uses openness to transfer
normality from a neighbourhood to its image; the second uses connectedness
and the common orbit point. These are proved structural lemmas, not additional
hypotheses in the paper's theorem statements.

## Theorem 1.3(1)

`SurfaceOrbitEscape.lean` removes a small coordinate disc inside the initial
wandering component, away from the marked point. The later components lie in
its disc-covered complement. Compact orbit bounds permit a source restriction;
`HyperbolicOrbitEscape.lean` combines shrinking covering discs, surface filling,
eventual injectivity and the finite-model area contradiction. This works for
multiply connected wandering components as well. `MeromorphicEscape.lean`
then supplies Theorem 1.2 for meromorphic maps via their local sphere model.

## Theorem 1.5

`NoEscapeCompactRange.lean` first separates compact escape: if no escaping
subsequence exists, the full orbit lies in an ambient compact set. Finite
backward models and a compact cluster-set separation in
`CompactClusterSeparation.lean` reduce the singular values near the orbit to a
finite exceptional set plus a closed remote set. `RegularCoveringArea.lean`
gives exact covering transport there; `HyperbolicDerivedLimits.lean` obtains
the required derived singular accumulation.

`SubsurfaceWanderingComponents.lean` proves that deleting the initial anchor
disc preserves the actual later simply connected components. The new singular
values are confined to the compact image of the removed disc, inside an early
wandering component. That set cannot contain a tail cluster point.
`SurfaceDerivedLimits.lean` therefore proves the exact arbitrary-surface target.

## Theorem 1.3(2)

`CompactLocalAreaAdvance.lean` handles every proper compact candidate through
a fixed hyperbolic subsurface. The remaining compact-global case is proved in
`CompactGlobalPositiveArea.lean`.

Choose three distinct anchor points and take their finite backward stages.
The anchors are a fixed choice of points; periodicity is unnecessary.
`CompactPunctureMontel.lean` and `CompactAnchorNormality.lean` prove normality
away from the closure of this backward set, including subsequences approaching
punctures. Hence the non-normal measured set lies in that closure.

Deleting a countable backward exceptional set preserves positive area and the
wandering cancellation identity. `FiniteDefectAreaAdvance.lean` transports area
through the actual regular covering; finite singular values and images of the
anchors account for the finite defect. The already proved uniform global
finite-puncture area package yields the contradiction.
`SurfacePositiveArea.lean` combines this with the proper-compact case.

## Entire statements and retained results

The entire escape and derived-singular statements use the previously verified
stronger entire results. The meromorphic statement is directly deduced from the
surface theorem. Earlier local-plane and sphere-area results remain available
through their separate entry points and comparator configurations. This keeps
the established results reproducible without duplicating their proofs in the
new surface assembly.

All six targets have only Lean's standard classical logical axioms. Supporting
geometric hypotheses such as disc-cover existence are discharged by the
attributed uniformisation development; they are not extra target assumptions.
