# Proof guide for the completed paper

The main surface arguments live in `BoundedWanderingDomains/Surfaces/`.

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
