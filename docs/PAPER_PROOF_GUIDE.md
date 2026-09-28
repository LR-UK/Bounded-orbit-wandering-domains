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
components are pairwise distinct (and hence disjoint). No simple-connectivity
hypothesis is imposed on these components in Theorem 1.5.

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
subsequence exists, the full orbit lies in an ambient compact set. Assuming
that its cluster points avoid the derived singular set gives a compact tail
neighbourhood with only finitely many relevant singular values.

The six modules in `BoundedWanderingDomains/Surfaces/BKL/` implement the
covering and filling argument for arbitrary local wandering components:

1. `ReturnLimits.lean` proves local isolation of finite-target backward orbits
   in regions whose iterate subsequences have constant limits, and proves that
   removing a closed discrete set does not disconnect a surface domain.
2. `PuncturedCovers.lean` classifies connected covers of a punctured disc and
   extends bounded punctured-disc embeddings across their removable centres.
3. `AnalyticCompletion.lean` glues compatible dense holomorphic extensions.
   It proves that completion introduces no singular values and that late
   filled covering discs lie in the completed source. The cover is pulled back
   on the full preimage of each regular punctured target disc.
4. `ComponentRecovery.lean` recovers the original normality component after
   removing the discrete exceptional backward orbits. Any remaining missing
   point would map to a puncture over one of finitely many values. A value can
   puncture at most one of the pairwise disjoint wandering components.
5. `ShrinkingFillings.lean` proves normality and constant limits for the forward
   fillings, then shows that sufficiently late fillings belong to the original
   components. Their fixed-radius covering discs are therefore embedded.
6. `DerivedLimits.lean` applies the regular-covering area argument to those
   eventually embedded discs. It also proves the final subsurface reduction
   using connectedness and compact-orbit normality.

Deleting a small anchor disc from the initial component gives a noncompact
hyperbolic ambient subsurface. It preserves the actual later normality
components. The extra singular values lie in the compact image of the removed
disc, inside an early wandering component, and cannot contain a tail cluster
point. `SurfaceDerivedLimits.lean` exports the resulting theorem on an arbitrary
Riemann surface without a simple-connectivity assumption.

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
through their separate entry points. This keeps
the established results reproducible without duplicating their proofs in the
new surface assembly.

All ten selected targets have only Lean's standard classical logical axioms. Supporting
geometric hypotheses such as disc-cover existence are discharged by the
attributed uniformisation development; they are not extra target assumptions.
