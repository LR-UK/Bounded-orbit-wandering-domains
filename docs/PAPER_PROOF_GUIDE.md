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
hypothesis is imposed on these components in the local derived-singular theorem.

`OmegaDynamics.lean` proves forward invariance of the normality locus in
`LocalMap.totalize_mapsTo_omega`, and then component containment in
`LocalMap.mapsTo_component_of_imageAt`. The first uses openness to transfer
normality from a neighbourhood to its image; the second uses connectedness
and the common orbit point. These are proved structural lemmas, not additional
hypotheses in the paper's theorem statements.

## the local compact-orbit theorem

`SurfaceOrbitEscape.lean` removes a small coordinate disc inside the initial
wandering component, away from the marked point. The later components lie in
its disc-covered complement. Compact orbit bounds permit a source restriction;
`HyperbolicOrbitEscape.lean` combines shrinking covering discs, surface filling,
eventual injectivity and the finite-model area contradiction. This works for
multiply connected wandering components as well. `MeromorphicEscape.lean`
then supplies the entire and meromorphic escape theorem for meromorphic maps via their local sphere model.

## the local derived-singular theorem

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

## the positive-area wandering-set theorem

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

All fourteen selected targets have only Lean's standard classical logical axioms. Supporting
geometric hypotheses such as disc-cover existence are discharged by the
attributed uniformisation development; they are not extra target assumptions.

## Compact and almost-everywhere refinements

The nine modules in `BoundedWanderingDomains/Surfaces/AlmostEverywhere/` contain
the refinements. `Definitions.lean` makes chartwise nullity and the two
subsequence conclusions explicit. `OrbitShift.lean` proves backward invariance
of normality, inheritance under time shifts, and the passage from injectivity
of every iterate on the starting set to injectivity on its disjoint saturation.

`CompactDerivedArea.lean` first proves positive-area exclusion for a compact
saturation avoiding the derived singular set on a hyperbolic surface. A compact
neighbourhood meets the singular set in only finitely many exceptional values.
Finite backward stages of the source boundary capture all non-normal points;
removing a countable backward-invariant set preserves positive area. The regular
covering gives uniform one-step area gain and the finite-model contradiction.
For a compact ambient surface with finite singular set, three anchors supply
the same argument even when the original map has a proper open source.

`ThreePointHyperbolization.lean` and `CompactAreaRestriction.lean` remove three
points outside any proper compact candidate. The resulting subsurface is
hyperbolic, and the restriction adds only finitely many singular values.
Compact-orbit normality transfers back to the original map. This proves the
ambient compact-set theorem on every surface.

`PositiveAreaImage.lean` proves that an injective open holomorphic map preserves
positive chart area. It uses compact chart patches, finitely many critical
points on each patch, and the holomorphic change-of-variables theorem.
`CompactSource.lean` and `DerivedSingular.lean` then use countable compact
exhaustions. For the latter, each exceptional set consists of points whose
orbits stay in a fixed compact set after a fixed time. Its forward image is
null by the compact-area theorem, so it too is null. Countable stability gives
the almost-everywhere conclusion in every chart. No global measure is needed.

`Results.lean` exposes the four new public statements, including the compact
wandering-orbit corollary of the BKL theorem. These results concern subsequences;
the full orbit is not asserted to escape permanently.
