# Proof guide

The main results share the combined componentwise encounter theorem in
`BoundedWanderingDomains/Surfaces/SingularEncounters/`.

## Wandering domains

`SurfaceWanderingEncounters.lean` separates ambient escape from compact orbit
range. A compact set meets finitely many ambient components. The lemmas in
`Surfaces/Disconnected/CompactWanderingReduction.lean` first restrict to their
clopen union without changing the retained inverse components or creating
singular values. `WanderingAnchors.lean` then deletes a small coordinate disc
in an early wandering component in each visited ambient component. After a
finite initial segment, the orbit remains in a compact subset of the resulting
componentwise hyperbolic manifold, whose components are all noncompact.
`OmegaDynamics.lean` supplies forward containment of the full normality
components. Compact-orbit normality identifies the restricted components.

The componentwise finite-obstruction contradiction combines the two area
estimates. `ComponentFilling.lean`, `ComponentControl.lean` and
`ShrinkingFillings.lean` apply the BKL covering and completion lemmas to full
inverse components. The shared lemmas in `Surfaces/BKL/` handle punctured-disc
covers, removable completions, discrete backward exceptional sets, and recovery
of the original normality components. No assumption that whole later
wandering domains become simply connected is made.

`CompactWanderingEncounters.lean` extracts distinct singular values in discs
shrinking to a derived singular value. A common increasing sequence of times
captures each compact subset of the initial component. Restriction transport
returns full inverse components of the original map, and
`SurfaceWanderingEncounters.lean` gives the arbitrary-surface theorem.

`EncounterSourceEscape.lean` proves that the selected source points leave every
source compact set: compact local holomorphic models have only finitely many
local branch obstructions, incompatible with the distinct shrinking encounters.
`EncounterConsequences.lean` gives convergence of the next iterates to the
derived singular value. `SurfaceOrbitEscape.lean` and
`SurfaceDerivedLimits.lean` are short corollaries of this combined proof.

## Measurable wandering sets

`CountableDiscBasis.lean` and `CountableObstructions.lean` choose a countable
analytic-disc basis and a countable pool containing all finite obstruction
sets. Failure of the encounter alternative yields finite component control
on a compact orbit range. `ConfigurationCover.lean` covers these failures by
countably many measurable configurations. Positive-area configurations are
shifted to their controlled tails using injective holomorphic iterates.

`CountableCrossAmbientArea.lean` sums local gain measures over a disjoint
measurable partition. There are only finitely many target-area budgets,
even when countably many source components are visited. The ordinary
single-ambient estimate is a specialization of this same proof.

`Disconnected/CompactPositiveAreaReduction.lean` restricts a compact measured
saturation and the finitely many relevant target discs to a finite clopen union
of ambient components. `FiniteComponentPositiveArea.lean` chooses three anchors
in each component, separately for each compact inner target. The proof compares
areas in overlapping anchor complements. `ComponentwiseFiniteComplementArea.lean`
establishes finite area above compact ambient sets, including at the finitely
many deleted points, and `ComponentwiseFiniteAreaPunctures.lean` preserves this
finiteness through the finite models. This one proof handles mixtures of compact
and noncompact ambient components. `SurfaceAlmostEverywhere.lean` then
proves the chartwise almost-everywhere encounter alternative. The prior area
and almost-everywhere results follow from it; their independent proofs are removed.

## Disconnected geometry

`ComponentwiseDiscCover` supplies a disc cover on each ambient component.
`Disconnected/ComponentwiseArea.lean` sums their intrinsic area measures;
compactly supported estimates involve only finitely many components.
Covering-area transport uses the actual target of each connected source piece,
with no permutation or periodicity assumption on ambient components.
`ClopenNormality.lean` proves compatibility of normality under clopen ambient
restriction. `ClopenSourceRestriction.lean` proves preservation of retained
inverse components and the required inclusion of singular sets. The BKL filling
steps apply in the relevant noncompact component.

## Entire, meromorphic and finite-type corollaries

The sphere models include poles as ordinary holomorphic source points.
`MeromorphicDerivedSingular.lean` specializes the surface theorem to the compact
sphere, excluding ambient escape. Infinity can itself be a derived singular
value; it is not a boundary point of the target sphere.
`EntireDerivedSingular.lean` gives the entire specialization, using that the
finite differences between singular-value conventions do not change derived
sets. `EntireBoundedOrbit.lean` preserves the original statement while replacing
its proof with the surface corollary. Normal-family extraction in
`MeromorphicEscape.lean` promotes escape subsequences to locally uniform limits.

`Surfaces/FiniteType.lean` excludes wandering domains on compact, possibly disconnected target manifolds
with finite singular set. `NoWanderingCorollaries.lean` deduces the rational,
compact-surface and class S entire/meromorphic cases from that theorem.

## Independent statements

`Challenge.lean` imports only Mathlib and states nineteen selected targets.
`Solution.lean` exposes the proved declarations without importing Challenge.
The definitions of the public encounter sequence specify full inverse
components, genuine component singular values and common visit times.
`comparator.json` selects the statements and their supporting definitions.
