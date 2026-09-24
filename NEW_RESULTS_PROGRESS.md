# New results: formalisation checkpoint (24 September 2026)

This branch is an additive working branch based on public commit `d57bf72`. It
contains no change to the existing Palomar Challenge, Solution, comparator,
README, or metadata. None of the three proposed challenge results is ready for
registration on this branch.

## What Lean checks

- `SphericalDerivedSet.lean`: derived sets and subsequential limits are taken
  in `OnePoint ℂ` (the Riemann sphere model used in this project). In particular,
  infinity is in the spherical derived set of a set precisely when the set is
  unbounded in the plane. The **final topological deduction** is now proved:
  eventual entry into every open sphere neighbourhood of the derived set
  produces a strictly increasing subsequence converging to a derived value.
- `GeneralDomainCovering.lean`: a disc covering of every component of the
  complement of a closed planar set with two distinct omitted points, and
  independence of the hyperbolic density from the chosen covering.
- `GeneralDensityLimit.lean`: convergence of finite-puncture densities to the
  covering density of the limiting component.
- `GeneralDomainMetric.lean`: an intrinsic density on these planar domains,
  positivity, monotonicity under removal of more points, local smoothness,
  the curvature equation, measurability, and pointwise convergence of
  finite-puncture models. The intrinsic density and area monotonicity proofs
  do not assume `FinitePunctureMetricInput`.
- `GeneralPunctureCost.lean`: the finite-puncture gain bound and its transfer
  to closed exhaustions through Fatou's lemma.
- `GeneralClosedPuncture.lean`: every closed obstacle admits an increasing
  finite exhaustion; conditional on `FinitePunctureMetricInput`, removing a
  point costs at most one unit of normalised area (at most 2π in curvature −1
  area). The integral is over the *new* domain, so there is no subtraction of
  infinite total areas.
- `UnconditionalPointRemoval.lean`: **closes that condition** using the
  existing theorems `exists_disc_covering_finitely_punctured_plane` and
  `IsHolomorphicDiscCovering.total_area`. Removing one point costs at most
  2π; removing a finite set `E` costs at most `2π * E.card` on arbitrary
  hyperbolic plane domains (those with at least two omitted planar points).
- `GeneralMetricDeficit.lean`: the logarithm of the ratio of two intrinsic
  hyperbolic densities is nonnegative and its Laplacian is the difference of
  squared densities. A direct cutoff bound from these identities is checked,
  provided a bound on the logarithmic gain is supplied. This does not depend
  on the total-area formula.
- `AnchoredCompactComparison.lean`: Schottky confinement supplies a
  logarithmic density comparison uniform over *both* sets of finite
  punctures, provided the old set contains two fixed omitted values.
- `AnchoredCompactArea.lean`: a smooth cutoff and Fatou's lemma give an
  unconditional **finite** area-gain bound for two disjoint compact planar
  sets. The bound is chosen before the old closed obstacle and applies to
  every obstacle containing the same two fixed omitted values. It includes
  existence of the separating cutoff, rather than assuming one as input.
  The integral is the actual curvature −1 hyperbolic area.
- `UnnormalisedPointRemoval.lean`: exposes the old finite-puncture bounds
  in curvature −1 hyperbolic area, as requested: one point costs at most
  `2π` and `E` costs at most `2π * E.card`. The older divided-by-`2π`
  quantity is now used only internally in transferring its proof.
- `AreaGainSubadditivity.lean` and `AreaAnchorIndependence.lean`: a
  subtraction/integration inequality, invariance of the intrinsic metric
  under changes of omitted-point anchors, and nullity of finite inserted
  punctures. These prepare the removal of the fixed-anchor hypothesis.
- `AreaAnchorFree.lean`: **removes that hypothesis completely in the plane**.
  Given disjoint compact planar sets `W,K`, one finite bound is chosen before
  the old closed obstacle `A`; for every hyperbolic complement of `A`, the
  curvature −1 hyperbolic area gain on `W ∩ Aᶜ` from removing `K` obeys
  the bound. It combines the anchored cutoff theorem with the `2π`-per-point
  estimate, without assuming that the total old area is finite.
- `SpherePole.lean`: for disjoint nonempty compact subsets of the connected
  sphere, there is a point outside both that can serve as a fixed chart pole.
- `SphereChartCompact.lean`: constructs a Möbius chart omitting **any**
  sphere point, proves compact sets avoiding the pole pull back to compact
  planar sets, and applies the uniform planar area bound in that chart.
- `ConformalDensityInvariance.lean` and `SphereChartTransition.lean`: prove
  conformal covariance of the intrinsic density and exact change-of-variables
  formulae for curvature −1 hyperbolic area and area gain between arbitrary
  sphere pole charts.
- `SphereHyperbolicArea.lean`: defines curvature −1 hyperbolic area and area
  gain intrinsically for sphere domains, and proves independence of the pole
  chart and omitted-point anchors.
- `SpherePointRemoval.lean`: proves that deleting any one point from an
  arbitrary hyperbolic sphere domain gains at most `2π` of curvature −1 area.
- `SphereCompactRemoval.lean`: proves the requested fully uniform sphere
  theorem. For disjoint compact sphere sets `K,L`, one finite constant is
  chosen independently of the original hyperbolic sphere domain, and bounds
  the area gained on `L` after deleting `K`.
- `SphericalEscape.lean`: an unbounded complex sequence has a strictly
  increasing subsequence converging to infinity in the sphere.
- `SphericalSingularUnbounded.lean`: applies the registered unconditional
  bounded-orbit theorem to settle the **unbounded singular-set branch** of
  the requested derived-set theorem. Its set parameter is any unbounded
  planar set, so it can be instantiated with the finite singular set when
  that set has been defined.
- `FiniteExceptionalComponents.lean`: any finite set meets only finitely
  many members of a pairwise disjoint sequence of components.
- `SphereCompactSeparation.lean`: disjoint compact spherical sets admit
  disjoint compact neighbourhoods, each containing the original in its
  interior.
- `DerivedSetExceptionalAvoidance.lean`: for any open spherical neighbourhood
  of the derived singular set, every sufficiently late member of a pairwise
  disjoint sequence avoids all singular values outside that neighbourhood.
  This is the finite-exception step in the bounded-singular-set argument,
  stated for an arbitrary set of complex values.

These modules compile with the pinned Lean toolchain and mathlib.
Their printed axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`; there are no `sorry`, `admit`, or declared axioms in these files.

## Essential missing work

1. Connect the two completed sphere area bounds to the
   **bounded-singular-set** dynamical iteration argument. In particular,
   formalise the relevant Fatou component and singular-set facts, covering
   dynamics, and prove that a wandering point orbit eventually enters every
   spherical neighbourhood of the derived singular set. The unbounded branch,
   finite-exception step, and final topological subsequence deduction are
   already checked.
2. Only after the genuine unconditional theorem is checked, add it as a new
   Palomar Challenge declaration and update the comparator and public
   metadata. Existing registered challenge declarations remain untouched.

Build in this branch:

```sh
PATH=/tmp/lean-4.35.0-rc2-linux/bin:$PATH LEAN_NUM_THREADS=4 lake build \
  BoundedWanderingDomains.UnconditionalPointRemoval \
  BoundedWanderingDomains.UnnormalisedPointRemoval \
  BoundedWanderingDomains.GeneralMetricDeficit \
  BoundedWanderingDomains.AnchoredCompactArea \
  BoundedWanderingDomains.AreaAnchorIndependence \
  BoundedWanderingDomains.AreaAnchorFree \
  BoundedWanderingDomains.SpherePole \
  BoundedWanderingDomains.SphereChartCompact \
  BoundedWanderingDomains.ConformalDensityInvariance \
  BoundedWanderingDomains.SphereChartTransition \
  BoundedWanderingDomains.SphereHyperbolicArea \
  BoundedWanderingDomains.SpherePointRemoval \
  BoundedWanderingDomains.SphereCompactRemoval \
  BoundedWanderingDomains.SphericalEscape \
  BoundedWanderingDomains.SphericalSingularUnbounded \
  BoundedWanderingDomains.FiniteExceptionalComponents \
  BoundedWanderingDomains.DerivedSetExceptionalAvoidance \
  BoundedWanderingDomains.SphereCompactSeparation \
  BoundedWanderingDomains.SphericalDerivedSet
```

The `/tmp` path names this working environment's local toolchain; use the
repository's `lean-toolchain` with `elan` on another machine.
