# New results: formalisation checkpoint (24 September 2026)

This branch is an additive working branch based on public commit `d57bf72`. It
contains no change to the existing Palomar Challenge, Solution, comparator,
README, or metadata. None of the three proposed challenge results is ready for
registration on this branch.

## What Lean checks

- `SphericalDerivedSet.lean`: derived sets and subsequential limits are taken
  in `OnePoint ℂ` (the Riemann sphere model used in this project). In particular,
  infinity is in the spherical derived set of a set precisely when the set is
  unbounded in the plane.
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

These modules compile with the pinned Lean toolchain and mathlib.
Their printed axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`; there are no `sorry`, `admit`, or declared axioms in these files.

## Essential missing work

1. Transfer the proved plane point-removal estimate to *sphere* domains
   through a suitable Möbius chart; prove conformal invariance of the
   integral and handle the chart pole correctly. The plane statement is
   unconditional, whereas the arbitrary sphere statement has not been
   checked.
2. Extend the proved compact-removal bound from closed planar obstacles
   containing two *fixed* omitted values to all hyperbolic sphere domains.
   The existing finite-point removal bound can pay for inserting two fixed
   anchors into the old obstacle; this transfer and the Möbius-coordinate
   invariance of the hyperbolic area integral are not yet formalised.
3. Connect both area bounds to the dynamical iteration argument. In
   particular formalise the relevant Fatou component and singular-set facts,
   covering dynamics, and spherical accumulation, and prove the derived-set
   conclusion for transcendental entire maps. The elementary topological
   subsequence lemma alone does not imply this dynamical conclusion.
4. Only after the genuine unconditional theorem is checked, add it as a new
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
  BoundedWanderingDomains.SphericalDerivedSet
```

The `/tmp` path names this working environment's local toolchain; use the
repository's `lean-toolchain` with `elan` on another machine.
