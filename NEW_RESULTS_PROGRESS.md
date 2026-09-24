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

All six modules compile together with the pinned Lean toolchain and mathlib.
Their printed axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`; there are no `sorry`, `admit`, or declared axioms in these files.

## Essential missing work

1. `FinitePunctureMetricInput` is an **uninstantiated structure** in the base
   repository. Its fields include the finite-puncture density, curvature,
   Schwarz extremal property, and total-area formula. Although the new
   point-removal result is a valid Lean theorem from these fields, the
   geometric point-removal theorem is **not yet unconditional**. Construct
   these fields from the uniformisation development and prove the finite
   total-area formula to close this gap. Do not present the result as the
   unconditional 2π theorem before this is done.
2. Formalise the compact-removal area estimate for arbitrary hyperbolic
   sphere domains, uniformly over the domain and away from the removed compact
   set. The existing local metric comparison lemmas do not give this theorem
   with the required quantifier order. Check the behaviour at the point at
   infinity when using plane charts.
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
  BoundedWanderingDomains.GeneralClosedPuncture \
  BoundedWanderingDomains.SphericalDerivedSet
```

The `/tmp` path names this working environment's local toolchain; use the
repository's `lean-toolchain` with `elan` on another machine.
