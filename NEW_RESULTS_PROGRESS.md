# Completed new results — 24 September 2026

All three results are proved. Build `lake build NewResults Submission Challenge`.
The public entry point `NewResults.lean` imports:

1. `AreaDeficit.uniform_compact_gain_sphere`: for disjoint compact sphere sets
   K,L, a finite bound on the hyperbolic area gain on L upon deleting K,
   uniform over the original hyperbolic sphere domain.
2. `AreaDeficit.sphere_finite_puncture_gain_le_two_pi_mul_card`: deleting any
   finite sphere set E, including infinity, gains at most 2π times its cardinality.
3. `BoundedWanderingDomains.wandering_orbit_locallyUniform_spherical_singular_derivedSet`:
   a subsequence of iterates on every wandering Fatou component of a transcendental
   entire function converges locally uniformly to a point in the derived set of
   its spherical singular values. The pointwise version is
   `wandering_orbit_subsequence_spherical_singular_derivedSet`.

Area has curvature −1 and is not divided by 2π in these statements. Area gain
is the integral of the difference of density squares, without subtracting
possibly infinite total areas. Intrinsic sphere area is independent of charts.

## Dynamics and local strengthening

The singular set includes infinity. Infinity is derived precisely when the
finite singular set is unbounded. No simple-connectivity hypothesis is present
in the entire theorem. The bounded-singular-set branch proves simple connectivity
of wandering components by extending constant normal-family limits across filled
continua, using the Eremenko–Lyubich tract theorem. The unbounded branch uses the
bounded-point-orbit theorem and a subsequence converging to infinity.
`no_escaping_wandering_orbit_of_classB` is then a corollary of derived accumulation.

The local theorem in both Challenge and Solution now also has no
simple-connectivity hypothesis. Baker filling proves eventual embedding of each
fixed covering disc. Compact confinement and eventual injectivity follow, then
the area contradiction applies. Only one point orbit must remain in a compact
subset of the analytic iteration domain. See `LOCAL_THEOREM_UPDATE.md`.

Local models use backward images of two points. No density theorem for repelling
periodic points is used. The Eremenko–Lyubich source import, licence and compatibility
changes are documented in `EremenkoLyubichConstant/RECOVERY_PORT.md`.

## Verification and scope

`verification/NewResultsAxioms.lean` audits all final declarations. Only
`propext`, `Classical.choice`, and `Quot.sound` occur transitively. No proof
holes or additional axioms occur in their dependency closure.
`verification/completion.json` records the combined build, source scan, transitive
axioms, and independent comparison of the two existing Challenge/Solution
statements and seven supporting definitions.

The three new results are exposed as proved declarations through NewResults;
they have not been added to the independent Palomar comparator configuration.
No public push, registry submission, official Comparator replay, or independent
human review is claimed. No meromorphic extension is claimed; in particular,
the multiply connected meromorphic question remains outside this work.
