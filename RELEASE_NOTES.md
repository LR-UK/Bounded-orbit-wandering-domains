# Version 1.3.0 — local singular-limit addition

Adds a derived-singular-set limit-function theorem for bounded local analytic
dynamics. The singular set is defined for the actual restriction f|V by failure
of the covering property. The theorem assumes simple connectivity of the wandering
trapped components, but derives eventual intrinsic-disc injectivity. It gives
Euclidean locally uniform convergence of a subsequence to a finite constant in
closure(V), whose spherical value belongs to the derived singular set.

The independent singular-limit Challenge and comparator now include the local
and entire results. Existing theorems are unchanged. See LOCAL_SINGULAR_LIMITS.md
for the exact hypotheses; no meromorphic extension is claimed.

# Version 1.2.0 — prepared 24 September 2026

Every wandering Fatou component of a transcendental entire function now has a
subsequence of iterates converging locally uniformly, spherically, to a constant
in the derived spherical singular set. The same subsequence converges for every
point in the original component. Neither simple connectivity nor injectivity is
assumed. Non-escape for class-B wandering orbits follows as a corollary.

The development also proves a uniform compact-deletion hyperbolic area bound
on the sphere and the 2π-per-puncture estimate, including punctures at infinity.
The local bounded-point theorem is strengthened by removing simple connectivity
using Baker filling. Hyperbolic area in the new results has curvature −1 without
normalising by 2π. No periodic-point-density theorem is used.

The GitHub update includes independent Challenge/proof configurations for the
bounded-orbit and entire singular-limit results, strict warning checks, metadata,
source provenance and transitive axiom audits. See VERIFICATION.md for actual
checks and remaining independent-kernel replay. No publication or acceptance is
claimed. This version does not include a local or meromorphic singular-limit theorem.
