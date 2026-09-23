# Local theorem update — project version 1.1.0

The public theorem `BoundedWanderingDomains.no_local_bounded_wandering_domains`
has been strengthened in both `Challenge.lean` and `Solution.lean`.

| Hypothesis | Version 1.0.0 | Version 1.1.0 |
| --- | --- | --- |
| Compact containment in V | Every component U n is contained in K | Only f^[n] z belongs to K |
| Eventual injectivity on intrinsic discs | Assumed | Proved |
| Simple connectivity of U n | Assumed | Assumed, as in the paper's local theorem |
| Classical hyperbolic metric facts | Proved | Proved |

The new boundedness hypothesis is exactly:

```lean
(hbounded : ∀ n, f^[n] z ∈ K)
```

Together with `IsCompact K` and `K ⊆ V`, this says that one forward point orbit
is compactly contained in V. It imposes no common compact subset of V on the
whole component orbit. There is no injectivity hypothesis in the public local
theorem. The entire-function theorem has the same statement and proof as before.

## Proof

The new module `BoundedWanderingDomains/LocalBoundedPoint.lean` assembles the
existing analytic ingredients for the local setting:

1. Choose normalised Riemann charts in the simply connected components.
2. Choose a positive closed thickening L of the compact orbit set K, with L
   still contained in V. This L is fixed independently of intrinsic radius.
3. In a hypothetical wandering orbit, every fixed intrinsic disc shrinks
   about its marked point, so these discs eventually lie in L.
4. Local power coordinates near K, together with simple connectivity and
   eventual avoidance of finitely many branch values, give eventual
   injectivity on each fixed intrinsic disc.
5. Apply the existing area contradiction for eventually compact intrinsic
   discs, with the classical metric input supplied by the proved covering and
   total-area theorems.

The times in steps 3 and 4 may depend on the intrinsic radius. This is enough
because the area bound uses the same compact L for every radius.

The now-unused injectivity definition has been removed from the independent
Challenge and its comparison list; it remains in the development for older
helper theorems. Seven supporting definitions are compared in this version.

## Scope relative to the paper

This update addresses both requested hypothesis changes in the bounded
plane-valued case of Theorem 1.3(1). It assumes that f is analytic near the
compact plane closure of V and has no locally constant germ there. Simple
connectivity remains a local hypothesis.

It does not claim the paper's general spherical/meromorphic formulation,
its separately stated boundary-approaching subsequence conclusion, or
Theorem 1.3(2) about measurable sets of positive area. Those distinctions are
recorded in the Challenge, README and metadata. No derived-singular-set result
is included.

## Documentation and application

Your recovered introductory wording and attribution are retained, with the
local-theorem sentence updated to remove its obsolete univalence restriction.
The detailed scope in README and formalization.yaml has been updated as well.
All existing licence texts and third-party notices are retained.

This package is a separate copy for the next submission. Keep the current
version and its running build intact. After that build/submission finishes,
copy this package into a new working copy or apply its source changes to a new
Git branch. Preserve any subsequent personal edits to README or metadata.
The toolchain and dependency pins are unchanged, so existing caches can be
reused. Run the documented checks on the final committed snapshot.

If the previous version has been registered, Palomar accepts a new version
under the existing Palomar ID, using a new full commit SHA. See
[Palomar's submission instructions](https://palomar-registry.org/how-to-submit).
No publication or submission has been made from this working copy.

See `VERIFICATION.md` for actual validation results and the remaining official
Comparator/independent-kernel gate.
