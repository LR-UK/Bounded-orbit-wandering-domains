# Local theorem: simple connectivity removed

`BoundedWanderingDomains.no_local_bounded_wandering_domains`, in both the
independent Challenge and proved Solution, assumes only one compactly contained
point orbit. It has no simple-connectivity or injectivity hypothesis.

The function is analytic near the compact closure of an open planar set V and
has no constant germ there. The U_n are the actual components of the interior
of the set trapped in V, through f^[n](z). If all these marked points lie in a
fixed compact K contained in V, the U_n cannot be pairwise disjoint.

## Proof

`LocalBoundedPointGeneral.lean` assembles the following argument.

1. Choose normalised holomorphic disc coverings of the components.
2. Under the wandering assumption, images of each fixed closed subdisc shrink
   around their marked points. One fixed compact thickening of K confines them.
3. Fill the images of these subdiscs. Local openness implies that filling
   commutes with forward mapping in the required inclusion direction. The fills
   stay trapped and hence lie in the same components. This is the Baker step.
4. Simply connected neighbourhoods of the filled images, together with covering
   theory, prove eventual embedding of each fixed covering disc.
5. Local power coordinates and avoidance of finitely many branch values give
   eventual injectivity of f on these discs.
6. The finite-puncture hyperbolic area contradiction applies. Covering existence,
   metric properties, and the area formula are all proved.

The relevant times may depend on the disc radius; the compact thickening and
area bound do not. Whole components need not lie in K, and need not be simply
connected. The older simply connected helper theorem remains available.

The statement concerns plane-valued maps analytic near compact closure(V).
It does not assert the paper's general meromorphic formulation or the separate
positive-area-set result. See `NEW_RESULTS_PROGRESS.md` for the additional entire
singular-limit theorem and sphere area bounds proved in this update.
