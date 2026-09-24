# Local derived singular limit theorem — version 1.3.0

The theorem is `BoundedWanderingDomains.local_wandering_orbit_locallyUniform_singular_derivedSet`
in `LocalUniformSingularLimits.lean`, exposed through NewResults and independently
stated in SingularLimitsChallenge.

Let V be open with compact closure. Assume f is analytic near closure(V) and
has no locally constant germ there. Let U_n be the actual connected components
of the interior of the set trapped in V, through f^[n](z). If these components
are pairwise disjoint and simply connected, then there are a finite a in
closure(V) and strictly increasing n_k such that f^[n_k] converges locally
uniformly on U_0 to the constant a, and a is a derived spherical singular value
of the restricted map f|V.

The restriction's regular values are those w with an open neighbourhood W
such that `(fun x : V => f x)` is a covering over W. Its singular set is the
complement of these regular values. Infinity is included when passing to the
sphere. `singularValuesOn_congr` proves that changing f outside V leaves this
singular set unchanged. This definition records failures of covering caused
by the source boundary as well as critical or asymptotic behaviour.

## Hypotheses and scope

- Simple connectivity of every U_n is assumed.
- Injectivity on the component orbit is not assumed. The proof derives eventual
  injectivity on fixed intrinsic discs from avoidance of singular values and
  covering-lift uniqueness.
- There is no compact K inside V containing the point orbit. Iterates may
  approach the boundary. Compactness is required only for closure(V).
- Convergence is convergence of functions on U_0, and of every point orbit
  along the same subsequence, not convergence of image domains. It is actually
  Euclidean locally uniform convergence, since V is bounded.
- No meromorphic or arbitrary unbounded-domain version is claimed.

The separate local bounded-point absence theorem remains stronger with respect
to connectivity: it still assumes neither simple connectivity nor injectivity.
The new theorem does not weaken or replace it.

## Proof

The existing finite local backward-puncture models recover the actual trapped
components. A new local covering pullback inequality lifts extremal discs through
f|V and proves the hyperbolic area transport needed for cancellation. The sphere
area-gain bound then forces a point-orbit cluster value into the derived singular
set. Bounded holomorphic normal-family compactness and disjoint images give a
single constant limit function on the whole initial component. No density of
repelling periodic points is used.

Lean checks all new proofs with only propext, Classical.choice and Quot.sound.
The independent singular-limit comparator configuration now includes both the
entire and local theorems and all thirteen supporting definitions.
