# Fullness in plane domains

[Main statements](../MAIN_RESULTS.md) · [Lean proof](../ComplexApproximation/Topology/Nonseparation.lean)

**Proved:** if U and V are open connected nonempty plane sets, h: U → V is
a homeomorphism, and K ⊂ U is compact with connected plane complement,
then h(K) has connected plane complement. Neither simple connectivity,
conformality, a Jordan boundary, nor an ambient extension is needed.

The checked declaration is
`ComplexApproximation.isConnected_compl_image_domain_homeomorph`.
The map has type `U ≃ₜ V`, so its domain is U itself. Its image of K is
written by restricting the subtype U to points belonging to K and then
coercing the image back to the plane. The statement is also displayed as
`MainTheorems.fullness_under_domain_homeomorphism`.

## The proof

1. **Disjoint closed nonseparation.** If A and B are disjoint closed plane
   sets and their complements are preconnected, the complement of their
   union is preconnected. The proof constructs a continuous exponential
   from a hypothetical separating component. A continuous logarithm on the
   plane gives incompatible logarithm branches on the two complements.
   This is the disjoint closed-set case of Janiszewski's theorem, now exposed
   as `isPreconnected_compl_union_disjoint`.
2. **The relative-complement test.** Apply that result to K and the closed
   set C \ U. It gives connectedness of U \ K when K is full. Nonemptiness
   and the converse follow because every complementary component of K
   meets U. To see this last fact, the frontier of each component lies in
   K ⊂ U. A component disjoint from U would have empty frontier and would
   therefore be the whole plane, contradicting nonemptiness of U.
   The resulting equivalence is `isConnected_compl_iff_domain_diff`.
3. **Transport by h.** The homeomorphism identifies U \ K with V \ h(K).
   Compactness of h(K) follows from continuity. Apply the same
   relative-complement test in V.

The equivalence in step 2 holds for **every plane domain**, not only simply
connected ones. This proves the requested conformal-isomorphism proposition
with a stronger topological hypothesis set.

One subsidiary assertion in the suggested proof needs correction:
complementary components of an arbitrary compact set are not necessarily
simply connected. For instance, the sphere minus a two-point set is an
annulus. The proof above does not use that assertion.

The still stronger statement about homeomorphisms of the compact sets
themselves has not been formalised in this revision. Only the explicitly
stated domain-homeomorphism result and its supporting lemmas are claimed.

## What the old ambient extension actually did

The application project's `AmbientExtension.lean` does not prove an
arbitrary conformal isomorphism of simply connected or Jordan domains
extends to a plane homeomorphism or diffeomorphism. It proves extension
for sufficiently small holomorphic perturbations of an existing chart on
a compact subset, using a quantitative extension tool from Mathlib.
Its conclusion is a homeomorphism, not a globally conformal map or a
claimed global diffeomorphism.

The induction retained this stronger invariant to obtain injectivity and
to transport interiors and frontiers of forward compact images. The
dynamics library's current wandering criterion also uses that transport.
The invariant remains in those existing proofs. Fullness itself now has
the separate local-domain theorem above, and the application's compact
disjoint-union lemma uses the generalised nonseparation proof from this
library. Replacing the whole inductive chart invariant is a separate
simplification, not a prerequisite for the new result.
