# Proof dependencies

For the current visual overview, use the [proof map](../PROOF_MAP.md).
The [statement gallery](../EremenkosConjecture/MainTheorems.lean) collects
the final conclusions by paper number; the [module index](MODULE_INDEX.md)
records all direct imports.

Source: the supplied 42-page published PDF, DOI 10.1090/jams/1049.
Sections 2 and 3 occupy pages 10–18. Display formulas were checked against
rendered pages, in particular the closed disks in Proposition 3.2.

1. Runge with local domains: completed in the sibling ComplexApproximation project.
2. Finite-iterate stability: completed in IterateApproximation.
3. Compact univalence stability: Schwarz lemma after composing with the
   conformal inverse; this avoids Koebe's quarter theorem for compact sets.
4. Entire limits of locally summable polynomial corrections.
5. Plane topology: full compact neighbourhoods, finite Jordan approximations,
   fullness under univalent images, and fullness of disjoint compact unions.
6. Proposition 3.2: recursive polynomial approximation with persistent
   tolerance bounds. No assumption replacing this construction is acceptable.
7. Theorem 3.1: disjoint escaping images, Julia boundary from trapping,
   Fatou components, wandering, and transcendence.
8. Proposition 3.3: adaptable radii and maximum-modulus control.
9. Theorem 1.4: existence of a Lakes of Wada continuum and the deduction.
10. Theorem 3.4 and Remark 3.5: alternating access gates and the singleton
    case, then path-component conclusions.
11. After completing Section 3, investigate neighbourhood-holomorphic
    Arakelyan approximation and the geometry in Sections 4 and 7.

The unbounded version of Lemma 2.3 needs a uniform image-domain margin;
the paper derives it from Koebe's quarter theorem. That extra ingredient
must be proved or sourced before claiming the full version.

The paper's proof of Lemma 2.9 invokes the Riemann mapping theorem. Our
continuum case instead uses the polygonal outer-face construction from the
audited Schoenflies dependency. The finite-union Jordan refinement for
disconnected compacta remains open, and is not needed by our Section 3 proofs.

## Completed construction route for Theorem 3.1 and Proposition 3.3

Full compact neighbourhoods can be built from Runge polynomial separators and
the maximum-modulus principle; this avoids the Riemann mapping theorem for
that portion of Lemma 2.9.

The current inductive invariant says that the reference iterate agrees near
the current compactum with a homeomorphism of the whole plane. It supplies
transport of interiors and frontiers as well as injectivity. A sufficiently small holomorphic
perturbation preserves this property. Schwarz gives a Lipschitz bound on its
difference from the identity after conjugating by the local inverse. Mathlib
ApproximatesLinearOn.exists_homeomorph_extension then extends the perturbed
map globally using LipschitzOnWith.extend_finite_dimension. AmbientExtension
implements this route. This is a perturbation-extension result, not an
extension theorem for arbitrary conformal isomorphisms. Fullness in these
existing proofs follows directly from the retained global homeomorphism,
but that stronger hypothesis is unnecessary for fullness alone: the new
`ComplexApproximation.isConnected_compl_image_domain_homeomorph` proves it
for compact sets under homeomorphisms of arbitrary plane domains, using
the disjoint nonseparation theorem. No simple connectivity is required.
The base iterate is the identity; the reference next iterate
is a translation composed with the previous iterate.

For Theorem 3.1, P_j may be finite. Fullness after adjoining finite points can
be shown by connectedness of an open plane domain after deleting finitely
many points. The old disk and the new compactum lie in disjoint half-planes;
fullness of their union can be proved with complementary components and
polynomial separators. These avoid general Janiszewski machinery for the
first construction. The adaptive-radius extension for Proposition 3.3 is
also complete and audited. The additional topology for general P_j, Theorem
3.4, its singleton case, and Lakes of Wada has now been proved. See
`SECTION3_COVERAGE.md` for the final declaration map and
`COUNTEREXAMPLE_FEASIBILITY.md` for the later Section 4/7 dependencies.
