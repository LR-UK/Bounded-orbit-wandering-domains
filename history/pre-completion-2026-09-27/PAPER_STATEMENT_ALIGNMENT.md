# Revised-paper statement alignment — 25 September 2026

The controlling specification is the introduction of the supplied
`no-bounded-WD-2.tex`, with the author's explicit correction: the compact set
in Theorem 1.3(2) is contained in **O**, not Ω(f). The incomplete proofs later
in the draft do not narrow the statements.

`PaperChallenge.lean` is a new independent specification importing Mathlib
only. Its six proposition targets cover all four introductory theorems after
splitting the entire/meromorphic cases and the two parts of Theorem 1.3.
They are specifications, not new proved theorems. There are no proof holes or
new axioms. The existing `Challenge.lean` and `Solution.lean` are unchanged.

## Correspondence

| Draft | Exact scope and conclusion | Proposed target |
| --- | --- | --- |
| Theorem 1.2, entire case (`thm:boundedorbitentire`) | Transcendental entire f; wandering Fatou component U; a strictly increasing subsequence of iterates converges locally uniformly on U to ∞ in the sphere. | `BoundedWanderingDomains.wandering_orbit_locallyUniform_inftyClaim` |
| Theorem 1.2, meromorphic case | Transcendental meromorphic f, allowing poles; the same locally uniform conclusion. As the author clarified, derive this as a corollary of Theorem 1.3. | `MeromorphicDynamics.WanderingLocallyUniformInfinityClaim` |
| Theorem 1.3(1) (`thm:spherelocal`) | Arbitrary Riemann surface X; open O ⊆ X; open holomorphic f : O → X; wandering component U of Ω(f); every z ∈ U and compact K ⊆ O. Some forward iterate is outside K. | `SurfaceDynamics.NoCompactWanderingOrbitClaim` |
| Theorem 1.3(2) | Measurable positive-area A ⊆ T(f) ∖ Ω(f), pairwise disjoint forward images, f injective on their whole union. That union is not contained in any compact subset of O. | `SurfaceDynamics.NoCompactPositiveAreaWanderingSetClaim` |
| Theorem 1.4 (`thm:derivedset`) | Transcendental entire f; wandering U; z ∈ U. A subsequence tends to a point of (S(f) ∪ {∞})′ in the sphere. | `BoundedWanderingDomains.wandering_orbit_pointwise_spherical_singular_derivedSetClaim` |
| Theorem 1.5 (last introductory theorem) | Arbitrary X; open holomorphic f : O → X; wandering U; every Ω(f)-component containing an iterate of U is simply connected. For each z ∈ U, a subsequence either leaves every compact subset of X or tends to a point of S(f)′ in X. | `SurfaceDynamics.WanderingDerivedSingularLimitClaim` |

Simple connectivity occurs only in Theorem 1.5. Injectivity on the forward
saturation occurs only in Theorem 1.3(2). No hyperbolicity of the ambient X,
auxiliary compact working domain, assumed area bound, or infinite-area limit
has been inserted into any dynamical target.

## Definition checks

- Wandering refers to actual connected components of the normality locus,
  not merely disjoint images of an arbitrary open set. Partial iterates in
  the surface definitions are used on trapped orbits, where they are defined.
- Surface normality uses the compatible uniformity on the one-point
  compactification of X. The proved `tendsto_infty_iff_leaves_compacts`
  identifies its escape alternative with compact avoidance. This is not
  convergence to a specified boundary point of O.
- Both local non-containment results quantify over compact subsets of O;
  the final theorem's escape alternative quantifies over compact subsets of X.
- Surface singular values are those without a neighbourhood over which the
  actual local map on O is a surjective covering. They are not singular values
  of a smaller auxiliary restriction or just a finite set of critical values.
- The entire derived-set target takes the derived set **after** adjoining ∞.
  It does not automatically accept ∞ when singular values do not accumulate
  there. Neither derived-set statement classifies every limit function.
- Positive area is positive Lebesgue area in some complex chart, with
  measurability and the usual second-countable surface hypotheses.
- The meromorphic target uses `MeromorphicNFOn f univ`, Mathlib's normalized
  finite representative, which permits poles. Its Fatou neighbourhoods avoid
  all poles and prepoles, so assigned representative values at poles never
  enter admissible iterates. Nonrationality uses meromorphic germs of polynomial
  quotients; “not a polynomial” would be insufficient for this case.

The older bounded planar local results are retained as proved intermediate
results; they are not substitutes for the general surface theorems. The
existing locally uniform entire derived-set theorem is stronger than the
pointwise conclusion requested by Theorem 1.4.

## Draft corrections

The original is preserved as `../paper-draft/no-bounded-WD-2.tex`. The adjacent
`no-bounded-WD-2-statements-corrected.tex` changes only these five items, plus
line-ending normalization:

1. The setup before T(f): O ⊆ X, replacing O ⊆ Ĉ.
2. Theorem 1.3's heading: “on Riemann surfaces,” replacing “on the sphere.”
3. Theorem 1.3(2): compact subset of O, replacing Ω(f), as confirmed by the author.
4. Theorem 1.4: f^{n_k}(z), replacing f^n(z).
5. Theorem 1.5: f^{n_k}(z), replacing f^n(z).

Strictly increasing indices are used for subsequences throughout. Proof text
is unchanged. The abstract informally omits ∞ in its entire derived-set
description; the precise introductory theorem governs the challenge.

## Verification and next work

**Passed locally:** the independent statement file builds successfully
(2,972 Lake jobs). All 35 declaration comparisons passed: nine shared entire
definitions, 24 surface declarations (including their three targets), and
the two entire target bodies against the existing theorem types. The six
proposition definitions use only the permitted standard axioms. These checks
verify the specification and its correspondence, not proofs of new results.
The final report is `../local-verification/paper-alignment-verification.json`.

Use `../Run-Local.ps1 -Action Statements` (which selects the pinned local
toolchain and runs `lake build PaperChallenge`) for the proposed specification. It repeats
declaration names intentionally and should not be imported alongside proof
modules in one environment. The old submission comparator remains unchanged;
a completed-paper submission will require its own solution connections and
expanded comparator contract. Compiling proposition definitions proves no
new dynamical theorem.

The two entire targets have existing proofs. The three surface targets remain
unproved, and the meromorphic conclusion must be connected as their corollary.
The author's new proof directions and the exact remaining uniformity issue
are recorded in `FORMALISATION_HANDOFF_2026-09-25.md`.
