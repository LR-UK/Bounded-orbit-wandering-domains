# Status

The complete root library builds. Its initial modules are `Normality`, `Basic`,
`UniformEscape`, `Trapping`, `FatouComponents`, and `Iteration`; the additional
checked modules are described below.

Definitions cover entire and transcendental entire functions, escaping sets,
bounded orbits, bungee orbits, uniform escape, the spherical iterates, local normality,
Fatou and Julia sets, Fatou components, and wandering domains.

Verified results include restriction of normality, normality of a convergent
sequence, openness of the Fatou set, closedness of the Julia set, uniform escape
implying normality and Fatou interior, the direct trapped-orbit obstruction to
normality, and identification of interior components as Fatou components when
the boundary is Julia.

`Iteration` also provides the open domain of a finite iterate and equality of
iterates for maps that agree along the relevant finite orbits. The 44-result
headline audit has passed, using only `propext`, `Classical.choice`, and
`Quot.sound`; see `verification/axioms.log`.

`Wandering` proves a general criterion for wandering interior components:
uniform escape, trapped points accumulating on the boundary, ambient
homeomorphisms on the forward compact images, and disjointness of those images.
The proof establishes Julia boundaries for all forward compact images and
then excludes equality of their Fatou components. It uses no Montel theorem.

`Scaling` proves invariance of entire/transcendental entire status, iteration,
uniform escape, and the relevant trapped-point properties under a nonzero
linear change of coordinates. `Conjugacy` now proves invariance of the escaping, bounded-orbit, bungee,
Fatou and Julia sets under every homeomorphism of the plane. Local normality
is transported through the induced homeomorphism of the one-point compactification.

`FastEscape` is included in the verified library. It defines maximum modulus and fast
escape, proves that the closed-disk maximum agrees with the boundary-circle
supremum for entire functions, and gives comparison and radius-sequence
lemmas. `FastEscapeScaling` proves the exact scaling law for maximum modulus,
its iterates, and fast escape at a specified radius. `Transcendence` gives a
criterion using an escaping orbit and bounded values along a sequence tending
to infinity. The sibling EremenkosConjecture project now constructs fast
escaping compacta with bounds at every nonnegative radius. General radius
independence for arbitrary transcendental entire functions remains unproved.

`TranscendentalApproximation` proves that a polynomial plus a nonzero multiple
of the exponential is transcendental entire, and gives arbitrarily small such
perturbations on a compact set. `BoundedNormality` derives bounded-family
normality on smaller disks from Schwarz's estimate and Arzelà–Ascoli, then
proves that every point eventually entering a bounded forward-invariant open
set belongs to the Fatou set.

`PathComponents` gives path-component equalities when paths cannot leave a
prescribed subset. `CurvesToInfinity` proves that a curve starting in a bounded
path component cannot tend to infinity. These support the complete Theorem 3.4
and Remark 3.5 in the sibling project.


## Statement and navigation revision

The public statements are gathered in `ComplexDynamics/MainTheorems.lean`
with explicit types and references to their completed proofs. `MAIN_RESULTS.md`
explains the hypotheses; `PROOF_MAP.md` shows the mathematical proof routes;
`CLASSICAL_RESULTS.md` catalogues reusable auxiliaries. The generated module
index and direct-import graph are maintained by `scripts/update-map.py`.
The statement gallery is part of the library build and selected axiom audit.
This is not yet a Palomar Challenge/Comparator submission.

`Bungee` supplies two-subsequence bungee criteria and a Julia criterion for
points with escaping subsequences accumulated by trapped points. It also
proves that eventual trapping in a bounded set gives a bounded orbit.
