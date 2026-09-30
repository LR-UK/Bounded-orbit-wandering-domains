# Statement alignment

The independent `Challenge.lean` and proved `Solution.lean` select nineteen
theorems. All names are descriptive, without unpublished manuscript numbering.
The original entire-function bounded-orbit theorem keeps its exact name and
statement. The current challenge imports only Mathlib; the proofs never import it.

- **Entire and meromorphic escape:** a strictly increasing subsequence of
  iterates converges locally uniformly to infinity on the initial wandering
  component. Meromorphic normal form permits poles; admissible Fatou
  neighbourhoods avoid poles and prepoles.
- **Local compact-source exclusion:** an orbit in a wandering normality
  component is not contained in a compact subset of the actual open source.
- **Entire and meromorphic derived-singular accumulation:** a marked wandering orbit has a
  subsequence converging to a derived spherical singular value, possibly infinity.
  The target surface is the compact sphere; there is no ambient-escape alternative.
- **Local derived-singular accumulation:** a marked wandering orbit has a
  subsequence escaping every ambient compact set or converging to a derived
  singular value of the actual local map. No simple-connectivity hypothesis
  is present. The Baker–Kotus–Lü adaptation handles multiply connected components.
- **Compact wandering-orbit version:** if such an orbit is contained in an
  ambient compact set, it has a derived-singular subsequential limit in that set.
- **Positive-area compact formulations:** a measurable wandering set in
  `trapped \ omega` cannot have positive chart area and saturation contained
  in a source compact set. The stronger derived-singular formulation excludes
  an ambient compact saturation disjoint from the derived singular set.
- **Almost-everywhere formulations:** for a measurable wandering set in
  `trapped \ omega` with every iterate injective on the set, almost every point
  has a subsequence escaping source compacts. Also, almost every point has an
  ambient-escaping or derived-singular subsequence. The exceptional set is
  Lebesgue-null in every chart. These conclusions do not require a global measure.
- **Finite-type theorem:** an open holomorphic map from an arbitrary open
  subset of a compact Riemann surface into that surface, with a finite singular
  set, has no wandering normality components. Neither simple connectivity nor
  maximality of the source is assumed; removable punctures are permitted.
- **Classical corollaries:** no wandering domains for compact-surface self-maps,
  rational maps in the intrinsic holomorphic-sphere formulation, and class S
  transcendental entire and meromorphic functions. All follow from the finite-type
  theorem. Polynomial maps are included among rational maps. Meromorphic singular
  values are defined using the genuine sphere-valued map and local coverings
  allowing empty sheets. Empty-preimage neighbourhoods are regular; omitted
  asymptotic values are singular. The pole-avoiding Fatou components agree
  with the normality components of the local sphere model.

The combined statement strengthens these conclusions. It supplies distinct
singular values s_n tending to s, analytic target discs D_n containing s and
shrinking to {s}, and full inverse components U_n of f^{-1}(D_n). Each s_n is
a genuine singular value of f restricted to U_n. At common strictly increasing
times, the U_n capture each compact subset of the initial wandering domain.
In particular every orbit enters every sufficiently late selected U_n. The
public definition quantifies over the U_n themselves and uses the ordinary
singular values of each restricted map U_n → D_n. Base points are confined
to internal component-identification proofs.
For measurable wandering sets the analogous pointwise assertion holds almost
everywhere, with sequences allowed to depend on the point. No infinite-degree
condition is imposed on the selected components.

The earlier main theorems are derived from this combined proof. Distinct
shrinking obstructions force a source-escaping subsequence, while the images
of the selected source points converge to s. The compact positive-area
formulations are consequences of the chartwise almost-everywhere conclusions.

Escape always has the meaning explicitly shown in the statement: compact
avoidance along the chosen subsequence. No assertion here requires the full
orbit eventually to leave every compact set forever.

The rational statement quantifies over a complex atlas on the sphere and applies
in particular to the standard atlas. It uses open holomorphic self-maps, including
poles and infinity; no polynomial-quotient equivalence theorem is asserted.
The original entire theorem and all preceding result families are retained.
The README preserves Lasse Rempe's supplied background, including Učakar's
independent proof and the planned joint PRW/DPU paper.

For maps between Riemann surfaces, a regular value has a disc neighbourhood
such that every connected component of its preimage maps homeomorphically
onto that disc. Lean uses the equivalent covering-neighbourhood formulation;
the disc is not required to lie in the image. If the preimage is empty,
the condition holds vacuously. This matters for locally defined maps: the
singular set contains the obstruction to such inverse branches, rather than
all omitted values. An omitted value approached by image points can still
be singular, as for the punctured-plane inclusion at zero.
