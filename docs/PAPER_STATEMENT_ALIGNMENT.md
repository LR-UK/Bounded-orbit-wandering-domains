# Statement alignment

The independent `Challenge.lean` and proved `Solution.lean` select fourteen
theorems. All names are descriptive, without unpublished manuscript numbering.
The original entire-function bounded-orbit theorem keeps its exact name and
statement. The current challenge imports only Mathlib; the proofs never import it.

- **Entire and meromorphic escape:** a strictly increasing subsequence of
  iterates converges locally uniformly to infinity on the initial wandering
  component. Meromorphic normal form permits poles; admissible Fatou
  neighbourhoods avoid poles and prepoles.
- **Local compact-source exclusion:** an orbit in a wandering normality
  component is not contained in a compact subset of the actual open source.
- **Entire derived-singular accumulation:** a marked wandering orbit has a
  subsequence converging to a derived spherical singular value, possibly infinity.
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
- **Classical corollaries:** no wandering domains for compact-surface self-maps,
  rational maps in the intrinsic holomorphic-sphere formulation, or
  transcendental entire functions with finitely many finite singular values.
  Polynomial maps are included among rational maps. No separate finite-type
  meromorphic no-wandering corollary is selected.

The almost-everywhere and compact-source area formulations are equivalent by
countable exhaustion, finite-prefix compactness and countable stability of null
sets. For the derived-singular statement, failure of both subsequence alternatives
puts an orbit tail in a compact set avoiding the derived singular set. Such tails
form a countable family after fixing the exhaustion level and starting time.
Injective holomorphic iterates preserve positive area, so these exceptional sets
are null. Pairwise disjoint forward images make the iterate-injectivity
hypothesis sufficient for the saturation-injectivity used in the area proofs.

Escape always has the meaning explicitly shown in the statement: compact
avoidance along the chosen subsequence. No assertion here requires the full
orbit eventually to leave every compact set forever.

The rational statement quantifies over a complex atlas on the sphere and applies
in particular to the standard atlas. It uses open holomorphic self-maps, including
poles and infinity; no polynomial-quotient equivalence theorem is asserted.
The original entire theorem and all preceding result families are retained.
The README preserves Lasse Rempe's supplied background, including Učakar's
independent proof and the planned joint PRW/DPU paper.
