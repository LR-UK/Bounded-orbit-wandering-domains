# Plane-topology sources checked

Checked on 16 September 2026. The Swiss reformalisation project is EPFL/LARA:
https://github.com/epfl-lara/jordan-curve-theorem

HOLLight-Lean contains 33 Lean files plus a README. The README describes a
reformalisation of Thomas Hales's HOL Light proof in Lean/Mathlib 4.29.0.
The standalone statement identifies a simple closed curve with a subset
homeomorphic to UnitAddCircle and gives two nonempty connected open
complementary regions. Sources were downloaded under work for review.
A scan found no proof placeholders, added axioms, or native decision proofs.
The complete library has now been ported and compiled against Lean 4.34.0 and
our pinned Mathlib. Both the Jordan theorem and the equivalence of its curve
predicate with a homeomorphic copy of UnitAddCircle passed axiom audits:
only propext, Classical.choice, and Quot.sound. Upstream snapshot:
e442525a662e9e3beb8205b9fa1fc99509076ded. The Apache licence is retained.
The headline statement gives the two complementary regions but does not
explicitly supply the common-frontier and boundedness conclusions needed by
some downstream arguments. It is not yet a dependency of our delivered projects.

The local HOL Light source contains JANISZEWSKI and JANISZEWSKI_CONNECTED in
Multivariate/moretop.ml, beginning at lines 7312 and 7453 in that snapshot.
The proof uses Borsuk-map homotopy and continuous logarithms. Its disjoint
compact special case motivated our independent continuous-logarithm proof of
`isConnected_compl_union_disjoint`, which now compiles and passes its axiom
audit. It supplies the full-union fact for arbitrary compact nonseparating
boundary subsets in Proposition 3.2.

Additional primary-source candidates downloaded for inspection:

- https://github.com/alonamaloh/schoenflies-lean at
  05a43d29cde026618777db3d4e4316204ccca237. Its JordanClosed module states
  the two-region theorem with common frontier and boundedness, and proves
  connected complements of simple arcs. Its 76-module dependency closure now
  compiles on Lean 4.34 and is vendored under vendor/schoenflies with licence
  and provenance. Five audits, including the Jordan theorem, crosscut theorem,
  arc complement, polygonal face cycles and square-chain connectivity, use only
  the three standard axioms. One compatibility edit was required in Subarc.lean.
  We use the polygonal outer-face construction to obtain Jordan neighbourhoods
  without invoking the Riemann mapping theorem.
- https://github.com/vbeffara/RMT4 at
  69a9efe77e912647d651aa7368856955b24dca2f. Contains a Riemann mapping
  theorem with explicit analytic domain hypotheses. Not built or audited here.
- https://github.com/leanprover-community/mathlib4/pull/33505,
  a draft Riemann-mapping development. Not imported or audited here.

Web searches for Lean formalisations of Lakes of Wada, Janiszewski, and
Arakelyan did not identify another specific reusable Lean source. This is a
search result, not a proof that no such development exists.

The delivered project now independently proves Lakes of Wada existence in
`WadaStages`, `WadaLimits`, and `LakesOfWada`. The singleton path-component
continuum is also constructed, using the topologist's sine curve in the pinned
Mathlib `Counterexamples` library. Neither existence result is an assumption.

Resumed work on 17 September includes the complete 128-module dependency
closure of the same pinned Schoenflies `JordanSchoenflies` theorem. All modules
compiled, and square extension plus the bundled relative theorem pass the
parent audit. Source alignment is 125 identical files and three proof ports:
the previous Subarc simplification and the `Set.domRestrict` rename in Endgame
and InitialPair. No statements changed. The application uses the closed-domain
extension to prove simple connectivity of Jordan interiors.
