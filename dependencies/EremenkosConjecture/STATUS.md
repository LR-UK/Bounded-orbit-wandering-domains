# Status — 21 September 2026

The shared univalence and derivative estimates now live in FunctionTheory.
`EremenkosConjecture/Univalence.lean` retains all five original names through
compatibility exports. After this refactor the full library, Challenge and
Solution builds, source-integrity scan, and all 299 selected axiom reports
passed on 21 September. Only `propext`, `Classical.choice` and `Quot.sound`
occur in the reports. The proved mathematical coverage is unchanged.

The [full-paper feasibility assessment](docs/FULL_PAPER_FEASIBILITY.md) now
records the remaining dependencies and a restart order. This documentation
adds no proved coverage. Private GitHub uploads will be performed manually
by the maintainer; Palomar submission is deferred until the full paper is ready.

**Theorem 1.2 is proved.** Every nonempty full compact continuum in the plane
is exactly a connected component of the escaping set of a transcendental
entire function. The theorem has no additional geometric or construction
hypotheses. Read [the statement gallery](EremenkosConjecture/MainTheorems.lean)
or [the proof and its final assembly](EremenkosConjecture/ContinuumCounterexample.lean).

The [Theorem 1.2 map](docs/THEOREM12_PLAN.md) explains the exterior-map
construction, uniform estimate on the whole continuum, approximation margins,
successor theorem, entire limit, and final connected-component argument.

## Proved coverage

| Paper result | Coverage |
| --- | --- |
| Theorem 1.2 | Every full compact continuum, including a singleton; exact connected escaping component |
| Theorem 7.1 | Exact ray statement with endpoint zero; explicit singleton escaping component |
| Failure of Eremenko's conjecture | An escaping point belongs to no connected escaping subset other than its singleton |
| Theorem 3.1 | Every full compact set is a uniformly escaping wandering compactum |
| Proposition 3.2 | Arbitrary compact nonseparating boundary data, including the eventual-empty case |
| Proposition 3.3 | Fast escape, with maximum-modulus inequalities at every nonnegative starting radius |
| Theorem 3.4 and Remark 3.5 | Prescribed escaping and Julia path components, including singleton continua |
| Strong Eremenko counterexamples | No escaping curve to infinity from the prescribed continuum, even though it is fast escaping |
| Theorem 1.4 | Countably many wandering Lakes of Wada, with fast escape on their closures |
| Section 4 | Lemma 4.1 with explicit tolerance, inverse branches, expansion and initial entire map |

Section 3 is complete; see [its detailed coverage](docs/SECTION3_COVERAGE.md).
The original counterexample and the strong curve-to-infinity counterexamples
are separate proved results. A connected component is not replaced by a path
component in either Theorem 1.2 or Theorem 7.1.

## Foundations and limitations

The proved Section 2 material includes finite-iterate approximation with
explicit uniform-control hypotheses, its automatic compact version, compact
univalence and Corollary 2.7, summable entire limits, full compact
neighbourhoods, and Jordan neighbourhoods for continua. The later unbounded
construction proves the needed uniform margins and local charts explicitly.

Neighbourhood-holomorphic Arakelian approximation and its Cauchy–Pompeiu
foundation are proved in ComplexApproximation. FunctionTheory supplies the
attributed public Tau Ceti Riemann mapping and reflection foundations, plus
the local boundary and kernel-convergence developments used here.

The following are **not claimed**:

- The full paper: Section 5 and the remaining later results are deferred.
- Either assertion of Proposition 7.6; the first has supporting topology but
  still needs its dynamical proof. Work stops after Theorem 1.2 as requested.
- The full continuous-on-the-set version of Arakelian (Theorem 2.2).
- The most general unbounded Lemma 2.3 and Corollary 2.7 from the paper.
- The disconnected finite-union Jordan refinement of Lemma 2.9.
- The arbitrary-two-domains formulation of Lemma 7.2; the needed straight-tail
  mapping theorem and the explicit ray map are proved.

None is an unresolved hypothesis of an advertised completed theorem.

## Verification and review

The current audit requests **299** named reports, including Theorem 1.2
and the proved challenge counterparts. `python scripts/verify.py` builds the
library and Challenge/Solution, scans proof sources, and checks that every
selected proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
The actual run outcome, time and source hashes are in
[verification/summary.json](verification/summary.json); detailed logs sit beside it.

Proof sources and Solution contain no holes or added axioms. Only the isolated
Challenge intentionally leaves its four statements unproved, as required by
the comparison format; it is never imported by the library or Solution.

[Challenge.lean](Challenge.lean), [Solution.lean](Solution.lean),
[comparator.json](comparator.json), and [formalization.yaml](formalization.yaml)
prepare a scoped Palomar-style review package. Comparator/NanoDa and hosted
verification have not been run. The repositories remain prepared for private
sharing; nothing has been submitted or published. See [Palomar readiness](docs/PALOMAR.md).

This is an AI-assisted research development under Lasse Rempe's direction.
Expert statement and maintainability review remains necessary before Mathlib
proposals. [Provenance](PROVENANCE.md) distinguishes original development from
attributed dependencies. [Main results](MAIN_RESULTS.md), [proof map](PROOF_MAP.md)
and [classical auxiliaries](CLASSICAL_RESULTS.md) provide the reading routes.
