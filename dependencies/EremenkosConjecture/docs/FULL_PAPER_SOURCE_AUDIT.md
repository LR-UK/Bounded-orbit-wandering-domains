# Source audit for the remaining paper

Read-only assessment, 18 September 2026. Companion to the
[feasibility plan](FULL_PAPER_FEASIBILITY.md). Negative search results below
mean that no suitable verified declaration was located in the stated search;
they are not claims that no formalisation exists anywhere.

## Mathematical source and reading scope

The supplied 42-page published PDF is Martí-Pete–Rempe–Waterman,
*Eremenko's conjecture, wandering Lakes of Wada, and maverick points*,
[JAMS, DOI 10.1090/jams/1049](https://doi.org/10.1090/jams/1049).
This assessment read the remaining arguments in Sections 5, 6, 8 and 9,
the final remarks and Proposition 7.6, and the corresponding introduction
statements, against the existing Section 2–4 and 7 development. Formulas on
printed pages 28, 36 and 37 were also checked visually. The supplied PDF and
extracted text are not redistributed in these repositories.

| External source | What was checked | Limit of this assessment |
| --- | --- | --- |
| Osborne–Sixsmith, [*On the set where the iterates of an entire function are neither escaping nor bounded*](https://arxiv.org/abs/1503.08077), Lemma 4.1 | Proof of the harmonic-measure estimate used as Lemma 8.2: comparison, Harnack bounds, disjoint exit arcs and a summability argument | No Lean implementation located or produced |
| Rippon–Stallard, [*Boundaries of escaping Fatou components*](https://arxiv.org/abs/1009.4450) | Statements and relevant harmonic-measure/Fatou-boundary arguments, especially Theorem 1.2 | General boundary dynamics is not already proved by the present construction lemmas |
| Garnett–Marshall, *Harmonic Measure*, [author's book listing](https://sites.math.washington.edu/~marshall/preprints/preprints.html) | Book identification and the Evans theorem required by the supplied paper's second proof of Proposition 9.1 | The full Appendix E proof has not been read and decomposed here; do this before committing to an implementation estimate |
| Rippon–Stallard, [*Fast escaping points of entire functions*](https://arxiv.org/abs/1009.5081), and the paper's cited earlier fast-escape results | Identified as sources for the general fast-escaping component facts still needed | No complete proof audit of those results in this assessment |

Bishop's interpolation/uniformization route is deliberately not a dependency
of the proposed plan. The finite logarithmic-sum proof in Section 9 was checked
directly. The full logarithmic-integral proof still needs Evans's theorem.

## Formal source versions inspected

- Mathlib: pinned commit `5ed2965256430c3649e86755f9576b54eca72435`, with the
  complete local source tree searched, plus current official generated docs.
- Tau Ceti: local source snapshot
  `f441315d5d3c9ccc377a691d7a7da00613010718`, with the relevant complex-analysis
  modules inspected. FunctionTheory vendors only its documented dependency
  closure; another Tau Ceti module is not automatically an available import.
- The four local libraries, including the attributed Schoenflies source
  closure. Their proof versions and audit dates are in `verification/` and
  the [private review setup](PRIVATE_REVIEW.md).
- [EPFL's reformalization project](https://github.com/epfl-lara/jordan-curve-theorem),
  the Swiss Jordan-curve translation project initially recalled as Zurich.
  Its public project and HOL Light/Mizar translation scope were checked.
- Targeted public searches covering HOL Light and Isabelle/AFP, as well as
  Lean/Mathlib and Tau Ceti, for harmonic measure, logarithmic capacity and
  Evans's theorem. No suitable verified artifact was located. This was not
  an exhaustive source checkout of every other prover library or every EPFL
  translation project.

The newest public Tau Ceti directory was also consulted, but the declaration
inventory below is based on the pinned local source. Recheck upstream before
starting a substantial new foundation: public repositories may have advanced.

## Useful existing interfaces

| Source | Verified content located | What it does not establish |
| --- | --- | --- |
| Mathlib `Analysis/Complex/Harmonic/Poisson.lean` | Poisson representations for harmonic functions, including `HarmonicOnNhd.circleAverage_poissonKernel_smul` and its `HarmonicContOnCl` counterpart | General harmonic measure on rough domain boundaries |
| Mathlib `Analysis/Complex/Poisson.lean` | Poisson/Herglotz–Riesz kernels, upper/lower bounds and parameter-dependent circle-integral differentiability | Almost-everywhere radial boundary values or a full Perron theory |
| Tau Ceti `Analysis/Complex/Conformal/Hyperbolic/Distance.lean` and related files | Disc hyperbolic distance, Schwarz–Pick contraction, density and length interfaces | A located general-domain boundary-distance estimate for Lemma 5.4 |
| Tau Ceti `Analysis/Complex/Conformal/Koebe.lean` | Extremal-map construction used for Riemann mapping | This filename is not evidence of a Koebe quarter theorem |
| FunctionTheory conformal modules | Normalized Riemann mapping, bounded Montel/inverse convergence, reflection, local boundary continuity, crosscuts and length-area estimates | Full prime-end theory or unrestricted rough-boundary harmonic measure |
| EremenkosConjecture `UnivalentIterates.lean` | Compact uniform iterate and univalence stability through actual local charts | Automatic margins on unbounded sets |
| EremenkosConjecture `NestedJordanNeighbourhoods.lean` | Nested Jordan neighbourhoods for full compact continua | The disconnected finite-union version of Lemma 2.9 |
| EremenkosConjecture `CompactComponentHoles.lean` | The topological hole argument relevant to Proposition 7.6(i) | The additional general dynamical theorems needed for its conclusion |

The Mathlib inventory can be compared with the official
[harmonic Poisson documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Harmonic/Poisson.html)
and [complex Poisson documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Poisson.html).
The precise pinned source, rather than an evolving documentation page, is
the reference for implementation compatibility.

## Search record and interpretation

The local analysis searches included variants of:

```text
harmonic.?measure
logarithmic.?capacity
logarithmic.?potential
Evans
Harnack
subharmonic
radial.*limit
nontangential
Koebe / quarter / hyperbolic / Poincare
Hausdorff / positive.*measure / Jordan.*arc
```

Broad word matches were inspected rather than counted as supporting theorems.
Generic measure theory, the harmonicity of a logarithm, a metric-space
capacity, or a theorem bearing the name Evans in another subject would not
supply the required planar potential theory. In the searched pinned trees
no suitable logarithmic-capacity/Evans development or positive-area Jordan-arc
construction was found. The sphere interfaces inspected also did not expose
the desired explicit chordal-distance API, although their topology and
uniformity provide a sound starting point.

Future source searches should again include other provers and EPFL. A public
proof in another prover is valuable mathematical guidance; it is not itself
a checked Lean dependency until translated and built with an explicit audit.

## Small implementation cautions from the paper

- Page 28 prints `πₘ(Z_mav)=Ξ` for concentric discs. With its definitions the
  image is `(r/rₘ)Ξ`, which converges to `Ξ`. The convergence is all that
  Proposition 6.1 requires.
- Containment of the non-maverick points in an analytic curve proves the
  Hausdorff-dimension upper bound in 1.14. Keep a separate lower-bound proof.
- The estimate behind Lemma 8.2 must control the measure of the limsup set;
  decay of the individual measures alone does not suffice.
- A capacity-zero hypothesis must refer to the standard capacity, with the
  correct extended logarithmic kernel, not to a definition tailored to Evans.

These are implementation obligations and clarifications, not newly verified
Lean results. The feasibility document labels alternative proof routes as
proposals so that a future session can test them without mistaking them for
completed lemmas.
