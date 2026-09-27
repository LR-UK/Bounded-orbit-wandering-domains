# Absence of bounded-orbit wandering domains

This project formalises the absence of bounded-orbit wandering domains of
transcendental entire and meromorphic functions, answering a major open question
in complex dynamics. It extends the
[first registered formalisation](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000001&version=1),
which formalised the main results of:

[PRW] N. Prochorov, L. Rempe and J. Waterman, *Absence of bounded-orbit wandering
domains*, [arXiv:2609.28279](https://arxiv.org/abs/2609.28279).

The current formalisation preserves those results and adds the following.

- The derived-set theorem announced without proof in [PRW]: for a transcendental
  entire function, every point in a wandering Fatou component has a subsequence
  of its orbit converging to the derived set of the spherical singular values.
- The local result with unnecessary hypotheses removed, on arbitrary Riemann
  surfaces: if an open holomorphic map is defined on an open subset $O$ of a
  Riemann surface and $U$ is a wandering normality component, no point of $U$
  has its whole forward orbit contained in a compact subset of $O$.
- A surface analogue of the derived-set theorem, currently assuming that the
  normality components met by the wandering orbit are simply connected.
- The positive-area statement, previously present for subsets of the sphere in
  the manuscript but absent from the first formalisation. If $A$ is measurable,
  has positive area in a chart, lies outside the normality locus, has all iterates
  defined in $O$, has pairwise disjoint forward images, and the map is injective
  on the whole forward saturation of $A$, that saturation is not contained in
  a compact subset of $O$.
- Classical no-wandering corollaries for rational maps and transcendental entire
  functions with finitely many singular values, together with the more general
  compact-surface corollary. The polynomial case is included among rational maps.

The spherical singular set of an entire function means its finite singular
values together with infinity; its derived set consists of its accumulation
points. The normality locus $\Omega(f)$ consists of points with a neighbourhood
on which all iterates are defined and form a normal family.

Following [PRW], two further preprints announced the absence of bounded-orbit
wandering domains:

- [DPU] K. Drach, L. Pardo-Simón and B. Učakar, *Bounded-orbit wandering domains do
  not exist*, [arXiv:2609.30103](https://arxiv.org/abs/2609.30103).
- [Y2] Z. Ye, *Hyperbolic Area Methods in Meromorphic Dynamics and Elliptic
  Polynomial Skew Products*, [arXiv:2609.30067](https://arxiv.org/abs/2609.30067).

All three proofs rely on the earlier preprint [Y1] Z. Ye, *A new proof of
no-wandering domain theorems without quasiconformal techniques*,
[arXiv:2609.23834](https://arxiv.org/abs/2609.23834). All four preprints acknowledge
generative AI in the generation of their proofs.

As reported by Lasse Rempe on 27 September 2026, the authors of [PRW] and [DPU]
have agreed to combine their efforts and are preparing a joint preprint
containing all the results formalised here.

This unconditional formalisation was prepared with generative AI for submission
to Palomar, based on [PRW], the new statements, proof sketches and prompts by
Lasse Rempe. Several classical supporting results were newly formalised.
The precise mathematical scope and verification status are given below.

## Formalised statements

All six statements from the revised paper introduction are proved in Lean.
The independent specifications are in [Challenge.lean](Challenge.lean);
the proofs are exposed by [Solution.lean](Solution.lean). The original
entire-function bounded-orbit theorem is also included under its unchanged name
and statement. With the three no-wandering corollaries, the current challenge
selects ten theorem declarations.

| Paper statement | Proved declaration |
|---|---|
| Theorem 1.2, entire escape | `BoundedWanderingDomains.theorem_1_2_entire` |
| Theorem 1.2, meromorphic escape | `MeromorphicDynamics.theorem_1_2_meromorphic` |
| Theorem 1.3(1), surface compact-orbit exclusion | `SurfaceDynamics.theorem_1_3_orbit` |
| Theorem 1.3(2), positive-area wandering sets | `SurfaceDynamics.theorem_1_3_positive_area` |
| Theorem 1.4, entire derived singular accumulation | `BoundedWanderingDomains.theorem_1_4` |
| Theorem 1.5, surface escape or derived singular accumulation | `SurfaceDynamics.theorem_1_5` |
| Original entire-function bounded-orbit theorem (unchanged) | `BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire` |
| Finite-type transcendental entire functions: no wandering domains | `BoundedWanderingDomains.no_wandering_domains_transcendental_entire_finite_singularValues` |
| Compact Riemann surface self-maps: no wandering domains | `SurfaceDynamics.no_wandering_domains_compact` |
| Rational maps: no wandering domains | `SurfaceDynamics.no_wandering_domains_rational` |

The surface statements apply to arbitrary Riemann surfaces and actual local
open holomorphic maps. Compact sets in Theorem 1.3 lie inside the map's source.
Simple connectivity is required only by Theorem 1.5. Meromorphic maps may have
poles. See [PAPER_STATEMENT_ALIGNMENT.md](PAPER_STATEMENT_ALIGNMENT.md) for the
precise hypotheses and [PAPER_PROOF_GUIDE.md](PAPER_PROOF_GUIDE.md) for the proof route.

The ten theorem types and 36 supporting declarations match the independent
challenge. The transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`; 772 local proof modules were scanned for holes and shortcuts.
The complete build also verifies the retained earlier results.

The rational-map corollary is stated intrinsically for open holomorphic maps
on the whole Riemann sphere, including poles and infinity. Its proof specialises
the compact-surface theorem; it does not require a polynomial-quotient encoding.
The finite-type entire corollary explicitly assumes transcendence and finiteness
of the finite singular-value set. No finite-type meromorphic no-wandering
corollary is claimed. The relation with the Baker–Kotus–Lü argument, especially
for multiply connected meromorphic wandering domains, remains a separate question.

## Project layout

Only the two current submission files are at the top level:

```text
Challenge.lean        All ten current statements
Solution.lean         Proved versions of those statements
BoundedWanderingDomains/   Main proof library, including CoveringSolution.lean
RiemannDynamics/           Meromorphic dynamics proofs
RMT4/, Ray/, EremenkoLyubichConstant/   Supporting libraries
Legacy/                   Earlier challenge and solution pairs
Research/                 Optional entry points for additional results
verification/             Audit sources, reports and logs
dependencies/             Contained source dependencies
```

The earlier entry points remain available under their folder-qualified module
names. See [LAYOUT_UPDATE.md](LAYOUT_UPDATE.md) for the complete path mapping.
The original entire-function statement retains its exact declaration name and
hypotheses. The current and legacy solutions share its proof.

## Build and check

Lean: `leanprover/lean4:v4.35.0-rc2`. Mathlib:
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
python3 scripts/fetch_cache.py
lake build
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_attribution.py
```

`lake build` builds the two paper entry points. The `--all` audit also builds
the retained earlier and research results. See [BUILD_AUDIT.md](BUILD_AUDIT.md)
for the import, duplication and performance audit.

The metadata checker requires PyYAML. On Windows, use UTF-8 Python mode for
the older attribution script (`python -X utf8 scripts/audit_attribution.py`).
For the official sandboxed comparison and bundled independent kernels, use
Linux with working bubblewrap user namespaces:

```sh
bash scripts/verify-comparator.sh comparator.json
```

`comparator.json` and `comparator-paper.json` select all ten
targets (six revised-paper statements, the original entire theorem, and three
no-wandering corollaries). `comparator-legacy.json` and `comparator-singular-limits.json` preserve
the earlier independent comparisons. Challenge `sorry` placeholders are
intentional specifications and are never imported by the proofs.

See [VERIFICATION.md](VERIFICATION.md) for actual check results and the distinction
between local verification and official registry verification. Nothing has been
pushed or submitted. [GITHUB_UPDATE.md](GITHUB_UPDATE.md) and
[SUBMISSION.md](SUBMISSION.md) describe the prepared upload workflow.

## Sources and authorship

Mathematical direction: Lasse Rempe. Paper authors: Nikolai Prochorov,
Lasse Rempe and James Waterman. AI-assisted formalisation: OpenAI ChatGPT/Codex.
The current manuscript source is `handoff/reference/no-bounded-WD-2.tex`.
Third-party proofs retain their authorship and licences; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), [LICENSE](LICENSE), and
`formalization.yaml`. Local path dependencies are included in the source
archive; Mathlib and its pinned dependencies are fetched by Lake. Caches are
not distributed. Earlier status documents are historical, not current scope.
