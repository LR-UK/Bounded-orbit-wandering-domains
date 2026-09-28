# Absence of bounded-orbit wandering domains

This project formalises the absence of bounded-orbit wandering domains of
transcendental entire and meromorphic functions, answering a major open question
in complex dynamics. It extends the
[first registered formalisation](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000001&version=1),
which formalised the main results of:

[PRW] N. Prochorov, L. Rempe and J. Waterman, *Absence of bounded-orbit wandering
domains*, [arXiv:2609.28279](https://arxiv.org/abs/2609.28279).

The current formalisation preserves the result on the absence of bounded-orbit wandering
domains (referred to as Theorem 1.2 entire), adds the meromorphic case that was not
stated in the previous version, although it follows from the results proved there
(referred to as Theorem 1.2 meromorphic) and adds the following.

- The derived-set theorem announced without proof in [PRW]: for a transcendental
  entire function, every point in a wandering Fatou component has a subsequence
  of its orbit converging to the derived set of the spherical singular values.
  This result is referred to hereafter as Theorem 1.4. Učakar has informed the
  authors that he independently obtained a proof of this theorem.
- The local result with unnecessary hypotheses removed, on arbitrary Riemann
  surfaces: if an open holomorphic map is defined on an open subset $O$ of a
  Riemann surface and $U$ is a wandering normality component, no point of $U$
  has its whole forward orbit contained in a compact subset of $O$.
  Referred to hereafter as Theorem 1.3(1)
- A surface analogue of the derived-set theorem for arbitrary wandering
  normality components, including multiply connected ones; referred to as
  Theorem 1.5. Version 1.5.0 removes the simple-connectivity hypothesis by
  formalising an adaptation of the Baker–Kotus–Lü covering and filling argument.
- The positive-area statement, previously present for subsets of the sphere in
  the manuscript but absent from the first formalisation. If $A$ is measurable,
  has positive area in a chart, lies outside the normality locus, has all iterates
  defined in $O$, has pairwise disjoint forward images, and the map is injective
  on the whole forward saturation of $A$, that saturation is not contained in
  a compact subset of $O$; referred to as Theorem 1.3(2).
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

The authors of [PRW] and [DPU] have agreed to combine their efforts and are preparing a joint preprint
containing all the results formalised here.

This unconditional formalisation was prepared with generative AI for submission
to Palomar, based on [PRW], the new statements, proof sketches and prompts by
Lasse Rempe. Several classical supporting results were newly formalised.
The precise mathematical scope and verification status are given below.

## Formalised statements

All the above statements are proved in Lean.
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
| Compact Riemann surface self-maps: no wandering domains. (Only the spherical case is actually non-trivial.) | `SurfaceDynamics.no_wandering_domains_compact` |
| Rational maps: no wandering domains | `SurfaceDynamics.no_wandering_domains_rational` |

The surface statements apply to arbitrary Riemann surfaces and actual local
open holomorphic maps. Compact sets in Theorem 1.3 lie inside the map's source.
Theorem 1.5 also applies to multiply connected normality components.
Meromorphic maps may have poles. See [PAPER_STATEMENT_ALIGNMENT.md](docs/PAPER_STATEMENT_ALIGNMENT.md) for the
precise hypotheses and [PAPER_PROOF_GUIDE.md](docs/PAPER_PROOF_GUIDE.md) for the proof route.

The ten theorem types and 35 supporting declarations match the independent
challenge. The transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`; 777 local proof modules were scanned for holes and shortcuts.
The complete build also verifies the retained earlier results.

The rational-map corollary is stated intrinsically for open holomorphic maps
on the whole Riemann sphere, including poles and infinity. Its proof specialises
the compact-surface theorem; it does not require a polynomial-quotient encoding.
The finite-type entire corollary explicitly assumes transcendence and finiteness
of the finite singular-value set. No separate finite-type meromorphic
no-wandering corollary is selected in the current challenge.

Theorem 1.5 now uses a local adaptation of the covering and filling argument in:

[BKL] I. N. Baker, J. Kotus and Y. Lü, *Iterates of Meromorphic Functions IV:
Critically Finite Functions*, Results in Mathematics 22 (1992), 651–656,
[doi:10.1007/BF03323112](https://doi.org/10.1007/BF03323112).

The proof uses the full preimages of regular punctured discs, fills removable
points, and controls the backward orbits of finitely many singular values.
It proves eventual injectivity on each fixed-radius covering disc inside the
wandering components, which is sufficient for the area argument. The new
supporting proofs are grouped into six files in
`BoundedWanderingDomains/Surfaces/BKL/`.

## Project layout

The only top-level Lean files are the two current submission files.

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
names. The original entire-function statement retains its exact declaration name and
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
the retained earlier and research results. Fetch the pinned dependency cache
before the first build; a build without it may compile Mathlib from source.
Keep the `.lake` directory when updating an existing checkout so that unchanged
dependencies remain cached.

The metadata checker requires PyYAML. On Windows, use UTF-8 Python mode for
the older attribution script (`python -X utf8 scripts/audit_attribution.py`).
For the official sandboxed comparison and bundled independent kernels, use
Linux with working bubblewrap user namespaces:

```sh
bash scripts/verify-comparator.sh comparator.json
```

`comparator.json` selects all ten targets. Challenge `sorry` placeholders are
intentional specifications and are never imported by the proofs.

See [VERIFICATION.md](docs/VERIFICATION.md) for actual check results and the distinction
between local verification and official registry verification.

## Sources and authorship

Mathematical direction: Lasse Rempe. Paper authors: Nikolai Prochorov,
Lasse Rempe and James Waterman. AI-assisted formalisation: OpenAI ChatGPT/Codex.
The current manuscript source is `handoff/reference/no-bounded-WD-2.tex`.
Third-party proofs retain their authorship and licences; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), [LICENSE](LICENSE), and
`formalization.yaml`. Local path dependencies are included in the source
archive; Mathlib and its pinned dependencies are fetched by Lake. Caches are
not distributed. Earlier status documents are historical, not current scope.
