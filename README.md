# Absence of bounded-orbit wandering domains

This project formalises the absence of bounded-orbit wandering domains of
transcendental entire and meromorphic functions, answering a major open question
in complex dynamics. It extends the
[first registered formalisation](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000001&version=1),
which formalised the main results of:

[PRW] N. Prochorov, L. Rempe and J. Waterman, *Absence of bounded-orbit wandering
domains*, [arXiv:2609.28279](https://arxiv.org/abs/2609.28279).

The current formalisation preserves the original entire-function bounded-orbit
statement unchanged and includes the following results.

- **Entire and meromorphic escape:** a wandering Fatou component has a
  subsequence of iterates converging locally uniformly to infinity.
- **Entire derived-singular accumulation:** every wandering point has an orbit
  subsequence converging to the derived set of the spherical singular values.
  This proves the assertion announced without proof in [PRW]. Učakar has informed
  the authors that he independently obtained a proof of this theorem.
- **Local compact-orbit exclusion:** for an open holomorphic map on an open
  subset $O$ of a Riemann surface, no wandering normality component contains a
  point whose whole orbit stays in a compact subset of $O$.
- **Local derived-singular accumulation:** every wandering orbit has a
  subsequence escaping ambient compact sets or converging to a derived singular
  value. This includes multiply connected components, using the formalised
  Baker–Kotus–Lü covering and filling argument. If the orbit stays in an ambient
  compact set, a derived-singular subsequential limit lies in that set.
- **Positive-area and almost-everywhere results:** let $A$ be a measurable set
  in the infinite-iteration locus, outside the normality locus, with pairwise
  disjoint forward images and each iterate injective on $A$. Almost every point
  of $A$ has a subsequence escaping every compact subset of $O$. Moreover,
  almost every point has a subsequence escaping ambient compact sets or
  converging to a derived singular value of the actual local map. The compact-set
  formulations are retained: a positive-area forward saturation cannot stay in
  a source compact set, or in an ambient compact set avoiding derived singular
  values. Almost everywhere means outside a Lebesgue-null set in every chart;
  no global surface measure is chosen.
- **Finite-type no-wandering theorem:** an open holomorphic map from an open
  subset of a compact Riemann surface to that surface has no wandering normality
  components if its singular set is finite. This recovers a theorem of Adam Epstein. 
  It follows directly from the local derived-singular theorem.
- **Classical no-wandering corollaries:** rational maps, compact Riemann surface
  self-maps, and class S entire and meromorphic functions have no wandering
  domains. All are deduced from the finite-type theorem. The explicit plane
  corollaries treat transcendental functions; polynomials and rational functions
  are covered by the intrinsic rational-map statement.

All escape conclusions above refer to subsequences where stated; they do not
assert that the full orbit eventually leaves every compact set forever.

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

The authors of [PRW] and [DPU] have agreed to combine their efforts and are preparing a joint preprint,
which is expected to contain all the results formalised here.

This unconditional formalisation was prepared with generative AI for submission
to Palomar, based on [PRW], the new statements, proof sketches and prompts by
Lasse Rempe. Several classical supporting results were newly formalised.
The precise mathematical scope and verification status are given below.

## Formalised statements

All the above statements are proved in Lean.
The independent specifications are in [Challenge.lean](Challenge.lean);
the proofs are exposed by [Solution.lean](Solution.lean). The original
entire-function bounded-orbit theorem is also included under its unchanged name
and statement. The current challenge selects sixteen theorem declarations, with descriptive
names independent of unpublished manuscript numbering.

| Paper statement | Proved declaration |
|---|---|
| Finite-type local maps on compact surfaces: no wandering domains | `SurfaceDynamics.no_wandering_domains_finite_type` |
| Class S transcendental meromorphic functions: no wandering domains | `MeromorphicDynamics.no_wandering_domains_transcendental_meromorphic_finite_singularValues` |
| Entire escape | `BoundedWanderingDomains.wandering_domain_has_locally_uniform_escaping_subsequence` |
| Meromorphic escape | `MeromorphicDynamics.wandering_domain_has_locally_uniform_escaping_subsequence` |
| Local compact-orbit exclusion | `SurfaceDynamics.wandering_component_orbit_not_compactly_contained` |
| Positive-area compact-source exclusion | `SurfaceDynamics.positive_area_wandering_saturation_not_compactly_contained` |
| Entire derived-singular accumulation | `BoundedWanderingDomains.wandering_orbit_accumulates_on_derived_singular_values` |
| Local escape or derived-singular accumulation | `SurfaceDynamics.wandering_orbit_has_escaping_or_derived_singular_subsequence` |
| Original entire-function bounded-orbit theorem (unchanged) | `BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire` |
| Finite-type transcendental entire functions: no wandering domains | `BoundedWanderingDomains.no_wandering_domains_transcendental_entire_finite_singularValues` |
| Compact Riemann surface self-maps: no wandering domains. (Only the spherical case is actually non-trivial.) | `SurfaceDynamics.no_wandering_domains_compact` |
| Rational maps: no wandering domains | `SurfaceDynamics.no_wandering_domains_rational` |
| Compact wandering orbit: derived-singular limit in the compact set | `SurfaceDynamics.compact_wandering_orbit_accumulates_on_derived_singular_values` |
| Almost-everywhere source escape | `SurfaceDynamics.almost_every_wandering_point_has_source_escaping_subsequence` |
| Positive-area compact exclusion away from derived singular values | `SurfaceDynamics.positive_area_wandering_saturation_not_compactly_contained_away_from_derived` |
| Almost-everywhere ambient escape or derived-singular accumulation | `SurfaceDynamics.almost_every_wandering_point_has_escaping_or_derived_singular_subsequence` |

The local escape and derived-singular statements apply to arbitrary Riemann
surfaces and actual local open holomorphic maps. The finite-type no-wandering
theorem assumes that the ambient surface is compact, as in Epstein's setting. The original compact-orbit exclusion concerns compact
subsets of the source; the derived-singular compact versions allow compact
subsets of the ambient surface. No simple-connectivity hypothesis is imposed.
Meromorphic maps may have poles. See [statement alignment](docs/PAPER_STATEMENT_ALIGNMENT.md)
for the precise hypotheses and [proof guide](docs/PAPER_PROOF_GUIDE.md) for the proof route.

The independent challenge and solution are compared declaration by declaration.
The transitive axiom and source audits are recorded in [verification](docs/VERIFICATION.md).
The complete build also checks the retained earlier results.

The rational-map corollary is stated intrinsically for open holomorphic maps
on the whole Riemann sphere, including poles and infinity. Its proof specialises
the compact-surface theorem; it does not require a polynomial-quotient encoding.
The finite-type entire corollary explicitly assumes transcendence and finiteness
of the finite singular-value set. The meromorphic corollary uses the genuine
sphere-valued map, sending poles to infinity. Its singular set is the complement
of values with a surjectively covered neighbourhood, so omitted values are
included. Finiteness is equivalent to finiteness of the finite singular values.
Both plane corollaries transport actual Fatou components to the local sphere
model before applying the general finite-type theorem.

The finite-type no-wandering theorem is due to Adam Epstein, *Towers of finite
type complex analytic maps*, PhD thesis, CUNY (1993). Here it is obtained as a
corollary of the derived-singular theorem, rather than by formalising Epstein's
original deformation argument. See also [Epstein's course description](https://pi.math.cornell.edu/m/Courses/GradCourses/SP00/722).

The local derived-singular theorem uses a local adaptation of the covering and filling argument in:

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
Challenge.lean        All sixteen current statements
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

`comparator.json` selects all sixteen targets. Challenge `sorry` placeholders are
intentional specifications and are never imported by the proofs.

See [VERIFICATION.md](docs/VERIFICATION.md) for actual check results and the distinction
between local verification and official registry verification.

## Sources and authorship

Mathematical direction: Lasse Rempe. Paper authors: Nikolai Prochorov,
Lasse Rempe and James Waterman. AI-assisted formalisation: OpenAI ChatGPT/Codex.
Current statements use descriptive names; their scope is recorded in the public
challenge and statement-alignment document.
Third-party proofs retain their authorship and licences; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), [LICENSE](LICENSE), and
`formalization.yaml`. Local path dependencies are included in the source
archive; Mathlib and its pinned dependencies are fetched by Lake. Caches are
not distributed. Earlier status documents are historical, not current scope.
