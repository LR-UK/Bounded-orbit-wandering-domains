# Absence of bounded-orbit wandering domains

All six statements from the revised paper introduction are proved in Lean.
The independent specifications are in [PaperChallenge.lean](PaperChallenge.lean);
the proofs are exposed by [PaperSolution.lean](PaperSolution.lean).

| Paper statement | Proved declaration |
|---|---|
| Theorem 1.2, entire escape | `BoundedWanderingDomains.theorem_1_2_entire` |
| Theorem 1.2, meromorphic escape | `MeromorphicDynamics.theorem_1_2_meromorphic` |
| Theorem 1.3(1), surface compact-orbit exclusion | `SurfaceDynamics.theorem_1_3_orbit` |
| Theorem 1.3(2), positive-area wandering sets | `SurfaceDynamics.theorem_1_3_positive_area` |
| Theorem 1.4, entire derived singular accumulation | `BoundedWanderingDomains.theorem_1_4` |
| Theorem 1.5, surface escape or derived singular accumulation | `SurfaceDynamics.theorem_1_5` |

The surface statements apply to arbitrary Riemann surfaces and actual local
open holomorphic maps. Compact sets in Theorem 1.3 lie inside the map's source.
Simple connectivity is required only by Theorem 1.5. Meromorphic maps may have
poles. See [PAPER_STATEMENT_ALIGNMENT.md](PAPER_STATEMENT_ALIGNMENT.md) for the
precise hypotheses and [PAPER_PROOF_GUIDE.md](PAPER_PROOF_GUIDE.md) for the proof route.

The six theorem types and 36 supporting declarations match the independent
challenge. The transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`; 773 local proof modules were scanned for holes and shortcuts.
The complete build also verifies the retained earlier results.

## Build and check

Lean: `leanprover/lean4:v4.35.0-rc2`. Mathlib:
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
python3 scripts/fetch_cache.py
lake build
python3 scripts/verify_paper.py
python3 scripts/verify_metadata.py
python3 scripts/audit_attribution.py
```

The metadata checker requires PyYAML. On Windows, use UTF-8 Python mode for
the older attribution script (`python -X utf8 scripts/audit_attribution.py`).
For the official sandboxed comparison and bundled independent kernels, use
Linux with working bubblewrap user namespaces:

```sh
bash scripts/verify-comparator.sh comparator.json
```

`comparator.json` and `comparator-paper.json` select the six revised-paper
targets. `comparator-legacy.json` and `comparator-singular-limits.json` preserve
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
