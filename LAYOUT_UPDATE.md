# Current submission layout - version 1.4.3

Only `Challenge.lean` and `Solution.lean` are at the project root.
`Challenge.lean` contains all six revised-paper statements and the original
entire-function bounded-orbit theorem, for seven compared theorem declarations.
The retained theorem has exactly the same name and hypotheses as before:
`BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire`.

`Solution.lean` exposes the corresponding proofs. The original theorem's proof
is shared with `Legacy/Solution.lean` through
`BoundedWanderingDomains/EntireBoundedOrbit.lean`; there is one copy of the proof.
The earlier complete challenge/solution pairs remain in `Legacy/`.
Optional entry points remain in `Research/`, and the main proof libraries remain
in their existing folders.

## Import and build names

The preceding version's `PaperChallenge` and `PaperSolution` are now `Challenge`
and `Solution`. Update such imports in your own Lean files. The primary
configuration remains `comparator.json`; `comparator-paper.json` is identical.
`lake build` builds the current pair; `python3 scripts/verify_paper.py --all`
also checks the retained legacy and research results.

The earlier supporting-file moves are:

| Previous module | Current module |
|---|---|
| `BoundedWanderingDomains` | `BoundedWanderingDomains.All` |
| `CoveringSolution` | `BoundedWanderingDomains.CoveringSolution` |
| `Challenge` | `Legacy.Challenge` |
| `Solution` | `Legacy.Solution` |
| `SingularLimitsChallenge` | `Legacy.SingularLimitsChallenge` |
| `SingularLimitsSolution` | `Legacy.SingularLimitsSolution` |
| `NewResults` | `Research.NewResults` |
| `SurfaceDynamicsTargets` | `Research.SurfaceDynamicsTargets` |
| `SurfaceFiniteRemoval` | `Research.SurfaceFiniteRemoval` |
| `SurfaceGeometry` | `Research.SurfaceGeometry` |
| `SurfaceKernel` | `Research.SurfaceKernel` |
| `SurfaceResearch` | `Research.SurfaceResearch` |

The earlier `lake build Submission` target is now `lake build Legacy.Solution`.
The earlier `Challenge`/`Solution` pair in that table predates the revised-paper
pair; its files are preserved under `Legacy/`. The current root files contain
the consolidated submission.

## Verification and historical reports

See VERIFICATION.md and `verification/submission-consolidation.json` for current
checks, including comparison with the previous compiled statement types.
`verification/paper-submission.json` is the main current audit report.
`verification/layout-audit.json` and `history/layout-1.4.2.md` describe the
preceding directory-only update. BUILD_AUDIT.md and `verification/build-audit.json`
describe the earlier version 1.4.1 performance audit.

The reorganisation itself is not a first-build speed optimisation. Renamed
entry points may need a one-time rebuild; supporting compiled modules can be reused.
