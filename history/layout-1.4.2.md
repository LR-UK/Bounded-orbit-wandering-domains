# Project layout update - version 1.4.2

Only `PaperChallenge.lean` and `PaperSolution.lean` remain as top-level Lean files.
These are still the current challenge and solution for the six paper theorems.
The Comparator settings, declaration names, hypotheses and proof bodies are unchanged.

Twelve supporting or earlier entry points were moved:

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

A module name such as `Legacy.Solution` corresponds to `Legacy/Solution.lean`.
Imports, Lake targets, verification scripts and the earlier Comparator configurations
now use these names. Mathematical namespaces and theorem names are unchanged.
If your own Lean files import one of the moved modules, update only that import
using the table above. `import PaperSolution` continues to work.
The old `lake build Submission` target becomes `lake build Legacy.Solution`.

`lake build` still builds the two current paper entry points.
`python3 scripts/verify_paper.py --all` also builds the retained earlier and
research results. The folder move itself is not a compilation-speed optimisation;
previously compiled files affected by the move may need rebuilding once.

## Validation

The complete retained build passed again, as did the exact comparison of all
six paper theorem types and 36 supporting declarations, and the transitive
axiom checks. Both older challenge/solution comparisons also passed under
their new names. All import-closure memberships are preserved.

The source comparison against commit `5dc6917882a38a985051ff36df21e91cdde9cc37` checks every Lean source
after accounting for file moves and import-path changes. No Lean statement or
proof body was edited; all 1,371 Lean source files and third-party sources are
preserved. The current paper files are unchanged. See
`verification/layout-audit.json` and VERIFICATION.md for the completed build
and declaration checks.

BUILD_AUDIT.md and `verification/build-audit.json` document the earlier version
1.4.1 performance audit. Their original module names and timings are historical.
The fresh reports are `verification/paper-submission.json`,
`verification/structure-audit.json` and `verification/layout-audit.json`.
