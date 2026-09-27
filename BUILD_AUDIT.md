# Build and duplication audit — version 1.4.1

The six completed paper theorem statements are unchanged. The audit reduces
unnecessary imports and repeated checking work, retains earlier proved results,
and preserves all licences, attribution and pinned dependencies.
Baseline: `bd33758d645a9e48cec3e8d2c9abd9d0dfbba0dd` (completed version 1.4.0).

## What changed

- Replaced **22** complete `Mathlib.Tactic` imports with specific mathematical
  and tactic imports. Missing dependencies exposed by this cleanup were made explicit.
- Removed **498** informational axiom-print commands from proof source files.
  The paper import closure previously contained **393**; it now contains **0**.
  The six mandatory transitive axiom checks remain in the central audit.
- Reduced PaperSolution's direct imports **8 → 5** and SurfaceResearch's
  **102 → 12**, preserving the full build's **795** local modules.
- Narrowed five local imports and made downstream dependencies explicit. The
  paper closure fell **773 → 770**. The 3 modules no longer
  needed by the paper remain available through
  the optional SurfaceResearch build, and were rebuilt in the full check.
- Consolidated **eight** duplicate proof bodies: two compact-disc lemmas, four
  finite-removal lemmas, the finite-area cancellation lemma, and the trapped-set
  interior lemma. Each now invokes its existing counterpart; every public name
  and exact statement type remains available.
- Made the two paper entry points the default build. `verify_paper.py --all`
  and CI retain the full build of earlier and research entry points. The `--all`
  check also scans all retained proof source closures for holes and shortcuts.
- Combined the solution declaration export and six axiom reports into one Lean
  process. The audit also rejects a missing comparison record, removes a stale
  success report before rechecking, and records command timings.
- Removed the unused whole-library umbrella from cache-fetch roots. Added the
  optional `scripts/audit_structure.py` to reproduce the source inventory.

The eight consolidated declarations are:

| Public name retained | Existing result now used |
|---|---|
| `mem_interior_trapped_of_not_mem_barrier` | `trapped_outside_barrier_is_interior` |
| `finite_area_cancellation` | `finite_area_cancellation_le` |
| `unitDisc_closed_ball_compact` | `unitDisc_closed_radius_compact` |
| `unitDisc_maps_compact_closed_ball` | `unitDisc_maps_compact_radius` |
| `uniform_compact_finite_removal_gain_le` | `uniform_compact_finite_removal_gain` |
| `uniform_compact_finite_remote_removal_gain_le` | `uniform_compact_finite_remote_removal_gain` |
| `uniform_compact_finite_remote_area_le` | `uniform_compact_finite_remote_area` |
| `uniform_compact_finite_remote_removal_gain_le_all_covers` | `uniform_compact_finite_remote_removal_gain_all_covers` |

## Measurements

| Command | Before | After | Time reduction |
|---|---:|---:|---:|
| Cached `lake build` | 27.67 s | 20.67 s | 25.3% |
| Lean frontend on `PaperSolution.lean` | 76.27 s | 71.47 s | 6.3% |
| Lean frontend on unchanged `PaperChallenge.lean` (control) | 57.48 s | 57.21 s | 0.5% |

These are single local warm-cache measurements with the same pinned compiler
and two Lean workers, with no concurrent Lean build during measurement. They
are observations, not a stable performance guarantee. The default build now
selects the paper entry points, so its comparison includes that deliberate
scope change. The unchanged challenge is included as a control for timing
variation. No clean-build speedup percentage is claimed.

The PaperSolution setup lists **4653 → 4271**
imported module artifacts, including Lean/core and external dependencies.
This count differs from the local source-module count. Reducing these imports
and removing repeated axiom traversals reduces work on future rebuilds; the
one-time rebuild needed to validate the audit is not an incremental benchmark.

## Checks completed

- Full retained build passed: **4326 Lake jobs**, **795 local modules**.
- All **6** headline theorem types and **36** supporting declarations match the
  independent challenge. Definition bodies and the local-map constructor are included.
- All six transitive axiom reports use only `propext`, `Classical.choice`, and
  `Quot.sound`. All **770** local paper proof modules, and **792**
  proof modules across the full build, passed the shortcut scan.
- A supplementary comparison retained all **8635**
  distinct previously imported theorem declarations, including the modules moved
  to the optional build. **8630**
  canonical compiled types have identical hashes. Five types use different
  automatically selected instance expressions after import narrowing. For each,
  the original compiled type was recreated and matched against its pre-audit
  hash, and the Lean kernel accepted the current theorem as a proof of that
  original type. No incompatible type change remains.
  Hash comparison is supporting evidence; it does not replace Lean checking or
  the exact independent comparison of the 42 paper declarations.
- Every changed Lean source was compared after ignoring comments, whitespace,
  imports and diagnostic commands. Only the eight intentional proof-body
  consolidations differ. No theorem statement was edited.
- The complete source inventory covers **1371** Lean files.
  The only proof placeholders are the intentional independent specifications
  in Challenge, PaperChallenge and SingularLimitsChallenge.
- Attribution passed: **12** licence texts, **51** attribution files and
  **274** vendored author headers. FunctionTheory's module map was refreshed.

## Material retained and limits

The audit inspected the complete source inventory, import graph, diagnostics,
normalized source duplicates and compiled theorem records, including equal
statement types whose proof text differs. Shared mathematical
foundations are already compiled once per module. They are not duplicate proof
work merely because several final theorems use them.

Unused parts of reusable dependencies, standalone audit scripts and historical
provenance were retained outside the paper build; deleting those files would
give no Lean build-time saving. Small public compatibility wrappers were kept
to preserve existing interfaces while sharing proofs.
The one exact source-file duplicate after ignoring comments is the archived
FunctionTheory umbrella and its active counterpart; the archive is not imported.
Four standalone dependency audit files share the module spelling `scripts.Audit`
in their separate projects. None is in an active root import closure.

The separate FunctionTheory verification was attempted, but fetching its own
Mathlib checkout failed with an SSL certificate error before compilation. Its
active imported modules were checked by the root build using the existing
pinned cache; no full standalone dependency-audit pass is claimed.

Official sandboxed Comparator and independent-kernel replay still require the
included Linux workflow. The current metadata checker requires PyYAML, which
is absent from the local runtime. No upload, registry acceptance or independent
human review is claimed. See VERIFICATION.md for those existing limits.

`verification/build-audit.json` contains counts and timings;
`verification/structure-audit.json` contains the reproducible full inventory.
