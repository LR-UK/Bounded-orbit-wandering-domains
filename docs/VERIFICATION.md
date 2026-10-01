# Verification — version 1.9.0, 1 October 2026

The configured Lean build passed for `Challenge`, `Solution` and
`BoundedWanderingDomains.All`. All 19 selected theorem declarations and 53
supporting declarations agree between the independent Challenge and Solution.
The local surface statements now allow disconnected ambient complex
one-manifolds. No finite-component or component-itinerary hypothesis is added
to the public statements. The original entire-function theorem and all entire,
meromorphic and rational specializations retain their previous declarations.

The pinned Comparator declaration-comparison core also passed, using the
compiled Challenge and Solution environments. This local test does not run
the Linux sandboxed export pipeline or the bundled independent kernels.
Those checks must run in GitHub/Palomar after upload; local success is not a
claim of registry acceptance.

Every selected proof uses only `propext`, `Classical.choice` and `Quot.sound`.
There are zero ordinary compiler or linter warnings. The 19 intentional
`sorry` warnings belong exclusively to the independent Challenge specifications;
the proof library never imports Challenge. No linter was disabled.

The solution closure contains 775 local proof modules. Including the optional
proof-library entry point, 776 modules passed the source scan for proof holes,
custom axioms, `native_decide` and imports of independent challenges. All
1335 retained Lean sources pass the module-header check. Unused vendored
modules are retained for attribution/source completeness and are not claimed
to have been compiled by these checks.

The disconnected proof replaces the separate compact and noncompact area
branches. Relative to the author's previous checkout, 54 obsolete Lean files
are removed and 50 componentwise geometry/reduction files are added.
The proof guide explains the finite clopen reductions and componentwise
covering, area and BKL arguments.

Metadata contract, attribution and source-structure audits passed. Attribution
checks cover 12 licence texts, 51 attribution files and
274 vendored headers. Epstein's thesis is now recorded as
`independently-proves`, retaining the note that its deformation argument is
not formalised here.

## Reproduce the checks

```sh
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_structure.py
python3 -X utf8 scripts/audit_attribution.py
```

The metadata checker needs PyYAML. For a fresh checkout, first run
`python3 scripts/fetch_cache.py`. Preserve all `.lake` directories when updating.
Lean remains `leanprover/lean4:v4.35.0-rc2`; Mathlib remains
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Changed project modules rebuild;
unchanged dependencies remain cached. The recorded recheck timings use existing
compiled artifacts and do not estimate a fresh build or another computer.

For the complete official comparison on Linux with working bubblewrap namespaces:

```sh
bash scripts/verify-comparator.sh comparator.json
```

Evidence is recorded in `verification/disconnected-release.json`,
`verification/paper-submission.json`, the declaration and axiom logs,
`verification/disconnected-comparator-core.log`, and the metadata, structure,
module-header and attribution reports.
