# Proof dependency audit

PaperSolution imports 770 local source modules transitively.

| Source group | Modules |
|---|---:|
| BoundedWanderingDomains | 357 |
| CoveringSolution.lean | 1 |
| EremenkoLyubichConstant | 18 |
| PaperSolution.lean | 1 |
| RMT4 | 2 |
| Ray | 55 |
| RiemannDynamics | 46 |
| dependencies/ComplexApproximation | 28 |
| dependencies/ComplexDynamics | 3 |
| dependencies/EremenkosConjecture | 139 |
| dependencies/FunctionTheory | 120 |

Each module and its normalized source hash is listed in paper-submission.json.
Pinned Mathlib and Lean/core modules are excluded from these local counts.
The import audit removed unused local modules from the paper closure;
they remain checked by the optional full build. All four active local dependency
packages are needed by the proof. See BUILD_AUDIT.md for the full audit.
