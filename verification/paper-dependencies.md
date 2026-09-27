# Proof dependency audit

PaperSolution imports 770 local source modules transitively.

| Source group | Modules |
|---|---:|
| BoundedWanderingDomains | 358 |
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
All four active local dependency packages are needed by the proof. The layout
update preserves the same module closure; CoveringSolution is now counted
under BoundedWanderingDomains. See LAYOUT_UPDATE.md for the file moves and
BUILD_AUDIT.md for the earlier import and duplication audit.
