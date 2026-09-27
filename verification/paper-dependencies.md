# Proof dependency audit

PaperSolution imports 773 local source modules transitively.

| Source group | Modules |
|---|---:|
| BoundedWanderingDomains | 360 |
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

Each module and its source hash is listed in paper-submission.json.
The graph excludes pinned Mathlib/core modules from local counts.

Contained FunctionTheory, ComplexDynamics, ComplexApproximation and
EremenkosConjecture dependencies remain in the checked import closure.
Planar filling and Jordan-domain topology use the approximation/topology
packages; normal-family and sphere foundations use the other attributed
libraries. Package removal has therefore not been inferred from a name
or from whether its main advertised theorem appears in the final statement.

The old unused CompactComplementCovering and CheckCovering experiments
were removed from the delivered source and preserved in local scratch.
Earlier proved entry points remain separate and continue to compile.
