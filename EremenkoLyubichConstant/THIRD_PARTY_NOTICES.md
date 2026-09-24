# Third-party notices

## Ray

This project vendors portions of Geoffrey Irving's **Ray** Lean formalisation from
commit `753f7131cf96f4651294de4398368abf136c34de`:

https://github.com/girving/ray/tree/753f7131cf96f4651294de4398368abf136c34de

Ray is licensed under the Apache License 2.0. Its licence is reproduced in
`RAY_LICENSE`. The 55 vendored modules under `Ray/` are exactly the Ray modules
reachable through the submission's imports. Unused portions of the earlier vendored
tree are retained only in the separate earlier-development archive.

The initial port to Lean/mathlib 4.34 made two compatibility changes:

- `Ray/Misc/Deriv.lean`: replaced a definitional-equality conversion by an explicit
  simplification;
- `Ray/Misc/Measure.lean`: adjusted an almost-everywhere proof to the current tactic
  interface.

A subsequent linter cleanup updated deprecated imports and theorem names, removed
unused simplifier arguments and tactics, used `theorem` for proposition-valued
proof declarations, and replaced the deprecated `ContinuousLinearMap.lipschitz`
name by `lipschitzWith`. These changes are retained in the vendored sources rather
than suppressing their warnings.

The mathematical content used here is unchanged. In particular, Ray supplies the
complete Koebe quarter theorem, including its Grönwall area and Bieberbach
second-coefficient arguments. The project now imports `Ray.Koebe.Koebe` directly.
