# Recovered Eremenko–Lyubich dependency

Imported from the user's `eremenko-lyubich-streamlined.zip` (version 2),
SHA-256 `1e1dceb5812f9b5fe24d4093164c5adead40edfcf61a3c2cdff5c24dd2fb714e`.
Only the import closure of `ClassBLogarithmicTransform` was copied, together
with the original third-party notices and Ray licence. Original author
attributions and mathematical proofs are retained.

Compatibility changes for Lean 4.35.0-rc2 and the wandering project's pinned
Mathlib:

- `Ray/Dynamics/Multiple.lean`: specify the complex continuous-linear-map
  instance explicitly in the nonzero derivative proof.
- `EremenkoLyubichConstant/Koebe.lean`: remove the redundant `import Mathlib`.
  Its existing Ray import supplies everything used. The broad import also
  introduced graph declarations colliding with the supplied Schoenflies
  dependency; no Schoenflies source was changed.

The exterior-tract simple-connectivity theorem is used by
`BoundedWanderingDomains/ClassBFillLimits.lean`. The sharp expansion estimate
is also available, but is not an additional assumption of the singular-limit
proof.
- Rename Ray's `OneDimension` namespace to `RayOneDimension` (module paths
  unchanged), because `FunctionTheory.RiemannSphere.Basic` independently
  declares `OneDimension.I`. This is a namespace compatibility change only.
