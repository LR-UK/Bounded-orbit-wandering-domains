# Riemann-sphere atlas from Geoffrey Irving's ray project

The source is [Ray/Manifold/RiemannSphere.lean](https://github.com/girving/ray/blob/753f7131cf96f4651294de4398368abf136c34de/Ray/Manifold/RiemannSphere.lean),
at commit `753f7131cf96f4651294de4398368abf136c34de`, under Apache 2.0.
Original review copies and the licence are included here. They are not compiled.

The compiled adaptation is `FunctionTheory/RiemannSphere/Basic.lean`. It retains
the initial portion through the complex-manifold instance: the underlying type
`OnePoint ℂ`, reciprocal homeomorphism, the two standard charts, and their
holomorphic transition functions. The retained public definitions, namespaces,
and theorem statements follow the original. The unrelated later dynamical and
parameter-dependent results are not imported.

Only import dependencies and reciprocal-limit helper proofs were adapted.
`OneDimension.I` is the unchanged model abbreviation from `Ray/Manifold/Defs.lean`.
The precise source and adaptation hashes are in `UPSTREAM.json`. The upstream
toolchain is Lean 4.33.0; the adaptation is checked against this project's pinned
Lean 4.34.0 and Mathlib. These are reused proofs, not new project claims.

The atlas is compatible with ComplexDynamics' existing `OnePoint ℂ` sphere.
The additional project theorem `FunctionTheory.exists_riemannMap_on_sphere_domain`
uses this atlas, a proved omitted-point coordinate, and the public Tau Ceti
plane Riemann mapping theorem. It is not a theorem attributed to Ray.


`FunctionTheory/RiemannSphere/Coordinates.lean` additionally adapts the public
finite-chart and inversion holomorphy proofs to Mathlib's direct chart
criterion, retaining their names and statements. Spherical translation and
the coordinate omitting an arbitrary finite point are new project proofs.
Their division into reused and additional work is recorded in the manifest.
