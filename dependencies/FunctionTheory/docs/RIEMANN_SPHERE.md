# Riemann mapping on the sphere

[Main results](../MAIN_RESULTS.md) · [Lean gallery](../FunctionTheory/MainTheorems.lean)

Let U be a nonempty simply connected open subset of the Riemann sphere.
If the complement of U contains at least two distinct points,
then there is a biholomorphism

**e : U → 𝔻.**

The statement allows infinity in U. Both e and its inverse are defined
only on their actual domains. Omitting just one point would give the plane,
which is not biholomorphic to the disk.

The checked theorem is
`FunctionTheory.exists_riemannMap_on_sphere_domain` in
[RiemannMapping.lean](../FunctionTheory/RiemannSphere/RiemannMapping.lean).
Mathlib's `IsSimplyConnected` already includes nonemptiness. The holomorphy
conditions are `ContMDiff` over the complex scalar field in both directions;
this is complex smoothness, hence ordinary holomorphy in local charts.

The proof chooses a finite omitted point a. The coordinate

**z ↦ 1/(z − a), with ∞ ↦ 0,**

is a biholomorphism from the punctured sphere to the plane. Its inverse is
the proved `RiemannSphere.omittedPointParam a`, with value infinity at zero.
The second omitted point makes the coordinate image of U a proper plane
domain. Simple connectivity transfers through the coordinate homeomorphism,
and the existing public Tau Ceti Riemann mapping theorem applies. The maps are
then composed and restricted to the actual domains.

## Topology and complex structure

The underlying type is `OnePoint ℂ`, the one-point compactification already
used in ComplexDynamics. The finite and reciprocal charts equip that same
type with a complex-manifold structure. There is no need to choose between
the topological sphere and a Riemann surface: the latter adds compatible
complex coordinates to the former.

Mathlib supplies the manifold framework. The concrete sphere atlas and the
finite-chart/inversion holomorphy proofs are adapted from Geoffrey Irving's
[Ray project](https://github.com/girving/ray/blob/753f7131cf96f4651294de4398368abf136c34de/Ray/Manifold/RiemannSphere.lean),
with the pinned source, Apache 2.0 licence, and compatibility record in
[third_party/Ray](../third_party/Ray/README.md). The spherical Riemann mapping
theorem and arbitrary omitted-point coordinate are additional project work.

This development does not assume or prove general uniformization or a theory
of prime ends. Boundary extension at the attached slit is a separate local
theorem needed for the Eremenko application.
