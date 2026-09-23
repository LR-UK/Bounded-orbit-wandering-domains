# Prescribed poles on the Riemann sphere

Maintainer request, 17 September 2026. Deferred while work on the Eremenko paper continues.

The current `Runge.prescribed_poles_approximation` accepts an arbitrary set
`P : Set ℂ`, meets every bounded complementary component, and controls every
zero of the chosen denominator. A pole at infinity is implicitly permitted:
there is no numerator/denominator degree restriction.

Add a spherical version with an allowed set in the complement of K in
`OnePoint ℂ`, meeting every complementary component, including the one
containing infinity. This must also cover allowed sets that omit infinity;
merely adjoining infinity to the current statement does not prove that case.
Keep the existing finite-pole interface and compatibility names.

The allowed set need not be finite. Each approximating rational function has
only finitely many poles; a compact set can have infinitely many complementary
components, so a finite allowed set cannot always meet them all.

Use the one-point compactification as the underlying sphere and add a compatible
complex-manifold structure when needed. These are compatible descriptions, not
alternative mathematical objects. ComplexDynamics currently uses `OnePoint ℂ`.
Do not assign a value at infinity to a transcendental entire function.

Sources inspected for future reuse:

- Mathlib: `Topology/Compactification/OnePoint/Basic` and the general
  `Geometry/Manifold/IsManifold` framework.
- [Geoffrey Irving's ray project](https://github.com/girving/ray): complex
  dynamics on compact one-dimensional complex manifolds and the Riemann sphere.
- [Lean community discussion of Riemann surfaces](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Riemann.20Surfaces.20.26.20Uniformization.20Theorem.html):
  the existing unbundled manifold approach permits compatible complex, real,
  and topological structures on the same type.

No spherical theorem or new manifold instance has been added by this note.
