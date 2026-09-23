# Proof architecture

The subsequent neighbourhood-holomorphic Arakelian theorem is also complete.
Its Cauchy–Pompeiu, cutoff gluing, filled-exhaustion, and local-limit route is
documented in [ARAKELIAN_PLAN.md](ARAKELIAN_PLAN.md). Preserve both developments.

All three Runge results are complete. This file preserves the project-plan
location as a guide to the finished mathematical argument.

## Rational approximation on an arbitrary compact set

1. `UniformClosure.lean` defines rational functions as a subalgebra of `C(K, ℂ)`.
   Membership in its topological closure is equivalent to simultaneous uniform
   approximation by one polynomial quotient with denominator nonzero on `K`.
   Closed real submodules contain integrals of their elements.
2. `SmoothCutoff.lean` constructs a globally smooth, compactly supported `g`
   agreeing with the given holomorphic function near `K`.
3. `CauchyGreen.lean` defines the defect `I * ∂ₓg - ∂ᵧg` and proves that it has
   compact support disjoint from `K`. For each `z ∈ K`, the difference quotient
   `(g(w)-g(z))/(w-z)` has a removable singularity. Applying Mathlib's rectangular
   Green theorem gives its boundary integral as an area Cauchy integral.
4. Choose one rectangle with both `K` and the support of `g` strictly inside.
   On its boundary, the difference quotient is `-g(z)/(w-z)`. Consequently the
   area integral equals minus `g(z)` times the boundary Cauchy integral.
5. `CauchyKernel.lean` and `IntegralTransforms.lean` put both integrals in the
   uniform rational closure. Integration is performed in `C(K, ℂ)`, so the
   approximants work on all of `K` simultaneously.
6. `RectangleKernel.lean` proves the boundary Cauchy integral has positive
   imaginary part at every interior point, hence is nonzero. Its exact value
   is unnecessary. `UniformOperations.lean` proves that the rational closure
   contains reciprocals of its nowhere-zero members.
7. `RationalApproximation.lean` combines these results to obtain `g`, and thus
   the original function on `K`, in the rational closure. This proves the exact
   original rational target.

No grid representation, general Cauchy–Pompeiu theorem, or rectangle-residue
formula is assumed.

## Prescribed poles

1. `PoleAlgebra.lean` defines rational functions with a nonzero denominator
   whose zeros all belong to the allowed set `P`. Denominators also remain
   nonzero on `K`. Its closure characterises uniform prescribed-pole approximation.
2. `PoleShift.lean` proves the finite geometric expansion that moves a pole to
   powers of a nearby pole, with an explicit uniform remainder bound.
3. `PoleTopology.lean` applies that expansion in any closed complex subalgebra
   of `C(K, ℂ)`. The poles whose kernels belong to the algebra form an open and
   closed subset of the complement. Thus membership propagates through a
   connected component.
4. `PolesAtInfinity.lean` proves that every sufficiently distant pole has a
   uniform expansion in polynomials. Every unbounded component therefore has
   a kernel in the closed algebra; bounded components are covered by the
   hypothesis that `P` meets them.
5. `RationalGeneration.lean` uses the fundamental theorem of algebra to factor
   an arbitrary denominator. A finite product of simple-pole kernels gives
   its reciprocal, including root multiplicities.
6. `PrescribedPoles.lean` concludes that the entire rational closure is contained
   in the prescribed-pole closure. Combining this with rational Runge gives
   the full prescribed-pole theorem.

## Polynomial approximation

For connected complement, compactness of `K` implies that the complement is
unbounded. There are therefore no bounded complement components, and the allowed
set may be empty. A nonzero complex polynomial with no zeros is constant, so
`PoleAlgebra.lean` identifies the empty-pole closure with uniform polynomial
approximation. This gives the original polynomial target in `PrescribedPoles.lean`.

`Holomorphic.lean` translates all three results to the usual complex-
differentiability hypothesis on the open neighbourhood.

## Reproduction and integrity

Run `scripts/verify.ps1` or the commands in `README.md`. All original targets
are proved; `RungeTargets` now serves only as a compatibility check. Preserve
the pinned dependencies and standard-axiom audit when modifying the project.

Future prior-art searches should continue to include other proof assistants
and EPFL's reformalization project, initially recalled by the user as Zurich.
