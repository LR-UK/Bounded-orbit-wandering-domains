# Runge approximation with finite derivative interpolation

The new theorem family in `Runge/Interpolation.lean` extends the existing
Runge results by requiring exact interpolation at finitely many marked
points. The input function is holomorphic on an open neighbourhood U of a
compact set K; marked points belong to K. For each point a, an independently
chosen natural number m(a) specifies the number of derivatives to retain.

The approximant has uniform error strictly below any prescribed epsilon>0,
and its derivatives of orders k<m(a) equal those of the input at a. In
particular, take m(a)=M+1 to retain orders 0 through M inclusive.

| Theorem | Additional conclusion |
| --- | --- |
| `Runge.rational_approximation_with_interpolation` | A quotient p/q, with q nonzero on K |
| `Runge.prescribed_poles_approximation_with_interpolation` | Every denominator zero belongs to the allowed set P |
| `Runge.polynomial_approximation_with_interpolation` | A polynomial, when the complement of K is connected |

Each has a corresponding `_on_domain` theorem in
`Runge/InterpolationLocalDomain.lean`, accepting a function f:U→C with the
existing `IsHolomorphicFunctionOn` predicate. Its germ derivatives are
computed through `domainExtension`; because the points lie in open U,
values outside U do not affect those derivatives.

## Proof

FunctionTheory's `Analytic/FiniteInterpolation.lean` repeatedly divides out
linear factors using analytic divided differences. It proves an identity

    f = p + Q g,    Q(z) = product over a of (z-a)^m(a),

where p is a polynomial and g is analytic on the same neighbourhood. Runge
approximation is applied to g with the error scaled by a positive uniform
bound for |Q| on K. Recombining the approximant with p and Q preserves the
chosen derivatives. In the prescribed-pole version the denominator is exactly
the denominator obtained when approximating g, so no new poles are introduced.

The analytic-order API turns divisibility of the error into vanishing of
all the required iterated derivatives. The argument works for disconnected
neighbourhoods, empty marked sets, and orders that vary from point to point.

## Scope

This theorem family has holomorphic input. The subsequent
[meromorphic extension](MEROMORPHIC_INTERPOLATION.md) is also proved: it retains
principal parts and prescribes ordinary derivatives at regular marked points.
Neither family asserts finite complex derivatives at poles.
