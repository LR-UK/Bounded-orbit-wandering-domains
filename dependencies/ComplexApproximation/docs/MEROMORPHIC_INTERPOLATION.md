# Meromorphic Runge approximation with interpolation

The theorem is `Runge.meromorphic_prescribed_poles_approximation_with_interpolation`
in [MeromorphicInterpolation.lean](../Runge/MeromorphicInterpolation.lean).
It is proved and audited. Its
[actual-domain version](../Runge/MeromorphicInterpolationLocalDomain.lean)
accepts a function defined only on an open neighbourhood U of K.

Let K be compact, f meromorphic near K, and P meet each bounded complementary
component of K. Given epsilon>0 and finitely many regular marked points a in K,
with independently chosen orders m(a), there are polynomials p,q and an error e
such that:

- q is nonzero as a polynomial and has no zero at any regular point of f in K;
- every zero of q is either an original singular point in K or belongs to P;
- e is holomorphic near K and |e|<epsilon throughout K;
- f-p/q agrees with e in a punctured neighbourhood of each point of K;
- |f-p/q|<epsilon at every regular point of K;
- derivatives of orders k<m(a) agree at each marked point a.

The punctured-neighbourhood identity and analyticity of e state precisely that
the principal parts agree. They avoid subtracting two sphere-valued infinities
at a pole. Ordinary derivative interpolation is required only at regular points.
The poles are represented using Mathlib's meromorphic-function convention;
their arbitrary default complex values do not enter the principal-part assertion.

## Proof

Mathlib's [meromorphy API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Meromorphic/Basic.html)
shows that nonanalytic points form a discrete set near K, hence only finitely
many belong to K. FunctionTheory multiplies f by a finite product Q of powers
of linear factors to make Qf analytic near K. Finite analytic division gives
Qf=p0+Qg, so f=p0/Q+g off the zeros of Q, with g analytic near K.

Apply holomorphic Runge approximation with interpolation to g, obtaining r/q1.
Then p/q=(p0*q1+Q*r)/(Q*q1). The error is g-r/q1, which is analytic near K
because q1 has no zero there. Adding back the fixed rational part preserves
the chosen jets at every regular marked point. All arguments use the pinned
Mathlib and the already checked interpolation theorem.

For unrestricted new poles, take P=C. If K has connected complement, the
existing `Runge.meets_empty_of_connected_complement` permits P=emptyset, so
no new poles are introduced. For holomorphic input the earlier polynomial
interpolation theorem already gives the polynomial conclusion directly.
