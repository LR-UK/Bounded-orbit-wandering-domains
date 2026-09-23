# Neighbourhood-holomorphic Arakelian approximation

Completed and audited on 16 September 2026 for the forthcoming Sections 4 and 7
application to Martí-Pete–Rempe–Waterman. The result is uniform approximation
on a closed Arakelian set of a function holomorphic on an open neighbourhood.
`IsArakelian` states closedness, absence of bounded complementary components,
and boundedness of the holes created by adjoining each closed disk.

## Source

Jean-Pierre Rosay and Walter Rudin, *Arakelian's Approximation Theorem*,
American Mathematical Monthly **96** (1989), 432–434,
[DOI](https://doi.org/10.1080/00029890.1989.11972213).
The text of pages 432–433 explicitly separates the neighbourhood-holomorphic
case, which uses Runge, from the continuous/interior-holomorphic case, which
uses Mergelyan. The present target is the former case.

## Analytic foundation

`CauchyTransform.lean` proves local integrability of the planar Cauchy kernel,
smoothness of convolution with a smooth compactly supported density, and
commutation with the Cauchy–Riemann defect.

`CauchyRectangle.lean` computes the Cauchy kernel integral around a centred
square as `2πi`, using real arctangent integrals.

`CauchyPompeiu.lean` obtains the formula from rectangular Green's theorem.
Subtracting the antiholomorphic part of the first derivative gives a removable
difference quotient at the centre. The added term contributes zero by symmetry.
For a smooth compactly supported density the result supplies a smooth solution
of the inhomogeneous Cauchy–Riemann equation on the whole plane.

`CauchyTransformBounds.lean` is checked: a unit-disk split gives a bound
uniform in the evaluation point, with a constant depending only on a fixed
compact set containing the density's support.

## Completed approximation argument

1. Closed sets with no bounded complementary components have full compact
   intersections with disks. Filling bounded components preserves this property.
2. Choose expanding disks containing the preceding bounded holes. Let `E_i`
   be the filled union of the original set and the i-th disk.
3. Approximate the current holomorphic function on a suitable full compact
   intersection by a polynomial. Glue it to the old function with a smooth cutoff.
4. Correct the Cauchy–Riemann defect by the solution operator. A second smooth
   cutoff supported in a small neighbourhood of the approximation set makes the
   density globally smooth; it equals the required density near the overlap.
   This is a smooth-density implementation of the Rosay–Rudin correction.
5. Choose summable errors and take a locally uniform limit on expanding
   neighbourhoods. The limit is entire and uniformly approximates the original
   function on the closed set.
6. Expose the result also for a function whose actual domain is the open
   neighbourhood, using the existing `Runge.IsHolomorphicFunctionOn` interface.

These steps are proved in `Topology/Filling`, `Topology/Arakelian`,
`SmoothLocalization`, `CorrectedInterpolation`, `ArakelianStep`,
`HolomorphicLimit`, `Arakelian`, and `ArakelianLocalDomain`.
The root build, original Runge compatibility targets, source-integrity scan,
and all 56 selected axiom reports passed. Only the standard Lean axioms occur.

The continuous/interior-holomorphic version and equivalence with the
sphere-complement formulation are not proved here. The counterexample
application has checked strip geometry and unbounded stability; its induction
is still being assembled in EremenkosConjecture.
