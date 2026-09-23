# Smooth corrections and limits

The smooth part of the wandering-dynamics construction uses a local
holomorphic correction only near a compact set, but needs a globally defined
smooth change of coordinates. The following ingredients passed the expanded build and all 350 selected
axiom reports. Only the standard allowed axioms occur.

1. [NearIdentityHomeomorph](../FunctionTheory/Smooth/NearIdentityHomeomorph.lean)
   proves that x ↦ x+u(x) is a global homeomorphism when u has Lipschitz
   constant below one. Surjectivity follows by contraction; the lower distance
   bound gives injectivity and continuity of the inverse.
2. [NearIdentitySmooth](../FunctionTheory/Smooth/NearIdentitySmooth.lean)
   proves smoothness of that inverse, using the smooth inverse function
   theorem and invertibility of identity plus a small derivative.
3. [Cutoff](../FunctionTheory/Smooth/Cutoff.lean) is the existing cutoff proof
   moved from ComplexApproximation with its original Runge names preserved.
   [CutoffBounds](../FunctionTheory/Smooth/CutoffBounds.lean) controls all
   derivatives through a chosen finite order after multiplication by the cutoff.
4. [ControlledExtension](../FunctionTheory/Smooth/ControlledExtension.lean)
   gives the global extension. It agrees locally with the given map near the
   compact set, equals the identity outside the prescribed neighbourhood,
   and has a compactly supported displacement. Its inverse is also smooth.
5. [ComplexDerivativeBounds](../FunctionTheory/Smooth/ComplexDerivativeBounds.lean)
   converts uniform holomorphic error on an open neighbourhood into uniform
   bounds on all prescribed real derivatives on a smaller compact set.
6. [CompactCompositionBounds](../FunctionTheory/Smooth/CompactCompositionBounds.lean)
   controls composition with a fixed C^m homeomorphism. Its derivatives are
   bounded only on the compact inverse image of the fixed support; no global
   derivative bound for an arbitrary homeomorphism is assumed.
7. [HolomorphicSmoothExtension](../FunctionTheory/Smooth/HolomorphicSmoothExtension.lean)
   combines these steps, including order m=0 by internally controlling at
   least the first derivative.
8. [FiniteSmoothNorm](../FunctionTheory/Smooth/FiniteSmoothNorm.lean) defines
   the uniform C^m norm as the sum of the suprema of the derivative norms.
   It takes values in the extended nonnegative reals, so an unbounded
   derivative is recorded as infinity. A fixed margin converts pointwise
   estimates into strict bounds on the suprema.

[ExtensionNorm](../FunctionTheory/Smooth/ExtensionNorm.lean) proves the
norm-form extension statements, including a function defined only on its
actual open domain. They are included in the successful expanded audit.

## Limit argument

Use the telescoping increments of the successive changes of coordinates.
Mathlib's SmoothSeries theorem gives a smooth sum when the number of
uniformly controlled derivatives increases with the stage. The first
derivatives must have a total bound strictly below one. This additional
estimate gives global invertibility and a smooth inverse of the limit;
smooth Cauchy convergence alone would not suffice (paper review M5).

Both series criteria have now compiled in
[SeriesDiffeomorphism](../FunctionTheory/Smooth/SeriesDiffeomorphism.lean),
including uniform convergence of the controlled derivative sums and
smoothness of the inverse. [SequenceLimit](../FunctionTheory/Smooth/SequenceLimit.lean)
applies this to successive changes of coordinates and preserves fixed points.
[ComplexSeriesDerivative](../FunctionTheory/Smooth/ComplexSeriesDerivative.lean)
proves the boundary complex-differentiability step without assuming a common
holomorphic neighbourhood for the summands. The adaptive triangle, realisation and
application theorems remain unfinished.

## Attribution

The cutoff proofs were moved without mathematical changes from this
development's existing ComplexApproximation source on 21 September 2026.
The other arguments use the pinned Mathlib Cauchy estimates, Leibniz and
composition bounds, contraction theorem, inverse function theorem and
smooth-series results. They are not presented as new proofs of the public
Mathlib foundations.

## Completed adaptive-construction ingredients

The expanded 357-report audit also includes
[local critical-point transport](../FunctionTheory/Conformal/LocalConjugacyCritical.lean),
[simultaneous smooth finite-chain corrections](../FunctionTheory/Conformal/SmoothFiniteChain.lean),
[complex-differentiable smooth sequence limits](../FunctionTheory/Smooth/ComplexSequenceLimit.lean),
and [uniform holomorphic sequence limits and moving-point evaluation](../FunctionTheory/Analytic/SequenceLimit.lean).
These are complete results. Their assembly into the final triangle conjugacy
belongs to WanderingDynamics and remains in progress.
