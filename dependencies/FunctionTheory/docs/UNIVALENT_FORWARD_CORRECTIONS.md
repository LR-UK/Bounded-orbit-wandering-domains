# Finite forward corrections

[`exists_smooth_univalent_forward_corrections`](../FunctionTheory/Conformal/SmoothUnivalentForward.lean)
is the finite approximation step for univalent realisation with the initial
coordinate fixed. It has passed the full library audit. The infinite
realisation theorem in WanderingDynamics is still in progress.

Given a finite chain of maps taking one compact image exactly onto the next,
assume the maps are holomorphic on neighbourhoods, injective on the compacts,
and have nonzero derivatives there. Supply the desired supports and smooth
error budgets before choosing the approximation tolerance.

The theorem constructs conformal inverse charts and smaller compact collars.
One positive uniform tolerance then gives smooth global corrections for any
sufficiently close holomorphic chain satisfying the displayed finite prefix
interpolation conditions. The first correction is exactly id. Later ones
fix the marks, have the prescribed supports and smooth bounds, are holomorphic
near the compact images with nonzero derivatives, and give the forward
conjugacy as an equality of germs. Intermediate images remain in their
required holomorphic domains.

The explicit interpolation hypothesis is on finite compositions at preimages
of marked points. It is not assumed in the final main theorem: the global
Runge induction must construct approximants meeting it.

The dependency chain is:

1. [Compact conformal inverses and finite prefixes](../FunctionTheory/Conformal/UnivalentFiniteComposition.lean).
2. [Target collars retaining every intermediate orbit](../FunctionTheory/Conformal/ForwardChainCollar.lean).
3. [One smooth prefix correction](../FunctionTheory/Conformal/SmoothForwardPrefix.lean).
4. [A common finite-chain tolerance](../FunctionTheory/Conformal/SmoothForwardChain.lean).
5. The full finite correction theorem linked above.

[Holomorphic inverse transport](../FunctionTheory/Conformal/HomeomorphAnalyticInverse.lean)
also shows that a plane homeomorphism holomorphic at a point has a holomorphic
inverse at its image. Global injectivity supplies the derivative condition.
These are local holomorphy statements about global smooth coordinates, not
assumptions that those coordinates are entire conformal automorphisms.
