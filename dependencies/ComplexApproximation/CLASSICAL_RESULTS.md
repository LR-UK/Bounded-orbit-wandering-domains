# Auxiliary classical results

## Unbounded approximation geometry and half-strip maps

The September 17 additions include:

- Arakelian sets are preserved by plane homeomorphisms: `IsArakelian.image_homeomorph`.
- An Arakelian set with a vertical margin inside one horizontal gap can be adjoined to a closed horizontal background: `IsArakelian.union_horizontal_background`.
- A U-shaped half-strip band and a separated inner half-strip form an Arakelian set: `isArakelian_bandAndHalfStrip`.
- Simultaneous entire approximation on three disjoint closed pieces, specialised to the preceding configuration: `arakelian_approximation_halfStrip_configuration`.
- The explicit map `log(sinh z)` on a right half-strip is injective and has quantitative derivative estimates, endpoint limits, and bi-Lipschitz ambient extensions on closed insets: `HalfStripExtension.lean`.
- Small Lipschitz perturbations on an arbitrary subset extend to bi-Lipschitz plane homeomorphisms: `exists_bilipschitz_extension_of_small_error`.

[Main results](MAIN_RESULTS.md) · [Proof map](PROOF_MAP.md) · [Complete module index](docs/MODULE_INDEX.md)

This is a curated catalogue of reusable mathematical results proved in this
development, including specialised forms of classical arguments. It is not
a claim of mathematical novelty or of first formalisation. The complete
declaration index also includes technical helper lemmas.

| Result and scope | Checked declaration(s) | Role |
| --- | --- | --- |
| A holomorphic neighbourhood function has a smooth compactly supported extension agreeing near the compact set, with CR defect supported away from it. | [exists_extension_with_separated_defect](Runge/CauchyGreen.lean#L67) | Localise the Cauchy–Green argument. |
| Rectangular boundary/area identity for the removable difference quotient. This is a specialised Green identity, not a general Cauchy–Pompeiu theorem. | [rectangleBoundary_dslope](Runge/CauchyGreen.lean#L88) | Integral representation used in rational Runge. |
| The uniform rational closure is closed under reciprocals of nowhere-zero members. | [ringInverse_mem_rationalClosure](Runge/UniformOperations.lean#L32) | Divide by the boundary kernel. |
| The rectangular boundary Cauchy kernel is nonzero at every interior point. | [rectangleKernel_ne_zero](Runge/RectangleKernel.lean#L86) | A qualitative substitute for computing the residue integral. |
| Uniform rational approximation passes through the specified parameter integrals. | [integral_uniform_rational_approximation](Runge/UniformClosure.lean#L102); [cauchyIntegral_uniform_rational_approximation](Runge/CauchyKernel.lean#L76) | Integrate in the Banach space of continuous functions on the compact set. |
| Geometric pole-shifting expansion, explicit remainder, and uniform approximation away from the poles. | [polePartial_remainder](Runge/PoleShift.lean#L31); [exists_polePartial_uniform_error](Runge/PoleShift.lean#L68); [pole_shift_uniform_approximation](Runge/PoleShift.lean#L95) | Move prescribed poles. |
| In a closed complex subalgebra, the poles whose kernels belong to the algebra form a clopen subset of the complement. | [isClopen_goodPoles](Runge/PoleTopology.lean#L95) | Propagate along a complementary component. |
| Sufficiently distant simple poles are in the uniform closure of polynomials on a bounded compact set. | [poleKernel_mem_of_large_norm](Runge/PolesAtInfinity.lean#L57) | Handle unbounded complementary components. |
| Polynomial functions and simple-pole kernels generate all required rational functions after taking closure. | [rationalClosure_le_of_polynomials_and_kernels](Runge/RationalGeneration.lean#L46) | Factor denominators, with multiplicities. |
| Separate an exterior point from a full compact set by a polynomial equal to one at that point and small on the compact set. | [exists_polynomial_separator](Runge/PolynomialSeparation.lean#L15) | Full compact neighbourhoods in the application. |
| Disjoint closed plane sets with preconnected complements have a preconnected complement of their union. | [isPreconnected_compl_union_disjoint](ComplexApproximation/Topology/Nonseparation.lean#L119) | The disjoint closed-set case of Janiszewski; proved by continuous logarithms. |
| Every complementary component of a closed plane set meets each nonempty open neighbourhood containing the set. | [complement_component_meets_domain](ComplexApproximation/Topology/Nonseparation.lean#L139) | Pass between the plane and an open neighbourhood. |
| For compact K inside an open connected plane domain U, K is full iff U minus K is connected. | [isConnected_compl_iff_domain_diff](ComplexApproximation/Topology/Nonseparation.lean#L160) | A local test for fullness. |
| Homeomorphisms between open connected plane domains preserve fullness of compact subsets. | [isConnected_compl_image_domain_homeomorph](ComplexApproximation/Topology/Nonseparation.lean#L195) | No simple connectivity, conformality, or ambient extension is required. |

## Additional Arakelian foundations

Additional results from the Arakelian development:

| Result and scope | Checked declaration(s) | Role |
| --- | --- | --- |
| The planar Cauchy kernel is locally integrable; its convolution with a smooth compactly supported density is smooth. | `locallyIntegrable_cauchyKernel`, `contDiff_cauchyTransform` | Handle the singularity, including evaluation inside the density's support. |
| The reciprocal kernel has boundary integral exactly $2\pi i$ around a centred square. | `rectangleBoundary_inv` | Normalize the solution operator. |
| Smooth compact-support Cauchy–Pompeiu and a right inverse of the Cauchy–Riemann defect. | `cauchyPompeiu_compact`, `cauchyRiemannDefect_solveCauchyRiemann` | Correct failure of holomorphy. |
| A uniform solution bound depending only on a fixed compact support container. | `norm_solveCauchyRiemann_le` | Control successive corrections. |
| Filling bounded complementary components preserves closedness; disk intersections of sets without bounded complementary components are full. | `isClosed_fill`, `isConnected_compl_inter_closedBall` | Supply compact polynomial-Runge sets. |
| Extend holomorphy across a compact set with arbitrarily small uniform change on the original closed set. | `exists_holomorphic_neighbourhood_extension` | The Rosay–Rudin gluing step. |
| Locally summable corrections of eventually holomorphic functions have an entire limit. | `exists_entire_limit_of_eventually_holomorphic_corrections` | Pass from expanding neighbourhoods to the plane. |

## Foundations imported from Mathlib

Rectangular Green integration, smooth cutoff machinery, complex polynomial
factorisation, covering-map/continuous-logarithm theory, Urysohn separation,
and general compactness and integration theory come from Mathlib. The rows
above are the additional statements or specialisations proved here using
those foundations. They should not be read as claims that those underlying
Mathlib theories were developed in this project.

## Conformal foundations for Section 7

The following are new project proofs, checked in the 94-result audit:

- Cauchy's estimate gives a common positive lower bound on the derivatives of
  inverse Riemann maps: `normalized_inverse_derivative_lower_bound`.
- Simultaneous locally uniform limits preserve both inverse identities:
  `invOn_of_locallyUniform_limits`.
- Normalized Riemann maps and their inverses converge on a decreasing bounded
  kernel: `normalized_riemannMaps_tendsto_on_bounded_kernel`.
- An omitted closed set is eventually avoided by compact inverse images:
  `eventually_disjoint_direct_image_of_inverse_convergence`.

Riemann mapping, normalized uniqueness, Montel selection for locally bounded
families, Hurwitz, and Schwarz reflection are **reused proofs from Tau Ceti**,
not new proofs attributed to this project. Their source and licence are
recorded in [third_party/TauCeti](../FunctionTheory/third_party/TauCeti/README.md).

The conformal-mapping development is now maintained in
[FunctionTheory](../FunctionTheory/README.md); the corresponding modules in
this repository are compatibility wrappers. Consult its theorem gallery for
the current statements and extensions.

The unbounded-component criterion now also accepts a ray in any nonzero
complex direction: `not_isBounded_component_of_affine_ray` in
[HorizontalEscape](ComplexApproximation/Topology/HorizontalEscape.lean).
The application uses vertical rays to analyse the continuum-plus-ray set.

## Filled continua

[FilledContinua](ComplexApproximation/Topology/FilledContinua.lean) proves
compactness and connectedness of the filled hull and connectedness of its
complement. It also proves containment in an ambient set whose complementary
components are all unbounded, with a connected-complement specialization.

## Filling inside open neighbourhoods and straight channels

| Result | Source |
| --- | --- |
| Filling preserves straight-channel width, including the interior bound at its endpoint | [FillingStraightChannels](ComplexApproximation/Topology/FillingStraightChannels.lean) |
| Filling a closed set stays inside the interior of an ambient set with no bounded complementary components | [FillingInterior](ComplexApproximation/Topology/FillingInterior.lean) |


[FillingCoordinateBounds](ComplexApproximation/Topology/FillingCoordinateBounds.lean)
proves that filling bounded complementary components preserves horizontal-strip
bounds and lower bounds on real parts. These support the continuum attachment
domains in EremenkosConjecture.

## Filled neighbourhoods and approximation bands

| Result | Source |
| --- | --- |
| Closed star-convex sets are Arakelian; compact decorations and bounded modifications are handled explicitly | [ArakelianElementaryGeometry](ComplexApproximation/Topology/ArakelianElementaryGeometry.lean) |
| Filling commutes with decreasing closed intersections when all added holes are uniformly bounded and the limit has no bounded holes | [FillingDecreasingIntersection](ComplexApproximation/Topology/FillingDecreasingIntersection.lean) |
| Nonseparation of a band together with an inner set, using connectedness and unboundedness of the gap | [NestedBandNonseparation](ComplexApproximation/Topology/NestedBandNonseparation.lean) |
| A filled set with one straight halfstrip tail has connected plane complement | [StraightTailComplement](ComplexApproximation/Topology/StraightTailComplement.lean) |
| The band-and-inner-strip tail gives the Arakelian condition, once bounded holes have been excluded | [StraightBandArakelian](ComplexApproximation/Topology/StraightBandArakelian.lean) |


## Transport under local charts

| Result | Source |
| --- | --- |
| Closed images under domain homeomorphisms retain absence of bounded complementary components | [LocalHomeomorphNonseparation](ComplexApproximation/Topology/LocalHomeomorphNonseparation.lean) |
| Agreement with a plane homeomorphism off a compact set gives closed images and transports Arakelian subsets | [HomeomorphicTail](ComplexApproximation/Topology/HomeomorphicTail.lean) |
| A derivative tending to one on a straight tail supplies this agreement and the Arakelian transport | [ConformalArakelian](ComplexApproximation/Topology/ConformalArakelian.lean) |

No ambient extension on the bounded decoration is assumed. The neighbourhood
characterization suggested by the maintainer is [recorded for later](docs/ARAKELIAN_FUTURE.md).

## Finite derivative interpolation

Runge approximation now preserves independently specified finite jets at
marked points, including simultaneous control of allowed poles. For full
compact sets the approximant can be a polynomial. The implementation reuses
analytic polynomial division from FunctionTheory and retains the original
Runge denominator. See [the proof description](docs/FINITE_INTERPOLATION.md).

## Meromorphic Runge interpolation

Simultaneous Runge approximation, preservation of principal parts, regular-point
jet interpolation and prescribed locations for new poles. The proof clears
the finitely many compact-set singularities by a polynomial, applies the
holomorphic finite-jet theorem to the analytic remainder and restores the
rational part. See [the theorem](docs/MEROMORPHIC_INTERPOLATION.md).

## Simultaneous approximation of finite returns

[Meromorphic approximation](Runge/MeromorphicReturnApproximation.lean) and
[polynomial approximation](Runge/PolynomialReturnApproximation.lean) can
retain finitely many return maps with different lengths and error tolerances.
They preserve all intermediate open domains, regularity, marked return values
and centred local degrees. The polynomial version requires a full compact
approximation set and returns an explicit polynomial witness.
