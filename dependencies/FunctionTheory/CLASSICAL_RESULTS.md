# Classical auxiliary results

## Uniform omitted-values confinement

`Conformal/SchottkyConfinement.lean` derives a common source radius for
holomorphic disc maps omitting two fixed distinct finite values, with
central values in a fixed compact set. The image of this source disc lies
within any prescribed positive distance of its centre value. The radius
is independent of additional omitted values; the central compact set need
not have positive distance from the fixed omitted pair.

The proof uses the existing Schottky estimate on the half-disc, followed
by Schwarz's lemma. Its four declarations are included in scripts/Audit.lean.
This result constructs neither a hyperbolic universal covering nor a
Poincaré metric.

## Reused public proofs

Riemann mapping, normalized uniqueness, conformality and holomorphic inverses,
Montel selection, Hurwitz injectivity, Schwarz reflection, and Carathéodory continuous extension come from Tau
Ceti. Their original authorship and declaration names are retained. These are
not new proofs produced by this project. See [provenance](PROVENANCE.md).

## Additional checked development

- **Finite critical-point conformal correction:** a close holomorphic perturbation
  preserving marked values and critical multiplicities is corrected by a small
  conformal source map fixing every marked point. The full inverse and global
  injectivity on the requested source are proved. The 316-report audit passed.
- **Quantitative local power coordinates:** divide by the prescribed vanishing
  power, bound the quotient by the maximum modulus principle, and absorb a
  small unit-factor perturbation into a holomorphic root normalized at one.
- **Gluing with a collar:** nearby lifts agree on overlaps by local injectivity;
  a uniform collar yields global injectivity of the glued map on the smaller set.
- **Compact preimage stability:** sufficiently close holomorphic maps retain
  nearby preimages of a varying target value, uniformly on a compact set.
- **Finite-composition stability:** all partial non-autonomous compositions
  remain close and stay in their prescribed open domains, using explicit collars.
- **Open holomorphic maps:** openness is equivalent to local nonconstancy,
  including for disconnected open domains and functions defined on their actual domains.
- **Shared univalence estimates:** five existing estimates were moved from
  EremenkosConjecture without changing their proofs. Compatibility names remain
  available there; these are shared earlier project work, not five new proofs.

- **Actual-domain holomorphy:** local representatives give ambient differential
  calculus without requiring the input function outside its domain.
- **Compact avoidance:** locally uniform convergence keeps images of a compact
  set away from a disjoint closed set; inverse convergence gives the corresponding
  direct-image separation statement.
- **Kernel inclusion:** a nondegenerate holomorphic limit maps into the interior
  of an intersection of eventual closed constraints.
- **Nondegeneracy:** a positive lower bound on the derivative prevents a locally
  uniform limit from being constant.
- **Inverse limits:** simultaneous locally uniform limits preserve the inverse
  identities under the explicit domain and image conditions.
- **Inverse derivative estimate:** a fixed disk in the domain gives a lower
  bound for the derivative at zero of a normalized inverse Riemann map.
- **Bounded kernel convergence:** Montel selection and normalized uniqueness
  yield locally uniform convergence of the whole sequences of direct and
  inverse maps.
- **Halfplane bounds:** a common lower bound for imaginary parts, together with
  a fixed value at zero, gives local boundedness on the unit disk by the
  Borel–Carathéodory estimate.
- **Unbounded kernel convergence:** the local bounds above replace boundedness
  of the source domain, yielding the same direct and inverse convergence for
  decreasing domains in a horizontal halfplane.

Runge, neighbourhood-holomorphic Arakelian, and the Cauchy–Pompeiu machinery
supporting approximation currently remain in the sibling ComplexApproximation
project. Further foundational extraction can be done without duplicating proofs.

## Analytic estimates at a reflected strip end

[StripEndAsymptotics](FunctionTheory/Conformal/StripEndAsymptotics.lean) proves
that an analytic function with a simple zero at zero satisfies
$z f'(z)/f(z)=1+O(z)$. If its leading coefficient is in the logarithm's slit
plane, it also proves $\log(f(z)/z)-\log f'(0)=O(z)$. Substituting
$z=\exp(-w)$ gives the corresponding $O(\exp(-\operatorname{Re}w))$ estimates,
uniformly as the real part tends to infinity.

These are the analytic estimates used after reflection in Lemma 7.2.
`StripEndCoordinates` now identifies the logarithm branch from source and
target strip bounds and the exponential identity. The domain geometry must
still supply that identity and the continuous boundary values needed for
reflection.

## Reflection interface and uniform derivative bounds

- [ImaginaryReflection](FunctionTheory/Conformal/ImaginaryReflection.lean):
  the public Schwarz principle transported by a quarter-turn, with the same
  explicit boundary-continuity and symmetry requirements.
- [StripBounds](FunctionTheory/Conformal/StripBounds.lean): a closed strip inset
  bounded to the left has compact left truncations. Tail bounds and continuity
  of a nonvanishing function give global bounds there. Applied to the derivative
  of an injective holomorphic map, convergence to one or the exponential error
  estimate gives uniform positive lower and finite upper derivative bounds.

## Injectivity at a reflected boundary

[ReflectionInjectivity](FunctionTheory/Conformal/ReflectionInjectivity.lean)
proves a general topological fact: an open map into a space with a dense
subset D is injective if it is injective on the preimage of D (with Hausdorff
source). Apply this to target values off the imaginary axis. The two
halfplanes separate the reflected branches; openness rules out collisions
on the axis. Thus injectivity of the original map on the open half suffices.
The zero is simple, and its derivative is positive real by restriction to
the real and imaginary axes. The reflection's boundary continuity remains
an explicit input.

[StripEndCoordinates](FunctionTheory/Conformal/StripEndCoordinates.lean)
recovers the derivative identity and logarithm branch, hence both asymptotics
for the original strip map. [StripUniformity](FunctionTheory/Conformal/StripUniformity.lean)
combines compact left truncations with end estimates to prove uniform
neighbourhood widths and uniform continuity. The application module
`EremenkosConjecture.StripInsetControl` uses these bounds for finite-iterate
approximation without an ambient extension hypothesis.

## Escape from inverse convergence on a closed strip

[StripKernelEscape](FunctionTheory/Conformal/StripKernelEscape.lean) applies
compact avoidance to closed rectangles, including their horizontal boundary
segments. If the inverse maps converge locally uniformly on the closed strip,
their limit omits a closed set A, and the direct maps invert them on A with
values in that strip, then the absolute real parts of the direct images tend
to infinity uniformly over A. No compactness of A is needed. The closed-strip
convergence assumption is stronger than the already proved open-domain
kernel-convergence theorem.

## Geometric construction of a normalized strip map

- [JordanBoundary](FunctionTheory/Conformal/JordanBoundary.lean) normalizes a
  disk map at an interior point and a boundary point, and provides its
  continuous closed-disk extension with exact closure and frontier images.
- [CayleyCoordinates](FunctionTheory/Conformal/CayleyCoordinates.lean) and
  [StripCoordinates](FunctionTheory/Conformal/StripCoordinates.lean) give
  the explicit disk, right-halfplane and horizontal-strip identifications.
- [StraightBoundaryExtension](FunctionTheory/Conformal/StraightBoundaryExtension.lean)
  reflects at a locally straight boundary, proving local injectivity, symmetry,
  and a positive real derivative. Its analytic inverse is constructed in
  [StraightBoundaryInverse](FunctionTheory/Conformal/StraightBoundaryInverse.lean).
- [StripEndMap](FunctionTheory/Conformal/StripEndMap.lean) assembles these
  results into a normalized strip bijection and both exponential end estimates.
  The domain is simply connected, bounded to the left, and has a full straight
  right tail; the exponential image is required to have Jordan boundary.

These additions use the attributed public Carathéodory theorem. They do not
require a homeomorphic extension of the conformal map to the whole plane.

## Properness of strip insets

[StripProper](FunctionTheory/Conformal/StripProper.lean) proves boundedness
from a tail limit and compact left truncations. A continuous map with bounded
displacement on a closed set is proper on that set. Applied to the strip
translation asymptotic, this gives compact preimages and closed images,
using only the actual-domain restriction.

## Simple connectivity from compact connected subsets

[SimpleConnectivity](FunctionTheory/Topology/SimpleConnectivity.lean) proves
`isSimplyConnected_of_compact_connected_subsets`. A loop has compact connected
image, so a contraction in a simply connected subdomain gives its contraction
in the original domain.

## Boundary approach and injectivity

[BoundaryApproach](FunctionTheory/Topology/BoundaryApproach.lean) proves
preconnected approach regions for convex sets and their transfer through a
relative chart or an ambient homeomorphism. The imported and audited
`TauCeti.injOn_closedBall_of_isPreconnected_image_approach` combines inverse
cluster sets, monotone boundary fibres and analytic arc uniqueness to prove
injectivity of a continuous conformal extension under this local hypothesis.

## Boundary convergence along shared arcs

| Result | Source |
| --- | --- |
| Rouché image-disk inclusion and nonvanishing on an outer annulus | [UnivalentAnnulus](FunctionTheory/Conformal/UnivalentAnnulus.lean) |
| Vitali convergence to a prescribed holomorphic limit | [AnalyticContinuationConvergence](FunctionTheory/Conformal/AnalyticContinuationConvergence.lean) |
| A lower bound on inner values bounds their circle reflections | [ReflectionBounds](FunctionTheory/Conformal/ReflectionBounds.lean) |
| Propagation of convergence across a circular arc | [ReflectionConvergence](FunctionTheory/Conformal/ReflectionConvergence.lean) |
| Boundary convergence on a symmetric collar, with the lower bound derived | [UnivalentBoundaryConvergence](FunctionTheory/Conformal/UnivalentBoundaryConvergence.lean) |
| Construction of the needed connected symmetric collar | [CircleCollar](FunctionTheory/Conformal/CircleCollar.lean) |
| Locally uniform convergence on the closed disk away from exceptional boundary points | [SharedArcConvergence](FunctionTheory/Conformal/SharedArcConvergence.lean) |
| Finite closed-strip coordinates and continuity of logarithmic inverses | [StripClosedCoordinates](FunctionTheory/Conformal/StripClosedCoordinates.lean) |

In the last boundary-convergence theorem the maps are continuous disk self-maps,
holomorphic and injective on the open disk, converging to the identity there.
Near each allowed boundary point they eventually map a circle arc into the
unit circle. These are the complete geometric and convergence hypotheses.

## Length-area separation and narrow attachments

| Result | Source |
| --- | --- |
| A common annulus works for every injective holomorphic map into a fixed bounded set | [UniformLengthArea](FunctionTheory/Conformal/UniformLengthArea.lean) |
| A short semicircle has uniformly small image chords | [UniformLengthArea](FunctionTheory/Conformal/UniformLengthArea.lean) |
| A barrier contained in a small disk cap traps its entire separated side there | [SeparatingCrosscut](FunctionTheory/Conformal/SeparatingCrosscut.lean) |
| A cap of radius delta about -1 has strip real part at most log delta | [SeparatingCrosscut](FunctionTheory/Conformal/SeparatingCrosscut.lean) |
| A continuous scalar barrier detects a semicircle across a narrow gate | [RightCircularCut](FunctionTheory/Conformal/RightCircularCut.lean) |
| A uniform gate width implies a uniform leftward bound | [ThinAttachment](FunctionTheory/Conformal/ThinAttachment.lean) |
| Interior kernel convergence controls the compact radial reference segment | [RadialKernelControl](FunctionTheory/Conformal/RadialKernelControl.lean) |
| Shrinking attachments imply uniform leftward escape of the entire attached side | [ThinAttachmentEscape](FunctionTheory/Conformal/ThinAttachmentEscape.lean) |

The length-area and chord foundations are the attributed pinned Tau Ceti
results in `Conformal/LengthArea.lean`; no new vendor modules were required.
The new uniform quantifier order and the separating-side argument are proved
in FunctionTheory. A general definition or full theory of extremal length
has not been added.

## Local Caratheodory and exterior coordinates

| Result | Source |
| --- | --- |
| A short circular crosscut has its entire image in a small cap centred on the unit circle | [CircularArcCap](FunctionTheory/Conformal/CircularArcCap.lean) |
| Circular crosscuts imply a unique boundary limit for a conformal disk map | [LocalCircularBoundary](FunctionTheory/Conformal/LocalCircularBoundary.lean) |
| Local straight-slit geometry satisfies the crosscut criterion | [SlitTipBoundary](FunctionTheory/Conformal/SlitTipBoundary.lean) |
| Affine transfer of the local slit-tip limit | [SlitTipCoordinates](FunctionTheory/Conformal/SlitTipCoordinates.lean) |
| Inversion coordinates retain infinity and preserve connectedness of a full compact exterior | [ExteriorCoordinate](FunctionTheory/Conformal/ExteriorCoordinate.lean) |
| A punctured set approaching the inversion pole has unbounded inverted image | [ExteriorCoordinate](FunctionTheory/Conformal/ExteriorCoordinate.lean) |

These are project proofs using the attributed Tau Ceti length-area and
boundary-cluster results. A general prime-end theory has not been introduced.


## Straight boundary sides and the Riemann sphere

| Result | Source |
| --- | --- |
| A disk map has a unique boundary limit from a chosen side of a straight boundary | [StraightBoundaryLimit](FunctionTheory/Conformal/StraightBoundaryLimit.lean) |
| The same assertion in translated and rotated coordinates | [StraightBoundaryCoordinates](FunctionTheory/Conformal/StraightBoundaryCoordinates.lean) |
| Two complex charts, reciprocal homeomorphism, and a complex-manifold structure on `OnePoint ℂ` | [RiemannSphere/Basic](FunctionTheory/RiemannSphere/Basic.lean) |

The first two are project proofs; the sphere atlas is attributed Ray code.


| Further result | Source |
| --- | --- |
| Continuous extension of a conformal disk map along a chosen straight boundary bank | [StraightBoundaryContinuous](FunctionTheory/Conformal/StraightBoundaryContinuous.lean) |
| Limits on either slit bank and injectivity of squaring on the right halfplane | [SlitBankLimit](FunctionTheory/Conformal/SlitBankLimit.lean) |
| Holomorphic spherical translation and a coordinate omitting an arbitrary finite point | [RiemannSphere/Coordinates](FunctionTheory/RiemannSphere/Coordinates.lean) |
| Riemann mapping for simply connected open spherical domains omitting two points | [RiemannSphere/RiemannMapping](FunctionTheory/RiemannSphere/RiemannMapping.lean) |
| Continuous disk-valued extension after unwrapping a slit tip by squaring a right half-disk | [SlitTipUnwrapped](FunctionTheory/Conformal/SlitTipUnwrapped.lean) |

The coordinate module identifies its adapted Ray chart proofs explicitly.
The spherical Riemann-map proof transports the attributed Tau Ceti plane theorem.


Local slit-tip boundary correspondence is proved in both directions, without
regularity assumptions on the rest of the boundary. Its proof uses square
unwrapping and Schwarz reflection. The inverse has an analytic extension at
the corresponding circle point; a separate continuity corollary is available.
Internally tangent circles yield Jordan curves through the tip. See
[SlitTipInverse](FunctionTheory/Conformal/SlitTipInverse.lean) and
[SlitTipJordanCurve](FunctionTheory/Conformal/SlitTipJordanCurve.lean).


The tangent-circle construction now gives compact Jordan enclosures after
undoing inversion, with only the designated tip on the boundary. The enclosures
eventually lie in every prescribed open neighbourhood of the removed set.
See [TangentEnclosure](FunctionTheory/Conformal/TangentEnclosure.lean) and
[TangentEnclosureNeighbourhood](FunctionTheory/Conformal/TangentEnclosureNeighbourhood.lean).


Local straight-boundary geometry now supplies a normalized conformal strip map
and both exponential end estimates without a global Jordan-frontier assumption:
[StripEndMapLocal](FunctionTheory/Conformal/StripEndMapLocal.lean).
[UniformStraightBoundary](FunctionTheory/Conformal/UniformStraightBoundary.lean)
gives a boundary-cap radius uniform over maps normalized at a fixed base point.
[ShrinkingGateKernel](FunctionTheory/Conformal/ShrinkingGateKernel.lean) separates
the kernel component on the right from a left decoration through a collapsing gate.

## Kernel convergence with the right end fixed

[RightEndKernel](FunctionTheory/Conformal/RightEndKernel.lean) proves
`rightEndRiemannMaps_tendsto_on_kernel`: decreasing simply connected domains
inside a horizontal strip, sharing its full right tail and the stated kernel,
have locally uniformly convergent disk maps normalized at an interior point
and the right end. [RightEndNormalization](FunctionTheory/Conformal/RightEndNormalization.lean)
provides existence, uniqueness and exponential strip-end estimates.
The proof derives boundary-value convergence from uniform local crosscut caps.
See the [proof and literature comparison](docs/RIGHT_END_NORMALIZATION.md).


[StripInverseUniformity](FunctionTheory/Conformal/StripInverseUniformity.lean)
proves uniform continuity of the inverse of a chart asymptotic to a translation
on a closed inset with bounded left truncations. It supplies the inverse
control used in the continuum construction's local charts.

## Analytic interpolation and zero sequences

- Analytic divided differences, repeated division by powers, and finite
  polynomial interpolation with an analytic remainder.
- Divisibility of an analytic error implies equality of its prescribed jets.
- Distinct zeros of a nonzero entire function, and distinct critical points
  of a nonconstant entire map, escape every compact set.

See [the theorem catalogue](MAIN_RESULTS.md#finite-interpolation-and-discrete-zero-sets).

## Meromorphic decomposition and compatible charts

- Clearing the finitely many singularities on a compact set by a polynomial,
  and splitting a meromorphic function into a rational part and a holomorphic remainder.
- Holomorphic composition on actual domains and backward transport of conformal charts.
- Finiteness of critical points on compact sets under local nonconstancy.

See [the public statements](MAIN_RESULTS.md#chart-normalization-and-meromorphic-decomposition).

## Smooth corrections

- [Global invertibility of small displacements](FunctionTheory/Smooth/NearIdentityHomeomorph.lean),
  with [smooth inverse](FunctionTheory/Smooth/NearIdentitySmooth.lean).
- [Uniform real derivative bounds for holomorphic errors](FunctionTheory/Smooth/ComplexDerivativeBounds.lean).
- [Controlled smooth compact extension](FunctionTheory/Smooth/ControlledExtension.lean).
- [Composition bounds on a fixed compact support](FunctionTheory/Smooth/CompactCompositionBounds.lean).
- [Holomorphic extension with composition control](FunctionTheory/Smooth/HolomorphicSmoothExtension.lean).
- [Smooth invertible limits of summable displacements](FunctionTheory/Smooth/SeriesDiffeomorphism.lean),
  including increasing orders of derivative control.
- [Finite critical neighbourhood chains](FunctionTheory/Conformal/CriticalNeighborhoodChain.lean).

These passed the full expanded FunctionTheory audit with 350 selected
reports. Only propext, Classical.choice and Quot.sound occur.

## Finite return maps and inverse branches

- [Finite Blaschke products](FunctionTheory/Conformal/FiniteBlaschke.lean):
  holomorphy across the closed disc, the boundary modulus identity, openness
  and disc surjectivity; [disc maps](FunctionTheory/Conformal/BlaschkeDiscMap.lean)
  align the factors with the attributed Tau Ceti Moebius convention.
- [Stable inverse branches](FunctionTheory/Conformal/StableInverseBranch.lean)
  persist under sufficiently small holomorphic perturbations on a compact
  target. [Derivative bounds](FunctionTheory/Conformal/InverseBranchContraction.lean)
  control inverse distances on convex targets.
- [Finite backward chains](FunctionTheory/Conformal/InverseBranchChain.lean)
  retain all intermediate domains and inverse identities.
  [Regularity](FunctionTheory/Conformal/InverseBranchRegularity.lean) follows
  from the holomorphic right-inverse identities.
- [Finite-orbit interpolation](FunctionTheory/Analytic/FiniteOrbitLocalDegree.lean)
  preserves values and centred local degrees of the full return, including
  critical points. [Orbit marks](FunctionTheory/Analytic/FiniteOrbitMarks.lean)
  supply the finite interpolation set.
- [Finite-iterate approximation](FunctionTheory/Topology/IterateApproximationDomains.lean)
  controls every intermediate domain as well as the final error;
  [matching orbit germs](FunctionTheory/Analytic/IterateGerms.lean) preserves
  the germ of the return map.


## Shrinking images and affine target preimages

- [Affine target noncontraction](FunctionTheory/Conformal/AffineTargetNoncontraction.lean)
  proves injective distance control and nonzero derivatives on all preimages
  of a prescribed compact target in a sufficiently close perturbation of an
  expanding affine map.
- [Shrinking image compactness](FunctionTheory/Topology/ShrinkingImages.lean)
  supplies a uniformly convergent subsequence when image diameters tend to
  zero in a sequentially compact uniform space. The source need not be compact
  and the maps need not be continuous.

## Local inverses and smooth Jordan boundaries

- [Compact conformal inverse](FunctionTheory/Conformal/CompactConformalInverse.lean):
  an injective noncritical holomorphic map on a compact set is conformal on
  a neighbourhood of that compact set, with a single inverse near its image.
- [Smooth Jordan curves](FunctionTheory/Topology/SmoothJordanCurve.lean):
  a definition including regularity, compatible with Tau Ceti's Jordan curves,
  with forward and backward transport through smooth local diffeomorphisms.
- [Boundary transport](FunctionTheory/Topology/LocalHomeomorphBoundary.lean):
  a local homeomorphism around a compact closure maps the whole frontier
  onto the frontier of the image.
- [Noncritical finite iterates](FunctionTheory/Analytic/IterateNoncritical.lean):
  finitely many nonzero orbit derivatives imply a nonzero iterate derivative.

## Univalent finite systems

- [Univalent finite compositions](FunctionTheory/Conformal/UnivalentFiniteComposition.lean)
  have conformal inverses on neighbourhoods of the initial compact and its image.
- [Finite composition stability](FunctionTheory/Conformal/UnivalentCompositionStability.lean)
  retains univalence near a compact set, uniform error bounds and every
  intermediate domain for close perturbations.
- [Forward coordinates](FunctionTheory/Conformal/UnivalentForwardCoordinates.lean)
  retain holomorphic directions, exact initial identity, neighbourhood
  conjugacies, finite-composition interpolation and prescribed displacement.
- [Mark compatibility](FunctionTheory/Conformal/FixedMarkCompatibility.lean)
  gives an adaptive tolerance excluding moved terminal marks and propagates
  fixed marks backwards through an injective conjugacy.

## Bloch, Schottky and normality foundations

- [Bloch's theorem](FunctionTheory/Conformal/BlochUnit.lean) supplies an
  injective subdisc whose image contains a disc of radius at least
  `norm (deriv f 0) / 256`, for a function analytic near the closed unit disc.
- [Derivative bounds from omitted image discs](FunctionTheory/Conformal/BlochDerivativeBound.lean)
  give the rescaled consequence on arbitrary discs.
- [Cosine lifts](FunctionTheory/Conformal/CosineLift.lean) and their
  [normalization](FunctionTheory/Conformal/NormalizedCosineLift.lean) reuse
  Tau Ceti's holomorphic logarithm and square-root branches.
- [Schottky's estimate](FunctionTheory/Conformal/SchottkyDisc.lean) bounds a
  function omitting zero and one on a smaller disc in terms of its central
  value. Explicit, nonoptimal constants are recorded in the statement.
- [Subsequence selection](FunctionTheory/Conformal/SchottkySelection.lean)
  bounds either a subsequence of the functions or their reciprocals, giving
  the local input to the sphere-valued omitted-values Montel theorem.

All these results are included in the passed 521-report audit. The
compatibility check for the public Li–Luo Zalcman development is separate
and does not yet constitute an installed or verified dependency.


## Zalcman and omitted-values Montel (verified 22 September 2026)

Li and Luo's public Zalcman rescaling theorem and selected supporting sphere
results are included with preserved proof statements and attribution; see
[the source record](third_party/NoWanderingDomains/README.md).
New reusable additions in [ZalcmanMontel](FunctionTheory/NormalFamilies/ZalcmanMontel.lean)
prove omitted-values Montel from this theorem, spherical Hurwitz, and Little
Picard. The spherical Hurwitz lemmas allow the approximants to be holomorphic
and to omit the value only eventually on each bounded disc, which is the
precise situation arising from rescaling an arbitrary open domain.
The finite-chart convergence argument is attributed to Li's public proof.

[LittlePicardBloch](FunctionTheory/Conformal/LittlePicardBloch.lean) states the
usual entire-function Little Picard theorem, aligned with ProjectVD's public
statement. Our proof uses Bloch and cosine lifts. The Zalcman–Montel proof
does not use the quantitative Schottky estimates. All these additions are
included in the passed **546-report** audit. The explicit identification
with the existing Fatou-set sphere uniformity is verified in WanderingDynamics.


## Analytic target-arc reflection (verified)

[AnalyticBoundaryContinuation](FunctionTheory/Conformal/AnalyticBoundaryContinuation.lean)
proves Schwarz reflection in an actual analytic target coordinate, transport
from half-disc reflection to a unit-disc continuation, and continuation
of a disc map continuous on its closed disc through a regular analytic
target arc. Injectivity is asserted on a neighbourhood of the boundary
point, not on the whole union with the original disc. The local target
coordinate and its domain-side orientation are explicit hypotheses.
These three results are included in the passed **549-report** audit.
The general boundary-extension theorem without closed-disc continuity,
and the remaining dynamical applications, are not claimed by this entry.

## Further boundary and punctured-domain results (22 September 2026)

The 563-report audit includes regular analytic boundary arcs in local
conformal coordinates, reflection from axis avoidance without a chosen
side, continuation through such arcs, and a nearby regular boundary point
for a possibly critical analytic extension. Circles satisfy this analytic
arc condition. Countably punctured plane discs are path connected; the
regular set of a meromorphic map is connected; nonconstant analytic maps
on connected domains have countable fibres and countable preimages of
countable sets. These support the meromorphic boundary application.

## Meromorphic continuation and proper disc maps (22 September 2026)

The passed 575-report audit includes pole images containing all sufficiently
large values, finite critical sets on compacta (including control near
poles), and escape of distinct meromorphic critical points. Rotational
identities continue on common regular domains with countable complements.

[Proper disc boundary estimates](FunctionTheory/Conformal/ProperDiscBoundary.lean)
and [zero factorisation](FunctionTheory/Conformal/ProperDiscZeros.lean) prove
uniform boundary collars, finite fibres and extraction of a finite zero
divisor. The factorisation uses Mathlib's existing `extract_zeros_poles`.
[Boundary maximum principles](FunctionTheory/Conformal/DiscBoundaryMaximum.lean)
use uniform limsup bounds without assuming a continuous boundary extension.
The complete proper-map / finite-Blaschke classification subsequently passed
the 579-report audit. See [its statement and proof map](docs/PROPER_DISC_MAPS.md).


The 589-report audit also proves the positive angular derivative of finite
Blaschke products, absence of boundary critical points, and the
[unicritical monomial classification](FunctionTheory/Conformal/BlaschkeUnicritical.lean).
[UnicriticalQuotient](FunctionTheory/Conformal/UnicriticalQuotient.lean) supplies
a removable quotient and strict real-part positivity from boundary data.

## Local analytic boundary continuation

A conformal disc chart extends analytically and locally injectively across a
regular analytic target boundary arc, without a global Jordan or closed-disc
continuity hypothesis. The proof allows slit domains. The component lemmas
include boundary-cap transfer in local coordinates and continuous extension
along an analytic boundary side. See the [statement guide](docs/LOCAL_ANALYTIC_BOUNDARY.md).

## Finite smooth univalent forward corrections

The 604-report checkpoint includes constructed prefix collars, a common
positive correction tolerance, fixed interpolation marks, initial identity,
prescribed supports and smooth norm bounds. Holomorphy of the inverse of an
analytic homeomorphism near the image compact is also proved. See the
[finite forward correction guide](docs/UNIVALENT_FORWARD_CORRECTIONS.md).
These are finite theorems; the infinite univalent realisation is unfinished.
