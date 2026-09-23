# Main results

[Lean statement gallery](FunctionTheory/MainTheorems.lean) · [Proof map](PROOF_MAP.md)

## Conformal correction and compact stability

The classical conformal-correction theorem is in
[FiniteCriticalCorrection](FunctionTheory/Conformal/FiniteCriticalCorrection.lean):
if phi is holomorphic on U, V has compact closure in U, and the finite marked
set C inside V contains every critical point in U, then sufficiently close
holomorphic g with the same marked values and critical multiplicities admits
a conformal change theta on V with g composed with theta equal to phi.
The change has arbitrarily small uniform displacement, fixes all of C,
maps into U, and has a holomorphic inverse on its image. This is the full
one-map correction lemma, including the critical case. The proof has compiled;
all 316 selected declarations passed the full build and axiom audit.

Its proof uses the [regular case](FunctionTheory/Conformal/RegularCorrection.lean),
[quantitative critical disks](FunctionTheory/Conformal/CriticalCorrectionRadius.lean),
[finite disk geometry](FunctionTheory/Topology/FiniteDiskGeometry.lean), and
[gluing with a collar](FunctionTheory/Conformal/ConformalLiftGluing.lean).

Other reusable additions are [compact preimage stability](FunctionTheory/Analytic/PreimageStabilityLocalDomain.lean),
[stability of finite compositions on actual domains](FunctionTheory/Topology/FiniteCompositionLocalDomain.lean),
and [openness versus local nonconstancy](FunctionTheory/Analytic/OpenHolomorphic.lean).
These precede the critical-case increment and passed the 299-report audit.

## Conformal mapping foundations

| Result | Exact declaration | Source and scope |
| --- | --- | --- |
| Riemann mapping | `TauCeti.riemannMapping` | [Upstream proof](TauCeti/Analysis/Complex/Conformal/RiemannMapping/Existence.lean); proper simply connected open domains |
| Normalized Riemann mapping | `TauCeti.riemannMapping_normalized` | [Normalization](TauCeti/Analysis/Complex/Conformal/RiemannMapping/Normalization.lean); specified basepoint maps to zero and derivative is positive real |
| Map defined on its actual domain | `FunctionTheory.exists_riemannMap_on_domain` | [Interface](FunctionTheory/Conformal/RiemannMapping.lean); a homeomorphism `U ≃ₜ ball 0 1`, holomorphic in both directions |
| Schwarz reflection | `TauCeti.exists_differentiableOn_eqOn_conj_of_symmetric` | [Principle](TauCeti/Analysis/Complex/Conformal/Reflection/Principle.lean); the precise symmetry and boundary hypotheses are in the declaration |
| Montel selection | `TauCeti.montel` | [Selection theorem](TauCeti/Analysis/Complex/Conformal/Montel/Basic.lean); locally bounded holomorphic families |
| Hurwitz injectivity | `TauCeti.hurwitz_injOn` | [Hurwitz](TauCeti/Analysis/Complex/Conformal/Hurwitz.lean); nonconstant locally uniform limits of injective holomorphic maps |
| Bounded kernel convergence | `FunctionTheory.normalized_riemannMaps_tendsto_on_bounded_kernel` | [Convergence](FunctionTheory/Conformal/KernelConvergence.lean); both maps and inverses |
| Unbounded halfplane kernel convergence | `FunctionTheory.normalized_riemannMaps_tendsto_on_halfPlane_kernel` | [HalfPlaneKernel](FunctionTheory/Conformal/HalfPlaneKernel.lean); a common lower bound on imaginary parts replaces boundedness |

For the bounded theorem, the domains `U n` are decreasing and open, `U 0` is
bounded, the maps are normalized at the same point, and the proposed kernel
`V` is open and connected, contains that point, and lies in every `U n`.
The component containing the basepoint of `interior (⋂ n, closure (U n))`
must lie in `V`. These hypotheses are explicit: the result does not silently
identify an arbitrary intersection with the kernel.

The halfplane version has the same normalization and kernel hypotheses, with
`-M ≤ im z` on `U 0` replacing boundedness. More generally, the library proves
convergence whenever the inverse maps form a locally bounded family. Existence
versions also construct the normalized limit map on the kernel.

`FunctionTheory.IsHolomorphicFunctionOn U f` accepts `f : U → ℂ`. It uses local
differentiable representatives to interface with Mathlib. Its compatibility
name `Runge.IsHolomorphicFunctionOn` denotes the same property.

The general decorated-halfstrip construction and Theorem 1.2 are proved
in EremenkosConjecture. Kernel convergence and the whole-continuum separation
estimate are distinct inputs to that proof. See the
[application map](../EremenkosConjecture/docs/THEOREM12_PLAN.md).

The [reflected-end estimates](FunctionTheory/Conformal/StripEndAsymptotics.lean)
formalise the analytic calculation underlying Lemma 7.2 once the reflected
map at zero is supplied. Their hypotheses are analyticity, a simple zero,
and, for the logarithm estimate, the slit-plane condition on its derivative.
The stronger local-boundary theorem now supplies this extension from a straight right tail alone; see the new statement below.

The [imaginary-axis reflection interface](FunctionTheory/Conformal/ImaginaryReflection.lean)
keeps the public theorem's continuity on the closed side, holomorphy on the
open side, symmetry, and boundary-value hypotheses explicit.
[StripBounds](FunctionTheory/Conformal/StripBounds.lean) proves uniform upper
and positive lower derivative bounds on a closed strip inset once the
derivative asymptotic and conformal neighbourhood have been supplied.

## Reflected maps and strip asymptotics

| Result | Source | Precise scope |
| --- | --- | --- |
| Conformal Schwarz reflection with positive derivative at zero | [ReflectionInjectivity](FunctionTheory/Conformal/ReflectionInjectivity.lean) | Requires continuity on the closed half, holomorphy and injectivity on the open half, axis values on the axis, and preservation of the right halfplane. Boundary injectivity is proved. |
| Both strip-end asymptotics with a real translation constant | [StripEndCoordinates](FunctionTheory/Conformal/StripEndCoordinates.lean) | Requires the reflected analytic map with positive derivative and the exponential identity. Bounds in source and target strips determine the logarithm branch. |
| Uniform neighbourhoods and continuity on strip insets | [StripUniformity](FunctionTheory/Conformal/StripUniformity.lean) | Closed sets bounded to the left and in imaginary part, with explicit control at the right end. |

The first two are also named in the Lean gallery as
`conformal_schwarz_reflection` and `strip_end_asymptotics`. Their geometric
hypotheses are supplied in the application for the required domains.

[StripKernelEscape](FunctionTheory/Conformal/StripKernelEscape.lean) proves
uniform real-part escape of a closed set from inverse convergence on a
**closed** strip, inverse identities and omission of the set by the limit.
It records the stronger boundary-convergence input needed in the continuum
application; convergence only on the open strip does not imply its hypothesis.

## Boundary normalization and the geometric strip theorem

| Gallery declaration | Source | Precise scope |
| --- | --- | --- |
| `caratheodory_continuity` | [Public Carathéodory proof](TauCeti/Analysis/Complex/Conformal/Caratheodory.lean) | A conformal disk map with bounded image and Jordan frontier extends continuously to the closed disk. Boundary injectivity is not asserted. |
| `boundary_normalized_riemann_map` | [JordanBoundary](FunctionTheory/Conformal/JordanBoundary.lean) | Bounded simply connected Jordan domain, prescribed interior and boundary points; actual-domain homeomorphism, holomorphic in both directions, with a continuous closed-disk extension. |
| `normalized_strip_map` | [StripEndMap](FunctionTheory/Conformal/StripEndMap.lean) | Simply connected domain inside the standard strip, bounded to the left and containing its full right tail, with Jordan boundary after exponentiation. Constructs a conformal strip map fixing the basepoint and right end, with both exponential asymptotics. |

All three statements are visible in the [Lean gallery](FunctionTheory/MainTheorems.lean).
The strip theorem derives the reflected analytic inverse from the geometry;
it does not assume that inverse as extra data. The compact enclosure, actual filled domains, exact kernel and analytic
uniform escape estimate are proved. The family normalization and the
complete Theorem 1.2 induction are also now proved in EremenkosConjecture.

## Convergence up to a shared boundary

Injective holomorphic disk self-maps that converge to the identity inside the
disk also converge locally uniformly up to boundary arcs that they eventually
preserve. The exceptional boundary points can be excluded explicitly. The
statement and proof are in
[SharedArcConvergence](FunctionTheory/Conformal/SharedArcConvergence.lean).
This auxiliary theorem is preserved independently of the chosen proof of (7.3).

## Uniform escape behind a narrowing attachment

The main statement is
`FunctionTheory.uniform_left_escape_of_shrinking_attachment` in
[ThinAttachmentEscape](FunctionTheory/Conformal/ThinAttachmentEscape.lean).
For conformal disk maps converging inside a limiting domain, a narrowing
attachment along a straight boundary forces the whole attached side towards
one boundary point. In strip coordinates its real parts tend uniformly to
minus infinity. The theorem states the domain geometry and normalization
explicitly. It requires no boundary convergence of the varying maps.

This implements the length-area form of the author's large-modulus
quadrilateral argument for equation (7.3). The paper-specific decorated
domains and their kernel normalization are constructed in EremenkosConjecture.

## Local boundary continuity at a slit tip

`FunctionTheory.exists_boundary_limit_at_slit_tip` in
[SlitTipBoundary](FunctionTheory/Conformal/SlitTipBoundary.lean) proves that a
conformal bijection to the disk has a unique unit-circle limit at a free
straight-slit endpoint. The domain need only agree locally with the slit
plane. No global Jordan-boundary condition or prime-end structure is assumed.

The more general circular-crosscut criterion is in
[LocalCircularBoundary](FunctionTheory/Conformal/LocalCircularBoundary.lean).
[SlitTipCoordinates](FunctionTheory/Conformal/SlitTipCoordinates.lean) transports
the conclusion through the affine coordinate used by the application.


The companion [straight-side theorem](FunctionTheory/Conformal/StraightBoundaryLimit.lean)
gives a unique limit from either selected bank of a locally straight slit.
The domain may have points on both sides; only the selected approach side is
used. [Affine coordinates](FunctionTheory/Conformal/StraightBoundaryCoordinates.lean)
allow translation and rotation. [SlitTipUnwrapped](FunctionTheory/Conformal/SlitTipUnwrapped.lean)
constructs a continuous extension of the map after the square coordinate
unwraps the slit tip into a diameter. It retains holomorphy and injectivity
on the open half-disk and maps the diameter into the unit circle.

## Riemann-sphere foundations

[RiemannSphere/Basic](FunctionTheory/RiemannSphere/Basic.lean) equips `OnePoint ℂ`
with the standard complex-manifold structure. Thus the sphere is both the
one-point compactification and a Riemann surface; these are compatible layers
on the same type. The atlas is adapted from attributed public Ray code.

**Spherical Riemann mapping is proved:** every simply connected open subset
of the sphere omitting two distinct points is biholomorphic to the unit disk.
The domain may contain infinity. Both directions are functions only on their
actual open domains, and holomorphy uses Mathlib's complex-manifold calculus.

The exact declaration is `FunctionTheory.exists_riemannMap_on_sphere_domain`
in [RiemannSphere/RiemannMapping](FunctionTheory/RiemannSphere/RiemannMapping.lean).
It also appears as `spherical_riemann_mapping` in the
[main theorem gallery](FunctionTheory/MainTheorems.lean).
See the [sphere theorem note](docs/RIEMANN_SPHERE.md) for the statement and proof route.


## Strip maps from local end geometry

[`exists_normalized_strip_map_of_straight_tail`](FunctionTheory/Conformal/StripEndMapLocal.lean)
constructs the conformal map onto the standard strip from any simply connected
open subdomain containing the full right tail. It fixes the interior basepoint
and the right end, and proves

    phi'(z) = 1 + O(exp(-Re z)),
    phi(z) = z + rho + O(exp(-Re z)), with rho real.

There is no Jordan-boundary or local-connectedness assumption away from the
right end. The earlier gallery theorem remains valid with its stronger
hypotheses. The new proof is in
[StraightBoundaryDirect](FunctionTheory/Conformal/StraightBoundaryDirect.lean).

## Kernel convergence with the right end fixed

[RightEndKernel](FunctionTheory/Conformal/RightEndKernel.lean) proves
`rightEndRiemannMaps_tendsto_on_kernel`: decreasing simply connected domains
inside a horizontal strip, sharing its full right tail and the stated kernel,
have locally uniformly convergent disk maps normalized at an interior point
and the right end. [RightEndNormalization](FunctionTheory/Conformal/RightEndNormalization.lean)
provides existence, uniqueness and exponential strip-end estimates.
The proof derives boundary-value convergence from uniform local crosscut caps.
See the [proof and literature comparison](docs/RIGHT_END_NORMALIZATION.md).

For the same normalization, [HalfStripEndpoint](FunctionTheory/Conformal/HalfStripEndpoint.lean)
identifies the finite left endpoint with -1 in the disk. Together with
[CompactCompression](FunctionTheory/Conformal/CompactCompression.lean), the
uniform left-escape theorem gives simultaneous compact control and escape
after a single positive rescaling. The application combines these inputs
with its completed recursive construction to prove Theorem 1.2.

## Finite interpolation and discrete zero sets

- [Analytic polynomial remainder](FunctionTheory/Analytic/FiniteInterpolation.lean):
  `exists_polynomial_analytic_remainder` gives f=p+Qg with g analytic on the
  original neighbourhood and Q having the chosen finite zero multiplicities.
  The file also proves the corresponding finite-derivative equality criterion.
- [Escaping critical-point sequences](FunctionTheory/Analytic/ZeroSequences.lean):
  `tendsto_norm_atTop_of_injective_critical_points` proves that any sequence
  of distinct critical points of a nonconstant entire map tends to infinity.

## Chart normalization and meromorphic decomposition

- [Chart transport](FunctionTheory/Conformal/ChartTransport.lean):
  `pullbackChart_tail_step` gives identity associated maps between compatible
  pulled-back charts; `pullbackChart_prescribed_step` retains the prescribed
  map at the start of a return block. `pullbackChart_holomorphic` preserves
  holomorphy in both directions on the actual domains.
- [Compact meromorphic decomposition](FunctionTheory/Meromorphic/CompactDecomposition.lean):
  `exists_rational_analytic_remainder` gives f=p/q+g off the zeros of q,
  with g holomorphic near the compact set and denominator zeros confined to
  singular points. [Local-domain meromorphy](FunctionTheory/Meromorphic/LocalDomain.lean)
  supplies `IsMeromorphicFunctionOn` and its Mathlib compatibility theorem.
- [Finite critical sets](FunctionTheory/Analytic/CompactCriticalPoints.lean):
  `finite_critical_points_of_locally_nonconstant` supplies the finite critical
  markings needed in the non-autonomous construction.

## Smooth extension and convergence

The smooth correction development has individually compiled: small
Lipschitz displacements give global smooth diffeomorphisms; cutoff and
Cauchy bounds give controlled extensions near compact sets; a fixed compact
support controls composition with preceding coordinates; and summable
displacements with increasing derivative control give a smooth invertible
limit. See [the smooth proof guide](docs/SMOOTH_CORRECTION.md) for exact
statements and dependencies. The full expanded 350-report audit passed.

[CriticalNeighborhoodChain](FunctionTheory/Conformal/CriticalNeighborhoodChain.lean)
chooses a finite chain of relatively compact working neighbourhoods with
the required image containment and critical-point control on their closures.
This supplies the strengthened finite-chain hypothesis from compact model data.
