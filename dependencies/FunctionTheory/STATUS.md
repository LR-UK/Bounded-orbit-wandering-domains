# Project status

## Current wandering-dynamics development

The full build, source-integrity scan and all **608 selected axiom reports**
passed on 22 September 2026. The selected results use only
propext, Classical.choice and Quot.sound.

The SchottkyConfinement addition has passed the full audit. It proves
uniform confinement near the centre for holomorphic disc maps omitting
two fixed values, uniformly over compact sets of central values. No
separation from the omitted pair is required. The source radius is
independent of additional omitted values. The sibling area-deficit
project uses this to construct uniform local holomorphic lifts.
Finite-puncture uniformisation, hyperbolic area costs and the proposed
local wandering-orbit exclusion remain outside these results.

The supporting development for WanderingDynamics now includes the complete
finite critical-point correction and finite-chain theorems, controlled
smooth extension, smooth diffeomorphism limits and preservation of complex
differentiability on arbitrary compact sets. These support the fully proved
main triangle conjugacy theorem in the sibling paper project.

The latest return-map foundations prove stable inverse branches, finite backward
chains, orbit-germ preservation, finite-orbit local-degree interpolation, and
approximation with explicit intermediate-domain control. They support the
oscillating main construction, now proved in WanderingDynamics.

The latest additions also include positive-degree finite Blaschke products,
holomorphy across the closed disc, openness on a larger neighbourhood,
surjectivity of the disc map and compatibility with Tau Ceti Moebius factors.
Disc-image geometry and actual-domain holomorphic charts support the
wandering-domain applications. New reusable results give a conformal inverse
on a neighbourhood of an injective noncritical compact set, smooth Jordan
curve transport under local diffeomorphisms, and exact boundary transport
for local homeomorphisms defined around compact closures.

The univalent foundations now also give conformal finite prefixes, stable
forward coordinates, exact finite mark interpolation, and smooth extensions
with prescribed supports and derivative budgets. Their approximation estimate
controls the coordinate on the inverse image of a compact target collar.
These are finite ingredients; the full univalent realisation remains open.

The boundary-application foundations now include monomial prefix symmetries,
small root-of-unity rotations, continuation of functional identities through
regular analytic boundary charts, and critical-point transport for monomial
Blaschke models. Properness of finite Blaschke disc maps and a quantitative Bloch theorem
are now also independently verified. Normalized holomorphic cosine lifts have passed the full audit too.
The Schottky estimates and bounded-or-reciprocal subsequence selection
have also passed the full-library audit. Li and Luo's attributed Zalcman proof and the required sphere and
normal-family foundations are now installed and have passed the full audit.
The comparison with the existing dynamical normality predicate has passed
the WanderingDynamics audit. A Bloch-based Little Picard theorem has passed
this project's full audit. The assembled Zalcman–Hurwitz–Picard proof of
omitted-values Montel, including eventual holomorphy on expanding domains,
is installed and has passed the full audit.
The full nowhere-analytic-boundary theorem is now proved in WanderingDynamics.
Its reflection input includes verified continuation of closed-disc-continuous conformal
maps through an analytic target arc in a local conformal coordinate.
Regular analytic arcs are expressed intrinsically through conformal
coordinates; the reflection proof does not assume a chosen side. These
results now prove the entire monomial boundary examples in WanderingDynamics.
Further verified results give path connectedness of countably punctured
plane discs, connectedness of the regular set of a meromorphic map, and
countability of fibres and countable preimages of nonconstant analytic maps.

Earlier additions prove stability of preimages under perturbations of
finite holomorphic compositions, including critical orbits. Separate
positive tolerances control changes to the maps and target sets, and all
intermediate evaluations stay in their actual open domains. Supporting
results cover valid orbit domains, locally nonconstant compositions,
composition of conjugacy germs and closure of tail unions.

The five shared Eremenko univalence estimates retain their original names
through compatibility exports. The application's complete verification
passed after the refactor, with all 299 selected reports.

Historical source-hash checkpoints are preserved in the sibling
WanderingDynamics/docs directory. Current verification hashes are in
verification/summary.json. The boundary addendum is proved in WanderingDynamics; the paper's geometric
realisation results remain in development. New shared inputs include escaping
neighbourhood geometry, smooth patching, boundary barriers, separated
exhaustions, meromorphic sequence limits, local-degree preservation by finite
jets, and gluing meromorphic germs on disjoint compact pieces.

The library contains complete proofs only. The reused public foundations
include Riemann mapping, normalized uniqueness, Montel selection, Hurwitz,
Schwarz reflection, and Carathéodory continuous extension for bounded Jordan
domains. The last theorem does not itself assert boundary injectivity.

Our additional kernel-convergence results cover both bounded domains and
unbounded domains in a common horizontal halfplane. Direct maps and inverses
converge locally uniformly under the displayed kernel hypotheses.

The stronger geometric strip-map theorem is now
`FunctionTheory.exists_normalized_strip_map_of_straight_tail`
in `Conformal/StripEndMapLocal.lean`. A simply connected open subdomain of the
standard horizontal strip that contains its full sufficiently far right tail
is conformally equivalent to that strip, fixing a prescribed interior point
and the right end. Both exponential end estimates are proved. No Jordan or
local-connectedness assumption on the remaining boundary is required, and
boundedness to the left is unnecessary for this existence theorem.

The proof applies the unchanged public plane Riemann mapping theorem, the
new local straight-boundary continuity theorem, and Schwarz reflection of the
Cayley-normalized map. Its derivative at zero is positive real. The earlier
Jordan-boundary interface remains available. This is not a claim of the full
arbitrary-two-domains formulation of the paper's Lemma 7.2.

Derivative bounds and uniform neighbourhood control on closed strip insets
are proved. `StripKernelEscape` also proves uniform real-part escape from
inverse convergence on a closed strip. That boundary convergence is a
stronger input than the proved convergence on open domains.

Eremenko Theorem 1.2 is now proved in the sibling application, including
the stage insets, return maps, approximation induction and entire limit.
See its [complete proof map](../EremenkosConjecture/docs/THEOREM12_PLAN.md).
No additional FunctionTheory proof changes were needed at that final stage. The arbitrary-two-domains version of Lemma 7.2 is not claimed.

There are 138 attributed Tau Ceti modules: 137 match the pinned source after
line-ending normalization; one measure-theory dependency has the documented
measurability compatibility changes. The headline Riemann mapping, reflection,
and Carathéodory statements and proofs are unchanged. See
[provenance](PROVENANCE.md) and [compatibility](third_party/TauCeti/COMPATIBILITY.md).

Pinned environment: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

`StripProper` additionally proves that the restriction of a continuous map
with bounded displacement to a closed set is proper. The strip asymptotics
supply that displacement bound on closed insets, so their images are closed
and compact sets have compact preimages. No ambient extension is used.

`Topology/SimpleConnectivity` proves a compact-subset criterion for simple
connectivity: each loop contracts if every compact connected subset of the
open connected domain lies in a simply connected subdomain. The application
supplies such subdomains using filled continua and Jordan neighbourhoods.

The additional public inverse-cluster and monotone-extension route proves
boundary injectivity when the image has preconnected approach regions.
`Topology/BoundaryApproach` proves this approach property for convex sets and
transfers it through relative boundary charts. The application supplies the
Jordan-domain chart and derives the full closure-homeomorphism theorem.
No public hypothesis was removed without proof.

`SharedArcConvergence` now proves boundary convergence for injective disk
maps converging to the identity on the open disk. At each nonexceptional
circle point, a small boundary arc must eventually be mapped into the unit
circle. Convergence then holds locally uniformly on the closed disk away
from the exceptional set, hence uniformly on its compact subsets.

The proof constructs symmetric collars, obtains eventual nonvanishing from
Rouché and injectivity, reflects the maps in the circle, and applies Vitali.
Boundary convergence and a uniform lower bound are conclusions, not assumptions
of the final theorem. This is saved as an auxiliary classical result. Following
the author's clarification, the intended application proof of (7.3) now uses
a large-modulus separating quadrilateral instead of boundary convergence.

`StripClosedCoordinates` separately constructs finite closed-strip coordinates
and proves continuity of the logarithmic inverse made from a disk boundary map.

The author's separating-quadrilateral argument now has a checked analytic
implementation. `ThinAttachmentEscape.uniform_left_escape_of_shrinking_attachment`
(the declaration is in the `FunctionTheory` namespace) proves uniform escape
of every point on the attached side. The source domain contains a right
half-annulus; its intersection with the vertical attachment line shrinks to
the attachment point. The normalized disk maps and continuous inverses satisfy
their usual inverse identities. The maps converge locally uniformly inside the
limiting domain, whose fixed map tends to -1 along the reference ray.

These explicit geometric and kernel hypotheses imply that all real parts of
the strip images on the attached side eventually lie below any prescribed
real bound. Boundary convergence of the varying maps is not assumed. The
length-area estimate is uniform in the domain and map, and the inner radius
is chosen before either. Application-specific domain construction remains
outside this theorem.

Local Caratheodory continuity at a straight slit tip is now proved. If an open
domain agrees with the slit plane near zero, every conformal bijection from
that domain to the unit disk has a unique limit on the unit circle at zero.
There is no regularity assumption on the rest of the domain boundary.
`CircularArcCap`, `LocalCircularBoundary`, `SlitTipBoundary` and
`SlitTipCoordinates` supply the short-crosscut estimate, shrinking image caps,
singleton cluster set, exact slit geometry, and affine coordinate transfer.

`ExteriorCoordinate` represents a spherical exterior using inversion, explicitly
including zero as the image of infinity. It proves openness, connectedness for
a full compact removed set containing the pole, and unboundedness of inverted
sets approaching that pole. The application proves simple connectivity and
constructs the exterior map for a continuum with an attached segment.

The local boundary results now also give a limit from either selected side of
a straight boundary, even when the domain lies on both sides. The affine
coordinate version applies along either bank of an attached slit. These are
forward limits. The inverse boundary correspondence at the tip is now proved
by the unwrapping and reflection argument described below.

The Riemann sphere now has a checked complex-manifold atlas on `OnePoint ℂ`,
adapted from Geoffrey Irving's Ray project with attribution. It uses the
finite and reciprocal charts. The sphere-domain Riemann mapping theorem is now proved: a simply connected
open spherical domain omitting two distinct points is biholomorphic to the
disk, including when it contains infinity. Both directions use actual domains
and Mathlib's complex-manifold calculus. See the
[statement and proof route](docs/RIEMANN_SPHERE.md) and [provenance](PROVENANCE.md).


`StraightBoundaryContinuous` proves a continuous extension over a smaller
closed half-neighbourhood along a selected straight boundary bank. The boundary
values lie on the unit circle. `SlitBankLimit` applies the one-sided limit to
either bank of a locally straight slit and verifies the square-coordinate
geometry used to unwrap its free tip. The subsequent inverse and curve
results use these checked local inputs.

`SlitTipUnwrapped` now constructs the continuous extension of `z ↦ f(z²)`
over the closed diameter of a right half-disk. It proves holomorphy and
injectivity on the open half, disk-valuedness there, and unit-circle values
on the diameter. The two banks use their respective local limits, joined
by the slit-tip limit at zero. `HalfDiskCircleReflection` reflects the
Cayley-normalized map. `SlitTipInverse` proves analytic extension of its inverse
at the corresponding circle point, and separately states the weaker inverse
continuity needed by the application. `SlitTipInverseCoordinates` transfers
the result to affine coordinates and proves that the forward and inverse limits
correspond to the same circle point.

`BoundaryPointExtension`, `TangentDiskGeometry`, and `SlitTipJordanCurve`
construct Jordan images of internally tangent circles through the tip. All
other curve points lie in the domain; sufficiently large tangent disks give
curves avoiding the image of zero. `TangentJordanDomain` identifies the image
of each tangent disk as a bounded Jordan domain. `InvertedDomain` proves that
undoing the reciprocal coordinate gives a compact set with exactly the inverted
boundary. `TangentEnclosure` proves enclosure of the removed set, with every
point except the tip in the interior. `TangentEnclosureNeighbourhood` proves
that these enclosures eventually lie in every prescribed open neighbourhood.
The application now supplies fullness and regularity by the Jordan theorem.
The application now joins a compact decoration to a straight tail by filling
the attached sets; the resulting open domains and their kernels are proved.


`ShrinkingGateKernel` proves that a gate collapsing to a point is absent from
the open kernel. The component seen from a base point on the right stays on
the right, even when the left decoration has interior.

`UniformStraightBoundary` makes the short-crosscut radius uniform over domains
and disk maps with a fixed interior base point and a common straight boundary
neighbourhood. `StraightBoundaryConvergence` and `StripBoundaryConvergence`
now prove convergence of the corresponding boundary values. `RightEndKernel`
proves locally uniform convergence of disk maps fixing an interior base point
and the right end, for decreasing strip domains with a common straight tail
and the displayed kernel. Boundary convergence is a conclusion, not an
additional hypothesis. `RightEndNormalization` gives existence, uniqueness
and both strip-end estimates for this normalization. The actual filled-domain
family is assembled in the application. See the
[normalization note and references](docs/RIGHT_END_NORMALIZATION.md).

`RightEndSymmetry` proves reflection symmetry and convergence along the real
axis for this normalization. `HalfStripEndpoint` identifies the opposite
finite endpoint with -1. `ContinuousPostcomposition` transfers local uniform
convergence through the disk-to-strip coordinate. `CompactCompression`
chooses a positive scale and one map satisfying both uniform control on a
compact set and a prescribed leftward bound on a second set. The application
supplies actual families and verifies the hypotheses.


`StripInverseUniformity` supplies uniform inverse continuity on closed strip
insets from translation asymptotics. The full build and 248 selected axiom
reports pass. This is a classical input to the ongoing continuum induction.

## Finite interpolation and critical-point sequences — 20–21 September

`Analytic/FiniteInterpolation.lean` proves analytic division with a polynomial
remainder at finitely many marked points, allowing variable orders, and the
corresponding equality of lower derivatives. `Analytic/ZeroSequences.lean`
proves that distinct zeros of a nonzero entire function escape every compact
set, and the corresponding statement for critical points of a nonconstant
entire function. Seven new declarations are included in the 255-result audit.
These are foundations for the separate WanderingDynamics project; they are
not proofs of its main realization theorems.

## Resumed wandering-dynamics foundations — 21 September

Chart transport now proves that pulling charts back through conformal
isomorphisms makes the intervening associated functions exactly the identity,
while retaining a prescribed return map as the first one-step map. Both
holomorphic directions and actual domains are preserved.

Compact meromorphic decomposition writes f=p/q+g away from the denominator
zeros, where g is holomorphic near the compact set and q has zeros only at
singular points there. Actual-domain meromorphy is compatible with Mathlib's
MeromorphicAt. A locally nonconstant holomorphic map has finitely many critical
points in any compact subset of its domain, even if that domain is disconnected.

These twelve additional declarations pass the full build and the 267-result
axiom audit. The audit parser also recognizes Lean's axiom-free report format;
missing, extra, duplicate and forbidden-axiom reports remain rejected.


## Smooth extension and limits — 21 September

The full build, source-integrity check and all 350 selected axiom reports
passed. The new development includes controlled smooth extension in the
uniform C^m norm, the actual-domain holomorphic version, composition bounds
using fixed compact support, and smooth invertible limits with increasing
derivative control. Boundary complex differentiability is retained even
when the holomorphic neighbourhoods of the summands shrink.

The original smooth cutoff proofs were moved from ComplexApproximation
without mathematical changes; their Runge names remain available.
ComplexApproximation also passed its full build, RungeTargets and 133
selected reports after the move.

The finite critical-neighbourhood chain supplies image containment and
critical-point control on closures from compact model data. The adaptive triangle and the main escaping and oscillating realisations
in WanderingDynamics are now proved; further application targets remain open. See [the smooth proof guide](docs/SMOOTH_CORRECTION.md).

The 442-report independent audit also includes escaping auxiliary discs,
stable inverse branches, inverse contraction, finite-orbit local degrees,
and finite backward chains. The affine-channel module is included in the current audit.

## Univalent forward-coordinate foundations

The finite univalent composition, perturbation stability, canonical forward
coordinates with exact marks and displacement bounds, and adaptive mark
compatibility lemmas are proved. These are foundations for the still
unfinished univalent triangle and main realisation in WanderingDynamics.
The manuscript support issue is recorded as M16 in that project's review.

The latest 568-report audit also verifies rotational continuation on the
common regular domain after countably many punctures, the local image
of a pole containing every sufficiently large value, and escape of any
sequence of distinct critical points of a locally nonconstant meromorphic
function. The critical-point argument includes neighbourhoods of poles;
no global meromorphy of higher iterates is assumed.

The proper-disc classification development now includes uniform boundary
collars, finite fibres, finite zero-divisor support and extraction of all
zeros using Mathlib's factorisation. A maximum principle formulated by
boundary limsup needs no boundary extension of the original map. These now give the full finite Blaschke classification, with both
distinct-zero/multiplicity and repeated-zero interfaces. See the
[statement and proof guide](docs/PROPER_DISC_MAPS.md). The unicritical-to-monomial consequence has also passed the full audit.
Its proof uses the positive angular derivative and a removable quotient,
followed by the maximum principle, rather than a critical-point count.

The classification now transports through arbitrary conformal charts, with
properness on actual source and target domains. Boundary-cap estimates for
closed source pieces and local short arcs support extension in nonlinear
analytic coordinates; that general local extension has now passed the full audit.

The general local analytic-boundary continuation theorem now passes the full audit.
It needs neither a Jordan boundary nor global closed-disc continuity; see
[the statement and proof map](docs/LOCAL_ANALYTIC_BOUNDARY.md).
