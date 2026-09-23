# Auxiliary classical results

The Section 7 additions are catalogued in the [progress page](docs/SECTION7_PROGRESS.md): uniform conformal stability on unbounded sets, quantitative ambient extensions, fullness from compact pieces, and connected-component barrier lemmas. Both the implication from `RayConstructionData` and the unconditional existence of those data are proved, yielding Theorem 7.1.

[Main results](MAIN_RESULTS.md) · [Proof map](PROOF_MAP.md) · [Complete module index](docs/MODULE_INDEX.md)

This catalogue separates reusable analysis and topology from the paper's
final dynamical existence results. These statements were proved in the
development, often by combining existing Mathlib results. The catalogue
does not assert novelty. Full signatures and exact hypotheses are at the links.

| Result and scope | Checked declaration(s) | Role |
| --- | --- | --- |
| Uniform control of a map on a neighbourhood controls finitely many iterates on a compact orbit (Lemma 2.5 and its compact form). | [iterate_approximation_of_uniform_control](EremenkosConjecture/IterateApproximation.lean#L36); [iterate_approximation_on_compact](EremenkosConjecture/IterateApproximation.lean#L100) | Stable orbit itineraries. |
| Sufficiently close holomorphic approximations retain injectivity, image control and nonzero derivative on a compact subset of a conformal chart (compact Lemma 2.3). | [exists_injective_approximation_tolerance](EremenkosConjecture/Univalence.lean#L65); [exists_derivative_approximation_tolerance](EremenkosConjecture/Univalence.lean#L96); [approximation_of_univalent_on_compact](EremenkosConjecture/Univalence.lean#L127) | Preserve the finite-stage conformal maps. |
| Compact Corollary 2.7: retain the preceding univalence properties for finitely many iterates. | [approximate_univalent_iterates_on_compact](EremenkosConjecture/UnivalentIterates.lean#L14) | Persistence of the inductive constraints. |
| Locally summable corrections between entire functions give an entire limit, with an explicit tail-error bound. | [exists_entire_limit_of_locally_summable_corrections](EremenkosConjecture/EntireLimit.lean#L37); [limit_error_le_tsum](EremenkosConjecture/EntireLimit.lean#L54) | Pass from polynomial stages to an entire function. |
| A bounded plane set with no bounded complementary component has connected complement. | [isConnected_compl_of_unbounded_components](EremenkosConjecture/PlaneTopology.lean#L43) | Elementary fullness criterion. |
| Polynomial separation of every exterior point implies fullness of a compact set, by the maximum principle. | [isConnected_compl_of_polynomial_separation](EremenkosConjecture/PlaneTopology.lean#L78) | Construct full neighbourhoods. |
| Full compact sets have full compact neighbourhoods inside every open neighbourhood, and nested such neighbourhoods with the prescribed intersection. | [exists_full_compact_neighbourhood](EremenkosConjecture/FullNeighbourhoods.lean#L16); [exists_nested_full_compact_neighbourhoods_within](EremenkosConjecture/FullNeighbourhoods.lean#L137) | Compact part of the Section 2 neighbourhood machinery. |
| Adjoining finitely many points preserves fullness; a separated pair of full compacta has full union. | [isConnected_compl_union_finite](EremenkosConjecture/FullUnions.lean#L48); [isConnected_compl_union_separated](EremenkosConjecture/FullUnions.lean#L76) | Simple gluing configurations. |
| Any disjoint pair of full compact plane sets has full union. | [isConnected_compl_union_disjoint](EremenkosConjecture/DisjointFullUnions.lean#L16) | Compact consequence of the general nonseparation theorem now in ComplexApproximation. |
| Small holomorphic perturbations of the identity, or of a chart already agreeing with a plane homeomorphism, agree on the specified compact set with a plane homeomorphism. | [exists_homeomorph_tolerance_near_id](EremenkosConjecture/AmbientExtension.lean#L45); [exists_homeomorph_approximation_tolerance](EremenkosConjecture/AmbientExtension.lean#L74) | A sufficient construction invariant; not a general conformal extension theorem. |
| A compact conformal chart has a positive derivative lower bound; its local conformal properties persist under sufficiently small perturbations with the stated ambient hypothesis. | [exists_pos_derivative_lower_bound](EremenkosConjecture/ConformalCharts.lean#L30); [exists_ambient_conformal_approximation_tolerance](EremenkosConjecture/ConformalCharts.lean#L54) | Chart stability. |
| Glue holomorphic neighbourhood data on disjoint compact pieces, then approximate when the union is full. | [exists_holomorphic_gluing](EremenkosConjecture/HolomorphicGluing.lean#L16); [polynomial_approximation_two_pieces](EremenkosConjecture/HolomorphicGluing.lean#L51) | Runge extension step. |
| Finite nets on nested compact boundaries approximate every point of the limiting boundary. | [exists_boundary_approximating_sequence](EremenkosConjecture/BoundaryApproximation.lean#L11) | Trapped points accumulate where needed. |
| A finite subset of a path-connected space lies on a loop. | [exists_loop_through_finset](EremenkosConjecture/FinitePath.lean#L9) | Finite polygonal covering step. |
| A full plane continuum has a compact Jordan neighbourhood inside any prescribed open neighbourhood. | [exists_jordan_compact_neighbourhood](EremenkosConjecture/ComplexJordanNeighbourhood.lean#L21) | Uses the selected Schoenflies polygonal topology dependency. |
| Nested Jordan neighbourhoods shrink to a full continuum. | [exists_nested_jordan_neighbourhoods_within](EremenkosConjecture/NestedJordanNeighbourhoods.lean#L37) | The connected case needed for the path barriers; not the disconnected finite-union refinement. |
| No continuous curve crosses all the prescribed shrinking barriers with alternating openings. | [no_curve_through_alternating_openings](EremenkosConjecture/PathBarriers.lean#L38) | Prevent escaping and Julia paths from leaving. |
| A bounded plane set with interval-shaped vertical sections is full. | [isConnected_compl_of_vertical_fibers](EremenkosConjecture/VerticalFibers.lean#L38) | Fullness of the sine-chain continuum. |
| At any specified point there is a nontrivial full continuum whose path component at that point is a singleton. | [exists_full_continuum_singleton_pathComponent](EremenkosConjecture/SingletonContinuum.lean#L60) | Extend Theorem 3.4 to singleton continua. |
| Two points of an open connected plane set can be carried to one another by a plane homeomorphism equal to the identity outside that set. | [exists_supportedMove](EremenkosConjecture/PointMoving.lean#L92) | Local modifications in the lake construction. |
| Compactness controls a nested sequence relative to a neighbourhood of its intersection; a decreasing sequence of nonempty compact connected plane sets has connected intersection. | [exists_stage_subset_open](EremenkosConjecture/NestedContinua.lean#L8); [isConnected_nested_inter](EremenkosConjecture/NestedContinua.lean#L22) | Limit land in the Wada construction. |
| Countably infinitely many pairwise disjoint bounded domains can share one compact connected boundary. | [exists_countably_many_lakes_of_wada](EremenkosConjecture/LakesOfWada.lean#L9) | Unconditional topological existence theorem before the dynamical application. |

## Reused results and attribution

- Runge and domain nonseparation come from the sibling **ComplexApproximation** library.
- Normality, Julia/Fatou criteria, scaling and fast-escape estimates come from **ComplexDynamics**.
- Polygonal outer-face and Jordan ingredients come from the selected **Schoenflies**
  sources vendored here, with their original licence and attribution. They are not
  claimed as original developments of this project.
- Mathlib supplies the underlying topologist's sine-curve example. The compact
  truncations, shrinking chain and singleton-path-component consequence are developed here.
- General Schwarz, maximum-principle, compactness, path and homeomorphism-extension
  tools are imported from Mathlib. The catalogue records the additional results
  obtained using those tools.

See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) and
[topology sources](docs/TOPOLOGY_SOURCES.md). The full unbounded Section 2 estimates,
and the disconnected Jordan refinement remain unproved. Neighbourhood-holomorphic
Arakelian approximation is now proved in the sibling ComplexApproximation project.

## Section 4 additions

| Result | Source | Use |
|---|---|---|
| A uniform function error on a disk bounds the derivative error at its centre. | [norm_deriv_sub_le_of_close_on_ball](EremenkosConjecture/UniformUnivalence.lean) | Unbounded strip estimates. |
| A holomorphic map uniformly close to the identity on a neighbourhood of a closed disk covers its centre. | [exists_preimage_of_close_to_id_on_closedBall](EremenkosConjecture/UniformUnivalence.lean) | Coverage of the next source and target strips. |
| An injective holomorphic map with nonzero derivative on an open set gives a conformal chart onto its image. | [exists_conformal_chart_of_injOn](EremenkosConjecture/ConformalEmbedding.lean) | Local inverse branches without extension to the plane. |
| Small uniform perturbations of multiplication by five on the source strips have the conformal inverse domains and derivative bounds of Lemma 4.1. | [lemma4_1](EremenkosConjecture/Scaffolding.lean) | The Section 7 scaffolding. |
| There is an entire function close to multiplication by five on all source strips and close to zero on the trapping disk. | [exists_scaffolding_function](EremenkosConjecture/Scaffolding.lean) | Initial function for the unbounded construction. |

## Section 7 additions

| Result | Source | Use |
| --- | --- | --- |
| Uniform approximation preserves finitely many bi-Lipschitz iterate extensions on a smaller unbounded set. | [UnboundedIterateStability](EremenkosConjecture/UnboundedIterateStability.lean) | Maintaining injectivity and uniform control through every finite return block. |
| Closed barriers identify connected components, including singleton components. | [ComponentBarriers](EremenkosConjecture/ComponentBarriers.lean) | The final escaping-component conclusion. |
| Compact connected-piece exhaustions imply absence of bounded complementary components under explicit covering hypotheses. | [UnboundedFullness](EremenkosConjecture/UnboundedFullness.lean) | Unbounded approximation-set geometry. |
| The log-sinh map has quantitative extensions on closed insets, uniform compression of finite positive intervals, and a shifted endpoint tending left. | Sibling ComplexApproximation: HalfStripNormalisation and HalfStripExtension | Explicit conformal map in place of Schwarz reflection for the ray construction. |
| Plane homeomorphisms transport Arakelian sets; an inner strip set can be combined with a separated horizontal background. | Sibling ComplexApproximation: ArakelianHomeomorphism and StripArakelian | The actual three-piece approximation set at every successor stage. |

For Theorem 1.2, `ContinuumConstructionData.conclusions` proves the final
connected-component argument for an arbitrary connected set once the uniform
escape, return, and barrier construction data are supplied. This separates
the reusable dynamical implication from the analytic existence construction,
now supplied by ContinuumCounterexample to prove Theorem 1.2.

## Affine normalization and complementary components

| Result | Source | Scope |
| --- | --- | --- |
| Affine conjugacy preserves transcendental entire functions and transports exact connected escaping components. | [ContinuumNormalization](EremenkosConjecture/ContinuumNormalization.lean) | Both directions of transport, including return to the original prescribed set. |
| A compact nonempty set can be placed in any disk with a selected rightmost point at its centre. | [ContinuumNormalization](EremenkosConjecture/ContinuumNormalization.lean) | Positive real scaling and translation; fullness and connectedness retained for continua. |
| A bounded hole of a compact component cannot be filled by the ambient set or meet an unbounded connected subset of it. | [CompactComponentHoles](EremenkosConjecture/CompactComponentHoles.lean) | Plane topology independent of complex dynamics; the dynamical alternatives in Proposition 7.6 remain open. |
| The general-continuum construction data give uniform escape, Fatou interior, Julia boundary, and the component equality in the union with the Julia and bungee sets. | [ContinuumBoundary](EremenkosConjecture/ContinuumBoundary.lean) | Conditional lemma; the required data are now constructed in ContinuumCounterexample. |

`uniformControlOn_of_strip_asymptotic` in
[StripInsetControl](EremenkosConjecture/StripInsetControl.lean) links the
FunctionTheory strip estimates to the uniform-control hypothesis of
finite-iterate approximation, using explicit closed inset margins.

## Jordan-boundary compatibility and geometric strip control

| Result | Source | Scope |
| --- | --- | --- |
| A Schoenflies simple closed path gives a set homeomorphic to the circle. | [JordanBoundaryCompatibility](EremenkosConjecture/JordanBoundaryCompatibility.lean) | Connects the two unchanged public Jordan-curve definitions and applies to the nested compact neighbourhoods. |
| A normalized conformal strip map has uniform control on suitable closed insets. | [DecoratedStripControl](EremenkosConjecture/DecoratedStripControl.lean) | Constructs the map from the explicit simply connected, straight-tail and exponential-Jordan-boundary geometry; supplies derivative bounds and the finite-iterate control interface. |

The decorated domains for arbitrary full continua are constructed in the
completed [Theorem 1.2 proof](docs/THEOREM12_PLAN.md).

## Jordan interiors and the attached-ray geometry

| Result | Source | Scope |
| --- | --- | --- |
| A bounded connected plane domain is the inside of its Jordan boundary. | [JordanDomains](EremenkosConjecture/JordanDomains.lean) | Also identifies interiors of regular compact Jordan neighbourhoods. |
| A Jordan inside is homeomorphic to an open square and is simply connected. | [JordanSimplyConnected](EremenkosConjecture/JordanSimplyConnected.lean) | Uses the attributed complete Schoenflies square-extension theorem. Applies to `JordanCompactNeighbourhood` interiors. |
| Attaching a horizontal ray at a rightmost point of a full compactum creates no bounded complementary components. | [ContinuumRayGeometry](EremenkosConjecture/ContinuumRayGeometry.lean) | Vertical escape on the right and polynomial separation rule out a bounded hole. |
| The compactum with its attached ray is Arakelian; large disk truncations are full continua when the compactum is connected. | [ContinuumRayArakelian](EremenkosConjecture/ContinuumRayArakelian.lean) | The bounded-holes condition is proved, not assumed. |

These are construction foundations for Theorem 1.2. They do not assert the
decorated domains, the uniform estimate over X, or existence of the final function.

## Simple connectivity and strip-domain geometry

- [PlaneSimpleConnectivity](EremenkosConjecture/PlaneSimpleConnectivity.lean):
  an open connected plane domain with no bounded complementary components
  is simply connected. Compact continua in it admit relatively compact simply
  connected Jordan neighbourhoods. The connected-complement corollary is included.
- [JordanStripGeometry](EremenkosConjecture/JordanStripGeometry.lean): a connected
  domain in a horizontal strip, bounded to the left, is simply connected when
  its exponential image has Jordan boundary. With a full straight right tail,
  the normalized conformal strip map and both end estimates follow.

These classical consequences use the attributed Schoenflies proof. They currently
live in this application because its Jordan-neighbourhood construction and
Schoenflies dependency are here; they are candidates for later library extraction.

## Carathéodory homeomorphism theorem

[JordanBoundaryApproach](EremenkosConjecture/JordanBoundaryApproach.lean)
proves preconnected approach regions at every point of a bounded Jordan
domain's closure. It uses the public Schoenflies closed-interior chart and
FunctionTheory's relative-chart transfer lemma.

[JordanCaratheodory](EremenkosConjecture/JordanCaratheodory.lean) then proves
injectivity of the continuous conformal extension and constructs the actual
homeomorphism `closedBall (0 : ℂ) 1 ≃ₜ closure Ω`, agreeing with the prescribed
conformal disk map on the open disk. The analytic continuity and conditional
boundary-injectivity theorems are reused from Tau Ceti. No global extension
of the conformal map is part of this statement.

## Auxiliary filled-domain geometry

| Result | Source |
| --- | --- |
| Filling a compact decoration and two half-strips retains a narrow attachment gate and the separating semicircles | [FilledAttachmentGeometry](EremenkosConjecture/FilledAttachmentGeometry.lean) |
| Every component of the interior of a filled closed set is simply connected | [FilledDomainComponents](EremenkosConjecture/FilledDomainComponents.lean) |

The current primary construction instead follows the author's exterior-map
suggestion; these fully checked auxiliary results remain available.

## Exterior maps for a continuum with an attached segment

| Result | Source |
| --- | --- |
| A closed set between a full compact set and its attached ray has no bounded complementary components | [AttachedSegmentGeometry](EremenkosConjecture/AttachedSegmentGeometry.lean) |
| A short attached segment preserves the full-continuum property and gives a local slit tip | [AttachedSegmentGeometry](EremenkosConjecture/AttachedSegmentGeometry.lean) |
| Inverting about an interior point of the segment yields a simply connected domain containing the image of infinity | [InvertedAttachedSegment](EremenkosConjecture/InvertedAttachedSegment.lean) |
| The normalized exterior Riemann map exists and has a unique boundary limit at the free endpoint | [ExteriorSlitTip](EremenkosConjecture/ExteriorSlitTip.lean) |


The exterior Riemann map of a full continuum with an attached segment now has
corresponding forward and inverse boundary limits at the free tip. See
[ExteriorSlitTipInverse](EremenkosConjecture/ExteriorSlitTipInverse.lean).
The two public Jordan-curve definitions are proved equivalent in
[JordanBoundaryEquivalence](EremenkosConjecture/JordanBoundaryEquivalence.lean).
See the detailed [local boundary argument](docs/LOCAL_CARATHEODORY.md), now
used in the completed Theorem 1.2 construction.


The full compact Jordan enclosure through the free segment tip is proved in
[AttachedSegmentJordanEnclosure](EremenkosConjecture/AttachedSegmentJordanEnclosure.lean),
inside any prescribed open neighbourhood of the attached continuum.
[JordanCompactRecognition](EremenkosConjecture/JordanCompactRecognition.lean)
proves that a compact set with Jordan frontier and nonempty interior is a
full regular closed Jordan region.


The actual filled attachment domains, their strip bounds, full straight tails,
monotonicity and exact shrinking-channel kernel are now checked. The stronger
strip-map theorem supplies the required analytic end estimates without a
global Jordan-frontier assumption. The completed construction is recorded in
[Theorem 1.2 proof map](docs/THEOREM12_PLAN.md). Boundary normalization convergence
is now proved. [ContinuumAttachmentMap](EremenkosConjecture/ContinuumAttachmentMap.lean)
constructs one map with simultaneous compact control and uniform escape of
the whole continuum, together with its exponential end estimates.

[ContinuumUniformTube](EremenkosConjecture/ContinuumUniformTube.lean) combines
compact control with a straight tail to give a uniform neighbourhood of the
continuum and ray. [FilledRayInsets](EremenkosConjecture/FilledRayInsets.lean)
proves closedness, connectedness, absence of bounded complementary components,
and an exactly straight tail after filling. The
[inset existence theorem](EremenkosConjecture/FilledRayInsetExistence.lean)
places a smaller such set strictly inside a preceding filled neighbourhood.
[FilledRayIntersection](EremenkosConjecture/FilledRayIntersection.lean)
proves the exact intersection of decreasing filled neighbourhoods;
[NestedFilledRayNeighbourhoods](EremenkosConjecture/NestedFilledRayNeighbourhoods.lean)
constructs such a sequence. [ClosedStripNeighbourhoods](EremenkosConjecture/ClosedStripNeighbourhoods.lean)
gives the compact-truncation criterion for eventual inclusion in an open
neighbourhood. [FilledRayInterior](EremenkosConjecture/FilledRayInterior.lean)
identifies the ray-containing interior component and its straight tail.
[FilledRayBandArakelian](EremenkosConjecture/FilledRayBandArakelian.lean)
proves the Arakelian property of the actual source band with its inner set.
The transported approximation configuration and induction are proved in
ContinuumReference, ContinuumSuccessor and ContinuumEntireLimit.


[LocalChartMargins](EremenkosConjecture/LocalChartMargins.lean) transfers
uniform source margins to image margins using uniform continuity of the
inverse, and gives finite-iterate control through consecutive local charts.
[LocalArakelianStability](EremenkosConjecture/LocalArakelianStability.lean)
proves that a sufficiently close holomorphic perturbation agrees on an inset
with a bi-Lipschitz change of the reference image coordinates.

## Final continuum-construction auxiliaries

| Result | Source | Role |
| --- | --- | --- |
| Strip maps with exponential end estimates supply conformal iterate charts on closed insets. | [ContinuumStripChart](EremenkosConjecture/ContinuumStripChart.lean) | Links classical map estimates to the approximation interface. |
| Changes of source and image coordinates preserve local iterate charts with exact open sources. | [ContinuumChartCoordinates](EremenkosConjecture/ContinuumChartCoordinates.lean), [LocalChartImageChange](EremenkosConjecture/LocalChartImageChange.lean) | Reusable chart transport. |
| Nested filled ray neighbourhoods have connected open insets, a common straight tail and uniform margins. | [ContinuumRegionGeometry](EremenkosConjecture/ContinuumRegionGeometry.lean) | Supplies the hypotheses of Section 2 stability. |
| Unbounded frontiers have an explicit sequence tending to infinity. | [ContinuumFrontierSequence](EremenkosConjecture/ContinuumFrontierSequence.lean) | Rules out a polynomial limit using bounded frontier values. |
| A single tolerance preserves all finite charts, orbit tubes, target margins and trapping barriers. | [ContinuumApproximationStability](EremenkosConjecture/ContinuumApproximationStability.lean) | Finite combination of the existing Section 2 estimates. |

The completed construction and its file-by-file map are in
[THEOREM12_PLAN.md](docs/THEOREM12_PLAN.md). These auxiliary results are not
claims of new classical mathematics or replacements for the main theorem.
