# Auxiliary classical results

[Main results](MAIN_RESULTS.md) · [Proof map](PROOF_MAP.md) · [Complete module index](docs/MODULE_INDEX.md)

These are reusable criteria and identities proved in this library. The
underlying general topology and analysis are imported from Mathlib. Some
rows package elementary classical arguments for the specific definitions
of normality and escaping sets used here.

| Result and scope | Checked declaration(s) | Role |
| --- | --- | --- |
| Locally uniform convergence implies the subsequence definition of normality. | [isNormalSequenceOn_of_tendstoLocallyUniformly](ComplexDynamics/Normality.lean#L30) | Normality from an explicit limit. |
| The Fatou set is open and the Julia set is closed. | [isOpen_fatouSet](ComplexDynamics/Basic.lean#L64); [isClosed_juliaSet](ComplexDynamics/Basic.lean#L69) | Basic dynamical topology. |
| Uniform escape becomes uniform spherical convergence to infinity, hence a Fatou interior. | [EscapesUniformlyOn.tendstoUniformlyOn_sphericalIterate](ComplexDynamics/UniformEscape.lean#L19); [EscapesUniformlyOn.interior_subset_fatouSet](ComplexDynamics/UniformEscape.lean#L36) | Direct normality argument. |
| An escaping point accumulated by orbits trapped in one compact set is a Julia point (for continuous maps). | [mem_juliaSet_of_escape_of_closure_trappedSet](ComplexDynamics/Trapping.lean#L15) | Direct failure of normality. |
| A closed set with Fatou interior and Julia boundary has precisely its boundary in the Julia set, and its interior components are Fatou components. | [connectedComponentIn_interior_eq_fatou](ComplexDynamics/FatouComponents.lean#L9); [inter_juliaSet_eq_frontier](ComplexDynamics/FatouComponents.lean#L37) | Identify actual components, rather than only open subsets. |
| Holomorphy of finite iterates on their orbit domains; those domains are open; local agreement propagates along finite orbits. | [differentiableOn_iterate_of_mapsTo](ComplexDynamics/Iteration.lean#L10); [isOpen_iterateDomain](ComplexDynamics/Iteration.lean#L49); [eventuallyEq_iterate_of_orbit](ComplexDynamics/Iteration.lean#L72) | Reusable finite-iteration calculus. |
| Uniform escape, trapped boundary accumulation, disjoint forward compacta and explicit ambient charts imply wandering Fatou components. | [wandering_of_uniformEscape_of_trappedBoundary](ComplexDynamics/Wandering.lean#L30) | Main construction criterion. |
| Iteration and transcendental entire status under nonzero linear scaling. | [iterate_scaleConjugate](ComplexDynamics/Scaling.lean#L21); [IsTranscendentalEntire.scaleConjugate](ComplexDynamics/Scaling.lean#L30) | Remove geometric normalisations. |
| Disk/circle maximum-modulus equality, perturbation bounds, and fast escape from a comparison radius sequence. | [maximumModulus_eq_sphere](ComplexDynamics/FastEscape.lean#L39); [maximumModulus_le_of_uniform_error](ComplexDynamics/FastEscape.lean#L57); [mem_fastEscapingSetAtRadius_of_radius_sequence](ComplexDynamics/FastEscape.lean#L86) | Quantitative growth control. |
| Exact scaling of maximum modulus and transport of fast escape at a specified radius. | [maximumModulus_scaleConjugate](ComplexDynamics/FastEscapeScaling.lean#L10); [mapsTo_scale_fastEscapingSetAtRadius](ComplexDynamics/FastEscapeScaling.lean#L57) | Scale the quantitative construction. |
| An entire function with an escaping orbit and bounded values along a sequence tending to infinity is transcendental. | [isTranscendentalEntire_of_escape_and_bounded_values](ComplexDynamics/Transcendence.lean#L14) | Exclude constants and nonconstant polynomials. |
| The exponential is transcendental entire; polynomials admit arbitrarily small transcendental entire perturbations on a compact set. | [isTranscendentalEntire_exp](ComplexDynamics/TranscendentalApproximation.lean#L11); [exists_transcendentalEntire_near_polynomial](ComplexDynamics/TranscendentalApproximation.lean#L36) | Handle finite or eventual-empty data. |
| A uniformly bounded holomorphic sequence on a disk is normal on the closed half-radius disk. | [isNormalSequenceOn_spherical_of_bounded_on_ball](ComplexDynamics/BoundedNormality.lean#L49) | Schwarz estimate plus Arzelà–Ascoli, using existing Mathlib foundations. |
| Every point eventually entering a bounded forward-invariant open set of an entire map is a Fatou point. | [mem_fatouSet_of_iterate_mem_bounded_invariant](ComplexDynamics/BoundedNormality.lean#L109) | Trapping regions. |
| Path components coincide when paths cannot leave the prescribed subset. | [pathComponentIn_eq_of_no_exit](ComplexDynamics/PathComponents.lean#L10); [pathComponentIn_eq_inter_of_no_exit](ComplexDynamics/PathComponents.lean#L19) | Barrier arguments. |
| A continuous curve from a bounded path component cannot tend to infinity while remaining in the ambient set. | [not_curve_to_infinity_of_bounded_pathComponent](ComplexDynamics/CurvesToInfinity.lean#L8) | Strong Eremenko consequence. |

The spherical and Fatou-set definitions adapt the attributed `exp-chaotic`
development. Schwarz estimates, Arzelà–Ascoli, one-point compactification and
the maximum-modulus principle are existing Mathlib results. Full Montel,
general radius independence for fast escape, and a general conjugacy theory
are not included; see [STATUS.md](STATUS.md).
