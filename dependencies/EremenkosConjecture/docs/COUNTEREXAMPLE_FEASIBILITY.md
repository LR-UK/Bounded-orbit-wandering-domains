# Feasibility of the counterexample to Eremenko's conjecture

**Historical assessment. Update 18 September 2026:** the original
singleton escaping-component counterexample, the full Theorem 7.1 with endpoint
zero, and Theorem 1.2 are now proved. The earlier gaps below record the state at
the time of the assessment. See [the current map](SECTION7_PROGRESS.md).

Assessment after completing Section 3, 16 September 2026.

**Update, evening of 16 September:** the neighbourhood-holomorphic Arakelian
theorem has now been proved in the sibling ComplexApproximation project.
Its Cauchy–Pompeiu formula, right inverse, uniform estimate, smooth gluing,
filled exhaustion, and expanding-domain limit are all checked; the project
passes its 56-result standard-axiom audit. The application-specific work in
Sections 4 and 7 remains in progress. No counterexample headline is yet claimed.

The next construction is feasible in principle, but still needs substantial
new Lean analysis. The most economical first target is Theorem 7.1: a
transcendental entire function for which a singleton is a **connected
component** of the escaping set. The completed Section 3 theorem gives a
singleton **path component**, which does not settle the original conjecture.
No result from Sections 4 or 7 is claimed as formalised in this delivery.

## The suggested approximation route is supported by a published proof

Rosay and Rudin explicitly separate the neighbourhood-holomorphic case of
Arakelyan approximation from the more general continuous-on-the-set case.
Their former case uses Runge approximation on successive compact sets,
cutoffs, and a Cauchy-transform correction of the failure of holomorphy.
Summable errors give an entire limit. Thus Mergelyan's theorem is unnecessary
for this restricted target. The source is Jean-Pierre Rosay and Walter Rudin,
*Arakelian's Approximation Theorem*, American Mathematical Monthly 96(5)
(1989), 432–434, especially pp. 432–433:
[publisher record](https://doi.org/10.1080/00029890.1989.11972213),
[indexed paper](https://citeseerx.ist.psu.edu/document?doi=13566671a8d7c762a1b29383d071140fc48ae4f0&repid=rep1&type=pdf).

A suitable local-domain target is: let E be closed, with no bounded
complement components, and suppose the union of the bounded components of
the complement of E ∪ closedBall(0,R) is bounded for every R. Given an open
U containing E and `g : U → ℂ` holomorphic on U, every positive constant
error admits an entire approximant on E. This uses the paper's bounded-hole
formulation of an Arakelyan set. Its equivalence with the sphere-complement
condition should be a separate theorem, or the concrete approximation sets
can be proved to satisfy the bounded-hole condition directly.

## What is already available, and what is missing

| Ingredient | Current position |
| --- | --- |
| Runge on full compact sets, with actual local domains | Proved in `Runge.LocalDomain` |
| Smooth cutoffs and compactly supported extensions | Proved in `Runge.SmoothCutoff` |
| Real derivatives, Cauchy–Riemann defect, rectangular Green identity | Available in `Runge.CauchyGreen` and pinned Mathlib |
| Integral representation when the defect is separated from the evaluation set | Used in `Runge.RationalApproximation` |
| Cauchy transform at points in the support of its density | Proved in `ComplexApproximation.CauchyPompeiu` |
| Uniform estimates for that singular integral | Proved in `ComplexApproximation.CauchyTransformBounds` |
| Compact univalence and finite-iterate stability | Proved in `EremenkosConjecture` |
| Stability with uniform margins on unbounded sets | Still needed |
| Summable corrections and locally uniform entire limits | Both entire-stage and expanding-domain versions are proved |
| Neighbourhood-holomorphic Arakelian approximation | Proved in `ComplexApproximation.ArakelianLocalDomain` |
| Fatou/Julia criteria from escape and bounded trapping | Proved in `ComplexDynamics` |
| Nested compact topology, Jordan neighbourhoods, barriers | Proved for Section 3; proper unbounded strip geometry needs additions |

The original Runge proof uses support separation to remove the kernel
singularity. The new Cauchy–Pompeiu development handles that singularity and
supplies the smooth compact-support inhomogeneous Cauchy–Riemann theorem
needed here. Searching the pinned Mathlib did not identify a
ready-made Arakelyan, Cauchy–Pompeiu, or Koebe-quarter theorem. This is a
statement about the inspected version and searches, not all Lean developments.

Relevant existing Mathlib foundations include
`Analysis/Complex/CauchyIntegral.lean`,
`MeasureTheory/Integral/DivergenceTheorem.lean`,
`Analysis/Calculus/BumpFunction/`, and
`Analysis/Complex/LocallyUniformLimit.lean`. The dependency pin is
`5ed2965256430c3649e86755f9576b54eca72435` with Lean 4.34.0.

## Analytic implementation (now completed)

The following plan has now been implemented in ComplexApproximation. The
uniform estimate uses a unit-disk split rather than the sharper radius estimate
displayed below; the required support-dependent bound is fully proved.

First develop the compactly supported smooth Cauchy transform

    Tq(z) = (1/π) ∫ q(w)/(z-w) dA(w),       ∂̄Tq = q.

The measure is planar Lebesgue measure and
`∂̄ = (∂x + i∂y)/2`. Our existing defect has normalization `2i∂̄`, so the
conversion factors must be proved explicitly.

For a density supported in the disk of radius R > 0, the elementary estimate

    sup_z ∫_{|w|≤R} 1/|z-w| dA(w) ≤ 6πR

suffices. If |z| ≤ 2R, enlarge to the disk of radius 3R around z and use
polar integration. If |z| > 2R, bound the denominator below by R. Thus
`‖Tq‖∞ ≤ 6R ‖q‖∞`. An optimal constant is unnecessary. The singularity is
locally integrable; it cannot be justified by continuity on the whole disk.

One can aim to keep the correction density smooth rather than introduce a
discontinuous indicator of an open neighbourhood. At a gluing step let φ be
a smooth radial cutoff and h the old holomorphic function. Approximate h by
a polynomial P on the relevant full compact set, with a strict error margin.
Choose a second smooth cutoff χ, equal to one near
`E_old ∩ support(∂̄φ)` and supported where h is defined and h−P is small.
Extend `q = χ(h−P)∂̄φ` by zero. This is a smooth compactly supported density.
On a suitably reduced neighbourhood of E_old it has the required value
`(h−P)∂̄φ`. Therefore `φP + (1−φ)h + Tq` is holomorphic there and on the
new inner disk. This reduces the analytic API initially needed to smooth
densities. The cutoff bounds, overlap identities, and shrinking of the
neighbourhood are now proved in `ArakelianStep.lean`.

The stages in this approximation argument are holomorphic on expanding open
sets, not initially entire. The new `HolomorphicLimit.lean` provides the local
variant: every fixed disk eventually lies in all domains, the corrections
there are summable, and the limit is holomorphic on that disk. Mathlib's
local uniform limit results provide the underlying analytic theorem.

## Applying the restricted theorem in Sections 4 and 7

In Section 4 the initial targets are affine or constant on separated closed
pieces. They extend holomorphically to neighbourhoods. The topological work
is to check the approximation sets: countably many strips, plus the finite
pieces used at each stage, with the strips tending uniformly to infinity.
Compact Runge alone cannot give uniform error on an entire unbounded strip.

Lemma 4.1 concerns perturbations of `z ↦ 5z`. For this affine reference it is
reasonable to prove the required injectivity, inverse branches, and derivative
bounds directly from Cauchy/Schwarz estimates and a contraction argument on
inset disks. This may avoid proving the full Koebe-quarter theorem first.
The later unbounded iterate construction still needs uniform image margins
and inverse control; the compact stability lemmas do not supply these by
compactness.

In equation (7.1), the conformal-map piece deserves explicit attention. The
paper initially states a continuous extension to the closed half-strip.
Continuity there does not itself establish the stronger neighbourhood
holomorphy required by the restricted approximation theorem. For straight
half-strips this can be settled by explicit formulas or reflection across
the straight sides; for decorated half-strips one can restrict to a smaller
closed region strictly inside the conformal domain, with the required
quantitative margins proved. This is a real interface obligation, not an
assumption to omit. The closed-set notation and shifts were checked against
the rendered p. 31 of the supplied paper.

### An explicit map for the singleton case

For positive a and b, put

    H_a = { z : Re z > 0 and |Im z| < a },
    φ(z) = (2b/π) Log(sinh(πz/(2a))).

With the principal logarithm this maps H_a conformally onto
`{w : |Im w| < b}`. Indeed, the scaled sinh maps H_a onto the right
half-plane, and Log maps that half-plane onto the strip of half-height π/2.
Real and imaginary translations supply the normalizations in the paper.
Its derivative is

    φ′(z) = (b/a) coth(πz/(2a)).

For a shifted closed half-strip whose real part stays positive, the formula
extends across its horizontal sides, avoids zeros and logarithm branch
cuts in a neighbourhood, and gives positive upper and lower derivative
bounds. On the positive real axis φ tends to −∞ at the finite endpoint and
to +∞ at infinity. Reducing b controls its variation on any prescribed
compact subinterval of that axis.

These elementary calculations give a specific alternative to importing a
general Riemann mapping, hyperbolic metric, and boundary reflection package
for Theorem 7.1. They have been checked mathematically for this assessment;
the mapping, branch, surjectivity, and estimates are **not yet Lean proofs**.
Their formalisation would use Mathlib's exponential, logarithm, and hyperbolic
function theory.

## Recommended order of further formalisation

1. Prove the smooth Cauchy-transform right-inverse and uniform bound.
2. Prove neighbourhood-holomorphic Arakelyan approximation, initially using
   an explicit bounded-hole exhaustion. Verify that the required unions of
   strips satisfy its hypotheses.
3. Prove Section 4's affine-strip perturbation and inverse-branch estimates.
4. Formalise the explicit half-strip maps and the unbounded stability needed
   to preserve the induction in Theorem 7.1.
5. Carry out the entire-function recursion, including all intermediate
   iterates. Define the bungee set as points whose orbit is unbounded but
   does not escape, and prove the ray's itinerary and Julia membership.
6. Use the surrounding curves trapped in a bounded invariant domain to
   establish the **connected-component** conclusion. The acceptance target
   is `connectedComponentIn (escapingSet f) 0 = {0}`, for a proved
   transcendental entire f, not a path-component statement.

The full Theorem 1.2 for arbitrary full continua adds decorated half-strips,
normalized conformal maps, and the kernel-convergence control used in (7.3).
Our continuum Jordan-neighbourhood theorem supplies part of the topology.
Riemann mapping and Carathéodory kernel convergence remain substantial
analytic dependencies. The RMT sources noted in `TOPOLOGY_SOURCES.md` were
reviewed as candidates, but no ready-to-use unconditional replacement was
built or audited for this project.

Section 5's oscillating compacta would reuse the unbounded approximation and
strip machinery, with compact prescribed sets. Section 6's further wandering
Lakes of Wada applications depend on those itinerary constructions. The
harmonic-measure results in Section 8 require a separate assessment of
potential theory and boundary measure. Their proofs are outside the completed
Section 3 formalisation and are not implied by the current libraries.
