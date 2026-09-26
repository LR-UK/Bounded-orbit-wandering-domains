# Author's proof route and local formalisation handoff

Recorded 25 September 2026, following the statement review of
`no-bounded-WD-2.tex`. Read this together with `PAPER_STATEMENT_ALIGNMENT.md`.
The instructions below supersede any older suggestion that the meromorphic
case needs a separate main proof. The mathematical targets retain their
precise introductory hypotheses.

## Author's directions

1. **Theorem 1.2, meromorphic case:** follows directly from the Riemann-surface
   statement in Theorem 1.3. Treat it as a corollary and prove the formal
   specialization/normality interface, not a second area argument.
2. **Theorem 1.3, arbitrary surfaces:** reuse the existing proof, replacing
   its subharmonic argument by the newly formulated **Lemma 2.6**. The lemma
   is the finite-logarithmic-singularity Riesz-mass estimate in the draft's
   preliminaries.
3. **Theorem 1.5:** use the compact area-gain estimate below, or a genuinely
   stronger version if already proved. Then follow essentially the same
   dynamical proof. Check exact quantifiers before treating an existing
   geometric estimate as sufficient.
4. The author wants subsequent proof development on GPT-5 if suitable and
   available, to conserve usage. This pass records and verifies the statement
   specification; it does not start a new long proof search.

## Required compact area-gain estimate

Let X be a Riemann surface and K,L ⊆ X disjoint compact sets. For a fixed
q ∈ ℕ there should exist a finite C = C(X,K,L,q) ≥ 0 such that, for **every**
open hyperbolic U ⊆ X and **every** finite E ⊆ X with #E ≤ q, putting

    V = U ∖ (K ∪ E),

every measurable A ⊆ L ∩ V with Area_U(A) < ∞ satisfies

    Area_V(A) ≤ Area_U(A) + C.

The lower inequality follows from monotonicity on V. Restricting to L ∩ V
makes both areas unambiguous; finite removed points can alternatively be
discarded as null sets. If the initial q is a finite nonnegative real bound,
use an integer cardinality bound. The constant may depend on the fixed
surface/compact sets/q, but **not** on U, E, its point locations, or A.

The author's sentence said “mass gained ... at most q,” followed by the
explicit parenthetical bound “at most C.” The formulation above follows the
parenthetical: q bounds the number of exceptional points; C bounds area gain.

Prefer a nonnegative gain measure or the displayed additive inequality to
subtraction of extended-real areas. The finite-area hypothesis then gives
finiteness of the new area without any ∞ − ∞ expression. It must not be
replaced by the stronger assumption that L itself has finite U-area.

## What is already formalised, and what is not

`Surfaces/CompactFiniteRemoval.lean` proves
`DiscCover.compact_finite_remote_removal_gain`. Its order of quantifiers is

    given p : DiscCover X, E, K, L, obtain B, then for every U ...

It is uniform in the old open domain U, allows a fixed closed K disjoint
from compact L, and includes disconnected U componentwise. However:

- **E is fixed before B is chosen.** This is not the desired uniformity over
  all E with #E ≤ q. `compact_point_removal_gain` likewise fixes a first.
- **The ambient X has a supplied disc cover.** This does not yet cover an
  arbitrary nonhyperbolic ambient surface merely because U is hyperbolic.

Thus the checked theorem is stronger concerning K being closed, but weaker
in two essential directions. No already-proved replacement with the requested
uniform cardinality quantifier was found in the recovered surface sources.
The full previous cloud conversations are not available beyond recovered
notes and files. If the dynamical proof can choose one exceptional E once for
all approximations, the fixed-E estimate may suffice for that application;
establish that fact explicitly rather than swapping quantifiers.

**Author's follow-up:** uniform puncture control is required. A possible
fixed-E shortcut in a particular application does not discharge the requested
uniform theorem. The author points out that a sharp 2π cost per puncture would
immediately supply uniformity; check and reuse that result wherever its full
hypotheses apply.

The checked `chart_point_removal_gain` does have the explicit bound 2π,
independent of the puncture. It requires the old domain to be contained in
one conformal chart, with the recorded omitted-coordinate values, and is
stated in the disc-cover framework. In contrast, the current arbitrary-domain
`compact_point_removal_gain` returns `(B₀ + 2π) + B₁`, with localization
constants constructed after choosing the puncture a. Its finite-set corollary
sums these point-dependent bounds. Consequently that corollary is not yet
the uniform-q result merely because 2π occurs in its proof.

Useful checked ingredients:

| File | Existing result / purpose |
| --- | --- |
| `Surfaces/DomainRemoteArea.lean` | `remote_compact_domainAreaGain`, `compact_localization_domainAreaGain`: remote removal and localization uniform in U, with a disc-covered ambient surface. |
| `Surfaces/ChartPointRemoval.lean` | Sharp chart-local puncture cost 2π. |
| `Surfaces/CompactPointRemoval.lean` | Fixed-point finite compact budget, uniform in U; its construction currently depends on the point. |
| `Surfaces/CompactFiniteRemoval.lean` | Telescoping for a fixed finite E and combination with a remote obstacle. |
| `Surfaces/DomainArea.lean` | `domainArea_le_add_gain`: converts a gain bound to the additive area inequality; coordinate formula. |
| `Surfaces/SeparatingCutoff.lean`, `ChartLaplacianSupport.lean` | Smooth separating cutoffs and control of the chart Laplacian's support. |
| `Surfaces/LogDensityRatio.lean` | Nonnegative logarithmic ratio and its Laplacian identity. |
| `Surfaces/DomainFiniteCutoff.lean` | Chart cutoff integration with finite exceptions. Inspect hypotheses before reuse. |
| `Surfaces/CoveringMetricPullback.lean` | `density_covering_pullback`, checked separately and included in the expanded 97-declaration local audit. |
| `Surfaces/FiniteModelArea.lean`, `DomainAreaBlowup.lean` | Finite compact model area and nullity from uniform finite-model bounds. The latter still needs those bounds from the dynamics. |

## Suggested translation of Lemma 2.6

### Author's additional metric-ratio argument

The author specifies the following route for the area-gain lemma:

1. For V = U ∖ (K ∪ E), take R = ρ_V/ρ_U on V and u = log R.
   Monotonicity gives R ≥ 1 and u ≥ 0; strict inequality holds on components
   where the removal changes the domain. Unchanged components contribute zero.
2. At boundary points of U in L, away from the exceptional punctures, the
   quotient tends to 1, so u tends to 0. This is the boundary behaviour to use
   when extending the argument to a fixed ambient neighbourhood of L.
3. Near the finitely many punctures, u has the logarithmic upper growth
   required in Lemma 2.6.
4. u is subharmonic, and in a conformal coordinate on V,

       Δu dA = (ρ_V² − ρ_U²) dA.

   Thus its Riesz measure there is precisely the difference of area elements.
   The author wrote “subhyperbolic” in the follow-up; this note uses
   “subharmonic,” the property expressed by the nonnegative Laplacian.
5. Lemma 2.2 supplies the uniform metric comparison, and Lemma 2.6 then bounds
   the Riesz mass with the explicit puncture contribution 2π #E ≤ 2πq.
   This gives the required uniform compact area-gain estimate.

This is the author's intended proof route, not a newly completed Lean proof.
The formal interfaces still to make explicit are the boundary limit/extension,
logarithmic growth, and **uniform** bound from Lemma 2.2. State the latter with
its constant chosen before U and before all E with #E ≤ q. The current
`chartLogRatio_nonneg`, `chartLogRatio_laplacian`, and
`chartLogRatio_laplacian_nonneg` already supply the smooth local identities
in their cover-based setting; reuse them.

An implementation can zero-extend u across the relevant boundary of U once
the boundary-limit and subharmonic-extension lemmas are proved. Equality of
the Riesz measure with area gain is needed on V; any extra positive boundary
mass in an extension is harmless for an upper bound. Do not assume the
extension or its measure identity without proving it. In applying Lemma 2.2,
keep the collar/working compact sets and all metric-comparison constants
uniform as the punctures move; a bound valid only after fixing E is not enough.
Also discharge the ambient-surface issue: the target assumes hyperbolicity of
U, not hyperbolicity of all X.

### Proposed formal interfaces

The draft's lemma has L ⊆ interior(K), finite Q ⊆ interior(K), and nonnegative
subharmonic u on interior(K) ∖ Q. It assumes u ≤ m off L ∪ Q and, in a
coordinate ζ centred at each a ∈ Q, u ≤ log(1/|ζ|) + c near a. Its conclusion is

    μ_u(L ∖ Q) ≤ C(L,K) m + 2π #Q.

Here μ_u uses the unnormalised convention corresponding to Δu dA in the
smooth case. Preserve this convention and curvature −1; no 1/(2π) rescaling.

The following are implementation suggestions, not already-proved lemmas:

1. First isolate the logarithmic-singularity budget in one chart. The growth
   condition controls the possible negative Dirac contribution by 2π at each
   puncture. One possible route is to add log|ζ|, prove a removable
   subharmonic extension, and recover the punctured Riesz measure with the
   atomic correction. A boundary-flux approximation is another route if the
   existing distribution machinery is inconvenient.
2. Use a smooth cutoff 0 ≤ χ ≤ 1 supported in interior(K), equal to 1 on a
   neighbourhood of L. Its Laplacian is supported away from L, where u ≤ m.
   This is the appropriate cutoff for the unfinished proof: the draft's
   current text asks for support in interior(K) and value 1 on K, which is
   generally incompatible; it also switches the cutoff's symbol.
3. Assemble the chart estimates using a finite chart cover and prove the
   conformal invariance needed for the Riesz measure. Keep C(L,K) independent
   of Q, of the chart constants c at the punctures, and of u. Partition and
   cutoff derivative terms must be included, not suppressed.
4. Instantiate the result with logarithms of hyperbolic density ratios (or
   the required positive part in the pullback comparison). The curvature
   identity converts the Laplacian into area gain/deficit. This should replace
   the old planar analytic step while retaining the dynamical argument.

For the compact gain lemma, one possible stronger route is a global
per-puncture cost ≤ 2π and telescoping, yielding C_remote + 2πq. The sharp
global surface result is still recorded as unfinished. A potentially cheaper
route is a uniform **compact** point budget: choose a fixed finite family of
charts around a neighbourhood of L, control punctures there uniformly in
their positions, and handle punctures outside that neighbourhood by a remote
localization estimate. This would yield C_remote + q B(X,L), which is enough.
Neither route is claimed complete; in particular the arbitrary-ambient-X
step remains to be supplied. A collar bound for a logarithmic ratio must not
silently depend on a moving puncture approaching the cutoff's Laplacian support.

## Assembly and efficient continuation

Follow the author's dependency order: Lemma 2.6 → surface local deficit and
area transport → Theorem 1.3 → meromorphic corollary; compact gain estimate →
the existing wandering-domain argument → Theorem 1.5. Keep the possible
fixed-E shortcut separate from the required general uniform-q estimate.
Use the author's Lemma 2.2/2.6 metric-ratio route above as the main plan for
that estimate; the alternative localization/global-puncture suggestions are
implementation options, not replacements for the requested uniformity.

For the meromorphic specialization take X = Ĉ and O = ℂ, with poles mapped
to ∞ holomorphically. The bridge must relate ordinary meromorphic Fatou
components to the local normality components and extract the locally uniform
subsequence from normality and the wandering-component argument. No new main
area estimate is needed. The current finite-representative target is simply
the independent statement interface for this corollary.

Do not redo the proved density convergence/divergence or the entire results.
Do not add simple connectivity or injectivity to statements that lack them.
Prove the small interfaces first, check one meaningful module at a time, and
keep a short log of completed declarations and actual obstructions. Stop a
repeatedly failing mathematical approach to reassess its lemma rather than
running broad builds or weakening the target.

The pinned Lean version remains `leanprover/lean4:v4.35.0-rc2`. The local build
caches are ready. `../Run-Local.ps1 -Action Build` checks the recovered research
targets; `-Action Audit` checks their 97 declarations. The new independent
specification is checked separately by `../Run-Local.ps1 -Action Statements`
(the pinned launcher for `lake build PaperChallenge`). Its
statement-alignment evidence is in `../local-verification/paper-*.log` and
`paper-alignment-verification.json`.

The model used for this pass has not been changed. My judgment is that GPT-5
is a reasonable model to try for the now-scoped Lean implementation with
compiler feedback; the remaining analytic design and uniformity questions
may still need stronger reasoning or author input. Start with a focused
lemma and retain the lighter model if it makes reliable progress. Availability
and usage accounting must be checked in the app; no saving is guaranteed.

## Local continuation checkpoint

The moving-puncture/cardinality gap has now been closed for a
**disc-covered ambient surface** in
`Surfaces/UniformFiniteRemoval.lean`. The new checked declarations are:

- `domainAreaGain_mono_right_on`;
- `compact_point_removal_gain_on_core`;
- `uniform_compact_point_removal_gain`;
- `uniform_compact_finite_removal_gain`;
- `uniform_compact_finite_remote_removal_gain`;
- `uniform_compact_finite_remote_area`.

Cardinality-at-most variants have now also been proved and checked:

- `uniform_compact_finite_removal_gain_le`;
- `uniform_compact_finite_remote_removal_gain_le`;
- `uniform_compact_finite_remote_area_le`;
- `uniform_compact_finite_remote_removal_gain_le_all_covers`.

These use `E.card ≤ q`, matching the manuscript rather than the earlier
exact-cardinality interface.

The proof uses finitely many nested chart cores near the measured compact
set, the sharp chart-local 2π estimate, and a fixed remote deletion bound.
It gives a constant independent of the old open domain, the exceptional
points, and their locations, depending on the cardinality bound only through
iteration of one uniform point budget. The focused module build passes.

This does **not** by itself remove the ambient hypothesis
`p : DiscCover X`. The manuscript formulation starts with an arbitrary
Riemann surface X and only assumes that the varying U is hyperbolic. A
remaining bridge must show that the constant is independent of the separately
chosen disc cover of each varying U, or formalise the Lemma 2.2/Lemma 2.6
argument directly on U. Cover existence itself is not missing:
`nonempty_discCover_of_isHyperbolic` converts the uniformisation predicate
to a concrete cover, and `DiscCover.nonempty_subdomain` proves that every
connected open subdomain of a disc-covered surface is disc-covered. Thus the
new result already gives the requested estimate whenever X has one fixed disc
cover. Do not cite it as the full arbitrary-ambient lemma until uniformity
over hyperbolic U inside a possibly nonhyperbolic X is proved.

The author's finite-anchor reduction should be used for the remaining case:
choose a fixed finite set `P`, away from the measured compact set, for which
`X \ P` is hyperbolic; compare `U` first with `U \ P`, and then work in the
fixed hyperbolic ambient `X \ P`. The second comparison is supplied by the
theorems above. The precise outstanding input is an ambient-independent
finite-puncture estimate for the first comparison (the sharp expected bound
is `2π * P.card`) together with the finite-hyperbolisation statement for an
arbitrary connected Riemann surface. This is a reduction of the remaining
analytic issue, not an assumption to insert into the final theorem.

The author additionally confirmed that these fixed anchors may be inserted
when the original surface is nonhyperbolic: their area contribution on the
remote compact set should be charged once by a constant. Thus the general
proof needs finite hyperbolisation and the uniform finite-puncture estimate;
it does not require a disc cover of the unpunctured nonhyperbolic surface.

For Theorem 1.5 the right analytic core is now recorded as
`WanderingOrbitClusterMeetsDerivedClaim`: it asks for one subsequential orbit
limit in the derived singular set. Requiring every finite subsequential limit
to lie there is stronger than the paper and stronger than the existing area
argument, whose natural conclusion is that the cluster set meets the derived
singular set. The checked implication
`wanderingDerivedSingularLimitClaim_of_clusterMeetsDerived` converts this
exact core directly into the paper's escape-or-derived-limit conclusion.

The open-mapping bridge has also been completed.  The checked theorem
`SurfaceDynamics.isOpenMap_of_mdifferentiable_of_locally_nonconstant` lifts
the complex open-mapping theorem through analytic-surface charts.  Together
with the meromorphic identity principle, it proves
`MeromorphicDynamics.surfaceModel_isOpenHolomorphic`: every transcendental
meromorphic map, read honestly as a sphere-valued local map with finite-chart
source, satisfies the exact open-holomorphic hypothesis of the surface
statements.  This includes local nonconstancy and openness at poles.
The same model now has the checked equivalence
`poleAvoiding_iff_mem_surfaceModel_trapped`, and its compactified partial
iterates agree with the usual meromorphic iterates on this set.  The remaining
meromorphic specialization work has been reduced further: the checked theorem
`surfaceModel_isNormalOn_of_normalSequence` transports every normal family on
a pole-avoiding plane set to local-map normality on its finite-chart image.
The connected-component comparison is now complete.  The checked reverse
normality theorem, set equality, component equality, and wandering-component
transport are:

- `normalSequence_of_surfaceModel_isNormalOn`;
- `mem_fatouSet_iff_coe_mem_surfaceModel_omega`;
- `surfaceModel_omega_eq_finiteImage_fatouSet`;
- `finiteImage_connectedComponentIn_fatouSet`;
- `surfaceModel_isWanderingComponent_of_fatouComponents`.

Thus the remaining meromorphic work is the locally-uniform promotion after
applying the still-outstanding surface escape theorem; no further comparison
of Fatou sets or components is needed.

That promotion is now complete in `MeromorphicEscape.lean`.  The checked
declarations are:

- `wandering_orbit_unbounded_of_surface_theorem`;
- `wandering_orbit_locallyUniform_infty_of_unbounded`;
- `wanderingLocallyUniformInfinityClaim_of_surface_theorem`.

The first turns a hypothetically bounded ordinary orbit into a compact subset
of the finite sphere chart and contradicts the surface theorem.  The second
uses local meromorphic normality on the Fatou-component subtype, the generic
Arzela--Ascoli extraction, and disjoint spherical images to promote a marked
escape subsequence to locally uniform convergence to infinity.  The auxiliary
bridges `normal_family_of_normalSequenceOn` and
`normal_family_restrict_subsequence` are also checked.  Consequently Theorem
1.2 (meromorphic) is now a formal corollary of Theorem 1.3(1), with no
remaining meromorphic-specific gap.

The nonhyperbolic ambient reduction has also advanced.  The checked theorem
`nonempty_discCover_coordDisk_compl` proves that deleting one closed
coordinate disk from any analytic surface produces a disc-covered hyperbolic
surface, via the existing Green-function construction and uniformisation.
This gives a formal fixed compact anchor without requiring classification of
the original surface.  The checked theorem
`uniform_remote_finite_area_budget_all_covers` records the paper's full
uniform area budget on a fixed hyperbolic ambient: its single finite constant
is independent of the open domain, all exceptional sets of cardinality at
most `q`, the measurable subset of `L`, and the chosen universal disc cover.
The bridge comparing the original domain with the anchored hyperbolic domain
is still needed for a possibly nonhyperbolic ambient.

`PaperSolution.lean` now exists and compiles.  It contains the exact
independent proof declarations for Theorem 1.2 (entire) and Theorem 1.4, both
with no `sorryAx`.  Do not add the four remaining declarations until their
surface-dependent proofs compile.

For Theorem 1.3(1), `exists_orbit_components` and
`orbit_mem_of_compactifiedIterate_mem_image` now extract the genuine marked
orbit and its pairwise disjoint normality components.  The checked reduction
`noCompactWanderingOrbitClaim_of_componentOrbitImpossible` leaves precisely
`CompactComponentOrbitImpossibleClaim` as the analytic area core.

The surface backward-puncture machinery has now been started and its first
analytic obstruction is closed.  `Surfaces/OpenMapping.lean` proves that a
complex one-dimensional manifold has no open singleton and hence an open
surface map is nowhere locally constant.  It also exposes the corresponding
nonconstancy statement in extended charts.  The new checked module
`Surfaces/FiniteFibers.lean` combines this with isolated zeros to prove:

- `isDiscrete_fiber_of_isOpenMap_of_mdifferentiable`;
- `finite_compact_inter_fiber_of_isOpenMap_of_mdifferentiable`.

Thus an open holomorphic surface map has discrete fibres, and every fibre
meets a compact set finitely.  The new checked module
`Surfaces/LocalPunctures.lean` then proves finite compact inverse images of
finite sets and ports the planar finite backward-tree construction:

- `finite_compact_inter_preimage_of_finite`;
- `localPunctures_finite`;
- `localPunctures_countable`.

These results have standard axioms only.  They supply the exact finiteness and
countability input needed to approximate a surface barrier by finite backward
puncture sets.  What remains for Theorem 1.3 is to choose the compact working
domain/barrier from a hypothetically compact wandering orbit, connect these
puncture sets to the normality components, and apply the uniform area budget
and kernel convergence to obtain the contradiction.  For Theorem 1.3(2), the
same punctures must be combined with the countable-exception removal and the
already checked density-divergence/Fatou argument.  Theorem 1.5 then still
requires the corresponding singular-value area construction.

The author clarified that the dynamical barrier should follow the manuscript
literally: take dense finite subsets of the boundary of a relatively compact
working domain and close them under successive preimages.  For a globally
defined map, first remove a small closed coordinate disk in the initial
wandering component.  The implementation has been redirected accordingly.

The following new checked declarations implement this formulation:

- `exists_coordDisk_closedCarrier_subset_diff` selects the small closed
  coordinate disk inside a prescribed open set while avoiding the marked
  point;
- `exists_anchorDisk_orbit_components` proves that all later wandering
  components avoid this disk;
- `exists_hyperbolicAnchor_orbit_components` attaches the concrete universal
  disc cover of the disk complement, so every tail component lies in one
  fixed hyperbolic ambient surface;
- `LocalMap.restrictSource` and
  `isOpenHolomorphic_restrictSource` formalise restriction to a smaller open
  source;
- `LocalMap.boundaryBackwardTree`, its finiteness and backward-invariance
  lemmas, and `LocalMap.exists_boundaryPunctureSequence` now construct the
  increasing finite boundary-preimage sequence for a relatively compact
  working domain whose closure lies in the actual source.

This supersedes the earlier idea of using the complement of the normality
locus as the primary roots.  The compact-exhaustion barrier modules remain
valid auxiliary results, but the proof of the paper theorems should use the
boundary-preimage sequence and the anchor disk described above.

The local continuation now also proves the two missing compatibility facts.
`LocalMapRestriction.lean` shows that restricting the source preserves every
partial iterate of an orbit which remains in the smaller source, and preserves
trappedness.  `exists_hyperbolic_restricted_tail` applies this to the deleted
anchor disk: from time one, the restricted dynamics agrees exactly with the
original wandering orbit on a hyperbolic ambient surface.

`BoundaryPunctureSequence.lean` now proves that every finite-stage boundary
preimage eventually reaches a chosen boundary root.  Consequently every
stage is disjoint from the trapped set of the working-domain restriction, and
the closure of their union is disjoint from its normality locus.  The main
existence theorem exposes this normality separation in its conclusion.  This
is item (3) of the manuscript's boundary-preimage lemma.

The next analytic obligation is item (4): an open complementary component
meeting the trapped set is a normality component.  The remaining Montel step
should use Schwarz--Pick for the existing disc covers to get equicontinuity
when all iterates stay in the relatively compact working domain, followed by
Arzela--Ascoli in the one-point compactification.  After that, assemble the
one-step intrinsic area cancellation from `PaperAreaLemma`, pullback equality,
and the already checked `DomainAreaBlowup`.

That item (4) normality and topology bridge is now complete.  The new checked
declarations are:

- `DiscCover.exists_normal_lift_subsequence` and
  `DiscCover.exists_normal_disc_subsequence`, deriving surface Montel directly
  from the ordinary bounded unit-disc theorem through the universal cover;
- `CoordDisk.mdifferentiable_param` and `CoordDisk.isOpenEmbedding_param`,
  identifying a centred coordinate neighbourhood with the unit disc;
- `LocalMap.mdifferentiable_orbitOn`;
- `LocalMap.mem_omega_of_compact_orbit`;
- `DiscCover.exists_normal_disc_subsequence_compact_range` and
  `LocalMap.mem_omega_of_compact_orbits_in_subsurface`, which allow the fixed
  disc cover of the anchor-disk complement while retaining convergence in the
  original surface;
- `LocalMap.omega_restrictSource_eq_interior_trapped`, proving that on a
  relatively compact working source contained in that covered complement the
  normality locus is exactly the interior trapped set;
- `LocalMap.trappedSet_totalize_eq_trapped` and
  `LocalMap.barrier_component_eq_omega_component`, transporting the existing
  barrier-component theorem to open-source local maps.

All of these focused modules compile with standard axioms.  The next step is
to instantiate them simultaneously with `exists_hyperbolic_restricted_tail`
and `exists_boundaryPunctureSequence`, then feed the resulting normality
components into the intrinsic finite-model cancellation and
`DomainAreaBlowup`.  The missing work is now the area-transport assembly, not
uniformisation or Montel.

The fixed-anchor compact-tail package is now checked as
`LocalMap.IsWanderingComponent.exists_compact_hyperbolic_restricted_tail`.
It retains a compact tail for the restricted orbit inside one disc-covered
anchor complement.  The final positive-area Fatou contradiction has also
been isolated and checked as
`SurfaceDynamics.false_of_positive_area_finite_model_bounds`: positive chart
area is impossible once the boundary puncture exhaustion is dense on the
measured set and all finite-puncture model areas have one finite uniform
bound.  Thus the unresolved positive-area core is precisely the dynamical
proof of that uniform model-area bound.

The boundary package now also returns the manuscript inclusion
`g.trapped \ g.omega ⊆ closure (⋃ n, P n)`.  This follows from the new
generic theorem `AreaDeficit.mem_interior_trapped_of_not_mem_barrier`: the
open complementary component of a trapped point outside a closed
backward-invariant barrier stays in the source under every iterate, hence is
contained in the interior trapped set.  Its local-map wrapper is
`LocalMap.trapped_diff_omega_subset_barrier`.  Both compile with standard
axioms.  This discharges the density-blowup containment used for the set
`A*` in the manuscript; transport/cancellation is the next obligation.

`LocalMap.exists_backwardExceptionalFinsets` now enlarges any increasing
finite puncture sequence by a fixed finite exceptional set and all local
backward iterates.  It returns increasing finite stages whose union is
backward invariant in the working domain.  The accompanying hyperbolic-area
lemmas show that deleting this countable union preserves intrinsic area.
This formalises the manuscript passage from `A` to `A*`; the remaining core
is the uniform one-step metric transport/cancellation estimate.

The cancellation side of that estimate is now complete.  The checked
theorems `finite_area_cancellation_le`,
`DiscCover.uniform_finitePuncture_insertion_area_le`, and
`DiscCover.finite_model_cancellation_of_area_advance` handle Schwarz--Pick
inequalities, finite model area, and the uniform cost of adjoining boundedly
many exceptional punctures.  Finally,
`SurfaceDynamics.false_of_positive_area_area_advances` combines those facts
with puncture density blow-up and positive chart area.  Its sole analytic
input is now the uniform one-step area-advance configuration in each finite
model.  Proving that input by coordinate change of variables plus the local
density-deficit estimate is the remaining positive-area core.

The coordinate-change half of that input is now checked.
`DiscCover.chart_area_advance_of_density_deficit_holomorphic` turns a
single-chart integrated pullback-density deficit into intrinsic surface area
advance, deriving the ordinary complex derivative directly from surface
holomorphicity.  `AreaDeficit.Surfaces.finite_patch_area_advance` adds such
comparisons over a finite measurable partition; injectivity gives disjoint
image patches.  The remaining analytic task is therefore to instantiate the
local integrated deficit uniformly on those compact chart patches.

The domain-metric change-of-variables layer is now also checked as
`DiscCover.chart_domainArea_eq_image_of_pullback`. Given the pointwise
pullback identity for two componentwise hyperbolic subdomain densities, it
proves exact intrinsic-area transport on every measurable injective chart
patch. The remaining local analytic obligation is now geometric: derive that
density identity from the covering obtained after deleting the finite
exceptional values, then compare its smaller target domain with the global
finite-puncture model using the checked uniform remote-gain estimate.

The pointwise geometric part is now checked too.
`DiscCover.domainDensity_covering_pullback_components` starts with the
explicit universal disc covers chosen for the connected source and target
components. If the holomorphic restriction between those components is a
covering, it proves the exact pullback identity for their componentwise
hyperbolic densities. Together with
`chart_domainArea_eq_image_of_pullback`, this closes the metric and
change-of-variables portion of each injective patch. The next construction
must obtain those component coverings uniformly after deleting the finite
critical-value set and partition the wandering set among their source
components.

The singular-value covering bridge is now checked in
`SurfaceSingularCovering.lean`.  The complement of the locally defined
surface singular-value set is a covering target, and restriction to the
preimage of any subset of regular values is a genuine covering map.  This
will provide the component coverings above once the finite exceptional
target has been chosen inside the regular-value set.

`ChartCriticalValues.lean` now supplies the finite branch-value input on a
single compact source/target chart pair. It proves that fixed-coordinate
readings of a holomorphic surface map are analytic, that openness rules out
constant germs, and hence that both the critical points and their images in
a compact chart patch are finite. The next step is a finite source/target
chart refinement of the compact working set, followed by taking the finite
union of these chartwise branch-value sets.

`exists_finite_chart_branch_values` now performs that finite union for any
supplied finite compact chart-pair cover. It returns an actual `Finset` of
target branch values and proves that every covered point mapping outside the
set lies in a patch where the coordinate derivative is nonzero. What remains
in this substep is to instantiate the abstract cover using compact chart
patches for the working compact set and its compact image.

That instantiation is now checked as
`exists_finite_branch_values_on_compact`. Compact source and image sets are
covered by finitely many compact coordinate patches; their pairwise
refinement gives one finite target `Finset` containing every branch value
arising on the working compact set. Outside it, the theorem returns explicit
source and target charts with nonzero coordinate derivative. This completes
the finiteness input for the bounded-cardinality puncture insertion.

`SurfaceLocalBranching.lean` now turns the nonzero coordinate derivative
into an actual local-homeomorphism statement, using local injectivity of the
analytic coordinate reading together with openness of the surface map. Its
compact corollary produces a finite target set `E` such that the map is a
local homeomorphism on the working compact set away from `f ⁻¹' E`. The next
step is the proper/compact restriction argument upgrading this to a covering
over target sets whose fibres remain in the interior of the working compact
set.

The compact restriction upgrade is now checked in
`CompactSurfaceCovering.lean`. A continuous map from a compact restriction
is a covering over any target set whose fibres stay in the compact interior
and on which the ambient map is locally a homeomorphism. Combining this with
the finite branch-value theorem gives one finite `E` that works for every
such target set disjoint from `E`. This is the surface version of the planar
compact analytic covering lemma used in the existing proof.

`compact_interior_isCoveringMap` now replaces the compact subtype by the
open domain `interior K ∩ f ⁻¹' S` and proves that its map to the open target
`S` is a genuine covering. This supplies manifolds on both sides, so the
componentwise hyperbolic-metric pullback theorem can be applied directly.

The first component restriction lemma is checked as
`IsCoveringMap.surjective_connectedComponent`: every connected source
component of a covering maps onto a path-connected target. The proof is by
lifting a path from the image of the chosen source point to an arbitrary
target point. It will be paired with the inherited local sheet structure to
obtain the component covering used by the density pullback theorem.

`DomainComponentMap.lean` now constructs the induced holomorphic map between
the connected components of arbitrary open source and target domains. It
proves both the underlying-value formula and preservation of
holomorphicity. This removes the subtype/component bookkeeping that had
blocked the direct covering-lift proof of the componentwise metric identity.

That direct proof is now checked as
`DiscCover.domainDensity_covering_pullback`. For a holomorphic covering
between possibly disconnected open domains, it lifts the extremal disc of
the target component through the ambient covering, proves that the lift
stays in the chosen source component, and obtains exact pullback of the two
componentwise hyperbolic densities. No separate component-covering theorem
or global uniformisation assumption is needed.

`OpenDomainAreaTransport.lean` now completes the local change-of-variables
bridge. A holomorphic covering between open surface domains preserves the
intrinsic domain area of every injective measurable chart patch. The ambient
representative of the map is required to agree with the covering only on the
open source, so this applies directly to a `LocalMap`; no global holomorphic
totalisation is assumed. The proof combines the exact componentwise density
pullback with the planar Jacobian theorem and explicitly identifies the
component-chart derivative with the ambient coordinate derivative.

`SaturationDynamics.lean` now proves the dynamical set identities needed by
the cancellation argument. For a trapped starting set, every partial image
and the full forward saturation remain trapped; the harmless totalisation
sends the nth image exactly to the next image; the challenge's injectivity
hypothesis gives injectivity on the saturation; and pairwise wandering gives
`totalize '' saturation = saturation \ A`. It also proves measurability of
every image and of the saturation under exactly the challenge's surface
hypotheses. `SurfacePolish.lean` supplies the needed Polish presentation: it
builds a countable basis for the one-point compactification from a compact
exhaustion, metrises the resulting compact Hausdorff space, and transfers the
Polish structure back through the canonical open embedding.

`OpenDomainFinitePatchTransport.lean` now assembles the local covering
equalities over an arbitrary finite measurable chart partition. It proves
the global one-step inequality between the two intrinsic domain-area
measures, with zero analytic loss. Thus the remaining positive-area work is
to construct the finite chart-pair partition of the compact saturation and
instantiate the compact-interior covering after deleting the finite branch
values and the current puncture stage.

`RemoteCoveringAreaAdvance.lean` now combines all analytic parts of that
configuration. If the step map becomes a covering after deleting a fixed
remote compact obstacle and at most `q` values, then exact finite-patch area
transport, domain monotonicity, and the uniform compact-removal lemma give
one finite area-advance constant valid for every old open-domain model. This
is the precise formal version of the author's Lemma 2.6 note: the compact
obstacle and bounded finite punctures contribute a uniform amount, while the
covering part has zero loss.

The chart bookkeeping is now automatic. `CountablePatchTransport.lean`
sums exact local covering equalities over countably many disjoint measurable
patches, and `ChartPartitionCoveringTransport.lean` constructs those patches
from independent countable source and target chart partitions using the
Cantor pairing of their indices. Consequently
`exists_uniform_area_advance_of_remote_covering` needs only the covering,
measurability, injectivity, and compact-containment data; no finite chart
cover is left for the dynamical proof to supply.

The combined `SurfaceResearch` module compiles after these additions. The
local totalisation is also now proved Borel measurable by applying the
piecewise-continuity theorem on the open source and its complement, so it can
serve directly as the ambient representative in the automatic chart
transport theorem.
# Checkpoint 2026-09-26: local compact-covering bridge

`BoundedWanderingDomains/Surfaces/LocalCompactCovering.lean` now compiles.  It
applies the compact branch-value theorem to the genuine open-source map
`f.map : f.source → X`, converts the resulting nested subtype domain back to
an ambient open subset of `X`, and proves that its covering map agrees there
with `f.totalize`.  The excluded target consists of a finite branch-value set
and the compact image of the compact source boundary.  This closes the type
and topology gap between local maps and `RemoteCoveringAreaAdvance`.

The remaining geometric input for the area contradiction is to select the
compact covering model (or its relevant sheets) so that its boundary-image
obstacle is disjoint from the compact forward saturation.  The manuscript's
backward-boundary construction and the already formalised boundary barrier
package are the intended source of this separation.  Once connected, the
existing saturation identities and uniform remote-removal theorem provide
the finite-model area bound.

`BoundedWanderingDomains/Surfaces/LocalCompactAreaAdvance.lean` now also
compiles.  It composes the bridge with the uniform remote-removal estimate.
For every old finite-puncture domain it yields the one-step area inequality
as soon as (i) the backward-invariant punctures make the covering source a
subdomain of the old model, (ii) the measured set lies in that source, and
(iii) its image lies in the fixed compact set separated from the boundary
obstacle.  These are now the only geometric/dynamical obligations before
`false_of_positive_area_area_advances` applies.

The existing boundary tree has now been strengthened, rather than replaced:
`boundaryBackwardTree_forward_invariant` proves that every finite stage is
forward invariant at points inside the working domain (the roots lie on its
frontier, and all other points are preimages).  The set-valued and
finset-valued boundary packages expose this property.  The compiled lemma
`localCompactCoverDomain_le_finitePunctureDomain` uses it to discharge the
subdomain obligation in the local area-advance theorem.  This is the precise
reuse of the removed-disc/backward-orbit construction discussed with the
author.

The compiled theorem
`exists_uniform_area_advance_of_local_compact_finite_models` now packages the
whole finite-stage conclusion: from a forward-invariant boundary-puncture
stage, a measurable injective set in the compact interior, and avoidance of
the finite branch values and fixed compact obstacle, it produces the uniform
one-step intrinsic-area inequality.  Membership in the ambient compact-cover
domain is constructed internally.  The remaining issue is mathematical, not
subtype plumbing: for Theorem 1.3 the paper's local deficit argument must be
used without imposing positive separation between the compact orbit and the
image of the artificial source boundary.  The surface cutoff, density-ratio,
finite-puncture, and chart transport lemmas required for that direct version
are already compiled; their final map-specific assembly remains.

# Checkpoint 2026-09-26: compact anchor complements and global cancellation

The compact universal-cover trichotomy is now connected to the dynamical
backward tree. `CompactFiniteHyperbolization.lean` proves that every prescribed
three-point set on a compact Riemann surface has disc-covered complement and
that every larger finite stage remains disc-covered. The plane branch uses the
user-specified torus mechanism: the plane universal cover, two distinct lifts
of one puncture, and Little Picard. The sphere branch uses three omitted values.

`CompactGlobalAnchors.lean` now produces one increasing backward-invariant
finite sequence containing the same three positive-area anchors, a disc cover
of every stage complement, and the positive measurable wandering remainder
with its injectivity, image-minus-first-piece, and disjointness identities.

`AnchorComplementModels.lean` restricts those ambient stages to one fixed
three-anchor complement, preserves monotonicity, and transfers closure density
to the subtype. `PositiveAreaAdvanceReduction.lean` and
`CompactAnchorAreaReduction.lean` provide the global finite-area cancellation
route, avoiding the false requirement that the wandering union be compact in
the punctured subtype.

`GlobalFinitePunctureArea.lean` isolates the remaining finite-type geometric
input as `GlobalFinitePunctureAreaPackage`: finite total area for every finite
model and a uniform cost for inserting boundedly many punctures. It proves the
package for compact hyperbolic ambients from the existing compact estimates.
For the compact nonhyperbolic anchor complement, the remaining construction is
the finite-type cusp-area/Gauss--Bonnet bridge (especially the plane-cover or
torus branch), followed by instantiation of the already compiled global
cancellation reducer. The existing sharp 2*pi planar/spherical puncture bounds
and cusp-density estimates are the intended inputs.

## 2026-09-26: cusp area integrability

`BoundedWanderingDomains/CuspAreaIntegrability.lean` now proves the analytic
end estimate needed for finite-type surface area.  The logarithmic cusp
majorant is integrable in polar coordinates, and the existing pointwise
covering-density estimate therefore gives finite curvature-minus-one area on
a smaller punctured disc.  The proved endpoint is
`IsHolomorphicDiscCovering.lintegral_density_sq_cusp_lt_top`; it uses only the
standard axioms accepted by the audit.  The next bridge is to apply the same
test-disc argument to `DiscCover.chartDensity` in an ambient surface chart,
then cover a compact surface minus finitely many points by a compact core and
these finitely many cusp neighbourhoods.  This supplies the finite-total-area
half of `GlobalFinitePunctureAreaPackage`; the uniform insertion half should
then use the recorded Lemma 2.6 / 2π-per-puncture estimate.

That chart bridge is now also complete.  `Surfaces/CuspDensityBounds.lean`
proves the exponential-test-disc upper estimate directly for
`DiscCover.chartDensity`, and `Surfaces/CuspAreaFinite.lean` proves that the
inverse image of the smaller punctured chart disc has finite intrinsic area.
The remaining finite-total-area step is purely the finite-cover assembly:
choose one such chart around each member of the finite puncture set and use
local finiteness on the compact core.

The finite measure assembly is also compiled as `hyperbolicArea_univ_lt_top_of_finite_cusp_cover`: a compact core plus finitely many cusp patches has finite total intrinsic area.
## 2026-09-26 local checkpoint: compact finite-puncture area

- Added `CompactFinitePunctureArea.lean`.
- Proved `DiscCover.hyperbolicArea_compl_finset_lt_top`: a supplied disc cover of the complement of a finite set in a compact Riemann surface has finite total hyperbolic area.
- The proof selects puncture-avoiding coordinate disks, applies the compiled cusp integral estimate at every puncture, and covers the remainder by one compact core.
- Next bridge: identify the ambient `domainArea` of a connected finite-puncture domain with the intrinsic hyperbolic area of its subtype, then feed the result into `GlobalFinitePunctureAreaPackage`.
## 2026-09-26 local checkpoint: finite area of every puncture stage

- Added `DomainAreaSubtype.lean`, proving local and total agreement between ambient `domainArea` and intrinsic subtype area on connected open domains.
- Strengthened `FiniteModelArea.lean`: if the ambient hyperbolic surface has finite total area, every further finite-puncture model has finite total area.
- The latter proof avoids flattening nested subtypes. It combines compact local finiteness with the already-formalised metric comparison outside a compact set.
- Together with `hyperbolicArea_compl_finset_lt_top`, this supplies the total-area half of the global finite-puncture package for the compact-surface anchor model.
- Remaining package input is the global uniform insertion cost. The sharp one-chart theorem already gives `2π` per puncture; the next step is its compact-surface/global assembly (or removal of the unnecessarily global reduction if the working sets are compact away from the anchors).
## 2026-09-26 local checkpoint: anchor-stage total area

- Added the canonical finite-puncture corollary `hyperbolicArea_finitePunctureDomain_lt_top`.
- Added `anchorComplement_hyperbolicArea_lt_top` and `anchorComplement_finiteStage_area_lt_top`.
- Added `globalFinitePunctureAreaPackage_of_finite_total`, so the global package now reduces to its uniform insertion-cost half whenever the ambient hyperbolic area is finite.
- This discharges finite total mass for the fixed three-anchor complement and every finite backward stage on a compact surface.
- The remaining analytic input is the global surface version of the sharp point insertion estimate (uniform `2π` per inserted puncture). The one-chart sharp theorem and compact remote Lemma 2.6 form are already compiled.

## 2026-09-26 local checkpoint: one-point global insertion reduction

- Added `Surfaces/GlobalPointInsertion.lean`.
- A whole-surface bound for inserting one point into an arbitrary finite-puncture model now telescopes to the bounded-cardinality estimate `q * C`, directly at the level of nonnegative area-gain measures.
- Combined this with finite total area in `globalFinitePunctureAreaPackage_of_pointInsertion` and with the compact anchor complement in `anchorComplement_globalFinitePunctureAreaPackage_of_pointInsertion`.
- Consequently the compact global positive-area argument has one geometric input left: `UniformGlobalPointInsertionBound (ENNReal.ofReal (2 * Real.pi))`. No separate finite-set or cancellation argument remains.
- `UniformGlobalPointInsertionBound` is independent of the chosen disc cover, and `uniformGlobalPointInsertionBound_of_global_chart` proves the sharp `2π` bound whenever the ambient surface has one global planar chart with two omitted coordinate values (the normalized punctured-sphere model).
- `domainArea_eq_add_gain_on` proves exact area = old area + gain on surviving measurable sets. `finitePunctureDomain_area_insert_eq_add_gain` extends this to total area because finite deleted sets are null. Hence `uniformGlobalPointInsertionBound_of_totalArea_increment` allows the remaining estimate to be supplied equivalently by a one-puncture finite-type total-area/Gauss--Bonnet increment.

## 27 September local continuation: exact total-area equivalence

`BoundedWanderingDomains/Surfaces/GlobalPointInsertion.lean` now proves both directions between the whole-surface one-point gain bound and the corresponding one-puncture total-area increment, under the already established finiteness of each finite-puncture model. The focused module build passed (4027 jobs). This confirms that the remaining compact-global geometric input can be stated entirely as a Gauss--Bonnet-style estimate on total area; no further measure subtraction or cancellation issue remains in that reduction.

The previously formalised coordinate-disk removal does close the noncompact and proper-source branches, but does not by itself close the compact globally-defined positive-area case: after deleting finite anchors, the reduced saturation can accumulate at those anchors and need not be compact in the punctured surface. The finite-total-area/global insertion route remains necessary for that branch unless a separate compact-surface dynamics classification is formalised.
