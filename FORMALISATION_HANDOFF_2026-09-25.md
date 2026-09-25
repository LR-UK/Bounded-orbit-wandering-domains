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
