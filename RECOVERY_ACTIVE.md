# Active continuation — do not stop at checkpoints

User explicitly instructed autonomous continuation until the full formalisation
is done or their input is genuinely required. A checkpoint is not completion.
Stable refs remain at 4a2c4b75c71541f569b7ae34bde616bcca66c07a.
Last audited checkpoint at start of this continuation: 182c39f.

Current work: construct intrinsic conformal hyperbolic density/area on surfaces
from the supplied holomorphic disc covering. First prove holomorphic lifting
and local inverse branches on arbitrary Riemann surfaces. Active source:
BoundedWanderingDomains/Surfaces/HolomorphicLifting.lean.

Build environment: PATH=/tmp/lean-4.35.0-rc2-linux/bin:$PATH, LEAN_NUM_THREADS=2.
Repository: /workspace/scratch/b0e1bbb36193/bounded-orbit-work.
Scratch conversation workspace: /workspace/scratch/bcaaac34f9c3.

Do not add geometric area estimates as assumptions and call the result proved.
No sorry/admit/custom axioms in proof modules. The three surface dynamical
propositions in Statements.lean are unproved targets. The entire-function
results and old bounded planar local results are proved.

Checkpoint archive identity: libfile_0280ba24a16c81919e3cd8025b3792e9,
current version 4 at start of this continuation. Replace with guarded version
on later saves. Preserve stable archive and stable Git refs. No public push.

## 25 September continuation: intrinsic density

Six new modules now build without holes or unexpected warnings:
HolomorphicLifting, PlaneReading, DiscSchwarz, CoordinateDerivative,
CoveringDensity, DensityRegularity (all under Surfaces/).
They prove holomorphic lifting, Schwarz–Pick, nonzero coordinate derivative,
independence of density from the fibre and from the cover, positivity,
local inverse-branch expression, C² regularity and curvature −1.
They are imported by SurfaceResearch; principal theorems added to
verification/SurfaceAxioms.lean. No new area theorem is yet claimed.
Next: coordinate transformation and Schwarz–Pick between covered surfaces,
then coordinate-invariant area and the removal estimates.
Focused build: lake build BoundedWanderingDomains.Surfaces.DensityRegularity
(success: 3712 jobs). Full audit follows at the next checkpoint.

Full audit passed: 91 distinct axiom reports, 311 sources, 8 theorem and 26 definition comparisons.

## Workspace recovery, 25 September morning

Execution workspace was replaced, losing the old repository/cache under
/workspace/scratch/b0e1bbb36193. The saved ZIP is intact and has been restored
to /workspace/scratch/bcaaac34f9c3/bounded-orbit-work. The standalone bundle
was truncated after reset; use the intact ZIP's embedded bundle.

Ten subsequent modules were reconstructed from the complete tool-call text:
CoordinateChainRule, SurfaceSchwarz, DensityCoordinateChange, ChartArea,
LocalAreaMeasure, CountableChartPartition, HyperbolicArea, SubdomainDensity,
LogDensityRatio, DensityRatioInvariance. They had each compiled successfully
before the workspace replacement. The second full audit was running when
the environment changed; its completion was not observed. Recheck restored
sources. No new proofs or altered hypotheses were introduced in recovery.

These prove coordinate-invariant hyperbolic area independent of chart
partition and disc cover, Schwarz–Pick, subdomain monotonicity, and the
log-ratio area-gain equation. Full puncture/remote-removal bounds and the
three arbitrary-surface dynamical claims remain outstanding.

Next: continuous intrinsic density ratio, area-gain integral and coordinate
formula, surface Green/cutoff estimates, puncture/kernel convergence, then
dynamical statements. Preserve stable release refs, do not stop at checkpoints.
Current saved archive version: 5 (c6a9399); newer recovery save will follow.

Active unverified additions after recovery: DensityRatioContinuity.lean,
AreaIntegration.lean, AreaGain.lean, ChartGainCutoff.lean. These have proof
scripts but await the restored build; do not claim they are checked yet.
Cache restored successfully (3884 files). Staged full build running at
/tmp/restored-build.log, exec session 95434. New runtime same /tmp path.
Most recent durable checkpoint ec48c36, archive version 6.

Further draft modules: UniformDiscAvoidance (local and compact uniform
avoidance via covering lift and Schwarz lemma), ExtremalDisc (recentres the
cover to realise the density). SubtypeHolomorphic is checked separately:
/tmp/surface-subtype-holo.log, 2821 jobs, no warnings.
Current rebuild has passed >340 local modules without failure. It will reach
new AreaGain through SurfaceResearch. ChartGainCutoff and ExtremalDisc need
separate builds/imports after the staged run because its graph was fixed
before their creation. Do not count draft scripts as checked results.

## Continuation: checked area gain and uniform remote density bound
All reconstructed modules and the seven WIP modules now individually compile.
New DiscDilation, DiscAvoidanceRatio and RemoteDensityBound compile too.
RemoteDensityBound derives a uniform density-ratio bound over all covered
open subdomains of a covered ambient surface, with centres in a compact set
and any disjoint closed removed set. This is an actual geometric bound,
not an assumed area estimate. ChartGainCutoff still takes its explicit
log-ratio hypothesis; assembly into full remote area bounds remains.
All are imported by SurfaceResearch and principal axioms added to audit.
The initial restored staged build stopped at AreaIntegration; fixed now.
Full submission audit is being restarted at /tmp/continued-audit.log.
Current repository: /workspace/scratch/bcaaac34f9c3/bounded-orbit-work.
Next: log-ratio bridge, coordinate cutoff assembly / surface Green;
point-removal bound, kernel convergence and surface dynamics still needed.
The arbitrary-surface dynamical claims are NOT proved yet.

## Continuation, 25 September: checked chart bridge

Focused builds passed for four previously untracked modules:
`UniformizationBridge` (hyperbolic uniformisation supplies the disc cover),
`LogRatioBound`, `RemoteChartGain` (uniform chart cutoff estimate from compact
separation), and `AreaNullSets` (intrinsic area and chart area have the same
null sets). The deprecated alias warning in `AreaNullSets` was removed and its
focused rebuild passed without warnings. These are imported by `SurfaceResearch`.
They have not yet assembled into the global removal estimate. The point
removal bound, exhaustion/kernel convergence and dynamical claims remain.
Next: turn the chart cutoff estimate into a bound on compact measured sets
uniformly in the open domain, then handle the noncompact measured region via
the reverse cutoff and an exhaustion argument. No new hypotheses are being
treated as theorems.

`PositiveAreaBridge` now proves that a measurable set with positive area in
one chart has positive intrinsic hyperbolic area. Its focused build passed.
This is the exact measure bridge for the positive-area dynamical target; it
does not establish the target itself.

`RemoteChartCompact` now converts the uniform density-ratio/cutoff bound to
an actual bound on intrinsic area gain over a compact set in one chart. Its
constant is independent of the disc cover chosen on the smaller domain.
The focused Lean build passed without warnings. **Important limitation:** its
cutoff must be supported inside the *variable old domain* `V`. Hence its
constant can depend on `V`, and a finite chart cover alone cannot establish
the needed uniformity over all old domains. For finite puncture models,
extend the bounded logarithmic density ratio subharmonically through the
punctures and integrate against a fixed ambient cutoff. Then use finite
chart patches, finite subadditivity and kernel/exhaustion convergence. This
is the next genuine analytic obstacle; do not claim the uniform compact
removal theorem from `RemoteChartCompact` alone.

The existing proved planar `density_deficit_cutoff` handles a finite set of
exceptional points inside a fixed cutoff's support. The new surface modules
`FinitePunctureChartCutoff` and `FinitePunctureRemoteChart` transport that
result to chart densities. The latter gives one logarithmic bound from
ambient compact separation for all old domains and all finite exceptional
sets; the cutoff can pass through those exceptional points. Focused builds
passed; an unused-binder warning was subsequently removed. Next connect
an ambient chart restricted to the complement of a finite point set to this
interface, then use fixed ambient chart cutoffs in the finite covering step.

`FinitePunctureChartTarget` now verifies the double chart restriction to
the complement of arbitrary finite `P` and the remote domain, and proves a
single fixed ambient chart cutoff and compact-chart gain estimate uniform
over all such `P`, old covers and remote covers. Its focused build passed;
it is imported into `SurfaceResearch`. Next assemble finite chart cover of
a compact measured subset of `M \ K`, identify coordinate integrals with
intrinsic area gain on punctured models (ignoring finite null sets), then
prove limit over puncture exhaustions and the full dynamical results.

`FinitePunctureAreaBridge` now compiles without warnings: finite chart
exceptional values are null, inverse-chart images of measurable sets are
measurable, and a fixed compact chart patch has a single *intrinsic* gain
bound for every finite puncture model. This is a genuinely uniform metric
area estimate, though only for one compact chart patch and only on the part
surviving the punctures. Next prove finite chart covering/subadditivity of
an arbitrary compact remote set, then pass to derived-set/infinite-puncture
limits and prove the three dynamical statements. No full surface result yet.

`FinitePatchAssembly` and `CompactChartPatches` now close the entire
finite-puncture remote compact bound for a hyperbolic ambient surface:
`DiscCover.remote_compact_gain_finite_puncture_models` derives a finite
constant from compact separation, independent of the finite puncture set
and both old/new covers. A key correction is `chartPunctures`: filter
punctures by chart source before taking chart coordinates, since the
underlying partial chart function has arbitrary values outside its source.
The finite patch cover proof uses the exact source-filtered exceptional set.
Focused builds passed without warnings. Next: kernel convergence as finite
punctures become dense in the complement of an arbitrary open domain;
then full remote bound, 2π point-removal bound, exceptional ambient surfaces,
and three dynamical claims. No full-surface theorem is claimed yet.

`DenseFinitePunctures` proves the needed topological exhaustion: any
closed subset of a second countable surface is the closure of an
increasing union of finite subsets. Its focused Lean build passed.
Still missing: convergence of intrinsic Poincaré density on the
punctured-domain sequence (normal-family/Hurwitz step), a Fatou transfer,
point-removal 2π and full surface dynamics.

`GainFatou` supplies the checked measure-theoretic transfer: measurable
chart integrands with pointwise convergence on a fixed measurable chart
set inherit any uniform finite integral bound. The geometric kernel
convergence and its chart measurability hypotheses remain unproved. The
planar `InteriorDensityLimit` proves an analogous limit using bounded
holomorphic subsequences and omission/Hurwitz, but that proof is typed
for planar finite-puncture metric inputs and must be adapted to the
ambient disc-cover lift on an arbitrary surface. Do not treat this as
an assumption satisfied by the surface metrics.

`KernelLift` is now checked: covers of arbitrary open subdomains lift
holomorphically to the fixed ambient disc; density-extremal discs lift
with a prescribed ambient centre; any sequence of these lifts has a
locally uniform holomorphic subsequence on a smaller disc, retaining
the fixed centre. This prepares the nonconstant/Hurwitz argument but
does not yet prove density convergence. To finish, establish a uniform
upper bound for subdomain densities at the chosen centre from a disc
inside the limiting domain, use the extremal derivative identity to
show the ambient subsequential limit is nonconstant, prove avoidance
of the closed complement by an appropriate surface Hurwitz lemma,
and compare with the limiting domain's density via Schwarz-Pick.

`LiftedPunctureClosure` now proves that the inverse image of an increasing
dense finite puncture exhaustion under the open ambient covering map is
dense in the inverse image of the closed limit set. Via the planar Hurwitz
theorem, a nonconstant locally uniform limit of ambient-disc lifts avoiding
the finite punctures cannot meet the closed limiting complement wherever
the limit stays inside the disc. `KernelLift` additionally proves the limit
stays inside the ambient disc on a sufficiently small fixed source disc
when all lifts share an interior centre (Schwarz–Pick displacement bound).
The focused build passed; full entry-point build follows. Next show the
limit is nonconstant from extremal derivatives and uniformly bounded
subdomain density, then use connectedness and Schwarz–Pick to identify the
limit density. These results do not yet establish kernel convergence.

`KernelNonconstant` now proves the chain-rule transfer of the subdomain
extremal derivative identity to ambient-disc lifts and the normal-family
noncollapse criterion: any uniform upper bound on the subdomain densities
forces a nonzero derivative in a locally uniform limit. A nonzero derivative
gives the exact nonconstancy required by `ambient_hurwitz_avoidance`.
The missing link is the uniform upper density bound from the fixed limiting
component, plus assembly of this lemma with the family of punctured covers.
