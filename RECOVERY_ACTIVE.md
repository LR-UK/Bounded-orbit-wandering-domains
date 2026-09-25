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
