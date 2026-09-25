# Surface extension: status and independent workstreams

Recovered on 25 September 2026 from archive version 15, research commit
`cdede188a8b5508f96e5c1b73af0b5b590f41968`. The stable entire-function
derived-set results are already proved. The remaining objective is the
arbitrary-Riemann-surface extension. Curvature is −1 throughout.

## Independent build targets

| Target | Contents | Remaining work |
| --- | --- | --- |
| `SurfaceGeometry` | Intrinsic density, curvature, Schwarz–Pick, area, null sets, positive chart area | Geometric inputs on exceptional ambient surfaces |
| `SurfaceFiniteRemoval` | Uniform compact remote, point and finite-removal bounds for arbitrary open subdomains | Sharp global point-removal cost and noncompact cutoffs |
| `SurfaceKernel` | Finite-puncture density convergence, with all component covers constructed | No remaining pointwise-convergence blocker; locally uniform statement optional |
| `SurfaceDynamicsTargets` | Partial iteration, normality, compact escape, exact target propositions | All three named surface dynamical claims remain unproved |
| `SurfaceResearch` | Assembles all surface workstreams | Final complete geometric and dynamical audit |

These are libraries in one pinned Lean project. They share their already
compiled foundations. They can be worked on in separate checkouts if needed;
they do not require duplicate repositories with divergent dependencies.

The kernel workstream no longer imports the remote-area workstream merely
to access unrelated normal-family facts. Its first restored build involved
98 local modules. A subsequent complete `lake build SurfaceKernel` passed
with 3736 jobs (most supplied by the restored Mathlib cache).

## User correction and proof route

On 25 September the user directed us back to Lemmas 2.2–2.4 of
Absence of bounded-orbit wandering domains. Lemma 2.2 is the intrinsic
Mihaljević–Rempe / Minda comparison lemma, already stated for hyperbolic
Riemann surfaces. The limit passage should be treated as a standard
comparison argument. Do not restart a large general kernel-convergence
project or describe this as a new mathematical obstruction.

The alternate normal-family/Hurwitz proof is already checked and retained.
Use its interface for the area argument; it does not need further expansion.
The formal comparison interface currently uses covering discs and Schwarz,
not an implemented intrinsic-distance formula for alpha and beta.

## Newly checked mathematics

- `AnalyticSurface` and `SubdomainCover` construct disc covers of connected
  open subdomains of a covered ambient surface, using uniformisation and
  excluding the plane/sphere alternatives. Covers of each component are
  constructed, not assumed.
- `ComponentDomains`, `ComponentDensity`, and `DomainChartDensity` give
  componentwise densities on arbitrary, possibly disconnected opens.
  Positivity, C² regularity, curvature −1, and measurable zero extensions
  are proved. They agree with any fixed cover of the relevant component.
- `ComponentKernel` and `DomainChartKernel` instantiate the checked
  finite-puncture limit on those actual components and chart densities.
- `DomainSchwarz` and `DomainRemoteBound` give the comparison estimate in
  covering-disc form, including a bound uniform over all old subdomains.
- `DomainFiniteCutoff` proves a uniform cutoff estimate for two finite
  puncture models. `DomainGainLimit.remote_domain_chart_cutoff` passes it
  to arbitrary closed complements by Fatou. This is now a proved area-limit
  application, not an assumed convergence statement.
- `DomainCompactGain.remote_domain_chart_compact_gain` bounds the gain on
  the portion of one fixed compact coordinate set lying in the smaller
  domain, uniformly over every closed old complement. No connectedness,
  positive distance from the old complement, or finite total area is assumed.

- `DomainAreaGain` constructs the intrinsic gain measure on arbitrary open
  domains. It is independent of the ambient cover, is supported on the
  smaller domain, and has the expected difference-of-squares coordinate
  formula.
- `DomainRemoteArea.remote_compact_domainAreaGain` assembles the fixed finite
  chart cover. It proves one finite intrinsic bound on a fixed compact L
  disjoint from closed K, uniform in every old closed complement A.
  This closes the compact remote-removal estimate for hyperbolic ambient S.

- `CompactDiscImages` and `DiscComparisonInfinity` prove that removing a
  fixed compact set changes the density ratio by at most `1 + epsilon`
  outside a compact set, uniformly over all old open domains. This is the
  qualitative upper comparison in covering-disc form.
- `DomainPlanarDensity` identifies intrinsic chart densities with the
  checked planar densities. `ChartPointRemoval` transfers the sharp `2*pi`
  bound to arbitrary domains contained in one chart.
- `DomainGainOrder` proves intrinsic localisation and telescoping bounds.
  `CompactPointRemoval` combines the local planar bound and remote gain
  estimates to give a finite compact point-removal cost uniform in the old
  domain. The compact measured set may meet the puncture and old complement.
- `CompactFiniteRemoval` gives the same uniform compact budget for a fixed
  finite set and a remote closed obstacle together. These compact estimates
  can now be used in the dynamical argument without waiting for the sharp
  global surface bound; that stronger bound remains a separate obligation.

`lake build SurfaceResearch` passed (4056 jobs). The surface axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.
`verification/surface-continuation.json` records this continuation's checks;
older submission metadata does not assert completion of the surface targets.

## Exact remaining obligations

1. Prove the sharp global curvature −1 point-removal bound of at most
   `2 * pi`, then the corresponding sharp finite-point bound. The uniform
   finite bounds on compact measured sets are now proved for hyperbolic
   ambient surfaces, but do not establish this sharp global statement.
   Give the boundary or exhaustion justification in the actual proof.
2. Establish the remote estimate for a cutoff with compactly supported
   differential but possibly noncompact support. Compact-support integration
   alone does not justify this case.
3. Treat nonhyperbolic ambient surfaces, including auxiliary punctures and
   their area cost. Current componentwise geometry starts with an ambient
   disc cover.
4. Prove `NoCompactWanderingOrbitClaim`,
   `NoCompactPositiveAreaWanderingSetClaim`, and
   `WanderingDerivedSingularLimitClaim` with their exact recorded hypotheses.
   Compact containment is inside the actual source `O`. This also requires
   the density-divergence half of paper Lemma 2.4 for the positive-area
   branch; the off-complement density-convergence half is already checked.
5. Run the final complete build, axiom audit, independent declaration
   comparison, metadata and attribution checks. The essentially-thick
   extension remains deferred by agreement.

## Recovery and focused commands

The recovered checkout is
`/workspace/scratch/5c43666a9327/bounded-orbit-work`.
Lean is `/tmp/lean-4.35.0-rc2-linux/bin/lean`; add that directory to `PATH`.
Use `LEAN_NUM_THREADS=2`.

```
python3 scripts/fetch_cache.py
python3 scripts/build_submission.py SurfaceKernel
lake build SurfaceKernel
lake env lean verification/KernelAxioms.lean
```

The staged build script now accepts explicit targets. Its default full
submission behaviour is unchanged. A staged build is followed by an ordinary
Lake target build, whose dependency hashes determine freshness.

The former workspace lost its checkout and compiled dependencies, although
the Lean runtime and compressed Mathlib cache survived. This is evidence of
a recovery cost, not a diagnosis of every conversation interruption. Save
the complete Git bundle, exact checked status and next proof obligation.
Never count a checkpoint as completion or treat an unproved claim as an axiom.
