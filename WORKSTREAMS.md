# Surface extension: status and independent workstreams

Recovered on 25 September 2026 from archive version 15, research commit
`cdede188a8b5508f96e5c1b73af0b5b590f41968`. The stable entire-function
derived-set results are already proved. The remaining objective is the
arbitrary-Riemann-surface extension. Curvature is −1 throughout.

## Independent build targets

| Target | Contents | Remaining work |
| --- | --- | --- |
| `SurfaceGeometry` | Intrinsic density, curvature, Schwarz–Pick, area, null sets, positive chart area | Geometric inputs on exceptional ambient surfaces |
| `SurfaceFiniteRemoval` | Uniform compact chart remote-removal bound for arbitrary open subdomains | Intrinsic global assembly; point-removal cost and noncompact cutoffs |
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

`lake build SurfaceResearch` passed (3990 jobs). The surface axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.
`verification/surface-continuation.json` records this continuation's checks;
older submission metadata does not assert completion of the surface targets.

## Exact remaining obligations

1. Identify the new componentwise chart gain with the intrinsic gain measure
   and assemble the fixed finite chart cover into the global compact estimate.
   The chart estimate and its limit passage are proved.
2. Prove the curvature −1 point-removal bound of at most `2 * pi`, then
   the finite-point bound on arbitrary surfaces. The existing sphere/plane
   bound does not settle this general case. Give the boundary or exhaustion
   justification in the actual proof, rather than assuming the area bound.
3. Establish the remote estimate for a cutoff with compactly supported
   differential but possibly noncompact support. Compact-support integration
   alone does not justify this case.
4. Treat nonhyperbolic ambient surfaces, including auxiliary punctures and
   their area cost. Current componentwise geometry starts with an ambient
   disc cover.
5. Prove `NoCompactWanderingOrbitClaim`,
   `NoCompactPositiveAreaWanderingSetClaim`, and
   `WanderingDerivedSingularLimitClaim` with their exact recorded hypotheses.
   Compact containment is inside the actual source `O`.
6. Run the final complete build, axiom audit, independent declaration
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
