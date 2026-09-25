# Surface extension: status and independent workstreams

Recovered on 25 September 2026 from archive version 15, research commit
`cdede188a8b5508f96e5c1b73af0b5b590f41968`. The stable entire-function
derived-set results are already proved. The remaining objective is the
arbitrary-Riemann-surface extension. Curvature is −1 throughout.

## Independent build targets

| Target | Contents | Remaining work |
| --- | --- | --- |
| `SurfaceGeometry` | Intrinsic density, curvature, Schwarz–Pick, area, null sets, positive chart area | Geometric inputs on exceptional ambient surfaces; componentwise extension for disconnected domains |
| `SurfaceFiniteRemoval` | Uniform compact remote-removal bound for finite-puncture models, abstract Fatou transfer | Apply kernel convergence to actual chart gain integrands; cover all components |
| `SurfaceKernel` | Normalised lifts, Hurwitz, density monotonicity, kernel convergence | Build the concrete puncture-exhaustion and area-limit applications |
| `SurfaceDynamicsTargets` | Partial iteration, normality, compact escape, exact target propositions | All three named surface dynamical claims remain unproved |
| `SurfaceResearch` | Assembles all surface workstreams | Final complete geometric and dynamical audit |

These are libraries in one pinned Lean project. They share their already
compiled foundations. They can be worked on in separate checkouts if needed;
they do not require duplicate repositories with divergent dependencies.

The kernel workstream no longer imports the remote-area workstream merely
to access unrelated normal-family facts. Its first restored build involved
98 local modules. A subsequent complete `lake build SurfaceKernel` passed
with 3736 jobs (most supplied by the restored Mathlib cache).

## Newly checked mathematics

`KernelDomains.lean` proves density comparison for two nested open subdomains
in a single ambient chart. A fixed limiting domain supplies a uniform upper
bound for every approximant.

`KernelNormal.lean` proves that a normal limit of disc lifts with a fixed
interior centre stays in the entire open disc, by the maximum modulus
principle. No shrinking-disc factor is lost.

`KernelConvergence.lean` proves `DiscCover.density_tendsto_of_dense_punctures`.
Given a covered ambient surface, decreasing covered open domains, and a
covered component of the complement of the limiting closed set contained
in every domain, the densities converge to that component's density if
the domains omit increasing finite sets dense in the closed complement.
Normalised extremal lifts, derivative convergence, Hurwitz, connectedness
and Schwarz–Pick prove the statement. Density convergence is not assumed.

Disc covers are geometric input data here. This theorem does not itself
prove that every required domain or component has such a cover.

## Exact remaining obligations

1. Construct the required covers of the approximating domains/components
   from the uniformisation results, and instantiate kernel convergence on
   finite puncture exhaustions, with and without a fixed removed set.
2. Transfer the fixed chart gain estimates by Fatou, verifying measurability
   and the equality with intrinsic gain. Handle disconnected removal
   domains componentwise: a single surjective disc cover covers a connected
   domain only.
3. Prove the curvature −1 point-removal bound of at most `2 * pi`, then
   the finite-point bound. The proposed surface proof still requires
   justified boundary/cusp flux or an alternative argument; the existing
   sphere bound does not settle the arbitrary-surface case.
4. Establish exhaustion convergence and the remote estimate for a cutoff
   with compactly supported differential but possibly noncompact support.
   Compact-support integration alone does not justify this case.
5. Treat nonhyperbolic ambient surfaces, including the auxiliary-puncture
   reduction and its area cost.
6. Prove `NoCompactWanderingOrbitClaim`,
   `NoCompactPositiveAreaWanderingSetClaim`, and
   `WanderingDerivedSingularLimitClaim` with exactly their recorded
   hypotheses. Keep compact containment inside the actual source `O`.
7. Run the complete build, axiom audit, independent declaration comparison,
   metadata and attribution checks. The essentially-thick extension remains
   deferred by agreement.

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
