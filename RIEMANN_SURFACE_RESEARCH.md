# Riemann-surface extension — research branch

## Stable version

The verified version 1.3.0 is preserved at
`4a2c4b75c71541f569b7ae34bde616bcca66c07a`:

- Stable branch: `stable-v1.3.0`.
- Annotated release tag: `v1.3.0`.
- Original prepared branch: `formalise-spherical-singular-limits-recovered`.
- GitHub update archive: `bounded-orbit-github-update-1.3.0.zip`, unchanged.

The experimental work is on `research-riemann-surfaces`. It is not part of
the stable release or its Palomar submission. No branch has been pushed.
The stable verification report applies to the stable commit, not to the
unfinished geometric extension described here.

## Current status, 24 September 2026

The full arbitrary-surface formalisation is **not complete**. In particular,
this branch does not yet prove either local dynamical theorem in the user's
new formulation. No such claim is hidden in an input structure or an axiom.
The essentially thick extension is explicitly deferred.

### Proved global formulations

`BoundedWanderingDomains/GlobalLimitStatements.lean` adds the locally uniform
escape-to-infinity theorem and the pointwise derived-singular-value theorem.
Together with the existing locally uniform derived-set theorem, these are
included in the consolidated independent `Challenge.lean` and supplied by
`Solution.lean`. The main comparator checks six theorems and thirteen
supporting definitions. The older singular-limit comparator remains usable.

### Checked surface foundation

`SurfaceResearch.lean` is a separate research entry point, built by the default
Lake target and audited by `verification/SurfaceAxioms.lean`.

- `LocalDynamics.lean`: actual open-source local maps, partial iteration,
  the trapped self-map and its continuous iterates, normality in the uniformity
  of the one-point compactification, actual normality components and wandering
  component orbits. Undefined iterates never enter normality on trapped sets.
- `CompactificationEscape.lean`: convergence to the added point is equivalent
  to eventual avoidance of every compact set; a sequence either escapes or
  has a subsequence converging inside the surface.
- `CompactSeparation.lean`: the compact-separator condition, symmetry and
  restriction, and its automatic validity when either set is compact.
- `SeparatingCutoff.lean`: disjoint closed sets with a compact separator admit
  a smooth separating cutoff, locally constant outside a compact set.
- `ChartLaplacianSupport.lean`: the cutoff's chart Laplacian has compact support
  and that support misses every set near which the cutoff is constant.
- `SmoothSurface.lean`: complex differentiability of chart transitions implies
  an underlying smooth real structure. The cutoff theorem therefore applies
  to an arbitrary Hausdorff second-countable Riemann surface, with no extra
  smooth-structure assumption.
- `DiscCover.lean`: supplied surjective holomorphic disc coverings and the
  simple connectivity of their source.
- `GeometricArea.lean`: the earlier measure-theoretic exhaustion argument,
  explicitly conditional on infinite limiting area and area convergence.

The additional upstream metric construction in
`RiemannDynamics/Uniformization/HyperbolicSurface.lean` has been ported from
Will (Ziang) Li's existing pinned revision. It proves existence of a compatible
complete metric locally isometric to the hyperbolic disc, given hyperbolicity
of the universal path cover. Its three disc-model dependencies are included
with the original authorship and licence headers. This metric result alone
does not construct the area comparison needed below.

### Exact unproved targets

`Surfaces/Statements.lean` records three named propositions, not theorems:

1. `NoCompactWanderingOrbitClaim`: no point orbit of a wandering normality
   component stays in a compact subset of the actual source O. No V, simple
   connectivity, or injectivity hypothesis is included.
2. `NoCompactPositiveAreaWanderingSetClaim`: the positive-area wandering-set
   statement, with injectivity on the forward saturation and compact containment
   in O. Positive area is defined in a chart.
3. `WanderingDerivedSingularLimitClaim`: simply connected component orbits
   have a subsequence escaping every compact subset of X or converging to a
   derived singular value. No injectivity hypothesis is included.

The covering definition explicitly requires surjectivity over the regular
value neighbourhood. Mathlib permits covering maps with empty fibres, so
that additional range condition is recorded rather than silently omitted.
The corrected compact containment is K ⊆ O throughout.

### Outstanding analytic work

`SURFACE_AREA_PROOFS.md` contains mathematical proof notes, not Lean theorems.
The remaining obligations are:

1. Construct the intrinsic curvature -1 area and connect it with local
   conformal densities and the descended metric.
2. Prove the 2π puncture bound on arbitrary surfaces, including the boundary
   or exhaustion argument; the sphere theorem does not discharge this.
3. Prove the uniform remote-removal estimate using the now-proved cutoffs,
   intrinsic Schwarz comparison and a justified integration/exhaustion formula.
4. Connect these estimates to the partial-iteration normality components and
   prove the two local dynamical results, including the positive-area case.

The finite-model hypotheses used inside the existing planar proof are fully
proved there. They are not treated as proved for arbitrary surfaces.

### Verification

```
lake build SurfaceResearch
python3 scripts/verify_submission.py
python3 scripts/verify_metadata.py
python3 scripts/audit_attribution.py
```

The strict audit checks all proof dependencies for the standard axioms only,
compares the six main Challenge declarations and the two legacy singular-limit
declarations, and scans all project sources for unexpected holes. Passing this
audit does not turn a named, unproved research proposition into a theorem.
No official independent-kernel replay or registry acceptance is claimed.
