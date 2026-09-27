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

## Intrinsic density continuation (25 September)

The supplied-disc-cover interface now has proved holomorphic lifting, the
nonvanishing coordinate derivative, Schwarz–Pick on the disc, and an intrinsic
positive chart density. Its value is independent of the fibre and of the
cover. Its local inverse-branch formula proves C² regularity and the curvature
−1 equation. See `Surfaces/DensityRegularity.lean` and its imports. These results
are covered by the standard-axiom audit. Surface area-removal estimates and the
three surface dynamical targets are still outstanding.

## Local recovery checkpoint (26 September 2026)

The earlier outstanding-work list is obsolete: the intrinsic density, curvature,
area measure, puncture insertion bound, remote-removal estimate (including the
paper's all-covers formulation), finite chart transport, boundary-preimage tree,
restricted normality components, and finite-model cancellation are now proved
and compiled. `PaperAreaLemma.lean` gives the uniform remote finite-area budget
with a constant independent of the old domain, the moving set of at most `q`
punctures, the measured subset, and the chosen disc cover.

The compact-saturation topology is now closed: source restriction preserves
partial iterates of trapped points, its normality locus is contained in the old
normality locus, and a set whose saturation lies in the restricted source stays
inside `trapped \ omega`. `PositiveAreaBarrierReduction.lean` combines this with
the boundary package to place the original positive-area set in the closure of
an increasing finite forward-invariant puncture sequence. The remaining step
for Theorem 1.3(2) is the direct local one-step area advance for the holomorphic
map on that compact working source. The provisional compact-cover theorem is
insufficient because it deletes a compact boundary-image set which need not be
disjoint from the compact orbit set; the paper's density-quotient/Lemma 2.6
argument must avoid that extra hypothesis.

For Theorem 1.3(1), deleting a coordinate disk in the first wandering component
and passing to its disc-covered complement is compiled. Ambient Montel descent
from this cover is now proved with compact control only at the disc centres.
Ordinary normality of the tail is not itself contradictory (the tail already
lies in `omega`); the existing planar hyperbolic-area growth/cancellation
argument still has to be transported through the finite surface chart patches.

For Theorem 1.5, the topological compactification reduction is complete and the
surface singular-value covering theorem is complete. Its remaining analytic
core is the finite-model area contradiction showing that the orbit cluster set
meets `derivedSet f.singularValues`. Once Theorems 1.3(1) and 1.5 compile, the
meromorphic Theorem 1.2 wrapper is already implemented conditionally on the
surface orbit theorem.

The positive-area analytic core is now proved.  `LocalCompactModelPatches.lean`
isolates a source point from its discrete fibre, chooses a compact source model,
and separates a compact target neighbourhood from the image of the model
boundary.  `CompactLocalAreaAdvance.lean` covers the compact wandering
saturation by finitely many such models, replaces the cover by a measurable
disjoint partition, adds the local constants, and proves
`compactLocalAreaAdvanceClaim`.  Combining this with the already compiled
boundary, exceptional-set, cancellation and Fatou steps gives the unconditional
theorem
`noCompactPositiveAreaWanderingSetClaim_of_discCover` for every surface supplied
with a holomorphic universal covering by the unit disc.  The axiom audit lists
only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining passage to the exact arbitrary-surface statement is now isolated
from the area argument.  One may either (a) formalise the standard fact that a
surface with a suitable finite set of punctures has a disc universal cover and
delete the backward orbits of those punctures, or (b) transfer the compact
saturation to the already compiled disc-covered complement of a coordinate
disk.  Route (a) matches the paper notes and preserves positive chart area
because the exceptional backward orbit is countable.  No new density-ratio or
Riesz-measure estimate is needed.
