# Astra handoff: derived-set formalisation

This branch is an active Lean research formalisation. Continue autonomously until all six declarations in `PaperChallenge.lean` have compiling proofs in `PaperSolution.lean`, the full build and axiom audit pass, and the GitHub and Palomar bundles are ready. Do not stop at checkpoints, partial reductions, or reports of remaining difficulty. Make frequent local commits and update `RECOVERY_ACTIVE.md` silently.

## Start here

1. Read this file, then `PAPER_STATEMENT_ALIGNMENT.md` for the exact theorem statements.
2. Read the latest entries of `RECOVERY_ACTIVE.md`; older history is background only.
3. Build the active module with:
   `C:\Users\Lasse\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe ..\Run-Local.py module BoundedWanderingDomains.Surfaces.CompactificationInsertionRiesz`
4. Continue at the first task below. Avoid rereading all legacy planning files unless a named dependency requires them.

## Checked state at handoff (27 September 2026)

Branch: `local-paper-formalisation`.

The compactification insertion analysis now compiles through a genuinely uniform estimate. The new-puncture boundary term is bounded by
`3 * (2 * π * ∫ |transitionSecond|)` independently of the finite stage and inserted point; all old compactification ends together contribute an eventual allowance of `1`. The raw, unnormalised restricted-surface cutoff Green identity removes the former fixed-reference constant. `compactification_pointInsertion_areaGain_finite` therefore has the common bound
`ENNReal.ofReal (1 + 3 * (2 * π * ∫ |transitionSecond|))`.

The latest compiling addition is
`DiscCover.compactification_uniformGlobalPointInsertionBound` in
`BoundedWanderingDomains/Surfaces/CompactificationInsertionRiesz.lean`. It automatically obtains the finite-puncture disc covers and handles the case where the inserted point is already present.

Supporting new results are in:
- `GlobalIntrinsicGreen.lean`: integrability when the intrinsic Laplacian, rather than the cutoff itself, has compact support.
- `IntrinsicGreenPairing.lean`: coordinate transport with only Laplacian support localized.
- `CompactificationCutoffGreen.lean`: raw restricted cutoff pairing, compact Laplacian support, and avoidance of all finite centres.
- `PunctureBoundaryMass.lean`, `NestedBoundaryMass.lean`, and `CompactificationInsertionEnds.lean`: explicit universal boundary bound propagated through nested covers and compactification ends.

## Immediate task

Import `CompactificationInsertionRiesz` into the compact positive-area route and apply
`compactification_uniformGlobalPointInsertionBound` to the anchor complement in
`CompactAnchorAreaReduction.lean`. Feed it to
`anchorComplement_globalFinitePunctureAreaPackage_of_pointInsertion`, then finish the compact branch of `CompactLocalAreaAdvance.lean` (or the nearest final reduction) and expose the arbitrary-surface proof as `PaperSolution.theorem_1_3_positive_area`.

The required constant only has to be finite; sharp `2π` is unnecessary here. Prove `ENNReal.ofReal (...) ≠ ⊤` with the standard `ofReal_ne_top` lemma.

## Remaining theorem-level work

`PaperSolution.lean` currently proves:
- Theorem 1.2 entire;
- Theorem 1.4;
- Theorem 1.3(2) for noncompact surfaces;
- Theorem 1.3(2) for disc-covered/hyperbolic surfaces.

Still required:
1. Theorem 1.3(2) on arbitrary compact surfaces, now expected to close from the uniform insertion theorem above.
2. Theorem 1.3(1), orbit escape. The remaining abstract core is `CompactComponentOrbitImpossibleClaim` in `OrbitEscapeReduction.lean`. Reuse `CompactOrbitNormal.lean`, `WanderingAnchorDisk.lean`, `WanderingCompactTail.lean`, `RestrictedOmega.lean`, and the completed area theorem where applicable. The user expects the ordinary bounded Montel theorem after lifting through the supplied universal disc cover; do not seek a full new uniformisation theorem.
3. Theorem 1.2 meromorphic, which should be a direct wrapper from Theorem 1.3(1). `MeromorphicEscape.lean` already contains `wanderingLocallyUniformInfinityClaim_of_surface_theorem`.
4. Theorem 1.5. The remaining core is `WanderingOrbitClusterMeetsDerivedClaim` in `DerivedLimitReduction.lean`. Use the completed finite-removal estimate (`UniformFiniteRemoval.lean`), the preimages-of-boundary construction in the paper, and the same dynamical proof architecture as the entire case.

## Author's mathematical guidance

- The meromorphic theorem follows directly from the surface theorem.
- The general proof of Theorem 1.3 should reuse the existing entire proof, replacing its subharmonic step by Lemma 2.6.
- Theorem 1.5 uses: for disjoint compact `K,L` in a Riemann surface and fixed finite `q`, deleting `K` and at most `q` points from a hyperbolic open `U` increases hyperbolic area on a finite-area subset of `L` by at most a uniform constant. The formalisation already proves the stronger finite-removal package needed here.
- Analytically, the log quotient of the two hyperbolic metrics is subhyperbolic; its Riesz measure is the area-element difference. The quotient tends to `1` at boundary points in `L`; punctures have controlled logarithmic growth; Lemma 2.2 supplies uniformity. The explicit boundary calculation above formalises this route.
- A hyperbolic surface may be treated as a Riemann surface supplied with a universal cover from the unit disc. Connected open subsets inherit disc covers (`SubdomainCover.lean`).
- For a nonhyperbolic compact surface, fixed punctures suffice: the only cases are sphere and torus; a punctured torus lifts to the plane minus a lattice and is hyperbolic. The existing compact hyperbolisation/anchor files formalise the needed finite-anchor alternative.
- For the barrier, follow preimages of the boundary as in the paper. In the global rational case one may remove a small ball in the first wandering domain so the map becomes local rather than globally defined.

## Exact specification and completion rules

The exact targets are the six declarations in `PaperChallenge.lean`. The compact set in Theorem 1.3(2) is a compact subset of `O`. Simple connectivity is assumed only in Theorem 1.5. Use `handoff/reference/no-bounded-WD-2.tex` as the current draft; its introductory statements control.

Completion means:
- all six `PaperSolution` theorems compile without `sorry` or new axioms;
- entire and meromorphic cases are deduced from surface/local results where possible;
- remove obsolete duplicate entire-case machinery not needed by the general proof;
- audit unused imports and dependency packages, including whether approximation/Runge imports are truly needed;
- remove parallel duplicate arguments where one theorem can serve all cases;
- run the full build and an axiom audit (only normal classical axioms; challenge placeholders are specifications, not solution dependencies);
- update README and `formalization.yaml` with the current exact six challenge statements;
- prepare a GitHub update bundle and a Palomar submission bundle.

Ignore generated `verification/limited-build/*.log` files. Tool edits have occasionally corrupted `𝓘` to `𝒘` and `𝓝` to `𝐩`; normalize those substitutions before diagnosing strange parser/type errors.
