# Remaining steps after version 0.12

The conditional bounded-point-orbit theorem is complete. See
`BOUNDED_POINT_PROOF.md` for the proof and `VERIFICATION.md` for the checks.
The entire theorem has no simple-connectivity or eventual-injectivity
hypothesis. These properties are derived for auxiliary trapped components
and their discs. The local Challenge theorem retains its existing scope.

## Replacing the metric bundle by uniformisation and area

Available proved tools include:

- Mathlib's IsCoveringMap and IsCoveringMapOn, with continuous unique lifting.
- HolomorphicLifting.exists_holomorphic_covering_lift (in namespace AreaDeficit).
- TauCeti.pseudoHyperbolicExpr_map_eq and the Moebius invariance results in
  TauCeti/Analysis/Complex/Conformal/SchwarzPick/Isometry.lean.
- TauCeti.exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv in
  TauCeti/Analysis/Complex/Conformal/UnitDisc/Automorphism/Classification.lean.
- The curvature -1 disc density and curvature equation in BoundedWanderingDomains/DiscMetric.lean,
  together with the conformal Laplacian calculations in BoundedWanderingDomains/ConformalLaplacian.lean.

The intended classical input is existence of a holomorphic universal covering
p : D -> C minus P for each finite P with at least two points, plus the total
area formula for its descended metric. The source disc is simply connected;
surjectivity onto C minus P must be included explicitly with the covering map.

Define the target density by rho(p(w)) = 2 / ((1 - |w|^2) |p'(w)|).
To replace the current input bundle, formalise independence of the chosen
lift w, using covering lifts and disc-automorphism invariance; construct local
inverse branches; prove smoothness and curvature from the pullback identity;
lift arbitrary holomorphic disc maps to prove Schwarz; and recenter the
cover to obtain extremal discs. The area formula is the remaining classical
assumption. This construction has not yet been completed here, so the existing
ClassicalHyperbolicMetrics hypothesis has not been relabelled as uniformisation.

These are development obligations, not new axioms or hypotheses hidden in the
proved Solution. All existing curvature conventions remain -1.
