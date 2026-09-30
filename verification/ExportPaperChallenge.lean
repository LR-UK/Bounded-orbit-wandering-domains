module

public import Challenge
public import Lean

@[expose] public section

/- Erase only bound-variable display names and nonsemantic metadata.
   Bound occurrences are de Bruijn indices; constants and their names stay intact. -/
private partial def canonicalExpr : Lean.Expr → Lean.Expr
  | .app f a => .app (canonicalExpr f) (canonicalExpr a)
  | .lam _ t b bi => .lam .anonymous (canonicalExpr t) (canonicalExpr b) bi
  | .forallE _ t b bi => .forallE .anonymous (canonicalExpr t) (canonicalExpr b) bi
  | .letE _ t v b nd =>
      .letE .anonymous (canonicalExpr t) (canonicalExpr v) (canonicalExpr b) nd
  | .mdata _ e => canonicalExpr e
  | .proj n i e => .proj n i (canonicalExpr e)
  | e => e

/- A local syntactic comparison aid; this is not Palomar Comparator. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- Match Comparator's target-kind contract, independently of the broader
  -- supporting-declaration comparison below (which also checks structures).
  let configText ← liftIO <| IO.FS.readFile "comparator.json"
  let config ← ofExcept <| Json.parse configText
  let definitionTargets ← ofExcept <| config.getObjValAs? (Array String) "definition_names"
  for target in definitionTargets do
    let name := target.toName
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Comparator definition_names entry is not a definition: {name}"
  let theoremTargets ← ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  for target in theoremTargets do
    let name := target.toName
    match env.find? name with
    | some (.thmInfo _) | some (.axiomInfo _) => pure ()
    | _ => throwError "Comparator theorem_names entry is not a theorem or axiom: {name}"
  let definitions : List Name := [`ComplexDynamics.IsNormalSequenceOn, `ComplexDynamics.RiemannSphere, `ComplexDynamics.riemannSphereUniformSpace, `ComplexDynamics.sphericalIterate, `ComplexDynamics.fatouSet, `ComplexDynamics.IsFatouComponent, `ComplexDynamics.regularValueSet, `ComplexDynamics.singularValues, `ComplexDynamics.sphericalSingularValues, `SurfaceDynamics.LocalMap.step, `SurfaceDynamics.LocalMap.iterate, `SurfaceDynamics.LocalMap.trapped, `SurfaceDynamics.LocalMap.imageAt, `SurfaceDynamics.LocalMap.compactifiedIterate, `SurfaceDynamics.LocalMap.IsNormalOn, `SurfaceDynamics.LocalMap.omega, `SurfaceDynamics.LocalMap.IsComponent, `SurfaceDynamics.LocalMap.IsWanderingComponent, `SurfaceDynamics.LocalMap.regularValues, `SurfaceDynamics.LocalMap.singularValues, `SurfaceDynamics.IsOpenHolomorphic, `SurfaceDynamics.HasPositiveChartArea, `SurfaceDynamics.LocalMap.saturation, `SurfaceDynamics.LocalMap.InjectiveOnSaturation, `MeromorphicDynamics.IsRationalMeromorphic, `MeromorphicDynamics.poleAvoidingSet, `MeromorphicDynamics.fatouSet, `MeromorphicDynamics.IsFatouComponent, `SurfaceDynamics.LocalMap, `BoundedWanderingDomains.wandering_orbit_locallyUniform_inftyClaim, `BoundedWanderingDomains.wandering_orbit_pointwise_spherical_singular_derivedSetClaim, `MeromorphicDynamics.WanderingLocallyUniformInfinityClaim, `SurfaceDynamics.NoCompactWanderingOrbitClaim, `SurfaceDynamics.NoCompactPositiveAreaWanderingSetClaim, `SurfaceDynamics.WanderingDerivedSingularLimitClaim, `SurfaceDynamics.ChartAlmostEverywhere, `SurfaceDynamics.LocalMap.HasSourceEscapingSubsequence, `SurfaceDynamics.LocalMap.HasEscapingOrDerivedSingularSubsequence, `FunctionTheory.meromorphicSphereValue, `MeromorphicDynamics.regularValues, `MeromorphicDynamics.singularValues, `AreaDeficit.Surfaces.unitDisc, `SurfaceDynamics.EmbeddedDisc, `SurfaceDynamics.EmbeddedDisc.carrier, `SurfaceDynamics.LocalMap.restrictSource, `SurfaceDynamics.LocalMap.totalize, `SurfaceDynamics.LocalMap.inverseComponentSource, `SurfaceDynamics.LocalMap.inverseComponentMap, `SurfaceDynamics.LocalMap.componentSingularValues, `SurfaceDynamics.LocalMap.HasSingularEncounterSequence, `SurfaceDynamics.LocalMap.HasEscapingOrSingularEncounterSequence]
  let theorems : List Name := [`BoundedWanderingDomains.wandering_domain_has_locally_uniform_escaping_subsequence, `MeromorphicDynamics.wandering_domain_has_locally_uniform_escaping_subsequence, `SurfaceDynamics.wandering_component_orbit_not_compactly_contained, `SurfaceDynamics.positive_area_wandering_saturation_not_compactly_contained, `BoundedWanderingDomains.wandering_orbit_accumulates_on_derived_singular_values, `SurfaceDynamics.wandering_orbit_has_escaping_or_derived_singular_subsequence, `BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire, `BoundedWanderingDomains.no_wandering_domains_transcendental_entire_finite_singularValues, `SurfaceDynamics.no_wandering_domains_compact, `SurfaceDynamics.no_wandering_domains_rational, `SurfaceDynamics.compact_wandering_orbit_accumulates_on_derived_singular_values, `SurfaceDynamics.almost_every_wandering_point_has_source_escaping_subsequence, `SurfaceDynamics.positive_area_wandering_saturation_not_compactly_contained_away_from_derived, `SurfaceDynamics.almost_every_wandering_point_has_escaping_or_derived_singular_subsequence, `SurfaceDynamics.no_wandering_domains_finite_type, `MeromorphicDynamics.no_wandering_domains_transcendental_meromorphic_finite_singularValues, `SurfaceDynamics.wandering_domain_has_escaping_or_singular_encounter_sequence, `SurfaceDynamics.almost_every_wandering_point_has_escaping_or_singular_encounter_sequence, `MeromorphicDynamics.wandering_orbit_accumulates_on_derived_singular_values]
  for name in definitions ++ theorems do
    let some ci := env.find? name | throwError "Missing declaration {name}"
    let mut fields := [
      ("name", Json.str name.toString),
      ("universes", Json.str (reprStr ci.levelParams)),
      ("type", Json.str (reprStr (canonicalExpr ci.type)))]
    if definitions.contains name then
      match ci.value? with
      | some value =>
        fields := fields ++ [("value", Json.str (reprStr (canonicalExpr value)))]
      | none =>
        match ci with
        | .inductInfo info =>
          fields := fields ++ [("constructors", Json.str (reprStr info.ctors)),
            ("numParams", toJson info.numParams), ("numIndices", toJson info.numIndices)]
          for ctor in info.ctors do
            let some c := env.find? ctor | throwError "Missing constructor {ctor}"
            fields := fields ++ [(ctor.toString, Json.str (reprStr (canonicalExpr c.type)))]
        | _ => throwError "Missing definition body {name}"
    logInfo s!"PALOMAR_DECL {(Json.mkObj fields).compress}"
