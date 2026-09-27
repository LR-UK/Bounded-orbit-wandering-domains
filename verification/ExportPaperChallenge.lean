import Challenge
import Lean

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
  let definitions : List Name := [`ComplexDynamics.IsNormalSequenceOn, `ComplexDynamics.RiemannSphere, `ComplexDynamics.riemannSphereUniformSpace, `ComplexDynamics.sphericalIterate, `ComplexDynamics.fatouSet, `ComplexDynamics.IsFatouComponent, `ComplexDynamics.regularValueSet, `ComplexDynamics.singularValues, `ComplexDynamics.sphericalSingularValues, `SurfaceDynamics.LocalMap.step, `SurfaceDynamics.LocalMap.iterate, `SurfaceDynamics.LocalMap.trapped, `SurfaceDynamics.LocalMap.imageAt, `SurfaceDynamics.LocalMap.compactifiedIterate, `SurfaceDynamics.LocalMap.IsNormalOn, `SurfaceDynamics.LocalMap.omega, `SurfaceDynamics.LocalMap.IsComponent, `SurfaceDynamics.LocalMap.IsWanderingComponent, `SurfaceDynamics.LocalMap.regularValues, `SurfaceDynamics.LocalMap.singularValues, `SurfaceDynamics.IsOpenHolomorphic, `SurfaceDynamics.HasPositiveChartArea, `SurfaceDynamics.LocalMap.saturation, `SurfaceDynamics.LocalMap.InjectiveOnSaturation, `SurfaceDynamics.LocalMap.HasSimplyConnectedComponentOrbit, `MeromorphicDynamics.IsRationalMeromorphic, `MeromorphicDynamics.poleAvoidingSet, `MeromorphicDynamics.fatouSet, `MeromorphicDynamics.IsFatouComponent, `SurfaceDynamics.LocalMap, `BoundedWanderingDomains.wandering_orbit_locallyUniform_inftyClaim, `BoundedWanderingDomains.wandering_orbit_pointwise_spherical_singular_derivedSetClaim, `MeromorphicDynamics.WanderingLocallyUniformInfinityClaim, `SurfaceDynamics.NoCompactWanderingOrbitClaim, `SurfaceDynamics.NoCompactPositiveAreaWanderingSetClaim, `SurfaceDynamics.WanderingDerivedSingularLimitClaim]
  let theorems : List Name := [`BoundedWanderingDomains.theorem_1_2_entire, `MeromorphicDynamics.theorem_1_2_meromorphic, `SurfaceDynamics.theorem_1_3_orbit, `SurfaceDynamics.theorem_1_3_positive_area, `BoundedWanderingDomains.theorem_1_4, `SurfaceDynamics.theorem_1_5, `BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire, `BoundedWanderingDomains.no_wandering_domains_transcendental_entire_finite_singularValues, `SurfaceDynamics.no_wandering_domains_compact, `SurfaceDynamics.no_wandering_domains_rational]
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
