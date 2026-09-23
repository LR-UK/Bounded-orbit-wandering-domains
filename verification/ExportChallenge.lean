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
  let definitions : List Name := [`ComplexDynamics.IsNormalSequenceOn, `ComplexDynamics.RiemannSphere, `ComplexDynamics.riemannSphereUniformSpace, `ComplexDynamics.sphericalIterate, `ComplexDynamics.fatouSet, `ComplexDynamics.IsFatouComponent, `BoundedWanderingDomains.ClassicalHyperbolicMetrics, `BoundedWanderingDomains.trappedInterior, `BoundedWanderingDomains.EventuallyInjectiveOnLargeDiscs]
  let theorems : List Name := [`BoundedWanderingDomains.no_local_bounded_wandering_domains, `BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire]
  for name in definitions ++ theorems do
    let some ci := env.find? name | throwError "Missing declaration {name}"
    let mut fields := [
      ("name", Json.str name.toString),
      ("universes", Json.str (reprStr ci.levelParams)),
      ("type", Json.str (reprStr (canonicalExpr ci.type)))]
    if definitions.contains name then
      let some value := ci.value? | throwError "Missing definition body {name}"
      fields := fields ++ [("value", Json.str (reprStr (canonicalExpr value)))]
    logInfo s!"PALOMAR_DECL {(Json.mkObj fields).compress}"
