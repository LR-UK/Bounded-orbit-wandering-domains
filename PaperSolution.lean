/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GlobalLimitStatements
import BoundedWanderingDomains.MeromorphicNormalityBridge
import BoundedWanderingDomains.Surfaces.DerivedLimitReduction
import BoundedWanderingDomains.Surfaces.CompactLocalAreaAdvance

/-! # Proofs of the revised paper statements

This file is the solution-side entry point for `PaperChallenge.lean`.  Each
declaration repeats its independent challenge type rather than importing the
challenge file.
-/

open Set Function Filter OnePoint
open scoped Topology Manifold

namespace BoundedWanderingDomains

theorem theorem_1_2_entire :
    ∀ {f : ℂ → ℂ} (_hf : Differentiable ℂ f)
      (_htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
      {U : ℕ → Set ℂ} {z : ℂ}
      (_hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
      (_hz : z ∈ U 0) (_hforward : ∀ n, MapsTo f (U n) (U (n+1)))
      (_hdis : Pairwise (fun n m => Disjoint (U n) (U m))),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
        (fun k w => ((f^[φ k]) w : OnePoint ℂ))
        (fun _ => (∞ : OnePoint ℂ)) atTop (U 0) := by
  intro f hf htrans U z hU hz hforward hdis
  exact wandering_orbit_locallyUniform_infty hf htrans hU hz hforward hdis

theorem theorem_1_4 :
    ∀ {f : ℂ → ℂ} (_hf : Differentiable ℂ f)
      (_htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
      {U : ℕ → Set ℂ} {z : ℂ}
      (_hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
      (_hz : z ∈ U 0) (_hforward : ∀ n, MapsTo f (U n) (U (n+1)))
      (_hdis : Pairwise (fun n m => Disjoint (U n) (U m))),
      ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto
          (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) := by
  intro f hf htrans U z hU hz hforward hdis
  exact wandering_orbit_pointwise_spherical_singular_derivedSet
    hf htrans hU hz hforward hdis

end BoundedWanderingDomains

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]
  [MeasurableSpace X] [BorelSpace X]

/-- The exact positive-area statement of Theorem 1.3(2) for every
noncompact Riemann surface. -/
theorem theorem_1_3_positive_area_noncompact [NoncompactSpace X] :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  letI : DecidableEq X := Classical.decEq X
  exact noCompactPositiveAreaWanderingSetClaim_of_noncompact

/-- The exact positive-area statement of Theorem 1.3(2) for every
hyperbolic Riemann surface, including compact ones. -/
theorem theorem_1_3_positive_area_hyperbolic
    (hX : RiemannDynamics.IsHyperbolic X) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  letI : DecidableEq X := Classical.decEq X
  exact noCompactPositiveAreaWanderingSetClaim_of_isHyperbolic hX

end SurfaceDynamics

#print axioms BoundedWanderingDomains.theorem_1_2_entire
#print axioms BoundedWanderingDomains.theorem_1_4
#print axioms SurfaceDynamics.theorem_1_3_positive_area_noncompact
#print axioms SurfaceDynamics.theorem_1_3_positive_area_hyperbolic
