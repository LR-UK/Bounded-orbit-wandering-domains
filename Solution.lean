module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.Results
public import BoundedWanderingDomains.NoWanderingCorollaries
public import BoundedWanderingDomains.EntireBoundedOrbit
public import BoundedWanderingDomains.GlobalLimitStatements
public import BoundedWanderingDomains.MeromorphicEscape
public import BoundedWanderingDomains.Surfaces.SurfaceOrbitEscape
public import BoundedWanderingDomains.Surfaces.SurfaceDerivedLimits
public import BoundedWanderingDomains.Surfaces.SurfacePositiveArea

@[expose] public section

/-! # Proofs of the revised paper statements

This file is the solution-side entry point for `Challenge.lean`.  Each
declaration repeats its independent challenge type rather than importing the
challenge file. The original entire-function bounded-orbit statement is
exposed unchanged by the shared EntireBoundedOrbit module.
-/

open Set Function Filter OnePoint
open scoped Topology Manifold

namespace BoundedWanderingDomains

def wandering_orbit_locallyUniform_inftyClaim : Prop :=
    ∀ {f : ℂ → ℂ} (_hf : Differentiable ℂ f)
      (_htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
      {U : ℕ → Set ℂ} {z : ℂ}
      (_hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
      (_hz : z ∈ U 0) (_hforward : ∀ n, MapsTo f (U n) (U (n+1)))
      (_hdis : Pairwise (fun n m => Disjoint (U n) (U m))),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
        (fun k w => ((f^[φ k]) w : OnePoint ℂ))
        (fun _ => (∞ : OnePoint ℂ)) atTop (U 0)

theorem wandering_domain_has_locally_uniform_escaping_subsequence : wandering_orbit_locallyUniform_inftyClaim := by
  intro f hf htrans U z hU hz hforward hdis
  exact wandering_orbit_locallyUniform_infty hf htrans hU hz hforward hdis

def wandering_orbit_pointwise_spherical_singular_derivedSetClaim : Prop :=
    ∀ {f : ℂ → ℂ} (_hf : Differentiable ℂ f)
      (_htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
      {U : ℕ → Set ℂ} {z : ℂ}
      (_hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
      (_hz : z ∈ U 0) (_hforward : ∀ n, MapsTo f (U n) (U (n+1)))
      (_hdis : Pairwise (fun n m => Disjoint (U n) (U m))),
      ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto
          (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a)

theorem wandering_orbit_accumulates_on_derived_singular_values : wandering_orbit_pointwise_spherical_singular_derivedSetClaim := by
  intro f hf htrans U z hU hz hforward hdis
  exact wandering_orbit_pointwise_spherical_singular_derivedSet
    hf htrans hU hz hforward hdis

end BoundedWanderingDomains

namespace MeromorphicDynamics

def WanderingLocallyUniformInfinityClaim : Prop :=
    ∀ {f : ℂ → ℂ}, MeromorphicNFOn f univ →
      ¬ IsRationalMeromorphic f →
      ∀ {U : ℕ → Set ℂ} {z : ℂ},
        (∀ n, IsFatouComponent f (U n)) → z ∈ U 0 →
        (∀ n, MapsTo f (U n) (U (n + 1))) →
        Pairwise (fun n m => Disjoint (U n) (U m)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
          (fun k w => ((f^[φ k]) w : OnePoint ℂ))
          (fun _ => (∞ : OnePoint ℂ)) atTop (U 0)

theorem wandering_domain_has_locally_uniform_escaping_subsequence : WanderingLocallyUniformInfinityClaim :=
  wanderingLocallyUniformInfinityClaim_of_surface_theorem
    SurfaceDynamics.noCompactWanderingOrbitClaim

end MeromorphicDynamics

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

theorem wandering_component_orbit_not_compactly_contained : NoCompactWanderingOrbitClaim (X := X) :=
  noCompactWanderingOrbitClaim

theorem wandering_orbit_has_escaping_or_derived_singular_subsequence : WanderingDerivedSingularLimitClaim (X := X) :=
  wanderingDerivedSingularLimitClaim

variable
  [MeasurableSpace X] [BorelSpace X]

theorem positive_area_wandering_saturation_not_compactly_contained : NoCompactPositiveAreaWanderingSetClaim (X := X) :=
  noCompactPositiveAreaWanderingSetClaim

/-- The exact positive-area statement of the positive-area wandering-set theorem for every
noncompact Riemann surface. -/
theorem positive_area_wandering_saturation_not_compactly_contained_noncompact [NoncompactSpace X] :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  let : DecidableEq X := Classical.decEq X
  exact noCompactPositiveAreaWanderingSetClaim_of_noncompact

/-- The exact positive-area statement of the positive-area wandering-set theorem for every
hyperbolic Riemann surface, including compact ones. -/
theorem positive_area_wandering_saturation_not_compactly_contained_hyperbolic
    (hX : RiemannDynamics.IsHyperbolic X) :
    NoCompactPositiveAreaWanderingSetClaim (X := X) := by
  let : DecidableEq X := Classical.decEq X
  exact noCompactPositiveAreaWanderingSetClaim_of_isHyperbolic hX

end SurfaceDynamics
