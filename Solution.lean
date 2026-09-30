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
public import BoundedWanderingDomains.MeromorphicDerivedSingular
public import BoundedWanderingDomains.Surfaces.SingularEncounters.Results
public import BoundedWanderingDomains.Surfaces.SurfaceOrbitEscape
public import BoundedWanderingDomains.Surfaces.SurfaceDerivedLimits
public import BoundedWanderingDomains.Surfaces.SurfacePositiveArea

@[expose] public section

/-! # Proofs of the revised paper statements

This file is the solution-side entry point for all nineteen theorems in
`Challenge.lean`. Seven theorem declarations appear below; twelve are already
proved in the publicly imported library modules. Importing `Solution` exposes
all nineteen. The proof library never imports the independent challenge.

The twelve imported theorem declarations are located as follows:
* `EntireBoundedOrbit`: the original entire-function bounded-orbit theorem,
  with its statement unchanged.
* `NoWanderingCorollaries`: the four no-wandering corollaries for class S entire
  and meromorphic functions, compact-surface self-maps, and rational maps.
* `Surfaces.FiniteType`: the finite-type no-wandering theorem.
* `Surfaces.AlmostEverywhere.Results`: compact wandering-orbit accumulation,
  almost-everywhere source escape, the positive-area exclusion away from the
  derived set, and the almost-everywhere escape-or-derived-set alternative.
* `Surfaces.SingularEncounters.Results`: the two combined singular-encounter
  theorems for wandering domains and almost every point of a wandering set.

The declaration and axiom audits check every selected theorem, including those
imported from these modules, against the independent challenge statement.
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


end SurfaceDynamics

namespace MeromorphicDynamics

/-- Every meromorphic wandering orbit accumulates on the spherical derived
singular set. The compact sphere target rules out ambient escape. -/
theorem wandering_orbit_accumulates_on_derived_singular_values
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ) (htrans : ¬ IsRationalMeromorphic f)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, IsFatouComponent f (U n)) (hz : z ∈ U 0)
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m : ℕ => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (singularValues f), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (((f^[φ n]) z : ℂ) : OnePoint ℂ)) atTop (𝓝 a) := by
  exact wandering_derived_singular_limit hf htrans hU hforward hdis hz

end MeromorphicDynamics
