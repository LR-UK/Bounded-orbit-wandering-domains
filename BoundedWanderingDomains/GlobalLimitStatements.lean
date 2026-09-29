module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.EntireBoundedOrbit
public import BoundedWanderingDomains.EntireDerivedSingular
public import BoundedWanderingDomains.MeromorphicEscape

@[expose] public section

/-! # Entire-function conclusions derived from the combined surface theorem -/

open Set Function Filter OnePoint
open scoped Topology

namespace BoundedWanderingDomains

theorem wandering_orbit_locallyUniform_infty
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
      (fun k w => ((f^[φ k]) w : OnePoint ℂ))
      (fun _ => (∞ : OnePoint ℂ)) atTop (U 0) := by
  apply MeromorphicDynamics.wandering_orbit_locallyUniform_infty_of_unbounded
    (fun n => MeromorphicDynamics.isFatouComponent_of_entire hf (hU n)) hz hforward hdis
  intro hb
  exact no_bounded_wandering_domains_transcendental_entire hf htrans hU hz hforward hb hdis

theorem wandering_orbit_pointwise_spherical_singular_derivedSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto
        (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) :=
  entire_wandering_derived_singular_limit hf htrans hU hforward hdis hz

end BoundedWanderingDomains
