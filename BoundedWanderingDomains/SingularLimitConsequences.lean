/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SimplyConnectedSingularLimits
import BoundedWanderingDomains.SphericalSingularValues

/-! # Non-escape as a consequence of a derived singular limit

This deduction uses the derived-limit conclusion, never a no-escape theorem
as an input. The application currently retains simple connectivity.
-/

open Set Filter Function OnePoint
open scoped Topology

namespace BoundedWanderingDomains

theorem not_tendsto_infty_of_derived_singular_subsequence
    {f : ℂ → ℂ} (hB : ComplexDynamics.MemClassB f) {z : ℕ → ℂ}
    (h : ∃ a ∈ sphericalDerivedSet (ComplexDynamics.singularValues f),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => (z (φ k) : OnePoint ℂ)) atTop (𝓝 a)) :
    ¬ Tendsto (fun n => (z n : OnePoint ℂ)) atTop (𝓝 ∞) := by
  intro hesc
  obtain ⟨a, ha, φ, hφ, hlim⟩ := h
  have he : a = ∞ := tendsto_nhds_unique hlim (hesc.comp hφ.tendsto_atTop)
  exact ((infty_mem_sphericalDerivedSet_iff _).mp (he ▸ ha)) hB

theorem no_escaping_simplyConnected_wandering_orbit_of_classB
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hB : ComplexDynamics.MemClassB f)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hsc : ∀ n, IsSimplyConnected (U n)) :
    ¬ Tendsto (fun n => ((f^[n]) z : OnePoint ℂ)) atTop (𝓝 ∞) :=
  not_tendsto_infty_of_derived_singular_subsequence hB
    (wandering_orbit_subsequence_singularDerivedSet_of_simplyConnected hf hU hz hforward hdis hsc)

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.no_escaping_simplyConnected_wandering_orbit_of_classB
