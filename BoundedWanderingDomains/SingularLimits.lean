/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.ClassBWanderingConnectivity
import BoundedWanderingDomains.SimplyConnectedSingularLimits
import BoundedWanderingDomains.SphericalSingularUnbounded
import BoundedWanderingDomains.SingularLimitConsequences

/-! # Derived singular accumulation for every entire wandering orbit

The unbounded-singular-set case follows from the bounded-orbit theorem.
For bounded singular values, tract simple connectivity fills the wandering
components, and the finite backward-orbit area argument applies. There is
no simple-connectivity or periodic-point hypothesis in the final result.
-/

open Set Filter Function OnePoint
open scoped Topology

namespace BoundedWanderingDomains

/-- Every wandering point of a transcendental entire function has a spherical
subsequential limit in the derived set of its finite singular values. -/
theorem wandering_orbit_subsequence_singularDerivedSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ sphericalDerivedSet (ComplexDynamics.singularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) := by
  by_cases hB : ComplexDynamics.MemClassB f
  · have hft : FunctionTheory.IsTranscendentalEntire f :=
      ⟨hf, fun ⟨p, hp⟩ => htrans ⟨p, fun z => congrFun hp z⟩⟩
    have hsc : ∀ n, IsSimplyConnected (U n) := by
      intro n
      have hs := AreaDeficit.classB_wandering_component_simplyConnected hft hB
        (U := fun m => U (n+m)) (fun m => hU (n+m))
        (fun m => by simpa only [Nat.add_assoc] using hforward (n+m))
        (fun i j hij => hdis (by omega : n+i ≠ n+j))
      simpa using hs
    exact wandering_orbit_subsequence_singularDerivedSet_of_simplyConnected
      hf hU hz hforward hdis hsc
  · exact wandering_orbit_subsequence_of_unbounded_set hf htrans hU hz hforward hdis
      (ComplexDynamics.singularValues f) hB

/-- The same result stated entirely on the sphere, with infinity included
in the singular set. -/
theorem wandering_orbit_subsequence_spherical_singular_derivedSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) := by
  rw [ComplexDynamics.derivedSet_sphericalSingularValues]
  exact wandering_orbit_subsequence_singularDerivedSet hf htrans hU hz hforward hdis

end BoundedWanderingDomains
