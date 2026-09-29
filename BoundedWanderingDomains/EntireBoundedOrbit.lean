module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import Mathlib.Analysis.CStarAlgebra.Classes
public import BoundedWanderingDomains.EntireSurfaceModel
public import BoundedWanderingDomains.Surfaces.SurfaceOrbitEscape

@[expose] public section

open Set Metric Function Filter
open scoped Topology

-- Retain the instance expression used in the original statement.
section
attribute [local instance] instCommCStarAlgebraComplex

namespace BoundedWanderingDomains

/-- An entire transcendental function has no wandering Fatou component
containing a point with bounded orbit. -/
theorem no_bounded_wandering_domains_transcendental_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  intro hdis
  have hnonconst : ¬ ∃ c, ∀ z, f z = c := by
    rintro ⟨c, hc⟩
    exact htrans ⟨Polynomial.C c, fun z => by simpa using hc z⟩
  have hwand := MeromorphicDynamics.surfaceModel_isWanderingComponent_of_fatouComponents
    (fun n => MeromorphicDynamics.isFatouComponent_of_entire hf (hU n)) hforward hdis
  let K0 : Set ℂ := closure (range fun n : ℕ => (f^[n]) z)
  let K : Set (OnePoint ℂ) := MeromorphicDynamics.finiteImage K0
  have hK : IsCompact K := hbounded.isCompact_closure.image OnePoint.continuous_coe
  obtain ⟨n, hn⟩ := SurfaceDynamics.noCompactWanderingOrbitClaim
    (MeromorphicDynamics.surfaceModel f)
    (MeromorphicDynamics.surfaceModel_isOpenHolomorphic_of_entire hf hnonconst)
    (MeromorphicDynamics.finiteImage (U 0)) hwand (z : OnePoint ℂ) ⟨z, hz, rfl⟩ K hK
    (by rintro _ ⟨w, _, rfl⟩; exact MeromorphicDynamics.coe_mem_finiteSphereOpens w)
  apply hn
  rw [MeromorphicDynamics.surfaceModel_compactifiedIterate_coe_of_poleAvoiding f n
    (show z ∈ MeromorphicDynamics.poleAvoidingSet f from fun n => hf.analyticAt _)]
  exact ⟨((f^[n]) z : OnePoint ℂ),
    ⟨(f^[n]) z, subset_closure (mem_range_self n), rfl⟩, rfl⟩

end BoundedWanderingDomains

end
