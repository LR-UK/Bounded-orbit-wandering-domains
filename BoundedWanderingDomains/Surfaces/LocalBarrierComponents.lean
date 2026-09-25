/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.BarrierComponents
import BoundedWanderingDomains.Surfaces.LocalMapTotalization

/-! # Barrier components for open-source local maps -/

open Set Function

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
  [T2Space X] [LocallyCompactSpace X]

/-- A closed backward-invariant barrier disjoint from the normality locus has
the same complementary components as the normality locus, once normality is
known to equal the interior trapped set. -/
theorem barrier_component_eq_omega_component
    (f : LocalMap X) (hf : Continuous f.map) {A : Set X}
    (hA : IsClosed A) (hfront : frontier (f.source : Set X) ⊆ A)
    (hback : ∀ x : f.source, f.map x ∈ A → (x : X) ∈ A)
    (homega : f.omega = interior f.trapped)
    (hdis : Disjoint A f.omega) {x : X} (hx : x ∈ f.omega) :
    connectedComponentIn Aᶜ x = connectedComponentIn f.omega x := by
  have hlocalback : (f.source : Set X) ∩ f.totalize ⁻¹' A ⊆ A := by
    rintro y ⟨hy, hfy⟩
    apply hback ⟨y, hy⟩
    change f.totalize y ∈ A at hfy
    rwa [f.totalize_eq hy] at hfy
  have havoid : interior (AreaDeficit.trappedSet f.totalize f.source) ⊆ Aᶜ := by
    rw [f.trappedSet_totalize_eq_trapped, ← homega]
    exact fun y hy hyA => Set.disjoint_left.mp hdis hyA hy
  have hxint : x ∈ interior (AreaDeficit.trappedSet f.totalize f.source) := by
    rwa [f.trappedSet_totalize_eq_trapped, ← homega]
  have h := AreaDeficit.barrier_component_eq_trapped_component
    f.source.isOpen hA (f.continuousOn_totalize hf) hfront hlocalback
      havoid hxint
  rwa [f.trappedSet_totalize_eq_trapped, ← homega] at h

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.barrier_component_eq_omega_component
