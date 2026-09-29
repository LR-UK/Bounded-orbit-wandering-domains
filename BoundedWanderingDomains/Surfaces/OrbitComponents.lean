module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.OmegaDynamics

@[expose] public section

/-! # Forward maps between the components containing a trapped orbit -/

open Set Function
open scoped Manifold

namespace SurfaceDynamics.LocalMap

theorem component_orbit_forward
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [T2Space X] [LocallyCompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (U : ℕ → Set X)
    (hU : ∀ n, f.IsComponent (U n)) (z : f.trapped)
    (hzU : ∀ n, f.orbit n z ∈ U n) :
    (∀ n, U n ⊆ f.source) ∧ ∀ n, MapsTo f.totalize (U n) (U (n + 1)) := by
  have hUeq : ∀ n, U n = connectedComponentIn f.omega (f.orbit n z) := by
    intro n
    obtain ⟨x, _, hx⟩ := hU n
    exact hx.trans (connectedComponentIn_eq (hx ▸ hzU n))
  have hUomega : ∀ n, U n ⊆ f.omega := fun n =>
    hUeq n ▸ connectedComponentIn_subset _ _
  have hUs : ∀ n, U n ⊆ f.source := fun n => (hUomega n).trans f.omega_subset_source
  refine ⟨hUs, ?_⟩
  intro n
  have hc : IsPreconnected (f.totalize '' U n) := by
    have hUc : IsPreconnected (U n) := hUeq n ▸ isPreconnected_connectedComponentIn
    exact hUc.image f.totalize ((f.continuousOn_totalize hf.2.continuous).mono (hUs n))
  have hnext : f.totalize (f.orbit n z) = f.orbit (n + 1) z := by
    rw [f.totalize_eq (f.orbit_mem_source n z), f.orbit_succ]
  have hb : f.orbit (n + 1) z ∈ f.totalize '' U n := ⟨f.orbit n z, hzU n, hnext⟩
  have hsub : f.totalize '' U n ⊆ f.omega := by
    rintro y ⟨x, hx, rfl⟩
    exact f.totalize_mapsTo_omega hf (hUomega n hx)
  apply mapsTo_iff_image_subset.mpr
  rw [hUeq (n + 1)]
  exact hc.subset_connectedComponentIn hb hsub

end SurfaceDynamics.LocalMap
