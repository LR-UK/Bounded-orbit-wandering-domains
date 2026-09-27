/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactOrbitNormal
import BoundedWanderingDomains.Surfaces.LocalMapRestriction

/-! # Normality for a relatively compact restricted source -/

open Set Function
open Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

/-- On a relatively compact working domain contained in a disc-covered open
subsurface, every interior trapped point is a normal point. -/
theorem omega_restrictSource_eq_interior_trapped
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O V : TopologicalSpace.Opens X) (p : DiscCover O)
    (hVsource : (V : Set X) ⊆ f.source)
    (hVcompact : IsCompact (closure (V : Set X)))
    (hVO : closure (V : Set X) ⊆ O) :
    (f.restrictSource V hVsource).omega =
      interior (f.restrictSource V hVsource).trapped := by
  let g := f.restrictSource V hVsource
  apply Set.Subset.antisymm
  · exact g.omega_subset_trapped_interior
  · intro x hx
    let W : TopologicalSpace.Opens X :=
      ⟨interior g.trapped, isOpen_interior⟩
    have hW : (W : Set X) ⊆ g.trapped := interior_subset
    have hxW : x ∈ W := hx
    let C : Set O := Subtype.val ⁻¹' closure (V : Set X)
    have hC : IsCompact C := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      rw [image_preimage_eq_inter_range]
      convert hVcompact using 1
      apply inter_eq_left.mpr
      intro y hy
      exact ⟨⟨y, hVO hy⟩, rfl⟩
    have horbitV (n : ℕ) (y : W) : g.orbitOn W hW n y ∈ V := by
      exact g.orbit_mem_source n ⟨y, hW y.property⟩
    have horbitO (n : ℕ) (y : W) : g.orbitOn W hW n y ∈ O :=
      hVO (subset_closure (horbitV n y))
    apply g.mem_omega_of_compact_orbits_in_subsurface
      (f.isOpenHolomorphic_restrictSource hf V hVsource) O p W hW horbitO
      ⟨x, hxW⟩ hC
    intro n y
    exact subset_closure (horbitV n y)

end SurfaceDynamics.LocalMap
