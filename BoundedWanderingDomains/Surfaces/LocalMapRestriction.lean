/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalDynamics
import BoundedWanderingDomains.Surfaces.PlaneReading
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

/-! # Restricting a local surface map to a smaller open source -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics
namespace LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- Restrict the source of a local map to a smaller open set. -/
def restrictSource (f : LocalMap X) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) : LocalMap X where
  source := V
  map := fun x => f.map ⟨x, hV x.property⟩

@[simp] theorem restrictSource_source (f : LocalMap X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source) :
    (f.restrictSource V hV).source = V := rfl

@[simp] theorem restrictSource_map (f : LocalMap X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (x : V) :
    (f.restrictSource V hV).map x = f.map ⟨x, hV x.property⟩ := rfl

/-- Openness and holomorphicity pass to a restriction of the open source. -/
theorem isOpenHolomorphic_restrictSource (f : LocalMap X)
    (hf : IsOpenHolomorphic f) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) :
    IsOpenHolomorphic (f.restrictSource V hV) := by
  let i : V → f.source := fun x => ⟨x, hV x.property⟩
  have hiopen : IsOpenMap i := by
    exact V.isOpen.isOpenMap_subtype_val.subtype_mk
      (fun x : V => hV x.property)
  have hidiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i := by
    apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff
      f.source i).mp
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : V → X)
    exact AreaDeficit.Surfaces.mdifferentiable_subtype_val V
  exact ⟨hf.1.comp hiopen, hf.2.comp hidiff⟩

end LocalMap
end SurfaceDynamics

#print axioms SurfaceDynamics.LocalMap.isOpenHolomorphic_restrictSource
