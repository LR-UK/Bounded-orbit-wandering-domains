module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableObstructions
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterConsequences

@[expose] public section

/-! # The open union of inverse components with prescribed finite obstructions -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem inverseComponentSource_eq_of_mem
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X)
    (a b : f.source) (hb : (b : X) ∈ f.inverseComponentSource hf D a) :
    f.inverseComponentSource hf D a = f.inverseComponentSource hf D b := by
  obtain ⟨v, hv, hvb⟩ := hb
  have he : v = b := Subtype.ext hvb
  subst v
  apply TopologicalSpace.Opens.ext
  change (Subtype.val : f.source → X) '' connectedComponentIn (f.map ⁻¹' (D : Set X)) a =
    (Subtype.val : f.source → X) '' connectedComponentIn (f.map ⁻¹' (D : Set X)) b
  rw [connectedComponentIn_eq hv]

def finiteObstructionSource
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X) (E : Set X) :
    TopologicalSpace.Opens X :=
  ⟨⋃ (a : f.source) (_ : f.map a ∈ D ∧ f.componentSingularValues hf D a ⊆ E),
      (f.inverseComponentSource hf D a : Set X),
    isOpen_iUnion (fun a => isOpen_iUnion (fun _ =>
      (f.inverseComponentSource hf D a).isOpen))⟩

theorem finiteObstructionSource_subset
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X) (E : Set X) :
    (f.finiteObstructionSource hf D E : Set X) ⊆ f.source := by
  intro x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  obtain ⟨_, ha⟩ := mem_iUnion.mp ha
  exact f.inverseComponentSource_subset hf D a ha

theorem mem_finiteObstructionSource_iff
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X) (E : Set X)
    (b : f.source) :
    (b : X) ∈ f.finiteObstructionSource hf D E ↔
      f.map b ∈ D ∧ f.componentSingularValues hf D b ⊆ E := by
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := mem_iUnion.mp hb
    obtain ⟨haD, hbC⟩ := mem_iUnion.mp ha
    have hsource := f.inverseComponentSource_eq_of_mem hf D a b hbC
    have hsing := f.componentSingularValues_eq_of_inverseComponentSource_eq hf D a b
      (congrArg (fun V : TopologicalSpace.Opens X => (V : Set X)) hsource)
    exact ⟨f.map_mem_of_mem_inverseComponentSource hf D a b hbC, hsing ▸ haD.2⟩
  · intro hb
    exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hb, b, mem_connectedComponentIn hb.1, rfl⟩⟩

end SurfaceDynamics.LocalMap
