module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.OpenAmbientRegularValues
public import BoundedWanderingDomains.Surfaces.LocalMapSubsurface

@[expose] public section

/-! # Full inverse components and their obstructions in an open ambient surface -/

open Set Function Topology

namespace SurfaceDynamics

def ambientOpen {X : Type*} [TopologicalSpace X]
    (O : TopologicalSpace.Opens X) (D : TopologicalSpace.Opens O) : TopologicalSpace.Opens X :=
  ⟨Subtype.val '' (D : Set O), O.isOpen.isOpenMap_subtype_val _ D.isOpen⟩

namespace LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem inverseComponentSource_restrictAmbient_image
    (f : LocalMap X) (hf : Continuous f.map) (O : TopologicalSpace.Opens X)
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O)
    (hg : Continuous (f.restrictAmbient O hsource hmap).map)
    (D : TopologicalSpace.Opens O)
    (a : (f.restrictAmbient O hsource hmap).source)
    (ha : (f.restrictAmbient O hsource hmap).map a ∈ D) :
    Subtype.val '' ((f.restrictAmbient O hsource hmap).inverseComponentSource hg D a : Set O) =
      (f.inverseComponentSource hf (ambientOpen O D)
        ((f.restrictAmbientSourceHomeomorph O hsource hmap) a) : Set X) := by
  let g := f.restrictAmbient O hsource hmap
  let e := f.restrictAmbientSourceHomeomorph O hsource hmap
  have hpreimage : e '' (g.map ⁻¹' (D : Set O)) = f.map ⁻¹' (ambientOpen O D : Set X) := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨g.map v, hv, rfl⟩
    · rintro ⟨y, hy, hyu⟩
      refine ⟨e.symm u, ?_, e.apply_symm_apply u⟩
      have he : g.map (e.symm u) = y := Subtype.ext hyu.symm
      change g.map (e.symm u) ∈ D
      rwa [he]
  have heq := e.image_connectedComponentIn (s := g.map ⁻¹' (D : Set O)) (x := a) ha
  rw [hpreimage] at heq
  change Subtype.val '' ((Subtype.val : g.source → O) ''
      connectedComponentIn (g.map ⁻¹' (D : Set O)) a) =
    (Subtype.val : f.source → X) ''
      connectedComponentIn (f.map ⁻¹' (ambientOpen O D : Set X)) (e a)
  rw [← heq, ← image_comp, ← image_comp]
  rfl

theorem componentSingularValues_restrictAmbient_subset
    (f : LocalMap X) (hf : Continuous f.map) (O : TopologicalSpace.Opens X)
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O)
    (hg : Continuous (f.restrictAmbient O hsource hmap).map)
    (D : TopologicalSpace.Opens O)
    (a : (f.restrictAmbient O hsource hmap).source)
    (ha : (f.restrictAmbient O hsource hmap).map a ∈ D) :
    Subtype.val '' (f.restrictAmbient O hsource hmap).componentSingularValues hg D a ⊆
      f.componentSingularValues hf (ambientOpen O D)
        ((f.restrictAmbientSourceHomeomorph O hsource hmap) a) := by
  let g := f.restrictAmbient O hsource hmap
  let g₁ := g.inverseComponentMap hg D a
  let g₂ := f.inverseComponentMap hf (ambientOpen O D)
    ((f.restrictAmbientSourceHomeomorph O hsource hmap) a)
  have hsourceEq : Subtype.val '' (g₁.source : Set O) = (g₂.source : Set X) :=
    f.inverseComponentSource_restrictAmbient_image hf O hsource hmap hg D a ha
  let e : g₁.source ≃ₜ g₂.source :=
    (IsEmbedding.subtypeVal.homeomorphImage (g₁.source : Set O)).trans
      (Homeomorph.setCongr hsourceEq)
  have hcomm : ∀ u, (g₁.map u : X) = g₂.map (e u) := fun _ => rfl
  have hreg := regularValues_into_open_ambient_of_source_homeomorph O g₂ g₁ e hcomm
  have hrange : Subtype.val '' range g₁.map = range g₂.map := by
    ext y
    constructor
    · rintro ⟨b, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, (hcomm u).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨g₁.map (e.symm v), mem_range_self _,
        (hcomm _).trans (congrArg g₂.map (e.apply_symm_apply v))⟩
  rintro y ⟨b, hb, rfl⟩
  have hbcl : (b : X) ∈ closure (range g₂.map) := by
    rw [← hrange]
    exact mem_closure_image continuous_subtype_val.continuousAt hb.1.2
  exact ⟨⟨fun hr => hb.1.1 (hreg hr), hbcl⟩, ⟨b, hb.2, rfl⟩⟩

end LocalMap
end SurfaceDynamics
