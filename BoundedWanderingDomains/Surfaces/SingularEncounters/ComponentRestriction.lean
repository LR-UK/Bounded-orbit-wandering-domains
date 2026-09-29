module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SourceRestrictionComponents

@[expose] public section

/-! # Restricting a source without changing a particular inverse component -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem inverseComponentSource_restrictSource_eq_of_component_subset
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (D : TopologicalSpace.Opens X)
    (a : (f.restrictSource V hV).source) (ha : (f.restrictSource V hV).map a ∈ D)
    (hC : (f.inverseComponentSource hf D ⟨(a : X), hV a.2⟩ : Set X) ⊆ V) :
    (f.restrictSource V hV).inverseComponentSource
      (hf.comp (continuous_subtype_val.subtype_mk _)) D a =
      f.inverseComponentSource hf D ⟨(a : X), hV a.2⟩ := by
  let r := f.restrictSource V hV
  let j : r.source → f.source := fun x => ⟨x, hV x.2⟩
  have hj : IsEmbedding j :=
    IsEmbedding.of_comp (by fun_prop) continuous_subtype_val IsEmbedding.subtypeVal
  let T := f.map ⁻¹' (D : Set X)
  let S := r.map ⁻¹' (D : Set X)
  have himage : j '' S ⊆ T := by
    rintro u ⟨v, hv, rfl⟩
    exact hv
  have hCimage : connectedComponentIn T (j a) ⊆ j '' S := by
    intro u hu
    have huV : (u : X) ∈ V := hC ⟨u, hu, rfl⟩
    have huD : f.map u ∈ D := connectedComponentIn_subset T (j a) hu
    exact ⟨⟨u, huV⟩, huD, rfl⟩
  have hceq : connectedComponentIn (j '' S) (j a) = connectedComponentIn T (j a) := by
    apply (connectedComponentIn_mono (j a) himage).antisymm
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ha) hCimage
  have heq := (embedding_image_connectedComponentIn hj S ha).trans hceq
  apply TopologicalSpace.Opens.ext
  change (Subtype.val : r.source → X) '' connectedComponentIn S a =
    (Subtype.val : f.source → X) '' connectedComponentIn T (j a)
  rw [← heq, ← image_comp]
  rfl

theorem componentSingularValues_restrictSource_eq_of_component_subset
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (D : TopologicalSpace.Opens X)
    (a : (f.restrictSource V hV).source) (ha : (f.restrictSource V hV).map a ∈ D)
    (hC : (f.inverseComponentSource hf D ⟨(a : X), hV a.2⟩ : Set X) ⊆ V) :
    (f.restrictSource V hV).componentSingularValues
      (hf.comp (continuous_subtype_val.subtype_mk _)) D a =
      f.componentSingularValues hf D ⟨(a : X), hV a.2⟩ := by
  let r := f.restrictSource V hV
  let hrc := hf.comp (continuous_subtype_val.subtype_mk (fun x : V => hV x.2))
  let g₁ := r.inverseComponentMap hrc D a
  let g₂ := f.inverseComponentMap hf D ⟨(a : X), hV a.2⟩
  have hsource : (g₁.source : Set X) = g₂.source :=
    congrArg (fun A : TopologicalSpace.Opens X => (A : Set X))
      (f.inverseComponentSource_restrictSource_eq_of_component_subset hf V hV D a ha hC)
  let e : g₁.source ≃ₜ g₂.source := Homeomorph.setCongr hsource
  have he : g₁.map = g₂.map ∘ e := by funext x; rfl
  have hreg := regularValues_eq_of_source_homeomorph g₂ g₁ e he
  have hrange : range g₁.map = range g₂.map := by
    rw [he, range_comp, e.surjective.range_eq, image_univ]
  change g₁.singularValues ∩ closure (range g₁.map) ∩ (D : Set X) =
    g₂.singularValues ∩ closure (range g₂.map) ∩ (D : Set X)
  rw [singularValues, singularValues, hreg, hrange]

end SurfaceDynamics.LocalMap
