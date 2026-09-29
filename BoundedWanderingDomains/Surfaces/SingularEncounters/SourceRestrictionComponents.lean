module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ComponentEmbedding

@[expose] public section

/-! # Full inverse components are unchanged when no preimages are removed -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

theorem regularValues_eq_of_source_homeomorph
    {X : Type*} [TopologicalSpace X] (f g : LocalMap X)
    (e : g.source ≃ₜ f.source) (hmap : g.map = f.map ∘ e) :
    g.regularValues = f.regularValues := by
  have hrange : range g.map = range f.map := by
    rw [hmap, range_comp, e.surjective.range_eq, image_univ]
  have hfmap : f.map = g.map ∘ e.symm := by
    funext x
    exact ((congrFun hmap (e.symm x)).trans (congrArg f.map (e.apply_symm_apply x))).symm
  ext y
  constructor
  · rintro ⟨A, hA, hyA, hAr, hAc⟩
    refine ⟨A, hA, hyA, hrange ▸ hAr, ?_⟩
    rw [hfmap]
    exact hAc.comp_homeomorph e.symm
  · rintro ⟨A, hA, hyA, hAr, hAc⟩
    refine ⟨A, hA, hyA, hrange.symm ▸ hAr, ?_⟩
    rw [hmap]
    exact hAc.comp_homeomorph e

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem inverseComponentSource_restrictSource_eq
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (D : TopologicalSpace.Opens X)
    (hpre : ∀ x : f.source, f.map x ∈ D → (x : X) ∈ V)
    (a : (f.restrictSource V hV).source) (ha : (f.restrictSource V hV).map a ∈ D) :
    (f.restrictSource V hV).inverseComponentSource
      (hf.comp (continuous_subtype_val.subtype_mk _)) D a =
      f.inverseComponentSource hf D ⟨(a : X), hV a.2⟩ := by
  let r := f.restrictSource V hV
  let j : r.source → f.source := fun x => ⟨x, hV x.2⟩
  have hj : IsEmbedding j :=
    IsEmbedding.of_comp (by fun_prop) continuous_subtype_val IsEmbedding.subtypeVal
  have hpreimage : j '' (r.map ⁻¹' (D : Set X)) = f.map ⁻¹' (D : Set X) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x, hpre x hx⟩, hx, rfl⟩
  have heq := embedding_image_connectedComponentIn hj (r.map ⁻¹' (D : Set X)) ha
  rw [hpreimage] at heq
  apply TopologicalSpace.Opens.ext
  change (Subtype.val : r.source → X) '' connectedComponentIn (r.map ⁻¹' (D : Set X)) a =
    (Subtype.val : f.source → X) '' connectedComponentIn (f.map ⁻¹' (D : Set X)) (j a)
  rw [← heq, ← image_comp]
  rfl

theorem componentSingularValues_restrictSource_eq
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (D : TopologicalSpace.Opens X)
    (hpre : ∀ x : f.source, f.map x ∈ D → (x : X) ∈ V)
    (a : (f.restrictSource V hV).source) (ha : (f.restrictSource V hV).map a ∈ D) :
    (f.restrictSource V hV).componentSingularValues
      (hf.comp (continuous_subtype_val.subtype_mk _)) D a =
      f.componentSingularValues hf D ⟨(a : X), hV a.2⟩ := by
  let r := f.restrictSource V hV
  let hrc := hf.comp (continuous_subtype_val.subtype_mk (fun x : V => hV x.2))
  let g₁ := r.inverseComponentMap hrc D a
  let g₂ := f.inverseComponentMap hf D ⟨(a : X), hV a.2⟩
  have hsource : (g₁.source : Set X) = g₂.source :=
    congrArg (fun A : TopologicalSpace.Opens X => (A : Set X))
      (f.inverseComponentSource_restrictSource_eq hf V hV D hpre a ha)
  let e : g₁.source ≃ₜ g₂.source := Homeomorph.setCongr hsource
  have he : g₁.map = g₂.map ∘ e := by
    funext x
    rfl
  have hreg := regularValues_eq_of_source_homeomorph g₂ g₁ e he
  have hrange : range g₁.map = range g₂.map := by
    rw [he, range_comp, e.surjective.range_eq, image_univ]
  change g₁.singularValues ∩ closure (range g₁.map) ∩ (D : Set X) =
    g₂.singularValues ∩ closure (range g₂.map) ∩ (D : Set X)
  rw [singularValues, singularValues, hreg, hrange]

end SurfaceDynamics.LocalMap
