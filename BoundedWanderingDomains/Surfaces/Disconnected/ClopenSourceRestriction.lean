module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenCovering
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SourceRestrictionComponents

@[expose] public section

/-! # Source restrictions which retain whole source components -/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem inverseComponentSource_restrictSource_clopen_eq
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (hVc : IsClosed ((Subtype.val : f.source → X) ⁻¹' (V : Set X)))
    (D : TopologicalSpace.Opens X)
    (a : (f.restrictSource V hV).source) (ha : (f.restrictSource V hV).map a ∈ D) :
    (f.restrictSource V hV).inverseComponentSource
      (hf.comp (continuous_subtype_val.subtype_mk _)) D a =
      f.inverseComponentSource hf D ⟨(a : X), hV a.2⟩ := by
  let r := f.restrictSource V hV
  let j : r.source → f.source := fun x => ⟨x, hV x.2⟩
  have hj : IsEmbedding j :=
    IsEmbedding.of_comp (by fun_prop) continuous_subtype_val IsEmbedding.subtypeVal
  let S : Set f.source := Subtype.val ⁻¹' (V : Set X)
  have hS : IsClopen S := ⟨hVc, V.isOpen.preimage continuous_subtype_val⟩
  have hpreimage : j '' (r.map ⁻¹' (D : Set X)) = (f.map ⁻¹' (D : Set X)) ∩ S := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.property⟩
    · rintro ⟨hx, hxV⟩
      exact ⟨⟨x, hxV⟩, hx, rfl⟩
  have hcomp : connectedComponentIn ((f.map ⁻¹' (D : Set X)) ∩ S) (j a) =
      connectedComponentIn (f.map ⁻¹' (D : Set X)) (j a) := by
    have ha' : j a ∈ f.map ⁻¹' (D : Set X) := ha
    apply (connectedComponentIn_mono _ inter_subset_left).antisymm
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn ha')
    exact subset_inter (connectedComponentIn_subset _ _)
      ((isPreconnected_connectedComponentIn.subset_connectedComponent (mem_connectedComponentIn ha')).trans
        (hS.connectedComponent_subset a.property))
  have heq := SurfaceDynamics.embedding_image_connectedComponentIn hj (r.map ⁻¹' (D : Set X)) ha
  rw [hpreimage, hcomp] at heq
  apply TopologicalSpace.Opens.ext
  change (Subtype.val : r.source → X) '' connectedComponentIn (r.map ⁻¹' (D : Set X)) a =
    (Subtype.val : f.source → X) '' connectedComponentIn (f.map ⁻¹' (D : Set X)) (j a)
  rw [← heq, ← image_comp]
  rfl

theorem componentSingularValues_restrictSource_clopen_eq
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (hVc : IsClosed ((Subtype.val : f.source → X) ⁻¹' (V : Set X)))
    (D : TopologicalSpace.Opens X)
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
      (f.inverseComponentSource_restrictSource_clopen_eq hf V hV hVc D a ha)
  let e : g₁.source ≃ₜ g₂.source := Homeomorph.setCongr hsource
  have he : g₁.map = g₂.map ∘ e := by funext x; rfl
  have hreg := regularValues_eq_of_source_homeomorph g₂ g₁ e he
  have hrange : range g₁.map = range g₂.map := by
    rw [he, range_comp, e.surjective.range_eq, image_univ]
  change g₁.singularValues ∩ closure (range g₁.map) ∩ (D : Set X) =
    g₂.singularValues ∩ closure (range g₂.map) ∩ (D : Set X)
  rw [singularValues, singularValues, hreg, hrange]

variable [T2Space X] [IsManifold 𝓘(ℂ) 1 X]

theorem singularValues_restrictSource_clopen_subset
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (hVc : IsClosed ((Subtype.val : f.source → X) ⁻¹' (V : Set X))) :
    (f.restrictSource V hV).singularValues ⊆ f.singularValues := by
  let S : Set f.source := Subtype.val ⁻¹' (V : Set X)
  have hS : IsClopen S := ⟨hVc, V.isOpen.preimage continuous_subtype_val⟩
  let e : (f.restrictSource V hV).source ≃ₜ S :=
    { toFun := fun x => ⟨⟨x, hV x.2⟩, x.2⟩
      invFun := fun x => ⟨(x : f.source), x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  intro y hy hyreg
  apply hy
  obtain ⟨A, hA, hyA, hcov⟩ := hyreg
  refine ⟨A, hA, hyA, ?_⟩
  exact (SurfaceDynamics.coveringOn_clopen_source hf hS hA hcov).comp_homeomorph e

end SurfaceDynamics.LocalMap
