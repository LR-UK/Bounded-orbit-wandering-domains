module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponents

@[expose] public section

/-! # Preimage components and maps into their target discs

The public statements quantify over components themselves. Base points are only
used internally to certify that an open set is a full, nonempty component.
-/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics.Map

/-- Reading a map in an open ambient target preserves regularity at its points. -/
theorem regularValues_into_open_iff
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (D : TopologicalSpace.Opens X) (g : A → D) (y : D) :
    y ∈ regularValues g ↔ (y : X) ∈ regularValues (Subtype.val ∘ g) := by
  constructor
  · rintro ⟨V, hV, hyV, hcov⟩
    refine ⟨Subtype.val '' V, D.isOpen.isOpenMap_subtype_val V hV,
      ⟨y, hyV, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (IsEvenlyCovered.subtypeVal_comp (D : Set X) D.isOpen
      (hcov z hz)).to_isEvenlyCovered_preimage
  · rintro ⟨V, hV, hyV, hcov⟩
    let p : A → X := Subtype.val ∘ g
    let e : A ≃ₜ p ⁻¹' (D : Set X) :=
      { toFun := fun a => ⟨a, (g a).2⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := continuous_id.subtype_mk _
        continuous_invFun := continuous_subtype_val }
    refine ⟨Subtype.val ⁻¹' V, hV.preimage continuous_subtype_val, hyV, ?_⟩
    intro z hz
    have h := ((hcov z hz).restrictPreimage (D : Set X) z.2).comp_homeomorph e
    exact h.to_isEvenlyCovered_preimage

end SurfaceDynamics.Map

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A full nonempty connected component of the inverse image of D. -/
structure PreimageComponent (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) where
  carrier : TopologicalSpace.Opens X
  isComponent : ∃ a : f.source, f.map a ∈ D ∧ carrier = f.inverseComponentSource hf D a

namespace PreimageComponent

variable {f : LocalMap X} {hf : Continuous f.map} {D : TopologicalSpace.Opens X}

theorem subset_source (U : f.PreimageComponent hf D) : (U.carrier : Set X) ⊆ f.source := by
  obtain ⟨a, _, he⟩ := U.isComponent
  rw [he]
  exact f.inverseComponentSource_subset hf D a

theorem map_mem (U : f.PreimageComponent hf D) (z : U.carrier) :
    f.map ⟨z, U.subset_source z.2⟩ ∈ D := by
  obtain ⟨a, _, he⟩ := U.isComponent
  have hz : (z : X) ∈ f.inverseComponentSource hf D a := he ▸ z.2
  obtain ⟨b, hb, hbe⟩ := hz
  have hba : b = ⟨z, U.subset_source z.2⟩ := Subtype.ext hbe
  exact hba ▸ connectedComponentIn_subset (f.map ⁻¹' (D : Set X)) a hb

/-- The restricted map has the component as source and D as target. -/
def map (U : f.PreimageComponent hf D) : U.carrier → D :=
  fun z => ⟨f.map ⟨z, U.subset_source z.2⟩, U.map_mem z⟩

/-- The ordinary singular values of the restricted map U → D, viewed in X. -/
def singularValues (U : f.PreimageComponent hf D) : Set X :=
  Subtype.val '' SurfaceDynamics.Map.singularValues U.map

end PreimageComponent

/-- Internal conversion from a base point to the component it names. -/
def preimageComponentAt (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) (ha : f.map a ∈ D) :
    f.PreimageComponent hf D :=
  ⟨f.inverseComponentSource hf D a, a, ha, rfl⟩

theorem singularValues_preimageComponentAt (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) (ha : f.map a ∈ D) :
    (f.preimageComponentAt hf D a ha).singularValues = f.componentSingularValues hf D a := by
  let U := f.preimageComponentAt hf D a ha
  let g := f.inverseComponentMap hf D a
  have heq : Subtype.val ∘ U.map = g.map := rfl
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hs : (z : X) ∈ g.singularValues := by
      intro hr
      apply hz
      apply (Map.regularValues_into_open_iff D U.map z).mpr
      rwa [heq]
    exact ⟨⟨hs, g.singularValues_subset_closure_range hs⟩, z.2⟩
  · rintro ⟨⟨hs, _⟩, hy⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    intro hr
    apply hs
    have hh := (Map.regularValues_into_open_iff D U.map ⟨y, hy⟩).mp hr
    rwa [heq] at hh

end SurfaceDynamics.LocalMap
