module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponentCovering
public import BoundedWanderingDomains.Surfaces.LocalMapRestriction
public import BoundedWanderingDomains.Surfaces.CoordinateDiscParam
public import BoundedWanderingDomains.Surfaces.LocalMapTotalization

@[expose] public section

/-! # Full inverse components and their genuine singular obstructions -/

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The ambient open set corresponding to a full inverse component, computed
in the actual source of the local map. -/
def inverseComponentSource (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) : TopologicalSpace.Opens X := by
  let : LocallyConnectedSpace f.source := ChartedSpace.locallyConnectedSpace ℂ f.source
  exact ⟨Subtype.val '' connectedComponentIn (f.map ⁻¹' (D : Set X)) a,
    f.source.isOpen.isOpenMap_subtype_val _ ((D.isOpen.preimage hf).connectedComponentIn)⟩

theorem inverseComponentSource_subset (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) :
    (f.inverseComponentSource hf D a : Set X) ⊆ f.source := by
  rintro x ⟨w, _, rfl⟩
  exact w.2

/-- The restriction to a full inverse component. Its target remains X. -/
def inverseComponentMap (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) : LocalMap X :=
  f.restrictSource (f.inverseComponentSource hf D a) (f.inverseComponentSource_subset hf D a)

/-- Singular obstructions which are approached by image values of this
component. Merely omitted open regions are excluded. -/
def componentSingularValues (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) : Set X :=
  (f.inverseComponentMap hf D a).singularValues ∩
    closure (range (f.inverseComponentMap hf D a).map) ∩ (D : Set X)

theorem subset_inverseComponentSource_of_preconnected
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X)
    (a : f.source) {A : Set X} (hA : IsPreconnected A) (hAs : A ⊆ f.source)
    (ha : (a : X) ∈ A) (hmap : ∀ x : f.source, (x : X) ∈ A → f.map x ∈ D) :
    A ⊆ f.inverseComponentSource hf D a := by
  let B : Set f.source := Subtype.val ⁻¹' A
  have hBA : (Subtype.val : f.source → X) '' B = A :=
    image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hAs hx⟩, rfl⟩)
  have hB : IsPreconnected B := by
    apply IsEmbedding.subtypeVal.isPreconnected_image.mp
    rwa [hBA]
  have hsub := hB.subset_connectedComponentIn ha (fun x hx => hmap x hx)
  intro x hx
  exact ⟨⟨x, hAs hx⟩, hsub hx, rfl⟩

variable [T2Space X]

theorem inverseComponent_regularValues_of_regular_neighborhood
    (f : LocalMap X) (hf : Continuous f.map) (D A : TopologicalSpace.Opens X)
    (hAD : (A : Set X) ⊆ D) [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (hc : IsCoveringMapOn f.map A) (a : f.source) {y : X} (_hyA : y ∈ A)
    (_hy : y ∈ closure (range (f.inverseComponentMap hf D a).map)) :
    (A : Set X) ⊆ (f.inverseComponentMap hf D a).regularValues := by
  let : LocallyConnectedSpace f.source := ChartedSpace.locallyConnectedSpace ℂ f.source
  let C := connectedComponentIn (f.map ⁻¹' (D : Set X)) a
  let V := f.inverseComponentSource hf D a
  let g := f.inverseComponentMap hf D a
  let e : C ≃ₜ V := IsEmbedding.subtypeVal.homeomorphImage C
  let p : C → X := fun z => f.map z
  have heq : g.map = p ∘ e.symm := by
    funext x
    have hx := congrArg Subtype.val (e.apply_symm_apply x)
    change f.map ⟨(x : X), _⟩ = f.map (e.symm x : f.source)
    exact congrArg f.map (Subtype.ext hx.symm)
  have hp := coveringOn_inverse_component_over_simplyConnected hf D.isOpen A.isOpen hAD hc a
  have hgcov : IsCoveringMapOn g.map A := by
    rw [heq]
    exact hp.comp_homeomorph e.symm
  exact fun z hz => ⟨A, A.isOpen, hz, hgcov⟩

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Every genuine obstruction of a full inverse component is a singular
value of the original map. -/
theorem componentSingularValues_subset (f : LocalMap X) (hf : Continuous f.map)
    (D : TopologicalSpace.Opens X) (a : f.source) :
    f.componentSingularValues hf D a ⊆ f.singularValues := by
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  intro y hy
  rcases hy with ⟨⟨hyS, hycl⟩, hyD⟩
  intro hyreg
  obtain ⟨W, hWo, hyW, hcov⟩ := hyreg
  obtain ⟨Q, hQ, hQsub⟩ := exists_coordDisk_center_closedCarrier_subset
    (hWo.inter D.isOpen) ⟨hyW, hyD⟩
  let A : TopologicalSpace.Opens X := ⟨range Q.param, Q.isOpenEmbedding_param.isOpen_range⟩
  let e : unitDisc ≃ₜ A := Q.isOpenEmbedding_param.isEmbedding.toHomeomorph
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  let : SimplyConnectedSpace A := e.symm.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace A := A.isOpen.locallyPathConnectedSpace
  have hAsub : (A : Set X) ⊆ W ∩ (D : Set X) := by
    rintro z ⟨w, rfl⟩
    exact hQsub (Q.param_mem_closedCarrier w)
  have hyA : y ∈ A := ⟨discZero, Q.param_zero.trans hQ⟩
  exact hyS (f.inverseComponent_regularValues_of_regular_neighborhood hf D A
    (fun _ hx => (hAsub hx).2) (hcov.mono (fun _ hx => (hAsub hx).1)) a hyA hycl hyA)

end SurfaceDynamics.LocalMap
