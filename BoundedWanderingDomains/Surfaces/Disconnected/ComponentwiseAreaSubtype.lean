module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseArea
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentDomains
public import BoundedWanderingDomains.Surfaces.DomainKernelArea
public import BoundedWanderingDomains.Surfaces.OpenEmbeddingAreaTransport

@[expose] public section

/-! # Intrinsic area of connected open subsets of disconnected manifolds -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem domainArea_component (p : ComponentwiseDiscCover X) (U : Opens X)
    (x : U) {A : Set X} (hA : MeasurableSet A)
    (hAU : A ⊆ componentDomain U (x : X)) :
    p.domainArea U A = p.domainArea (componentDomain U (x : X)) A := by
  let c := ConnectedComponents.mk (x : X)
  have hAc : A ⊆ ambientComponent c :=
    hAU.trans (componentDomain_subset_ambientComponent U x)
  rw [p.domainArea_apply_of_subset_component U c hA hAc,
    p.domainArea_apply_of_subset_component _ c hA hAc]
  let y : ambientComponent c := ⟨x, rfl⟩
  rw [componentPart_componentDomain c U y x.property]
  apply (p.cover c).domainArea_component (componentPart c U) ⟨y, x.property⟩
    (hA.preimage continuous_subtype_val.measurable)
  rw [← componentPart_componentDomain c U y x.property]
  exact fun _ hz => hAU hz

variable [LocallyCompactSpace X]

theorem domainArea_eq_hyperbolicArea_preimage_connected
    (p : ComponentwiseDiscCover X) (U : Opens X) [ConnectedSpace U]
    (q : DiscCover U) {A : Set X} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    p.domainArea U A = q.hyperbolicArea (Subtype.val ⁻¹' A) := by
  classical
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let x : U := Classical.choice (inferInstance : Nonempty U)
  let c := ConnectedComponents.mk (x : X)
  let C := ambientComponent c
  let : LocallyCompactSpace C := C.isOpen.locallyCompactSpace
  have hUC : (U : Set X) ⊆ C := by
    rw [show (C : Set X) = connectedComponent (x : X) from ambientComponent_mk (x : X)]
    exact (isConnected_iff_connectedSpace.mpr inferInstance).subset_connectedComponent x.property
  let j : U → C := Set.inclusion hUC
  have hj : Topology.IsOpenEmbedding j :=
    .of_continuous_injective_isOpenMap (continuous_inclusion hUC)
      (Set.inclusion_injective hUC) (U.isOpen.isOpenMap_inclusion hUC)
  have hjh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j := by
    apply (mdifferentiable_subtypeVal_comp_iff C j).mp
    exact mdifferentiable_subtype_val U
  have hJU : (⟨j '' (⊤ : Opens U), hj.isOpenMap _ isOpen_univ⟩ : Opens C) =
      componentPart c U := by
    apply Opens.ext
    ext y
    constructor
    · rintro ⟨z, _, rfl⟩
      exact z.property
    · intro hy
      exact ⟨⟨y, hy⟩, mem_univ _, Subtype.ext rfl⟩
  have hJA : j '' (Subtype.val ⁻¹' A : Set U) = (Subtype.val ⁻¹' A : Set C) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hAU hy⟩, hy, Subtype.ext rfl⟩
  have he := q.domainArea_image_openEmbedding (p.cover c) j hj hjh ⊤
    (hA.preimage continuous_subtype_val.measurable) (subset_univ _)
  rw [DiscCover.domainArea_top, hJU, hJA] at he
  rw [p.domainArea_apply_of_subset_component U c hA (hAU.trans hUC)]
  exact he.symm

end AreaDeficit.Surfaces.ComponentwiseDiscCover
