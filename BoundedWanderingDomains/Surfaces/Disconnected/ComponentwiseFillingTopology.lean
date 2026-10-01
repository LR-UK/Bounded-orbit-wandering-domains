module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseFilling
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentDomains

@[expose] public section

/-! # Comparing intrinsic filling with filling inside an ambient component -/

open Set Function Topology

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

instance ambientComponent_noncompactSpace [NoncompactComponents X] (c : ConnectedComponents X) :
    NoncompactSpace (ambientComponent c) where
  noncompact_univ h := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have hi := h.image (continuous_subtype_val :
      Continuous (Subtype.val : ambientComponent (ConnectedComponents.mk x) → X))
    rw [image_univ, Subtype.range_coe, ambientComponent_mk] at hi
    exact NoncompactComponents.not_isCompact x hi

theorem preimage_compactFill_ambientComponent (c : ConnectedComponents X)
    {K : Set X} (hK : IsClosed K) :
    (Subtype.val : ambientComponent c → X) ⁻¹' compactFill K =
      compactFill ((Subtype.val : ambientComponent c → X) ⁻¹' K) := by
  ext x
  by_cases hx : (x : X) ∈ K
  · exact ⟨fun _ => subset_compactFill _ hx, fun _ => subset_compactFill K hx⟩
  let U : TopologicalSpace.Opens X := ⟨Kᶜ, hK.isOpen_compl⟩
  have he := SurfaceDynamics.embedding_image_connectedComponentIn
    (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : ambientComponent c → X))
    ((Subtype.val : ambientComponent c → X) ⁻¹' K)ᶜ hx
  have hSU : (Subtype.val : ambientComponent c → X) ''
      ((Subtype.val ⁻¹' K : Set (ambientComponent c))ᶜ) = Kᶜ ∩ ambientComponent c := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.property⟩
    · rintro ⟨hyK, hyc⟩
      exact ⟨⟨y, hyc⟩, hyK, rfl⟩
  rw [hSU] at he
  have he' := he.trans (connectedComponentIn_inter_ambientComponent c U x hx)
  change (Subtype.val : ambientComponent c → X) ''
    connectedComponentIn (Subtype.val ⁻¹' K)ᶜ x = connectedComponentIn Kᶜ (x : X) at he'
  change IsCompact (closure (connectedComponentIn Kᶜ (x : X))) ↔ _
  have hj : IsClosedEmbedding (Subtype.val : ambientComponent c → X) :=
    (isClosed_ambientComponent c).isClosedEmbedding_subtypeVal
  rw [← he', hj.closure_image_eq]
  exact hj.isEmbedding.isCompact_iff.symm

theorem isConnected_compactFill_of_noncompactComponents [NoncompactComponents X]
    {K : Set X} (hK : IsClosed K) (hconn : IsConnected K) :
    IsConnected (compactFill K) := by
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  obtain ⟨a, ha⟩ := hconn.nonempty
  let c := ConnectedComponents.mk a
  let C := ambientComponent c
  let : LocallyConnectedSpace C := ChartedSpace.locallyConnectedSpace ℂ C
  have hKC : K ⊆ C := by
    rw [show (C : Set X) = connectedComponent a from ambientComponent_mk a]
    exact hconn.subset_connectedComponent ha
  have him : (Subtype.val : C → X) '' (Subtype.val ⁻¹' K) = K :=
    image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hKC hx⟩, rfl⟩)
  have hpre : IsConnected ((Subtype.val : C → X) ⁻¹' K) := by
    refine ⟨⟨⟨a, hKC ha⟩, ha⟩, ?_⟩
    apply (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : C → X)).isPreconnected_image.mp
    rw [him]
    exact hconn.isPreconnected
  have hfill := isConnected_compactFill (hK.preimage continuous_subtype_val) hpre
  have himfill : (Subtype.val : C → X) '' compactFill (Subtype.val ⁻¹' K) = compactFill K := by
    rw [← preimage_compactFill_ambientComponent c hK]
    exact image_preimage_eq_of_subset (fun x hx =>
      ⟨⟨x, compactFill_subset_ambientComponent c hKC hx⟩, rfl⟩)
  rw [← himfill]
  exact hfill.image _ continuous_subtype_val.continuousOn

end AreaDeficit.Surfaces
