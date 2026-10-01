module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.TargetAnchors
public import BoundedWanderingDomains.Surfaces.Disconnected.OpenComponentCovers
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.ThreePointHyperbolization
public import BoundedWanderingDomains.Surfaces.AnchorComplementModels

@[expose] public section

/-! # Finite hyperbolising anchors in every ambient component -/

open Set Function Metric TopologicalSpace Topology
open AreaDeficit.Surfaces
open scoped Manifold ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [Finite (ConnectedComponents X)]

theorem exists_componentwise_anchors_disjoint_compact_in_disc
    (Q : EmbeddedDisc X) {L : Set X} (hL : IsCompact L) (hLQ : L ⊆ Q.carrier) :
    ∃ F : Finset X, Disjoint L (F : Set X) ∧
      Nonempty (ComponentwiseDiscCover (anchorComplement F)) := by
  classical
  let : Fintype (ConnectedComponents X) := Fintype.ofFinite _
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  let componentInfinite : ∀ c : ConnectedComponents X, Infinite (ambientComponent c) := by
    intro c
    let x : ambientComponent c := Classical.choice inferInstance
    obtain ⟨D, _, _⟩ := exists_coordDisk_center_closedCarrier_subset isOpen_univ (mem_univ x)
    let : Infinite unitDisc := Set.Infinite.to_subtype
      (infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1)))
    exact Infinite.of_injective D.param D.isOpenEmbedding_param.injective
  have hLc : ∀ c, IsCompact ((Subtype.val : ambientComponent c → X) ⁻¹' L) :=
    fun c => (isClosed_ambientComponent c).isClosedEmbedding_subtypeVal.isCompact_preimage hL
  have hLne : ∀ c, (Subtype.val : ambientComponent c → X) ⁻¹' L ≠ univ := by
    intro c he
    let x : ambientComponent c := Classical.choice inferInstance
    have hCL : (ambientComponent c : Set X) ⊆ L := by
      intro y hy
      have hh : (⟨y, hy⟩ : ambientComponent c) ∈ (Subtype.val ⁻¹' L : Set (ambientComponent c)) :=
        he.symm ▸ mem_univ _
      exact hh
    have hQC : (Q.carrier : Set X) ⊆ ambientComponent c := by
      have hh := Q.isConnected_carrier.subset_connectedComponent (hLQ (hCL x.property))
      rw [← ambientComponent_mk, show ConnectedComponents.mk (x : X) = c from x.property] at hh
      exact hh
    have hLQeq : L = (Q.carrier : Set X) := subset_antisymm hLQ (hQC.trans hCL)
    apply unitDisc_univ_not_isCompact
    rw [Q.embedding.isEmbedding.isCompact_iff, image_univ]
    change IsCompact (Q.carrier : Set X)
    exact hLQeq ▸ hL
  choose F hFcard hLF using fun c => exists_three_anchors_disjoint_proper_compact (hLc c) (hLne c)
  let E : Finset X := Finset.univ.biUnion (fun c => (F c).image Subtype.val)
  have hFE : ∀ c, (Subtype.val : ambientComponent c → X) '' (F c : Set (ambientComponent c)) ⊆ E := by
    intro c y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  refine ⟨E, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro y hyL hyE
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hyE
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hc
    have hxL : (x : X) ∈ L := hxy.symm ▸ hyL
    exact disjoint_left.mp (hLF c) hxL hx
  · apply nonempty_componentwiseDiscCover_of_component_pieces (anchorComplement E)
      (fun c => anchorComplement (F c))
    · intro c x hx hxF
      exact hx (hFE c ⟨x, hxF, rfl⟩)
    · intro c _
      exact DiscCover.nonempty_compl_three_on_any_surface (F c) (hFcard c)

end SurfaceDynamics
