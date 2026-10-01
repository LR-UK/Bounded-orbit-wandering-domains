module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseCover
public import BoundedWanderingDomains.Surfaces.DiscCovering

@[expose] public section

/-! # Reading a component's disc cover in the full ambient manifold -/

open Set Function Topology
open scoped Manifold

namespace AreaDeficit.Surfaces

theorem covering_comp_clopen_inclusion
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {C : Set X} (hC : IsClopen C) {p : E → C} (hp : IsCoveringMap p) :
    IsCoveringMap ((Subtype.val : C → X) ∘ p) := by
  let f : E → X := (Subtype.val : C → X) ∘ p
  have hfc : IsCoveringMapOn f C :=
    IsCoveringMapOn.of_isCoveringMap_subtype hC.isOpen (fun x => (p x).property) hp
  intro y
  by_cases hy : y ∈ C
  · exact hfc y hy
  · have he : f ⁻¹' Cᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx (p x).property
    exact (IsEvenlyCovered.of_preimage_eq_empty Empty
      (hC.isClosed.isOpen_compl.mem_nhds hy) he).to_isEvenlyCovered_preimage

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

def ComponentwiseDiscCover.discCovering (p : ComponentwiseDiscCover X)
    (c : ConnectedComponents X) : DiscCovering X where
  projection := (Subtype.val : ambientComponent c → X) ∘ (p.cover c).projection
  holomorphic := (mdifferentiable_subtype_val (ambientComponent c)).comp (p.cover c).holomorphic
  covering := covering_comp_clopen_inclusion
    ⟨isClosed_ambientComponent c, (ambientComponent c).isOpen⟩ (p.cover c).covering

theorem ComponentwiseDiscCover.discCovering_range (p : ComponentwiseDiscCover X)
    (c : ConnectedComponents X) :
    range (p.discCovering c).projection = (ambientComponent c : Set X) := by
  change range ((Subtype.val : ambientComponent c → X) ∘ (p.cover c).projection) = _
  rw [range_comp, (p.cover c).surjective.range_eq, image_univ, Subtype.range_coe]

theorem ComponentwiseDiscCover.mem_discCovering_range (p : ComponentwiseDiscCover X) (x : X) :
    x ∈ range (p.discCovering (ConnectedComponents.mk x)).projection := by
  rw [p.discCovering_range]
  rfl

end AreaDeficit.Surfaces
