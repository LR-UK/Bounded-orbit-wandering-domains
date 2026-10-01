module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SurfaceFilling
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseFillingTopology

@[expose] public section

/-! # Coordinate discs and their fillings inside one ambient component -/

open Set Function Metric Topology TopologicalSpace

namespace RiemannDynamics.CoordDisk

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def restrict (D : CoordDisk X) (O : Opens X) (hcenter : D.center ∈ O)
    (hD : D.closedCarrier ⊆ O) : CoordDisk O where
  center := ⟨D.center, hcenter⟩
  radius := D.radius
  radius_pos := D.radius_pos
  closedBall_subset := by
    intro z hz
    refine ⟨D.closedBall_subset hz, ?_⟩
    rw [O.openPartialHomeomorphSubtypeCoe_target, mem_preimage]
    exact hD ⟨z, hz, rfl⟩

theorem image_closedCarrier_restrict (D : CoordDisk X) (O : Opens X)
    (hcenter : D.center ∈ O) (hD : D.closedCarrier ⊆ O) :
    (Subtype.val : O → X) '' (D.restrict O hcenter hD).closedCarrier = D.closedCarrier := by
  let R := D.restrict O hcenter hD
  have hval (z : ℂ) (hz : z ∈ closedBall (chartAt ℂ D.center D.center) D.radius) :
      (((chartAt ℂ R.center).symm z : O) : X) = (chartAt ℂ D.center).symm z :=
    (chartAt ℂ D.center).subtypeRestr_symm_apply ⟨R.center⟩ (R.closedBall_subset hz)
  change Subtype.val '' ((chartAt ℂ R.center).symm ''
    closedBall (chartAt ℂ D.center D.center) D.radius) = _
  rw [image_image]
  apply image_congr
  exact hval

theorem preimage_closedCarrier_restrict (D : CoordDisk X) (O : Opens X)
    (hcenter : D.center ∈ O) (hD : D.closedCarrier ⊆ O) :
    (Subtype.val : O → X) ⁻¹' D.closedCarrier = (D.restrict O hcenter hD).closedCarrier := by
  rw [← D.image_closedCarrier_restrict O hcenter hD, preimage_image_eq _ Subtype.val_injective]

theorem closedCarrier_subset_ambientComponent (D : CoordDisk X) :
    D.closedCarrier ⊆ AreaDeficit.Surfaces.ambientComponent (ConnectedComponents.mk D.center) := by
  rw [AreaDeficit.Surfaces.ambientComponent_mk]
  apply (isPreconnected_closedBall.image _
    ((chartAt ℂ D.center).continuousOn_symm.mono D.closedBall_subset)).subset_connectedComponent
  exact ⟨chartAt ℂ D.center D.center, mem_closedBall_self D.radius_pos.le,
    (chartAt ℂ D.center).left_inv (mem_chart_source ℂ D.center)⟩

end RiemannDynamics.CoordDisk

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
  [NoncompactComponents X]

theorem compactFill_subset_coordDisk_of_noncompactComponents {K : Set X}
    (D : RiemannDynamics.CoordDisk X) (hKD : K ⊆ D.closedCarrier) :
    compactFill K ⊆ D.closedCarrier := by
  let c := ConnectedComponents.mk D.center
  let C := ambientComponent c
  let R := D.restrict C rfl D.closedCarrier_subset_ambientComponent
  have hKC : K ⊆ C := hKD.trans D.closedCarrier_subset_ambientComponent
  intro x hx
  let y : C := ⟨x, compactFill_subset_ambientComponent c hKC hx⟩
  have hy : y ∈ compactFill ((Subtype.val : C → X) ⁻¹' D.closedCarrier) := by
    rw [← preimage_compactFill_ambientComponent c D.isCompact_closedCarrier.isClosed]
    exact compactFill_mono hKD hx
  rw [D.preimage_closedCarrier_restrict C rfl D.closedCarrier_subset_ambientComponent] at hy
  have hyR : y ∈ R.closedCarrier := compactFill_subset_coordDisk R subset_rfl hy
  rw [← D.image_closedCarrier_restrict C rfl D.closedCarrier_subset_ambientComponent]
  exact ⟨y, hyR, rfl⟩

end AreaDeficit.Surfaces
