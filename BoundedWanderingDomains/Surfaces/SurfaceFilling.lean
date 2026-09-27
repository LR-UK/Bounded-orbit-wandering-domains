/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactFilling
import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
import BoundedWanderingDomains.HolomorphicFilling
import EremenkosConjecture.PlaneSimpleConnectivity

/-! # Coordinate neighbourhoods of surface fillings -/

open Set Function Metric Bornology
open scoped Topology Manifold

namespace AreaDeficit.Surfaces

theorem compactFill_complex_eq_fill (K : Set ℂ) :
    compactFill K = ComplexApproximation.fill K := by
  ext x
  change IsCompact (closure (connectedComponentIn Kᶜ x)) ↔
    IsBounded (connectedComponentIn Kᶜ x)
  exact ⟨fun h => h.isBounded.subset subset_closure, fun h => h.isCompact_closure⟩

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [ConnectedSpace X] [NoncompactSpace X]

theorem compactFill_subset_coordDisk {C : Set X}
    (D : RiemannDynamics.CoordDisk X) (hCD : C ⊆ D.closedCarrier) :
    compactFill C ⊆ D.closedCarrier :=
  compactFill_subset_compact_of_connected_complement hCD D.isCompact_closedCarrier
    (RiemannDynamics.isConnected_coordDisk_compl D).isPreconnected

/-- The planar filling in a coordinate disc maps into the intrinsic
surface filling. This comparison allows the planar Jordan theorem to be
reused only where a coordinate chart is actually available. -/
theorem chart_symm_image_fill_subset_compactFill
    {C : Set X} (hC : IsCompact C) (D : RiemannDynamics.CoordDisk X)
    (hCD : C ⊆ D.closedCarrier) :
    (chartAt ℂ D.center).symm ''
      ComplexApproximation.fill ((chartAt ℂ D.center) '' C) ⊆ compactFill C := by
  let c := chartAt ℂ D.center
  have hCc : C ⊆ c.source := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hCD hx
    exact c.map_target (D.closedBall_subset hz)
  have hCimage : IsCompact (c '' C) := hC.image_of_continuousOn (c.continuousOn.mono hCc)
  have himageball : c '' C ⊆ closedBall (c D.center) D.radius := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hCD hx
    rw [← hzx, c.right_inv (D.closedBall_subset hz)]
    exact hz
  have hfillball : ComplexApproximation.fill (c '' C) ⊆
      closedBall (c D.center) D.radius := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    simpa only [id_eq] using AreaDeficit.norm_le_on_fill hCimage
      (differentiable_id.sub_const (c D.center))
      (fun w hw => by simpa only [mem_closedBall, dist_eq_norm, id_eq] using himageball hw) z hz
  have hfilltarget : compactFill (c '' C) ⊆ c.target := by
    rw [compactFill_complex_eq_fill]
    exact hfillball.trans D.closedBall_subset
  have hh := image_compactFill_subset_compactFill_image_local hCimage.isClosed
    hfilltarget c.continuousOn_symm
    (fun S hS hSo => c.isOpen_image_symm_of_subset_target hSo hS)
  have heq : c.symm '' (c '' C) = C := c.symm_image_image_of_subset_source hCc
  rw [compactFill_complex_eq_fill, heq] at hh
  exact hh

/-- A compact connected set in a coordinate disc whose filling lies in an
open set has a simply connected open neighbourhood inside that open set. -/
theorem exists_simplyConnected_neighborhood_of_compactFill_subset
    {C U : Set X} (hC : IsCompact C) (hCc : IsConnected C) (hU : IsOpen U)
    (D : RiemannDynamics.CoordDisk X) (hCD : C ⊆ D.closedCarrier)
    (hfillU : compactFill C ⊆ U) :
    ∃ W : Set X, IsOpen W ∧ IsSimplyConnected W ∧ C ⊆ W ∧ W ⊆ U := by
  let c := chartAt ℂ D.center
  have hCc' : C ⊆ c.source := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hCD hx
    exact c.map_target (D.closedBall_subset hz)
  have hAc : IsCompact (c '' C) := hC.image_of_continuousOn (c.continuousOn.mono hCc')
  have hAconn : IsConnected (c '' C) := hCc.image c (c.continuousOn.mono hCc')
  let L := ComplexApproximation.fill (c '' C)
  let T := c.target ∩ c.symm ⁻¹' U
  have hLT : L ⊆ T := by
    intro z hz
    have hzs : c.symm z ∈ compactFill C :=
      chart_symm_image_fill_subset_compactFill hC D hCD ⟨z, hz, rfl⟩
    have hzball : z ∈ closedBall (c D.center) D.radius := by
      rw [mem_closedBall, dist_eq_norm]
      apply AreaDeficit.norm_le_on_fill hAc (differentiable_id.sub_const (c D.center))
        (fun w hw => ?_) z hz
      obtain ⟨x, hx, rfl⟩ := hw
      obtain ⟨v, hv, hvx⟩ := hCD hx
      rw [← hvx, c.right_inv (D.closedBall_subset hv)]
      exact mem_closedBall_iff_norm.mp hv
    exact ⟨D.closedBall_subset hzball, hfillU hzs⟩
  obtain ⟨J, -, -, hJT⟩ := EremenkosConjecture.exists_nested_jordan_neighbourhoods_within
    L T (ComplexApproximation.isCompact_fill hAc)
    (ComplexApproximation.isConnected_fill hAc.isClosed hAconn)
    (ComplexApproximation.isConnected_compl_fill hAc)
    (c.isOpen_inter_preimage_symm hU) hLT
  let S := interior (J 0).carrier
  have hStarget : S ⊆ c.target := interior_subset.trans (hJT.trans inter_subset_left)
  let W := c.symm '' S
  have hWc : W ⊆ c.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact c.map_target (hStarget hz)
  have himage : c '' W = S := c.image_symm_image_of_subset_target hStarget
  let e : W ≃ₜ S := c.homeomorphOfImageSubsetSource hWc himage
  have hSsc : SimplyConnectedSpace S := (J 0).simplyConnectedInterior
  letI := hSsc
  refine ⟨W, c.isOpen_image_symm_of_subset_target isOpen_interior hStarget,
    e.toHomotopyEquiv.simplyConnectedSpace, ?_, ?_⟩
  · intro x hx
    exact ⟨c x, (J 0).contains (ComplexApproximation.subset_fill _ ⟨x, hx, rfl⟩),
      c.left_inv (hCc' hx)⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hJT (interior_subset hz)).2

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.exists_simplyConnected_neighborhood_of_compactFill_subset
