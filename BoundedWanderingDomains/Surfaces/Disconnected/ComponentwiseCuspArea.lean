module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CuspAreaFinite
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseFiniteArea
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FiniteObstructions

@[expose] public section

/-! # Finite cusp area in a disconnected hyperbolic manifold -/

open Set Function Metric MeasureTheory TopologicalSpace Topology
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [LocallyCompactSpace X] in
theorem hyperbolicArea_cusp_chart_finite (p : ComponentwiseDiscCover X)
    {d : OpenPartialHomeomorph X ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ d.target) :
    p.hyperbolicArea (d.symm '' (ball a (R / 2) \ {a})) < ⊤ := by
  classical
  obtain ⟨b, hb, hba⟩ := (infinite_of_mem_nhds a (ball_mem_nhds a hR)).exists_notMem_finite
    (finite_singleton a)
  let B : Set ℂ := ball a R \ {a}
  let A : Set ℂ := ball a (R / 2) \ {a}
  have hAB : A ⊆ B := fun z hz => ⟨hz.1.trans (half_lt_self hR), hz.2⟩
  have hB : IsConnected B := SurfaceDynamics.BKL.isConnected_diff_finite
    ⟨ball a R, isOpen_ball⟩ (isConnected_ball hR) (finite_singleton a) ⟨b, hb, hba⟩
  let c := ConnectedComponents.mk (d.symm b)
  let C := ambientComponent c
  let : Nonempty C := inferInstance
  have hBC : d.symm '' B ⊆ C := by
    change d.symm '' B ⊆ (ambientComponent (ConnectedComponents.mk (d.symm b)) : Set X)
    rw [ambientComponent_mk]
    exact (hB.isPreconnected.image d.symm (d.continuousOn_symm.mono hball)).subset_connectedComponent
      ⟨b, ⟨hb, hba⟩, rfl⟩
  let e := d.subtypeRestr (inferInstance : Nonempty C)
  have hballC : B ⊆ e.target := by
    intro z hz
    let y : C := ⟨d.symm z, hBC ⟨z, hz, rfl⟩⟩
    have hh := d.map_subtype_source (inferInstance : Nonempty C) (x := y)
      (d.map_target (hball hz))
    change d (d.symm z) ∈ e.target at hh
    simpa only [d.right_inv (hball hz)] using hh
  have hv : ∀ z ∈ A, ((e.symm z : C) : X) = d.symm z := by
    intro z hz
    exact d.subtypeRestr_symm_apply (inferInstance : Nonempty C) (hballC (hAB hz))
  have he : (Subtype.val : C → X) ⁻¹' (d.symm '' A) = e.symm '' A := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact ⟨z, hz, Subtype.ext ((hv z hz).trans hzy)⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (hv z hz).symm⟩
  have hAm : MeasurableSet (d.symm '' A) := chart_inverse_image_measurable d
    (measurableSet_ball.diff (measurableSet_singleton a)) (hAB.trans hball)
  rw [p.hyperbolicArea_apply_of_subset_component c hAm ((image_mono hAB).trans hBC), he]
  exact (p.cover c).hyperbolicArea_cusp_chart_finite
    (mdifferentiableOn_subtypeRestr (inferInstance : Nonempty C) hd) hR hballC

theorem hyperbolicArea_compact_finite (p : ComponentwiseDiscCover X)
    {K : Set X} (hK : IsCompact K) : p.hyperbolicArea K < ⊤ := by
  have he : finitePunctureDomain (∅ : Finset X) = ⊤ := by ext x; simp [finitePunctureDomain]
  simpa only [he, hyperbolicArea] using p.finitePunctureDomain_area_compact_finite ∅ hK

end AreaDeficit.Surfaces.ComponentwiseDiscCover
