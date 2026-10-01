module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.PositiveAreaImage

@[expose] public section

/-! # Positive chart area survives passage to an open ambient manifold -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] in
theorem HasPositiveChartArea.openSubtype {A : Set X}
    (hpos : HasPositiveChartArea A) (hA : MeasurableSet A)
    (O : TopologicalSpace.Opens X) (hAO : A ⊆ O) :
    HasPositiveChartArea ((Subtype.val : O → X) ⁻¹' A) := by
  classical
  obtain ⟨s, hsc, hcover⟩ := countable_cover_nhds (fun x : O => chart_source_mem_nhds ℂ x)
  let : Countable s := hsc.to_subtype
  let B : s → Set X := fun i => (Subtype.val : O → X) '' (chartAt ℂ i.val).source
  have hBo : ∀ i, IsOpen (B i) := fun i =>
    O.isOpen.isOpenMap_subtype_val _ (chartAt ℂ i.val).open_source
  have hAB : A ⊆ ⋃ i, B i := by
    intro x hx
    have hh : (⟨x, hAO hx⟩ : O) ∈ ⋃ i ∈ s, (chartAt ℂ i).source := hcover ▸ mem_univ _
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hh
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, ⟨x, hAO hx⟩, hxi, rfl⟩
  obtain ⟨i, hpiece⟩ := hpos.exists_positive_piece B hAB
  obtain ⟨x, K, hK, hKsub, hKpos⟩ :=
    hpiece.exists_compact_chart_patch (hA.inter (hBo i).measurableSet)
  have hKO : K ⊆ O := fun _ hx => hAO (hKsub hx).1.1
  let KO : Set O := Subtype.val ⁻¹' K
  have himage : (Subtype.val : O → X) '' KO = K :=
    image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hKO hx⟩, rfl⟩)
  have hKOc : IsCompact KO := IsEmbedding.subtypeVal.isCompact_iff.mpr (himage.symm ▸ hK)
  have hON : Nonempty O := ⟨i.val⟩
  let c := (chartAt ℂ x).subtypeRestr hON
  let d := chartAt ℂ i.val
  have hKOcsource : KO ⊆ c.source := by
    intro y hy
    simpa [c] using (hKsub hy).2
  have hKOd : KO ⊆ d.source := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := (hKsub hy).1.2
    exact (Subtype.ext hzy : z = y) ▸ hz
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    mdifferentiableOn_subtypeRestr hON (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have he : c '' KO = (chartAt ℂ x) '' K := by
    rw [← himage, image_image]
    rfl
  have hp := positive_chart_area_image_of_compact hc (mdifferentiable_chart (I := 𝓘(ℂ)) i.val).1
    (f := id) mdifferentiable_id (fun S hS => by simpa only [image_id] using hS) hKOc hKOcsource
    (by simpa only [image_id] using hKOd) (fun _ _ _ _ h => h) (he.symm ▸ hKpos)
  refine ⟨i.val, lt_of_lt_of_le ?_ (measure_mono (image_mono (show KO ⊆
    (Subtype.val ⁻¹' A) ∩ d.source from fun y hy => ⟨(hKsub hy).1.1, hKOd hy⟩)))⟩
  simpa only [image_id] using hp

end SurfaceDynamics
