module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.AreaNullSets
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! # Local finiteness and absence of atoms for intrinsic hyperbolic area -/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem hyperbolicArea_compact_chart_finite (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {L : Set ℂ} (hL : IsCompact L) (hLc : L ⊆ c.target) :
    p.hyperbolicArea (c.symm '' L) < ⊤ := by
  have hM : IsCompact (c.symm '' L) :=
    hL.image_of_continuousOn (c.symm.continuousOn.mono hLc)
  have hMc : c.symm '' L ⊆ c.source := by
    rintro _ ⟨z,hz,rfl⟩
    exact c.map_target (hLc hz)
  rw [p.hyperbolicArea_apply_chart hc hM.measurableSet hMc]
  unfold coordinateArea
  have he : c '' (c.symm '' L) = L := by
    rw [← image_comp]
    exact image_congr (fun z hz => c.right_inv (hLc hz)) |>.trans (image_id L)
  rw [he]
  have hcont : ContinuousOn (fun z => (p.chartDensity c z)^2) L := by
    intro z hz
    exact ((p.chartDensity_contDiffAt hc (hLc hz)).continuousAt.pow 2).continuousWithinAt
  have hi : IntegrableOn (fun z => (p.chartDensity c z)^2) L := hcont.integrableOn_compact hL
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (ae_of_all _ (fun _ => sq_nonneg _))).mpr hi)

theorem hyperbolicArea_locallyFinite (p : DiscCover M) :
    IsLocallyFiniteMeasure p.hyperbolicArea := by
  constructor
  intro x
  let c := chartAt ℂ x
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  obtain ⟨L,hL,hxL,hLc⟩ := exists_compact_subset c.open_target (c.map_source hxc)
  refine ⟨c.source ∩ c ⁻¹' interior L,
    (c.isOpen_inter_preimage isOpen_interior).mem_nhds ⟨hxc,hxL⟩,?_⟩
  apply lt_of_le_of_lt (measure_mono ?_) (p.hyperbolicArea_compact_chart_finite hc hL hLc)
  rintro y ⟨hyc,hyL⟩
  exact ⟨c y,interior_subset hyL,c.left_inv hyc⟩

theorem hyperbolicArea_compact_finite (p : DiscCover M)
    {L : Set M} (hL : IsCompact L) : p.hyperbolicArea L < ⊤ := by
  let : IsLocallyFiniteMeasure p.hyperbolicArea := p.hyperbolicArea_locallyFinite
  exact hL.measure_lt_top

theorem hyperbolicArea_noAtoms (p : DiscCover M) : NullSingletonClass p.hyperbolicArea := by
  constructor
  intro x
  apply (p.hyperbolicArea_zero_iff_chart (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
    (measurableSet_singleton x) (singleton_subset_iff.mpr (mem_chart_source ℂ x))).mpr
  simp only [image_singleton,measure_singleton]

end AreaDeficit.Surfaces.DiscCover
