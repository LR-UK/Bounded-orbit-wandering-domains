/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AreaNullSets
import BoundedWanderingDomains.Surfaces.HyperbolicAreaFinite
import BoundedWanderingDomains.Surfaces.Statements
import BoundedWanderingDomains.Surfaces.SubdomainDensity

/-! # Positive chart area implies positive intrinsic hyperbolic area

This connects the area condition in the dynamical surface statement with the
intrinsic measure derived from a holomorphic disc covering. -/

open Set MeasureTheory
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

theorem HasPositiveChartArea.hyperbolicArea_pos {A : Set X}
    (hA : HasPositiveChartArea A) (hm : MeasurableSet A)
    (p : AreaDeficit.Surfaces.DiscCover X) :
    0 < p.hyperbolicArea A := by
  obtain ⟨x, hx⟩ := hA
  let c := chartAt ℂ x
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source := by
    intro y hy
    exact (mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _) hy).mdifferentiableWithinAt
  have hAc : MeasurableSet (A ∩ c.source) := hm.inter c.open_source.measurableSet
  have hpos : 0 < p.hyperbolicArea (A ∩ c.source) :=
    (p.hyperbolicArea_pos_iff_chart hc hAc inter_subset_right).2 hx
  exact lt_of_lt_of_le hpos (measure_mono inter_subset_left)

/-- Positive chart area remains positive for the intrinsic area of any open
subsurface containing the measured set. -/
theorem HasPositiveChartArea.hyperbolicArea_pos_openSubtype
    {A : Set X} (hA : HasPositiveChartArea A) (hm : MeasurableSet A)
    (O : TopologicalSpace.Opens X) (hAO : A ⊆ O)
    (p : AreaDeficit.Surfaces.DiscCover O) :
    0 < p.hyperbolicArea ((↑) ⁻¹' A : Set O) := by
  obtain ⟨x, hx⟩ := hA
  let c := chartAt ℂ x
  have hnon : (A ∩ c.source).Nonempty := by
    by_contra hn
    have he : A ∩ c.source = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he, image_empty, measure_empty] at hx
    exact (lt_irrefl 0 hx)
  obtain ⟨a, haA, hac⟩ := hnon
  let ao : O := ⟨a, hAO haA⟩
  let hON : Nonempty O := ⟨ao⟩
  let d := c.subtypeRestr hON
  let AO : Set O := (↑) ⁻¹' A
  have hAOmeas : MeasurableSet AO :=
    hm.preimage continuous_subtype_val.measurable
  have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source := by
    apply AreaDeficit.Surfaces.mdifferentiableOn_subtypeRestr hON
    intro y hy
    exact (mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _) hy).mdifferentiableWithinAt
  have himage : d '' (AO ∩ d.source) = c '' (A ∩ c.source) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyA, hyd⟩, rfl⟩
      exact ⟨(y : X), ⟨hyA, by simpa [d] using hyd⟩, rfl⟩
    · rintro ⟨y, ⟨hyA, hyc⟩, rfl⟩
      let yo : O := ⟨y, hAO hyA⟩
      refine ⟨yo, ⟨hyA, ?_⟩, rfl⟩
      simpa [d] using hyc
  have hmeas : MeasurableSet (AO ∩ d.source) :=
    hAOmeas.inter d.open_source.measurableSet
  have hpos : 0 < p.hyperbolicArea (AO ∩ d.source) :=
    (p.hyperbolicArea_pos_iff_chart hd hmeas inter_subset_right).2 (by
      rw [himage]
      exact hx)
  exact lt_of_lt_of_le hpos (measure_mono inter_subset_left)

/-- Countable exceptional sets have zero intrinsic hyperbolic area. -/
theorem hyperbolicArea_countable_zero
    (p : AreaDeficit.Surfaces.DiscCover X) {S : Set X}
    (hS : S.Countable) : p.hyperbolicArea S = 0 := by
  let : NullSingletonClass p.hyperbolicArea := p.hyperbolicArea_noAtoms
  exact hS.measure_zero p.hyperbolicArea

/-- Removing the countable backward exceptional set used in the dynamical
area argument preserves intrinsic area and hence positivity. -/
theorem hyperbolicArea_diff_countable
    (p : AreaDeficit.Surfaces.DiscCover X) (A : Set X) {S : Set X}
    (hS : S.Countable) : p.hyperbolicArea (A \ S) = p.hyperbolicArea A := by
  rw [measure_sdiff_null (hyperbolicArea_countable_zero p hS)]

/-- Positive chart area is unchanged by deleting a countable set. -/
theorem HasPositiveChartArea.diff_countable {A S : Set X}
    (hA : HasPositiveChartArea A) (hS : S.Countable) :
    HasPositiveChartArea (A \ S) := by
  obtain ⟨x, hx⟩ := hA
  let c := chartAt ℂ x
  refine ⟨x, ?_⟩
  let B : Set ℂ := c '' (S ∩ c.source)
  have hBcount : B.Countable := (hS.mono inter_subset_left).image c
  have hBzero : volume B = 0 := hBcount.measure_zero volume
  have heq : c '' ((A \ S) ∩ c.source) =
      c '' (A ∩ c.source) \ B := by
    ext z
    constructor
    · rintro ⟨y, ⟨⟨hyA, hyS⟩, hyc⟩, rfl⟩
      refine ⟨⟨y, ⟨hyA, hyc⟩, rfl⟩, ?_⟩
      rintro ⟨w, ⟨hwS, hwc⟩, hw⟩
      have hyw : y = w := c.injOn hyc hwc hw.symm
      exact hyS (hyw ▸ hwS)
    · rintro ⟨⟨y, ⟨hyA, hyc⟩, rfl⟩, hyB⟩
      refine ⟨y, ⟨⟨hyA, ?_⟩, hyc⟩, rfl⟩
      intro hyS
      exact hyB ⟨y, ⟨hyS, hyc⟩, rfl⟩
  rw [heq, measure_sdiff_null hBzero]
  exact hx

end SurfaceDynamics

