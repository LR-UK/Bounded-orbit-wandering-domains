/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AnalyticSurface
import Mathlib.Analysis.Complex.OpenMapping

/-! # Open mapping on analytic surfaces -/

open Set Function Filter
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A complex one-dimensional manifold has no open singleton.  This local
fact does not require a global connectedness assumption. -/
theorem not_isOpen_singleton_surface (x : X) :
    ¬ IsOpen ({x} : Set X) := by
  intro hx
  have himage : IsOpen ((chartAt ℂ x) '' ({x} : Set X)) :=
    (chartAt ℂ x).isOpen_image_of_subset_source hx
      (Set.singleton_subset_iff.mpr (mem_chart_source ℂ x))
  rw [Set.image_singleton] at himage
  exact not_isOpen_singleton (chartAt ℂ x x) himage

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] in
/-- An open map between complex one-dimensional manifolds cannot be locally
constant. -/
theorem not_eventuallyEq_const_of_isOpenMap {f : X → Y}
    (hf : IsOpenMap f) (x : X) :
    ¬ f =ᶠ[𝓝 x] fun _ => f x := by
  intro hconst
  rcases mem_nhds_iff.mp hconst with ⟨U, hUsub, hUopen, hxU⟩
  have himage : f '' U = ({f x} : Set Y) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hzU, rfl⟩
      exact Set.mem_singleton_iff.mpr (hUsub hzU)
    · exact Set.singleton_subset_iff.mpr ⟨x, hxU, rfl⟩
  exact not_isOpen_singleton_surface (f x) (himage ▸ hf U hUopen)

/-- A holomorphic map between analytic surfaces has an analytic scalar
reading in extended charts. -/
theorem analyticAt_writtenInExtChartAt {f : X → Y}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (x : X) :
    AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f)
      (extChartAt 𝓘(ℂ) x x) := by
  let e := extChartAt 𝓘(ℂ) x
  let d := extChartAt 𝓘(ℂ) (f x)
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  have hI : range 𝓘(ℂ) = univ := ModelWithCorners.range_eq_univ 𝓘(ℂ)
  have hemap : Filter.map e.symm (𝓝 (e x)) = 𝓝 x := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℂ)) x, hI,
      nhdsWithin_univ]
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have het : e.target ∈ 𝓝 (e x) := by
    simpa only [hI, nhdsWithin_univ] using
      (extChartAt_target_mem_nhdsWithin (I := 𝓘(ℂ)) x)
  have hsource : ∀ᶠ y in 𝓝 (e x), f (e.symm y) ∈ (chartAt ℂ (f x)).source := by
    have hfsource : ∀ᶠ z in 𝓝 x, f z ∈ (chartAt ℂ (f x)).source :=
      (hf x).continuousAt
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    have he : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      show Filter.map e.symm (𝓝 (e x)) ≤ 𝓝 x
      rw [hemap]
    exact he.eventually hfsource
  filter_upwards [het, hsource] with y hyt hfy
  have hys : e.symm y ∈ (chartAt ℂ x).source := by
    rw [← extChartAt_source (I := 𝓘(ℂ)) x]
    exact e.map_target hyt
  have hy := (mdifferentiableAt_iff_of_mem_source
    (f := f) (x := x) (y := f x) hys hfy).mp (hf (e.symm y))
  rw [hI, differentiableWithinAt_univ, e.right_inv hyt] at hy
  exact hy.2

omit [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] in
/-- In extended coordinates, an open holomorphic surface map is not locally
constant. -/
theorem not_eventuallyEq_writtenInExtChartAt {f : X → Y}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hopen : IsOpenMap f) (x : X) :
    ¬ writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f =ᶠ[𝓝 (extChartAt 𝓘(ℂ) x x)]
      fun _ => writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f (extChartAt 𝓘(ℂ) x x) := by
  let e := extChartAt 𝓘(ℂ) x
  let d := extChartAt 𝓘(ℂ) (f x)
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  intro hg
  apply not_eventuallyEq_const_of_isOpenMap hopen x
  have he : Tendsto e (𝓝 x) (𝓝 (e x)) := by
    exact (chartAt ℂ x).continuousAt_extend (mem_chart_source ℂ x)
  have hg' : (g ∘ e) =ᶠ[𝓝 x] fun _ => g (e x) := hg.comp_tendsto he
  have hfs : ∀ᶠ z in 𝓝 x, f z ∈ d.source :=
    (hf x).continuousAt (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x))
  have hes : ∀ᶠ z in 𝓝 x, z ∈ e.source :=
    extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x
  filter_upwards [hg', hfs, hes] with z hgz hfz hez
  have hcoord : d (f z) = d (f x) := by
    simpa only [g, e, d, writtenInExtChartAt, Function.comp_apply,
      e.left_inv hez, extChartAt_to_inv] using hgz
  exact d.injOn hfz (mem_extChartAt_source (f x)) hcoord

/-- The complex open-mapping theorem in analytic-surface coordinates. -/
theorem isOpenMap_of_mdifferentiable_of_locally_nonconstant
    {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnc : ∀ x, ¬ f =ᶠ[𝓝 x] fun _ => f x) : IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  let e := extChartAt 𝓘(ℂ) x
  let d := extChartAt 𝓘(ℂ) (f x)
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  have hI : range 𝓘(ℂ) = univ := by
    exact ModelWithCorners.range_eq_univ 𝓘(ℂ)
  have hemap : Filter.map e.symm (𝓝 (e x)) = 𝓝 x := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℂ)) x, hI,
      nhdsWithin_univ]
  have hfdiff : ∀ᶠ y in 𝓝 (e x), DifferentiableAt ℂ g y := by
    have het : e.target ∈ 𝓝 (e x) := by
      simpa only [hI, nhdsWithin_univ] using
        (extChartAt_target_mem_nhdsWithin (I := 𝓘(ℂ)) x)
    have hsource : ∀ᶠ y in 𝓝 (e x), f (e.symm y) ∈ (chartAt ℂ (f x)).source := by
      have hfsource : ∀ᶠ z in 𝓝 x, f z ∈ (chartAt ℂ (f x)).source :=
        (hf x).continuousAt
          ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
      have he : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
        show Filter.map e.symm (𝓝 (e x)) ≤ 𝓝 x
        rw [hemap]
      exact he.eventually hfsource
    filter_upwards [het, hsource] with y hyt hfy
    have hys : e.symm y ∈ (chartAt ℂ x).source := by
      rw [← extChartAt_source (I := 𝓘(ℂ)) x]
      exact e.map_target hyt
    have hy := (mdifferentiableAt_iff_of_mem_source
      (f := f) (x := x) (y := f x) hys hfy).mp (hf (e.symm y))
    rw [hI, differentiableWithinAt_univ, e.right_inv hyt] at hy
    exact hy.2
  have hgan : AnalyticAt ℂ g (e x) :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr hfdiff
  have hgnc : ¬ g =ᶠ[𝓝 (e x)] fun _ => g (e x) := by
    intro hg
    apply hnc x
    have he : Tendsto e (𝓝 x) (𝓝 (e x)) := by
      exact (chartAt ℂ x).continuousAt_extend (mem_chart_source ℂ x)
    have hg' : (g ∘ e) =ᶠ[𝓝 x] fun _ => g (e x) := hg.comp_tendsto he
    have hfs : ∀ᶠ z in 𝓝 x, f z ∈ d.source :=
      (hf x).continuousAt (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x))
    have hes : ∀ᶠ z in 𝓝 x, z ∈ e.source :=
      extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x
    filter_upwards [hg', hfs, hes] with z hgz hfz hez
    have hcoord : d (f z) = d (f x) := by
      simpa only [g, e, d, writtenInExtChartAt, Function.comp_apply,
        e.left_inv hez, extChartAt_to_inv] using hgz
    exact d.injOn hfz (mem_extChartAt_source (f x)) hcoord
  have hgopen : 𝓝 (g (e x)) ≤ Filter.map g (𝓝 (e x)) :=
    hgan.eventually_constant_or_nhds_le_map_nhds.resolve_left hgnc
  have hge : g (e x) = d (f x) := by
    simp only [g, e, d, writtenInExtChartAt, Function.comp_apply,
      extChartAt_to_inv]
  rw [hge] at hgopen
  rw [← map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℂ)) (f x),
    hI, nhdsWithin_univ]
  apply le_trans (Filter.map_mono hgopen)
  rw [Filter.map_map]
  have heforward : Filter.map e (𝓝 x) = 𝓝 (e x) :=
    (chartAt ℂ x).map_extend_nhds_of_boundaryless (I := 𝓘(ℂ))
      (mem_chart_source ℂ x)
  rw [← heforward, Filter.map_map]
  have hfun : ((d.symm ∘ g) ∘ e) =ᶠ[𝓝 x] f := by
    have hfs : ∀ᶠ z in 𝓝 x, f z ∈ d.source :=
      (hf x).continuousAt (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x))
    have hes : ∀ᶠ z in 𝓝 x, z ∈ e.source :=
      extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x
    filter_upwards [hfs, hes] with z hfz hez
    simp only [g, e, d, writtenInExtChartAt,
      Function.comp_apply, e.left_inv hez, d.left_inv hfz]
  dsimp only [d, e] at hfun ⊢
  rw [Filter.map_congr hfun]

end SurfaceDynamics
