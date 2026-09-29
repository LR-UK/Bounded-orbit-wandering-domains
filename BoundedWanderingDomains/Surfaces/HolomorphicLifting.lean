module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.DiscCover
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Analysis.Complex.Conformal.Inverse.Function

@[expose] public section

/-! # Holomorphic inverse branches and lifts on Riemann surfaces

The inverse of a locally injective holomorphic surface map is holomorphic.
Consequently the continuous covering-space lift of a holomorphic map is
holomorphic. No differentiability of an inverse branch is assumed.
-/

open Set Function Filter Topology
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {M N A : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]

omit [IsManifold 𝓘(ℂ) 1 M] [IsManifold 𝓘(ℂ) 1 N] in
/-- In the boundaryless one-dimensional case, differentiability is ordinary
complex differentiability in the preferred charts, together with continuity. -/
theorem mdifferentiableAt_iff_chart {f : M → N} {x : M} :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x ↔ ContinuousAt f x ∧
      DifferentiableAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        (chartAt ℂ x x) := by
  rw [mdifferentiableAt_iff]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    comp_id, id_comp, range_id, differentiableWithinAt_univ]

/-- A holomorphic open partial homeomorphism has a holomorphic inverse. -/
theorem mdifferentiableOn_symm {e : OpenPartialHomeomorph M N}
    (he : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
  intro y hy
  let c := chartAt ℂ (e.symm y)
  let d := chartAt ℂ y
  let a : OpenPartialHomeomorph ℂ ℂ := (c.symm ≫ₕ e) ≫ₕ d
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M := IsManifold.chart_mem_maximalAtlas _
  have hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 N := IsManifold.chart_mem_maximalAtlas _
  have ha : DifferentiableOn ℂ a a.source := by
    intro u hu
    have huc : u ∈ c.target := hu.1.1
    have hue : c.symm u ∈ e.source := hu.1.2
    have hud : e (c.symm u) ∈ d.source := hu.2
    have h1 := mdifferentiableAt_symm_of_mem_maximalAtlas hc huc
    have h2 := (he _ hue).mdifferentiableAt (e.open_source.mem_nhds hue)
    have h3 := mdifferentiableAt_of_mem_maximalAtlas hd hud
    exact ((h3.comp u (h2.comp u h1)).differentiableAt).differentiableWithinAt
  have hdy : d y ∈ a.target := by
    change d y ∈ d.target ∧ d.symm (d y) ∈ (c.symm ≫ₕ e).target
    have hyD : y ∈ d.source := mem_chart_source ℂ y
    refine ⟨d.map_source hyD, ?_⟩
    rw [d.left_inv hyD]
    exact ⟨hy, mem_chart_source ℂ (e.symm y)⟩
  have hai : DifferentiableAt ℂ a.symm (d y) :=
    (TauCeti.OpenPartialHomeomorph.differentiableOn_symm ha).differentiableAt
      (a.open_target.mem_nhds hdy)
  apply MDifferentiableAt.mdifferentiableWithinAt
  apply mdifferentiableAt_iff_chart.mpr
  exact ⟨e.continuousAt_symm hy, hai⟩

/-- A continuous lift through a holomorphic local homeomorphism is holomorphic. -/
theorem mdifferentiable_lift [TopologicalSpace A] [ChartedSpace ℂ A]
    [IsManifold 𝓘(ℂ) 1 A] {p : M → N} (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    (hlocal : IsLocalHomeomorph p) {g : A → M} (hg : Continuous g)
    (hcomp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p ∘ g)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
  intro x
  obtain ⟨e,hex,hep⟩ := hlocal (g x)
  have he : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
    rw [← hep]
    exact hp.mdifferentiableOn
  have hei := mdifferentiableOn_symm he
  have hpx : p (g x) ∈ e.target := hep ▸ e.map_source hex
  have hdiff := (hei _ hpx).mdifferentiableAt (e.open_target.mem_nhds hpx)
  have hdiffcomp := hdiff.comp x (hcomp x)
  apply hdiffcomp.congr_of_eventuallyEq
  filter_upwards [hg.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hex)] with z hz
  exact (by simpa only [comp_apply, hep] using (e.left_inv hz).symm)

/-- The ordinary unique covering-space lift is holomorphic. -/
theorem exists_holomorphic_lift [TopologicalSpace A] [ChartedSpace ℂ A]
    [IsManifold 𝓘(ℂ) 1 A] [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : M → N} (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hc : IsCoveringMap p)
    {g : A → N} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (x : A) (w : M) (hw : p w = g x) :
    ∃ h : A → M, h x = w ∧ p ∘ h = g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
  obtain ⟨h,⟨h0,hfac⟩,_⟩ := hc.existsUnique_continuousMap_lifts ⟨g,hg.continuous⟩ x w hw
  refine ⟨h,h0,hfac,mdifferentiable_lift hp hc.isLocalHomeomorph h.continuous ?_⟩
  simpa only [hfac, ContinuousMap.coe_mk] using hg

end AreaDeficit.Surfaces
