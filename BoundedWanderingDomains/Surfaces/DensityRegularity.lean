module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.CoveringDensity

@[expose] public section

/-! # Smoothness and curvature of the intrinsic surface density

A local inverse branch expresses the density as a pullback of the disc
density. In particular it is C² and satisfies the curvature −1 equation.
-/

open Set Function Filter Metric
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- Density as a function of the complex coordinate, rather than of the
point on the abstract surface. -/
noncomputable def chartDensity (p : DiscCover M) (c : OpenPartialHomeomorph M ℂ) : ℂ → ℝ :=
  fun t => p.density c (c.symm t)

theorem local_density_expression (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) {x : M} (hx : x ∈ c.source) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (c x) ∧ h (c x) ∈ ball 0 1 ∧
      deriv h (c x) ≠ 0 ∧
      p.chartDensity c =ᶠ[𝓝 (c x)] (fun t => ‖deriv h t‖ * discDensity (h t)) := by
  obtain ⟨w,rfl⟩ := p.surjective x
  obtain ⟨V,hV,hwV,hVD,hf,hinj,hchart⟩ :=
    coordinate_local_injective p.holomorphic p.covering.isLocalHomeomorph hc hx
  let f := planeExtension (c ∘ p.projection)
  have hO : IsOpen (f '' V) := TauCeti.isOpen_image_of_differentiableOn_of_injOn hV hf hinj
  let h := invFunOn f V
  have hh : DifferentiableOn ℂ h (f '' V) := hf.invFunOn hV hinj
  have hfw : f w = c (p.projection w) := planeExtension_coe _ w
  have hpw : c (p.projection w) ∈ f '' V := hfw ▸ mem_image_of_mem f hwV
  have hh0 : h (c (p.projection w)) = w := by
    rw [← hfw]
    exact hinj.leftInvOn_invFunOn hwV
  have hd0 : deriv h (c (p.projection w)) = (deriv f w)⁻¹ := by
    rw [← hfw]
    exact (TauCeti.hasDerivAt_invFunOn hf hV hinj hwV).deriv
  refine ⟨h, hh.analyticAt (hO.mem_nhds hpw), ?_, ?_, ?_⟩
  · rw [hh0]
    exact w.2
  · rw [hd0]
    exact inv_ne_zero (p.coordinate_deriv_ne_zero hc hx)
  · filter_upwards [hO.mem_nhds hpw] with t ht
    have hht : h t ∈ V := invFunOn_mem ht
    have hpt : f (h t) = t := invFunOn_eq ht
    let v : unitDisc := ⟨h t,hVD hht⟩
    have hv : p.projection v ∈ c.source := hchart v hht
    have hcv : c (p.projection v) = t := by
      exact (planeExtension_coe (c ∘ p.projection) v).symm.trans hpt
    have hinv : c.symm t = p.projection v := by rw [← hcv, c.left_inv hv]
    have hd : deriv h t = (deriv f (h t))⁻¹ := by
      have hd' : deriv h (f (h t)) = (deriv f (h t))⁻¹ :=
        (TauCeti.hasDerivAt_invFunOn hf hV hinj hht).deriv
      rw [hpt] at hd'
      exact hd'
    change p.density c (c.symm t) = _
    rw [hinv, p.density_eq_fibre hc hv, fibreDensity, hd, norm_inv]
    exact div_eq_inv_mul _ _

theorem chartDensity_pos (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) {z : ℂ} (hz : z ∈ c.target) :
    0 < p.chartDensity c z := p.density_pos hc (c.map_target hz)

theorem chartDensity_contDiffAt (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) {z : ℂ} (hz : z ∈ c.target) :
    ContDiffAt ℝ 2 (p.chartDensity c) z := by
  obtain ⟨h,hh,hD,hd,he⟩ := p.local_density_expression hc (c.map_target hz)
  rw [c.right_inv hz] at hh hD hd he
  exact (pullback_density_contDiffAt (discDensity_contDiffAt (mem_ball_zero_iff.mp hD))
    hh hd).congr_of_eventuallyEq he

theorem chartDensity_curvature (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) {z : ℂ} (hz : z ∈ c.target) :
    Laplacian.laplacian (fun t => Real.log (p.chartDensity c t)) z =
      (p.chartDensity c z)^2 := by
  obtain ⟨h,hh,hD,hd,he⟩ := p.local_density_expression hc (c.map_target hz)
  rw [c.right_inv hz] at hh hD hd he
  have hn : ‖h z‖ < 1 := mem_ball_zero_iff.mp hD
  have hlog := he.fun_comp Real.log
  simp only [Function.comp_def] at hlog
  rw [(InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds, he.eq_of_nhds]
  exact pullback_density_curvature (discDensity_contDiffAt hn) (discDensity_pos hn)
    (discDensity_curvature hn) hh hd

end AreaDeficit.Surfaces.DiscCover
