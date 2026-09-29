module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SmoothSurface
public import BoundedWanderingDomains.Surfaces.ChartZeroExtension
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

@[expose] public section

/-! # Compactly supported planar functions pulled back through a chart -/

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]

/-- Pull a planar function back through a surface chart and extend it by
zero outside the chart source. -/
noncomputable def chartPullbackExtension
    (e : OpenPartialHomeomorph M ℂ) (g : ℂ → ℝ) : M → ℝ := by
  classical
  exact e.source.piecewise (g ∘ e) 0

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M] [T2Space M] in
theorem chartPullbackExtension_eq {e : OpenPartialHomeomorph M ℂ}
    {g : ℂ → ℝ} {x : M} (hx : x ∈ e.source) :
    chartPullbackExtension e g x = g (e x) := by
  simp [chartPullbackExtension, hx]

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M] [T2Space M] in
theorem support_chartPullbackExtension_subset
    {e : OpenPartialHomeomorph M ℂ} {g : ℂ → ℝ} :
    support (chartPullbackExtension e g) ⊆ e.symm '' support g := by
  intro x hx
  have hxs : x ∈ e.source := by
    by_contra h
    exact hx (by simp [chartPullbackExtension, h])
  refine ⟨e x, ?_, e.left_inv hxs⟩
  exact fun hg => hx (by simp [chartPullbackExtension, hxs, hg])

theorem contMDiff_chartPullbackExtension
    {e : OpenPartialHomeomorph M ℂ} {g : ℂ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgcompact : HasCompactSupport g)
    (hgtarget : tsupport g ⊆ e.target)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (chartPullbackExtension e g) := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
  have hK : IsCompact (e.symm '' tsupport g) :=
    hgcompact.image_of_continuousOn (e.symm.continuousOn.mono hgtarget)
  have hsupp : tsupport (chartPullbackExtension e g) ⊆
      e.symm '' tsupport g := by
    apply closure_minimal
    · exact support_chartPullbackExtension_subset.trans (image_mono subset_closure)
    · exact hK.isClosed
  intro x
  by_cases hx : x ∈ tsupport (chartPullbackExtension e g)
  · obtain ⟨z, hz, rfl⟩ := hsupp hx
    have hzt : z ∈ e.target := hgtarget hz
    have hzs : e.symm z ∈ e.source := e.map_target hzt
    have hlocal : chartPullbackExtension e g =ᶠ[𝓝 (e.symm z)] g ∘ e := by
      filter_upwards [e.open_source.mem_nhds hzs] with y hy
      exact chartPullbackExtension_eq hy
    apply ContMDiffAt.congr_of_eventuallyEq _ hlocal
    have hge : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 g z := by
      rw [contMDiffAt_iff_contDiffAt]
      exact hg.contDiffAt
    have hge' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 g (e (e.symm z)) := by
      simpa only [e.right_inv hzt] using hge
    exact hge'.comp (e.symm z) (contMDiffAt_of_mem_maximalAtlas he hzs)
  · exact contMDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hx)

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] in
theorem hasCompactSupport_chartPullbackExtension
    {e : OpenPartialHomeomorph M ℂ} {g : ℂ → ℝ}
    (hgcompact : HasCompactSupport g) (hgtarget : tsupport g ⊆ e.target) :
    HasCompactSupport (chartPullbackExtension e g) := by
  have hK : IsCompact (e.symm '' tsupport g) :=
    hgcompact.image_of_continuousOn (e.symm.continuousOn.mono hgtarget)
  exact hK.of_isClosed_subset isClosed_closure <|
    closure_minimal
      (support_chartPullbackExtension_subset.trans (image_mono subset_closure))
      hK.isClosed

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] [T2Space M] in
/-- Pulling a planar function back through a chart and then reading it in
the same chart recovers the original zero-extended planar function. -/
theorem chartZeroExtensionIn_chartPullbackExtension
    {e : OpenPartialHomeomorph M ℂ} {g : ℂ → ℝ}
    (hgtarget : tsupport g ⊆ e.target) :
    chartZeroExtensionIn e (chartPullbackExtension e g) = g := by
  funext z
  by_cases hz : z ∈ e.target
  · rw [chartZeroExtensionIn_eq hz,
      chartPullbackExtension_eq (e.map_target hz), e.right_inv hz]
  · have hg : g z = 0 := by
      by_contra hgz
      exact hz (hgtarget (subset_closure hgz))
    simp [chartZeroExtensionIn, hz, hg]

end AreaDeficit.Surfaces
