/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SmoothSurface
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Compactly supported chart readings -/

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]

/-- Zero extension of a scalar function through an arbitrary surface chart. -/
noncomputable def chartZeroExtensionIn
    (e : OpenPartialHomeomorph M ℂ) (v : M → ℝ) : ℂ → ℝ := by
  classical
  exact e.target.piecewise (v ∘ e.symm) 0

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M] [T2Space M] in
theorem chartZeroExtensionIn_eq {e : OpenPartialHomeomorph M ℂ}
    {v : M → ℝ} {z : ℂ} (hz : z ∈ e.target) :
    chartZeroExtensionIn e v z = v (e.symm z) := by
  simp [chartZeroExtensionIn, hz]

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M] [T2Space M] in
theorem support_chartZeroExtensionIn_subset
    {e : OpenPartialHomeomorph M ℂ} {v : M → ℝ} :
    support (chartZeroExtensionIn e v) ⊆ e '' support v := by
  intro z hz
  have hzt : z ∈ e.target := by
    by_contra h
    exact hz (by simp [chartZeroExtensionIn, h])
  refine ⟨e.symm z, ?_, e.right_inv hzt⟩
  exact fun hv => hz (by simp [chartZeroExtensionIn, hzt, hv])

omit [IsManifold 𝓘(ℂ) 1 M] [T2Space M] in
/-- Generic chart form of the zero-extension lemma. -/
theorem contDiff_chartZeroExtensionIn
    {e : OpenPartialHomeomorph M ℂ} {v : M → ℝ}
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v) (hvsource : tsupport v ⊆ e.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M) :
    ContDiff ℝ 2 (chartZeroExtensionIn e v) := by
  have hK : IsCompact (e '' tsupport v) :=
    hvcompact.image_of_continuousOn (e.continuousOn.mono hvsource)
  have hsupp : tsupport (chartZeroExtensionIn e v) ⊆ e '' tsupport v := by
    apply closure_minimal
    · exact support_chartZeroExtensionIn_subset.trans (image_mono subset_closure)
    · exact hK.isClosed
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (chartZeroExtensionIn e v)
  · obtain ⟨x, hx, rfl⟩ := hsupp hz
    have hxs : x ∈ e.source := hvsource hx
    have hxt := e.map_source hxs
    have hlocal : chartZeroExtensionIn e v =ᶠ[𝓝 (e x)] v ∘ e.symm := by
      filter_upwards [e.open_target.mem_nhds hxt] with z hz
      exact chartZeroExtensionIn_eq hz
    apply ContDiffAt.congr_of_eventuallyEq _ hlocal
    rw [← contMDiffAt_iff_contDiffAt]
    exact hv.contMDiffAt.comp _ (contMDiffAt_symm_of_mem_maximalAtlas he hxt)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] [T2Space M] in
theorem hasCompactSupport_chartZeroExtensionIn
    {e : OpenPartialHomeomorph M ℂ} {v : M → ℝ}
    (hvcompact : HasCompactSupport v) (hvsource : tsupport v ⊆ e.source) :
    HasCompactSupport (chartZeroExtensionIn e v) := by
  have hK : IsCompact (e '' tsupport v) :=
    hvcompact.image_of_continuousOn (e.continuousOn.mono hvsource)
  exact hK.of_isClosed_subset isClosed_closure <|
    closure_minimal
      (support_chartZeroExtensionIn_subset.trans (image_mono subset_closure))
      hK.isClosed

/-- Extend a scalar function written in the chart at `a` by zero outside the
chart target. -/
noncomputable def chartZeroExtension (a : M) (v : M → ℝ) : ℂ → ℝ :=
  by
    classical
    exact (chartAt ℂ a).target.piecewise (v ∘ (chartAt ℂ a).symm) 0

omit [IsManifold 𝓘(ℂ, ℂ) 1 M] [T2Space M] in
theorem chartZeroExtension_eq {a : M} {v : M → ℝ} {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    chartZeroExtension a v z = v ((chartAt ℂ a).symm z) := by
  simp [chartZeroExtension, hz]

omit [IsManifold 𝓘(ℂ, ℂ) 1 M] [T2Space M] in
theorem support_chartZeroExtension_subset {a : M} {v : M → ℝ} :
    support (chartZeroExtension a v) ⊆ (chartAt ℂ a) '' support v := by
  intro z hz
  have hzt : z ∈ (chartAt ℂ a).target := by
    by_contra h
    exact hz (by simp [chartZeroExtension, h])
  refine ⟨(chartAt ℂ a).symm z, ?_, (chartAt ℂ a).right_inv hzt⟩
  exact fun hv => hz (by simp [chartZeroExtension, hzt, hv])

omit [T2Space M] in
/-- A smooth compactly supported surface function whose topological support
lies in one chart has a globally `C²` zero-extended chart reading. -/
theorem contDiff_chartZeroExtension
    {a : M} {v : M → ℝ}
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v)
    (hvsource : tsupport v ⊆ (chartAt ℂ a).source) :
    ContDiff ℝ 2 (chartZeroExtension a v) := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
  have hK : IsCompact ((chartAt ℂ a) '' tsupport v) := by
    exact hvcompact.image_of_continuousOn
      ((chartAt ℂ a).continuousOn.mono hvsource)
  have hsupp : tsupport (chartZeroExtension a v) ⊆
      (chartAt ℂ a) '' tsupport v := by
    apply closure_minimal
    · exact (support_chartZeroExtension_subset).trans
        (image_mono subset_closure)
    · exact hK.isClosed
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (chartZeroExtension a v)
  · obtain ⟨x, hx, rfl⟩ := hsupp hz
    have hxs : x ∈ (chartAt ℂ a).source := hvsource hx
    have hxt := (chartAt ℂ a).map_source hxs
    have he : chartZeroExtension a v =ᶠ[𝓝 ((chartAt ℂ a) x)]
        v ∘ (chartAt ℂ a).symm := by
      filter_upwards [(chartAt ℂ a).open_target.mem_nhds hxt] with z hz
      exact chartZeroExtension_eq hz
    apply ContDiffAt.congr_of_eventuallyEq _ he
    rw [← contMDiffAt_iff_contDiffAt]
    exact hv.contMDiffAt.comp _
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (2 : ℕ∞))).contMDiffAt
        ((chartAt ℂ a).open_target.mem_nhds hxt))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

omit [IsManifold 𝓘(ℂ) 1 M] [T2Space M] in
theorem hasCompactSupport_chartZeroExtension
    {a : M} {v : M → ℝ} (hvcompact : HasCompactSupport v)
    (hvsource : tsupport v ⊆ (chartAt ℂ a).source) :
    HasCompactSupport (chartZeroExtension a v) := by
  have hK : IsCompact ((chartAt ℂ a) '' tsupport v) :=
    hvcompact.image_of_continuousOn ((chartAt ℂ a).continuousOn.mono hvsource)
  exact hK.of_isClosed_subset isClosed_closure <|
    closure_minimal
      ((support_chartZeroExtension_subset).trans (image_mono subset_closure))
      hK.isClosed

end AreaDeficit.Surfaces
