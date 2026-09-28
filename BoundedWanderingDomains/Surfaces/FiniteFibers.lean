/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OpenMapping
import Mathlib.Topology.DiscreteSubset

/-! # Finite fibres of open holomorphic surface maps -/

open Set Function Filter
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-- Every fibre of an open holomorphic map between analytic surfaces is a
discrete subset of the source. -/
theorem isDiscrete_fiber_of_isOpenMap_of_mdifferentiable {f : X → Y}
    (hopen : IsOpenMap f) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (y : Y) :
    IsDiscrete {x | f x = y} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  let e := extChartAt 𝓘(ℂ) x
  let d := extChartAt 𝓘(ℂ) (f x)
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  have hgan : AnalyticAt ℂ g (e x) := analyticAt_writtenInExtChartAt hf x
  have hgnc : ¬ g =ᶠ[𝓝 (e x)] fun _ => g (e x) :=
    not_eventuallyEq_writtenInExtChartAt hf hopen x
  have hne : ∀ᶠ z in 𝓝[≠] (e x), g z ≠ g (e x) :=
    (hgan.eventually_eq_or_eventually_ne analyticAt_const).resolve_left hgnc
  rw [eventually_nhdsWithin_iff] at hne
  rcases mem_nhds_iff.mp hne with ⟨V, hVsub, hVopen, hxV⟩
  refine ⟨e.source ∩ e ⁻¹' V, isOpen_extChartAt_preimage' x hVopen, ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨⟨hzs, hzV⟩, hzy⟩
    have hgeq : g (e z) = g (e x) := by
      simp only [g, e, writtenInExtChartAt, Function.comp_apply,
        e.left_inv hzs, extChartAt_to_inv]
      exact congrArg d ((show f z = y from hzy).trans (show f x = y from hx).symm)
    have heq : e z = e x := by
      by_contra hnecoord
      exact (hVsub hzV hnecoord) hgeq
    exact Set.mem_singleton_iff.mpr
      (e.injOn hzs (mem_extChartAt_source x) heq)
  · rintro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨⟨mem_extChartAt_source x, hxV⟩, hx⟩

/-- A fibre of an open holomorphic surface map meets every compact set in a
finite set. -/
theorem finite_compact_inter_fiber_of_isOpenMap_of_mdifferentiable
    [T2Space Y] {f : X → Y} (hopen : IsOpenMap f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {K : Set X}
    (hK : IsCompact K) (y : Y) :
    (K ∩ {x | f x = y}).Finite := by
  exact (hK.inter_right (isClosed_eq hf.continuous continuous_const)).finite
    ((isDiscrete_fiber_of_isOpenMap_of_mdifferentiable hopen hf y).mono inter_subset_right)

end SurfaceDynamics
