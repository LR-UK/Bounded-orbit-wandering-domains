/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.SeparatingCutoff
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Geometry.Manifold.Complex

/-! # Localisation of the cutoff's second derivatives

The chart Laplacian is a coordinate coefficient, not an intrinsic scalar
Laplacian. Its vanishing on locally constant regions is chart-independent.
This file proves compact localisation and separation from the removed set;
it does not assume or assert a hyperbolic area estimate.
-/

open Set Function Filter InnerProductSpace
open scoped Topology Manifold

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

noncomputable def chartLaplacian (u : M → ℝ) (x : M) : ℝ :=
  Laplacian.laplacian (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

omit [ChartedSpace ℂ M] in
/-- Local constancy forces the Laplacian to vanish in every coordinate. -/
theorem laplacian_in_chart_eq_zero_of_locally_const {u : M → ℝ} {x : M}
    {c : ℝ} (h : ∀ᶠ y in 𝓝 x, u y = c)
    (e : OpenPartialHomeomorph M ℂ) (hx : x ∈ e.source) :
    Laplacian.laplacian (u ∘ e.symm) (e x) = 0 := by
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [e.left_inv hx] using (e.continuousAt_symm (e.map_source hx)).tendsto
  have he : u ∘ e.symm =ᶠ[𝓝 (e x)] (fun _ => c) := ht.eventually h
  simpa using (laplacian_congr_nhds he).eq_of_nhds

theorem chartLaplacian_eq_zero_of_locally_const {u : M → ℝ} {x : M}
    {c : ℝ} (h : ∀ᶠ y in 𝓝 x, u y = c) : chartLaplacian u x = 0 :=
  laplacian_in_chart_eq_zero_of_locally_const h _ (mem_chart_source ℂ x)

/-- The topological support stays inside any closed transition region. -/
theorem tsupport_chartLaplacian_subset [T2Space M] {u : M → ℝ} {D : Set M}
    (hD : IsClosed D) (h : ∀ x ∉ D, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, u y = c) :
    tsupport (chartLaplacian u) ⊆ D := by
  apply closure_minimal _ hD
  intro x hx
  by_contra hxd
  obtain ⟨c,hc⟩ := h x hxd
  exact hx (chartLaplacian_eq_zero_of_locally_const hc)

theorem hasCompactSupport_chartLaplacian [T2Space M] {u : M → ℝ} {D : Set M}
    (hD : IsCompact D) (h : ∀ x ∉ D, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, u y = c) :
    HasCompactSupport (chartLaplacian u) :=
  hD.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartLaplacian_subset hD.isClosed h)

/-- The Laplacian support misses every set near which the cutoff is constant. -/
theorem disjoint_tsupport_chartLaplacian_of_const_near {u : M → ℝ} {K : Set M}
    {c : ℝ} (h : ∀ᶠ y in 𝓝ˢ K, u y = c) :
    Disjoint (tsupport (chartLaplacian u)) K := by
  obtain ⟨W,hW,hKW,hWc⟩ := eventually_nhdsSet_iff_exists.mp h
  have hz : ∀ x ∈ W, chartLaplacian u x = 0 := by
    intro x hx
    exact chartLaplacian_eq_zero_of_locally_const
      (mem_of_superset (hW.mem_nhds hx) hWc)
  have hs : tsupport (chartLaplacian u) ⊆ Wᶜ := by
    apply closure_minimal _ hW.isClosed_compl
    intro x hx hw
    exact hx (hz x hw)
  exact disjoint_left.mpr (fun x hx hK => hs hx (hKW hK))

end AreaDeficit.Surfaces
