/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactBranchValues
import Mathlib.Topology.IsLocalHomeomorph

/-! # Local homeomorphisms away from surface branch values -/

open Set Function Filter Topology
open scoped Manifold Topology

namespace SurfaceDynamics

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

/-- A nonzero coordinate derivative of an open holomorphic surface map gives
a local homeomorphism at the corresponding point. -/
theorem isLocalHomeomorphOn_of_chart_deriv_ne_zero
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {S : Set M}
    (hregular : ∀ x ∈ S,
      ∃ (c : OpenPartialHomeomorph M ℂ) (d : OpenPartialHomeomorph N ℂ),
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source ∧
        x ∈ c.source ∧ f x ∈ d.source ∧
          deriv (d ∘ f ∘ c.symm) (c x) ≠ 0) :
    IsLocalHomeomorphOn f S := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro x hx
  obtain ⟨c, d, hc, hd, hxc, hfd, hder⟩ := hregular x hx
  have hgan := analyticAt_writtenInCharts hc hd hf hxc hfd
  obtain ⟨T, hT, hTinj⟩ :=
    (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero hgan).mpr hder
  let U : Set M := c.source ∩ c ⁻¹' T ∩ f ⁻¹' d.source
  have hU : U ∈ 𝓝 x := by
    exact inter_mem
      (inter_mem (c.open_source.mem_nhds hxc) ((c.continuousAt hxc) hT))
      ((hf x).continuousAt (d.open_source.mem_nhds hfd))
  have hinj : InjOn f U := by
    intro y hy z hz heq
    have hcoord : (d ∘ f ∘ c.symm) (c y) =
        (d ∘ f ∘ c.symm) (c z) := by
      simp only [comp_apply, c.left_inv hy.1.1, c.left_inv hz.1.1, heq]
    have hcyz : c y = c z := hTinj hy.1.2 hz.1.2 hcoord
    exact c.injOn hy.1.1 hz.1.1 hcyz
  have hxint : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  refine ⟨interior U, isOpen_interior.mem_nhds hxint, ?_⟩
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap]
  exact ⟨continuousOn_iff_continuous_domRestrict.mp hf.continuous.continuousOn,
    (hinj.mono interior_subset).injective,
    hopen.domRestrict isOpen_interior⟩

variable [LocallyCompactSpace M] [LocallyCompactSpace N] [T2Space N]
  [DecidableEq N] [IsManifold 𝓘(ℂ) 1 N]

/-- On a compact set, deleting one finite set of branch values makes the
open holomorphic map a local homeomorphism at every remaining point. -/
theorem exists_finite_branch_values_isLocalHomeomorphOn
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {L : Set M} (hL : IsCompact L) :
    ∃ E : Finset N,
      IsLocalHomeomorphOn f (L \ f ⁻¹' (E : Set N)) := by
  obtain ⟨E, hE⟩ := exists_finite_branch_values_on_compact hf hopen hL
  refine ⟨E, isLocalHomeomorphOn_of_chart_deriv_ne_zero hf hopen ?_⟩
  intro x hx
  exact hE x hx.1 hx.2

end SurfaceDynamics
