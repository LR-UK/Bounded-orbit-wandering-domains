module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainChartDensity

@[expose] public section

/-! # A small coordinate neighbourhood with two omitted coordinate values -/
open Set Function Filter Metric
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M]

theorem exists_small_chart_domain {c : OpenPartialHomeomorph M ℂ}
    {a : M} (ha : a ∈ c.source) :
    ∃ D : TopologicalSpace.Opens M, a ∈ D ∧ (D : Set M) ⊆ c.source ∧
      ∃ b d : ℂ, b ≠ d ∧ b ∉ domainChartSet D c ∧ d ∉ domainChartSet D c := by
  let D : TopologicalSpace.Opens M :=
    ⟨c.source ∩ c ⁻¹' ball (c a) 1,c.isOpen_inter_preimage isOpen_ball⟩
  refine ⟨D,⟨ha,by simp⟩,inter_subset_left,c a + 2,c a + 3,?_,?_,?_⟩
  · intro h
    have : (2 : ℂ) = 3 := add_left_cancel h
    norm_num at this
  · intro h
    have hh : c (c.symm (c a + 2)) ∈ ball (c a) 1 := h.2.2
    rw [c.right_inv h.1] at hh
    norm_num [mem_ball,dist_eq_norm] at hh
  · intro h
    have hh : c (c.symm (c a + 3)) ∈ ball (c a) 1 := h.2.2
    rw [c.right_inv h.1] at hh
    norm_num [mem_ball,dist_eq_norm] at hh

end AreaDeficit.Surfaces
