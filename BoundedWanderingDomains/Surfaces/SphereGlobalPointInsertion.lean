/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.GlobalPointInsertion
import BoundedWanderingDomains.Surfaces.SpherePunctureCover
import BoundedWanderingDomains.SphereHyperbolicArea

/-! # Global point insertion on the normalized punctured sphere -/

open Set Function TopologicalSpace OnePoint
open scoped Manifold ENNReal ContDiff

namespace AreaDeficit.Surfaces.DiscCover

/-- The normalized thrice-punctured sphere has the sharp global one-point
insertion bound.  Its whole surface lies in the finite sphere chart, while
the coordinate values zero and one are omitted. -/
theorem normalizedThricePuncturedSphere_uniformGlobalPointInsertionBound
    [DecidableEq normalizedThricePuncturedSphere]
    (p : DiscCover normalizedThricePuncturedSphere) :
    p.UniformGlobalPointInsertionBound (ENNReal.ofReal (2 * Real.pi)) := by
  classical
  let U : Opens ℂ̂ := normalizedThricePuncturedSphere
  have hUN : Nonempty U := by
    refine ⟨⟨((2 : ℂ) : ℂ̂), ?_⟩⟩
    simp [U, normalizedThricePuncturedSphere]
  let c : OpenPartialHomeomorph U ℂ :=
    RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hUN
  have hc0 : RiemannSphere.coeOpenPartialHomeomorph.symm =
      chartAt ℂ (((0 : ℂ) : ℂ̂)) := by
    rw [RiemannSphere.chartAt_coe]
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      RiemannSphere.coeOpenPartialHomeomorph.symm
      RiemannSphere.coeOpenPartialHomeomorph.symm.source := by
    rw [hc0]
    exact (mdifferentiable_chart (I := 𝓘(ℂ)) (((0 : ℂ) : ℂ̂))).1
  have hci : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      RiemannSphere.coeOpenPartialHomeomorph
      RiemannSphere.coeOpenPartialHomeomorph.symm.target := by
    rw [hc0]
    exact (mdifferentiable_chart (I := 𝓘(ℂ)) (((0 : ℂ) : ℂ̂))).2
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  apply p.uniformGlobalPointInsertionBound_of_global_chart
      (c := c) (mdifferentiableOn_subtypeRestr hUN hc)
      (mdifferentiableOn_subtypeRestr_symm hUN hci)
  · intro x _
    dsimp only [c]
    simp only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    change (x : ℂ̂) ≠ (∞ : ℂ̂)
    exact fun hx =>
      x.property (by simp [U, normalizedThricePuncturedSphere, hx])
  · exact zero_ne_one
  · rintro ⟨h0, _⟩
    change 0 ∈ (RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hUN).target at h0
    have hy := ((RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hUN).symm 0).property
    have heq := RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr_symm_apply hUN h0
    change (((RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hUN).symm 0 : U) : ℂ̂) =
      RiemannSphere.coeOpenPartialHomeomorph 0 at heq
    rw [heq] at hy
    change ((0 : ℂ) : ℂ̂) ∈ U at hy
    exact hy (by simp [U, normalizedThricePuncturedSphere])
  · rintro ⟨h1, _⟩
    change 1 ∈ (RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hUN).target at h1
    have hy := ((RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hUN).symm 1).property
    have heq := RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr_symm_apply hUN h1
    change (((RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hUN).symm 1 : U) : ℂ̂) =
      RiemannSphere.coeOpenPartialHomeomorph 1 at heq
    rw [heq] at hy
    change ((1 : ℂ) : ℂ̂) ∈ U at hy
    exact hy (by simp [U, normalizedThricePuncturedSphere])

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.normalizedThricePuncturedSphere_uniformGlobalPointInsertionBound
