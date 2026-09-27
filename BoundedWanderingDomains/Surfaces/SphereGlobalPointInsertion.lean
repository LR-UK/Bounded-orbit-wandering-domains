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

/-- The normalized estimate pulls back along a biholomorphism.  We use the
pulled-back finite coordinate as a global chart, so no separate area-change
formula is needed. -/
theorem uniformGlobalPointInsertionBound_of_diffeomorph_normalized
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
    [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [DecidableEq M]
    (p : DiscCover M)
    (e : M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ normalizedThricePuncturedSphere) :
    p.UniformGlobalPointInsertionBound (ENNReal.ofReal (2 * Real.pi)) := by
  classical
  let V : Opens ℂ̂ := normalizedThricePuncturedSphere
  have hVN : Nonempty V := by
    refine ⟨⟨((2 : ℂ) : ℂ̂), ?_⟩⟩
    simp [V, normalizedThricePuncturedSphere]
  let n : OpenPartialHomeomorph V ℂ :=
    RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr hVN
  have hn0 : RiemannSphere.coeOpenPartialHomeomorph.symm =
      chartAt ℂ (((0 : ℂ) : ℂ̂)) := by
    rw [RiemannSphere.chartAt_coe]
  have hnBase : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      RiemannSphere.coeOpenPartialHomeomorph.symm
      RiemannSphere.coeOpenPartialHomeomorph.symm.source := by
    rw [hn0]
    exact (mdifferentiable_chart (I := 𝓘(ℂ)) (((0 : ℂ) : ℂ̂))).1
  have hniBase : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      RiemannSphere.coeOpenPartialHomeomorph
      RiemannSphere.coeOpenPartialHomeomorph.symm.target := by
    rw [hn0]
    exact (mdifferentiable_chart (I := 𝓘(ℂ)) (((0 : ℂ) : ℂ̂))).2
  have hn : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) n n.source := by
    exact mdifferentiableOn_subtypeRestr hVN hnBase
  have hni : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) n.symm n.target := by
    exact mdifferentiableOn_subtypeRestr_symm hVN hniBase
  let eh : OpenPartialHomeomorph M V :=
    e.toHomeomorph.toOpenPartialHomeomorph
  let c : OpenPartialHomeomorph M ℂ := eh.trans n
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source := by
    intro x hx
    change x ∈ (eh.trans n).source at hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    have hnat := (hn (e x) hx.2).mdifferentiableAt
      (n.open_source.mem_nhds hx.2)
    have heat := e.mdifferentiable (by simp) x
    exact (hnat.comp x heat).mdifferentiableWithinAt
  have hci : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c.symm c.target := by
    intro z hz
    change z ∈ (eh.trans n).target at hz
    rw [OpenPartialHomeomorph.trans_target] at hz
    have hniat := (hni z hz.1).mdifferentiableAt
      (n.open_target.mem_nhds hz.1)
    have heat := e.symm.mdifferentiable (by simp) (n.symm z)
    exact (heat.comp z hniat).mdifferentiableWithinAt
  apply p.uniformGlobalPointInsertionBound_of_global_chart hc hci
  · intro x _
    change x ∈ (eh.trans n).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by simp [eh], ?_⟩
    simp only [mem_preimage]
    change e x ∈ n.source
    dsimp only [n]
    simp only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    change (e x : ℂ̂) ≠ (∞ : ℂ̂)
    intro hx
    have hp := (e x).property
    change (e x : ℂ̂) ∉
      ({(∞ : ℂ̂), ((0 : ℂ) : ℂ̂), ((1 : ℂ) : ℂ̂)} : Set ℂ̂) at hp
    exact hp (by simp [hx])
  · exact zero_ne_one
  · rintro ⟨h0, _⟩
    change 0 ∈ (eh.trans n).target at h0
    rw [OpenPartialHomeomorph.trans_target] at h0
    have hy := (n.symm 0).property
    have heq := RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr_symm_apply hVN h0.1
    change ((n.symm 0 : V) : ℂ̂) =
      RiemannSphere.coeOpenPartialHomeomorph 0 at heq
    rw [heq] at hy
    change ((0 : ℂ) : ℂ̂) ∈ V at hy
    exact hy (by simp [V, normalizedThricePuncturedSphere])
  · rintro ⟨h1, _⟩
    change 1 ∈ (eh.trans n).target at h1
    rw [OpenPartialHomeomorph.trans_target] at h1
    have hy := (n.symm 1).property
    have heq := RiemannSphere.coeOpenPartialHomeomorph.symm.subtypeRestr_symm_apply hVN h1.1
    change ((n.symm 1 : V) : ℂ̂) =
      RiemannSphere.coeOpenPartialHomeomorph 1 at heq
    rw [heq] at hy
    change ((1 : ℂ) : ℂ̂) ∈ V at hy
    exact hy (by simp [V, normalizedThricePuncturedSphere])

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.normalizedThricePuncturedSphere_uniformGlobalPointInsertionBound
#print axioms AreaDeficit.Surfaces.DiscCover.uniformGlobalPointInsertionBound_of_diffeomorph_normalized
