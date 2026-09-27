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

/-- A sphere domain contained in one global coordinate and omitting two
points in that coordinate has the sharp global insertion bound. -/
theorem sphereDomain_uniformGlobalPointInsertionBound_of_chart
    {U : Opens ℂ̂} [DecidableEq U] (p : DiscCover U)
    {a b : ℂ̂} (haU : a ∉ U) (hbU : b ∉ U)
    {g : OpenPartialHomeomorph ℂ̂ ℂ}
    (hg : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g g.source)
    (hgi : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g.symm g.target)
    (hUg : (U : Set ℂ̂) ⊆ g.source)
    (ha : a ∈ g.source) (hb : b ∈ g.source) (hab : a ≠ b) :
    p.UniformGlobalPointInsertionBound (ENNReal.ofReal (2 * Real.pi)) := by
  classical
  have hUN : Nonempty U := ⟨p.projection discZero⟩
  let c : OpenPartialHomeomorph U ℂ := g.subtypeRestr hUN
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  apply p.uniformGlobalPointInsertionBound_of_global_chart
      (c := c) (mdifferentiableOn_subtypeRestr hUN hg)
      (mdifferentiableOn_subtypeRestr_symm hUN hgi)
  · intro x _
    dsimp only [c]
    simp only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    exact hUg x.property
  · intro heq
    exact hab (g.injOn ha hb heq)
  · rintro ⟨hga, _⟩
    change g a ∈ (g.subtypeRestr hUN).target at hga
    have hy := ((g.subtypeRestr hUN).symm (g a)).property
    have heq := g.subtypeRestr_symm_apply hUN hga
    change (((g.subtypeRestr hUN).symm (g a) : U) : ℂ̂) =
      g.symm (g a) at heq
    rw [heq, g.left_inv ha] at hy
    exact haU hy
  · rintro ⟨hgb, _⟩
    change g b ∈ (g.subtypeRestr hUN).target at hgb
    have hy := ((g.subtypeRestr hUN).symm (g b)).property
    have heq := g.subtypeRestr_symm_apply hUN hgb
    change (((g.subtypeRestr hUN).symm (g b) : U) : ℂ̂) =
      g.symm (g b) at heq
    rw [heq, g.left_inv hb] at hy
    exact hbU hy

/-- The sphere with three specified points removed. -/
def sphereComplThree (a b c : ℂ̂) : Opens ℂ̂ :=
  ⟨({a, b, c} : Set ℂ̂)ᶜ,
    (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩

/-- Every three-punctured sphere has the sharp global one-point insertion
bound.  The pole chart at the third puncture contains the whole domain, while
the other two punctures supply the two omitted finite coordinate values. -/
theorem sphereComplThree_uniformGlobalPointInsertionBound
    {a b c : ℂ̂} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [DecidableEq (sphereComplThree a b c)]
    (p : DiscCover (sphereComplThree a b c)) :
    p.UniformGlobalPointInsertionBound (ENNReal.ofReal (2 * Real.pi)) := by
  classical
  let g : OpenPartialHomeomorph ℂ̂ ℂ := (AreaDeficit.spherePoleChart c).symm
  have hg : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g g.source := by
    intro z hz
    have hzc : z ≠ c := by
      simpa only [g, OpenPartialHomeomorph.symm_source,
        AreaDeficit.spherePoleChart_target, mem_compl_iff,
        mem_singleton_iff] using hz
    exact ((AreaDeficit.spherePoleChart_symm_contMDiffAt hzc).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt
  have hgi : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g.symm g.target := by
    exact ((AreaDeficit.spherePoleChart_contMDiff c).mdifferentiable
      (by simp)).mdifferentiableOn
  apply p.sphereDomain_uniformGlobalPointInsertionBound_of_chart
      (a := a) (b := b) (g := g) (by simp [sphereComplThree])
      (by simp [sphereComplThree]) hg hgi
  · intro z hz
    change z ∈ (AreaDeficit.spherePoleChart c).target
    rw [AreaDeficit.spherePoleChart_target]
    exact by
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hzc
      exact hz (by simp [sphereComplThree, hzc])
  · change a ∈ (AreaDeficit.spherePoleChart c).target
    simpa only [AreaDeficit.spherePoleChart_target, mem_compl_iff,
      mem_singleton_iff] using hac
  · change b ∈ (AreaDeficit.spherePoleChart c).target
    simpa only [AreaDeficit.spherePoleChart_target, mem_compl_iff,
      mem_singleton_iff] using hbc
  · exact hab

/-- The sharp insertion estimate on a three-anchor complement of any surface
biholomorphic to the sphere.  The canonical sphere atlas now agrees with the
uniformization atlas, so Möbius normalization supplies the required
biholomorphism to the normalized model directly. -/
theorem uniformGlobalPointInsertionBound_of_diffeomorph_sphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e : X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂)
    (U : Opens X) (hU : ∀ x : X, x ∈ U ↔ x ∉ ({a, b, c} : Set X))
    [DecidableEq U] (p : DiscCover U) :
    p.UniformGlobalPointInsertionBound (ENNReal.ofReal (2 * Real.pi)) := by
  classical
  obtain ⟨g, hga, hgb, hgc⟩ :=
    RiemannDynamics.exists_gl_smul_eq_zero_one_infty
      (e.injective.ne hab) (e.injective.ne hac) (e.injective.ne hbc)
  obtain ⟨eg, heg⟩ := RiemannDynamics.exists_gl_smul_diffeomorph g
  let h : X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂ := e.trans eg
  obtain ⟨V, hVimg, ⟨r⟩⟩ :=
    RiemannDynamics.exists_diffeomorph_opens_image h U
  have hV : V = normalizedThricePuncturedSphere := by
    apply Opens.ext
    rw [hVimg]
    have hUset : (U : Set X) = ({a, b, c} : Set X)ᶜ := by
      ext x
      exact hU x
    rw [hUset]
    change (h.toHomeomorph : X → ℂ̂) '' ({a, b, c} : Set X)ᶜ =
      ({(∞ : ℂ̂), ((0 : ℂ) : ℂ̂), ((1 : ℂ) : ℂ̂)} : Set ℂ̂)ᶜ
    rw [h.toHomeomorph.image_compl]
    congr 1
    change (h.toHomeomorph : X → ℂ̂) '' ({a, b, c} : Set X) =
      ({(∞ : ℂ̂), ((0 : ℂ) : ℂ̂), ((1 : ℂ) : ℂ̂)} : Set ℂ̂)
    have hea : h a = ((0 : ℂ) : ℂ̂) := by
      change eg (e a) = ((0 : ℂ) : ℂ̂)
      rw [heg]
      exact hga
    have heb : h b = ((1 : ℂ) : ℂ̂) := by
      change eg (e b) = ((1 : ℂ) : ℂ̂)
      rw [heg]
      exact hgb
    have hec : h c = (∞ : ℂ̂) := by
      change eg (e c) = (∞ : ℂ̂)
      rw [heg]
      exact hgc
    ext z
    simp [hea, heb, hec, or_comm, or_left_comm]
  subst V
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact p.uniformGlobalPointInsertionBound_of_diffeomorph_normalized r

end AreaDeficit.Surfaces.DiscCover
