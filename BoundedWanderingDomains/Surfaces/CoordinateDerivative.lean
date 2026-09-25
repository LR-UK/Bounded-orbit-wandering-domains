/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.PlaneReading

/-! # Nonvanishing coordinate derivatives of holomorphic local homeomorphisms -/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- A coordinate reading is injective and holomorphic on a sufficiently
small plane neighbourhood, whose image stays in the chart source. -/
theorem coordinate_local_injective {U : TopologicalSpace.Opens ℂ} {p : U → M}
    (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hl : IsLocalHomeomorph p)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {w : U} (hw : p w ∈ c.source) :
    ∃ W : Set ℂ, IsOpen W ∧ (w : ℂ) ∈ W ∧ W ⊆ U ∧
      DifferentiableOn ℂ (planeExtension (c ∘ p)) W ∧
      InjOn (planeExtension (c ∘ p)) W ∧
      ∀ (z : U), (z : ℂ) ∈ W → p z ∈ c.source := by
  obtain ⟨e,hew,hep⟩ := hl w
  let V : Set U := e.source ∩ p ⁻¹' c.source
  have hV : IsOpen V := e.open_source.inter (c.open_source.preimage hp.continuous)
  have hwV : w ∈ V := ⟨hew,hw⟩
  let W : Set ℂ := Subtype.val '' V
  have hW : IsOpen W := U.isOpen.isOpenMap_subtype_val V hV
  refine ⟨W,hW,⟨w,hwV,rfl⟩,?_,?_,?_,?_⟩
  · rintro z ⟨v,_,rfl⟩
    exact v.2
  · rintro z ⟨v,hv,rfl⟩
    apply DifferentiableAt.differentiableWithinAt
    apply planeExtension_mdifferentiableAt
    exact ((hc _ hv.2).mdifferentiableAt (c.open_source.mem_nhds hv.2)).comp v (hp v)
  · rintro z ⟨v,hv,rfl⟩ z' ⟨v',hv',rfl⟩ heq
    simp only [planeExtension_coe, comp_apply] at heq
    apply congrArg Subtype.val
    apply e.injOn hv.1 hv'.1
    rw [← hep]
    exact c.injOn hv.2 hv'.2 heq
  · rintro z ⟨v,hv,he⟩
    have hvz : v = z := Subtype.ext he
    have hv' : p v ∈ c.source := hv.2
    rw [hvz] at hv'
    exact hv'

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- A holomorphic local homeomorphism has nonzero derivative in every
holomorphic target coordinate. -/
theorem coordinate_deriv_ne_zero {U : TopologicalSpace.Opens ℂ} {p : U → M}
    (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hl : IsLocalHomeomorph p)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {w : U} (hw : p w ∈ c.source) :
    deriv (planeExtension (c ∘ p)) w ≠ 0 := by
  obtain ⟨W,hW,hwW,_,hd,hi,_⟩ := coordinate_local_injective hp hl hc hw
  exact TauCeti.deriv_ne_zero_of_injOn hd hW hi hwW

/-- Holomorphic coordinate reading of a disc cover at a point. -/
theorem DiscCover.coordinate_differentiableAt (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {w : unitDisc} (hw : p.projection w ∈ c.source) :
    DifferentiableAt ℂ (planeExtension (c ∘ p.projection)) w :=
  planeExtension_mdifferentiableAt
    (((hc _ hw).mdifferentiableAt (c.open_source.mem_nhds hw)).comp w (p.holomorphic w))

theorem DiscCover.coordinate_deriv_ne_zero (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {w : unitDisc} (hw : p.projection w ∈ c.source) :
    deriv (planeExtension (c ∘ p.projection)) w ≠ 0 :=
  AreaDeficit.Surfaces.coordinate_deriv_ne_zero p.holomorphic p.covering.isLocalHomeomorph hc hw

end AreaDeficit.Surfaces
