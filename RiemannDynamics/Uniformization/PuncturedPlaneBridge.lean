/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.

The projection-smoothness argument adapts Will (Ziang) Li's proof in
RiemannDynamics/Uniformization/Fuchsian.lean (Apache 2.0).
-/
import RiemannDynamics.Uniformization.CoverCountable
import BoundedWanderingDomains.DiscCoveringMetric
import FunctionTheory.Conformal.LittlePicardBloch

open Set Metric Function Filter Topology TopologicalSpace
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

namespace RiemannDynamics

theorem contMDiff_pathCoverProj {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] (x₀ : M) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (pathCoverProj x₀) := by
  intro pc
  obtain ⟨e, he, f, hf, hpc, hp, hm, hc⟩ := exists_charts_pathCoverProj_comm x₀ pc
  have hA := contMDiffAt_of_mem_maximalAtlas he hpc
  have htarget : e pc ∈ f.target := by
    rw [← hc pc hpc]
    exact f.map_source hp
  have hB := contMDiffAt_symm_of_mem_maximalAtlas hf htarget
  have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun qc : PathCover x₀ => f.symm (e qc)) pc := hB.comp pc hA
  refine hF.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hpc) fun qc hqc => ?_)
  rw [← hc qc hqc]
  exact (f.left_inv (hm qc hqc)).symm

/-- Convert a manifold-valued disc covering to the existing plane-function
interface; the extension outside the disc plays no part in the theorem. -/
theorem exists_plane_disc_covering (U : Opens ℂ)
    (π : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) → U)
    (hd : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π)
    (hc : IsCoveringMap π) (hs : Surjective π) :
    ∃ p : ℂ → ℂ, AreaDeficit.IsHolomorphicDiscCovering p U := by
  classical
  let D : Opens ℂ := ⟨ball 0 1, isOpen_ball⟩
  let p : ℂ → ℂ := fun z => if h : z ∈ D then (π ⟨z, h⟩ : ℂ) else 0
  have he : ∀ w : D, p w = (π w : ℂ) := fun w => by simp [p, w.2]
  have hsm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun w : D => p w) := by
    have H := contMDiff_subtype_val.comp hd
    exact H.congr (fun w => he w)
  refine ⟨p, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    have h := (contMDiffAt_subtype_iff.mp (hsm ⟨w, hw⟩)).contDiffAt
    exact (h.differentiableAt (by simp)).differentiableWithinAt
  · intro w hw
    change p w ∈ U
    rw [he ⟨w, hw⟩]
    exact (π ⟨w, hw⟩).2
  · intro z hz
    obtain ⟨w, hw⟩ := hs ⟨z, hz⟩
    exact ⟨w, w.2, (he w).trans (congrArg Subtype.val hw)⟩
  · change IsCoveringMapOn (fun w : D => p w) (U : Set ℂ)
    have hcov : IsCoveringMapOn (fun w : D => (π w : ℂ)) (U : Set ℂ) := by
      intro z hz
      exact ((hc ⟨z, hz⟩).subtypeVal_comp (U : Set ℂ) U.isOpen).to_isEvenlyCovered_preimage
    simpa only [he] using hcov

/-- The plane and sphere alternatives of uniformisation are excluded for
an open plane domain omitting two points. Little Picard excludes the plane;
compactness and connectedness of the ambient plane exclude the sphere. -/
theorem exists_disc_covering_of_models (U : Opens ℂ) [ConnectedSpace U]
    (x₀ : U) (hinf : (U : Set ℂ).Infinite)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hmodel :
      Nonempty (PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯
        ↥(⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)) ∨
      Nonempty (PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
      Nonempty (PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂)) :
    ∃ p : ℂ → ℂ, AreaDeficit.IsHolomorphicDiscCovering p U := by
  let : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace ℂ U
  let : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
  have hproj := contMDiff_pathCoverProj x₀
  have hsurj : Surjective (pathCoverProj x₀) := fun y =>
    ⟨⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)⟩, rfl⟩
  rcases hmodel with hmodel | hmodel | hmodel
  · obtain ⟨E⟩ := hmodel
    exact exists_plane_disc_covering U (pathCoverProj x₀ ∘ E.symm)
      (hproj.comp E.symm.contMDiff)
      ((pathCoverProj_isCoveringMap x₀).comp_homeomorph E.toHomeomorph.symm)
      (hsurj.comp E.symm.surjective)
  · obtain ⟨E⟩ := hmodel
    let F : ℂ → ℂ := fun z => ((pathCoverProj (M := U) x₀ (E.symm z) : U) : ℂ)
    have hF : Differentiable ℂ F :=
      (contMDiff_subtype_val.comp (hproj.comp E.symm.contMDiff)).contDiff.differentiable
        (by simp)
    obtain ⟨c, hc⟩ := FunctionTheory.exists_eq_const_of_two_omitted_values hF hab
      (fun z he => ha (he ▸ (pathCoverProj x₀ (E.symm z)).2))
      (fun z he => hb (he ▸ (pathCoverProj x₀ (E.symm z)).2))
    have hsub : (U : Set ℂ) ⊆ {c} := by
      intro z hz
      obtain ⟨w, hw⟩ := (hsurj.comp E.symm.surjective) ⟨z, hz⟩
      have he : F w = z := congrArg Subtype.val hw
      rw [hc] at he
      exact he.symm
    exact (hinf (Set.finite_singleton c |>.subset hsub)).elim
  · obtain ⟨E⟩ := hmodel
    let : CompactSpace (PathCover x₀) := E.toHomeomorph.symm.compactSpace
    let : CompactSpace U := hsurj.compactSpace hproj.continuous
    have hc : IsCompact (U : Set ℂ) := isCompact_iff_compactSpace.mpr inferInstance
    have he : (U : Set ℂ) = univ :=
      (show IsClopen (U : Set ℂ) from ⟨hc.isClosed, U.isOpen⟩).eq_univ ⟨x₀, x₀.2⟩
    exfalso
    apply ha
    change a ∈ (U : Set ℂ)
    rw [he]
    trivial

end RiemannDynamics
