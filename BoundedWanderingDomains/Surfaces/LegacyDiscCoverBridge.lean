/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DiscCover
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic
import BoundedWanderingDomains.DiscCoveringMetric
import RiemannDynamics.Uniformization.PuncturedPlaneCovering

/-! # Bridge from the plane-domain covering interface -/

open Set Function Metric TopologicalSpace
open scoped Manifold ContDiff

namespace AreaDeficit.Surfaces

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]

/-- Transport a supplied universal disc covering across a biholomorphism. -/
noncomputable def DiscCover.transDiffeomorph (p : DiscCover M)
    (e : M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ N) : DiscCover N where
  projection := e ∘ p.projection
  holomorphic := e.mdifferentiable (by simp) |>.comp p.holomorphic
  covering := p.covering.homeomorph_comp e.toHomeomorph
  surjective := e.surjective.comp p.surjective

/-- A disc covering of an open plane domain in the original plane-function
interface supplies the intrinsic surface `DiscCover` used by the surface
area development. -/
noncomputable def DiscCover.ofPlaneCovering (U : Opens ℂ) (p : ℂ → ℂ)
    (hp : AreaDeficit.IsHolomorphicDiscCovering p U) : DiscCover U where
  projection := fun w =>
    ⟨p w, hp.maps (x := (w : ℂ)) w.property⟩
  holomorphic := by
    apply (mdifferentiable_subtypeVal_comp_iff U _).mp
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : unitDisc => p (w : ℂ))
    intro w
    have hpAt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) p (w : ℂ) :=
      mdifferentiableAt_iff_differentiableAt.mpr
        ((hp.holo (w : ℂ) w.2).differentiableAt (isOpen_ball.mem_nhds w.2))
    have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (Subtype.val : unitDisc → ℂ) :=
      (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω)).mdifferentiable (by simp)
    exact hpAt.comp w (hval w)
  covering := by
    let F : unitDisc → ℂ := fun w => p w
    let G : unitDisc → U := fun w =>
      ⟨p w, hp.maps (x := (w : ℂ)) w.property⟩
    have hpre : F ⁻¹' (U : Set ℂ) = Set.univ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact hp.maps (x := (w : ℂ)) w.property
    have hr := hp.covering.isCoveringMap_restrictPreimage
    let e : unitDisc ≃ₜ F ⁻¹' (U : Set ℂ) :=
      (Homeomorph.Set.univ unitDisc).symm.trans (Homeomorph.setCongr hpre.symm)
    have heq : (Set.restrictPreimage (U : Set ℂ) F) ∘ e = G := by
      funext w
      apply Subtype.ext
      rfl
    change IsCoveringMap G
    rw [← heq]
    exact hr.comp_homeomorph e
  surjective := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, hpw⟩ := hp.surj hz
    exact ⟨⟨w, hw⟩, Subtype.ext hpw⟩

/-- A plane with at least two finite punctures, now in the intrinsic surface
covering interface. -/
theorem DiscCover.nonempty_finitelyPuncturedPlane (P : Finset ℂ)
    (hP : 2 ≤ P.card) :
    let U : Opens ℂ :=
      ⟨((↑P : Set ℂ)ᶜ), P.finite_toSet.isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  let U : Opens ℂ :=
    ⟨((↑P : Set ℂ)ᶜ), P.finite_toSet.isClosed.isOpen_compl⟩
  obtain ⟨p, hp⟩ :=
    RiemannDynamics.exists_disc_covering_finitely_punctured_plane P hP
  exact ⟨DiscCover.ofPlaneCovering U p hp⟩

end AreaDeficit.Surfaces
