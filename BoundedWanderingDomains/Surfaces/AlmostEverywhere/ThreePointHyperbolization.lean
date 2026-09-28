/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.PlaneCoverPuncture
import BoundedWanderingDomains.Surfaces.SpherePunctureCover
import BoundedWanderingDomains.Surfaces.UniformizationBridge

/-! # Hyperbolization after deleting three points -/

open Set Function Metric TopologicalSpace
open scoped Manifold ContDiff

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] [ConnectedSpace X] [T2Space X]
  [SecondCountableTopology X] [Infinite X]

theorem DiscCover.nonempty_compl_finset_of_plane_cover_two_lifts
    (π : ℂ → X) (hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π)
    (hcov : IsCoveringMap π) (hsurj : Surjective π)
    (P : Finset X) {u v : ℂ} (huv : u ≠ v) (hu : π u ∈ P) (hv : π v ∈ P) :
    let U : Opens X := ⟨(P : Set X)ᶜ, P.finite_toSet.isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  let U : Opens X := ⟨(P : Set X)ᶜ, P.finite_toSet.isClosed.isOpen_compl⟩
  let : ConnectedSpace U := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset P)
  let : Infinite U := Set.Infinite.to_subtype P.finite_toSet.infinite_compl
  let x₀ : U := Classical.choice (inferInstance : Nonempty U)
  let : T2Space (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.t2space_pathCover x₀
  let : SimplyConnectedSpace (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  let : SecondCountableTopology (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.secondCountableTopology_pathCover x₀
  have hmodels := RiemannDynamics.uniformization_trichotomy
    (RiemannDynamics.PathCover x₀)
  have hproj := RiemannDynamics.contMDiff_pathCoverProj x₀
  have hprojSurj : Surjective (RiemannDynamics.pathCoverProj x₀) := by
    let : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace ℂ U
    let : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
    intro y
    exact ⟨⟨y, Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath x₀ y)⟩, rfl⟩
  rcases hmodels with hdisc | hplane | hsphere
  · obtain ⟨e⟩ := hdisc
    refine ⟨{ projection := RiemannDynamics.pathCoverProj x₀ ∘ e.symm
              holomorphic := ?_
              covering := ?_
              surjective := ?_ }⟩
    · exact (hproj.mdifferentiable (by simp)).comp
        (e.symm.mdifferentiable (by simp))
    · exact (RiemannDynamics.pathCoverProj_isCoveringMap x₀).comp_homeomorph
        e.symm.toHomeomorph
    · exact hprojSurj.comp e.symm.surjective
  · obtain ⟨e⟩ := hplane
    let F : ℂ → U := RiemannDynamics.pathCoverProj x₀ ∘ e.symm
    let G : ℂ → X := Subtype.val ∘ F
    have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
      (hproj.comp e.symm.contMDiff).mdifferentiable (by simp)
    have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : U → X) :=
      (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω)).mdifferentiable (by simp)
    have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := hval.comp hF
    obtain ⟨w, hw⟩ := hsurj (G 0)
    obtain ⟨H, -, hfac, hH⟩ := exists_holomorphic_lift hπ hcov hG 0 w hw
    have hHu : ∀ z, H z ≠ u := by
      intro z hzu
      have hz := congrFun hfac z
      have hGa : G z ∈ P := by rw [← hz]; simpa [hzu] using hu
      exact (F z).property hGa
    have hHv : ∀ z, H z ≠ v := by
      intro z hzv
      have hz := congrFun hfac z
      have hGa : G z ∈ P := by rw [← hz]; simpa [hzv] using hv
      exact (F z).property hGa
    have hHd : Differentiable ℂ H := mdifferentiable_iff_differentiable.mp hH
    obtain ⟨c, hc⟩ := FunctionTheory.exists_eq_const_of_two_omitted_values
      hHd huv (fun z hz => hHu z hz) (fun z hz => hHv z hz)
    have hGc : G = fun _ => π c := by
      funext z
      have hz := congrFun hfac z
      simpa [hc] using hz.symm
    have hFc : F = fun _ => F 0 := by
      funext z
      apply Subtype.ext
      have hz := congrFun hGc z
      have h0 := congrFun hGc 0
      exact hz.trans h0.symm
    have hFsurj : Surjective F := hprojSurj.comp e.symm.surjective
    obtain ⟨y, hy⟩ := exists_ne (F 0)
    obtain ⟨z, rfl⟩ := hFsurj y
    exact (hy (congrFun hFc z)).elim
  · obtain ⟨e⟩ := hsphere
    let : CompactSpace (RiemannDynamics.PathCover x₀) :=
      e.toHomeomorph.symm.compactSpace
    let : CompactSpace U := hprojSurj.compactSpace hproj.continuous
    have hUc : IsCompact (U : Set X) := isCompact_iff_compactSpace.mpr inferInstance
    have hUuniv : (U : Set X) = Set.univ :=
      (show IsClopen (U : Set X) from ⟨hUc.isClosed, U.isOpen⟩).eq_univ
        ⟨x₀, x₀.property⟩
    have haU : π u ∈ (U : Set X) := by rw [hUuniv]; trivial
    exact (haU hu).elim


/-- Three prescribed punctures hyperbolize any connected Riemann surface. -/
theorem DiscCover.nonempty_compl_three_on_any_surface (F : Finset X)
    (hF : F.card = 3) :
    let U : Opens X := ⟨(F : Set X)ᶜ, F.finite_toSet.isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let : T2Space (RiemannDynamics.PathCover x₀) := RiemannDynamics.t2space_pathCover x₀
  let : SimplyConnectedSpace (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  let : SecondCountableTopology (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.secondCountableTopology_pathCover x₀
  rcases RiemannDynamics.uniformization_trichotomy
      (RiemannDynamics.PathCover x₀) with hdisc | hplane | hsphere
  · obtain ⟨p⟩ := nonempty_discCover_of_isHyperbolic
      (RiemannDynamics.isHyperbolic_of_nonempty_diffeomorph_disc hdisc)
    exact p.nonempty_finitePuncture F
  · obtain ⟨e⟩ := hplane
    let π : ℂ → X := RiemannDynamics.pathCoverProj x₀ ∘ e.symm
    have hproj := RiemannDynamics.contMDiff_pathCoverProj x₀
    have hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π :=
      (hproj.comp e.symm.contMDiff).mdifferentiable (by simp)
    have hcov : IsCoveringMap π :=
      (RiemannDynamics.pathCoverProj_isCoveringMap x₀).comp_homeomorph e.symm.toHomeomorph
    let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
    let : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
    have hprojSurj : Surjective (RiemannDynamics.pathCoverProj x₀) := by
      intro y
      exact ⟨⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)⟩, rfl⟩
    have hsurj : Surjective π := hprojSurj.comp e.symm.surjective
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hF
    obtain ⟨u, hu⟩ := hsurj a
    obtain ⟨v, hv⟩ := hsurj b
    have huv : u ≠ v := fun he => hab (hu.symm.trans ((congrArg π he).trans hv))
    exact DiscCover.nonempty_compl_finset_of_plane_cover_two_lifts π hπ hcov hsurj
      {a, b, c} huv (by simp [hu]) (by simp [hv])
  · obtain ⟨e⟩ := hsphere
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hF
    let U : Opens X :=
      ⟨(({a, b, c} : Finset X) : Set X)ᶜ,
        ({a, b, c} : Finset X).finite_toSet.isClosed.isOpen_compl⟩
    let V : Opens X := ⟨({a, b, c} : Set X)ᶜ,
      (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
    change Nonempty (DiscCover U)
    have hUV : U = V := Opens.ext (by simp [U, V])
    rw [hUV]
    exact DiscCover.nonempty_compl_three_of_pathCover_sphere x₀ e hab hac hbc

end AreaDeficit.Surfaces
