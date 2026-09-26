/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.HolomorphicLifting
import BoundedWanderingDomains.Surfaces.LegacyDiscCoverBridge
import BoundedWanderingDomains.Surfaces.FinitePunctureTopology
import FunctionTheory.Conformal.LittlePicardBloch
import RiemannDynamics.Uniformization.Trichotomy

/-! # Puncturing a surface with a plane universal cover

If a holomorphic plane covering has two distinct points over the puncture,
then the punctured surface is hyperbolic.  In the plane alternative for its
universal cover, lifting back to the original plane cover would give an
entire function omitting those two fibre points, contradicting Little Picard.
-/

open Set Function Metric TopologicalSpace
open scoped Manifold ContDiff

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] [ConnectedSpace X] [T2Space X]
  [SecondCountableTopology X] [Infinite X]

/-- Removing a point with a nontrivial fibre from a plane-covered surface
produces a surface with a supplied disc cover.  This is the torus branch of
the compact finite-puncture reduction. -/
theorem DiscCover.nonempty_compl_singleton_of_plane_cover
    (π : ℂ → X) (hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π)
    (hcov : IsCoveringMap π) (hsurj : Surjective π)
    {a : X} {u v : ℂ} (huv : u ≠ v) (hu : π u = a) (hv : π v = a) :
    let U : Opens X := ⟨({a} : Set X)ᶜ, isOpen_compl_singleton⟩
    Nonempty (DiscCover U) := by
  let U : Opens X := ⟨({a} : Set X)ᶜ, isOpen_compl_singleton⟩
  letI : ConnectedSpace U := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_singleton_of_connected
      (exists_pair_ne X) a)
  letI : Infinite U := Set.Infinite.to_subtype (Set.finite_singleton a).infinite_compl
  let x₀ : U := Classical.choice (inferInstance : Nonempty U)
  letI : T2Space (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.t2space_pathCover x₀
  letI : SimplyConnectedSpace (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  letI : SecondCountableTopology (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.secondCountableTopology_pathCover x₀
  have hmodels := RiemannDynamics.uniformization_trichotomy
    (RiemannDynamics.PathCover x₀)
  have hproj := RiemannDynamics.contMDiff_pathCoverProj x₀
  have hprojSurj : Surjective (RiemannDynamics.pathCoverProj x₀) := by
    letI : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace ℂ U
    letI : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
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
      have hGa : G z = a := by simpa [hzu, hu] using hz.symm
      exact (F z).property (by simpa [G] using hGa)
    have hHv : ∀ z, H z ≠ v := by
      intro z hzv
      have hz := congrFun hfac z
      have hGa : G z = a := by simpa [hzv, hv] using hz.symm
      exact (F z).property (by simpa [G] using hGa)
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
    letI : CompactSpace (RiemannDynamics.PathCover x₀) :=
      e.toHomeomorph.symm.compactSpace
    letI : CompactSpace U := hprojSurj.compactSpace hproj.continuous
    have hUc : IsCompact (U : Set X) := isCompact_iff_compactSpace.mpr inferInstance
    have hUuniv : (U : Set X) = Set.univ :=
      (show IsClopen (U : Set X) from ⟨hUc.isClosed, U.isOpen⟩).eq_univ
        ⟨x₀, x₀.property⟩
    have haU : a ∈ (U : Set X) := by rw [hUuniv]; trivial
    exact (by simpa [U] using haU)

/-- On a compact surface whose universal path cover is the plane, every
point has at least two lifts.  Removing any one point therefore gives a disc
cover by the preceding Little-Picard argument. -/
theorem DiscCover.nonempty_compl_singleton_of_pathCover_plane
    [CompactSpace X] (x₀ : X)
    (e : RiemannDynamics.PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) (a : X) :
    let U : Opens X := ⟨({a} : Set X)ᶜ, isOpen_compl_singleton⟩
    Nonempty (DiscCover U) := by
  let π : ℂ → X := RiemannDynamics.pathCoverProj x₀ ∘ e.symm
  have hproj := RiemannDynamics.contMDiff_pathCoverProj x₀
  have hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π :=
    (hproj.comp e.symm.contMDiff).mdifferentiable (by simp)
  have hcov : IsCoveringMap π :=
    (RiemannDynamics.pathCoverProj_isCoveringMap x₀).comp_homeomorph
      e.symm.toHomeomorph
  letI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  letI : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  have hprojSurj : Surjective (RiemannDynamics.pathCoverProj x₀) := by
    intro y
    exact ⟨⟨y, Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath x₀ y)⟩, rfl⟩
  have hsurj : Surjective π := hprojSurj.comp e.symm.surjective
  have hninj : ¬ Injective (RiemannDynamics.pathCoverProj x₀) := by
    intro hinj
    have hhome : IsHomeomorph (RiemannDynamics.pathCoverProj x₀) :=
      ⟨RiemannDynamics.pathCoverProj_isCoveringMap x₀ |>.continuous,
        RiemannDynamics.pathCoverProj_isCoveringMap x₀ |>.isOpenMap,
        ⟨hinj, hprojSurj⟩⟩
    let h : RiemannDynamics.PathCover x₀ ≃ₜ X :=
      IsHomeomorph.homeomorph _ hhome
    letI : CompactSpace (RiemannDynamics.PathCover x₀) := h.symm.compactSpace
    letI : CompactSpace ℂ := e.toHomeomorph.compactSpace
    exact noncompact_univ ℂ isCompact_univ
  obtain ⟨pc, qc, hpqproj, hpq⟩ := Function.not_injective_iff.mp hninj
  obtain ⟨γ, hγpc⟩ :=
    RiemannDynamics.pathCoverDeck_transitive x₀ pc qc hpqproj
  obtain ⟨r, hr⟩ := hprojSurj a
  let s : RiemannDynamics.PathCover x₀ :=
    RiemannDynamics.pathCoverDeck x₀ γ r
  have hrsproj : RiemannDynamics.pathCoverProj x₀ s =
      RiemannDynamics.pathCoverProj x₀ r := rfl
  have hrs : r ≠ s := by
    intro hrsEq
    have hsfix : RiemannDynamics.pathCoverDeck x₀ γ r = r := hrsEq.symm
    obtain ⟨rpt, rcls⟩ := r
    have hmk : RiemannDynamics.PathCover.mk rpt
        (Path.Homotopic.Quotient.trans γ rcls) =
        RiemannDynamics.PathCover.mk rpt rcls := hsfix
    rw [RiemannDynamics.PathCover.mk.injEq] at hmk
    have hcls : Path.Homotopic.Quotient.trans γ rcls = rcls :=
      eq_of_heq hmk.2
    have hloop := congrArg
      (fun c : Path.Homotopic.Quotient x₀ rpt =>
        Path.Homotopic.Quotient.trans c
          (Path.Homotopic.Quotient.symm rcls)) hcls
    have hγrefl : γ = Path.Homotopic.Quotient.refl x₀ := by
      simpa [Path.Homotopic.Quotient.trans_assoc] using hloop
    have hpcfix : RiemannDynamics.pathCoverDeck x₀ γ pc = pc := by
      rw [hγrefl]
      obtain ⟨pt, cls⟩ := pc
      exact congrArg (RiemannDynamics.PathCover.mk pt)
        (Path.Homotopic.Quotient.refl_trans cls)
    exact hpq (hpcfix.symm.trans hγpc)
  let u : ℂ := e r
  let v : ℂ := e s
  have huv : u ≠ v := e.injective.ne hrs
  have hu : π u = a := by simp [π, u, hr]
  have hv : π v = a := by
    change RiemannDynamics.pathCoverProj x₀ (e.symm (e s)) = a
    rw [e.symm_apply_apply, hrsproj, hr]
  exact DiscCover.nonempty_compl_singleton_of_plane_cover
    π hπ hcov hsurj huv hu hv

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.DiscCover.nonempty_compl_singleton_of_plane_cover
#print axioms AreaDeficit.Surfaces.DiscCover.nonempty_compl_singleton_of_pathCover_plane
