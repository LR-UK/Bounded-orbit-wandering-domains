module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.PlaneCoverPuncture
public import BoundedWanderingDomains.Surfaces.SpherePunctureCover
public import BoundedWanderingDomains.Surfaces.UniformizationBridge

@[expose] public section

/-! # Uniform finite hyperbolization of compact surfaces

The universal-cover trichotomy gives a uniform choice of at most three
punctures after which every compact Riemann surface has a supplied disc cover.
-/

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] [ConnectedSpace X] [T2Space X]
  [SecondCountableTopology X] [Infinite X] [CompactSpace X]

/-- Every compact Riemann surface becomes disc-covered after deleting at most
three points.  The disc, plane, and sphere cases require respectively zero,
one, and three punctures. -/
theorem DiscCover.exists_finite_hyperbolizing_punctures :
    ∃ F : Finset X, F.card ≤ 3 ∧
      let U : Opens X :=
        ⟨((↑F : Set X)ᶜ), F.finite_toSet.isClosed.isOpen_compl⟩
      Nonempty (DiscCover U) := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let : T2Space (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.t2space_pathCover x₀
  let : SimplyConnectedSpace (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  let : SecondCountableTopology (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.secondCountableTopology_pathCover x₀
  rcases RiemannDynamics.uniformization_trichotomy
      (RiemannDynamics.PathCover x₀) with hdisc | hplane | hsphere
  · refine ⟨∅, by simp, ?_⟩
    obtain ⟨p⟩ := nonempty_discCover_of_isHyperbolic
      (RiemannDynamics.isHyperbolic_of_nonempty_diffeomorph_disc hdisc)
    exact p.nonempty_finitePuncture ∅
  · obtain ⟨e⟩ := hplane
    let a : X := Classical.choice (inferInstance : Nonempty X)
    refine ⟨{a}, by simp, ?_⟩
    let U : Opens X :=
      ⟨((↑({a} : Finset X) : Set X)ᶜ),
        ({a} : Finset X).finite_toSet.isClosed.isOpen_compl⟩
    let V : Opens X := ⟨({a} : Set X)ᶜ, isOpen_compl_singleton⟩
    change Nonempty (DiscCover U)
    have hUV : U = V := Opens.ext (by simp [U, V])
    rw [hUV]
    exact DiscCover.nonempty_compl_singleton_of_pathCover_plane x₀ e a
  · obtain ⟨e⟩ := hsphere
    let a : X := Classical.choice (inferInstance : Nonempty X)
    obtain ⟨b, hb⟩ := ({a} : Finset X).exists_notMem
    obtain ⟨c, hc⟩ := ({a, b} : Finset X).exists_notMem
    simp only [Finset.mem_singleton] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    have hab : a ≠ b := fun h => hb h.symm
    have hac : a ≠ c := fun h => hc.1 h.symm
    have hbc : b ≠ c := fun h => hc.2 h.symm
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], ?_⟩
    let U : Opens X :=
      ⟨((↑({a, b, c} : Finset X) : Set X)ᶜ),
        ({a, b, c} : Finset X).finite_toSet.isClosed.isOpen_compl⟩
    let V : Opens X :=
      ⟨({a, b, c} : Set X)ᶜ,
        (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
    change Nonempty (DiscCover U)
    have hUV : U = V := Opens.ext (by simp [U, V])
    rw [hUV]
    exact DiscCover.nonempty_compl_three_of_pathCover_sphere
      x₀ e hab hac hbc

/-- Every prescribed three-point set hyperbolizes a compact Riemann surface.
This form is used when the punctures must be chosen inside the wandering set. -/
theorem DiscCover.nonempty_compl_finset_card_three (F : Finset X)
    (hF : F.card = 3) :
    let U : Opens X :=
      ⟨((↑F : Set X)ᶜ), F.finite_toSet.isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let : T2Space (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.t2space_pathCover x₀
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
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hF
    let V : Opens X := ⟨({a} : Set X)ᶜ, isOpen_compl_singleton⟩
    let U : Opens X :=
      ⟨((↑({a, b, c} : Finset X) : Set X)ᶜ),
        ({a, b, c} : Finset X).finite_toSet.isClosed.isOpen_compl⟩
    let : ConnectedSpace U := Subtype.connectedSpace
      (RiemannDynamics.isConnected_compl_finset {a, b, c})
    obtain ⟨p⟩ := DiscCover.nonempty_compl_singleton_of_pathCover_plane x₀ e a
    apply DiscCover.nonempty_of_le_open V U p
    intro x hx
    change x ≠ a
    intro hxa
    apply hx
    simp [hxa]
  · obtain ⟨e⟩ := hsphere
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hF
    let U : Opens X :=
      ⟨((↑({a, b, c} : Finset X) : Set X)ᶜ),
        ({a, b, c} : Finset X).finite_toSet.isClosed.isOpen_compl⟩
    let V : Opens X :=
      ⟨({a, b, c} : Set X)ᶜ,
        (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
    change Nonempty (DiscCover U)
    have hUV : U = V := Opens.ext (by simp [U, V])
    rw [hUV]
    exact DiscCover.nonempty_compl_three_of_pathCover_sphere
      x₀ e hab hac hbc

/-- Once three anchors have been inserted, every larger finite puncture stage
remains disc-covered.  This is the form used by backward-orbit exhaustions. -/
theorem DiscCover.nonempty_compl_finset_of_three_le_card (F : Finset X)
    (hF : 3 ≤ F.card) :
    let U : Opens X :=
      ⟨((↑F : Set X)ᶜ), F.finite_toSet.isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  classical
  obtain ⟨E, hEF, hEcard⟩ := Finset.exists_subset_card_eq hF
  let V : Opens X :=
    ⟨((↑E : Set X)ᶜ), E.finite_toSet.isClosed.isOpen_compl⟩
  let U : Opens X :=
    ⟨((↑F : Set X)ᶜ), F.finite_toSet.isClosed.isOpen_compl⟩
  let : ConnectedSpace U := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset F)
  obtain ⟨p⟩ := DiscCover.nonempty_compl_finset_card_three E hEcard
  apply DiscCover.nonempty_of_le_open V U p
  intro x hx
  exact fun hxE => hx (hEF hxE)

/-- A finite backward stage containing a three-point anchor set is
automatically a hyperbolic model. -/
theorem DiscCover.nonempty_compl_finset_of_card_three_subset
    (E F : Finset X) (hE : E.card = 3) (hEF : E ⊆ F) :
    let U : Opens X :=
      ⟨((↑F : Set X)ᶜ), F.finite_toSet.isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  apply DiscCover.nonempty_compl_finset_of_three_le_card F
  rw [← hE]
  exact Finset.card_le_card hEF

end AreaDeficit.Surfaces
