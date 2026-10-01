module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.Components
public import BoundedWanderingDomains.Surfaces.SubdomainCover
public import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

@[expose] public section

/-! # Disc covers supplied separately on ambient components -/

open Set Function TopologicalSpace Topology
open scoped Manifold

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- Hyperbolicity of each ambient component, with no connectedness imposed
on their union and no requirement on component itineraries of local maps. -/
structure ComponentwiseDiscCover (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] where
  cover : ∀ c : ConnectedComponents X, DiscCover (ambientComponent c)

/-- The componentwise interface includes the existing connected interface. -/
noncomputable def DiscCover.componentwise (p : DiscCover X) : ComponentwiseDiscCover X where
  cover c := by
    let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
    let : ConnectedSpace X := p.surjective.connectedSpace p.continuous
    have hC : (ambientComponent c : Set X) = univ := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      rw [ambientComponent_mk, PreconnectedSpace.connectedComponent_eq_univ]
    have hm (z : unitDisc) : p.projection z ∈ ambientComponent c := by
      change p.projection z ∈ (ambientComponent c : Set X)
      rw [hC]
      trivial
    let F : unitDisc → ambientComponent c := fun z => ⟨p.projection z, hm z⟩
    have hpre : p.projection ⁻¹' (ambientComponent c : Set X) = univ := by rw [hC]; rfl
    let e : unitDisc ≃ₜ p.projection ⁻¹' (ambientComponent c : Set X) :=
      (Homeomorph.Set.univ unitDisc).symm.trans (Homeomorph.setCongr hpre).symm
    refine ⟨F, (mdifferentiable_subtypeVal_comp_iff (ambientComponent c) F).mp p.holomorphic,
      (p.covering.restrictPreimage (ambientComponent c : Set X)).comp_homeomorph e, ?_⟩
    intro x
    obtain ⟨z, hz⟩ := p.surjective (x : X)
    exact ⟨z, Subtype.ext hz⟩

noncomputable instance : Coe (DiscCover X) (ComponentwiseDiscCover X) :=
  ⟨DiscCover.componentwise⟩

variable [T2Space X] [SecondCountableTopology X]

namespace ComponentwiseDiscCover

/-- A connected open subset lies in one ambient component, even when other
pieces of the source of a local map lie in other components. -/
theorem nonempty_subdomain (p : ComponentwiseDiscCover X)
    (U : Opens X) [ConnectedSpace U] : Nonempty (DiscCover U) := by
  classical
  let x : U := Classical.choice (inferInstance : Nonempty U)
  let C := ambientComponent (ConnectedComponents.mk (x : X))
  have hUC : (U : Set X) ⊆ C := by
    rw [show (C : Set X) = connectedComponent (x : X) from ambientComponent_mk (x : X)]
    exact (isConnected_iff_connectedSpace.mpr inferInstance).subset_connectedComponent x.property
  let j : U → C := Set.inclusion hUC
  have hj : IsOpenEmbedding j :=
    .of_continuous_injective_isOpenMap (continuous_inclusion hUC)
      (Set.inclusion_injective hUC) (U.isOpen.isOpenMap_inclusion hUC)
  have hjh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j := by
    apply (mdifferentiable_subtypeVal_comp_iff C j).mp
    exact mdifferentiable_subtype_val U
  exact (p.cover (ConnectedComponents.mk (x : X))).nonempty_of_holomorphic_localHomeomorph
    j hjh hj.isLocalHomeomorph

noncomputable def componentCover (p : ComponentwiseDiscCover X)
    (U : Opens X) (x : U) : DiscCover (componentDomain U (x : X)) := by
  let : ConnectedSpace (componentDomain U (x : X)) := componentDomain_connected x.property
  exact Classical.choice (p.nonempty_subdomain (componentDomain U (x : X)))

end ComponentwiseDiscCover

end AreaDeficit.Surfaces
