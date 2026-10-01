module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.Components
public import BoundedWanderingDomains.Surfaces.CompactFilling

@[expose] public section

/-! # Keeping fillings inside their ambient component

After hyperbolising each relevant ambient component by deleting a disc or
finitely many points, every component is noncompact. The existing intrinsic
filling then cannot include an unrelated ambient component.
-/

open Set Function Topology

namespace AreaDeficit.Surfaces

/-- Every connected component is noncompact. Unlike noncompactness of the
whole space, this condition excludes extraneous compact components in fillings. -/
class NoncompactComponents (X : Type*) [TopologicalSpace X] : Prop where
  not_isCompact (x : X) : ¬ IsCompact (connectedComponent x)

instance {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [NoncompactSpace X] :
    NoncompactComponents X where
  not_isCompact x := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact noncompact_univ X

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [NoncompactComponents X]

theorem compactFill_subset_ambientComponent (c : ConnectedComponents X)
    {K : Set X} (hKc : K ⊆ ambientComponent c) :
    compactFill K ⊆ ambientComponent c := by
  intro x hx
  by_contra hxc
  have hcc : connectedComponent x ⊆ Kᶜ := by
    intro y hy hyK
    have hyx : ConnectedComponents.mk y = ConnectedComponents.mk x :=
      ConnectedComponents.coe_eq_coe'.mpr hy
    exact hxc (hyx.symm.trans (hKc hyK))
  have hsub : connectedComponent x ⊆ connectedComponentIn Kᶜ x :=
    isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent hcc
  exact NoncompactComponents.not_isCompact x
    (hx.of_isClosed_subset isClosed_connectedComponent (hsub.trans subset_closure))

end AreaDeficit.Surfaces
