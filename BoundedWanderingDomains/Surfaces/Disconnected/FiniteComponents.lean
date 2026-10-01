module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.Components

@[expose] public section

/-! # Finite clopen unions of ambient components -/

open Set Function Topology TopologicalSpace

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def componentUnion (I : Finset (ConnectedComponents X)) : Opens X :=
  ⟨⋃ c : I, (ambientComponent c.val : Set X), isOpen_iUnion (fun c => (ambientComponent c.val).isOpen)⟩

theorem isClosed_componentUnion (I : Finset (ConnectedComponents X)) :
    IsClosed (componentUnion I : Set X) :=
  isClosed_iUnion_of_finite (fun c : I => isClosed_ambientComponent c.val)

@[simp] theorem mem_componentUnion (I : Finset (ConnectedComponents X)) (x : X) :
    x ∈ componentUnion I ↔ ConnectedComponents.mk x ∈ I := by
  change x ∈ (⋃ c : I, (ambientComponent c.val : Set X)) ↔ _
  simp only [mem_iUnion]
  constructor
  · rintro ⟨c, hc⟩
    exact hc.symm ▸ c.property
  · intro hx
    exact ⟨⟨ConnectedComponents.mk x, hx⟩, rfl⟩

theorem ambientComponent_subset_componentUnion {I : Finset (ConnectedComponents X)}
    (c : I) : (ambientComponent c.val : Set X) ⊆ componentUnion I := by
  intro x hx
  exact mem_iUnion.mpr ⟨c, hx⟩

noncomputable def componentUnion_components_equiv (I : Finset (ConnectedComponents X)) :
    ConnectedComponents (componentUnion I) ≃ I := by
  let U := componentUnion I
  let A : I → Set U := fun c => Subtype.val ⁻¹' (ambientComponent c.val : Set X)
  have hA : ∀ c, IsClopen (A c) := fun c =>
    ⟨(isClosed_ambientComponent c.val).preimage continuous_subtype_val,
      (ambientComponent c.val).isOpen.preimage continuous_subtype_val⟩
  have hd : Pairwise (Disjoint on A) := by
    intro c d hcd
    exact (ambientComponent_pairwise_disjoint (Subtype.val_injective.ne hcd)).preimage Subtype.val
  have hU : ⋃ c, A c = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨c, hc⟩ := mem_iUnion.mp x.property
    exact ⟨c, hc⟩
  have hc : ∀ c, IsConnected (A c) := by
    intro c
    have hconn : IsConnected (ambientComponent c.val : Set X) := by
      obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c.val
      rw [← hx, ambientComponent_mk]
      exact isConnected_connectedComponent
    exact hconn.preimage_of_isOpenMap Subtype.val_injective U.isOpen.isOpenMap_subtype_val
      (fun x hx => ⟨⟨x, ambientComponent_subset_componentUnion c hx⟩, rfl⟩)
  exact ConnectedComponents.equivOfIsClopenOfIsConnected hA hd hU hc

instance componentUnion_finite_components (I : Finset (ConnectedComponents X)) :
    Finite (ConnectedComponents (componentUnion I)) :=
  Finite.of_equiv I (componentUnion_components_equiv I).symm

theorem exists_finite_clopen_component_neighborhood {K : Set X} (hK : IsCompact K) :
    ∃ O : Opens X, IsClosed (O : Set X) ∧ K ⊆ O ∧ Finite (ConnectedComponents O) := by
  classical
  let I := (finite_components_of_isCompact hK).toFinset
  refine ⟨componentUnion I, isClosed_componentUnion I, ?_, inferInstance⟩
  intro x hx
  exact (mem_componentUnion I x).mpr ((finite_components_of_isCompact hK).mem_toFinset.mpr
    ⟨x, hx, rfl⟩)

omit [ChartedSpace ℂ X] in
theorem connectedComponents_eq_of_clopen_inclusion (O : Opens X) (hO : IsClosed (O : Set X))
    {x y : O} (h : ConnectedComponents.mk (x : X) = ConnectedComponents.mk (y : X)) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  rw [ConnectedComponents.coe_eq_coe'] at h ⊢
  have he : (Subtype.val : O → X) '' connectedComponent y = connectedComponent (y : X) := by
    have he0 : connectedComponentIn (O : Set X) (y : X) =
        (Subtype.val : O → X) '' connectedComponent y :=
      connectedComponentIn_eq_image y.property
    exact he0.symm.trans
      ((show IsClopen (O : Set X) from ⟨hO, O.isOpen⟩).connectedComponentIn_eq y.property)
  rw [← he] at h
  obtain ⟨z, hz, hzx⟩ := h
  exact (Subtype.ext hzx : z = x) ▸ hz

omit [ChartedSpace ℂ X] in
theorem visits_all_components_of_ambient_labels (O : Opens X) (hO : IsClosed (O : Set X))
    (u : ℕ → O) (hvisit : ∀ x : O, ∃ n, ConnectedComponents.mk (u n : X) = ConnectedComponents.mk (x : X)) :
    ∀ c : ConnectedComponents O, ∃ n, ConnectedComponents.mk (u n) = c := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨n, hn⟩ := hvisit x
  exact ⟨n, connectedComponents_eq_of_clopen_inclusion O hO hn⟩

end AreaDeficit.Surfaces
