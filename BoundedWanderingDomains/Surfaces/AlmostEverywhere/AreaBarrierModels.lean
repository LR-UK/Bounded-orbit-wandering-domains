module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.ForwardSourceBarrier
public import BoundedWanderingDomains.Surfaces.BarrierCompactOrbit
public import BoundedWanderingDomains.Surfaces.CompactAnchorNormality
public import BoundedWanderingDomains.Surfaces.AnchorComplementModels

@[expose] public section

/-! # Finite source barriers and countable backward exceptional sets -/

open Set Function Filter MeasureTheory
open AreaDeficit.Surfaces
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [SecondCountableTopology X]

theorem LocalMap.exists_countable_backward_invariant_superset
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (P : ℕ → Finset X) (E : Finset X) :
    ∃ S : Set X, S.Countable ∧ (∀ n, (P n : Set X) ⊆ S) ∧
      (E : Set X) ⊆ S ∧ (∀ x : f.source, f.map x ∈ S → (x : X) ∈ S) := by
  classical
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  let K : CompactExhaustion f.source := CompactExhaustion.choice f.source
  let Q : ℕ → Set X := fun n => (P n ∪ E : Finset X)
  let T := f.sourceExhaustiveBackwardTree K Q
  let S : Set X := ⋃ n, T n
  have hfin : ∀ n, (T n).Finite :=
    f.sourceExhaustiveBackwardTree_finite hf K.isCompact (fun n => (P n ∪ E).finite_toSet)
  refine ⟨S, countable_iUnion (fun n => (hfin n).countable), ?_, ?_, ?_⟩
  · intro n x hx
    exact mem_iUnion.mpr ⟨n, f.roots_subset_sourceExhaustiveBackwardTree n
      (Finset.mem_union_left E hx)⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨0, f.roots_subset_sourceExhaustiveBackwardTree 0
      (Finset.mem_union_right (P 0) hx)⟩
  · exact f.sourceExhaustiveBackwardTree_union_backward (OrderHomClass.mono K) K.iUnion_eq

end SurfaceDynamics

open Set Function Filter TopologicalSpace
open AreaDeficit.Surfaces
open SurfaceDynamics
open scoped Topology Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

theorem sourceExhaustiveBackwardTree_forward_defect
    (f : LocalMap X) (K : ℕ → Set f.source) (Q : ℕ → Set X) (J : Set X)
    (hQ : ∀ n (x : f.source), (x : X) ∈ Q n → f.map x ∈ J) (n : ℕ) :
    ∀ x : f.source, (x : X) ∈ f.sourceExhaustiveBackwardTree K Q n →
      f.map x ∈ f.sourceExhaustiveBackwardTree K Q n ∪ J := by
  induction n with
  | zero => exact fun x hx => Or.inr (hQ 0 x hx)
  | succ n ih =>
      intro x hx
      rcases hx with ((hx | hx) | ⟨y, hy, he⟩)
      · rcases ih x hx with hp | hj
        · exact Or.inl (Or.inl (Or.inl hp))
        · exact Or.inr hj
      · exact Or.inr (hQ (n + 1) x hx)
      · have hey : y = x := Subtype.ext he
        exact Or.inl (Or.inl (Or.inl (hey ▸ hy.2)))

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem exists_finite_source_anchor_models
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (E : Finset X) :
    ∃ P : ℕ → Finset X, Monotone P ∧ (∀ n, E ⊆ P n) ∧
      frontier (f.source : Set X) ⊆ closure (⋃ n, (P n : Set X)) ∧
      (∀ n (x : f.source), (x : X) ∈ P n →
        f.map x ∈ (P n : Set X) ∪ f.totalize '' (E : Set X)) ∧
      (∀ x : f.source, f.map x ∈ closure (⋃ n, (P n : Set X)) →
        (x : X) ∈ closure (⋃ n, (P n : Set X))) := by
  classical
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  obtain ⟨Q₀, _, hQfront, hQcl⟩ := closed_set_dense_finite_exhaustion
    (isClosed_frontier : IsClosed (frontier (f.source : Set X)))
  let Q : ℕ → Set X := fun n => (Q₀ n ∪ E : Finset X)
  let K : CompactExhaustion f.source := CompactExhaustion.choice f.source
  let T := f.sourceExhaustiveBackwardTree K Q
  have hfin : ∀ n, (T n).Finite :=
    f.sourceExhaustiveBackwardTree_finite hf K.isCompact (fun n => (Q₀ n ∪ E).finite_toSet)
  let P : ℕ → Finset X := fun n => (hfin n).toFinset
  have hcoe : ∀ n, (P n : Set X) = T n := fun n => (hfin n).coe_toFinset
  have hQdef : ∀ n (x : f.source), (x : X) ∈ Q n → f.map x ∈ f.totalize '' (E : Set X) := by
    intro n x hx
    rcases Finset.mem_union.mp hx with hfront | he
    · exact ((disjoint_frontier_iff_isOpen.mpr f.source.isOpen).le_bot ⟨hQfront n hfront, x.property⟩).elim
    · exact ⟨x, he, f.totalize_eq x.property⟩
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm x hx
    exact (hfin m).mem_toFinset.mpr (f.sourceExhaustiveBackwardTree_mono K Q hnm
      ((hfin n).mem_toFinset.mp hx))
  · intro n x hx
    exact (hfin n).mem_toFinset.mpr (f.roots_subset_sourceExhaustiveBackwardTree n
      (Finset.mem_union_right (Q₀ n) hx))
  · simp_rw [hcoe]
    rw [← hQcl]
    apply closure_mono
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, f.roots_subset_sourceExhaustiveBackwardTree n
      (Finset.mem_union_left E hn)⟩
  · intro n x hx
    change (x : X) ∈ (P n : Set X) at hx
    rw [hcoe] at hx ⊢
    exact f.sourceExhaustiveBackwardTree_forward_defect K Q _ hQdef n x hx
  · simp_rw [hcoe]
    exact f.closure_source_backward_invariant hf.1
      (f.sourceExhaustiveBackwardTree_union_backward (OrderHomClass.mono K) K.iUnion_eq)

theorem bad_compact_orbit_point_mem_anchor_barrier
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (E : Finset X) (p : ComponentwiseDiscCover (anchorComplement E))
    (P : ℕ → Finset X) (hEP : (E : Set X) ⊆ closure (⋃ n, (P n : Set X)))
    (hfront : frontier (f.source : Set X) ⊆ closure (⋃ n, (P n : Set X)))
    (hback : ∀ x : f.source, f.map x ∈ closure (⋃ n, (P n : Set X)) →
      (x : X) ∈ closure (⋃ n, (P n : Set X)))
    {x : X} (hx : x ∈ f.trapped \ f.omega)
    {K : Set X} (hK : IsCompact K) (hxK : ∀ n, f.orbit n ⟨x, hx.1⟩ ∈ K) :
    x ∈ closure (⋃ n, (P n : Set X)) := by
  by_contra hxP
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let C := closure (⋃ n, (P n : Set X))
  let W := componentDomain ⟨Cᶜ, isClosed_closure.isOpen_compl⟩ x
  have hxW : x ∈ W := mem_componentDomain hxP
  have hWtr : (W : Set X) ⊆ f.trapped :=
    f.trapped_barrier_component hf.2.continuous isClosed_closure hfront hback hx.1 hxP
  have hWO : ∀ n y, f.orbitOn W hWtr n y ∈ anchorComplement E := by
    intro n y
    have hnot : ∀ k, f.orbit k ⟨y, hWtr y.property⟩ ∉ C := by
      intro k
      induction k with
      | zero => exact connectedComponentIn_subset _ _ y.property
      | succ k ih =>
          intro hh
          apply ih
          apply hback ⟨f.orbit k ⟨y, hWtr y.property⟩, f.orbit_mem_source k _⟩
          rwa [← f.orbit_succ k ⟨y, hWtr y.property⟩]
    exact fun he => hnot n (hEP he)
  exact hx.2 (f.mem_omega_of_omits_finite_anchors_compact_orbit hf E (anchorComplement E) (fun _ => Iff.rfl)
    p W hWtr hWO ⟨x, hxW⟩ hK hxK)

variable [CompactSpace X]

theorem bad_compact_source_points_subset_anchor_barrier
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (E : Finset X) (p : DiscCover (anchorComplement E))
    (P : ℕ → Finset X) (hEP : (E : Set X) ⊆ closure (⋃ n, (P n : Set X)))
    (hfront : frontier (f.source : Set X) ⊆ closure (⋃ n, (P n : Set X)))
    (hback : ∀ x : f.source, f.map x ∈ closure (⋃ n, (P n : Set X)) →
      (x : X) ∈ closure (⋃ n, (P n : Set X))) :
    f.trapped \ f.omega ⊆ closure (⋃ n, (P n : Set X)) := by
  intro x hx
  exact f.bad_compact_orbit_point_mem_anchor_barrier hf E p P hEP hfront hback hx
    isCompact_univ (fun _ => mem_univ _)

end SurfaceDynamics.LocalMap
