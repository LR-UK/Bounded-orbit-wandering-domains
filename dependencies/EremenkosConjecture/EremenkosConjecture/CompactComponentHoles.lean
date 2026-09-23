import ComplexApproximation.Topology.Filling
import ComplexApproximation.Topology.Nonseparation

/-! # The topological obstruction in Proposition 7.6

This file isolates the plane-topological argument. To apply it to escaping
sets, the dynamical alternatives for bounded complementary components must
still be proved. They are explicit hypotheses here.
-/

open Set Bornology ComplexApproximation

namespace EremenkosConjecture

theorem preconnected_subset_component_of_inter_nonempty {A K Y : Set ℂ} {a : ℂ}
    (hK : connectedComponentIn A a = K) (hY : IsPreconnected Y) (hYA : Y ⊆ A)
    (hinter : (K ∩ Y).Nonempty) : Y ⊆ K := by
  obtain ⟨p, hpK, hpY⟩ := hinter
  have hp : p ∈ connectedComponentIn A a := hK.symm ▸ hpK
  have hsub := hY.subset_connectedComponentIn hpY hYA
  rw [← connectedComponentIn_eq hp, hK] at hsub
  exact hsub

theorem unbounded_connected_subset_cannot_meet_bounded_hole
    {A K Y : Set ℂ} {a x : ℂ} (hK : IsBounded K)
    (hcomponent : connectedComponentIn A a = K)
    (hY : IsPreconnected Y) (hYA : Y ⊆ A) (hYu : ¬ IsBounded Y)
    (hU : IsBounded (connectedComponentIn Kᶜ x)) :
    Disjoint Y (connectedComponentIn Kᶜ x) := by
  have hYK : Disjoint Y K := by
    apply disjoint_left.mpr
    intro p hpY hpK
    exact hYu (hK.subset (preconnected_subset_component_of_inter_nonempty
      hcomponent hY hYA ⟨p, hpK, hpY⟩))
  have hYc : Y ⊆ Kᶜ := fun p hp hpK => disjoint_left.mp hYK hp hpK
  apply disjoint_left.mpr
  intro p hpY hpU
  have hsub := hY.subset_connectedComponentIn hpY hYc
  rw [← connectedComponentIn_eq hpU] at hsub
  exact hYu (hU.subset hsub)

theorem bounded_hole_not_subset_of_component_ambient {A K : Set ℂ} {a x : ℂ}
    (hK : IsCompact K) (hcomponent : connectedComponentIn A a = K) (hx : x ∉ K)
    (hbound : IsBounded (connectedComponentIn Kᶜ x)) :
    ¬ connectedComponentIn Kᶜ x ⊆ A := by
  intro hUA
  let U := connectedComponentIn Kᶜ x
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hUne : U ≠ univ := by
    intro heq
    have hb : IsBounded (univ : Set ℂ) := heq ▸ hbound
    exact not_isBounded_exterior 1 (hb.subset (subset_univ _))
  have hfront : frontier U ⊆ K := by
    simpa only [compl_compl] using
      frontier_component_subset_compl hK.isClosed.isOpen_compl hx
  have hKA : K ⊆ A := hcomponent ▸ connectedComponentIn_subset A a
  have hclA : closure U ⊆ A := by
    rw [closure_eq_self_union_frontier]
    exact union_subset hUA (hfront.trans hKA)
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hxU⟩, hUne⟩
  have hclK := preconnected_subset_component_of_inter_nonempty hcomponent
    isPreconnected_connectedComponentIn.closure hclA
    ⟨p, hfront hp, frontier_subset_closure hp⟩
  exact hx (hclK (subset_closure hxU))

/-- A compact component is full if every bounded hole is either entirely in
the ambient set or met by one of its unbounded connected subsets. Proposition 7.6
needs the dynamical proof of this alternative when the ambient set is I(f). -/
theorem isConnected_compl_of_component_hole_alternatives {A K : Set ℂ} {a : ℂ}
    (hK : IsCompact K) (hcomponent : connectedComponentIn A a = K)
    (hholes : ∀ x ∉ K, IsBounded (connectedComponentIn Kᶜ x) →
      connectedComponentIn Kᶜ x ⊆ A ∨
      ∃ Y : Set ℂ, IsPreconnected Y ∧ Y ⊆ A ∧ ¬ IsBounded Y ∧
        (Y ∩ connectedComponentIn Kᶜ x).Nonempty) :
    IsConnected Kᶜ := by
  apply isConnected_compl_of_unbounded_components K hK.isBounded
  intro x hx hb
  rcases hholes x hx hb with hUA | ⟨Y, hY, hYA, hYu, p, hpY, hpU⟩
  · exact bounded_hole_not_subset_of_component_ambient hK hcomponent hx hb hUA
  · exact disjoint_left.mp
      (unbounded_connected_subset_cannot_meet_bounded_hole hK.isBounded hcomponent
        hY hYA hYu hb) hpY hpU

end EremenkosConjecture
