module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EmbeddedDisc
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! # Hyperbolising anchors outside compact inner target sets -/

open Set Function Topology
open AreaDeficit.Surfaces

namespace SurfaceDynamics

theorem unitDisc_univ_not_isCompact : ¬ IsCompact (univ : Set unitDisc) := by
  intro hc
  have him : IsCompact (unitDisc : Set ℂ) := by
    have hh := hc.image (continuous_subtype_val : Continuous (Subtype.val : unitDisc → ℂ))
    convert hh using 1
    ext x
    simp
  have he : (unitDisc : Set ℂ) = univ :=
    (show IsClopen (unitDisc : Set ℂ) from ⟨him.isClosed, unitDisc.isOpen⟩).eq_univ
      ⟨0, by simp [unitDisc]⟩
  have h1 : (1 : ℂ) ∈ (unitDisc : Set ℂ) := by rw [he]; trivial
  simp [unitDisc] at h1

theorem compact_subset_embeddedDisc_ne_univ
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : EmbeddedDisc X) {L : Set X} (hL : IsCompact L) (hLQ : L ⊆ Q.carrier) :
    L ≠ univ := by
  intro he
  have hrange : range Q.param = univ := eq_univ_of_forall fun x => hLQ (he.symm ▸ mem_univ x)
  apply unitDisc_univ_not_isCompact
  apply Q.embedding.isEmbedding.isCompact_iff.mpr
  rw [image_univ, hrange]
  exact he ▸ hL

theorem exists_three_anchors_disjoint_proper_compact
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [Nontrivial X]
    {L : Set X} (hL : IsCompact L) (hLne : L ≠ univ) :
    ∃ F : Finset X, F.card = 3 ∧ Disjoint L (F : Set X) := by
  classical
  obtain ⟨a, ha⟩ : Lᶜ.Nonempty := nonempty_compl.mpr hLne
  have hLi : Lᶜ.Infinite := infinite_of_mem_nhds a (hL.isClosed.isOpen_compl.mem_nhds ha)
  obtain ⟨b, hbL, hba⟩ := hLi.exists_notMem_finite (Set.finite_singleton a)
  obtain ⟨c, hcL, hcab⟩ := hLi.exists_notMem_finite (Set.toFinite {a, b})
  have hab : a ≠ b := by simpa only [mem_singleton_iff, ne_eq, eq_comm] using hba
  have hac : a ≠ c := fun he => hcab (by simp [he])
  have hbc : b ≠ c := fun he => hcab (by simp [he])
  refine ⟨{a, b, c}, by simp [hab, hac, hbc], ?_⟩
  apply disjoint_left.mpr
  intro x hx hxF
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hxF
  rcases hxF with rfl | rfl | rfl
  · exact ha hx
  · exact hbL hx
  · exact hcL hx

theorem exists_three_anchors_disjoint_compact_in_disc
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [Nontrivial X]
    (Q : EmbeddedDisc X) {L : Set X} (hL : IsCompact L) (hLQ : L ⊆ Q.carrier) :
    ∃ F : Finset X, F.card = 3 ∧ Disjoint L (F : Set X) :=
  exists_three_anchors_disjoint_proper_compact hL (compact_subset_embeddedDisc_ne_univ Q hL hLQ)

end SurfaceDynamics


