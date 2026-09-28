/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalMapPunctureBarrier

/-! # Finite forward-invariant barriers from the actual source frontier -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] in
theorem sourceExhaustiveBackwardTree_forward (f : LocalMap X)
    (K : ℕ → Set f.source) (Q : ℕ → Set X)
    (hQ : ∀ n, Disjoint (Q n) (f.source : Set X)) (n : ℕ) :
    ∀ x : f.source, (x : X) ∈ f.sourceExhaustiveBackwardTree K Q n →
      f.map x ∈ f.sourceExhaustiveBackwardTree K Q n := by
  induction n with
  | zero =>
      intro x hx
      exact False.elim (disjoint_left.mp (hQ 0) hx x.property)
  | succ n ih =>
      intro x hx
      rcases hx with ((hx | hx) | ⟨y, hy, he⟩)
      · exact Or.inl (Or.inl (ih x hx))
      · exact False.elim (disjoint_left.mp (hQ (n + 1)) hx x.property)
      · have hey : y = x := Subtype.ext he
        exact Or.inl (Or.inl (hey ▸ hy.2))

theorem exists_forward_source_finitePuncture_barrier (f : LocalMap X)
    (hf : IsOpenHolomorphic f) {R : Set X} (hRo : IsOpen R)
    (hRs : R ⊆ f.source)
    (hRf : ∀ x (hx : x ∈ R), f.map ⟨x, hRs hx⟩ ∈ R) :
    ∃ P : ℕ → Finset X, Monotone P ∧
      frontier (f.source : Set X) ⊆ closure (⋃ n, (P n : Set X)) ∧
      (∀ n (x : f.source), (x : X) ∈ P n → f.map x ∈ P n) ∧
      (∀ x : f.source, f.map x ∈ closure (⋃ n, (P n : Set X)) →
        (x : X) ∈ closure (⋃ n, (P n : Set X))) ∧
      Disjoint (closure (⋃ n, (P n : Set X))) R := by
  classical
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  obtain ⟨Q, hQm, hQfront, hQcl⟩ :=
    AreaDeficit.Surfaces.closed_set_dense_finite_exhaustion
      (isClosed_frontier : IsClosed (frontier (f.source : Set X)))
  let roots : ℕ → Set X := fun n => (Q n : Set X)
  let K : CompactExhaustion f.source := CompactExhaustion.choice f.source
  let Pset := f.sourceExhaustiveBackwardTree K roots
  have hPfin : ∀ n, (Pset n).Finite :=
    f.sourceExhaustiveBackwardTree_finite hf K.isCompact (fun n => (Q n).finite_toSet)
  let P : ℕ → Finset X := fun n => (hPfin n).toFinset
  have hPcoe : ∀ n, (P n : Set X) = Pset n := fun n => (hPfin n).coe_toFinset
  have hPm : Monotone P := fun n m hnm x hx =>
    (hPfin m).mem_toFinset.mpr (f.sourceExhaustiveBackwardTree_mono K roots hnm
      ((hPfin n).mem_toFinset.mp hx))
  have hroots : ∀ n, Disjoint (roots n) (f.source : Set X) := fun n =>
    (disjoint_frontier_iff_isOpen.mpr f.source.isOpen).mono_left (hQfront n)
  refine ⟨P, hPm, ?_, ?_, ?_, ?_⟩
  · simp_rw [hPcoe]
    rw [← hQcl]
    apply closure_mono
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, f.roots_subset_sourceExhaustiveBackwardTree n hn⟩
  · intro n x hx
    apply (hPfin n).mem_toFinset.mpr
    exact f.sourceExhaustiveBackwardTree_forward K roots hroots n x
      ((hPfin n).mem_toFinset.mp hx)
  · simp_rw [hPcoe]
    exact f.closure_source_backward_invariant hf.1
      (f.sourceExhaustiveBackwardTree_union_backward (OrderHomClass.mono K) K.iUnion_eq)
  · simp_rw [hPcoe]
    exact f.sourceExhaustiveBackwardTree_disjoint_forwardInvariant
      (fun n => (hroots n).mono_right hRs) hRo hRs hRf

end SurfaceDynamics.LocalMap
