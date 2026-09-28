/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.BoundaryPunctureSequence

/-! # Countable backward exceptional sets in a working surface domain -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Enlarge an increasing finite puncture sequence by a fixed finite set and
all local backward iterates.  The result remains an increasing sequence of
finite sets, while its union is backward invariant in the working domain. -/
theorem exists_backwardExceptionalFinsets
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (V : TopologicalSpace.Opens X)
    (hVcompact : IsCompact (closure (V : Set X)))
    (hVsource : closure (V : Set X) ⊆ f.source)
    (P : ℕ → Finset X) (hP : Monotone P) (E : Finset X) :
    ∃ S : ℕ → Finset X, Monotone S ∧
      (∀ n, (P n : Set X) ⊆ (S n : Set X) ∧
        (E : Set X) ⊆ (S n : Set X)) ∧
      (∀ n x (hx : x ∈ V), x ∈ S n →
        f.map ⟨x, hVsource (subset_closure hx)⟩ ∈
          (S n : Set X) ∪ f.totalize ''
            ((P n : Set X) ∪ (E : Set X))) ∧
      (∀ x (hx : x ∈ V),
        f.map ⟨x, hVsource (subset_closure hx)⟩ ∈
            (⋃ n, ((S n : Finset X) : Set X)) →
          x ∈ (⋃ n, ((S n : Finset X) : Set X))) := by
  classical
  let Q : ℕ → Set X := fun n => ((P n ∪ E : Finset X) : Set X)
  have hQmono : Monotone Q := by
    intro n m hnm x hx
    rcases Finset.mem_union.mp hx with hxP | hxE
    · exact Finset.mem_union_left E (hP hnm hxP)
    · exact Finset.mem_union_right (P m) hxE
  let R : ℕ → Set X := fun n =>
    f.boundaryBackwardTree (V : Set X) hVsource (Q n) n
  have hRmono : Monotone R := by
    intro n m hnm
    exact (f.boundaryBackwardTree_mono_roots hVsource (hQmono hnm) n).trans
      (f.boundaryBackwardTree_mono (V : Set X) hVsource (Q m) hnm)
  have hRfinite : ∀ n, (R n).Finite := fun n =>
    f.boundaryBackwardTree_finite hf hVcompact hVsource
      (P n ∪ E).finite_toSet n
  let S : ℕ → Finset X := fun n => (hRfinite n).toFinset
  have hcoe : ∀ n, ((S n : Finset X) : Set X) = R n :=
    fun n => (hRfinite n).coe_toFinset
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro n m hnm x hx
    apply (hRfinite m).mem_toFinset.mpr
    exact hRmono hnm ((hRfinite n).mem_toFinset.mp hx)
  · intro n
    constructor
    · intro x hxP
      apply (hRfinite n).mem_toFinset.mpr
      apply f.roots_subset_boundaryBackwardTree (V : Set X) hVsource (Q n) n
      exact Finset.mem_union_left E hxP
    · intro x hxE
      apply (hRfinite n).mem_toFinset.mpr
      apply f.roots_subset_boundaryBackwardTree (V : Set X) hVsource (Q n) n
      exact Finset.mem_union_right (P n) hxE
  · intro n x hxV hxS
    change x ∈ (S n : Set X) at hxS
    rw [hcoe] at hxS ⊢
    simpa only [R, Q, Finset.coe_union] using
      f.boundaryBackwardTree_forward_up_to_roots hVsource n x hxV hxS
  · intro x hx hfx
    simp_rw [hcoe] at hfx ⊢
    obtain ⟨n, hn⟩ := mem_iUnion.mp hfx
    apply mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    apply Or.inr
    refine ⟨hx, ?_⟩
    exact f.boundaryBackwardTree_mono_roots hVsource
      (hQmono (Nat.le_succ n)) n hn

end SurfaceDynamics.LocalMap
