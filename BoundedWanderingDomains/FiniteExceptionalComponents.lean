/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphericalDerivedSet

/-!
# Avoiding finitely many exceptional values along a wandering orbit

A finite collection of points meets only finitely many pairwise disjoint
Fatou components. Hence all sufficiently late components avoid that set.
-/

open Set Filter

namespace BoundedWanderingDomains

/-- Only finitely many members of a pairwise disjoint family meet a given
finite set. No dynamical assumptions are needed. -/
theorem finite_components_meeting_finite_set
    {α : Type*} [DecidableEq α]
    (U : ℕ → Set α) (hU : Pairwise (fun n m => Disjoint (U n) (U m)))
    (E : Finset α) :
    {n : ℕ | (U n ∩ (↑E : Set α)).Nonempty}.Finite := by
  have hs (x : α) : {n : ℕ | x ∈ U n}.Subsingleton := by
    intro n hn m hm
    by_contra hnm
    exact Set.disjoint_left.mp (hU hnm) hn hm
  have hall : (⋃ x ∈ (↑E : Set α), {n : ℕ | x ∈ U n}).Finite :=
    E.finite_toSet.biUnion (fun x _ => (hs x).finite)
  apply hall.subset
  rintro n ⟨x, hxU, hxE⟩
  exact mem_iUnion₂.mpr ⟨x, hxE, hxU⟩

/-- Every sufficiently late member of a pairwise disjoint family avoids a
fixed finite exceptional set. -/
theorem eventually_components_avoid_finite_set
    {α : Type*} [DecidableEq α]
    (U : ℕ → Set α) (hU : Pairwise (fun n m => Disjoint (U n) (U m)))
    (E : Finset α) :
    ∀ᶠ n : ℕ in atTop, Disjoint (U n) (↑E : Set α) := by
  have hfin := finite_components_meeting_finite_set U hU E
  obtain ⟨N, hN⟩ := hfin.exists_le
  filter_upwards [eventually_gt_atTop N] with n hn
  apply Set.disjoint_left.mpr
  intro x hxU hxE
  exact (not_le_of_gt hn) (hN n ⟨x, hxU, hxE⟩)

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.eventually_components_avoid_finite_set
