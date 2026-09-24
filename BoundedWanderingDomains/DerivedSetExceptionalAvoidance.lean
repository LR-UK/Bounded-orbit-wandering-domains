/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.FiniteExceptionalComponents

/-!
# Avoiding singular values outside a neighbourhood of their spherical derived set

For any planar set of values and any open spherical neighbourhood of its
derived set, only finitely many values lie outside that neighbourhood. A
pairwise disjoint sequence of components therefore eventually avoids them.
-/

open Set Filter

namespace BoundedWanderingDomains

/-- Late members of a pairwise disjoint sequence avoid every value outside
an open neighbourhood of the spherical derived set. -/
theorem eventually_components_avoid_outside_spherical_derived_neighbourhood
    (S : Set ℂ) (O : Set (OnePoint ℂ)) (hO : IsOpen O)
    (hder : sphericalDerivedSet S ⊆ O)
    (U : ℕ → Set ℂ) (hU : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∀ᶠ n : ℕ in atTop,
      Disjoint (U n) {z : ℂ | z ∈ S ∧ (z : OnePoint ℂ) ∉ O} := by
  let E : Set ℂ := {z : ℂ | z ∈ S ∧ (z : OnePoint ℂ) ∉ O}
  have hE : E.Finite :=
    finite_planar_outside_spherical_derived_neighbourhood S O hO hder
  classical
  simpa only [hE.coe_toFinset] using
    (eventually_components_avoid_finite_set U hU hE.toFinset)

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.eventually_components_avoid_outside_spherical_derived_neighbourhood
