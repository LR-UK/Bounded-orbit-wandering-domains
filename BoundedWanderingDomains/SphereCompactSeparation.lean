/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SpherePole
import Mathlib.Topology.Separation.Regular

/-!
# Separating compact spherical cluster and singular sets

Disjoint compact subsets of the sphere admit disjoint compact neighbourhoods.
This supplies the order of choices in the derived-singular-set argument.
-/

open Set OnePoint
open scoped Topology

namespace BoundedWanderingDomains

theorem exists_disjoint_compact_sphere_neighborhoods
    {C D : Set (OnePoint ℂ)} (hC : IsCompact C) (hD : IsCompact D)
    (hCD : Disjoint C D) :
    ∃ K L : Set (OnePoint ℂ), IsCompact K ∧ IsCompact L ∧
      Disjoint K L ∧ C ⊆ interior K ∧ D ⊆ interior L := by
  have hCD' : C ⊆ Dᶜ := by
    intro z hzC hzD
    exact Set.disjoint_left.mp hCD hzC hzD
  obtain ⟨U, hU, hCU, hUD, hUc⟩ :=
    exists_open_between_and_isCompact_closure hC hD.isClosed.isOpen_compl hCD'
  have hDc : D ⊆ (closure U)ᶜ := by
    intro z hzD hzU
    exact hUD hzU hzD
  obtain ⟨V, hV, hDV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hD isClosed_closure.isOpen_compl hDc
  refine ⟨closure U, closure V, hUc, hVc, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro z hzU hzV
    exact hVU hzV hzU
  · exact hCU.trans (hU.subset_interior_iff.mpr subset_closure)
  · exact hDV.trans (hV.subset_interior_iff.mpr subset_closure)

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.exists_disjoint_compact_sphere_neighborhoods
