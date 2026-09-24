/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SingularValues
import BoundedWanderingDomains.SphericalDerivedSet
import Mathlib.Topology.DiscreteSubset

/-! # The singular set in the sphere

Infinity is included as a singular value of the plane-valued dynamical map.
Adding this one point does not change the derived set. No value of the map
at infinity is defined.
-/

open Set OnePoint Filter
open scoped Topology

namespace ComplexDynamics

def sphericalSingularValues (f : ℂ → ℂ) : Set (OnePoint ℂ) :=
  insert ∞ (((↑) : ℂ → OnePoint ℂ) '' singularValues f)

theorem isClosed_sphericalSingularValues (f : ℂ → ℂ) :
    IsClosed (sphericalSingularValues f) := by
  apply (OnePoint.isClosed_iff_of_mem (show ∞ ∈ sphericalSingularValues f from Or.inl rfl)).mpr
  convert isClosed_singularValues f using 1
  ext z
  simp [sphericalSingularValues]

theorem derivedSet_sphericalSingularValues (f : ℂ → ℂ) :
    derivedSet (sphericalSingularValues f) =
      BoundedWanderingDomains.sphericalDerivedSet (singularValues f) := by
  have hsingle : derivedSet ({∞} : Set (OnePoint ℂ)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Set.Infinite.of_accPt hx) (finite_singleton _)
  rw [sphericalSingularValues, ← singleton_union, derivedSet_union, hsingle, empty_union]
  rfl

theorem infty_mem_derivedSet_sphericalSingularValues_iff (f : ℂ → ℂ) :
    ∞ ∈ derivedSet (sphericalSingularValues f) ↔ ¬ MemClassB f := by
  rw [derivedSet_sphericalSingularValues,
    BoundedWanderingDomains.infty_mem_sphericalDerivedSet_iff]
  rfl

end ComplexDynamics

#print axioms ComplexDynamics.infty_mem_derivedSet_sphericalSingularValues_iff
