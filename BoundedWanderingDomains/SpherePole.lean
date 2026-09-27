/- 
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphericalDerivedSet

/-!
# Choosing a pole away from two compact sets on the sphere

The connectedness of the sphere guarantees a coordinate pole outside both
nonempty disjoint compact sets. Empty-set cases of the area theorem are
trivial and are treated separately.
-/

open Set OnePoint
open scoped Topology

namespace AreaDeficit

/-- Two nonempty disjoint compact sets cannot cover the connected sphere. -/
theorem exists_sphere_pole_avoiding_compacts
    {K L : Set (OnePoint ℂ)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) (hKn : K.Nonempty) (hLn : L.Nonempty) :
    ∃ p : OnePoint ℂ, p ∉ K ∪ L := by
  by_contra h
  have hcover : K ∪ L = Set.univ := by
    apply eq_univ_of_forall
    intro p
    by_contra hp
    exact h ⟨p, hp⟩
  have hKcompl : Kᶜ = L := by
    ext p
    constructor
    · intro hp
      rcases (Set.eq_univ_iff_forall.mp hcover p) with hpK | hpL
      · exact (hp hpK).elim
      · exact hpL
    · intro hpL hpK
      exact Set.disjoint_left.mp hKL hpK hpL
  have hKclopen : IsClopen K := by
    constructor
    · exact hK.isClosed
    · rw [← compl_compl K, hKcompl]
      exact hL.isClosed.isOpen_compl
  have hKuniv : K = Set.univ := hKclopen.eq_univ hKn
  obtain ⟨p, hp⟩ := hLn
  exact Set.disjoint_left.mp hKL (hKuniv.symm ▸ Set.mem_univ p) hp

end AreaDeficit
