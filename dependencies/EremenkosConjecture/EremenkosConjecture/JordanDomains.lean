import EremenkosConjecture.NestedJordanNeighbourhoods
import Schoenflies.JordanClosed

/-! # Recognizing bounded Jordan domains

A bounded connected open set is the bounded complementary region of its
Jordan frontier. This identifies the interiors of our regular compact
neighbourhoods with the public Schoenflies notion of inside.
-/

open Set Schoenflies

namespace EremenkosConjecture

theorem eq_inside_frontier_of_bounded_domain {U : Set Plane}
    (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (hJ : IsJordanCurve (frontier U)) : U = inside (frontier U) := by
  obtain ⟨z, hz⟩ := hUc.nonempty
  have hsub : U ⊆ (frontier U)ᶜ := by
    intro w hw hf
    exact (hUo.frontier_eq ▸ hf).2 hw
  have hcomp : connectedComponentIn (frontier U)ᶜ z = U :=
    Plane.connectedComponentIn_eq_of_frontier_disjoint hUo hUc.isPreconnected
      hsub (by simp) hz
  have hzi : z ∈ inside (frontier U) := ⟨hsub hz, hcomp.symm ▸ hUb⟩
  exact hcomp.symm.trans ((jordan_curve_theorem hJ).connectedComponentIn_eq_inside hzi)

theorem interior_eq_inside_frontier_of_regular_compact {K : Set Plane}
    (hK : IsCompact K) (hKi : IsConnected (interior K))
    (hreg : K = closure (interior K)) (hJ : IsJordanCurve (frontier K)) :
    interior K = inside (frontier K) := by
  have hfr : frontier (interior K) = frontier K := by
    rw [frontier, hreg.symm, interior_interior, hK.isClosed.frontier_eq]
  have h := eq_inside_frontier_of_bounded_domain isOpen_interior hKi
    (hK.isBounded.subset interior_subset) (hfr.symm ▸ hJ)
  rwa [hfr] at h

end EremenkosConjecture
