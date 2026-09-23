import ComplexApproximation.Topology.FilledContinua

open Set

namespace ComplexApproximation

/-- A compact set lying inside a filled set can be filled without reaching
that set's boundary. Each added hole is itself an open subset of the filling. -/
theorem fill_subset_interior_of_noBoundedComplementComponents
    {K F : Set ℂ} (hK : IsClosed K) (hKF : K ⊆ interior F)
    (hF : NoBoundedComplementComponents F) : fill K ⊆ interior F := by
  have hfill : fill K ⊆ F :=
    fill_subset_of_noBoundedComplementComponents (hKF.trans interior_subset) hF
  intro z hz
  by_cases hzK : z ∈ K
  · exact hKF hzK
  let C := connectedComponentIn Kᶜ z
  have hCo : IsOpen C := hK.isOpen_compl.connectedComponentIn
  have hCF : C ⊆ F := by
    intro w hw
    apply hfill
    change Bornology.IsBounded (connectedComponentIn Kᶜ w)
    exact (connectedComponentIn_eq hw) ▸ hz
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hCo.mem_nhds (mem_connectedComponentIn hzK)) hCF)

end ComplexApproximation
