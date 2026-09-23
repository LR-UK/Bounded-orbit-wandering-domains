import EremenkosConjecture.PlaneSimpleConnectivity
import ComplexApproximation.Topology.FillingInterior

open Set

namespace EremenkosConjecture

/-- Every component of the interior of a set with no bounded complementary
components is simply connected. Compact loop images can first be filled
inside that interior and then enclosed in a Jordan neighbourhood. -/
theorem isSimplyConnected_component_interior_of_noBoundedComplementComponents
    {F : Set ℂ} {z : ℂ} (hF : ComplexApproximation.NoBoundedComplementComponents F)
    (hz : z ∈ interior F) :
    IsSimplyConnected (connectedComponentIn (interior F) z) := by
  apply FunctionTheory.isSimplyConnected_of_compact_connected_subsets
    isOpen_interior.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hz)
  intro K hK hKc hKU
  let L := ComplexApproximation.fill K
  have hLcompact : IsCompact L := ComplexApproximation.isCompact_fill hK
  have hLconn : IsConnected L := ComplexApproximation.isConnected_fill hK.isClosed hKc
  have hLfull : IsConnected Lᶜ := ComplexApproximation.isConnected_compl_fill hK
  have hLI : L ⊆ interior F :=
    ComplexApproximation.fill_subset_interior_of_noBoundedComplementComponents hK.isClosed
      (hKU.trans (connectedComponentIn_subset _ _)) hF
  obtain ⟨N, _, _, hNI⟩ := exists_nested_jordan_neighbourhoods_within
    L (interior F) hLcompact hLconn hLfull isOpen_interior hLI
  have hKN : K ⊆ interior (N 0).carrier :=
    (ComplexApproximation.subset_fill K).trans (N 0).contains
  refine ⟨interior (N 0).carrier, (N 0).simplyConnectedInterior, hKN, ?_⟩
  obtain ⟨p, hp⟩ := hKc.nonempty
  have hsub := (N 0).connectedInterior.isPreconnected.subset_connectedComponentIn
    (hKN hp) (interior_subset.trans hNI)
  rwa [← connectedComponentIn_eq (hKU hp)] at hsub

theorem isSimplyConnected_component_interior_fill
    {E : Set ℂ} {z : ℂ} (hz : z ∈ interior (ComplexApproximation.fill E)) :
    IsSimplyConnected (connectedComponentIn (interior (ComplexApproximation.fill E)) z) :=
  isSimplyConnected_component_interior_of_noBoundedComplementComponents
    (ComplexApproximation.noBoundedComplementComponents_fill E) hz

end EremenkosConjecture
