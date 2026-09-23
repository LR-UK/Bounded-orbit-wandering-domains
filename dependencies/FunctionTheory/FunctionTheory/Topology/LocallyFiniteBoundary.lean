import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Closure

open Set

namespace FunctionTheory

set_option autoImplicit false

/-- Every boundary point of a locally finite union of closed sets belongs
to the boundary of one member. -/
theorem frontier_iUnion_subset_of_locallyFinite
    {E I : Type*} [TopologicalSpace E] (K : I → Set E)
    (hloc : LocallyFinite K) (hclosed : ∀ i, IsClosed (K i)) :
    frontier (⋃ i, K i) ⊆ ⋃ i, frontier (K i) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp ((hloc.isClosed_iUnion hclosed).frontier_subset hx)
  refine mem_iUnion.mpr ⟨i, (mem_frontier_iff_notMem_interior hi).2 ?_⟩
  exact fun h => hx.2 (interior_mono (subset_iUnion K i) h)

end FunctionTheory
