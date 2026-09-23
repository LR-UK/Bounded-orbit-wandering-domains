import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

open Set
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A local homeomorphism defined around the compact closure of a set
carries its entire boundary onto the boundary of its image. -/
theorem image_frontier_of_compact_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X}
    (hK : IsCompact (closure S)) (hS : closure S ⊆ e.source) :
    e '' frontier S=frontier (e '' S) := by
  have hSs : S ⊆ e.source := subset_closure.trans hS
  have H : e.IsImage S (e '' S) := by
    intro x hx
    constructor
    · rintro ⟨z,hz,hzx⟩
      exact (e.injOn (hSs hz) hx hzx) ▸ hz
    · intro hxS
      exact mem_image_of_mem e hxS
  have himage : IsClosed (e '' closure S) :=
    (hK.image_of_continuousOn (e.continuousOn.mono hS)).isClosed
  have hcl : closure (e '' S) ⊆ e '' closure S :=
    himage.closure_subset_iff.mpr (image_mono subset_closure)
  have hft : frontier (e '' S) ⊆ e.target := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hcl (frontier_subset_closure hy)
    exact e.map_source (hS hz)
  have hfs : frontier S ⊆ e.source := frontier_subset_closure.trans hS
  simpa only [inter_eq_right.mpr hfs,inter_eq_right.mpr hft] using H.frontier.image_eq

end FunctionTheory
