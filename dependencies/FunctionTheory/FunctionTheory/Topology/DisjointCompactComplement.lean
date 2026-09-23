import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A connected noncompact space cannot be covered by a locally finite
family of pairwise disjoint compact sets. -/
theorem iUnion_ne_univ_of_locallyFinite_disjoint_compacts
    {E ι : Type*} [TopologicalSpace E] [T2Space E]
    [ConnectedSpace E] [NoncompactSpace E]
    (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hfinite : LocallyFinite K)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j))) :
    (⋃ i, K i) ≠ univ := by
  classical
  intro hcover
  let x : E := Classical.arbitrary E
  have hx : x ∈ ⋃ i, K i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  let O : Set E := ⋃ j : {j : ι // j ≠ i}, K j
  have hO : IsClosed O :=
    (hfinite.comp_injective (g := fun j : {j : ι // j ≠ i} => (j : ι))
      Subtype.val_injective).isClosed_iUnion (fun j => (hK j).isClosed)
  have hcompl : (K i)ᶜ = O := by
    ext z
    constructor
    · intro hz
      have hzall : z ∈ ⋃ j, K j := by rw [hcover]; trivial
      obtain ⟨j, hj⟩ := mem_iUnion.mp hzall
      have hji : j ≠ i := by intro h; subst j; exact hz hj
      exact mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hz hi
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact Set.disjoint_left.mp (hdis j.property) hj hi
  have hopen : IsOpen (K i) := by
    apply isClosed_compl_iff.mp
    rw [hcompl]
    exact hO
  exact (hK i).ne_univ (IsClopen.eq_univ ⟨(hK i).isClosed, hopen⟩ ⟨x, hi⟩)

/-- There is a positive closed ball avoiding the whole compact family.
This supplies a trapping-disc location independently of the approximation
construction. -/
theorem exists_closedBall_disjoint_locallyFinite_compacts
    {E ι : Type*} [MetricSpace E] [ConnectedSpace E] [NoncompactSpace E]
    (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hfinite : LocallyFinite K)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ (c : E) (r : ℝ), 0 < r ∧ Disjoint (closedBall c r) (⋃ i, K i) := by
  have hne := iUnion_ne_univ_of_locallyFinite_disjoint_compacts K hK hfinite hdis
  have Hex : ∃ c : E, c ∉ ⋃ i, K i := by
    by_contra! H
    exact hne (eq_univ_of_forall H)
  obtain ⟨c, hc⟩ := Hex
  have hopen : IsOpen (⋃ i, K i)ᶜ :=
    (hfinite.isClosed_iUnion (fun i => (hK i).isClosed)).isOpen_compl
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hc)
  exact ⟨c, r, hr, Set.disjoint_left.mpr (fun z hz hKz => hsub hz hKz)⟩

end FunctionTheory
