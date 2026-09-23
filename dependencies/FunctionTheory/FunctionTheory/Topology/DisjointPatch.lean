import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Replace a background function by specified functions on disjoint pieces. -/
noncomputable def disjointPatch {E F ι : Type*} (U : ι → Set E)
    (f : ι → E → F) (g : E → F) (z : E) : F := by
  classical
  exact if h : ∃ i, z ∈ U i then f (Classical.choose h) z else g z

theorem disjointPatch_of_mem {E F ι : Type*} (U : ι → Set E)
    (f : ι → E → F) (g : E → F)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    {i : ι} {z : E} (hz : z ∈ U i) :
    disjointPatch U f g z = f i z := by
  classical
  have H : ∃ j, z ∈ U j := ⟨i, hz⟩
  have hi : Classical.choose H = i := by
    by_contra h
    exact Set.disjoint_left.mp (hdis h) (Classical.choose_spec H) hz
  simp only [disjointPatch, dif_pos H, hi]

theorem disjointPatch_of_notMem {E F ι : Type*} (U : ι → Set E)
    (f : ι → E → F) (g : E → F) {z : E}
    (hz : ∀ i, z ∉ U i) : disjointPatch U f g z = g z := by
  classical
  exact dif_neg (by rintro ⟨i, hi⟩; exact hz i hi)

/-- Near every point a locally finite patch with disjoint closures agrees
with one complete component function or with the background function.
This also handles points on the boundaries of the pieces. -/
theorem disjointPatch_eventuallyEq {E F ι : Type*} [TopologicalSpace E]
    (U : ι → Set E) (f : ι → E → F) (g : E → F)
    (hfinite : LocallyFinite U)
    (hdis : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))))
    (hout : ∀ i, EqOn (f i) g (U i)ᶜ) (x : E) :
    disjointPatch U f g =ᶠ[𝓝 x] g ∨
      ∃ i, x ∈ closure (U i) ∧ disjointPatch U f g =ᶠ[𝓝 x] f i := by
  classical
  have hpair : Pairwise (fun i j => Disjoint (U i) (U j)) :=
    fun i j hij => (hdis hij).mono subset_closure subset_closure
  have Hnbhd := hfinite.closure.eventually_subset (fun _ => isClosed_closure) x
  by_cases hx : ∃ i, x ∈ closure (U i)
  · obtain ⟨i, hi⟩ := hx
    refine Or.inr ⟨i, hi, ?_⟩
    filter_upwards [Hnbhd] with y hy
    by_cases hyU : ∃ j, y ∈ U j
    · obtain ⟨j, hj⟩ := hyU
      have hjx : x ∈ closure (U j) := hy (subset_closure hj)
      have hji : j = i := by
        by_contra h
        exact Set.disjoint_left.mp (hdis h) hjx hi
      subst j
      exact disjointPatch_of_mem U f g hpair hj
    · have hyi : y ∉ U i := fun H => hyU ⟨i, H⟩
      exact (disjointPatch_of_notMem U f g (fun j hj => hyU ⟨j, hj⟩)).trans
        (hout i hyi).symm
  · refine Or.inl ?_
    filter_upwards [Hnbhd] with y hy
    apply disjointPatch_of_notMem U f g
    intro i hi
    exact hx ⟨i, hy (subset_closure hi)⟩

end FunctionTheory
