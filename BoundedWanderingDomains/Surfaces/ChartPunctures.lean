/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Analysis.Complex.Basic

/-! # Finite punctures in a partial chart -/
open Set Function
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M]

/-- Coordinates of punctures lying in the source of a partial chart. -/
noncomputable def chartPunctures (c : OpenPartialHomeomorph M ℂ)
    (P : Finset M) : Finset ℂ := by
  classical
  exact (P.filter (fun x => x ∈ c.source)).image c

theorem mem_chartPunctures_iff (c : OpenPartialHomeomorph M ℂ)
    (P : Finset M) {z : ℂ} (hz : z ∈ c.target) :
    z ∈ chartPunctures c P ↔ c.symm z ∈ P := by
  classical
  constructor
  · intro hzP
    obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hzP
    have hx' := (Finset.mem_filter.mp hx)
    have heq : c.symm z = x := by
      rw [← hxz, c.left_inv hx'.2]
    exact heq ▸ hx'.1
  · intro hx
    exact Finset.mem_image.mpr ⟨c.symm z,
      Finset.mem_filter.mpr ⟨hx,c.map_target hz⟩, c.right_inv hz⟩

theorem chartPunctures_mono (c : OpenPartialHomeomorph M ℂ) :
    Monotone (chartPunctures c) := by
  classical
  intro P Q hPQ
  exact Finset.image_mono c (Finset.filter_subset_filter _ hPQ)

theorem chartPunctures_mem_closure (c : OpenPartialHomeomorph M ℂ)
    (P : ℕ → Finset M) {x : M} (hxc : x ∈ c.source)
    (hx : x ∈ closure (⋃ n, (P n : Set M))) :
    c x ∈ closure (⋃ n, (chartPunctures c (P n) : Set ℂ)) := by
  classical
  apply mem_closure_iff.mpr
  intro V hV hxV
  obtain ⟨y,hy,hPy⟩ := mem_closure_iff.mp hx
    (c.source ∩ c ⁻¹' V) (c.isOpen_inter_preimage hV) ⟨hxc,hxV⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp hPy
  refine ⟨c y,hy.2,mem_iUnion.mpr ⟨n,?_⟩⟩
  exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hn,hy.1⟩,rfl⟩

end AreaDeficit.Surfaces
