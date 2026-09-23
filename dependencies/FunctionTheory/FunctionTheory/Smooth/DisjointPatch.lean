import FunctionTheory.Topology.DisjointPatch
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Homeomorph.Defs

open Set Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Locally finite disjoint patches preserve arbitrary real differentiability
orders, including at the boundary of every patch. -/
theorem contDiff_disjointPatch
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : ι → Set E) (f : ι → E → F) (g : E → F)
    (hfinite : LocallyFinite U)
    (hdis : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))))
    (hout : ∀ i, EqOn (f i) g (U i)ᶜ) (m : ℕ∞ω)
    (hf : ∀ i, ContDiff ℝ m (f i)) (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (disjointPatch U f g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  rcases disjointPatch_eventuallyEq U f g hfinite hdis hout x with H | ⟨i, _, H⟩
  · exact hg.contDiffAt.congr_of_eventuallyEq H
  · exact (hf i).contDiffAt.congr_of_eventuallyEq H

/-- The patch of the inverse homeomorphisms is an inverse to the patch
of homeomorphisms supported on disjoint sets. -/
theorem disjointPatch_homeomorph_leftInverse
    {E ι : Type*} [TopologicalSpace E]
    (U : ι → Set E) (e : ι → E ≃ₜ E)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hout : ∀ i, EqOn (e i : E → E) id (U i)ᶜ) :
    Function.LeftInverse
      (disjointPatch U (fun i => ((e i).symm : E → E)) id)
      (disjointPatch U (fun i => (e i : E → E)) id) := by
  classical
  have hmap : ∀ i, MapsTo (e i) (U i) (U i) := by
    intro i z hz
    by_contra H
    have he : e i z = z := (e i).injective (hout i H)
    rw [he] at H
    exact H hz
  intro z
  by_cases hz : ∃ i, z ∈ U i
  · obtain ⟨i, hi⟩ := hz
    rw [disjointPatch_of_mem U (fun i => (e i : E → E)) id hdis hi,
      disjointPatch_of_mem U (fun i => ((e i).symm : E → E)) id hdis (hmap i hi)]
    exact (e i).symm_apply_apply z
  · have H : ∀ i, z ∉ U i := fun i hi => hz ⟨i, hi⟩
    rw [disjointPatch_of_notMem U (fun i => (e i : E → E)) id H]
    exact disjointPatch_of_notMem U (fun i => ((e i).symm : E → E)) id H

/-- A locally finite family of smooth homeomorphisms with disjoint support
closures glues to one global smooth homeomorphism with a smooth inverse. -/
theorem exists_disjoint_smooth_homeomorph
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : ι → Set E) (e : ι → E ≃ₜ E)
    (hfinite : LocallyFinite U)
    (hdis : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))))
    (hout : ∀ i, EqOn (e i : E → E) id (U i)ᶜ)
    (he : ∀ i, ContDiff ℝ ∞ (e i : E → E))
    (hei : ∀ i, ContDiff ℝ ∞ ((e i).symm : E → E)) :
    ∃ Θ : E ≃ₜ E, ContDiff ℝ ∞ (Θ : E → E) ∧
      ContDiff ℝ ∞ (Θ.symm : E → E) ∧
      (∀ i, EqOn (Θ : E → E) (e i : E → E) (U i)) ∧
      EqOn (Θ : E → E) id (⋃ i, U i)ᶜ := by
  have hpair : Pairwise (fun i j => Disjoint (U i) (U j)) :=
    fun i j hij => (hdis hij).mono subset_closure subset_closure
  have hiout : ∀ i, EqOn ((e i).symm : E → E) id (U i)ᶜ := by
    intro i z hz
    apply (e i).injective
    simpa only [Homeomorph.apply_symm_apply, id_eq] using (hout i hz).symm
  let F := disjointPatch U (fun i => (e i : E → E)) id
  let G := disjointPatch U (fun i => ((e i).symm : E → E)) id
  have HF : ContDiff ℝ ∞ F :=
    contDiff_disjointPatch U _ id hfinite hdis hout ∞ he contDiff_id
  have HG : ContDiff ℝ ∞ G :=
    contDiff_disjointPatch U _ id hfinite hdis hiout ∞ hei contDiff_id
  have HL : Function.LeftInverse G F :=
    disjointPatch_homeomorph_leftInverse U e hpair hout
  have HR : Function.RightInverse G F := by
    simpa only [F, G, Homeomorph.symm_symm, Function.RightInverse] using
      disjointPatch_homeomorph_leftInverse U (fun i => (e i).symm) hpair hiout
  let Θ : E ≃ₜ E := {
    toFun := F
    invFun := G
    left_inv := HL
    right_inv := HR
    continuous_toFun := HF.continuous
    continuous_invFun := HG.continuous
  }
  refine ⟨Θ, HF, HG, ?_, ?_⟩
  · intro i z hz
    exact disjointPatch_of_mem U (fun i => (e i : E → E)) id hpair hz
  · intro z hz
    exact disjointPatch_of_notMem U (fun i => (e i : E → E)) id
      (fun i hi => hz (mem_iUnion.mpr ⟨i, hi⟩))

end FunctionTheory
