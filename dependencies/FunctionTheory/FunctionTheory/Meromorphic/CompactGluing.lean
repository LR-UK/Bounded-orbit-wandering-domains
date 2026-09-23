import FunctionTheory.Topology.LocallyFiniteCompactFamily
import FunctionTheory.Topology.DisjointPatch
import Mathlib.Analysis.Meromorphic.Basic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Arbitrary functions can be glued on full neighbourhoods of finitely many
disjoint compact sets. The equality is a germ equality, not merely equality
on the compact sets themselves. -/
theorem exists_function_with_germs_on_disjoint_compacts
    {E F ι : Type*} [PseudoMetricSpace E] [T2Space E] [Finite ι]
    (K : ι → Set E) (f : ι → E → F) (g₀ : E → F)
    (hK : ∀ i, IsCompact (K i))
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ g : E → F, ∀ i a, a ∈ K i → g =ᶠ[𝓝 a] f i := by
  obtain ⟨r, hr, _, _, hpair⟩ := exists_disjoint_closed_thickenings K (fun _ => univ)
    hK (locallyFinite_of_finite K) hdis (fun _ => isOpen_univ) (fun _ => subset_univ _)
  let V : ι → Set E := fun i => thickening (r i) (K i)
  have hVpair : Pairwise (fun i j => Disjoint (V i) (V j)) := fun i j hij =>
    (hpair hij).mono (thickening_subset_cthickening _ _) (thickening_subset_cthickening _ _)
  refine ⟨disjointPatch V f g₀, ?_⟩
  intro i a ha
  have haV : a ∈ V i := self_subset_thickening (hr i) (K i) ha
  filter_upwards [isOpen_thickening.mem_nhds haV] with z hz
  exact disjointPatch_of_mem V f g₀ hVpair hz

/-- Meromorphic data on finitely many disjoint compact pieces have a common
meromorphic germ on their union, as required by the Runge construction. -/
theorem exists_meromorphic_gluing_on_disjoint_compacts
    {ι : Type*} [Finite ι] (K : ι → Set ℂ) (f : ι → ℂ → ℂ)
    (hK : ∀ i, IsCompact (K i))
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hf : ∀ i, MeromorphicOn (f i) (K i)) :
    ∃ g : ℂ → ℂ, MeromorphicOn g (⋃ i, K i) ∧
      ∀ i a, a ∈ K i → g =ᶠ[𝓝 a] f i := by
  obtain ⟨g, hg⟩ := exists_function_with_germs_on_disjoint_compacts K f (fun _ => 0) hK hdis
  refine ⟨g, ?_, hg⟩
  intro a ha
  obtain ⟨i, hi⟩ := mem_iUnion.mp ha
  exact (hf i a hi).congr ((hg i a hi).symm.filter_mono nhdsWithin_le_nhds)

end FunctionTheory
