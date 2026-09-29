module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.Disjointed

@[expose] public section
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces
variable (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
/-- A measurable partition subordinate to holomorphic charts, without metric assumptions. -/
structure ChartPartition where
  chart : ℕ → OpenPartialHomeomorph M ℂ
  holomorphic : ∀ n, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (chart n) (chart n).source
  piece : ℕ → Set M
  measurable : ∀ n, MeasurableSet (piece n)
  subordinate : ∀ n, piece n ⊆ (chart n).source
  disjoint : Pairwise (Disjoint on piece)
  covers : ⋃ n, piece n = univ
variable {M}
theorem exists_chartPartition [SecondCountableTopology M] [Nonempty M] :
    Nonempty (ChartPartition M) := by
  obtain ⟨s,hsc,hcover⟩ := countable_cover_nhds (fun x : M => chart_source_mem_nhds ℂ x)
  have hs : s.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty M›
    have hx : x ∈ ⋃ y ∈ s, (chartAt ℂ y).source := hcover ▸ mem_univ x
    rcases mem_iUnion.mp hx with ⟨y,hy⟩
    rcases mem_iUnion.mp hy with ⟨hys,_⟩
    exact ⟨y,hys⟩
  obtain ⟨a,ha⟩ := hsc.exists_eq_range hs
  let c := fun n => chartAt ℂ (a n)
  let V := fun n => (c n).source
  have hV : ⋃ n, V n = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ y ∈ s, (chartAt ℂ y).source := hcover ▸ mem_univ x
    rcases mem_iUnion.mp hx with ⟨y,hy⟩
    rcases mem_iUnion.mp hy with ⟨hys,hxy⟩
    rw [ha] at hys
    obtain ⟨n,rfl⟩ := hys
    exact mem_iUnion.mpr ⟨n,hxy⟩
  refine ⟨⟨c,?_,disjointed V,?_,?_,disjoint_disjointed V,?_⟩⟩
  · intro n x hx
    exact (mdifferentiableAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) hx).mdifferentiableWithinAt
  · exact MeasurableSet.disjointed (fun n => (c n).open_source.measurableSet)
  · exact disjointed_subset V
  · rw [iUnion_disjointed,hV]
end AreaDeficit.Surfaces
