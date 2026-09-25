/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.ChartMapAreaTransport

/-! # Assembly of one-step area transport over finitely many patches -/

open Set MeasureTheory
open scoped ENNReal

namespace AreaDeficit.Surfaces

/-- Local area-advance inequalities add over a finite measurable partition.
Injectivity makes the image patches disjoint as well. -/
theorem finite_patch_area_advance
    {X : Type*} [MeasurableSpace X] {ι : Type*} [DecidableEq ι]
    (μ ν : Measure X) (I : Finset ι) (A : ι → Set X)
    {f : X → X} {W : Set X} (C : ι → ℝ≥0∞)
    (hA : ∀ i ∈ I, MeasurableSet (A i))
    (hfiA : ∀ i ∈ I, MeasurableSet (f '' A i))
    (hsub : ∀ i ∈ I, A i ⊆ W)
    (hdis : Set.PairwiseDisjoint (I : Set ι) A)
    (hcover : (⋃ i ∈ I, A i) = W) (hinj : InjOn f W)
    (hlocal : ∀ i ∈ I, μ (A i) ≤ ν (f '' A i) + C i) :
    μ W ≤ ν (f '' W) + ∑ i ∈ I, C i := by
  have hdisImage : Set.PairwiseDisjoint (I : Set ι) (fun i => f '' A i) := by
    intro i hi j hj hij
    apply Set.disjoint_left.2
    rintro y ⟨x, hxi, rfl⟩ ⟨x', hxj, heq⟩
    have hxx : x = x' := hinj (hsub i hi hxi) (hsub j hj hxj) heq.symm
    subst x'
    exact Set.disjoint_left.mp (hdis hi hj hij) hxi hxj
  have hcoverImage : (⋃ i ∈ I, f '' A i) = f '' W := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      obtain ⟨hiI, hiA⟩ := mem_iUnion.mp hi
      obtain ⟨x, hx, rfl⟩ := hiA
      exact ⟨x, hcover ▸ mem_iUnion.mpr ⟨i,
        mem_iUnion.mpr ⟨hiI, hx⟩⟩, rfl⟩
    · rintro ⟨x, hxW, rfl⟩
      have hxU : x ∈ ⋃ i ∈ I, A i := hcover.symm ▸ hxW
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      obtain ⟨hiI, hiA⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiI, ⟨x, hiA, rfl⟩⟩⟩
  calc
    μ W = ∑ i ∈ I, μ (A i) := by
      rw [← measure_biUnion_finset hdis hA, hcover]
    _ ≤ ∑ i ∈ I, (ν (f '' A i) + C i) := by
      exact Finset.sum_le_sum fun i hi => hlocal i hi
    _ = (∑ i ∈ I, ν (f '' A i)) + ∑ i ∈ I, C i := by
      rw [Finset.sum_add_distrib]
    _ = ν (f '' W) + ∑ i ∈ I, C i := by
      rw [← measure_biUnion_finset hdisImage hfiA, hcoverImage]

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.finite_patch_area_advance
