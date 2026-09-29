module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.ChartCriticalValues

@[expose] public section

/-! # Finite branch-value sets from finitely many compact chart patches -/

open Set Function
open scoped Manifold

namespace SurfaceDynamics

variable {M N ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [DecidableEq N]

/-- Finitely many compact chart pairs produce one finite set containing all
branch values on the covered compact set. Outside it, a covering patch can
always be chosen with nonvanishing coordinate derivative. -/
theorem exists_finite_chart_branch_values
    (I : Finset ι) (K : ι → Set M)
    (c : ι → OpenPartialHomeomorph M ℂ)
    (d : ι → OpenPartialHomeomorph N ℂ)
    (hc : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c i) (c i).source)
    (hd : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (d i) (d i).source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {L : Set M}
    (hKcompact : ∀ i, IsCompact (K i))
    (hKc : ∀ i, K i ⊆ (c i).source)
    (hfKd : ∀ i, f '' K i ⊆ (d i).source)
    (hcover : L ⊆ ⋃ i ∈ I, K i) :
    ∃ E : Finset N, ∀ x ∈ L, f x ∉ E →
      ∃ i ∈ I, x ∈ K i ∧
        deriv (d i ∘ f ∘ (c i).symm) (c i x) ≠ 0 := by
  let S : ι → Set N := fun i =>
    f '' (K i ∩ {x | deriv (d i ∘ f ∘ (c i).symm) (c i x) = 0})
  have hS : ∀ i, (S i).Finite := fun i =>
    finite_chart_critical_values (hc i) (hd i) hf hopen
      (hKcompact i) (hKc i) (hfKd i)
  let F : ι → Finset N := fun i => (hS i).toFinset
  refine ⟨I.biUnion F, ?_⟩
  intro x hxL hxE
  obtain ⟨i, hiI, hxi⟩ := Set.mem_iUnion₂.mp (hcover hxL)
  refine ⟨i, hiI, hxi, ?_⟩
  intro hzero
  apply hxE
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hiI, ?_⟩
  change f x ∈ (hS i).toFinset
  rw [Set.Finite.mem_toFinset]
  exact ⟨x, ⟨hxi, hzero⟩, rfl⟩

end SurfaceDynamics
