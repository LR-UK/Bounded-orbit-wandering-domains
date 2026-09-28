/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.LocalPunctures
import BoundedWanderingDomains.Surfaces.FiniteFibers

/-! # Finite local backward puncture trees on analytic surfaces -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

omit [T2Space X] in
/-- The inverse image of a finite set, restricted to a compact set, is finite
for an open holomorphic surface map. -/
theorem finite_compact_inter_preimage_of_finite {f : X → Y}
    (hopen : IsOpenMap f) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {K : Set X} {S : Set Y} (hK : IsCompact K) (hS : S.Finite) :
    (K ∩ f ⁻¹' S).Finite := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert y S hyS hS ih =>
      have hy := finite_compact_inter_fiber_of_isOpenMap_of_mdifferentiable
        hopen hf hK y
      apply (hy.union ih).subset
      rintro x ⟨hxK, hx⟩
      rw [mem_preimage, mem_insert_iff] at hx
      rcases hx with hxy | hxS
      · exact Or.inl ⟨hxK, hxy⟩
      · exact Or.inr ⟨hxK, hxS⟩

section SelfMap

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Every stage of the local backward tree is finite on a compact working
set. -/
theorem localPunctures_finite {f : X → X} {V K : Set X}
    {Q : ℕ → Set X} (hVK : V ⊆ K) (hK : IsCompact K)
    (hopen : IsOpenMap f) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hQ : ∀ n, (Q n).Finite) (n : ℕ) :
    (AreaDeficit.localPunctures f V Q n).Finite := by
  apply AreaDeficit.backwardTree_finite (hQ n)
  intro S hS
  exact (finite_compact_inter_preimage_of_finite hopen hf hK hS).subset
    (inter_subset_inter_left _ hVK)

/-- The union of the finite local puncture stages is countable. -/
theorem localPunctures_countable {f : X → X} {V K : Set X}
    {Q : ℕ → Set X} (hVK : V ⊆ K) (hK : IsCompact K)
    (hopen : IsOpenMap f) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hQ : ∀ n, (Q n).Finite) :
    (⋃ n : ℕ, AreaDeficit.localPunctures f V Q n).Countable :=
  countable_iUnion (fun n =>
    (localPunctures_finite hVK hK hopen hf hQ n).countable)

end SelfMap

end SurfaceDynamics
