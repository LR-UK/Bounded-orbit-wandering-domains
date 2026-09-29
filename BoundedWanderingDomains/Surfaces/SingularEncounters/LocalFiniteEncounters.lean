module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FiniteObstructions

@[expose] public section

/-! # Local finite control and the selection of new singular encounters -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Near a target point, sufficiently late visits meet only a fixed finite
set of genuine singular obstructions in their full inverse components. -/
def LocallyFiniteComponentEncounters (f : LocalMap X) (hf : Continuous f.map)
    (c : ℕ → f.source) (x : X) : Prop :=
  ∃ D B : TopologicalSpace.Opens X, IsConnected (D : Set X) ∧ x ∈ B ∧ B ≤ D ∧
    ∃ (E : Finset X) (N : ℕ), ∀ n, N ≤ n → f.map (c n) ∈ B →
      f.componentSingularValues hf D (c n) ⊆ (E : Set X)

theorem exists_new_singular_encounter_of_not_locally_finite
    (f : LocalMap X) (hf : Continuous f.map) (c : ℕ → f.source) {x : X}
    (hnot : ¬ f.LocallyFiniteComponentEncounters hf c x)
    (D B : TopologicalSpace.Opens X) (hD : IsConnected (D : Set X))
    (hxB : x ∈ B) (hBD : B ≤ D) (E : Finset X) (N : ℕ) :
    ∃ n, N ≤ n ∧ f.map (c n) ∈ B ∧
      ∃ s, s ∈ f.componentSingularValues hf D (c n) ∧ s ∉ E := by
  by_contra hn
  apply hnot
  refine ⟨D, B, hD, hxB, hBD, E, N, ?_⟩
  intro n hnN hnb s hs
  by_contra hsE
  exact hn ⟨n, hnN, hnb, s, hs, hsE⟩

end SurfaceDynamics.LocalMap
