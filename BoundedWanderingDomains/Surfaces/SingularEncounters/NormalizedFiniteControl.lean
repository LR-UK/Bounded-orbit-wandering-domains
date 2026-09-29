module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.BasisEncounterSelection
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableObstructions

@[expose] public section

/-! # Choosing exceptional sets from a fixed countable pool -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem LocallyFiniteBasisEncounters.from_pool
    (f : LocalMap X) (hf : Continuous f.map) (B : Set (EmbeddedDisc X))
    (T : Set X)
    (hT : ∀ Q ∈ B, ∀ a : f.source, (f.componentSingularValues hf Q.carrier a).Finite →
      f.componentSingularValues hf Q.carrier a ⊆ T)
    (c : ℕ → f.source) {x : X} (h : f.LocallyFiniteBasisEncounters hf B c x) :
    ∃ Q ∈ B, x ∈ Q.carrier ∧ ∃ (E : Finset T) (N : ℕ), ∀ n, N ≤ n →
      f.map (c n) ∈ Q.carrier →
        f.componentSingularValues hf Q.carrier (c n) ⊆ Subtype.val '' (E : Set T) := by
  classical
  obtain ⟨Q, hQB, hxQ, E, N, hcontrol⟩ := h
  have hfin : ((Subtype.val : T → X) ⁻¹' (E : Set X)).Finite :=
    E.finite_toSet.preimage Subtype.val_injective.injOn
  refine ⟨Q, hQB, hxQ, hfin.toFinset, N, ?_⟩
  intro n hn hnQ y hy
  have hyT := hT Q hQB (c n) (E.finite_toSet.subset (hcontrol n hn hnQ)) hy
  exact ⟨⟨y, hyT⟩, hfin.mem_toFinset.mpr (hcontrol n hn hnQ hy), rfl⟩

end SurfaceDynamics.LocalMap
