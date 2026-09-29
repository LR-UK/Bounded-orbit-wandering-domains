module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableDiscBasis
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterConsequences
public import BoundedWanderingDomains.Surfaces.SingularEncounters.DistinctSelection

@[expose] public section

/-! # Selecting singular encounters from a fixed analytic-disc basis -/

open Set Function Filter Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def LocallyFiniteBasisEncounters (f : LocalMap X) (hf : Continuous f.map)
    (B : Set (EmbeddedDisc X)) (c : ℕ → f.source) (x : X) : Prop :=
  ∃ Q ∈ B, x ∈ Q.carrier ∧ ∃ (E : Finset X) (N : ℕ), ∀ n, N ≤ n →
    f.map (c n) ∈ Q.carrier → f.componentSingularValues hf Q.carrier (c n) ⊆ E

theorem encounters_of_not_locally_finite_basis
    [FirstCountableTopology X]
    (f : LocalMap X) (hf : Continuous f.map) (B : Set (EmbeddedDisc X))
    (hB : TopologicalSpace.IsTopologicalBasis
      ((fun Q : EmbeddedDisc X => (Q.carrier : Set X)) '' B))
    (z : f.trapped) {x : X}
    (hnot : ¬ f.LocallyFiniteBasisEncounters hf B
      (fun n => ⟨f.orbit n z, f.orbit_mem_source n z⟩) x) :
    f.HasSingularEncounterSequenceAt hf {(z : X)} z x := by
  classical
  obtain ⟨V, hV, hb⟩ := (nhds_basis_opens x).exists_antitone_subbasis
  have hchoose : ∀ n, ∃ Q ∈ B, x ∈ Q.carrier ∧ (Q.carrier : Set X) ⊆ V n := by
    intro n
    obtain ⟨A, ⟨Q, hQB, rfl⟩, hxQ, hQV⟩ :=
      hB.exists_subset_of_mem_open (hV n).1 (hV n).2
    exact ⟨Q, hQB, hxQ, hQV⟩
  choose Q hQB hxQ hQV using hchoose
  let c : ℕ → f.source := fun n => ⟨f.orbit n z, f.orbit_mem_source n z⟩
  have hnew : ∀ m N : ℕ, ∀ E : Finset X, ∃ n, N ≤ n ∧ ∃ s,
      s ∉ E ∧ s ∈ f.componentSingularValues hf (Q m).carrier (c n) := by
    intro m N E
    by_contra hno
    apply hnot
    refine ⟨Q m, hQB m, hxQ m, E, N, ?_⟩
    intro n hn _ s hs
    by_contra hse
    exact hno ⟨n, hn, s, hse, hs⟩
  obtain ⟨μ, φ, s, hμ, hφ, hs, hsing⟩ :=
    exists_increasing_distinct_selection
      (fun m n s => s ∈ f.componentSingularValues hf (Q m).carrier (c n)) hnew
  refine ⟨Q ∘ μ, φ, s, hφ, hs, fun n => hxQ (μ n), ?_, hsing, ?_⟩
  · intro O hO
    obtain ⟨m, _, hm⟩ := hb.toHasBasis.mem_iff.mp hO
    filter_upwards [hμ.tendsto_atTop.eventually (eventually_ge_atTop m)] with n hn
    exact (hQV (μ n)).trans ((hb.antitone hn).trans hm)
  · intro L _ hL
    apply Eventually.of_forall
    intro n y hy
    have hyz : y = (z : X) := mem_singleton_iff.mp (hL hy)
    subst y
    rw [f.totalize_iterate_orbit]
    exact ⟨c (φ n), mem_connectedComponentIn
      (f.base_map_mem_of_component_singular_value hf _ _ (hsing n)), rfl⟩

end SurfaceDynamics.LocalMap
