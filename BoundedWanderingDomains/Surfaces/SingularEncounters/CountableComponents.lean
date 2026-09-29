module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.InverseComponents
public import Mathlib.Topology.Bases

@[expose] public section

/-! # Countably many full inverse components over an open target -/

open Set Function Topology

namespace SurfaceDynamics

theorem countable_range_connectedComponentIn_open
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [SecondCountableTopology X]
    {D : Set X} (hD : IsOpen D) : (range (connectedComponentIn D)).Countable := by
  let S : Set (Set X) := {C ∈ range (connectedComponentIn D) | C.Nonempty}
  have hdis : S.PairwiseDisjoint id := by
    intro C hC B hB hne
    obtain ⟨⟨a, rfl⟩, _⟩ := hC
    obtain ⟨⟨b, rfl⟩, _⟩ := hB
    apply disjoint_left.mpr
    intro x hxa hxb
    exact hne ((connectedComponentIn_eq hxa).trans (connectedComponentIn_eq hxb).symm)
  have hSc : S.Countable := hdis.countable_of_isOpen
    (by rintro C ⟨⟨a, rfl⟩, _⟩; exact hD.connectedComponentIn)
    (fun _ hC => hC.2)
  apply (hSc.insert ∅).mono
  intro C hC
  by_cases hne : C.Nonempty
  · exact mem_insert_of_mem _ ⟨hC, hne⟩
  · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

namespace LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [SecondCountableTopology X]

theorem countable_inverseComponentSources
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X) :
    (range (fun a : f.source => (f.inverseComponentSource hf D a : Set X))).Countable := by
  let sourceLocallyConnected : LocallyConnectedSpace f.source :=
    ChartedSpace.locallyConnectedSpace ℂ f.source
  have hc := countable_range_connectedComponentIn_open (D.isOpen.preimage hf)
  convert hc.image (fun C : Set f.source => (Subtype.val : f.source → X) '' C) using 1
  rw [← range_comp]
  rfl

end LocalMap
end SurfaceDynamics
