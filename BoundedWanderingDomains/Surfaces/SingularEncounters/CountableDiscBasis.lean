module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EmbeddedDisc
public import Mathlib.Topology.Bases

@[expose] public section

/-! # Countable analytic-disc bases -/

open Set Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [SecondCountableTopology X] [T2Space X]

omit [T2Space X] in
theorem exists_countable_embeddedDisc_basis :
    ∃ B : Set (EmbeddedDisc X), B.Countable ∧
      TopologicalSpace.IsTopologicalBasis ((fun Q : EmbeddedDisc X =>
        (Q.carrier : Set X)) '' B) := by
  classical
  let carriers : Set (Set X) := range (fun Q : EmbeddedDisc X => (Q.carrier : Set X))
  have hb : TopologicalSpace.IsTopologicalBasis carriers := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro A ⟨Q, rfl⟩
      exact Q.carrier.isOpen
    · intro x O hx hO
      obtain ⟨Q, hQ, hsub⟩ := exists_coordDisk_center_closedCarrier_subset hO hx
      let D := EmbeddedDisc.ofCoordDisk Q
      refine ⟨D.carrier, ⟨D, rfl⟩, ?_, ?_⟩
      · exact ⟨discZero, Q.param_zero.trans hQ⟩
      · rintro y ⟨w, rfl⟩
        exact hsub (Q.param_mem_closedCarrier w)
  obtain ⟨S, hS, hSc, hSb⟩ := hb.exists_countable
  have hchoice : ∀ A : S, ∃ Q : EmbeddedDisc X, (Q.carrier : Set X) = (A : Set X) :=
    fun A => hS A.2
  choose Q hQ using hchoice
  let countableSets : Countable S := hSc.to_subtype
  refine ⟨range Q, countable_range Q, ?_⟩
  convert hSb using 1
  ext A
  constructor
  · rintro ⟨D, ⟨B, rfl⟩, rfl⟩
    change ((Q B).carrier : Set X) ∈ S
    rw [hQ B]
    exact B.2
  · intro hA
    exact ⟨Q ⟨A, hA⟩, mem_range_self _, hQ ⟨A, hA⟩⟩

end SurfaceDynamics
