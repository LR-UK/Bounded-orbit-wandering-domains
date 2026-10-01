module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.Statements
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SurfaceWanderingEncounters
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SurfaceAlmostEverywhere
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.OrbitShift

@[expose] public section

/-! # Public combined wandering-domain and wandering-set theorems -/

open Set Function Filter MeasureTheory Topology OnePoint
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [IsManifold 𝓘(ℂ) 1 X]

theorem LocalMap.HasSingularEncounterSequenceAt.to_sequence
    (f : LocalMap X) (hf : Continuous f.map) {W : Set X} {z : f.trapped} {x : X}
    (h : f.HasSingularEncounterSequenceAt hf W z x) :
    f.HasSingularEncounterSequence hf W x := by
  obtain ⟨Q, φ, s, hφ, hs, hx, hshrink, hsing, hcapture⟩ := h
  let c : ℕ → f.source := fun n => ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩
  let U : ∀ n, f.PreimageComponent hf (Q n).carrier := fun n =>
    f.preimageComponentAt hf (Q n).carrier (c n)
      (f.base_map_mem_of_component_singular_value hf (Q n).carrier (c n) (hsing n))
  refine ⟨Q, U, φ, s, hφ, hs,
    (f.derived_mem_of_shrinking_component_obstructions hf c (fun n => (Q n).carrier)
      s hs hshrink hsing).1,
    fun n => f.componentSingularValues_subset hf _ _ (hsing n), hx, hshrink, ?_, hcapture⟩
  intro n
  rw [f.singularValues_preimageComponentAt]
  exact hsing n

variable [LocallyCompactSpace X] [SecondCountableTopology X]

/-- Unless there is ambient escape, all points of a wandering domain visit
full inverse components carrying distinct singular values in shrinking discs.
The visits are uniform on each compact subset of the initial domain. -/
theorem wandering_domain_has_escaping_or_singular_encounter_sequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {U : Set X} (hU : f.IsWanderingComponent U) {z : X} (hz : z ∈ U) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => f.compactifiedIterate (φ n) z) atTop (𝓝 (∞ : OnePoint X))) ∨
    ∃ a ∈ derivedSet f.singularValues, f.HasSingularEncounterSequence hf.2.continuous U a := by
  rcases wanderingSingularEncounterAlternative f hf U hU z hz with he | ⟨a, ha, henc⟩
  · exact Or.inl he
  · exact Or.inr ⟨a, ha, LocalMap.HasSingularEncounterSequenceAt.to_sequence f hf.2.continuous henc⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- The same componentwise alternative holds almost everywhere in any
measurable wandering set outside normality whose iterates are injective. -/
theorem almost_every_wandering_point_has_escaping_or_singular_encounter_sequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) :
    ChartAlmostEverywhere A (f.HasEscapingOrSingularEncounterSequence hf.2.continuous) := by
  apply (f.ae_has_escaping_or_singular_encounters hf hA hAbad hdis
    (f.injectiveOnSaturation_of_iterates_injective (fun _ hx => (hAbad hx).1) hdis hinj)).mono
  intro x _ hx
  rcases hx with ⟨_, he | ⟨a, henc⟩⟩
  · exact Or.inl he
  · exact Or.inr ⟨a, LocalMap.HasSingularEncounterSequenceAt.derived_mem f hf.2.continuous henc,
      LocalMap.HasSingularEncounterSequenceAt.to_sequence f hf.2.continuous henc⟩

end SurfaceDynamics
