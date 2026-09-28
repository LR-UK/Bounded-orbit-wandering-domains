/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AlmostEverywhere.DerivedSingular
import BoundedWanderingDomains.Surfaces.SurfaceDerivedLimits

/-! # Public compact-orbit and almost-everywhere results -/

open Set Function Filter MeasureTheory OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X]

/-- A wandering orbit contained in an ambient compact set has a subsequence
converging to a derived singular value in that compact set. -/
theorem compact_wandering_orbit_accumulates_on_derived_singular_values
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {U : Set X} (hU : f.IsWanderingComponent U) {z : X} (hz : z ∈ U)
    {K : Set X} (hK : IsCompact K)
    (horbit : ∀ n, f.compactifiedIterate n z ∈ ((↑) : X → OnePoint X) '' K) :
    ∃ a ∈ K ∩ derivedSet f.singularValues, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => f.compactifiedIterate (φ n) z) atTop (𝓝 (a : OnePoint X)) := by
  have hztr := hU.subset_trapped f hz
  obtain ⟨φ, hφ, hescape | ⟨a, ha, hlim⟩⟩ := wanderingDerivedSingularLimitClaim f hf U hU z hz
  · apply False.elim
    apply not_tendsto_infty_of_range_subset_compact (fun n => f.orbit (φ n) ⟨z, hztr⟩) hK ?_ ?_
    · intro n
      obtain ⟨x, hx, he⟩ := horbit (φ n)
      rw [f.compactifiedIterate_eq_orbit _ ⟨z, hztr⟩] at he
      exact OnePoint.coe_injective he ▸ hx
    · simpa only [f.compactifiedIterate_eq_orbit _ ⟨z, hztr⟩] using hescape
  · have haK : (a : OnePoint X) ∈ ((↑) : X → OnePoint X) '' K :=
      (hK.image OnePoint.continuous_coe).isClosed.mem_of_tendsto hlim
        (Eventually.of_forall (fun n => horbit (φ n)))
    obtain ⟨x, hx, he⟩ := haK
    exact ⟨a, ⟨OnePoint.coe_injective he ▸ hx, ha⟩, φ, hφ, hlim⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- Almost every point of a measurable wandering set outside normality has
a subsequence escaping every compact subset of the source. -/
theorem almost_every_wandering_point_has_source_escaping_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) :
    ChartAlmostEverywhere A f.HasSourceEscapingSubsequence :=
  f.ae_has_source_escaping_subsequence hf hA hAbad hdis
    (f.injectiveOnSaturation_of_iterates_injective (fun _ hx => (hAbad hx).1) hdis hinj)

/-- A positive-area wandering set with injective iterates cannot have its
whole saturation in an ambient compact set avoiding derived singular values. -/
theorem positive_area_wandering_saturation_not_compactly_contained_away_from_derived
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) (hpos : HasPositiveChartArea A) :
    ¬ ∃ K : Set X, IsCompact K ∧ Disjoint K (derivedSet f.singularValues) ∧ f.saturation A ⊆ K := by
  rintro ⟨K, hK, havoid, hsat⟩
  exact no_compact_positive_area_saturation_away_from_derived f hf hA hAbad hdis
    (f.injectiveOnSaturation_of_iterates_injective (fun _ hx => (hAbad hx).1) hdis hinj)
    hpos hK havoid hsat

/-- Almost every point of a measurable wandering set with injective iterates,
outside normality, has an escaping or derived-singular subsequence. -/
theorem almost_every_wandering_point_has_escaping_or_derived_singular_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : ∀ n, InjOn (f.compactifiedIterate n) A) :
    ChartAlmostEverywhere A f.HasEscapingOrDerivedSingularSubsequence :=
  f.ae_has_escaping_or_derived_singular_subsequence hf hA hAbad hdis
    (f.injectiveOnSaturation_of_iterates_injective (fun _ hx => (hAbad hx).1) hdis hinj)

end SurfaceDynamics
