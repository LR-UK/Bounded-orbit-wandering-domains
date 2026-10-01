module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompactEncounterPoint
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ShrinkingEncounterSelection
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompactOrbitCapture
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterData

@[expose] public section

/-! # The combined theorem for compact wandering orbits on a hyperbolic surface -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [NoncompactComponents X]

theorem compact_wandering_singular_encounters
    (p : ComponentwiseDiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hU : ∀ n, f.IsComponent (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (z : f.trapped) (hq0 : ∀ n, ((q n).projection discZero : X) = f.orbit n z)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K) :
    ∃ x ∈ K ∩ derivedSet f.singularValues,
      f.HasSingularEncounterSequenceAt hf.2.continuous (U 0) z x := by
  obtain ⟨x, hxK, hx⟩ :=
    exists_not_locally_finite_encounters_of_compact_wandering_orbit p f hf U q hU hdis
      z hq0 hK hzK
  let F : ℕ → unitDisc → X := fun n w => (q n).projection w
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := fun n =>
    (mdifferentiable_subtype_val (U n)).comp (q n).holomorphic
  have hzU : ∀ n, f.orbit n z ∈ (U n : Set X) := fun n =>
    hq0 n ▸ ((q n).projection discZero).property
  obtain ⟨hUs, hfU⟩ := f.component_orbit_forward hf (fun n => (U n : Set X)) hU z hzU
  have hFs : ∀ n, range (F n) ⊆ f.source := by
    intro n y hy
    obtain ⟨w, rfl⟩ := hy
    exact hUs n ((q n).projection w).property
  have hdisF : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))) := by
    intro n m hnm
    exact (hdis hnm).mono
      (by rintro y ⟨w, rfl⟩; exact ((q n).projection w).property)
      (by rintro y ⟨w, rfl⟩; exact ((q m).projection w).property)
  have hnext : ∀ n, f.totalize (f.orbit n z) = f.orbit (n + 1) z := by
    intro n
    rw [f.totalize_eq (f.orbit_mem_source n z), f.orbit_succ]
  have hforward : ∀ R : ℝ, ∀ n,
      MapsTo f.totalize (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R})
        (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}) := by
    intro R n
    exact f.mapsTo_covering_closed_radius hf.2 (U n) (U (n + 1)) (hUs n)
      (q n) (q (n + 1)) (hfU n) (by rw [hq0, hq0, hnext]) R
  obtain ⟨Q, φ, s, hφ, hs, hQ, hshrink, hsingular, hcapture⟩ :=
    f.exists_shrinking_encounters_of_not_locally_finite p hf.2.continuous
      (fun n => ⟨f.orbit n z, f.orbit_mem_source n z⟩) F hF hFs hq0
      (by intro n; change f.map ⟨f.orbit n z, _⟩ = ((q (n + 1)).projection discZero : X)
          rw [hq0, f.orbit_succ]) hdisF
      (fun R _ _ => hforward R) hK hzK hx
  have hderived := (f.derived_mem_of_shrinking_component_singular_values hf.2.continuous
    (fun n => ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩) Q s hs hshrink hsingular).2
  refine ⟨x, ⟨hxK, hderived⟩, fun n => EmbeddedDisc.ofCoordDisk (Q n), φ, s,
    hφ, hs, ?_, ?_, hsingular, ?_⟩
  · intro n
    exact ⟨discZero, (Q n).param_zero.trans (hQ n)⟩
  · intro O hO
    filter_upwards [hshrink O hO] with n hn
    rintro y ⟨w, rfl⟩
    exact hn ((Q n).param_mem_closedCarrier w)
  · exact f.eventually_capture_compact_of_covering_radii (U 0) (q 0) F rfl
      (fun R _ => hforward R) φ _ hcapture

end SurfaceDynamics.BKL
