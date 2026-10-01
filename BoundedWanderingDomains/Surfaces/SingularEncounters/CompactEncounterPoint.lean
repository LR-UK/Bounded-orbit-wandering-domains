module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.OrbitComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompactFiniteControl
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FiniteComponentContradiction

@[expose] public section

/-! # A compact wandering orbit has a point of infinitely many component obstructions -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [NoncompactComponents X]

theorem exists_not_locally_finite_encounters_of_compact_wandering_orbit
    (p : ComponentwiseDiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hU : ∀ n, f.IsComponent (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (z : f.trapped) (hq0 : ∀ n, ((q n).projection discZero : X) = f.orbit n z)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K) :
    ∃ x ∈ K, ¬ f.LocallyFiniteComponentEncounters hf.2.continuous
      (fun n => ⟨f.orbit n z, f.orbit_mem_source n z⟩) x := by
  classical
  by_contra hn
  have hfinite : ∀ x ∈ K, f.LocallyFiniteComponentEncounters hf.2.continuous
      (fun n => ⟨f.orbit n z, f.orbit_mem_source n z⟩) x := by
    intro x hx
    by_contra hxnot
    exact hn ⟨x, hx, hxnot⟩
  have hzU : ∀ n, f.orbit n z ∈ (U n : Set X) := fun n =>
    hq0 n ▸ ((q n).projection discZero).property
  obtain ⟨hUs, hfU⟩ := f.component_orbit_forward hf (fun n => (U n : Set X)) hU z hzU
  let F : ℕ → unitDisc → X := fun n w => (q n).projection w
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := fun n =>
    (mdifferentiable_subtype_val (U n)).comp (q n).holomorphic
  have hFs : ∀ n, range (F n) ⊆ f.source := by
    intro n x hx
    obtain ⟨w, rfl⟩ := hx
    exact hUs n ((q n).projection w).property
  have hdisF : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))) := by
    intro n m hnm
    exact (hdis hnm).mono
      (by rintro x ⟨w, rfl⟩; exact ((q n).projection w).property)
      (by rintro x ⟨w, rfl⟩; exact ((q m).projection w).property)
  have hnext : ∀ n, f.totalize (f.orbit n z) = f.orbit (n + 1) z := by
    intro n
    rw [f.totalize_eq (f.orbit_mem_source n z), f.orbit_succ]
  have hforward : ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ n,
      MapsTo f.totalize (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R})
        (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}) := by
    intro R _ _ n
    exact f.mapsTo_covering_closed_radius hf.2 (U n) (U (n + 1)) (hUs n)
      (q n) (q (n + 1)) (hfU n) (by rw [hq0, hq0, hnext]) R
  obtain ⟨I, target, E, inner, hinner, hinnerTarget, hcontrol⟩ :=
    f.exists_finite_disc_control_of_locally_finite_encounters p hf
      (fun n => ⟨f.orbit n z, f.orbit_mem_source n z⟩) F hF hFs hq0
      (by intro n; change f.map ⟨f.orbit n z, _⟩ = ((q (n + 1)).projection discZero : X)
          rw [hq0, f.orbit_succ]) hdisF hforward hK hzK hfinite
  apply false_of_compact_wandering_finite_component_control p f hf U q hU hdis z hq0
    hK hzK target E inner hinner hinnerTarget
  · intro R hR hR1
    filter_upwards [hcontrol R hR hR1] with n hn
    obtain ⟨i, V, hV, hbkl, _⟩ := hn
    exact hbkl
  · intro r hr hr1
    filter_upwards [hcontrol r hr.le hr1] with n hn
    obtain ⟨i, V, hV, _, hreg, hAV, hnextInner⟩ := hn
    have hclosed : {w : unitDisc | ‖(w : ℂ)‖ < r} ⊆ {w : unitDisc | ‖(w : ℂ)‖ ≤ r} := by
      intro w hw
      change ‖(w : ℂ)‖ < r at hw
      change ‖(w : ℂ)‖ ≤ r
      exact hw.le
    refine ⟨i, V, hV, hreg, ?_, ?_⟩
    · exact (image_mono hclosed).trans hAV
    · exact (image_mono hclosed).trans hnextInner

end SurfaceDynamics.BKL
