module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterData

@[expose] public section

/-! # Orbit accumulation follows from a singular-encounter sequence -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem base_map_mem_of_component_singular_value
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X)
    (a : f.source) {s : X} (hs : s ∈ f.componentSingularValues hf D a) :
    f.map a ∈ D := by
  have hne : (range (f.inverseComponentMap hf D a).map).Nonempty :=
    closure_nonempty_iff.mp ⟨s, hs.1.2⟩
  obtain ⟨_, u, _⟩ := hne
  obtain ⟨v, hv, _⟩ := u.2
  change a ∈ f.map ⁻¹' (D : Set X)
  exact connectedComponentIn_nonempty_iff.mp ⟨v, hv⟩

theorem map_mem_of_mem_inverseComponentSource
    (f : LocalMap X) (hf : Continuous f.map) (D : TopologicalSpace.Opens X)
    (a b : f.source) (hb : (b : X) ∈ f.inverseComponentSource hf D a) :
    f.map b ∈ D := by
  obtain ⟨u, hu, hub⟩ := hb
  have he : u = b := Subtype.ext hub
  have huD : f.map u ∈ D := connectedComponentIn_subset (f.map ⁻¹' (D : Set X)) a hu
  simpa only [he] using huD

theorem HasSingularEncounterSequenceAt.successor_orbit_limit
    (f : LocalMap X) (hf : Continuous f.map) {W : Set X} {z : f.trapped} {x : X}
    (h : f.HasSingularEncounterSequenceAt hf W z x) (hzW : (z : X) ∈ W) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => f.orbit (φ n + 1) z) atTop (𝓝 x) := by
  obtain ⟨Q, φ, _, hφ, _, _, hshrink, _, hcapture⟩ := h
  have hvisit := hcapture {(z : X)} isCompact_singleton (singleton_subset_iff.mpr hzW)
  refine ⟨φ, hφ, tendsto_def.mpr ?_⟩
  intro O hO
  filter_upwards [hvisit, hshrink O hO] with n hn hnO
  apply hnO
  change f.orbit (φ n + 1) z ∈ (Q n).carrier
  rw [f.orbit_succ]
  apply f.map_mem_of_mem_inverseComponentSource hf (Q n).carrier
    ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩
    ⟨f.orbit (φ n) z, f.orbit_mem_source (φ n) z⟩
  have hh := hn (mem_singleton (z : X))
  rwa [f.totalize_iterate_orbit] at hh

end SurfaceDynamics.LocalMap
