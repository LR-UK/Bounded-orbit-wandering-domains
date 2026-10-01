module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.BarrierCompactOrbit
public import BoundedWanderingDomains.Surfaces.ForwardSourceBarrier
public import BoundedWanderingDomains.Surfaces.OmegaDynamics

@[expose] public section

/-! # Exact finite-puncture models for a compact marked normal orbit -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

theorem exists_finite_models_of_compact_normal_orbit
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : ComponentwiseDiscCover X)
    (z : f.trapped) (hz : (z : X) ∈ f.omega)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K) :
    ∃ P : ℕ → Finset X, Monotone P ∧
      (∀ j (x : f.source), (x : X) ∈ P j → f.map x ∈ P j) ∧
      (∀ n, connectedComponentIn (closure (⋃ j, (P j : Set X)))ᶜ (f.orbit n z) =
        connectedComponentIn f.omega (f.orbit n z)) := by
  classical
  obtain ⟨P, hPm, hfront, hforward, hback, hdis⟩ :=
    f.exists_forward_source_finitePuncture_barrier hf f.isOpen_omega f.omega_subset_source
      (fun x hx => by
        have hh := f.totalize_mapsTo_omega hf hx
        rwa [f.totalize_eq (f.omega_subset_source hx)] at hh)
  refine ⟨P, hPm, hforward, ?_⟩
  intro n
  let a : f.trapped := (f.trappedMap^[n]) z
  have haomega : (a : X) ∈ f.omega := by
    have hh := (f.totalize_mapsTo_omega hf).iterate n hz
    rwa [f.totalize_iterate_orbit n z] at hh
  have haA : (a : X) ∉ closure (⋃ j, (P j : Set X)) :=
    fun h => disjoint_left.mp hdis h haomega
  have haK : ∀ k, f.orbit k a ∈ K := by
    intro k
    have hh := hzK (k + n)
    simpa only [orbit, iterate_add_apply] using hh
  have hcompOmega := f.barrier_component_subset_omega_of_compact_orbit hf p
    isClosed_closure hfront hback a.property haA hK haK
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn haA) hcompOmega
  · apply connectedComponentIn_mono
    exact fun x hx hxA => disjoint_left.mp hdis hxA hx

end SurfaceDynamics.LocalMap
