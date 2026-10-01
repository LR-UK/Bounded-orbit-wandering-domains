module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalMapSubsurface
public import BoundedWanderingDomains.Surfaces.BarrierCompactOrbit

@[expose] public section

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
theorem restrictAmbient_orbit_val (f : LocalMap X)
    (O : TopologicalSpace.Opens X) (hs : (f.source : Set X) ⊆ O)
    (hm : ∀ x : f.source, f.map x ∈ O)
    (z : (f.restrictAmbient O hs hm).trapped) (n : ℕ) :
    ((f.restrictAmbient O hs hm).orbit n z : X) =
      f.orbit n ⟨(z : O), (f.mem_restrictAmbient_trapped_iff O hs hm (z : O)).mp z.property⟩ := by
  have hh := f.restrictAmbient_iterate_val O hs hm n (z : O)
  rw [(f.restrictAmbient O hs hm).iterate_eq_some_orbit n z,
    f.iterate_eq_some_orbit n ⟨(z : O),
      (f.mem_restrictAmbient_trapped_iff O hs hm (z : O)).mp z.property⟩] at hh
  exact Option.some.inj hh

/-- Compact marked dynamics in a covered subsurface makes the connected
trapped neighbourhood normal also in the ambient surface. -/
theorem image_connected_trapped_open_subset_omega_of_compact_orbit
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O : TopologicalSpace.Opens X) [LocallyCompactSpace O] (p : ComponentwiseDiscCover O)
    (hs : (f.source : Set X) ⊆ O) (hm : ∀ x : f.source, f.map x ∈ O)
    (W : TopologicalSpace.Opens O) [ConnectedSpace W]
    (hW : (W : Set O) ⊆ (f.restrictAmbient O hs hm).trapped) (x : W)
    {K : Set O} (hK : IsCompact K)
    (hxK : ∀ n, (f.restrictAmbient O hs hm).orbit n ⟨x, hW x.property⟩ ∈ K) :
    Subtype.val '' (W : Set O) ⊆ f.omega := by
  classical
  let g := f.restrictAmbient O hs hm
  have hg := f.isOpenHolomorphic_restrictAmbient hf O hs hm
  let V : TopologicalSpace.Opens X :=
    ⟨Subtype.val '' (W : Set O), O.isOpen.isOpenMap_subtype_val _ W.isOpen⟩
  have hV : (V : Set X) ⊆ f.trapped := by
    rintro y ⟨yo, hy, rfl⟩
    exact (f.mem_restrictAmbient_trapped_iff O hs hm yo).mp (hW hy)
  have hVO : ∀ n y, f.orbitOn V hV n y ∈ O :=
    fun n y => hs (f.orbit_mem_source n ⟨y, hV y.property⟩)
  rintro y ⟨yo, hyo, rfl⟩
  obtain ⟨L, hL, hyL⟩ := g.compact_orbits_on_connected_trapped_open hg p W hW x hK hxK ⟨yo, hyo⟩
  apply f.mem_omega_of_compact_orbit_in_subsurface hf O p V hV hVO
    ⟨yo, ⟨yo, hyo, rfl⟩⟩ hL
  intro n
  have he : (⟨f.orbitOn V hV n ⟨yo, ⟨yo, hyo, rfl⟩⟩,
      hVO n ⟨yo, ⟨yo, hyo, rfl⟩⟩⟩ : O) = g.orbit n ⟨yo, hW hyo⟩ := by
    apply Subtype.ext
    exact (f.restrictAmbient_orbit_val O hs hm ⟨yo, hW hyo⟩ n).symm
  rw [he]
  exact hyL n

end SurfaceDynamics.LocalMap
