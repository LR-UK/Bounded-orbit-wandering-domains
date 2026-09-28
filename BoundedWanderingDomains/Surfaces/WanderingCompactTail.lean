/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.BoundaryBarrierPackage
import BoundedWanderingDomains.Surfaces.WanderingAnchorDisk

/-! # A compact wandering tail in a fixed covered subsurface -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X]

/-- A compactly contained marked wandering orbit has, from time one onward,
a compact tail for the restriction to one fixed hyperbolic anchor complement. -/
theorem IsWanderingComponent.exists_compact_hyperbolic_restricted_tail
    (f : LocalMap X) {U : Set X} (hU : f.IsWanderingComponent U)
    {z : X} (hz : z ∈ U) {K : Set X} (hK : IsCompact K)
    (hKsource : K ⊆ f.source)
    (horbitK : ∀ n, f.orbit n
      ⟨z, LocalMap.IsWanderingComponent.subset_trapped f hU hz⟩ ∈ K) :
    ∃ (D : RiemannDynamics.CoordDisk X)
      (_p : DiscCover D.compl)
      (W : TopologicalSpace.Opens X) (hW : (W : Set X) ⊆ f.source)
      (z₁ : X) (hz₁ : z₁ ∈ (f.restrictSource W hW).trapped)
      (L : Set X),
      (W : Set X) ⊆ D.compl ∧ IsCompact L ∧ L ⊆ W ∧
      ∀ n, (f.restrictSource W hW).orbit n ⟨z₁, hz₁⟩ ∈ L := by
  let : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace ℂ X
  obtain ⟨V, hztrapped, D, p, hV0, hcomp, horbit, hdis, hD, htail,
      hz₁restricted, hiter⟩ := hU.exists_hyperbolic_restricted_tail f hz
  let W : TopologicalSpace.Opens X := f.source ⊓ D.compl
  let hW : (W : Set X) ⊆ f.source := fun _ hx => hx.1
  let z₁ : f.trapped := f.trappedMap ⟨z, hztrapped⟩
  have hUopen : IsOpen U := by
    obtain ⟨w, hw, hUw⟩ := hcomp 0
    rw [← hV0, hUw]
    exact f.isOpen_omega.connectedComponentIn
  let L : Set X := K \ U
  have hLcompact : IsCompact L := hK.diff hUopen
  have hLsource : L ⊆ W := by
    rintro x ⟨hxK, hxU⟩
    refine ⟨hKsource hxK, ?_⟩
    intro hxD
    exact hxU (hD hxD).1
  have hWcompl : (W : Set X) ⊆ D.compl := fun _ hx => hx.2
  refine ⟨D, p, W, hW, z₁, hz₁restricted, L, hWcompl,
    hLcompact, hLsource, ?_⟩
  intro n
  have heq : (f.restrictSource W hW).orbit n ⟨z₁, hz₁restricted⟩ =
      f.orbit (n + 1) ⟨z, hztrapped⟩ := by
    apply Option.some.inj
    rw [← (f.restrictSource W hW).iterate_eq_some_orbit n
      ⟨z₁, hz₁restricted⟩]
    exact hiter n
  rw [heq]
  refine ⟨horbitK (n + 1), ?_⟩
  intro hmemU
  have hmemV0 : f.orbit (n + 1) ⟨z, hztrapped⟩ ∈ V 0 := by
    rwa [hV0]
  exact Set.disjoint_left.mp (hdis (by omega : n + 1 ≠ 0))
    (horbit (n + 1)) hmemV0

end SurfaceDynamics.LocalMap
