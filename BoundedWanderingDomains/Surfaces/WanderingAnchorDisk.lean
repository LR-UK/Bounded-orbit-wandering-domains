/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
import BoundedWanderingDomains.Surfaces.LocalMapRestriction
import BoundedWanderingDomains.Surfaces.WanderingOrbitStructure

/-! # A fixed hyperbolic anchor inside the first wandering component -/

open Set Function
open scoped Manifold Topology ContDiff

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Delete a small closed coordinate disk in the initial wandering component,
away from the marked point.  Every later component, and hence the marked tail
orbit, lies in the resulting fixed hyperbolic surface. -/
theorem LocalMap.IsWanderingComponent.exists_anchorDisk_orbit_components
    (f : LocalMap X) {U : Set X} (hU : f.IsWanderingComponent U)
    {z : X} (hz : z ∈ U) :
    ∃ (V : ℕ → Set X) (hztrapped : z ∈ f.trapped)
      (D : RiemannDynamics.CoordDisk X),
      V 0 = U ∧
      (∀ n, f.IsComponent (V n)) ∧
      (∀ n, f.orbit n ⟨z, hztrapped⟩ ∈ V n) ∧
      Pairwise (fun n m => Disjoint (V n) (V m)) ∧
      D.closedCarrier ⊆ U \ {z} ∧
      (∀ n, 0 < n → V n ⊆ (D.compl : Set X)) := by
  obtain ⟨V, hztrapped, hV0, hcomp, horbit, hdis⟩ :=
    hU.exists_orbit_components f hz
  obtain ⟨w, hwomega, hVw⟩ := hcomp 0
  letI : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace ℂ X
  have hUopen : IsOpen U := by
    rw [← hV0, hVw]
    exact f.isOpen_omega.connectedComponentIn
  obtain ⟨D, hD⟩ := exists_coordDisk_closedCarrier_subset_diff hUopen hz
  refine ⟨V, hztrapped, D, hV0, hcomp, horbit, hdis, hD, ?_⟩
  intro n hn x hxV hxD
  have hxU : x ∈ U := (hD hxD).1
  have hxV0 : x ∈ V 0 := by rw [hV0]; exact hxU
  exact Set.disjoint_left.mp (hdis (Nat.ne_of_lt hn)) hxV0 hxV

/-- The deleted disk supplies a concrete universal disc cover of the fixed
ambient surface containing every later wandering component. -/
theorem LocalMap.IsWanderingComponent.exists_hyperbolicAnchor_orbit_components
    (f : LocalMap X) {U : Set X} (hU : f.IsWanderingComponent U)
    {z : X} (hz : z ∈ U) :
    ∃ (V : ℕ → Set X) (hztrapped : z ∈ f.trapped)
      (D : RiemannDynamics.CoordDisk X)
      (p : AreaDeficit.Surfaces.DiscCover D.compl),
      V 0 = U ∧
      (∀ n, f.IsComponent (V n)) ∧
      (∀ n, f.orbit n ⟨z, hztrapped⟩ ∈ V n) ∧
      Pairwise (fun n m => Disjoint (V n) (V m)) ∧
      D.closedCarrier ⊆ U \ {z} ∧
      (∀ n, 0 < n → V n ⊆ (D.compl : Set X)) := by
  obtain ⟨V, hztrapped, D, hV0, hcomp, horbit, hdis, hD, htail⟩ :=
    hU.exists_anchorDisk_orbit_components f hz
  letI : IsManifold 𝓘(ℂ) ω X :=
    AreaDeficit.Surfaces.isManifold_analytic_of_complex
  let p : AreaDeficit.Surfaces.DiscCover D.compl :=
    Classical.choice (AreaDeficit.Surfaces.nonempty_discCover_coordDisk_compl D)
  exact ⟨V, hztrapped, D, p, hV0, hcomp, horbit, hdis, hD, htail⟩

/-- After deleting the anchor disk, restrict the original local map to the
intersection of its source with the hyperbolic complement.  The marked orbit
from time one onwards is trapped for this restriction and its partial
iterates are the original tail orbit. -/
theorem LocalMap.IsWanderingComponent.exists_hyperbolic_restricted_tail
    (f : LocalMap X) {U : Set X} (hU : f.IsWanderingComponent U)
    {z : X} (hz : z ∈ U) :
    ∃ (V : ℕ → Set X) (hztrapped : z ∈ f.trapped)
      (D : RiemannDynamics.CoordDisk X)
      (p : AreaDeficit.Surfaces.DiscCover D.compl),
      let W : TopologicalSpace.Opens X := f.source ⊓ D.compl
      let hW : (W : Set X) ⊆ f.source := fun _ hx => hx.1
      let z₁ : f.trapped := f.trappedMap ⟨z, hztrapped⟩
      V 0 = U ∧
      (∀ n, f.IsComponent (V n)) ∧
      (∀ n, f.orbit n ⟨z, hztrapped⟩ ∈ V n) ∧
      Pairwise (fun n m => Disjoint (V n) (V m)) ∧
      D.closedCarrier ⊆ U \ {z} ∧
      (∀ n, 0 < n → V n ⊆ (D.compl : Set X)) ∧
      (z₁ : X) ∈ (f.restrictSource W hW).trapped ∧
      (∀ n, (f.restrictSource W hW).iterate n (z₁ : X) =
        some (f.orbit (n + 1) ⟨z, hztrapped⟩)) := by
  obtain ⟨V, hztrapped, D, p, hV0, hcomp, horbit, hdis, hD, htail⟩ :=
    hU.exists_hyperbolicAnchor_orbit_components f hz
  let W : TopologicalSpace.Opens X := f.source ⊓ D.compl
  let hW : (W : Set X) ⊆ f.source := fun _ hx => hx.1
  let z₁ : f.trapped := f.trappedMap ⟨z, hztrapped⟩
  have horbit_succ (n : ℕ) :
      f.orbit n z₁ = f.orbit (n + 1) ⟨z, hztrapped⟩ := by
    dsimp [z₁, LocalMap.orbit]
  have hstay (n : ℕ) : f.orbit n z₁ ∈ W := by
    have hn : 0 < n + 1 := Nat.zero_lt_succ n
    exact ⟨f.orbit_mem_source n z₁,
      htail (n + 1) hn (horbit (n + 1))⟩
  have hz₁restricted : (z₁ : X) ∈ (f.restrictSource W hW).trapped :=
    f.restrictSource_mem_trapped_of_orbit_mem W hW z₁.property hstay
  refine ⟨V, hztrapped, D, p, hV0, hcomp, horbit, hdis, hD, htail,
    hz₁restricted, ?_⟩
  intro n
  rw [f.restrictSource_iterate_eq_some_orbit W hW z₁.property hstay n,
    horbit_succ n]

end SurfaceDynamics
