/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LocalDynamics
import BoundedWanderingDomains.Surfaces.PlaneReading
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

/-! # Restricting a local surface map to a smaller open source -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics
namespace LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- Restrict the source of a local map to a smaller open set. -/
def restrictSource (f : LocalMap X) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) : LocalMap X where
  source := V
  map := fun x => f.map ⟨x, hV x.property⟩

@[simp] theorem restrictSource_source (f : LocalMap X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source) :
    (f.restrictSource V hV).source = V := rfl

@[simp] theorem restrictSource_map (f : LocalMap X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (x : V) :
    (f.restrictSource V hV).map x = f.map ⟨x, hV x.property⟩ := rfl

/-- Restricting the source does not change a finite partial iterate provided
all of its preceding values remain in the smaller source. -/
theorem restrictSource_iterate_eq_of_stays (f : LocalMap X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (x : X) (n : ℕ)
    (hstay : ∀ k < n, ∃ y ∈ V, f.iterate k x = some y) :
    (f.restrictSource V hV).iterate n x = f.iterate n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      obtain ⟨y, hyV, hxy⟩ := hstay 0 (Nat.zero_lt_succ n)
      have hxy' : x = y := Option.some.inj (by simpa using hxy)
      subst y
      rw [(f.restrictSource V hV).iterate_succ n x hyV,
        f.iterate_succ n x (hV hyV)]
      change (f.restrictSource V hV).iterate n (f.map ⟨x, hV hyV⟩) =
        f.iterate n (f.map ⟨x, hV hyV⟩)
      apply ih
      intro k hk
      obtain ⟨y, hyV', hy⟩ := hstay (k + 1) (Nat.succ_lt_succ hk)
      refine ⟨y, hyV', ?_⟩
      simpa only [f.iterate_succ k x (hV hyV)] using hy

/-- An orbit which remains in the smaller source is still a trapped orbit
after restriction. -/
theorem restrictSource_mem_trapped_of_orbit_mem (f : LocalMap X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    {x : X} (hx : x ∈ f.trapped)
    (hstay : ∀ n, f.orbit n ⟨x, hx⟩ ∈ V) :
    x ∈ (f.restrictSource V hV).trapped := by
  intro n
  refine ⟨f.orbit n ⟨x, hx⟩, hstay n, ?_⟩
  rw [f.restrictSource_iterate_eq_of_stays V hV x n]
  · exact f.iterate_eq_some_orbit n ⟨x, hx⟩
  · intro k hk
    exact ⟨f.orbit k ⟨x, hx⟩, hstay k,
      f.iterate_eq_some_orbit k ⟨x, hx⟩⟩

/-- On such an orbit, the restricted partial iterates have exactly the old
surface values.  This is the form used after deleting a small disk from the
first wandering component of a globally defined map. -/
theorem restrictSource_iterate_eq_some_orbit (f : LocalMap X)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    {x : X} (hx : x ∈ f.trapped)
    (hstay : ∀ n, f.orbit n ⟨x, hx⟩ ∈ V) (n : ℕ) :
    (f.restrictSource V hV).iterate n x =
      some (f.orbit n ⟨x, hx⟩) := by
  rw [f.restrictSource_iterate_eq_of_stays V hV x n]
  · exact f.iterate_eq_some_orbit n ⟨x, hx⟩
  · intro k hk
    exact ⟨f.orbit k ⟨x, hx⟩, hstay k,
      f.iterate_eq_some_orbit k ⟨x, hx⟩⟩

/-- Openness and holomorphicity pass to a restriction of the open source. -/
theorem isOpenHolomorphic_restrictSource (f : LocalMap X)
    (hf : IsOpenHolomorphic f) (V : TopologicalSpace.Opens X)
    (hV : (V : Set X) ⊆ f.source) :
    IsOpenHolomorphic (f.restrictSource V hV) := by
  let i : V → f.source := fun x => ⟨x, hV x.property⟩
  have hiopen : IsOpenMap i := by
    exact V.isOpen.isOpenMap_subtype_val.subtype_mk
      (fun x : V => hV x.property)
  have hidiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i := by
    apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff
      f.source i).mp
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : V → X)
    exact AreaDeficit.Surfaces.mdifferentiable_subtype_val V
  exact ⟨hf.1.comp hiopen, hf.2.comp hidiff⟩

end LocalMap
end SurfaceDynamics

#print axioms SurfaceDynamics.LocalMap.isOpenHolomorphic_restrictSource
