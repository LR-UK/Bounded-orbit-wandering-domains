/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.LocalTrappedTopology
import BoundedWanderingDomains.Surfaces.LocalDynamics

/-! # A harmless total extension of an open-source local map -/

open Set Function
open scoped Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X]

/-- Extend a local map by the identity outside its source.  Only its values on
the source are used. -/
noncomputable def totalize (f : LocalMap X) (x : X) : X := by
  classical
  exact if hx : x ∈ f.source then f.map ⟨x, hx⟩ else x

theorem totalize_eq (f : LocalMap X) {x : X} (hx : x ∈ f.source) :
    f.totalize x = f.map ⟨x, hx⟩ := by
  simp [totalize, hx]

theorem continuousOn_totalize (f : LocalMap X) (hf : Continuous f.map) :
    ContinuousOn f.totalize f.source := by
  rw [continuousOn_iff_continuous_restrict]
  convert hf using 1
  funext x
  exact f.totalize_eq x.property

theorem orbit_succ (f : LocalMap X) (n : ℕ) (x : f.trapped) :
    f.orbit (n + 1) x =
      f.map ⟨f.orbit n x, f.orbit_mem_source n x⟩ := by
  exact congrArg Subtype.val
    (Function.iterate_succ_apply' f.trappedMap n x)

theorem totalize_iterate_orbit (f : LocalMap X) (n : ℕ) (x : f.trapped) :
    (f.totalize^[n]) (x : X) = f.orbit n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, f.totalize_eq (f.orbit_mem_source n x),
        f.orbit_succ]

theorem trapped_subset_trappedSet_totalize (f : LocalMap X) :
    f.trapped ⊆ AreaDeficit.trappedSet f.totalize f.source := by
  intro x hx n
  rw [f.totalize_iterate_orbit n ⟨x, hx⟩]
  exact f.orbit_mem_source n ⟨x, hx⟩

theorem local_iterate_eq_totalize_iterate_of_stays (f : LocalMap X)
    {x : X} (hstay : ∀ n, (f.totalize^[n]) x ∈ f.source) (n : ℕ) :
    f.iterate n x = some ((f.totalize^[n]) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hx : x ∈ f.source := hstay 0
      rw [f.iterate_succ n x hx]
      have hshift : ∀ k, (f.totalize^[k]) (f.map ⟨x, hx⟩) ∈ f.source := by
        intro k
        rw [← f.totalize_eq hx, ← Function.iterate_succ_apply]
        exact hstay (k + 1)
      rw [ih hshift, Function.iterate_succ_apply, f.totalize_eq hx]

theorem trappedSet_totalize_eq_trapped (f : LocalMap X) :
    AreaDeficit.trappedSet f.totalize f.source = f.trapped := by
  apply Set.Subset.antisymm
  · intro x hx n
    exact ⟨(f.totalize^[n]) x, hx n,
      f.local_iterate_eq_totalize_iterate_of_stays hx n⟩
  · exact f.trapped_subset_trappedSet_totalize

end SurfaceDynamics.LocalMap
