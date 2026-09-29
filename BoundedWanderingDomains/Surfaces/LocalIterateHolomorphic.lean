module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalDynamics
public import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic
public import BoundedWanderingDomains.Surfaces.PlaneReading

@[expose] public section

/-! # Holomorphic iterates on an open trapped set -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- The genuine surface-valued iterate on an open set of trapped points. -/
noncomputable def orbitOn (f : LocalMap X) (W : TopologicalSpace.Opens X)
    (hW : (W : Set X) ⊆ f.trapped) (n : ℕ) (x : W) : X :=
  f.orbit n ⟨x, hW x.property⟩

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] in
@[simp] theorem orbitOn_zero (f : LocalMap X) (W : TopologicalSpace.Opens X)
    (hW : (W : Set X) ⊆ f.trapped) (x : W) :
    f.orbitOn W hW 0 x = x := rfl

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] in
theorem orbitOn_succ (f : LocalMap X) (W : TopologicalSpace.Opens X)
    (hW : (W : Set X) ⊆ f.trapped) (n : ℕ) (x : W) :
    f.orbitOn W hW (n + 1) x =
      f.map ⟨f.orbitOn W hW n x,
        f.orbit_mem_source n ⟨x, hW x.property⟩⟩ := by
  dsimp [orbitOn, orbit]
  have he : (f.trappedMap^[n]) (f.trappedMap ⟨x, hW x.property⟩) =
      f.trappedMap ((f.trappedMap^[n]) ⟨x, hW x.property⟩) :=
    (Function.iterate_succ_apply f.trappedMap n
      ⟨x, hW x.property⟩).symm.trans
      (Function.iterate_succ_apply' f.trappedMap n
        ⟨x, hW x.property⟩)
  exact congrArg Subtype.val he

/-- Holomorphicity of the local map propagates to every genuine iterate on
an open trapped set. -/
theorem mdifferentiable_orbitOn (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (W : TopologicalSpace.Opens X) (hW : (W : Set X) ⊆ f.trapped) (n : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f.orbitOn W hW n) := by
  induction n with
  | zero =>
      convert AreaDeficit.Surfaces.mdifferentiable_subtype_val W using 1
      funext x
      rfl
  | succ n ih =>
      let h : W → f.source := fun x =>
        ⟨f.orbitOn W hW n x,
          f.orbit_mem_source n ⟨x, hW x.property⟩⟩
      have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
        apply (AreaDeficit.Surfaces.mdifferentiable_subtypeVal_comp_iff
          f.source h).mp
        exact ih
      have hcomp := hf.2.comp hh
      convert hcomp using 1
      funext x
      exact f.orbitOn_succ W hW n x

end SurfaceDynamics.LocalMap
