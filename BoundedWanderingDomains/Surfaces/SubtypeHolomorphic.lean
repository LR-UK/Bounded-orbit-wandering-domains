/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Complex

/-! # Holomorphicity of maps valued in an open submanifold -/
open Set Function
open scoped Manifold
namespace AreaDeficit.Surfaces
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

theorem mdifferentiableAt_subtypeVal_comp_iff (U : TopologicalSpace.Opens N)
    (f : M → U) (x : M) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ f) x ↔
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f univ x

theorem mdifferentiable_subtypeVal_comp_iff (U : TopologicalSpace.Opens N)
    (f : M → U) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ f) ↔
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  simp only [MDifferentiable,mdifferentiableAt_subtypeVal_comp_iff]

end AreaDeficit.Surfaces
