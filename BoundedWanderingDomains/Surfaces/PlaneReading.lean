/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.HolomorphicLifting

/-! # Ordinary complex derivatives of maps defined on open submanifolds

Extensions are used only to take ordinary derivatives at interior points.
Every statement identifies the extension with the original map there.
-/

open Set Function Filter Topology
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]

omit [IsManifold 𝓘(ℂ) 1 M] [IsManifold 𝓘(ℂ) 1 N] in
theorem mdifferentiableAt_subtype_iff {U : TopologicalSpace.Opens M}
    {f : M → N} {x : U} :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x : U => f x) x ↔
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x :=
  (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val _ _).symm

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- The inclusion of an open submanifold is holomorphic. -/
theorem mdifferentiable_subtype_val (U : TopologicalSpace.Opens M) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : U → M) :=
  fun _ => mdifferentiableAt_subtype_iff.mpr mdifferentiableAt_id

/-- Scalar reading of a map on a plane domain. Values outside the domain
are immaterial; all derivative statements below are at interior points. -/
noncomputable def planeExtension {U : TopologicalSpace.Opens ℂ} (g : U → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then g ⟨z,hz⟩ else 0

@[simp] theorem planeExtension_coe {U : TopologicalSpace.Opens ℂ} (g : U → ℂ) (z : U) :
    planeExtension g z = g z := by simp [planeExtension, z.2]

theorem planeExtension_mdifferentiableAt {U : TopologicalSpace.Opens ℂ} {g : U → ℂ}
    {w : U} (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g w) :
    DifferentiableAt ℂ (planeExtension g) w := by
  have hfun : (fun v : U => planeExtension g v) = g := funext (planeExtension_coe g)
  have h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v : U => planeExtension g v) w := by
    rw [hfun]
    exact hg
  exact (mdifferentiableAt_subtype_iff.mp h).differentiableAt

theorem planeExtension_differentiableOn {U : TopologicalSpace.Opens ℂ} {g : U → ℂ}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    DifferentiableOn ℂ (planeExtension g) U :=
  fun w hw => (planeExtension_mdifferentiableAt (hg ⟨w,hw⟩)).differentiableWithinAt

/-- The ordinary chain rule applies to the scalar readings of subtype-valued maps. -/
theorem planeExtension_deriv_comp {U V : TopologicalSpace.Opens ℂ}
    {g : V → ℂ} {h : U → V} {w : U}
    (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (h w))
    (hh : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h w) :
    deriv (planeExtension (g ∘ h)) w = deriv (planeExtension g) (h w) *
      deriv (planeExtension (fun z => (h z : ℂ))) w := by
  have hscalar := (mdifferentiable_subtype_val V (h w)).comp w hh
  have hhd : DifferentiableAt ℂ (planeExtension (fun z => (h z : ℂ))) w :=
    planeExtension_mdifferentiableAt hscalar
  have hgd := planeExtension_mdifferentiableAt hg
  have he : planeExtension (g ∘ h) =ᶠ[𝓝 (w : ℂ)]
      planeExtension g ∘ planeExtension (fun z => (h z : ℂ)) := by
    filter_upwards [U.isOpen.mem_nhds w.2] with z hz
    change planeExtension (g ∘ h) (⟨z,hz⟩ : U) =
      planeExtension g (planeExtension (fun z => (h z : ℂ)) (⟨z,hz⟩ : U))
    rw [planeExtension_coe, planeExtension_coe, planeExtension_coe]
    rfl
  rw [he.deriv_eq]
  have hp : planeExtension (fun z => (h z : ℂ)) w = (h w : ℂ) := planeExtension_coe _ w
  rw [deriv_comp (w : ℂ) (hp.symm ▸ hgd) hhd, hp]

end AreaDeficit.Surfaces
