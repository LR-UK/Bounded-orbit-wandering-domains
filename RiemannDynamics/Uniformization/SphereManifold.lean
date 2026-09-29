module

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
public import RiemannDynamics.Sphere.Basic
public import RiemannDynamics.Sphere.MobiusAction
public import RiemannDynamics.NormalFamilies.Spherical
public import FunctionTheory.RiemannSphere.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

/-!
# The Riemann sphere as a complex-analytic manifold

The Riemann sphere `ℂ̂ = OnePoint ℂ` carries a canonical structure of a
one-dimensional complex-analytic manifold: the atlas consists of the finite
chart (the identity on `ℂ̂ ∖ {∞}`) and the infinity chart (`z ↦ z⁻¹` on
`ℂ̂ ∖ {0}`), whose transition map `z ↦ z⁻¹` is analytic on `ℂ ∖ {0}`.

This file bundles the unbundled charts of `Sphere/Basic.lean` into
`OpenPartialHomeomorph`s and registers the instances

* `ChartedSpace ℂ ℂ̂`;
* `IsManifold 𝓘(ℂ) ω ℂ̂` — the analytic (hence also `C^n` for every `n`)
  manifold structure.

The chart maps agree with `chartFiniteMap` and `chartInftyMap` on the
corresponding chart sources, so all holomorphy statements phrased through the
concrete chart maps transfer to the manifold language and back.

## Main definitions

* `sphereChartFinite : OpenPartialHomeomorph ℂ̂ ℂ` — the identity chart with
  source `ℂ̂ ∖ {∞}`;
* `sphereChartInfty : OpenPartialHomeomorph ℂ̂ ℂ` — the inversion chart with
  source `ℂ̂ ∖ {0}`;
* `inversionHomeomorph : ℂ̂ ≃ₜ ℂ̂` — the Möbius inversion `z ↦ z⁻¹` as a
  self-homeomorphism of the sphere.
-/

open OnePoint Topology
open scoped Manifold

namespace RiemannDynamics

/-! ## The inversion homeomorphism -/

/-- The Möbius inversion `inversionGL` is an involution of `ℂ̂`. -/
theorem inversionGL_smul_smul (z : ℂ̂) : inversionGL • inversionGL • z = z := by
  cases z with
  | infty =>
    rw [inversionGL_smul_infty, inversionGL_smul_coe, ite_eq_left rfl]
  | coe w =>
    by_cases hw : w = 0
    · subst hw
      rw [inversionGL_smul_coe, ite_eq_left rfl, inversionGL_smul_infty]
    · rw [inversionGL_smul_coe, ite_eq_right hw, inversionGL_smul_coe,
        ite_eq_right (inv_ne_zero hw), inv_inv]

/-- The Möbius inversion `z ↦ z⁻¹` as a self-homeomorphism of the Riemann
sphere, swapping `0` and `∞`. -/
noncomputable def inversionHomeomorph : ℂ̂ ≃ₜ ℂ̂ :=
  { toFun := (inversionGL • ·)
    invFun := (inversionGL • ·)
    left_inv := inversionGL_smul_smul
    right_inv := inversionGL_smul_smul
    continuous_toFun := continuous_gl_smul inversionGL
    continuous_invFun := continuous_gl_smul inversionGL }

/-- The inversion homeomorphism acts by the Möbius element `inversionGL`. -/
@[simp]
theorem inversionHomeomorph_apply (z : ℂ̂) :
    inversionHomeomorph z = inversionGL • z := rfl

/-- The inversion homeomorphism is its own inverse, since `inversionGL` is an
involution of the sphere. -/
@[simp]
theorem inversionHomeomorph_symm_apply (z : ℂ̂) :
    inversionHomeomorph.symm z = inversionGL • z := rfl

/-- The inversion sends exactly `0` to `∞`. -/
theorem inversionGL_smul_eq_infty_iff (z : ℂ̂) :
    inversionGL • z = (∞ : ℂ̂) ↔ z = ((0 : ℂ) : ℂ̂) := by
  cases z with
  | infty =>
    rw [inversionGL_smul_infty]
    exact iff_of_false (OnePoint.coe_ne_infty 0) (OnePoint.infty_ne_coe 0)
  | coe w =>
    by_cases hw : w = 0
    · subst hw
      rw [inversionGL_smul_coe, ite_eq_left rfl]
      exact iff_of_true rfl rfl
    · rw [inversionGL_smul_coe, ite_eq_right hw]
      exact iff_of_false (OnePoint.coe_ne_infty _)
        (fun h => hw (OnePoint.coe_eq_coe.mp h))

/-! ## The bundled charts -/

/-- The coercion `ℂ → ℂ̂` as an `OpenPartialHomeomorph` with source `ℂ` and
target `ℂ̂ ∖ {∞}`. -/
noncomputable def coeSpherePartialHomeomorph : OpenPartialHomeomorph ℂ ℂ̂ :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph _

/-- The finite chart of the Riemann sphere: the inverse of the coercion
`ℂ → ℂ̂`, with source `ℂ̂ ∖ {∞}` and target `ℂ`. -/
noncomputable def sphereChartFinite : OpenPartialHomeomorph ℂ̂ ℂ :=
  RiemannSphere.coeOpenPartialHomeomorph.symm

/-- The infinity chart of the Riemann sphere: the inversion followed by the
finite chart, with source `ℂ̂ ∖ {0}` and target `ℂ`. -/
noncomputable def sphereChartInfty : OpenPartialHomeomorph ℂ̂ ℂ :=
  RiemannSphere.invCoeOpenPartialHomeomorph.symm

/-- The source of the bundled finite chart is the unbundled finite-chart source
`ℂ̂ ∖ {∞}`. -/
theorem sphereChartFinite_source : sphereChartFinite.source = chartFiniteSource := by
  change RiemannSphere.coeOpenPartialHomeomorph.target = chartFiniteSource
  ext z
  simp [RiemannSphere.coeOpenPartialHomeomorph,
    RiemannSphere.coePartialEquiv, chartFiniteSource]

/-- The finite chart inverts the coercion `ℂ → ℂ̂`: it sends a finite point back to the
complex number naming it. -/
@[simp]
theorem sphereChartFinite_coe (w : ℂ) : sphereChartFinite ((w : ℂ̂)) = w := by
  change ((w : ℂ̂).toComplex) = w
  exact RiemannSphere.toComplex_coe

/-- The inverse of the finite chart is the coercion `ℂ → ℂ̂`. -/
@[simp]
theorem sphereChartFinite_symm_apply (w : ℂ) :
    sphereChartFinite.symm w = (w : ℂ̂) := rfl

/-- On its source, the bundled finite chart agrees with `chartFiniteMap`. -/
theorem sphereChartFinite_eqOn :
    Set.EqOn sphereChartFinite chartFiniteMap chartFiniteSource := by
  intro z hz
  obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
  rw [sphereChartFinite_coe]
  rfl

/-- The source of the bundled infinity chart is the unbundled infinity-chart source
`ℂ̂ ∖ {0}`. -/
theorem sphereChartInfty_source : sphereChartInfty.source = chartInftySource := by
  change RiemannSphere.invCoeOpenPartialHomeomorph.target = chartInftySource
  ext z
  simp [RiemannSphere.invCoeOpenPartialHomeomorph,
    RiemannSphere.coeOpenPartialHomeomorph,
    RiemannSphere.coePartialEquiv, RiemannSphere.invHomeomorph,
    RiemannSphere.invEquiv, chartInftySource]

/-- The infinity chart is the inversion followed by the finite chart. -/
@[simp]
theorem sphereChartInfty_apply (z : ℂ̂) :
    sphereChartInfty z = sphereChartFinite (inversionGL • z) := by
  induction z using OnePoint.rec with
  | infty =>
    rw [inversionGL_smul_infty, sphereChartFinite_coe]
    change ((∞ : ℂ̂)⁻¹).toComplex = 0
    simp
  | coe z =>
    by_cases hz : z = 0
    · subst z
      rw [inversionGL_smul_coe, ite_eq_left rfl]
      change ((((0 : ℂ) : ℂ̂)⁻¹).toComplex) = (∞ : ℂ̂).toComplex
      simp
    · rw [inversionGL_smul_coe, ite_eq_right hz, sphereChartFinite_coe]
      simp only [sphereChartInfty,
        RiemannSphere.invCoeOpenPartialHomeomorph_symm_apply,
        RiemannSphere.inv_coe hz, RiemannSphere.toComplex_coe]

/-- On its source, the bundled infinity chart agrees with `chartInftyMap`. -/
theorem sphereChartInfty_eqOn :
    Set.EqOn sphereChartInfty chartInftyMap chartInftySource := by
  intro z hz
  cases z with
  | infty =>
    have h0 : chartInftyMap (∞ : ℂ̂) = 0 := rfl
    rw [sphereChartInfty_apply, inversionGL_smul_infty, sphereChartFinite_coe, h0]
  | coe w =>
    have hw : w ≠ 0 := by
      intro h
      exact hz (by simp [h])
    have hval : chartInftyMap ((w : ℂ̂)) = w⁻¹ := rfl
    rw [sphereChartInfty_apply, inversionGL_smul_coe, ite_eq_right hw,
      sphereChartFinite_coe, hval]

/-- The inverse of the infinity chart sends `w` to the inversion of the finite point `w`,
so that `0` is carried to `∞`. -/
theorem sphereChartInfty_symm_apply (w : ℂ) :
    sphereChartInfty.symm w = inversionGL • ((w : ℂ̂)) := by
  by_cases hw : w = 0
  · subst w
    rw [inversionGL_smul_coe, ite_eq_left rfl]
    change (((0 : ℂ) : ℂ̂)⁻¹) = (∞ : ℂ̂)
    exact RiemannSphere.inv_zero'
  · rw [inversionGL_smul_coe, ite_eq_right hw]
    exact RiemannSphere.inv_coe hw

/-! ## The charted-space and manifold instances -/

/-- The project uses FunctionTheory's canonical Riemann-sphere atlas.  Keeping
this historical instance name as an alias avoids a second, definitionally
different manifold structure on the same type. -/
noncomputable instance chartedSpaceSphere : ChartedSpace ℂ ℂ̂ := by
  infer_instance

/-- Analyticity of the canonical Riemann-sphere atlas, at the order used by
the uniformization development. -/
instance isManifoldSphere : IsManifold 𝓘(ℂ) ω ℂ̂ := by
  infer_instance

theorem sphereChartFinite_eq_canonical : sphereChartFinite =
    RiemannSphere.coeOpenPartialHomeomorph.symm := by
  rfl

theorem sphereChartInfty_eq_canonical : sphereChartInfty =
    RiemannSphere.invCoeOpenPartialHomeomorph.symm := by
  rfl

end RiemannDynamics
