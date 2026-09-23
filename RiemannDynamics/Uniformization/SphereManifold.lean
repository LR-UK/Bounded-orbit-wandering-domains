/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Sphere.Basic
import RiemannDynamics.Sphere.MobiusAction
import RiemannDynamics.NormalFamilies.Spherical
import Mathlib.Geometry.Manifold.IsManifold.Basic

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
  coeSpherePartialHomeomorph.symm

/-- The infinity chart of the Riemann sphere: the inversion followed by the
finite chart, with source `ℂ̂ ∖ {0}` and target `ℂ`. -/
noncomputable def sphereChartInfty : OpenPartialHomeomorph ℂ̂ ℂ :=
  inversionHomeomorph.toOpenPartialHomeomorph.trans sphereChartFinite

/-- The source of the bundled finite chart is the unbundled finite-chart source
`ℂ̂ ∖ {∞}`. -/
theorem sphereChartFinite_source : sphereChartFinite.source = chartFiniteSource := by
  have hrange : chartFiniteSource = Set.range ((↑) : ℂ → ℂ̂) := by
    ext z
    simp only [chartFiniteSource, Set.mem_ofPred_eq, Set.mem_range]
    exact OnePoint.ne_infty_iff_exists
  rw [hrange]
  simp [sphereChartFinite, coeSpherePartialHomeomorph]

/-- The finite chart inverts the coercion `ℂ → ℂ̂`: it sends a finite point back to the
complex number naming it. -/
@[simp]
theorem sphereChartFinite_coe (w : ℂ) : sphereChartFinite ((w : ℂ̂)) = w := by
  have h : coeSpherePartialHomeomorph w = (w : ℂ̂) := rfl
  rw [sphereChartFinite, ← h]
  exact coeSpherePartialHomeomorph.left_inv (by simp [coeSpherePartialHomeomorph])

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
  ext z
  simp only [sphereChartInfty, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ,
    true_and, Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply,
    inversionHomeomorph_apply, sphereChartFinite_source, chartFiniteSource,
    chartInftySource, Set.mem_ofPred_eq]
  exact not_congr (inversionGL_smul_eq_infty_iff z)

/-- The infinity chart is the inversion followed by the finite chart. -/
@[simp]
theorem sphereChartInfty_apply (z : ℂ̂) :
    sphereChartInfty z = sphereChartFinite (inversionGL • z) := rfl

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
    sphereChartInfty.symm w = inversionGL • ((w : ℂ̂)) := rfl

/-! ## The charted-space and manifold instances -/

noncomputable instance chartedSpaceSphere : ChartedSpace ℂ ℂ̂ where
  atlas := {sphereChartFinite, sphereChartInfty}
  chartAt z :=
    match z with
    | (∞ : ℂ̂) => sphereChartInfty
    | ((_ : ℂ) : ℂ̂) => sphereChartFinite
  mem_chart_source z := by
    cases z with
    | infty =>
      change (∞ : ℂ̂) ∈ sphereChartInfty.source
      rw [sphereChartInfty_source]
      exact OnePoint.infty_ne_coe 0
    | coe w =>
      change (w : ℂ̂) ∈ sphereChartFinite.source
      rw [sphereChartFinite_source]
      exact OnePoint.coe_ne_infty w
  chart_mem_atlas z := by
    cases z with
    | infty => exact Set.mem_insert_iff.mpr (Or.inr rfl)
    | coe w => exact Set.mem_insert _ _

open scoped ContDiff in
/-- The transition maps of the sphere atlas are analytic: each one is either
the identity or the inversion `w ↦ w⁻¹` away from `0`. -/
instance isManifoldSphere : IsManifold 𝓘(ℂ) ω ℂ̂ := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ]
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · -- finite ∘ finite⁻¹ is the identity.
    apply contDiffOn_id.congr
    intro w _
    change sphereChartFinite (sphereChartFinite.symm w) = id w
    rw [sphereChartFinite_symm_apply, sphereChartFinite_coe, id_eq]
  · -- infty ∘ finite⁻¹ is the inversion away from 0.
    have hsub : (sphereChartFinite.symm.trans sphereChartInfty).source ⊆
        {(0 : ℂ)}ᶜ := by
      intro w hw
      rw [OpenPartialHomeomorph.trans_source] at hw
      have hmem := hw.2
      rw [Set.mem_preimage, sphereChartInfty_source] at hmem
      rw [sphereChartFinite_symm_apply] at hmem
      simp only [chartInftySource, Set.mem_ofPred_eq] at hmem
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h0 => hmem (OnePoint.coe_eq_coe.mpr h0)
    refine ((contDiffOn_inv ℂ).mono hsub).congr ?_
    intro w hw
    have hw0 : w ≠ 0 := by
      have := hsub hw
      simpa using this
    have hmem : ((w : ℂ̂)) ∈ chartInftySource := by
      simp only [chartInftySource, Set.mem_ofPred_eq]
      exact fun h => hw0 (OnePoint.coe_eq_coe.mp h)
    change sphereChartInfty (sphereChartFinite.symm w) = w⁻¹
    rw [sphereChartFinite_symm_apply, sphereChartInfty_eqOn hmem]
    rfl
  · -- finite ∘ infty⁻¹ is the inversion away from 0.
    have hsub : (sphereChartInfty.symm.trans sphereChartFinite).source ⊆
        {(0 : ℂ)}ᶜ := by
      intro w hw
      rw [OpenPartialHomeomorph.trans_source] at hw
      have hmem := hw.2
      rw [Set.mem_preimage, sphereChartFinite_source] at hmem
      simp only [chartFiniteSource, Set.mem_ofPred_eq,
        sphereChartInfty_symm_apply] at hmem
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      subst h0
      exact hmem ((inversionGL_smul_eq_infty_iff _).mpr rfl)
    refine ((contDiffOn_inv ℂ).mono hsub).congr ?_
    intro w hw
    have hw0 : w ≠ 0 := by
      have := hsub hw
      simpa using this
    change sphereChartFinite (sphereChartInfty.symm w) = w⁻¹
    rw [sphereChartInfty_symm_apply, inversionGL_smul_coe, ite_eq_right hw0,
      sphereChartFinite_coe]
  · -- infty ∘ infty⁻¹ is the identity.
    apply contDiffOn_id.congr
    intro w hw
    rw [OpenPartialHomeomorph.trans_source] at hw
    have hmem := hw.2
    rw [Set.mem_preimage, sphereChartInfty_source] at hmem
    change sphereChartInfty (sphereChartInfty.symm w) = id w
    rw [sphereChartInfty_eqOn hmem, sphereChartInfty_symm_apply, id_eq]
    by_cases hw0 : w = 0
    · subst hw0
      rw [inversionGL_smul_coe, ite_eq_left rfl]
      rfl
    · rw [inversionGL_smul_coe, ite_eq_right hw0]
      change (w⁻¹)⁻¹ = w
      rw [inv_inv]

end RiemannDynamics
