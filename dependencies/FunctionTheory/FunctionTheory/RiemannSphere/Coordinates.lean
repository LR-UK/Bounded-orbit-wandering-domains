import FunctionTheory.RiemannSphere.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The finite-chart and inversion proofs follow Geoffrey Irving's Ray/Manifold/RiemannSphere.lean
at 753f7131cf96f4651294de4398368abf136c34de (Apache 2.0), using Mathlib's
ContDiff chart criterion directly in place of Ray's analytic-chart helpers. -/

open Set OneDimension
open scoped Topology OnePoint RiemannSphere

namespace RiemannSphere

theorem mAnalytic_coe : ContMDiff I I ⊤ (fun z : ℂ ↦ (z : 𝕊)) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨continuous_coe.continuousAt, ?_⟩
  simp only [extChartAt_coe]
  change ContDiffWithinAt ℂ ⊤ (fun w : ℂ => w) _ z
  exact contDiffAt_id.contDiffWithinAt

theorem mAnalyticAt_toComplex {z : ℂ} :
    ContMDiffAt I I ⊤ (OnePoint.toComplex : 𝕊 → ℂ) z := by
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_toComplex, ?_⟩
  simp only [toComplex_coe, extChartAt_coe]
  change ContDiffWithinAt ℂ ⊤ (fun w : ℂ => w) _ z
  exact contDiffAt_id.contDiffWithinAt

theorem mAnalyticAt_toComplex' {z : 𝕊} (ne : z ≠ ∞) :
    ContMDiffAt I I ⊤ (OnePoint.toComplex : 𝕊 → ℂ) z := by
  induction z using OnePoint.rec with
  | infty => exact (ne rfl).elim
  | coe z => exact mAnalyticAt_toComplex

theorem mAnalytic_inv : ContMDiff I I ⊤ (fun z : 𝕊 ↦ z⁻¹) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨continuous_inv.continuousAt, ?_⟩
  induction z using OnePoint.rec with
  | infty =>
    simp only [inv_inf, extChartAt_inf, ← coe_zero, extChartAt_coe, Function.comp_def,
      PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
      coePartialEquiv_symm_apply, toComplex_coe, PartialEquiv.coe_trans_symm,
      PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply,
      invEquiv_symm, inv_inv, toComplex_zero]
    exact contDiffAt_id.contDiffWithinAt
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp only [extChartAt_coe, PartialEquiv.symm_symm, Function.comp_def,
        coePartialEquiv_apply, coePartialEquiv_symm_apply, toComplex_coe,
        coe_zero, inv_zero', extChartAt_inf, PartialEquiv.trans_apply,
        coePartialEquiv_symm_apply, invEquiv_apply, Equiv.toPartialEquiv_apply,
        inv_inv, toComplex_coe]
      exact contDiffAt_id.contDiffWithinAt
    · simp only [inv_coe hz, extChartAt_coe, Function.comp_def,
        PartialEquiv.symm_symm, coePartialEquiv_apply, coePartialEquiv_symm_apply,
        toComplex_coe]
      apply ContDiffAt.contDiffWithinAt
      refine (contDiffAt_id.inv hz).congr_of_eventuallyEq ?_
      filter_upwards [continuousAt_id.eventually_ne hz] with w hw
      change w ≠ 0 at hw
      change ((w : 𝕊)⁻¹).toComplex = w⁻¹
      rw [inv_coe hw, toComplex_coe]

noncomputable def translation (a : ℂ) : 𝕊 ≃ₜ 𝕊 :=
  (Homeomorph.addRight a).onePointCongr

@[simp] theorem translation_coe (a z : ℂ) : translation a (z : 𝕊) = ↑(z + a) := rfl

@[simp] theorem translation_inf (a : ℂ) : translation a ∞ = ∞ := rfl

theorem mAnalytic_translation (a : ℂ) : ContMDiff I I ⊤ (translation a) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨(translation a).continuous.continuousAt, ?_⟩
  induction z using OnePoint.rec with
  | coe z =>
    simp only [translation_coe, extChartAt_coe]
    change ContDiffWithinAt ℂ ⊤ (fun w : ℂ => w + a) _ z
    exact (contDiffAt_id.add contDiffAt_const).contDiffWithinAt
  | infty =>
    simp only [translation_inf, extChartAt_inf, Function.comp_def,
      PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
      coePartialEquiv_symm_apply, PartialEquiv.coe_trans_symm,
      PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply,
      invEquiv_symm, inv_inf, toComplex_zero]
    change ContDiffWithinAt ℂ ⊤
      (fun w : ℂ => ((translation a ((w : 𝕊)⁻¹))⁻¹).toComplex) _ 0
    apply ContDiffAt.contDiffWithinAt
    have hn : (1 : ℂ) + a * 0 ≠ 0 := by simp
    refine ((contDiffAt_id.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)) hn)
      : ContDiffAt ℂ ⊤ (fun w : ℂ => w / (1 + a * w)) 0).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_const.add (continuous_const.mul continuous_id)).continuousAt.eventually_ne hn] with w hw
    by_cases hw0 : w = 0
    · subst w
      simp
    · rw [inv_coe hw0, translation_coe, toComplex_inv, toComplex_coe]
      change (w⁻¹ + a)⁻¹ = w / (1 + a * w)
      change 1 + a * w ≠ 0 at hw
      field_simp

theorem translation_symm_eq (a : ℂ) : (translation a).symm = translation (-a) := by
  ext z
  induction z using OnePoint.rec <;> rfl

/-- A global complex coordinate on the sphere with the finite point `a` omitted.
The parameter zero represents infinity. -/
noncomputable def omittedPointParam (a : ℂ) : OpenPartialHomeomorph ℂ 𝕊 :=
  invCoeOpenPartialHomeomorph.trans (translation a).toOpenPartialHomeomorph

@[simp] theorem omittedPointParam_source (a : ℂ) : (omittedPointParam a).source = univ := by
  simp [omittedPointParam, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph,
    coePartialEquiv]

@[simp] theorem omittedPointParam_apply (a z : ℂ) :
    omittedPointParam a z = translation a ((z : 𝕊)⁻¹) := rfl

@[simp] theorem omittedPointParam_symm_apply (a : ℂ) (z : 𝕊) :
    (omittedPointParam a).symm z = ((translation (-a) z)⁻¹).toComplex := by
  change ((translation a).symm z)⁻¹.toComplex = _
  rw [translation_symm_eq]

@[simp] theorem omittedPointParam_target (a : ℂ) : (omittedPointParam a).target = {(a : 𝕊)}ᶜ := by
  have ht : invCoeOpenPartialHomeomorph.target = {(0 : 𝕊)}ᶜ := by
    ext z
    change (True ∧ z⁻¹ ≠ ∞) ↔ z ≠ 0
    simp only [true_and, ne_eq, inv_eq_inf]
  ext z
  simp only [omittedPointParam, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, mem_inter_iff, mem_univ, true_and,
    mem_preimage, Homeomorph.toOpenPartialHomeomorph_symm_apply, translation_symm_eq]
  rw [ht]
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp only [translation_coe, mem_compl_singleton_iff, ne_eq, coe_eq_zero,
      coe_eq_coe, ← sub_eq_add_neg, sub_eq_zero]

theorem mAnalytic_omittedPointParam (a : ℂ) : ContMDiff I I ⊤ (omittedPointParam a) :=
  (mAnalytic_translation a).comp (mAnalytic_inv.comp mAnalytic_coe)

theorem mAnalyticAt_omittedPointParam_symm (a : ℂ) {z : 𝕊} (hz : z ≠ (a : 𝕊)) :
    ContMDiffAt I I ⊤ (omittedPointParam a).symm z := by
  have hn : (translation (-a) z)⁻¹ ≠ ∞ := by
    simp only [ne_eq, inv_eq_inf]
    induction z using OnePoint.rec with
    | infty => simp
    | coe z => simpa only [translation_coe, ne_eq, coe_eq_zero, coe_eq_coe,
        ← sub_eq_add_neg, sub_eq_zero] using hz
  change ContMDiffAt I I ⊤ (fun w => (omittedPointParam a).symm w) z
  simp_rw [omittedPointParam_symm_apply]
  exact
    (mAnalyticAt_toComplex' hn).comp z
      (mAnalytic_inv.contMDiffAt.comp z (mAnalytic_translation (-a)).contMDiffAt)

end RiemannSphere
