/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import EremenkoLyubichConstant.Tract
import EremenkoLyubichConstant.UniversalCover
import Ray.Dynamics.Multiple
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible

/-!
# Logarithmic transforms from universal covering maps

This file supplies the analytic bridge which is usually left implicit in the definition of a
logarithmic tract.  A based equivalence of universal covers is initially only a homeomorphism.
The commuting exponential diagram makes its forward map holomorphic, and injectivity plus the
complex inverse-function theorem makes its inverse holomorphic.
-/

open Filter Function Set
open scoped Topology

namespace EremenkoLyubichConstant

noncomputable section

/-- The exterior disk naturally covered by `exp` on `rightHalfPlane ρ`. -/
def exponentialExterior (ρ : ℝ) : Set ℂ :=
  {w | Real.exp ρ < ‖w‖}

/-- The exponential preimage of the exterior of the circle of radius `exp ρ`
is the right half-plane with boundary real part `ρ`. -/
lemma exp_preimage_exponentialExterior (ρ : ℝ) :
    Complex.exp ⁻¹' exponentialExterior ρ = rightHalfPlane ρ := by
  ext z
  simp only [Set.mem_preimage, exponentialExterior, Set.mem_ofPred_eq, Complex.norm_exp,
    rightHalfPlane]
  exact Real.exp_lt_exp

/-- The exponential restricted to a right half-plane is a covering of the corresponding
exterior disk. -/
theorem isCoveringMap_exp_rightHalfPlane (ρ : ℝ) :
    IsCoveringMap fun z : rightHalfPlane ρ ↦
      (⟨Complex.exp z, by
        simpa only [exponentialExterior, Set.mem_ofPred_eq, Complex.norm_exp,
          rightHalfPlane, Set.mem_ofPred_eq] using Real.exp_lt_exp.mpr z.2⟩ : exponentialExterior ρ) := by
  have hsub : exponentialExterior ρ ⊆ ({0}ᶜ : Set ℂ) := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    change Real.exp ρ < ‖w‖ at hw
    rw [h, norm_zero] at hw
    exact (not_lt_of_ge (Real.exp_pos ρ).le) hw
  have hcov := (Complex.isCoveringMapOn_exp.mono hsub).isCoveringMap_restrictPreimage
  have heq := exp_preimage_exponentialExterior ρ
  convert hcov.comp_homeomorph (.setCongr heq.symm) using 1
  funext z
  apply Subtype.ext
  rfl

private noncomputable def extendSubtype {s : Set ℂ} (f : s → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ s then f ⟨z, hz⟩ else 0

/-- A homeomorphism of an open plane domain with a right half-plane, commuting with `exp`,
produces the conformal equivalence used throughout the paper. -/
theorem tractEquiv_of_homeomorph
    {T : Set ℂ} {ρ : ℝ} {g : ℂ → ℂ}
    (hT : IsOpen T) (hg : DifferentiableOn ℂ g T)
    (h : T ≃ₜ (rightHalfPlane ρ))
    (hcomm : ∀ z : T, Complex.exp (h z) = g z) :
    ∃ e : TractEquiv T ρ,
      (∀ z ∈ T, Complex.exp (e.toFun z) = g z) := by
  let F : ℂ → ℂ := extendSubtype (fun z ↦ (h z : ℂ))
  let G : ℂ → ℂ := extendSubtype (fun w ↦ (h.symm w : ℂ))
  have hF_apply {z : ℂ} (hz : z ∈ T) : F z = h ⟨z, hz⟩ := by
    simp [F, extendSubtype, hz]
  have hG_apply {w : ℂ} (hw : w ∈ rightHalfPlane ρ) : G w = h.symm ⟨w, hw⟩ := by
    simp [G, extendSubtype, hw]
  have hFcont : ContinuousOn F T := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : T.domRestrict F = fun z ↦ (h z : ℂ) := by
      funext z
      exact hF_apply z.2
    rw [heq]
    exact continuous_subtype_val.comp h.continuous
  have hGcont : ContinuousOn G (rightHalfPlane ρ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (rightHalfPlane ρ).domRestrict G = fun w ↦ (h.symm w : ℂ) := by
      funext w
      exact hG_apply w.2
    rw [heq]
    exact continuous_subtype_val.comp h.symm.continuous
  have hFmaps : MapsTo F T (rightHalfPlane ρ) := by
    intro z hz
    rw [hF_apply hz]
    exact (h ⟨z, hz⟩).2
  have hGmaps : MapsTo G (rightHalfPlane ρ) T := by
    intro w hw
    rw [hG_apply hw]
    exact (h.symm ⟨w, hw⟩).2
  have hleft : Set.LeftInvOn G F T := by
    intro z hz
    rw [hF_apply hz, hG_apply (h ⟨z, hz⟩).2]
    exact congrArg Subtype.val (h.symm_apply_apply ⟨z, hz⟩)
  have hright : Set.RightInvOn G F (rightHalfPlane ρ) := by
    intro w hw
    rw [hG_apply hw, hF_apply (h.symm ⟨w, hw⟩).2]
    exact congrArg Subtype.val (h.apply_symm_apply ⟨w, hw⟩)
  have hcommF : Set.EqOn (Complex.exp ∘ F) g T := by
    intro z hz
    rw [Function.comp_apply, hF_apply hz]
    exact hcomm ⟨z, hz⟩
  have hFdiff : DifferentiableOn ℂ F T :=
    differentiableOn_of_continuousOn_exp_eq hT hFcont hg hcommF
  have hFinj : Set.InjOn F T := by
    intro z hz w hw heq
    have hsub : h ⟨z, hz⟩ = h ⟨w, hw⟩ := by
      apply Subtype.ext
      simpa [hF_apply hz, hF_apply hw] using heq
    exact congrArg Subtype.val (h.injective hsub)
  have hGdiff : DifferentiableOn ℂ G (rightHalfPlane ρ) := by
    intro w hw
    have hz : G w ∈ T := hGmaps hw
    have hFd : DifferentiableAt ℂ F (G w) :=
      hFdiff.differentiableAt (hT.mem_nhds hz)
    have hdne : deriv F (G w) ≠ 0 :=
      hFinj.deriv_ne_zero hT hz ((hFdiff.analyticOnNhd hT) (G w) hz)
    have hGc : ContinuousAt G w :=
      hGcont.continuousAt (isOpen_rightHalfPlane ρ |>.mem_nhds hw)
    have hloc : ∀ᶠ y in nhds w, F (G y) = y :=
      (isOpen_rightHalfPlane ρ |>.eventually_mem hw).mono fun y hy ↦ hright hy
    exact (hFd.hasDerivAt.of_local_left_inverse hGc hdne hloc).differentiableAt.differentiableWithinAt
  let e : TractEquiv T ρ :=
    { toFun := F
      invFun := G
      isOpen_source := hT
      toFun_maps := hFmaps
      invFun_maps := hGmaps
      left_inv := hleft
      right_inv := hright
      differentiableOn_toFun := hFdiff
      differentiableOn_invFun := hGdiff }
  exact ⟨e, hcommF⟩

/-- Every exterior covering admits a based lift of the standard exponential cover.
This does not assume that a preimage component is simply connected. Injectivity of this
lift is the additional issue needed to identify that component as a universal cover. -/
theorem exists_inverse_exp_lift
    {f : ℂ → ℂ} {ρ : ℝ}
    (hcover : IsCoveringMapOn f (exponentialExterior ρ))
    {z₀ : ℂ} (hz₀ : Real.exp ρ < ‖f z₀‖) :
    ∃ G : C(rightHalfPlane ρ, ℂ),
      (∀ w, f (G w) = Complex.exp w) ∧
      ∃ w₀ : rightHalfPlane ρ, G w₀ = z₀ := by
  have hHconv : Convex ℝ (rightHalfPlane ρ) := by
    simpa [rightHalfPlane] using convex_halfSpace_re_gt ρ
  let : ContractibleSpace (rightHalfPlane ρ) :=
    hHconv.contractibleSpace ⟨(ρ + 1 : ℝ), by simp [rightHalfPlane]⟩
  let : LocallyPathConnectedSpace (rightHalfPlane ρ) :=
    (isOpen_rightHalfPlane ρ).locallyPathConnectedSpace
  have hn : f z₀ ≠ 0 := norm_pos_iff.mp ((Real.exp_pos ρ).trans hz₀)
  have hw : Complex.log (f z₀) ∈ rightHalfPlane ρ := by
    change ρ < (Complex.log (f z₀)).re
    rw [Complex.log_re, ← Real.exp_lt_exp]
    simpa [Real.exp_log (norm_pos_iff.mpr hn)] using hz₀
  let w₀ : rightHalfPlane ρ := ⟨Complex.log (f z₀), hw⟩
  let q : C(rightHalfPlane ρ, ℂ) := ⟨fun w ↦ Complex.exp w, by fun_prop⟩
  have hbase : f z₀ = q w₀ := (Complex.exp_log hn).symm
  obtain ⟨G, ⟨hG₀, hG⟩, _⟩ := hcover.existsUnique_continuousMap_lifts q hbase
    (fun w ↦ by
      change Real.exp ρ < ‖Complex.exp (w : ℂ)‖
      rw [Complex.norm_exp]
      exact Real.exp_lt_exp.mpr w.2)
  exact ⟨G, fun w ↦ congrFun hG w, w₀, hG₀⟩

/-- A simply connected covering of an exterior disk is conformally equivalent to the standard
exponential covering.  This is the formal universal-cover construction of a logarithmic
transform. -/
theorem exists_tractEquiv_of_isCoveringMap
    {T : Set ℂ} {ρ : ℝ} {g : ℂ → ℂ}
    (hT : IsOpen T) (hTs : IsSimplyConnected T)
    (hg : DifferentiableOn ℂ g T)
    (hmaps : MapsTo g T (exponentialExterior ρ))
    (hcover : IsCoveringMap fun z : T ↦
      (⟨g z, hmaps z.2⟩ : exponentialExterior ρ)) :
    ∃ e : TractEquiv T ρ,
      ∀ z ∈ T, Complex.exp (e.toFun z) = g z := by
  let : SimplyConnectedSpace T := hTs.simplyConnectedSpace
  let : LocallyPathConnectedSpace T := hT.locallyPathConnectedSpace
  have hHconv : Convex ℝ (rightHalfPlane ρ) := by
    simpa [rightHalfPlane] using convex_halfSpace_re_gt ρ
  let : ContractibleSpace (rightHalfPlane ρ) :=
    hHconv.contractibleSpace ⟨(ρ + 1 : ℝ), by simp [rightHalfPlane]⟩
  let : LocallyPathConnectedSpace (rightHalfPlane ρ) :=
    (isOpen_rightHalfPlane ρ).locallyPathConnectedSpace
  let z₀ : T := ⟨hTs.nonempty.some, hTs.nonempty.some_mem⟩
  have hg₀norm : Real.exp ρ < ‖g z₀‖ := hmaps z₀.2
  have hg₀ne : g z₀ ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos ρ).trans hg₀norm)
  have hw₀ : Complex.log (g z₀) ∈ rightHalfPlane ρ := by
    change ρ < (Complex.log (g z₀)).re
    rw [Complex.log_re, ← Real.exp_lt_exp]
    simpa [Real.exp_log (norm_pos_iff.mpr hg₀ne)] using hg₀norm
  let w₀ : rightHalfPlane ρ := ⟨Complex.log (g z₀), hw₀⟩
  have hbase :
      (⟨g z₀, hmaps z₀.2⟩ : exponentialExterior ρ) =
        ⟨Complex.exp w₀, by
          simpa only [exponentialExterior, Set.mem_ofPred_eq, Complex.norm_exp,
            rightHalfPlane, Set.mem_ofPred_eq] using Real.exp_lt_exp.mpr w₀.2⟩ := by
    apply Subtype.ext
    exact (Complex.exp_log hg₀ne).symm
  obtain ⟨h, _hz₀, hcomm⟩ := exists_homeomorph_of_isCoveringMap
    hcover (isCoveringMap_exp_rightHalfPlane ρ) z₀ w₀ hbase
  apply tractEquiv_of_homeomorph hT hg h
  intro z
  have hz := congrFun hcomm z
  exact congrArg Subtype.val hz

end

end EremenkoLyubichConstant
