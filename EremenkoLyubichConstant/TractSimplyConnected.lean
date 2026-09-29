module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.ExteriorCoverClassification
public import EremenkoLyubichConstant.HolomorphicLift
public import EremenkoLyubichConstant.Puncture
public import EremenkoLyubichConstant.TractCovering

@[expose] public section

open Set Function Metric
open scoped Topology

namespace EremenkoLyubichConstant

open ExteriorPowerCover FunctionTheory

/-- A power-cover model for an entire exterior covering omitting a disk forces polynomiality. -/
theorem isPolynomialFunction_of_power_cover_equiv
    {f : ℂ → ℂ} {T : Set ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hc : IsCoveringMapOn f (exponentialExterior ρ))
    (hm : MapsTo f T (exponentialExterior ρ))
    (havoid : ∃ b : ℂ, ∃ ε > 0, ∀ z ∈ T, ε ≤ ‖z - b‖)
    (d : ℕ) (hd : 0 < d) (h : T ≃ₜ exponentialExterior (ρ / d))
    (hcomm : powerCover ρ d hd ∘ h = fun z : T ↦ ⟨f z, hm z.2⟩) :
    IsPolynomialFunction f := by
  classical
  obtain ⟨b, ε, hε, havoid⟩ := havoid
  let r := Real.exp (-(ρ / d))
  let V : Set ℂ := ball 0 r \ {0}
  let W := exponentialExterior (ρ / d)
  have hr : 0 < r := Real.exp_pos _
  have hV : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hinv (z : ℂ) (hz : z ∈ V) : z⁻¹ ∈ W := by
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz.2
    have hz' : ‖z‖ < (Real.exp (ρ / d))⁻¹ := by
      simpa only [V, mem_sdiff, mem_ball_zero_iff, r, Real.exp_neg] using hz.1
    change Real.exp (ρ / d) < ‖z⁻¹‖
    rw [norm_inv, inv_eq_one_div, lt_div_iff₀ hn]
    have hh := (lt_div_iff₀ (Real.exp_pos (ρ / d))).mp
      (show ‖z‖ < 1 / Real.exp (ρ / d) by simpa only [one_div] using hz')
    simpa only [mul_comm] using hh
  let φ : ℂ → ℂ := fun z ↦ if hz : z⁻¹ ∈ W then (h.symm ⟨z⁻¹, hz⟩ : ℂ) else 0
  have hφ (z : ℂ) (hz : z ∈ V) : φ z = (h.symm ⟨z⁻¹, hinv z hz⟩ : ℂ) := by
    simp only [φ, dite_eq_left (hinv z hz)]
  have hφmem (z : ℂ) (hz : z ∈ V) : φ z ∈ T := by
    rw [hφ z hz]
    exact (h.symm ⟨z⁻¹, hinv z hz⟩).2
  have hφcont : ContinuousOn φ V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hci : Continuous (fun z : V ↦ (⟨(z : ℂ)⁻¹, hinv z z.2⟩ : W)) :=
      (continuous_subtype_val.inv₀ fun z : V ↦ z.2.2).subtype_mk _
    exact (continuous_subtype_val.comp (h.symm.continuous.comp hci)).congr
      (fun z ↦ (hφ z z.2).symm)
  have heq (z : ℂ) (hz : z ∈ V) : f (φ z) = (z⁻¹) ^ d := by
    rw [hφ z hz]
    have hh := congrArg Subtype.val (congrFun hcomm (h.symm ⟨z⁻¹, hinv z hz⟩))
    simpa only [comp_apply, h.apply_symm_apply, powerCover] using hh.symm
  have hdiff : DifferentiableOn ℂ φ V :=
    differentiableOn_of_continuousOn_covering_lift hf hc hV hφcont
      (fun z hz ↦ hm (hφmem z hz))
      (fun z hz ↦ (((differentiableAt_id (𝕜 := ℂ) (x := z)).inv
        (show z ≠ 0 from hz.2)).pow d).differentiableWithinAt)
      (fun z hz ↦ heq z hz)
  have hinj : InjOn φ V := by
    intro z hz w hw he
    rw [hφ z hz, hφ w hw] at he
    have hh := h.symm.injective (Subtype.ext he)
    exact inv_injective (congrArg Subtype.val hh)
  apply isPolynomialFunction_of_finite_tract_model_omitting_ball hf hr hdiff hinj hε
    (fun z hz ↦ havoid (φ z) (hφmem z hz)) (a := 1) one_ne_zero hd
  intro z hz
  simpa only [one_mul] using heq z hz

/-- Every connected exterior covering of a transcendental entire function is conformally
equivalent to the exponential half-plane cover. No source normalization is required. -/
theorem exists_tractEquiv_of_transcendental_covering
    {f : ℂ → ℂ} {T : Set ℂ} {ρ : ℝ}
    (hf : IsTranscendentalEntire f) (hc : IsCoveringMapOn f (exponentialExterior ρ))
    (hT : IsOpen T) [PathConnectedSpace T]
    (hm : MapsTo f T (exponentialExterior ρ))
    (hcover : IsCoveringMap fun z : T ↦ (⟨f z, hm z.2⟩ : exponentialExterior ρ)) :
    ∃ e : TractEquiv T ρ, ∀ z ∈ T, Complex.exp (e.toFun z) = f z := by
  let : LocallyPathConnectedSpace T := hT.locallyPathConnectedSpace
  obtain ⟨b, ε, hε, ha⟩ := hf.exterior_omits_ball (Real.exp_pos ρ)
  have havoid : ∃ b : ℂ, ∃ ε > 0, ∀ z ∈ T, ε ≤ ‖z - b‖ :=
    ⟨b, ε, hε, fun z hz ↦ ha z (hm hz)⟩
  let z₀ : T := Classical.choice inferInstance
  rcases exterior_covering_dichotomy hcover z₀ with hzero | ⟨d, hd, h, hh⟩
  · exact exists_tractEquiv_of_trivial_covering_subgroup hT hf.1.differentiableOn hm hcover z₀ hzero
  · exact False.elim (hf.2 (isPolynomialFunction_of_power_cover_equiv hf.1 hc hm havoid d hd h hh))

/-- A conformal tract chart induces a homeomorphism of the underlying domains. -/
noncomputable def TractEquiv.toHomeomorph {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ) :
    T ≃ₜ rightHalfPlane ρ where
  toFun z := ⟨e.toFun z, e.toFun_maps z.2⟩
  invFun z := ⟨e.invFun z, e.invFun_maps z.2⟩
  left_inv z := Subtype.ext (e.left_inv z.2)
  right_inv z := Subtype.ext (e.right_inv z.2)
  continuous_toFun := (e.differentiableOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val fun z ↦ z.2).subtype_mk _
  continuous_invFun := (e.differentiableOn_invFun.continuousOn.comp_continuous
    continuous_subtype_val fun z ↦ z.2).subtype_mk _

/-- A domain admitting a conformal half-plane chart is simply connected. -/
theorem TractEquiv.isSimplyConnected {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ) :
    IsSimplyConnected T := by
  let : ContractibleSpace (rightHalfPlane ρ) :=
    (show Convex ℝ (rightHalfPlane ρ) from by
      simpa [rightHalfPlane] using convex_halfSpace_re_gt ρ).contractibleSpace
        ⟨(ρ + 1 : ℝ), by simp [rightHalfPlane]⟩
  let : ContractibleSpace T := e.toHomeomorph.contractibleSpace
  exact (inferInstance : SimplyConnectedSpace T)

end EremenkoLyubichConstant
