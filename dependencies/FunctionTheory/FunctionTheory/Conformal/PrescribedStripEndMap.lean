import FunctionTheory.Conformal.StripBoundaryConvergence

open Set Metric Complex Function Filter Asymptotics
open scoped Topology

namespace FunctionTheory

theorem bijOn_div_unit_disk {ξ : ℂ} (hξ : ‖ξ‖ = 1) :
    BijOn (fun w : ℂ => w / ξ) (ball 0 1) (ball 0 1) := by
  have hξ0 : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ]; norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    simpa only [mem_ball, dist_zero_right, norm_div, hξ, div_one] using hw
  · intro z hz w hw he
    exact (div_left_inj' hξ0).mp he
  · intro w hw
    refine ⟨w * ξ, ?_, mul_div_cancel_right₀ w hξ0⟩
    simpa only [mem_ball, dist_zero_right, norm_mul, hξ, mul_one] using hw

/-- A prescribed disk map on a straight-tail domain determines a right-end
normalization. The same map supplies the boundary limit and both exponential
strip-end estimates, so this normalization can be used in convergence arguments. -/
theorem exists_strip_end_normalization_of_disk_map
    {U : Set ℂ} {F : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hUo : IsOpen U) (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U)
    (hF : DifferentiableOn ℂ F U) (hFb : BijOn F U (ball 0 1))
    (hF0 : F z₀ = 0) :
    ∃ ξ : ℂ, ∃ ρ : ℝ, ‖ξ‖ = 1 ∧
      Tendsto (fun w => F (-log w)) (𝓝[exponentialImage U] 0) (𝓝 ξ) ∧
      let φ := fun z => discToHorizontalStrip (F z / ξ)
      DifferentiableOn ℂ φ U ∧ BijOn φ U standardHorizontalStrip ∧ φ z₀ = 0 ∧
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      Tendsto (fun z => (φ z).re) (comap Complex.re atTop ⊓ 𝓟 U) atTop := by
  have hΩo : IsOpen (exponentialImage U) :=
    TauCeti.isOpen_image_of_differentiableOn_of_injOn hUo
      ((differentiable_exp.comp differentiable_id.neg).differentiableOn)
      (bijOn_exp_neg_strip.injOn.mono hUS)
  have hlog : DifferentiableOn ℂ (fun w => -log w) (exponentialImage U) := by
    apply differentiableOn_neg_log_rightHalfPlane.mono
    rintro w ⟨z, hz, rfl⟩
    exact re_exp_neg_pos_of_mem_strip (hUS hz)
  have hlogb := bijOn_neg_log_exponentialImage hUS
  obtain ⟨ξ, ψ, a, hξ, hlim, hψ, hψ0, ha, hψd, heq⟩ :=
    exists_positive_cayley_coordinate_of_disk_map_at_straight_boundary
      hΩo (hF.comp hlog hlogb.mapsTo) (hFb.comp hlogb) (Real.exp_pos _)
      (exponentialImage_agrees_with_halfplane_at_zero hUS htail)
  let φ := fun z => discToHorizontalStrip (F z / ξ)
  have hgb := (bijOn_div_unit_disk hξ).comp hFb
  have hφd : DifferentiableOn ℂ φ U :=
    differentiableOn_discToHorizontalStrip.comp (hF.div_const ξ) hgb.mapsTo
  have hφb : BijOn φ U standardHorizontalStrip :=
    bijOn_discToHorizontalStrip.comp hgb
  have hφ0 : φ z₀ = 0 := by simp only [φ, hF0, zero_div, discToHorizontalStrip_zero]
  have hψeq : EqOn (fun z => ψ (exp (-z))) (fun z => exp (-φ z)) U := by
    intro z hz
    have he := heq (show exp (-z) ∈ exponentialImage U from ⟨z, hz, rfl⟩)
    simp only [Function.comp_apply, neg_log_exp_neg_of_mem_strip (hUS hz)] at he
    exact he.trans (exp_neg_discToHorizontalStrip (hgb.mapsTo hz)).symm
  obtain ⟨ρ, hd, hv⟩ := stripEnd_estimates_of_reflected_map hUo hφd hψeq
    (fun z hz => hUS hz) (fun z hz => hφb.mapsTo hz) hψ hψ0 ha hψd
  exact ⟨ξ, ρ, hξ, hlim, hφd, hφb, hφ0, hd, hv,
    tendsto_re_atTop_of_strip_translation_asymptotic hv⟩

end FunctionTheory
