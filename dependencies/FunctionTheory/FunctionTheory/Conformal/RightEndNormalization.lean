import FunctionTheory.Conformal.PrescribedStripEndMap
import FunctionTheory.Conformal.HalfPlaneKernel

open Set Metric Complex Function Filter Asymptotics
open scoped Topology

namespace FunctionTheory

/-- A disk map fixing an interior base point and sending the right end to `1`.
The endpoint limit is expressed in the coordinate `w = exp (-z)`. -/
structure IsRightEndRiemannMapOn (f : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ) : Prop where
  base_mem : z₀ ∈ U
  differentiableOn : DifferentiableOn ℂ f U
  bijOn : BijOn f U (ball 0 1)
  map_base : f z₀ = 0
  end_limit : Tendsto (fun w => f (-log w)) (𝓝[exponentialImage U] 0) (𝓝 1)

theorem zero_mem_closure_exponentialImage_of_straight_tail
    {U : Set ℂ} {R : ℝ} (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U) :
    (0 : ℂ) ∈ closure (exponentialImage U) := by
  apply closure_mono (show ball (0 : ℂ) (Real.exp (-R)) ∩ {z : ℂ | 0 < z.re} ⊆
      exponentialImage U from fun z hz =>
        (exponentialImage_agrees_with_halfplane_at_zero hUS htail z hz.1).mpr hz.2)
  exact mem_closure_right_half_ball (by simpa using Real.exp_pos (-R)) (by simp)

theorem IsRightEndRiemannMapOn.eqOn
    {U : Set ℂ} {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hg : IsRightEndRiemannMapOn g U z₀) (hf : IsRightEndRiemannMapOn f U z₀)
    (hU : IsOpen U) (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U) : EqOn g f U := by
  obtain ⟨u, hu⟩ := TauCeti.exists_eqOn_const_mul_of_image_eq_ball_of_apply_eq_zero
    hU hf.differentiableOn hg.differentiableOn hf.bijOn.injOn hg.bijOn.injOn
    hf.bijOn.image_eq hg.bijOn.image_eq hf.base_mem hf.map_base hg.map_base
  have : (𝓝[exponentialImage U] (0 : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (zero_mem_closure_exponentialImage_of_straight_tail hUS htail)
  have he : (fun w => (u : ℂ) * f (-log w)) =ᶠ[𝓝[exponentialImage U] 0]
      (fun w => g (-log w)) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hu ((bijOn_neg_log_exponentialImage hUS).mapsTo hw)).symm
  have hl : Tendsto (fun w => g (-log w)) (𝓝[exponentialImage U] 0) (𝓝 (u : ℂ)) := by
    simpa only [mul_one] using (tendsto_const_nhds.mul hf.end_limit).congr' he
  have hu1 : (u : ℂ) = 1 := tendsto_nhds_unique hl hg.end_limit
  intro z hz
  simpa only [hu1, one_mul] using hu hz

theorem exists_rightEndRiemannMapOn
    {U : Set ℂ} {z₀ : ℂ} {R : ℝ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U) (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, IsRightEndRiemannMapOn f U z₀ := by
  have hproper : U ≠ univ := by
    intro he
    have h := hUS (he ▸ mem_univ ((Real.pi : ℂ) * I))
    change |((Real.pi : ℂ) * I).im| < Real.pi / 2 at h
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_pos]
  obtain ⟨F, hF⟩ := TauCeti.exists_isNormalizedRiemannMapOn hUo hUc hproper hz₀
  obtain ⟨ξ, ρ, hξ, hlim, _⟩ := exists_strip_end_normalization_of_disk_map
    hUo hUS htail hF.differentiableOn hF.bijOn hF.map_base
  have hξ0 : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ]; norm_num)
  refine ⟨fun z => F z / ξ, hz₀, hF.differentiableOn.div_const ξ,
    (bijOn_div_unit_disk hξ).comp hF.bijOn, by simp [hF.map_base], ?_⟩
  simpa only [div_self hξ0] using hlim.div_const ξ

theorem IsRightEndRiemannMapOn.strip_end_estimates
    {U : Set ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : IsRightEndRiemannMapOn f U z₀) (hUo : IsOpen U)
    (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U) :
    let φ := fun z => discToHorizontalStrip (f z)
    DifferentiableOn ℂ φ U ∧ BijOn φ U standardHorizontalStrip ∧ φ z₀ = 0 ∧
    ∃ ρ : ℝ,
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      Tendsto (fun z => (φ z).re) (comap Complex.re atTop ⊓ 𝓟 U) atTop := by
  obtain ⟨ξ, ρ, _, hlim, hφ⟩ := exists_strip_end_normalization_of_disk_map
    hUo hUS htail hf.differentiableOn hf.bijOn hf.map_base
  have : (𝓝[exponentialImage U] (0 : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (zero_mem_closure_exponentialImage_of_straight_tail hUS htail)
  have hξ : ξ = 1 := tendsto_nhds_unique hlim hf.end_limit
  simp only [hξ, div_one] at hφ
  exact ⟨hφ.1, hφ.2.1, hφ.2.2.1, ρ, hφ.2.2.2⟩

end FunctionTheory
