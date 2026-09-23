import FunctionTheory.Conformal.StripEndMap
import FunctionTheory.Conformal.StraightBoundaryDirect

open Set Metric Complex Function Filter Asymptotics
open scoped Topology

namespace FunctionTheory

/-- Local straight-boundary correspondence suffices for the normalized
strip map and both exponential end estimates. The remaining boundary need
not be Jordan or locally connected. -/
theorem exists_normalized_strip_map_of_straight_tail
    {U : Set ℂ} {z₀ : ℂ} {R : ℝ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U)
    (hz₀ : z₀ ∈ U) :
    ∃ (φ : ℂ → ℂ) (ρ : ℝ), DifferentiableOn ℂ φ U ∧
      BijOn φ U standardHorizontalStrip ∧ φ z₀ = 0 ∧
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      Tendsto (fun z => (φ z).re) (comap Complex.re atTop ⊓ 𝓟 U) atTop := by
  let Ω := exponentialImage U
  have hed : DifferentiableOn ℂ (fun z => exp (-z)) U :=
    (differentiable_exp.comp differentiable_id.neg).differentiableOn
  have hei : InjOn (fun z => exp (-z)) U := bijOn_exp_neg_strip.injOn.mono hUS
  have hebij : BijOn (fun z => exp (-z)) U Ω := hei.bijOn_image
  have hΩo : IsOpen Ω := TauCeti.isOpen_image_of_differentiableOn_of_injOn hUo hed hei
  have hΩc : IsSimplyConnected Ω :=
    TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn hUo hUc hed hei
  obtain ⟨g, ψ, a, hgd, hgbij, hg0, hψa, hψ0, ha, hψd, hψeq⟩ :=
    exists_disk_map_with_positive_cayley_coordinate_at_straight_boundary
      hΩo hΩc (hebij.mapsTo hz₀) (Real.exp_pos _)
      (exponentialImage_agrees_with_halfplane_at_zero hUS htail)
  let φ : ℂ → ℂ := fun z => discToHorizontalStrip (g (exp (-z)))
  have hφd : DifferentiableOn ℂ φ U :=
    differentiableOn_discToHorizontalStrip.comp (hgd.comp hed hebij.mapsTo)
      (hgbij.mapsTo.comp hebij.mapsTo)
  have hφbij : BijOn φ U standardHorizontalStrip :=
    bijOn_discToHorizontalStrip.comp (hgbij.comp hebij)
  have hφ0 : φ z₀ = 0 := by simp only [φ, hg0, discToHorizontalStrip_zero]
  have heq : EqOn (fun z => ψ (exp (-z))) (fun z => exp (-φ z)) U := by
    intro z hz
    exact (hψeq (hebij.mapsTo hz)).trans
      (exp_neg_discToHorizontalStrip (hgbij.mapsTo (hebij.mapsTo hz))).symm
  obtain ⟨ρ, hd, hv⟩ := stripEnd_estimates_of_reflected_map hUo hφd heq
    (fun z hz => hUS hz) (fun z hz => hφbij.mapsTo hz) hψa hψ0 ha hψd
  exact ⟨φ, ρ, hφd, hφbij, hφ0, hd, hv,
    tendsto_re_atTop_of_strip_translation_asymptotic hv⟩

end FunctionTheory
