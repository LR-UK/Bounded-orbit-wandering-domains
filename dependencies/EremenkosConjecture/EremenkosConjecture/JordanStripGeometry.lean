import EremenkosConjecture.JordanSimplyConnected
import EremenkosConjecture.JordanBoundaryCompatibility
import FunctionTheory.Conformal.StripEndMap

/-! # Strip maps with simple connectivity derived from Jordan geometry

The bounded exponential image of a connected strip domain with Jordan
boundary is simply connected by Schoenflies. The negative logarithm transfers
this to the original domain. Thus the normalized strip-map theorem needs
connectedness, rather than a separate simple-connectivity hypothesis.
-/

open Set Complex Filter Asymptotics
open scoped Topology

namespace EremenkosConjecture

theorem isSimplyConnected_of_jordan_exponential_image
    {U : Set ℂ} {L : ℝ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hUS : U ⊆ FunctionTheory.standardHorizontalStrip)
    (hleft : ∀ z ∈ U, L ≤ z.re)
    (hJ : IsComplexJordanCurve (frontier (FunctionTheory.exponentialImage U))) :
    IsSimplyConnected U := by
  let Ω := FunctionTheory.exponentialImage U
  have hed : DifferentiableOn ℂ (fun z => exp (-z)) U :=
    (differentiable_exp.comp differentiable_id.neg).differentiableOn
  have hei : InjOn (fun z => exp (-z)) U :=
    FunctionTheory.bijOn_exp_neg_strip.injOn.mono hUS
  have hΩo : IsOpen Ω := TauCeti.isOpen_image_of_differentiableOn_of_injOn hUo hed hei
  have hΩc : IsConnected Ω := hUc.image _ hed.continuousOn
  have hΩb : Bornology.IsBounded Ω :=
    FunctionTheory.isBounded_exponentialImage_of_re_lower_bound hleft
  have hΩs := isSimplyConnected_bounded_jordan_domain hΩo hΩc hΩb hJ
  have hΩH : Ω ⊆ {w : ℂ | 0 < w.re} := by
    rintro w ⟨z, hz, rfl⟩
    exact FunctionTheory.re_exp_neg_pos_of_mem_strip (hUS hz)
  have hgd : DifferentiableOn ℂ (fun w => -log w) Ω :=
    FunctionTheory.differentiableOn_neg_log_rightHalfPlane.mono hΩH
  have hgi : InjOn (fun w => -log w) Ω :=
    FunctionTheory.bijOn_neg_log_rightHalfPlane.injOn.mono hΩH
  have himage : (fun w => -log w) '' Ω = U := by
    apply Subset.antisymm
    · rintro z ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      simpa only [FunctionTheory.neg_log_exp_neg_of_mem_strip (hUS hv)] using hv
    · intro z hz
      exact ⟨exp (-z), ⟨z, hz, rfl⟩,
        FunctionTheory.neg_log_exp_neg_of_mem_strip (hUS hz)⟩
  rw [← himage]
  exact TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn hΩo hΩs hgd hgi

theorem exists_normalized_strip_map_of_jordan_tail
    {U : Set ℂ} {z₀ : ℂ} {L R : ℝ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hUS : U ⊆ FunctionTheory.standardHorizontalStrip)
    (hleft : ∀ z ∈ U, L ≤ z.re)
    (htail : ∀ z ∈ FunctionTheory.standardHorizontalStrip, R < z.re → z ∈ U)
    (hJordan : IsComplexJordanCurve (frontier (FunctionTheory.exponentialImage U)))
    (hz₀ : z₀ ∈ U) :
    ∃ (φ : ℂ → ℂ) (ρ : ℝ), DifferentiableOn ℂ φ U ∧
      BijOn φ U FunctionTheory.standardHorizontalStrip ∧ φ z₀ = 0 ∧
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      Tendsto (fun z => (φ z).re) (comap Complex.re atTop ⊓ 𝓟 U) atTop :=
  FunctionTheory.exists_normalized_strip_map_of_jordan_exponential_image hUo
    (isSimplyConnected_of_jordan_exponential_image hUo hUc hUS hleft hJordan)
    hUS hleft htail hJordan.tauCeti hz₀

end EremenkosConjecture
