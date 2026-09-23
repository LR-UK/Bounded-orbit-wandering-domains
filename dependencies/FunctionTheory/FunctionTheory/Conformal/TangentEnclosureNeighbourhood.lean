import FunctionTheory.Conformal.InvertedDomain
import FunctionTheory.Conformal.TangentDiskGeometry

open Set Metric Complex Function

namespace FunctionTheory

/-- Tangent disks exhaust the unit disk as their centres tend to zero.
Transporting this exhaustion through an exterior map gives compact enclosures
inside any prescribed open neighbourhood of the removed set. -/
theorem tangent_enclosures_eventually_subset_neighbourhood
    {E : Set ℂ} {f G : ℂ → ℂ} {ξ : ℂ}
    (h0E : (0 : ℂ) ∈ E) (hξ : ‖ξ‖ = 1)
    (hfc : ContinuousOn f (invertedExterior E))
    (hfD : MapsTo f (invertedExterior E) (ball 0 1))
    (hGF : LeftInvOn G f (invertedExterior E))
    {N : Set ℂ} (hN : IsOpen N) (hEN : E ⊆ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      invertedExterior (G '' ball ((t : ℂ) * ξ) (1 - t)) ⊆ N := by
  let L := invertedExterior N
  have hLc : IsCompact L := isCompact_invertedExterior_of_isOpen hN (hEN h0E)
  have h0L : (0 : ℂ) ∈ L := Or.inl rfl
  have hLU : L ⊆ invertedExterior E := by
    rintro w (hw | hw)
    · exact Or.inl hw
    · exact Or.inr (fun he => hw (hEN he))
  have him : IsCompact (f '' L) := hLc.image_of_continuousOn (hfc.mono hLU)
  obtain ⟨a, ha, hmax⟩ := him.exists_isMaxOn ⟨f 0, mem_image_of_mem f h0L⟩
    continuous_norm.continuousOn
  have haD : a ∈ ball (0 : ℂ) 1 := by
    obtain ⟨w, hw, rfl⟩ := ha
    exact hfD (hLU hw)
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp haD
  refine ⟨(1 - ‖a‖) / 2, by linarith, ?_⟩
  intro t ht htd z hz
  have hLV : L ⊆ G '' ball ((t : ℂ) * ξ) (1 - t) := by
    intro w hw
    refine ⟨f w, ?_, hGF (hLU hw)⟩
    have hnorm : ‖f w‖ ≤ ‖a‖ := hmax (mem_image_of_mem f hw)
    have hcent : dist (0 : ℂ) ((t : ℂ) * ξ) = t := by
      simp [dist_zero_left, hξ, abs_of_pos ht]
    have htri := dist_triangle (f w) 0 ((t : ℂ) * ξ)
    rw [dist_zero_right, hcent] at htri
    rw [mem_ball]
    linarith
  by_contra hzN
  have hz0 : z ≠ 0 := fun he => hzN (he ▸ hEN h0E)
  exact (hz.resolve_left hz0) (hLV (Or.inr (by simpa using hzN)))

end FunctionTheory
