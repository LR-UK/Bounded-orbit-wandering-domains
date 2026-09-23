import EremenkosConjecture.ExteriorSlitTip
import FunctionTheory.Conformal.SlitTipInverseCoordinates

open Set Metric Complex Filter Function
open scoped Topology

namespace EremenkosConjecture

/-- The normalized exterior map and its inverse extend continuously at the
same free attached-segment endpoint. This is the local correspondence used
to draw a surrounding curve through that endpoint. -/
theorem exists_exterior_map_with_corresponding_slit_tip_limits
    {X : Set ℂ} {a b : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (ha : 0 < a) (hb : 0 < b) (hleft : (-(a : ℂ)) ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ -a) :
    ∃ f : ℂ → ℂ,
      TauCeti.IsNormalizedRiemannMapOn f
        (FunctionTheory.invertedExterior (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)) 0 ∧
      ∃ ξ ∈ sphere (0 : ℂ) 1,
        Tendsto f (𝓝[FunctionTheory.invertedExterior
          (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)] ((b⁻¹ : ℝ) : ℂ)) (𝓝 ξ) ∧
        Tendsto (invFunOn f (FunctionTheory.invertedExterior
          (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)))
          (𝓝[ball 0 1] ξ) (𝓝 ((b⁻¹ : ℝ) : ℂ)) := by
  obtain ⟨f, hf⟩ := exists_normalized_exterior_map_of_attached_segment
    hX hconn hfull ha hb hleft hmax
  refine ⟨f, hf, ?_⟩
  have hopen := FunctionTheory.isOpen_invertedExterior
    (hX.union ((isCompact_Icc : IsCompact (Icc (-a) b)).image continuous_ofReal))
  exact FunctionTheory.exists_corresponding_boundary_limits_at_reflected_slit_tip hopen
    hf.differentiableOn hf.bijOn (half_pos (inv_pos.mpr hb))
    (local_slit_at_inverted_segment_tip ha hb hmax)

end EremenkosConjecture
