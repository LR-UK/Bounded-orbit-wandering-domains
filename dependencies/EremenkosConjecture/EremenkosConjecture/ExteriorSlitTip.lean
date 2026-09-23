import EremenkosConjecture.InvertedAttachedSegment
import FunctionTheory.Conformal.SlitTipCoordinates

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

theorem mem_invertedExterior_attached_segment_of_re_pos
    {X : Set ℂ} {a b : ℝ} {z : ℂ}
    (ha : 0 < a) (hb : 0 < b) (hmax : ∀ x ∈ X, x.re ≤ -a) (hz : 0 < z.re) :
    z ∈ FunctionTheory.invertedExterior (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b) ↔
      z.re < b⁻¹ ∨ z.im ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => by simpa [h] using hz
  have hn : 0 < normSq z := normSq_pos.mpr hz0
  have hpos : 0 < (z⁻¹).re := by rw [inv_re]; exact div_pos hz hn
  have hnotX : z⁻¹ ∉ X := by intro h; linarith [hmax _ h]
  by_cases him : z.im = 0
  · have heq : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
    have hinv : z⁻¹ = ((z.re)⁻¹ : ℝ) := by rw [heq]; simp
    have hsegment : z⁻¹ ∈ ((↑) : ℝ → ℂ) '' Icc (-a) b ↔ (z.re)⁻¹ ≤ b := by
      rw [hinv]
      constructor
      · rintro ⟨t, ht, he⟩
        have hte : t = z.re⁻¹ := ofReal_injective he
        simpa only [hte] using ht.2
      · intro h
        exact ⟨z.re⁻¹, ⟨by linarith [inv_pos.mpr hz], h⟩, rfl⟩
    simp only [FunctionTheory.invertedExterior, mem_ofPred_eq, hz0, false_or,
      mem_union, hnotX, hsegment, not_le, him, ne_eq, not_true_eq_false, or_false]
    exact lt_inv_comm₀ hb hz
  · have hnotS : z⁻¹ ∉ ((↑) : ℝ → ℂ) '' Icc (-a) b := by
      rintro ⟨t, _, he⟩
      have h := congrArg Complex.im he
      simp only [ofReal_im, inv_im] at h
      have hzneg : -z.im = 0 := (div_eq_zero_iff.mp h.symm).resolve_right hn.ne'
      exact him (neg_eq_zero.mp hzneg)
    simp only [FunctionTheory.invertedExterior, mem_ofPred_eq, hz0, false_or,
      mem_union, hnotX, hnotS, not_false_eq_true, ne_eq, him, or_true]

/-- The image of the free segment endpoint remains a straight slit tip in
the exterior coordinate. The radius is explicit and independent of X. -/
theorem local_slit_at_inverted_segment_tip
    {X : Set ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hmax : ∀ x ∈ X, x.re ≤ -a) :
    {z : ℂ | ((b⁻¹ : ℝ) : ℂ) - z ∈ FunctionTheory.invertedExterior
        (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)} ∩ ball (0 : ℂ) (b⁻¹ / 2) =
      slitPlane ∩ ball 0 (b⁻¹ / 2) := by
  ext z
  by_cases hz : z ∈ ball (0 : ℂ) (b⁻¹ / 2)
  · have hnorm : ‖z‖ < b⁻¹ / 2 := by simpa only [mem_ball, dist_zero_right] using hz
    have hre : 0 < (((b⁻¹ : ℝ) : ℂ) - z).re := by
      simp only [sub_re, ofReal_re]
      linarith [re_le_norm z, inv_pos.mpr hb]
    have hiff : b⁻¹ - z.re < b⁻¹ ↔ 0 < z.re := by constructor <;> intro h <;> linarith
    simpa only [mem_inter_iff, mem_ofPred_eq, hz, and_true, mem_slitPlane_iff,
      mem_invertedExterior_attached_segment_of_re_pos ha hb hmax hre,
      sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, neg_ne_zero]
      using or_congr hiff (Iff.rfl : z.im ≠ 0 ↔ z.im ≠ 0)
  · simp only [mem_inter_iff, hz, and_false]

/-- The exterior Riemann map, normalized at infinity, has a unique limit
at the free attached-segment endpoint. No regularity of the rest of X is assumed. -/
theorem exists_exterior_map_with_slit_tip_limit
    {X : Set ℂ} {a b : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (ha : 0 < a) (hb : 0 < b) (hleft : (-(a : ℂ)) ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ -a) :
    ∃ f : ℂ → ℂ,
      TauCeti.IsNormalizedRiemannMapOn f
        (FunctionTheory.invertedExterior (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)) 0 ∧
      ∃ ξ ∈ sphere (0 : ℂ) 1,
        Tendsto f (𝓝[FunctionTheory.invertedExterior
          (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)] ((b⁻¹ : ℝ) : ℂ)) (𝓝 ξ) := by
  obtain ⟨f, hf⟩ := exists_normalized_exterior_map_of_attached_segment
    hX hconn hfull ha hb hleft hmax
  refine ⟨f, hf, ?_⟩
  have hopen := FunctionTheory.isOpen_invertedExterior
    (hX.union ((isCompact_Icc : IsCompact (Icc (-a) b)).image continuous_ofReal))
  exact FunctionTheory.exists_boundary_limit_at_reflected_slit_tip hopen
    hf.differentiableOn hf.bijOn (half_pos (inv_pos.mpr hb))
    (local_slit_at_inverted_segment_tip ha hb hmax)

end EremenkosConjecture
