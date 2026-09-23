import EremenkosConjecture.ExteriorSlitTip
import EremenkosConjecture.JordanBoundaryEquivalence
import EremenkosConjecture.JordanCompactRecognition
import FunctionTheory.Conformal.SlitTipJordanCurve
import FunctionTheory.Conformal.TangentEnclosure
import FunctionTheory.Conformal.TangentEnclosureNeighbourhood

open Set Metric Complex Function

namespace EremenkosConjecture

/-- The author's exterior-map construction: in any neighbourhood of a full
continuum and a short rightmost segment, there is a full Jordan neighbourhood
of the continuum whose boundary passes through the free segment endpoint.
The rest of the segment is in its interior. -/
theorem exists_jordan_enclosure_through_attached_segment_tip
    {X N : Set ℂ} {a b : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (ha : 0 < a) (hb : 0 < b) (hleft : (-(a : ℂ)) ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ -a)
    (hN : IsOpen N) (hEN : X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b ⊆ N) :
    ∃ L : JordanCompactNeighbourhood X,
      L.carrier ⊆ N ∧
      X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b ⊆ L.carrier ∧
      (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b) \ {(b : ℂ)} ⊆ interior L.carrier ∧
      (b : ℂ) ∈ frontier L.carrier ∧
      frontier L.carrier \ {(b : ℂ)} ⊆ (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)ᶜ := by
  let E := X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b
  let U := FunctionTheory.invertedExterior E
  have h0E : (0 : ℂ) ∈ E := Or.inr ⟨0, ⟨by linarith, hb.le⟩, by simp⟩
  have hEc : IsCompact E := hX.union (isCompact_Icc.image continuous_ofReal)
  have hUo : IsOpen U := FunctionTheory.isOpen_invertedExterior hEc
  obtain ⟨f, hf⟩ := exists_normalized_exterior_map_of_attached_segment
    hX hconn hfull ha hb hleft hmax
  obtain ⟨ξ, G, hξ, hGc, hGi, heq, hGξ, _⟩ :=
    FunctionTheory.exists_jordan_curves_through_reflected_slit_tip
      hUo hf.differentiableOn hf.bijOn (half_pos (inv_pos.mpr hb))
      (local_slit_at_inverted_segment_tip ha hb hmax)
  have hξnorm : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
  have hgd : DifferentiableOn ℂ (invFunOn f U) (ball 0 1) := by
    simpa only [hf.bijOn.image_eq] using hf.differentiableOn.invFunOn hUo hf.injOn
  have hGd : DifferentiableOn ℂ G (ball 0 1) := hgd.congr heq
  have hG0 : G 0 = 0 := by
    rw [heq (mem_ball_self zero_lt_one)]
    simpa only [hf.map_base] using hf.injOn.leftInvOn_invFunOn hf.base_mem
  have hGU : MapsTo G (ball 0 1) U := by
    intro w hw
    rw [heq hw]
    exact hf.surjOn.mapsTo_invFunOn hw
  have hGF : LeftInvOn G f U := by
    intro z hz
    rw [heq (hf.mapsTo hz)]
    exact hf.injOn.leftInvOn_invFunOn hz
  obtain ⟨δ, hδ, hδN⟩ := FunctionTheory.tangent_enclosures_eventually_subset_neighbourhood
    h0E hξnorm hf.differentiableOn.continuousOn hf.mapsTo hGF hN hEN
  let t := min δ (1 / 2) / 2
  have ht : 0 < t := half_pos (lt_min hδ (by norm_num))
  have htδ : t < δ := (half_lt_self (lt_min hδ (by norm_num))).trans_le (min_le_left _ _)
  have htHalf : t < 1 / 2 :=
    (half_lt_self (lt_min hδ (by norm_num))).trans_le (min_le_right _ _)
  let K := FunctionTheory.invertedExterior (G '' ball ((t : ℂ) * ξ) (1 - t))
  obtain ⟨hK, hEK, hEint, hJ, hbK, hfront⟩ :=
    FunctionTheory.tangent_disk_gives_compact_jordan_enclosure hξnorm ht htHalf
      hGc hGi hGd hG0 hGξ (by exact_mod_cast (inv_ne_zero hb.ne')) hGU
  have hbinv : (((b⁻¹ : ℝ) : ℂ))⁻¹ = (b : ℂ) := by simp
  rw [hbinv] at hEint hbK hfront
  have h0b : (0 : ℂ) ≠ (b : ℂ) := by exact_mod_cast hb.ne
  have hne : (interior K).Nonempty := ⟨0, hEint ⟨h0E, h0b⟩⟩
  have hJc := isComplexJordanCurve_of_tauCeti hJ
  obtain ⟨hKc, hKf, hKi, hKr⟩ := complex_compact_with_jordan_frontier_regular hK hne hJc
  have hXint : X ⊆ interior K := by
    intro z hz
    apply hEint ⟨Or.inl hz, ?_⟩
    intro he
    have he' : z = (b : ℂ) := he
    have hm := hmax z hz
    rw [he', ofReal_re] at hm
    linarith
  exact ⟨⟨K, hK, hKc, hKf, hXint, hJc, hKi, hKr⟩,
    hδN t ht htδ, hEK, hEint, hbK, hfront⟩

end EremenkosConjecture
