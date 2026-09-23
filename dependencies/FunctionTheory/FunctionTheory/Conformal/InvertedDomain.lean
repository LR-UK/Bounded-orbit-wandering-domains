import FunctionTheory.Conformal.ExteriorCoordinate

open Set Metric Complex Filter Bornology
open scoped Topology

namespace FunctionTheory

/-- Away from the inversion pole, neighbourhood membership transfers in
both directions through the reciprocal coordinate. -/
theorem invertedExterior_mem_nhds_iff {V : Set ℂ} {z : ℂ} (hz : z ≠ 0) :
    invertedExterior V ∈ 𝓝 z ↔ Vᶜ ∈ 𝓝 z⁻¹ := by
  constructor
  · intro h
    have hp := (continuousAt_inv₀ (inv_ne_zero hz)).preimage_mem_nhds
      (show invertedExterior V ∈ 𝓝 z⁻¹⁻¹ by simpa using h)
    have hn : ∀ᶠ w : ℂ in 𝓝 z⁻¹, w ≠ 0 :=
      isOpen_compl_singleton.mem_nhds (inv_ne_zero hz)
    filter_upwards [hp, hn] with w hw hw0
    rcases hw with hw | hw
    · exact (hw0 (inv_eq_zero.mp hw)).elim
    · simpa using hw
  · intro h
    exact mem_of_superset ((continuousAt_inv₀ hz).preimage_mem_nhds h)
      (fun w hw => Or.inr hw)

theorem zero_mem_interior_invertedExterior {V : Set ℂ} (hV : IsBounded V) :
    (0 : ℂ) ∈ interior (invertedExterior V) := by
  obtain ⟨M, hM, hbound⟩ := hV.exists_pos_norm_le
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨1 / (M + 1), by positivity, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  · right
    intro hzin
    have hsmall : ‖z‖ < 1 / (M + 1) := by simpa using hz
    have hprod : ‖z‖ * (M + 1) < 1 := (lt_div_iff₀ (by positivity)).mp hsmall
    have hle := mul_le_mul_of_nonneg_right (hbound _ hzin) (norm_nonneg z)
    rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)] at hle
    nlinarith [norm_nonneg z]

theorem isClosed_invertedExterior_of_isOpen {V : Set ℂ} (hV : IsOpen V) :
    IsClosed (invertedExterior V) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hz0 : z ≠ 0 := fun he => hz (Or.inl he)
  have hzV : z⁻¹ ∈ V := by
    by_contra hn
    exact hz (Or.inr hn)
  have hp := (continuousAt_inv₀ hz0).preimage_mem_nhds (hV.mem_nhds hzV)
  have hn : ∀ᶠ w : ℂ in 𝓝 z, w ≠ 0 := isOpen_compl_singleton.mem_nhds hz0
  filter_upwards [hp, hn] with w hw hw0
  rintro (he | he)
  · exact hw0 he
  · exact he hw

/-- A neighbourhood of the image of infinity becomes the exterior of a
compact set when the reciprocal coordinate is undone. -/
theorem isCompact_invertedExterior_of_isOpen {V : Set ℂ}
    (hV : IsOpen V) (h0 : (0 : ℂ) ∈ V) : IsCompact (invertedExterior V) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  apply (isCompact_iff_isClosed_bounded).mpr
  refine ⟨isClosed_invertedExterior_of_isOpen hV, ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨ε⁻¹, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0, le_of_lt (inv_pos.mpr hε)]
  · by_contra! hlarge
    have hinv : ‖z⁻¹‖ < ε := by
      rw [norm_inv]
      simpa only [inv_inv] using (inv_lt_inv₀ (norm_pos_iff.mpr hz0) (inv_pos.mpr hε)).mpr hlarge
    exact (hz.resolve_left hz0) (hball (by simpa using hinv))

/-- The Jordan boundary transforms by ordinary complex inversion. The
adjoined zero is an interior point, so it creates no spurious boundary. -/
theorem frontier_invertedExterior_of_bounded_open {V : Set ℂ}
    (hV : IsOpen V) (hb : IsBounded V) (h0 : (0 : ℂ) ∈ V) :
    frontier (invertedExterior V) = (fun z : ℂ => z⁻¹) '' frontier V := by
  have hc := isClosed_invertedExterior_of_isOpen hV
  have h0i := zero_mem_interior_invertedExterior hb
  have h0f : (0 : ℂ) ∉ frontier V := fun h => (hV.frontier_eq ▸ h).2 h0
  ext z
  by_cases hz0 : z = 0
  · subst z
    constructor
    · intro hz
      exact ((hc.frontier_eq ▸ hz).2 h0i).elim
    · rintro ⟨w, hw, he⟩
      exact (h0f (inv_eq_zero.mp he ▸ hw)).elim
  · rw [hc.frontier_eq, Set.mem_sdiff, mem_interior_iff_mem_nhds,
      invertedExterior_mem_nhds_iff hz0]
    have hint : Vᶜ ∈ 𝓝 z⁻¹ ↔ z⁻¹ ∉ closure V := by
      rw [← mem_interior_iff_mem_nhds, interior_compl]
      rfl
    rw [hint]
    constructor
    · rintro ⟨hz, hn⟩
      refine ⟨z⁻¹, ?_, inv_inv z⟩
      rw [hV.frontier_eq]
      exact ⟨not_not.mp hn, hz.resolve_left hz0⟩
    · rintro ⟨w, hw, he⟩
      have hw' : z⁻¹ = w := by rw [← he, inv_inv]
      exact ⟨Or.inr (by rw [hw']; exact (hV.frontier_eq ▸ hw).2),
        by rw [hw']; exact not_not.mpr ((hV.frontier_eq ▸ hw).1)⟩

end FunctionTheory
