import EremenkosConjecture.FastNormalizedConstruction
import EremenkosConjecture.UniformEscape
import ComplexDynamics.FastEscapeScaling

/-! # Proposition 3.3: fast escaping wandering compacta -/

open Set Metric Function ComplexDynamics

namespace EremenkosConjecture

noncomputable def FastWanderingWitness.scale {K : Set ℂ} (W : FastWanderingWitness K)
    (c : ℂ) (hc : c ≠ 0) : FastWanderingWitness ((fun z => c * z) '' K) := by
  let H := Homeomorph.mulLeft₀ c hc
  refine {
    toUniformWanderingWitness := W.toUniformWanderingWitness.scale c hc
    radius := ‖c‖ * W.radius
    radius_pos := mul_pos (norm_pos_iff.mpr hc) W.radius_pos
    fastAt := ?_
    marker := c * W.marker
    marker_boundary := ?_
    marker_norm := ?_
  }
  · intro r hr
    rintro z ⟨w, hw, rfl⟩
    have hcpos := norm_pos_iff.mpr hc
    have H := mapsTo_scale_fastEscapingSetAtRadius W.transcendental.1.continuous c hc
      (div_nonneg hr hcpos.le) (W.fastAt (r / ‖c‖) (div_nonneg hr hcpos.le) hw)
    have heq : ‖c‖ * (r / ‖c‖) = r := by field_simp
    rwa [heq] at H
  · change H W.marker ∈ frontier (H '' K)
    rw [← H.image_frontier]
    exact mem_image_of_mem H W.marker_boundary
  · rw [norm_mul]
    exact mul_lt_mul_of_pos_left W.marker_norm (norm_pos_iff.mpr hc)

theorem exists_fastWanderingWitness (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hne : K.Nonempty) : Nonempty (FastWanderingWitness K) := by
  obtain ⟨r, hr, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let R := r + 1
  have hR : 0 < R := by dsimp [R]; linarith
  let c : ℂ := R
  have hc : c ≠ 0 := by
    change (R : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt hR)
  let H := Homeomorph.mulLeft₀ c hc
  let L := H.symm '' K
  have hLc : IsCompact L := hK.image H.symm.continuous
  have hLf : IsConnected Lᶜ := isConnected_compl_image_homeomorph H.symm hfull
  have hLne : L.Nonempty := hne.image H.symm
  have hcnorm : ‖c‖ = R := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hLnorm : L ⊆ targetDisc 0 := by
    rintro z ⟨w, hw, rfl⟩
    change (Homeomorph.mulLeft₀ c hc).symm w ∈ targetDisc 0
    rw [Homeomorph.mulLeft₀_symm_apply]
    simp only [targetDisc, mem_ball, Nat.cast_zero, mul_zero, Complex.ofReal_zero,
      dist_zero_right, norm_mul, norm_inv, hcnorm]
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_lt_one hR).mpr
    have hwbound := hbound w hw
    dsimp [R]
    linarith
  obtain ⟨W⟩ := exists_fastWanderingWitness_normalized L hLc hLf hLne hLnorm
  have himage : (fun z => c * z) '' L = K := by
    change H '' (H.symm '' K) = K
    rw [← image_comp, show H ∘ H.symm = id from funext H.apply_symm_apply, image_id]
  exact himage ▸ ⟨W.scale c hc⟩

/-- **Proposition 3.3.** The function in Theorem 3.1 can additionally be
chosen so that the whole compactum lies in its fast escaping set. -/
theorem fast_escaping_wandering_compactum (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      (∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)) ∧
      EscapesUniformlyOn f K ∧ frontier K ⊆ juliaSet f ∧
      (∀ z ∈ interior K, IsWanderingDomain f (connectedComponentIn (interior K) z)) ∧
      K ⊆ fastEscapingSet f ∧
      ∀ r : ℝ, 0 ≤ r → K ⊆ fastEscapingSetAtRadius f r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨f, hf, hd, he, hj, hw⟩ := wandering_compactum ∅ hK hfull
    exact ⟨f, hf, hd, he, hj, hw, empty_subset _, fun _ _ => empty_subset _⟩
  · obtain ⟨W⟩ := exists_fastWanderingWitness K hK hfull hne
    exact ⟨W.f, W.transcendental, W.disjoint, W.escape,
      W.toUniformWanderingWitness.julia_boundary hK.isClosed,
      W.toUniformWanderingWitness.wandering hK, W.fast hK.isClosed, W.fastAt⟩

end EremenkosConjecture
