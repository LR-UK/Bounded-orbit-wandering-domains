import EremenkosConjecture.NormalizedConstruction
import ComplexDynamics.Scaling

/-! # Theorem 3.1: wandering compacta with uniform escape -/

open Set Metric Function ComplexDynamics

namespace EremenkosConjecture

noncomputable def UniformWanderingWitness.scale {K : Set ℂ} (W : UniformWanderingWitness K)
    (c : ℂ) (hc : c ≠ 0) : UniformWanderingWitness ((fun z => c * z) '' K) := by
  let H := Homeomorph.mulLeft₀ c hc
  let F := scaleConjugate c W.f
  have himage (n : ℕ) : (F^[n]) '' (H '' K) = H '' ((W.f^[n]) '' K) := by
    rw [← image_comp, ← image_comp]
    apply image_congr
    intro z _
    exact iterate_scaleConjugate_mul c hc W.f n z
  refine {
    f := F
    transcendental := W.transcendental.scaleConjugate c hc
    B := H '' W.B
    compactB := W.compactB.image H.continuous
    escape := W.escape.scaleConjugate c hc
    disjoint := ?_
    boundary := ?_
    ambient := ?_
  }
  · intro n m hnm
    change Disjoint ((F^[n]) '' (H '' K)) ((F^[m]) '' (H '' K))
    rw [himage n, himage m]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq : y = x := H.injective hxy
    exact Set.disjoint_left.mp (W.disjoint n m hnm) hx (heq ▸ hy)
  · change frontier (H '' K) ⊆ closure (trappedSet F (H '' W.B))
    rw [← H.image_frontier]
    rintro z ⟨w, hw, rfl⟩
    exact (mapsTo_scale_trappedSet W.f W.B c hc).closure_of_continuousOn
      H.continuous.continuousOn (W.boundary hw)
  · intro n
    obtain ⟨G, hG⟩ := W.ambient n
    refine ⟨H.symm.trans (G.trans H), ?_⟩
    rintro z ⟨w, hw, rfl⟩
    change (F^[n]) (H w) = (H.symm.trans (G.trans H)) (H w)
    rw [Homeomorph.trans_apply, H.symm_apply_apply]
    change (F^[n]) (c * w) = c * G w
    rw [iterate_scaleConjugate_mul c hc, hG hw]

theorem exists_uniformWanderingWitness (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) : Nonempty (UniformWanderingWitness K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · have hfull₀ : IsConnected ({0} : Set ℂ)ᶜ := by
      simpa only [closedBall_zero] using isConnected_compl_closedBall (0 : ℂ) 0
    obtain ⟨W⟩ := exists_uniformWanderingWitness_normalized {0} isCompact_singleton hfull₀
      (singleton_nonempty 0) (by simp [targetDisc])
    exact ⟨{
      f := W.f
      transcendental := W.transcendental
      B := W.B
      compactB := W.compactB
      escape := W.escape.mono (empty_subset _)
      disjoint := by simp
      boundary := by simp
      ambient := fun n => ⟨Homeomorph.refl ℂ, by simp [EqOn]⟩
    }⟩
  · obtain ⟨r, hr, hbound⟩ := hK.isBounded.exists_pos_norm_le
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
    obtain ⟨W⟩ := exists_uniformWanderingWitness_normalized L hLc hLf hLne hLnorm
    have himage : (fun z => c * z) '' L = K := by
      change H '' (H.symm '' K) = K
      rw [← image_comp, show H ∘ H.symm = id from funext H.apply_symm_apply, image_id]
    exact himage ▸ ⟨W.scale c hc⟩

/-- **Theorem 3.1.** Every full compact subset of the plane is a wandering
compactum of a transcendental entire function, with uniform escape, Julia
boundary, and wandering Fatou components in its interior. -/
theorem wandering_compactum (K : Set ℂ) (hK : IsCompact K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      (∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)) ∧
      EscapesUniformlyOn f K ∧ frontier K ⊆ juliaSet f ∧
      ∀ z ∈ interior K, IsWanderingDomain f (connectedComponentIn (interior K) z) := by
  obtain ⟨W⟩ := exists_uniformWanderingWitness K hK hfull
  exact ⟨W.f, W.transcendental, W.disjoint, W.escape, W.julia_boundary hK.isClosed, W.wandering hK⟩

end EremenkosConjecture
