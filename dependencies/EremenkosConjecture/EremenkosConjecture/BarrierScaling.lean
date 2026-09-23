import EremenkosConjecture.BarrierDynamics

open Set Metric Function ComplexDynamics

namespace EremenkosConjecture

theorem frontier_nontrivial_of_compact_full {K : Set ℂ} (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hKnt : K.Nontrivial) : (frontier K).Nontrivial := by
  by_contra h
  have hs : (frontier K).Subsingleton := not_nontrivial_iff.mp h
  have hne : (frontier K).Nonempty := nonempty_frontier_iff.mpr ⟨hKnt.nonempty, by
    intro H
    have h := hfull.nonempty
    simpa [H] using h⟩
  obtain ⟨a, ha⟩ := hne
  have hall (z : ℂ) (hz : z ∈ K) : z = a := by
    have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le hK.isBounded
      ((differentiable_id.sub_const a).diffContOnCl : DiffContOnCl ℂ (fun w : ℂ => w - a) K)
      (C := 0) (fun w hw => by simp only [id_eq, hs hw ha, sub_self, norm_zero, le_refl]) (subset_closure hz)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hbound)
  obtain ⟨x, hx, y, hy, hxy⟩ := hKnt
  exact hxy ((hall x hx).trans (hall y hy).symm)

noncomputable def BarrierWanderingWitness.scale {K : Set ℂ} (W : BarrierWanderingWitness K)
    (c : ℂ) (hc : c ≠ 0) : BarrierWanderingWitness ((fun z => c * z) '' K) := by
  let H := Homeomorph.mulLeft₀ c hc
  refine {
    toFastWanderingWitness := W.toFastWanderingWitness.scale c hc
    P := fun n => H '' W.P n
    trap := H '' W.trap
    trapOpen := H.isOpenMap _ W.trapOpen
    trapBounded := ?_
    trapInvariant := ?_
    entersTrap := ?_
    barrier := ?_
  }
  · obtain ⟨R, _, hR⟩ := W.trapBounded.exists_pos_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖c‖ * R, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    change ‖c * w‖ ≤ ‖c‖ * R
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hR w hw) (norm_nonneg c)
  · rintro z ⟨w, hw, rfl⟩
    refine ⟨W.f w, W.trapInvariant hw, ?_⟩
    change c * W.f w = scaleConjugate c W.f (c * w)
    simp only [scaleConjugate, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · intro n z hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨m, hm⟩ := W.entersTrap n w hw
    refine ⟨m, ?_⟩
    change ((scaleConjugate c W.f)^[m]) (c * w) ∈ H '' W.trap
    rw [iterate_scaleConjugate_mul c hc]
    exact mem_image_of_mem H hm
  · intro g hg hstart hend havoid
    have hx : H.symm (g 0) ∈ K := by
      obtain ⟨w, hw, heq⟩ := hstart
      change H w = g 0 at heq
      rw [← heq, H.symm_apply_apply]
      exact hw
    have hy : H.symm (g 1) ∉ K := fun h => hend ⟨H.symm (g 1), h, H.apply_symm_apply _⟩
    apply W.barrier (H.symm ∘ g) (H.symm.continuous.comp hg) hx hy
    intro t ht n hp
    exact havoid t ht n ⟨H.symm (g t), hp, H.apply_symm_apply _⟩

theorem exists_barrierWanderingWitness (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) (hKnt : K.Nontrivial) :
    Nonempty (BarrierWanderingWitness K) := by
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
  have hLconn : IsConnected L := hconn.image H.symm H.symm.continuous.continuousOn
  have hLf : IsConnected Lᶜ := isConnected_compl_image_homeomorph H.symm hfull
  have hLnt : L.Nontrivial := hKnt.image H.symm.injective
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
  obtain ⟨a, ha, b, hb, hab⟩ := frontier_nontrivial_of_compact_full hLc hLf hLnt
  obtain ⟨W⟩ := exists_barrierWanderingWitness_normalized L hLc hLconn hLf hLnorm ha hb hab
  have himage : (fun z => c * z) '' L = K := by
    change H '' (H.symm '' K) = K
    rw [← image_comp, show H ∘ H.symm = id from funext H.apply_symm_apply, image_id]
  exact himage ▸ ⟨W.scale c hc⟩

/-- Theorem 3.4 and Remark 3.5 for every non-singleton full continuum.
The singleton reduction to an inaccessible continuum is a separate step. -/
theorem fast_escaping_path_components_nontrivial (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) (hKnt : K.Nontrivial) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ K ⊆ fastEscapingSet f ∧
      (∀ x ∈ K, pathComponentIn (escapingSet f) x = pathComponentIn K x) ∧
      (∀ x ∈ frontier K, pathComponentIn (juliaSet f) x = pathComponentIn (frontier K) x) := by
  obtain ⟨W⟩ := exists_barrierWanderingWitness K hK hconn hfull hKnt
  exact ⟨W.f, W.transcendental, W.toFastWanderingWitness.fast hK.isClosed,
    fun _ hx => W.escaping_path_components hx, fun _ hx => W.julia_path_components hK.isClosed hx⟩

end EremenkosConjecture
