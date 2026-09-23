import ComplexApproximation.Topology.LocalHomeomorphNonseparation

open Set Metric Bornology Function

namespace ComplexApproximation

/-- Outside a compact set, the displayed map agrees with a plane homeomorphism.
The condition imposes no ambient extension on the compact decoration. -/
def HasHomeomorphicTailOn (f : ℂ → ℂ) (A : Set ℂ) : Prop :=
  ∃ K : Set ℂ, IsCompact K ∧ ∃ H : ℂ ≃ₜ ℂ, EqOn f H (A \ K)

theorem HasHomeomorphicTailOn.mono {f : ℂ → ℂ} {A B : Set ℂ}
    (h : HasHomeomorphicTailOn f A) (hBA : B ⊆ A) : HasHomeomorphicTailOn f B := by
  obtain ⟨K, hK, H, heq⟩ := h
  exact ⟨K, hK, H, heq.mono (sdiff_subset_sdiff_left hBA)⟩

theorem HasHomeomorphicTailOn.congr {f g : ℂ → ℂ} {A : Set ℂ}
    (h : HasHomeomorphicTailOn f A) (heq : EqOn g f A) : HasHomeomorphicTailOn g A := by
  obtain ⟨K, hK, H, hH⟩ := h
  exact ⟨K, hK, H, fun _ hz => (heq hz.1).trans (hH hz)⟩

theorem HasHomeomorphicTailOn.homeomorph_comp {f : ℂ → ℂ} {A : Set ℂ}
    (h : HasHomeomorphicTailOn f A) (G : ℂ ≃ₜ ℂ) :
    HasHomeomorphicTailOn (G ∘ f) A := by
  obtain ⟨K, hK, H, heq⟩ := h
  exact ⟨K, hK, H.trans G, fun _ hz => congrArg G (heq hz)⟩

theorem HasHomeomorphicTailOn.isClosed_image {f : ℂ → ℂ} {A : Set ℂ}
    (h : HasHomeomorphicTailOn f A) (hA : IsClosed A) (hf : ContinuousOn f A) :
    IsClosed (f '' A) := by
  obtain ⟨K, hK, H, heq⟩ := h
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  let B := A ∩ closedBall 0 (R + 1)
  let T := A ∩ {z : ℂ | R + 1 ≤ ‖z‖}
  have hB : IsCompact B := (isCompact_closedBall 0 (R + 1)).inter_left hA
  have hT : IsClosed T := hA.inter (isClosed_le continuous_const continuous_norm)
  have hABT : A = B ∪ T := by
    ext z
    constructor
    · intro hz
      rcases le_total ‖z‖ (R + 1) with hr | hr
      · exact Or.inl ⟨hz, mem_closedBall_zero_iff.mpr hr⟩
      · exact Or.inr ⟨hz, hr⟩
    · exact fun hz => hz.elim And.left And.left
  have htail : f '' T = H '' T := image_congr (fun z hz => heq ⟨hz.1, by
    intro hzK
    have hb := hR z hzK
    have ht : R + 1 ≤ ‖z‖ := hz.2
    linarith⟩)
  rw [hABT, image_union, htail]
  exact (hB.image_of_continuousOn (hf.mono inter_subset_left)).isClosed.union
    (H.isClosedMap T hT)

/-- The tail condition transports every Arakelian closed subset of the chart
domain, so the inset may be chosen after the chart. -/
theorem IsArakelian.image_openPartialHomeomorph_of_homeomorphic_tail
    {E : Set ℂ} (hE : IsArakelian E)
    (e : OpenPartialHomeomorph ℂ ℂ) (hU : IsConnected e.source)
    (hEU : E ⊆ e.source) (htail : HasHomeomorphicTailOn e E) :
    IsArakelian (e '' E) := by
  have hc := htail.isClosed_image hE.isClosed (e.continuousOn.mono hEU)
  obtain ⟨K, hK, H, heq⟩ := htail
  exact hE.image_openPartialHomeomorph_of_eqOn_off_compact e hU hEU hc hK H heq

end ComplexApproximation
