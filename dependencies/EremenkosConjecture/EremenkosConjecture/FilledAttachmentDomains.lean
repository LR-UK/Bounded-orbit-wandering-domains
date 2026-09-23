import EremenkosConjecture.FilledAttachmentGeometry
import EremenkosConjecture.FilledDomainComponents
import EremenkosConjecture.HalfStripInterior

open Set Metric Complex

namespace EremenkosConjecture

def attachmentCore (C : Set ℂ) (ζ a : ℂ) (s η H : ℝ) : Set ℂ :=
  interior C ∪ interior (closedHalfStrip ζ s η) ∪ interior (closedHalfStrip a 0 H)

def filledAttachmentDomain (C : Set ℂ) (ζ a : ℂ) (s η H : ℝ) : Set ℂ :=
  connectedComponentIn (interior (ComplexApproximation.fill (attachedHalfStrips C ζ a s η H))) ζ

theorem isConnected_attachmentCore
    {C : Set ℂ} {ζ a : ℂ} {s η H : ℝ}
    (hC : IsConnected (interior C)) (hζ : ζ ∈ interior C)
    (hs : 0 < s) (hη : 0 < η) (hH : 0 < H) (him : ζ.im = a.im) :
    IsConnected (attachmentCore C ζ a s η H) := by
  have hζS := horizontalRay_subset_interior_halfStrip hs hη (mem_horizontalRay ζ)
  have hleft := hC.union ⟨ζ, hζ, hζS⟩ (isConnected_interior_closedHalfStrip ζ s hη)
  let p : ℂ := ((max (ζ.re - s) a.re + 1 : ℝ) : ℂ) + (a.im : ℂ) * I
  have hpre : p.re = max (ζ.re - s) a.re + 1 := by simp [p]
  have hpim : p.im = a.im := by simp [p]
  have hpS : p ∈ interior (closedHalfStrip ζ s η) := by
    apply mem_interior_closedHalfStrip_of_strict
    · rw [hpre]; linarith [le_max_left (ζ.re - s) a.re]
    · simpa [hpim, him] using hη
  have hpH : p ∈ interior (closedHalfStrip a 0 H) := by
    apply mem_interior_closedHalfStrip_of_strict
    · rw [hpre, sub_zero]; linarith [le_max_right (ζ.re - s) a.re]
    · simpa [hpim] using hH
  exact hleft.union ⟨p, Or.inr hpS, hpH⟩ (isConnected_interior_closedHalfStrip a 0 hH)

theorem attachmentCore_subset_filledAttachmentDomain
    {C : Set ℂ} {ζ a : ℂ} {s η H : ℝ}
    (hC : IsConnected (interior C)) (hζ : ζ ∈ interior C)
    (hs : 0 < s) (hη : 0 < η) (hH : 0 < H) (him : ζ.im = a.im) :
    attachmentCore C ζ a s η H ⊆ filledAttachmentDomain C ζ a s η H := by
  apply (isConnected_attachmentCore hC hζ hs hη hH him).isPreconnected.subset_connectedComponentIn
    (Or.inl (Or.inl hζ))
  intro z hz
  rcases hz with (hzC | hzS) | hzH
  · exact (interior_mono (fun _ hw => ComplexApproximation.subset_fill _ (Or.inl (Or.inl hw)))) hzC
  · exact (interior_mono (fun _ hw => ComplexApproximation.subset_fill _ (Or.inl (Or.inr hw)))) hzS
  · exact (interior_mono (fun _ hw => ComplexApproximation.subset_fill _ (Or.inr hw))) hzH

/-- An actual open simply connected domain containing the decoration and the
ray, with the narrow gate and semicircles used by the analytic estimate.
No assertion about its Jordan boundary is made here. -/
theorem filledAttachmentDomain_properties
    {X C : Set ℂ} {ζ a : ℂ} {s η H A : ℝ}
    (hC : IsConnected (interior C)) (hζ : ζ ∈ interior C) (hXC : X ⊆ interior C)
    (hs : 0 < s) (hη : 0 < η) (hH : 0 < H) (him : ζ.im = a.im)
    (hleft : ∀ z ∈ C, z.re ≤ A) (hAa : A < a.re) :
    IsOpen (filledAttachmentDomain C ζ a s η H) ∧
    IsSimplyConnected (filledAttachmentDomain C ζ a s η H) ∧
    X ∪ horizontalRay ζ ⊆ filledAttachmentDomain C ζ a s η H ∧
    (∀ z ∈ filledAttachmentDomain C ζ a s η H, z.re = a.re → dist z a ≤ η) ∧
    ∀ ρ ∈ Ioo 0 H, ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2),
      circleMap a ρ θ ∈ filledAttachmentDomain C ζ a s η H := by
  have hcore := attachmentCore_subset_filledAttachmentDomain hC hζ hs hη hH him
  have hζfill : ζ ∈ interior (ComplexApproximation.fill (attachedHalfStrips C ζ a s η H)) :=
    (interior_mono (fun _ hw => ComplexApproximation.subset_fill _ (Or.inl (Or.inl hw)))) hζ
  refine ⟨isOpen_interior.connectedComponentIn,
    isSimplyConnected_component_interior_fill hζfill, ?_, ?_, ?_⟩
  · rintro z (hz | hz)
    · exact hcore (Or.inl (Or.inl (hXC hz)))
    · exact hcore (Or.inl (Or.inr (horizontalRay_subset_interior_halfStrip hs hη hz)))
  · intro z hz hza
    exact interior_filled_attachment_gate_bound hleft hAa him z
      (connectedComponentIn_subset _ _ hz) hza
  · intro ρ hρ θ hθ
    exact hcore (Or.inr (right_semicircle_mem_interior_closedHalfStrip a hρ.1 hρ.2 hθ))

theorem filledAttachmentDomain_mono
    {C D : Set ℂ} {ζ a : ℂ} {s t η κ H : ℝ}
    (hCD : C ⊆ D) (hst : s ≤ t) (hηκ : η ≤ κ) :
    filledAttachmentDomain C ζ a s η H ⊆ filledAttachmentDomain D ζ a t κ H := by
  apply connectedComponentIn_mono
  apply interior_mono
  apply ComplexApproximation.fill_mono
  rintro z ((hzC | hzS) | hzH)
  · exact Or.inl (Or.inl (hCD hzC))
  · exact Or.inl (Or.inr ⟨by have := hzS.1; linarith, hzS.2.trans hηκ⟩)
  · exact Or.inr hzH

end EremenkosConjecture
