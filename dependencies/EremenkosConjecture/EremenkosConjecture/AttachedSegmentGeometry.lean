import EremenkosConjecture.ContinuumRayGeometry
import ComplexApproximation.Topology.FilledContinua

open Set Metric Complex Bornology

namespace EremenkosConjecture

/-- Truncating the attached ray, or removing any closed selection from it,
cannot create a bounded complementary component. -/
theorem noBoundedComplementComponents_between_set_and_attached_ray
    {X E : Set ℂ} {ζ : ℂ}
    (hX : IsCompact X) (hfull : IsConnected Xᶜ) (hζ : ζ ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ ζ.re) (hE : IsClosed E)
    (hXE : X ⊆ E) (hEX : E ⊆ X ∪ horizontalRay ζ) :
    ComplexApproximation.NoBoundedComplementComponents E := by
  have hfill : ComplexApproximation.fill E ⊆ X ∪ horizontalRay ζ := by
    have h := ComplexApproximation.fill_mono hEX
    rwa [ComplexApproximation.fill_eq_self
      (noBoundedComplementComponents_union_horizontalRay hX hfull hζ hmax)] at h
  intro z hz hb
  let D := connectedComponentIn Eᶜ z
  have hDR : D ⊆ horizontalRay ζ := by
    intro w hw
    have hwfill : w ∈ ComplexApproximation.fill E := by
      change IsBounded (connectedComponentIn Eᶜ w)
      rwa [← connectedComponentIn_eq hw]
    rcases hfill hwfill with hwX | hwR
    · exact False.elim ((connectedComponentIn_subset Eᶜ z hw) (hXE hwX))
    · exact hwR
  have hzD : z ∈ D := mem_connectedComponentIn hz
  have hzi : z ∈ interior (horizontalRay ζ) :=
    interior_mono hDR (hE.isOpen_compl.connectedComponentIn.interior_eq.symm ▸ hzD)
  have hzf : z ∈ frontier (horizontalRay ζ) := by
    rw [frontier_horizontalRay]
    exact hDR hzD
  exact hzf.2 hzi

def attachedSegment (ζ : ℂ) (ε : ℝ) : Set ℂ :=
  (fun t : ℝ => ζ + (t : ℂ)) '' Icc 0 ε

theorem full_continuum_with_attached_segment
    {X : Set ℂ} {ζ : ℂ} {ε : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : ζ ∈ X) (hmax : ∀ x ∈ X, x.re ≤ ζ.re) (hε : 0 ≤ ε) :
    IsCompact (X ∪ attachedSegment ζ ε) ∧
      IsConnected (X ∪ attachedSegment ζ ε) ∧
      IsConnected (X ∪ attachedSegment ζ ε)ᶜ := by
  have hc : Continuous (fun t : ℝ => ζ + (t : ℂ)) := by fun_prop
  have hS : IsCompact (attachedSegment ζ ε) := isCompact_Icc.image hc
  have hζS : ζ ∈ attachedSegment ζ ε := ⟨0, ⟨le_rfl, hε⟩, by simp⟩
  have hSc : IsConnected (attachedSegment ζ ε) :=
    (isConnected_Icc hε).image _ hc.continuousOn
  have hcompact := hX.union hS
  refine ⟨hcompact, hconn.union ⟨ζ, hζ, hζS⟩ hSc, ?_⟩
  apply ComplexApproximation.isConnected_compl_of_unbounded_components _ hcompact.isBounded
  apply noBoundedComplementComponents_between_set_and_attached_ray hX hfull hζ hmax
    hcompact.isClosed subset_union_left
  rintro z (hz | ⟨t, ht, rfl⟩)
  · exact Or.inl hz
  · exact Or.inr ⟨by simpa using ht.1, by simp⟩

/-- Near the free endpoint, the exterior really is a straight slit plane.
The compact continuum itself imposes no further local boundary conditions. -/
theorem local_slit_at_attached_segment_tip
    {X : Set ℂ} {ζ : ℂ} {ε : ℝ}
    (hmax : ∀ x ∈ X, x.re ≤ ζ.re) (hε : 0 < ε) :
    {z : ℂ | ζ + (ε : ℂ) + z ∈ (X ∪ attachedSegment ζ ε)ᶜ} ∩
        ball (0 : ℂ) (ε / 2) = slitPlane ∩ ball 0 (ε / 2) := by
  ext z
  by_cases hz : z ∈ ball (0 : ℂ) (ε / 2)
  · have hn : ‖z‖ < ε / 2 := by simpa only [mem_ball, dist_zero_right] using hz
    have hr : -ε < z.re := by
      have h := (abs_le.mp (abs_re_le_norm z)).1
      linarith
    have hnotX : ζ + (ε : ℂ) + z ∉ X := by
      intro h
      have hh := hmax _ h
      simp only [add_re, ofReal_re] at hh
      linarith
    have hsegment : ζ + (ε : ℂ) + z ∈ attachedSegment ζ ε ↔
        z.re ≤ 0 ∧ z.im = 0 := by
      constructor
      · rintro ⟨t, ht, heq⟩
        have hre := congrArg Complex.re heq
        have him := congrArg Complex.im heq
        simp only [add_re, add_im, ofReal_re, ofReal_im, add_zero] at hre him
        exact ⟨by linarith [ht.2], by linarith⟩
      · rintro ⟨hre, him⟩
        refine ⟨ε + z.re, ⟨by linarith, by linarith⟩, ?_⟩
        apply Complex.ext <;> simp [him] <;> ring
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_union,
      hnotX, false_or, hsegment, hz, and_true, mem_slitPlane_iff, not_and_or, not_le]
  · simp only [mem_inter_iff, hz, and_false]

end EremenkosConjecture
