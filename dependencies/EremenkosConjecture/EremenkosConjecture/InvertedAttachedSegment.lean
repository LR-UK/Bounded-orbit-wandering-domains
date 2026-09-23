import EremenkosConjecture.AttachedSegmentGeometry
import EremenkosConjecture.PlaneSimpleConnectivity
import FunctionTheory.Conformal.ExteriorCoordinate
import FunctionTheory.Conformal.RiemannMapping

open Set Metric Complex Bornology

namespace EremenkosConjecture

theorem attachedSegment_ofReal_eq_image_Icc (a b : ℝ) :
    attachedSegment (a : ℂ) (b - a) = ((↑) : ℝ → ℂ) '' Icc a b := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨a + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by simp⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t - a, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    push_cast
    ring

/-- Inverting about an interior point of the added segment yields an ordinary
simply connected plane domain. The coordinate includes the image of infinity. -/
theorem isSimplyConnected_invertedExterior_of_attached_segment
    {X : Set ℂ} {a b : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (ha : 0 < a) (hb : 0 < b) (hleft : (-(a : ℂ)) ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ -a) :
    IsSimplyConnected (FunctionTheory.invertedExterior
      (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)) := by
  let E := X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b
  have hsegment : attachedSegment (-(a : ℂ)) (a + b) =
      ((↑) : ℝ → ℂ) '' Icc (-a) b := by
    simpa only [ofReal_neg, sub_neg_eq_add, add_comm b] using
      attachedSegment_ofReal_eq_image_Icc (-a) b
  obtain ⟨hEc, _, hEf⟩ := full_continuum_with_attached_segment
    hX hconn hfull hleft (by simpa using hmax) (by linarith : 0 ≤ a + b)
  rw [hsegment] at hEc hEf
  have h0E : (0 : ℂ) ∈ E := Or.inr ⟨0, ⟨by linarith, hb.le⟩, by simp⟩
  apply isSimplyConnected_of_noBoundedComplementComponents
    (FunctionTheory.isOpen_invertedExterior hEc)
    (FunctionTheory.isConnected_invertedExterior hEc hEf h0E)
  let A : Set ℂ := X ∪ ((↑) : ℝ → ℂ) '' Ico (-a) 0
  let B : Set ℂ := ((↑) : ℝ → ℂ) '' Ioc 0 b
  have hAc : IsConnected A := hconn.union
    ⟨-(a : ℂ), hleft, ⟨-a, ⟨le_rfl, by linarith⟩, by simp⟩⟩
    ((isConnected_Ico (by linarith : -a < 0)).image _ continuous_ofReal.continuousOn)
  have hBc : IsConnected B := (isConnected_Ioc hb).image _ continuous_ofReal.continuousOn
  have hA0 : (0 : ℂ) ∉ A := by
    rintro (hx | ⟨t, ht, heq⟩)
    · have h := hmax 0 hx
      simp only [zero_re] at h
      linarith
    · have ht0 : t = 0 := by exact_mod_cast heq
      linarith [ht.2]
  have hB0 : (0 : ℂ) ∉ B := by
    rintro ⟨t, ht, heq⟩
    have ht0 : t = 0 := by exact_mod_cast heq
    linarith [ht.1]
  have hAcl : (0 : ℂ) ∈ closure A := by
    apply closure_mono (subset_union_right :
      ((↑) : ℝ → ℂ) '' Ico (-a) 0 ⊆ A)
    have hc := continuous_ofReal.continuousAt.continuousWithinAt.mem_closure_image
      (show (0 : ℝ) ∈ closure (Ico (-a) 0) by
        rw [closure_Ico (by linarith : -a ≠ 0)]
        exact ⟨by linarith, le_rfl⟩)
    simpa only [ofReal_zero] using hc
  have hBcl : (0 : ℂ) ∈ closure B := by
    have hc := continuous_ofReal.continuousAt.continuousWithinAt.mem_closure_image
      (show (0 : ℝ) ∈ closure (Ioc 0 b) by
        rw [closure_Ioc hb.ne]
        exact ⟨le_rfl, hb.le⟩)
    simpa only [ofReal_zero] using hc
  have hAE : A ⊆ E := by
    rintro z (hz | ⟨t, ht, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨t, ⟨ht.1, by linarith [ht.2]⟩, rfl⟩
  have hBE : B ⊆ E := by
    rintro z ⟨t, ht, rfl⟩
    exact Or.inr ⟨t, ⟨by linarith [ht.1], ht.2⟩, rfl⟩
  have hcover : ∀ z ∈ E, z ≠ 0 → z ∈ A ∨ z ∈ B := by
    rintro z (hz | ⟨t, ht, rfl⟩) hz0
    · exact Or.inl (Or.inl hz)
    · by_cases ht0 : t < 0
      · exact Or.inl (Or.inr ⟨t, ⟨ht.1, ht0⟩, rfl⟩)
      · have htne : t ≠ 0 := fun heq => hz0 (by simp [heq])
        exact Or.inr ⟨t, ⟨lt_of_le_of_ne (le_of_not_gt ht0) htne.symm, ht.2⟩, rfl⟩
  have hcomponent : ∀ C : Set ℂ, IsConnected C → (0 : ℂ) ∉ C →
      (0 : ℂ) ∈ closure C → C ⊆ E → ∀ z ∈ C,
      ¬ IsBounded (connectedComponentIn (FunctionTheory.invertedExterior E)ᶜ z⁻¹) := by
    intro C hCc hC0 hCcl hCE z hz
    have hci : ContinuousOn (fun w : ℂ => w⁻¹) C := by
      apply continuousOn_id.inv₀
      intro w hw heq
      change w = 0 at heq
      exact hC0 (heq ▸ hw)
    have hc := (hCc.image _ hci).isPreconnected
    have hsub : (fun w : ℂ => w⁻¹) '' C ⊆ (FunctionTheory.invertedExterior E)ᶜ := by
      rintro _ ⟨w, hw, rfl⟩ (heq | heq)
      · exact hC0 ((inv_eq_zero.mp heq) ▸ hw)
      · exact heq (by simpa only [inv_inv] using hCE hw)
    have hwithin := hc.subset_connectedComponentIn ⟨z, hz, rfl⟩ hsub
    exact fun hbounded => FunctionTheory.not_isBounded_inv_image_of_zero_mem_closure
      hCcl hC0 (hbounded.subset hwithin)
  intro z hz hbounded
  have hz0 : z ≠ 0 := fun heq => hz (Or.inl heq)
  have hzE : z⁻¹ ∈ E := by
    by_contra h
    exact hz (Or.inr h)
  rcases hcover z⁻¹ hzE (inv_ne_zero hz0) with hzA | hzB
  · exact hcomponent A hAc hA0 hAcl hAE _ hzA (by simpa only [inv_inv] using hbounded)
  · exact hcomponent B hBc hB0 hBcl hBE _ hzB (by simpa only [inv_inv] using hbounded)

/-- The spherical exterior map exists, normalized at infinity. In this chart,
zero represents infinity and the removed set contains the inversion pole. -/
theorem exists_normalized_exterior_map_of_attached_segment
    {X : Set ℂ} {a b : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (ha : 0 < a) (hb : 0 < b) (hleft : (-(a : ℂ)) ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ -a) :
    ∃ f : ℂ → ℂ, TauCeti.IsNormalizedRiemannMapOn f
      (FunctionTheory.invertedExterior (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b)) 0 := by
  have hcompact : IsCompact (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b) :=
    hX.union (isCompact_Icc.image continuous_ofReal)
  have hopen := FunctionTheory.isOpen_invertedExterior hcompact
  have hsc := isSimplyConnected_invertedExterior_of_attached_segment
    hX hconn hfull ha hb hleft hmax
  have htip : ((b⁻¹ : ℝ) : ℂ) ∉ FunctionTheory.invertedExterior
      (X ∪ ((↑) : ℝ → ℂ) '' Icc (-a) b) := by
    rintro (hzero | hnot)
    · exact (ofReal_ne_zero.mpr (inv_ne_zero hb.ne')) hzero
    · apply hnot
      exact Or.inr ⟨b, ⟨by linarith, le_rfl⟩, by simp⟩
  exact TauCeti.exists_isNormalizedRiemannMapOn hopen hsc
    (fun heq => htip (heq.symm ▸ mem_univ _)) (Or.inl rfl)

end EremenkosConjecture
