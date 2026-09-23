import ComplexApproximation.Topology.StripLocalisation
import ComplexApproximation.Topology.ArakelianHomeomorphism
import ComplexApproximation.Topology.ArakelianElementaryGeometry
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Metric Bornology

namespace ComplexApproximation

/-- A local plane homeomorphism preserves fullness of compact subsets of its
connected source domain. -/
theorem isConnected_compl_image_openPartialHomeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (hU : IsConnected e.source)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ e.source)
    (hfull : IsConnected Kᶜ) : IsConnected (e '' K)ᶜ := by
  have hV : IsConnected e.target := by
    rw [← e.image_source_eq_target]
    exact hU.image e e.continuousOn
  have h := isConnected_compl_image_domain_homeomorph e.open_source e.open_target
    hU hV e.toHomeomorphSourceTarget K hK hKU hfull
  have heq : (fun z : e.source => (e.toHomeomorphSourceTarget z : ℂ)) ''
      ((↑) ⁻¹' K) = e '' K := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hKU hz⟩, hz, rfl⟩
  rwa [heq] at h

/-- For an unbounded closed set, closedness of its image is enough to extend
compact fullness invariance to absence of bounded complementary components.
No ambient homeomorphism is assumed. -/
theorem noBoundedComplementComponents_image_openPartialHomeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (hU : IsConnected e.source)
    {E : Set ℂ} (hE : IsClosed E) (hEU : E ⊆ e.source)
    (hfull : NoBoundedComplementComponents E) (himage : IsClosed (e '' E)) :
    NoBoundedComplementComponents (e '' E) := by
  intro z hz hb
  let D := connectedComponentIn (e '' E)ᶜ z
  have hDo : IsOpen D := himage.isOpen_compl.connectedComponentIn
  have hzD : z ∈ D := mem_connectedComponentIn hz
  have hfront : frontier D ⊆ e '' E := by
    simpa only [compl_compl] using frontier_component_subset_compl himage.isOpen_compl hz
  have hfrontV : frontier D ⊆ e.target := by
    rintro w hw
    obtain ⟨v, hv, rfl⟩ := hfront hw
    exact e.map_source (hEU hv)
  have hfrontc : IsCompact (frontier D) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hpre : IsCompact (e.symm '' frontier D) :=
    hfrontc.image_of_continuousOn (e.continuousOn_symm.mono hfrontV)
  obtain ⟨R, hR, hbound⟩ := hpre.isBounded.exists_pos_norm_le
  let K := E ∩ closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_left hE
  have hKU : K ⊆ e.source := inter_subset_left.trans hEU
  have hKfull := isConnected_compl_image_openPartialHomeomorph e hU hK hKU
    (isConnected_compl_inter_closedBall hfull hR)
  have hfrontK : frontier D ⊆ e '' K := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := hfront hw
    refine ⟨v, ⟨hv, ?_⟩, hvw⟩
    apply mem_closedBall_zero_iff.mpr
    have hb' := hbound (e.symm w) (mem_image_of_mem e.symm hw)
    rw [← hvw, e.left_inv (hEU hv)] at hb'
    exact hb'
  have hKc : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hunb : ¬ IsBounded (e '' K)ᶜ := by
    intro hb'
    have hall : IsBounded (univ : Set ℂ) := by
      simpa only [union_compl_self] using hKc.isBounded.union hb'
    exact not_isBounded_exterior 1 (hall.subset (subset_univ _))
  obtain ⟨w, hwK, hwD⟩ := unbounded_connected_meets_frontier
    hKfull.isPreconnected hunb hDo hb
    ⟨z, fun hzK => hz (image_mono inter_subset_left hzK), hzD⟩
  exact hwK (hfrontK hwD)

/-- To transport an Arakelian set by a local chart, it suffices to match an
ambient homeomorphism away from a compact set. The compact decoration itself
needs no ambient extension. -/
theorem IsArakelian.image_openPartialHomeomorph_of_eqOn_off_compact
    {E K : Set ℂ} (hE : IsArakelian E)
    (e : OpenPartialHomeomorph ℂ ℂ) (hU : IsConnected e.source)
    (hEU : E ⊆ e.source) (himage : IsClosed (e '' E))
    (hK : IsCompact K) (H : ℂ ≃ₜ ℂ) (heH : EqOn e H (E \ K)) :
    IsArakelian (e '' E) := by
  apply (hE.image_homeomorph H).of_bounded_modification himage
    (noBoundedComplementComponents_image_openPartialHomeomorph e hU hE.isClosed hEU
      hE.noBoundedComplementComponents himage)
  · have hEK : IsCompact (E ∩ K) := hK.inter_left hE.isClosed
    apply (hEK.image_of_continuousOn (e.continuousOn.mono
      (inter_subset_left.trans hEU))).isBounded.subset
    rintro w ⟨⟨z, hz, rfl⟩, hw⟩
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    by_contra hzK
    exact hw ⟨z, hz, (heH ⟨hz, hzK⟩).symm⟩
  · apply ((hK.inter_left hE.isClosed).image H.continuous).isBounded.subset
    rintro w ⟨⟨z, hz, rfl⟩, hw⟩
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    by_contra hzK
    exact hw ⟨z, hz, heH ⟨hz, hzK⟩⟩

end ComplexApproximation
