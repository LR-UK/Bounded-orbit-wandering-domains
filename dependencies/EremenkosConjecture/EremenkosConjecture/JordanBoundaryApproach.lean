import EremenkosConjecture.JordanSimplyConnected
import FunctionTheory.Topology.BoundaryApproach

/-! # Connected approach to a Jordan boundary

The public Schoenflies closed-interior chart transfers convex approach regions
from the model square to a Jordan interior. Complex plane coordinates then
give the approach property at every point of the closure of a bounded Jordan
domain, as required by Tau Ceti's boundary-injectivity theorem.
-/

open Set Metric Schoenflies

namespace EremenkosConjecture

theorem isPreconnectedApproachAt_inside_jordanCurve {C : Set Plane}
    (hC : IsJordanCurve C) {a : Plane} (ha : a ∈ C ∪ inside C) :
    TauCeti.IsPreconnectedApproachAt (inside C) a := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨u, v, huv, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, G, hFG, hFu⟩ := squareExtension C u v hC huv
  have hFC : F '' C = modelCurve := hFu.image_eq.trans huv.image_eq
  have hFI : F '' inside C = Plane.openSquare 0 1 := by
    rw [image_eq_diff_of_bijOn_union hFG.bijOn hFC (disjoint_curve_inside C),
      closedSquare_sdiff_modelCurve]
  have hGI : G '' Plane.openSquare 0 1 = inside C :=
    hFG.image_inv_eq subset_union_right hFI
  apply FunctionTheory.isPreconnectedApproachAt_of_relative_chart
    (S := C ∪ inside C) (T := Plane.closedSquare 0 1)
    (V := Plane.openSquare 0 1) (F := F) (G := G)
    subset_union_right (fun z hz => (show Plane.supDist z 0 < 1 from hz).le)
    (hFG.continuousOn a ha) hFG.continuousOn_inv
    (hFG.mapsTo ha) (hFG.invOn.1 ha)
    (mapsTo_iff_image_subset.mpr hFI.subset) (mapsTo_iff_image_subset.mpr hGI.subset)
    (fun _ hz => hFG.invOn.1 (Or.inr hz))
    (FunctionTheory.isPreconnectedApproachAt_of_convex (Plane.convex_openSquare 0 1) _)

theorem isPreconnectedApproachAt_bounded_jordan_domain {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (hJ : IsComplexJordanCurve (frontier U)) {a : ℂ} (ha : a ∈ closure U) :
    TauCeti.IsPreconnectedApproachAt U a := by
  let e := complexPlaneHomeomorph
  have hUpb : Bornology.IsBounded (e '' U) :=
    (hUb.isCompact_closure.image e.continuous).isBounded.subset (image_mono subset_closure)
  have hJp : IsJordanCurve (frontier (e '' U)) := by
    rw [← e.image_frontier]
    exact hJ
  have heq := eq_inside_frontier_of_bounded_domain (e.isOpenMap _ hUo)
    (hUc.image e e.continuous.continuousOn) hUpb hJp
  have hae : e a ∈ frontier (e '' U) ∪ inside (frontier (e '' U)) := by
    have h : e a ∈ closure (e '' U) := by
      rw [← e.image_closure]
      exact mem_image_of_mem e ha
    rw [heq, closure_eq_self_union_frontier,
      (jordan_curve_theorem hJp).frontier_inside] at h
    exact h.symm
  have hP := isPreconnectedApproachAt_inside_jordanCurve hJp hae
  rw [← heq] at hP
  simpa only [e.preimage_image] using
    FunctionTheory.isPreconnectedApproachAt_preimage_homeomorph e hP

end EremenkosConjecture
