import EremenkosConjecture.JordanDomains
import Schoenflies.JordanSchoenflies
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! # Simple connectivity of bounded Jordan domains

The attributed Schoenflies closed-interior extension gives a homeomorphism
between a Jordan interior and an open square. Its contractibility and simple
connectivity then follow from Mathlib. This is a topological chart of the
domain, not an extension of a conformal map to the plane.
-/

open Set Schoenflies

namespace EremenkosConjecture

noncomputable def homeomorphOfIsHomeoOn {f g : Plane → Plane} {S T : Set Plane}
    (h : IsHomeoOn f g S T) : S ≃ₜ T where
  toFun z := ⟨f z, h.mapsTo z.property⟩
  invFun w := ⟨g w, h.mapsTo_inv w.property⟩
  left_inv z := Subtype.ext (h.invOn.1 z.property)
  right_inv w := Subtype.ext (h.invOn.2 w.property)
  continuous_toFun := h.continuousOn.domRestrict.subtype_mk _
  continuous_invFun := h.continuousOn_inv.domRestrict.subtype_mk _

theorem exists_homeomorph_inside_openSquare {C : Set Plane}
    (hC : IsJordanCurve C) : Nonempty (inside C ≃ₜ Plane.openSquare 0 1) := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨u, v, huv, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, G, hFG, hFu⟩ := squareExtension C u v hC huv
  have hFC : F '' C = modelCurve := hFu.image_eq.trans huv.image_eq
  have hFI : F '' inside C = Plane.openSquare 0 1 := by
    rw [image_eq_diff_of_bijOn_union hFG.bijOn hFC (disjoint_curve_inside C),
      closedSquare_sdiff_modelCurve]
  have hGI : G '' Plane.openSquare 0 1 = inside C :=
    hFG.image_inv_eq subset_union_right hFI
  have hI : IsHomeoOn F G (inside C) (Plane.openSquare 0 1) :=
    hFG.mono (S' := inside C) (T' := Plane.openSquare 0 1) subset_union_right
      (fun z hz => (show Plane.supDist z 0 < 1 from hz).le)
      (mapsTo_iff_image_subset.mpr hFI.subset) (mapsTo_iff_image_subset.mpr hGI.subset)
  exact ⟨homeomorphOfIsHomeoOn hI⟩

theorem isSimplyConnected_inside_jordanCurve {C : Set Plane}
    (hC : IsJordanCurve C) : IsSimplyConnected (inside C) := by
  obtain ⟨e⟩ := exists_homeomorph_inside_openSquare hC
  have : ContractibleSpace (Plane.openSquare (0 : Plane) 1) :=
    (Plane.convex_openSquare 0 1).contractibleSpace
      ⟨0, Plane.mem_openSquare_self (by norm_num)⟩
  exact e.toHomotopyEquiv.simplyConnectedSpace

theorem isSimplyConnected_bounded_jordan_domain {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (hJ : IsComplexJordanCurve (frontier U)) : IsSimplyConnected U := by
  let e := complexPlaneHomeomorph
  have hUpb : Bornology.IsBounded (e '' U) :=
    (hUb.isCompact_closure.image e.continuous).isBounded.subset (image_mono subset_closure)
  have hJp : IsJordanCurve (frontier (e '' U)) := by
    rw [← e.image_frontier]
    exact hJ
  have heq := eq_inside_frontier_of_bounded_domain (e.isOpenMap _ hUo)
    (hUc.image e e.continuous.continuousOn) hUpb hJp
  apply e.isSimplyConnected_image.mp
  rw [heq]
  exact isSimplyConnected_inside_jordanCurve hJp

theorem JordanCompactNeighbourhood.simplyConnectedInterior {K : Set ℂ}
    (L : JordanCompactNeighbourhood K) : IsSimplyConnected (interior L.carrier) := by
  apply isSimplyConnected_bounded_jordan_domain isOpen_interior L.connectedInterior
    (L.compact.isBounded.subset interior_subset)
  have hfr : frontier (interior L.carrier) = frontier L.carrier := by
    rw [frontier, L.regular.symm, interior_interior, L.compact.isClosed.frontier_eq]
  rw [hfr]
  exact L.jordan

end EremenkosConjecture
