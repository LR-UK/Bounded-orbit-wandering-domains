import EremenkosConjecture.NestedJordanNeighbourhoods
import TauCeti.Topology.JordanCurve.Path

/-! # Compatibility of the two public Jordan-curve definitions

Our neighbourhood construction uses the Schoenflies project's simple closed
paths in the Euclidean plane. Tau Ceti's boundary theorem uses a homeomorphism
with the circle. This file proves the required conversion, retaining both
public definitions unchanged.
-/

open Set

namespace EremenkosConjecture

theorem tauCeti_isJordanCurve_of_schoenflies {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) : TauCeti.IsJordanCurve C := by
  obtain ⟨f, hf, hC⟩ := hC
  let γ : Path (f 0) (f 0) :=
    { toFun := fun t => f t
      continuous_toFun := hf.continuousOn.domRestrict
      source' := rfl
      target' := hf.closes.symm }
  have hγ : ∀ ⦃s t : unitInterval⦄, γ s = γ t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t hst
    change f s = f t at hst
    by_cases hs : s = 1
    · subst s
      by_cases ht : t = 1
      · exact Or.inl ht.symm
      · right; right
        refine ⟨rfl, Subtype.ext ?_⟩
        have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
          (fun h => ht (Subtype.ext h))
        exact (hf.injOn (show (0 : ℝ) ∈ Ico 0 1 by simp)
          ⟨t.property.1, ht'⟩ (hf.closes.trans hst)).symm
    · have hs' : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2
        (fun h => hs (Subtype.ext h))
      by_cases ht : t = 1
      · subst t
        right; left
        exact ⟨Subtype.ext (hf.injOn ⟨s.property.1, hs'⟩
          (show (0 : ℝ) ∈ Ico 0 1 by simp) (hst.trans hf.closes.symm)), rfl⟩
      · left
        have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
          (fun h => ht (Subtype.ext h))
        exact Subtype.ext (hf.injOn ⟨s.property.1, hs'⟩ ⟨t.property.1, ht'⟩ hst)
  have hrange : range γ = C := by
    rw [← hC]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hrange]
  exact TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints γ hγ

theorem IsComplexJordanCurve.tauCeti {C : Set ℂ} (hC : IsComplexJordanCurve C) :
    TauCeti.IsJordanCurve C := by
  have h := tauCeti_isJordanCurve_of_schoenflies hC
  exact (TauCeti.isJordanCurve_image_homeomorph_iff complexPlaneHomeomorph).mp h

theorem JordanCompactNeighbourhood.tauCeti_frontier {K : Set ℂ}
    (L : JordanCompactNeighbourhood K) : TauCeti.IsJordanCurve (frontier L.carrier) :=
  L.jordan.tauCeti

end EremenkosConjecture
