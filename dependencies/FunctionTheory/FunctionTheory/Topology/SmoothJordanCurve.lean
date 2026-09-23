import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Composition

open Set Metric
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- A smooth Jordan curve is the image of the unit circle under a smooth
local plane diffeomorphism defined on a neighbourhood of the entire circle.
The inverse is smooth too, so this definition includes regularity. -/
def IsSmoothJordanCurve (C : Set ℂ) : Prop :=
  ∃ e : OpenPartialHomeomorph ℂ ℂ,
    sphere (0 : ℂ) 1 ⊆ e.source ∧
    ContDiffOn ℝ ∞ (e : ℂ → ℂ) e.source ∧
    ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) e.target ∧
    C=e '' sphere (0 : ℂ) 1

theorem IsSmoothJordanCurve.isJordanCurve {C : Set ℂ} (hC : IsSmoothJordanCurve C) :
    TauCeti.IsJordanCurve C := by
  obtain ⟨e,hs,he,hei,rfl⟩ := hC
  exact (TauCeti.isJordanCurve_sphere (0 : ℂ) (by norm_num : (0 : ℝ)<1)).image
    (e.continuousOn.mono hs) (e.injOn.mono hs)

/-- Smoothness is preserved under a smooth diffeomorphism of neighbourhoods. -/
theorem IsSmoothJordanCurve.image {C : Set ℂ} (hC : IsSmoothJordanCurve C)
    (e : OpenPartialHomeomorph ℂ ℂ) (hCe : C ⊆ e.source)
    (he : ContDiffOn ℝ ∞ (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) e.target) :
    IsSmoothJordanCurve (e '' C) := by
  obtain ⟨b,hs,hb,hbi,rfl⟩ := hC
  refine ⟨b.trans e,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨hs hz,hCe (mem_image_of_mem b hz)⟩
  · exact he.comp (hb.mono inter_subset_left) (fun z hz => hz.2)
  · exact hbi.comp (hei.mono inter_subset_left) (fun z hz => hz.2)
  · simp only [image_image]
    rfl

/-- Smoothness also transports backwards through a local diffeomorphism. -/
theorem IsSmoothJordanCurve.of_image {C : Set ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ) (hCe : C ⊆ e.source)
    (he : ContDiffOn ℝ ∞ (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) e.target)
    (hC : IsSmoothJordanCurve (e '' C)) : IsSmoothJordanCurve C := by
  have ht : e '' C ⊆ e.symm.source := by
    rintro _ ⟨z,hz,rfl⟩
    exact e.map_source (hCe hz)
  have H := hC.image e.symm ht hei he
  have heq : e.symm '' (e '' C)=C := by
    ext z
    constructor
    · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
      simpa only [e.left_inv (hCe hv)] using hv
    · intro hz
      exact ⟨e z,mem_image_of_mem e hz,e.left_inv (hCe hz)⟩
  rwa [heq] at H

/-- A global smooth plane diffeomorphism sends every unit circle to a
smooth Jordan curve. -/
theorem isSmoothJordanCurve_image_sphere (H : ℂ ≃ₜ ℂ) (c : ℂ)
    (hH : ContDiff ℝ ∞ (H : ℂ → ℂ)) (hHi : ContDiff ℝ ∞ (H.symm : ℂ → ℂ)) :
    IsSmoothJordanCurve (H '' sphere c 1) := by
  let J := (Homeomorph.addRight c).trans H
  refine ⟨J.toOpenPartialHomeomorph,subset_univ _,?_,?_,?_⟩
  · exact (hH.comp (contDiff_id.add contDiff_const)).contDiffOn
  · exact (hHi.sub contDiff_const).contDiffOn
  · ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w-c,?_,by simp [J]⟩
      simpa [mem_sphere,dist_eq_norm] using hw
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w+c,?_,rfl⟩
      simpa [mem_sphere,dist_eq_norm] using hw

end FunctionTheory
