import EremenkosConjecture.RayGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Convex.Topology

open Set Metric Complex

namespace EremenkosConjecture

theorem mem_interior_closedHalfStrip_of_strict
    {ζ z : ℂ} {a b : ℝ} (hre : ζ.re - a < z.re) (him : |z.im - ζ.im| < b) :
    z ∈ interior (closedHalfStrip ζ a b) := by
  let V : Set ℂ := {w | ζ.re - a < w.re ∧ |w.im - ζ.im| < b}
  have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (Complex.continuous_im.sub continuous_const).abs continuous_const)
  have hsub : V ⊆ closedHalfStrip ζ a b := fun _ h => ⟨h.1.le, h.2.le⟩
  exact (interior_mono hsub) (hV.interior_eq.symm ▸ (show z ∈ V from ⟨hre, him⟩))

theorem convex_closedHalfStrip (ζ : ℂ) (a b : ℝ) :
    Convex ℝ (closedHalfStrip ζ a b) := by
  have heq : closedHalfStrip ζ a b =
      {z : ℂ | ζ.re - a ≤ z.re} ∩
        ({z : ℂ | ζ.im - b ≤ z.im} ∩ {z : ℂ | z.im ≤ ζ.im + b}) := by
    ext z
    simp only [closedHalfStrip, mem_ofPred_eq, mem_inter_iff, abs_le]
    constructor <;> rintro ⟨hr, hl, hu⟩ <;> constructor
    · exact hr
    · constructor <;> linarith
    · exact hr
    · constructor <;> linarith
  rw [heq]
  exact (convex_halfSpace_re_ge _).inter
    ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _))

theorem isConnected_interior_closedHalfStrip (ζ : ℂ) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    IsConnected (interior (closedHalfStrip ζ a b)) := by
  apply (convex_closedHalfStrip ζ a b).interior.isConnected
  refine ⟨ζ + ((1 - a : ℝ) : ℂ), mem_interior_closedHalfStrip_of_strict ?_ ?_⟩
  · simp only [add_re, ofReal_re]; linarith
  · simpa using hb

theorem right_semicircle_mem_interior_closedHalfStrip
    (a : ℂ) {H ρ : ℝ} (hρ : 0 < ρ) (hρH : ρ < H)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    circleMap a ρ θ ∈ interior (closedHalfStrip a 0 H) := by
  apply mem_interior_closedHalfStrip_of_strict
  · have hcos := Real.cos_pos_of_mem_Ioo hθ
    have hre : (circleMap a ρ θ).re = a.re + ρ * Real.cos θ := by simp [circleMap]
    rw [sub_zero, hre]
    exact lt_add_of_pos_right _ (mul_pos hρ hcos)
  · have h := Complex.abs_im_le_norm (circleMap a ρ θ - a)
    rw [sub_im, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ] at h
    exact h.trans_lt hρH

end EremenkosConjecture
