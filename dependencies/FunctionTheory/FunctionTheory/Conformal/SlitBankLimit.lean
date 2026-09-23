import FunctionTheory.Conformal.StraightBoundaryCoordinates
import FunctionTheory.Conformal.SlitTipBoundary

open Set Metric Complex Filter
open scoped Topology

namespace FunctionTheory

/-- A selected bank of a straight slit has a boundary limit. The transverse
coordinate can point to either side of the slit. -/
theorem exists_boundary_limit_at_slit_bank
    {U : Set ℂ} {f : ℂ → ℂ} {R : ℝ} {c α : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hlocal : U ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R)
    (hc : c ∈ ball (0 : ℂ) R) (hcre : c.re < 0) (hcim : c.im = 0)
    (hαre : α.re = 0) (hαim : α.im ≠ 0) :
    ∃ a ∈ sphere (0 : ℂ) 1,
      Tendsto f (𝓝[U ∩ {z : ℂ | 0 < ((z - c) / α).re}] c) (𝓝 a) := by
  have hα : α ≠ 0 := fun h => hαim (by rw [h]; rfl)
  have hmem : ∀ z ∈ ball (0 : ℂ) R, z ∈ U ↔ z ∈ slitPlane := by
    intro z hz
    have h := congrArg (fun S : Set ℂ => z ∈ S) hlocal
    simpa only [mem_inter_iff, hz, and_true] using iff_of_eq h
  let V : Set ℂ := (fun z : ℂ => c + α * z) ⁻¹' (ball 0 R ∩ {z : ℂ | z.re < 0})
  have hVo : IsOpen V :=
    (isOpen_ball.inter (isOpen_lt Complex.continuous_re continuous_const)).preimage (by fun_prop)
  have h0V : (0 : ℂ) ∈ V := by exact ⟨by simpa using hc, by simpa using hcre⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hVo 0 h0V
  refine exists_boundary_limit_at_straight_side_in_coordinates hU hf hbij hα hδ ?_ ?_
  · intro z hz hzre
    apply (hmem _ (hδV hz).1).mpr
    change 0 < (c + α * z).re ∨ (c + α * z).im ≠ 0
    right
    simpa [Complex.add_im, Complex.mul_im, hcim, hαre] using mul_ne_zero hαim hzre.ne'
  · intro z hz hzre hzU
    have hslit := (hmem _ (hδV hz).1).mp hzU
    change 0 < (c + α * z).re ∨ (c + α * z).im ≠ 0 at hslit
    rcases hslit with hpos | hne
    · exact (lt_asymm (show (c + α * z).re < 0 from (hδV hz).2) hpos)
    · apply hne
      simp [Complex.add_im, Complex.mul_im, hcim, hαre, hzre]

theorem sq_mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ^ 2 ∈ slitPlane := by
  change 0 < (z ^ 2).re ∨ (z ^ 2).im ≠ 0
  by_cases hi : z.im = 0
  · left
    simp only [pow_two, Complex.mul_re, hi, mul_zero, sub_zero]
    exact mul_pos hz hz
  · right
    simp only [pow_two, Complex.mul_im]
    have h : z.re * z.im ≠ 0 := mul_ne_zero hz.ne' hi
    intro heq
    apply h
    linear_combination heq / 2

theorem injOn_sq_right_halfplane : InjOn (fun z : ℂ => z ^ 2) {z : ℂ | 0 < z.re} := by
  intro z hz w hw heq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
  · exact h
  · have hre := congrArg Complex.re h
    simp only [Complex.neg_re] at hre
    have hz' : 0 < z.re := hz
    have hw' : 0 < w.re := hw
    linarith

end FunctionTheory
