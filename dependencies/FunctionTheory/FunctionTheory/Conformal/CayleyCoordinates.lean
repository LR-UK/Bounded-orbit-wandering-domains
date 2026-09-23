import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Coordinates near the boundary point one of the disk

The involution `(1-z)/(1+z)` carries the right halfplane to the unit disk,
the imaginary axis to its boundary, and zero to one. These coordinates let
Schwarz reflection on a straight line apply at a disk boundary point.
-/

open Set Metric Complex

namespace FunctionTheory

noncomputable def cayleyCoordinate (z : ℂ) : ℂ := (1 - z) / (1 + z)

@[simp] theorem cayleyCoordinate_zero : cayleyCoordinate 0 = 1 := by
  simp [cayleyCoordinate]

@[simp] theorem cayleyCoordinate_one : cayleyCoordinate 1 = 0 := by
  simp [cayleyCoordinate]

theorem cayley_denominator_ne_zero {z : ℂ} (hz : 0 ≤ z.re) : 1 + z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, one_re, zero_re] at this
  linarith

theorem differentiableAt_cayleyCoordinate {z : ℂ} (hz : 1 + z ≠ 0) :
    DifferentiableAt ℂ cayleyCoordinate z :=
  ((differentiable_const (1 : ℂ)).sub differentiable_id).differentiableAt.div
    ((differentiable_const (1 : ℂ)).add differentiable_id).differentiableAt hz

theorem cayleyCoordinate_injOn : InjOn cayleyCoordinate {z : ℂ | 1 + z ≠ 0} := by
  intro z hz w hw h
  have hcross := (div_eq_div_iff hz hw).mp h
  linear_combination -hcross / 2

theorem one_add_cayleyCoordinate_ne_zero {z : ℂ} (hz : 1 + z ≠ 0) :
    1 + cayleyCoordinate z ≠ 0 := by
  intro h
  have hh : (1 + z) + (1 - z) = 0 := by
    simpa only [cayleyCoordinate, add_mul, one_mul, div_mul_cancel₀ _ hz,
      zero_mul] using congrArg (fun w => w * (1 + z)) h
  have htwo : (2 : ℂ) = 0 := by linear_combination hh
  exact two_ne_zero htwo

theorem cayleyCoordinate_involution {z : ℂ} (hz : 1 + z ≠ 0) :
    cayleyCoordinate (cayleyCoordinate z) = z := by
  have hh := one_add_cayleyCoordinate_ne_zero hz
  apply (div_eq_iff hh).mpr
  change 1 - (1 - z) / (1 + z) = z * (1 + (1 - z) / (1 + z))
  field_simp
  ring

private theorem normSq_one_add_sub (z : ℂ) :
    normSq (1 + z) - normSq (1 - z) = 4 * z.re := by
  simp only [normSq_apply, add_re, sub_re, add_im, sub_im, one_re, one_im]
  ring

theorem cayleyCoordinate_mem_closedBall {z : ℂ} (hz : 0 ≤ z.re) :
    cayleyCoordinate z ∈ closedBall 0 1 := by
  have hd := cayley_denominator_ne_zero hz
  have hnorm : ‖1 - z‖ ≤ ‖1 + z‖ := by
    have h := normSq_one_add_sub z
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (1 - z), norm_nonneg (1 + z)]
  simpa only [mem_closedBall, dist_zero_right, cayleyCoordinate, norm_div] using
    (div_le_one (norm_pos_iff.mpr hd)).mpr hnorm

theorem cayleyCoordinate_mem_ball {z : ℂ} (hz : 0 < z.re) :
    cayleyCoordinate z ∈ ball 0 1 := by
  have hd := cayley_denominator_ne_zero hz.le
  have hnorm : ‖1 - z‖ < ‖1 + z‖ := by
    have h := normSq_one_add_sub z
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (1 - z), norm_nonneg (1 + z)]
  simpa only [mem_ball, dist_zero_right, cayleyCoordinate, norm_div] using
    (div_lt_one (norm_pos_iff.mpr hd)).mpr hnorm

theorem cayleyCoordinate_mem_sphere {z : ℂ} (hz : z.re = 0) :
    cayleyCoordinate z ∈ sphere 0 1 := by
  have hd := cayley_denominator_ne_zero (le_of_eq hz.symm)
  have hnorm : ‖1 - z‖ = ‖1 + z‖ := by
    have h := normSq_one_add_sub z
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq, hz] at h
    nlinarith [norm_nonneg (1 - z), norm_nonneg (1 + z)]
  simp only [mem_sphere, dist_zero_right, cayleyCoordinate, norm_div, hnorm,
    div_self (norm_ne_zero_iff.mpr hd)]

theorem cayley_denominator_ne_zero_of_mem_ball {z : ℂ} (hz : z ∈ ball 0 1) :
    1 + z ≠ 0 := by
  intro h
  have hz' : z = -1 := by linear_combination h
  simp [hz'] at hz

theorem re_cayleyCoordinate (z : ℂ) :
    (cayleyCoordinate z).re = (1 - normSq z) / normSq (1 + z) := by
  simp only [cayleyCoordinate, div_re, normSq_apply, sub_re, one_re, add_re, sub_im, one_im,
    add_im, zero_sub, zero_add]
  ring

theorem re_cayleyCoordinate_pos_of_mem_ball {z : ℂ} (hz : z ∈ ball 0 1) :
    0 < (cayleyCoordinate z).re := by
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hd := cayley_denominator_ne_zero_of_mem_ball hz
  rw [re_cayleyCoordinate]
  apply div_pos
  · rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  · rw [normSq_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd)

theorem bijOn_cayleyCoordinate_ball :
    BijOn cayleyCoordinate (ball 0 1) {w : ℂ | 0 < w.re} := by
  refine ⟨fun _ hz => re_cayleyCoordinate_pos_of_mem_ball hz, ?_, ?_⟩
  · exact cayleyCoordinate_injOn.mono fun _ hz => cayley_denominator_ne_zero_of_mem_ball hz
  · intro w hw
    exact ⟨cayleyCoordinate w, cayleyCoordinate_mem_ball hw,
      cayleyCoordinate_involution (cayley_denominator_ne_zero (show 0 < w.re from hw).le)⟩

end FunctionTheory
