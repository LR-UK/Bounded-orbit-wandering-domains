import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Order.Basic

open Set Metric Complex

namespace FunctionTheory

/-- The positive side is the part to the right of the attachment and outside
the cutting circle. The other side contains the attached continuum. -/
noncomputable def rightCircularCut (ζ : ℂ) (ρ : ℝ) (z : ℂ) : ℝ :=
  min (z.re - ζ.re) (dist z ζ - ρ)

theorem continuous_rightCircularCut (ζ : ℂ) (ρ : ℝ) :
    Continuous (rightCircularCut ζ ρ) :=
  (Complex.continuous_re.sub continuous_const).min
    ((continuous_id.dist continuous_const).sub continuous_const)

theorem rightCircularCut_neg_of_re_lt {ζ z : ℂ} {ρ : ℝ} (hz : z.re < ζ.re) :
    rightCircularCut ζ ρ z < 0 :=
  (min_le_left _ _).trans_lt (sub_neg.mpr hz)

theorem rightCircularCut_pos_iff {ζ z : ℂ} {ρ : ℝ} :
    0 < rightCircularCut ζ ρ z ↔ ζ.re < z.re ∧ ρ < dist z ζ := by
  simp [rightCircularCut, lt_min_iff]

/-- If the domain meets the vertical attachment line only inside a smaller
disk, every zero of the barrier is on the open right semicircle. -/
theorem exists_right_semicircle_of_rightCircularCut_eq_zero
    {U : Set ℂ} {ζ z : ℂ} {r ρ : ℝ} (hrρ : r < ρ)
    (hgate : ∀ w ∈ U, w.re = ζ.re → dist w ζ ≤ r)
    (hz : z ∈ U) (hcut : rightCircularCut ζ ρ z = 0) :
    ∃ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), z = circleMap ζ ρ θ := by
  have hmin : 0 ≤ min (z.re - ζ.re) (dist z ζ - ρ) := le_of_eq hcut.symm
  have hparts := le_min_iff.mp hmin
  have hre : ζ.re < z.re := by
    have hle : ζ.re ≤ z.re := sub_nonneg.mp hparts.1
    rcases hle.eq_or_lt with heq | hlt
    · have hdist := hgate z hz heq.symm
      linarith [hparts.2]
    · exact hlt
  have hdist : dist z ζ = ρ := by
    have hpos : 0 < z.re - ζ.re := sub_pos.mpr hre
    dsimp [rightCircularCut] at hcut
    rcases le_total (z.re - ζ.re) (dist z ζ - ρ) with hle | hle
    · rw [min_eq_left hle] at hcut
      linarith
    · rw [min_eq_right hle] at hcut
      linarith
  have harg : |(z - ζ).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using sub_pos.mpr hre))
  refine ⟨(z - ζ).arg, abs_lt.mp harg, ?_⟩
  have hnorm : ‖z - ζ‖ = ρ := by simpa [dist_eq_norm] using hdist
  have hexp := Complex.norm_mul_exp_arg_mul_I (z - ζ)
  rw [hnorm] at hexp
  simp only [circleMap]
  rw [hexp]
  abel

end FunctionTheory
