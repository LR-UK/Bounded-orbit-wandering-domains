import TauCeti.Analysis.Complex.Conformal.Reflection.Circle.Principle

/-! # Bounds for Schwarz reflection in the unit circle

A positive lower bound on the inner values bounds their reflected reciprocals.
Together with an upper bound on the closed inner side, this gives a single
bound for the reflected function on a symmetric open neighbourhood.
-/

open Set Metric EuclideanGeometry

namespace FunctionTheory

theorem norm_unit_circle_inversion (w : ℂ) : ‖inversion (0 : ℂ) 1 w‖ = 1 / ‖w‖ := by
  simpa only [dist_zero_right, one_pow] using dist_inversion_center (0 : ℂ) w 1

theorem norm_circleSchwarzReflection_le {Ω : Set ℂ} {f : ℂ → ℂ} {δ M : ℝ}
    (hδ : 0 < δ) (hsymm : MapsTo (inversion (0 : ℂ) 1) Ω Ω)
    (hupper : ∀ z ∈ Ω ∩ closedBall (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hlower : ∀ z ∈ Ω ∩ ball (0 : ℂ) 1, z ≠ 0 → δ ≤ ‖f z‖) :
    ∀ z ∈ Ω, ‖TauCeti.circleSchwarzReflection 0 1 0 1 f z‖ ≤ max M (1 / δ) := by
  intro z hz
  by_cases hzcl : z ∈ closedBall (0 : ℂ) 1
  · rw [TauCeti.circleSchwarzReflection_of_mem_closedBall 0 1 f hzcl]
    exact (hupper z ⟨hz, hzcl⟩).trans (le_max_left _ _)
  · have hzgt : 1 < dist z 0 := by simpa only [mem_closedBall, not_le] using hzcl
    have hz0 : z ≠ 0 := by rintro rfl; norm_num at hzgt
    have hinvb : inversion (0 : ℂ) 1 z ∈ ball 0 1 :=
      (TauCeti.dist_inversion_center_lt_iff one_pos hz0).mpr hzgt
    have hinv0 : inversion (0 : ℂ) 1 z ≠ 0 :=
      (inversion_eq_center one_ne_zero).not.mpr hz0
    have hl := hlower _ ⟨hsymm hz, hinvb⟩ hinv0
    rw [TauCeti.circleSchwarzReflection_of_notMem_closedBall 0 1 0 1 f hzcl,
      TauCeti.circleReflectionConjugate_apply, norm_unit_circle_inversion]
    exact (one_div_le_one_div_of_le hδ hl).trans (le_max_right _ _)

end FunctionTheory
