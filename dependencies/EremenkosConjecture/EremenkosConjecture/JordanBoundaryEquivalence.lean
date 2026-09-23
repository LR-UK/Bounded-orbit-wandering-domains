import EremenkosConjecture.JordanBoundaryCompatibility
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Set

namespace EremenkosConjecture

/-- The circle-homeomorphism and interval-loop definitions of a Jordan curve
agree. This supplies the reverse direction of the existing compatibility map
without changing either public formalisation's definition. -/
theorem schoenflies_isJordanCurve_of_tauCeti {C : Set Schoenflies.Plane}
    (hC : TauCeti.IsJordanCurve C) : Schoenflies.IsJordanCurve C := by
  obtain ⟨e⟩ := TauCeti.isJordanCurve_iff.mp hC
  let p : ℝ → Circle := fun t => Circle.exp (2 * Real.pi * t)
  have hp : Continuous p := Circle.exp.continuous.comp (continuous_const.mul continuous_id)
  have hp_image : p '' Icc 0 1 = univ := by
    have hscale : (fun t : ℝ => 2 * Real.pi * t) '' Icc 0 1 = Icc 0 (2 * Real.pi) := by
      ext θ
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨mul_nonneg Real.two_pi_pos.le ht.1,
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 Real.two_pi_pos.le⟩
      · intro hθ
        refine ⟨θ / (2 * Real.pi), ⟨div_nonneg hθ.1 Real.two_pi_pos.le,
          (div_le_one Real.two_pi_pos).mpr hθ.2⟩, ?_⟩
        exact mul_div_cancel₀ _ Real.two_pi_pos.ne'
    change (Circle.exp ∘ fun t : ℝ => 2 * Real.pi * t) '' Icc 0 1 = univ
    rw [image_comp, hscale]
    simpa only [zero_add, Circle.exp_surjective.range_eq] using
      Circle.periodic_exp.image_Icc Real.two_pi_pos 0
  refine ⟨TauCeti.jordanParam e ∘ p, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact ((TauCeti.continuous_jordanParam e).comp hp).continuousOn
  · simp [Function.comp_def, p]
  · intro s hs t ht he
    have he' := TauCeti.jordanParam_injective e he
    have hangle := Circle.exp_injOn_Ico
      (a := 0) (b := 2 * Real.pi) (by simp)
      (show 2 * Real.pi * s ∈ Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg Real.two_pi_pos.le hs.1, by nlinarith [Real.pi_pos, hs.2]⟩)
      (show 2 * Real.pi * t ∈ Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg Real.two_pi_pos.le ht.1, by nlinarith [Real.pi_pos, ht.2]⟩) he'
    exact mul_left_cancel₀ Real.two_pi_pos.ne' hangle
  · rw [image_comp, hp_image, image_univ, TauCeti.range_jordanParam]

theorem isComplexJordanCurve_of_tauCeti {C : Set ℂ} (hC : TauCeti.IsJordanCurve C) :
    IsComplexJordanCurve C :=
  schoenflies_isJordanCurve_of_tauCeti (hC.image_homeomorph complexPlaneHomeomorph)

theorem isComplexJordanCurve_iff_tauCeti {C : Set ℂ} :
    IsComplexJordanCurve C ↔ TauCeti.IsJordanCurve C :=
  ⟨fun h => h.tauCeti, isComplexJordanCurve_of_tauCeti⟩

end EremenkosConjecture
