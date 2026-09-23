import FunctionTheory.Conformal.ReflectionBounds
import Mathlib.Analysis.Normed.Module.Convex

/-! # Symmetric neighbourhoods of unit-circle points

A small ball centred on the unit circle, united with its circle-reflected
image, is an open connected symmetric collar. It stays away from zero, meets
the open disk, and intersects the unit circle only in the prescribed small arc.
-/

open Set Metric EuclideanGeometry

namespace FunctionTheory

theorem exists_symmetric_circle_collar {a : ℂ} (ha : a ∈ sphere (0 : ℂ) 1)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ IsConnected Ω ∧ a ∈ Ω ∧
      MapsTo (inversion (0 : ℂ) 1) Ω Ω ∧
      (∀ z ∈ Ω, (1 / 2 : ℝ) ≤ ‖z‖) ∧
      (Ω ∩ ball (0 : ℂ) 1).Nonempty ∧
      Ω ∩ sphere (0 : ℂ) 1 ⊆ ball a ε := by
  have han : ‖a‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using ha
  have hBn (z : ℂ) (hz : z ∈ ball a ε) : (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ < 2 := by
    have hdist : ‖z - a‖ < ε := by simpa only [mem_ball, dist_eq_norm] using hz
    have hlow := norm_sub_norm_le a z
    have hupp := norm_sub_norm_le z a
    rw [han, norm_sub_rev] at hlow
    rw [han] at hupp
    constructor <;> linarith
  have hB0 (z : ℂ) (hz : z ∈ ball a ε) : z ≠ 0 := by
    intro h
    have := (hBn z hz).1
    simp only [h, norm_zero] at this
    norm_num at this
  let R : ℂ → ℂ := inversion 0 1
  have hRc : ContinuousOn R (ball a ε) :=
    continuousOn_const.inversion continuousOn_const continuousOn_id hB0
  have hRI : R '' ball a ε = R ⁻¹' ball a ε := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [mem_preimage, R, inversion_inversion _ one_ne_zero] using hw
    · intro hz
      exact ⟨R z, hz, inversion_inversion _ one_ne_zero z⟩
  have hRo : IsOpen (R '' ball a ε) := by
    rw [hRI]
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have hRz0 : R z = 0 := by simp [R, h]
      exact hB0 _ hz hRz0
    exact (continuousAt_const.inversion continuousAt_const continuousAt_id hz0)
      (isOpen_ball.mem_nhds hz)
  have hBc : IsConnected (ball a ε) := (convex_ball a ε).isConnected ⟨a, mem_ball_self hε⟩
  let Ω := ball a ε ∪ R '' ball a ε
  have haB : a ∈ ball a ε := mem_ball_self hε
  have haR : R a = a := inversion_of_mem_sphere ha
  refine ⟨Ω, isOpen_ball.union hRo,
    hBc.union ⟨a, haB, ⟨a, haB, haR⟩⟩ (hBc.image R hRc), Or.inl haB, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact Or.inr ⟨z, hz, rfl⟩
    · exact Or.inl (by simpa only [R, inversion_inversion _ one_ne_zero] using hw)
  · intro z hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact (hBn z hz).1
    · rw [show ‖R w‖ = 1 / ‖w‖ from norm_unit_circle_inversion w]
      apply (le_div_iff₀ (norm_pos_iff.mpr (hB0 w hw))).mpr
      linarith [(hBn w hw).2]
  · have hacl : a ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball _ one_ne_zero]
      exact sphere_subset_closedBall ha
    obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hacl ε hε
    exact ⟨z, Or.inl (by simpa only [mem_ball, dist_comm] using hdist), hz⟩
  · rintro z ⟨hz, hzs⟩
    rcases hz with hz | ⟨w, hw, hwz⟩
    · exact hz
    · have hwz' : w = z := by
        calc
          w = R (R w) := (inversion_inversion _ one_ne_zero w).symm
          _ = R z := congrArg R hwz
          _ = z := inversion_of_mem_sphere hzs
      exact hwz' ▸ hw

end FunctionTheory
