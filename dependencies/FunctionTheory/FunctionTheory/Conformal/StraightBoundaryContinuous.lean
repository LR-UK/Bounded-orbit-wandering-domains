import FunctionTheory.Conformal.StraightBoundaryCoordinates

open Set Metric Complex Filter
open scoped Topology

namespace FunctionTheory

theorem mem_closure_right_half_ball {c : ℂ} {R : ℝ}
    (hc : ‖c‖ < R) (hre : 0 ≤ c.re) :
    c ∈ closure (ball (0 : ℂ) R ∩ {z : ℂ | 0 < z.re}) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t : ℝ := min ε (R - ‖c‖) / 2
  have ht : 0 < t := half_pos (lt_min hε (sub_pos.mpr hc))
  have htε : t < ε := lt_of_lt_of_le (half_lt_self (lt_min hε (sub_pos.mpr hc))) (min_le_left _ _)
  have htR : t < R - ‖c‖ := lt_of_lt_of_le (half_lt_self (lt_min hε (sub_pos.mpr hc))) (min_le_right _ _)
  refine ⟨c + (t : ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_zero_right]
    calc
      ‖c + (t : ℂ)‖ ≤ ‖c‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ = ‖c‖ + t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      _ < R := by linarith
  · change 0 < (c + (t : ℂ)).re
    simpa only [Complex.add_re, Complex.ofReal_re] using add_pos_of_nonneg_of_pos hre ht
  · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact htε

/-- A disk map extends continuously from either chosen side of a straight
boundary to a smaller closed half-neighbourhood. Its boundary values lie on
the unit circle, even if the original domain also occupies the other side. -/
theorem exists_continuous_extension_at_straight_side
    {U : Set ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R)
    (hhalf : ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → z ∈ U)
    (hline : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → z ∉ U) :
    ∃ F : ℂ → ℂ,
      ContinuousOn F (ball 0 (R / 2) ∩ {z : ℂ | 0 ≤ z.re}) ∧
      EqOn F f (ball 0 (R / 2) ∩ {z : ℂ | 0 < z.re}) ∧
      ∀ z ∈ ball (0 : ℂ) (R / 2), z.re = 0 → F z ∈ sphere (0 : ℂ) 1 := by
  let S : Set ℂ := ball 0 R ∩ {z : ℂ | 0 < z.re}
  let B : Set ℂ := ball 0 (R / 2) ∩ {z : ℂ | 0 ≤ z.re}
  have hSU : S ⊆ U := fun z hz => hhalf z hz.1 hz.2
  have hBS : B ⊆ closure S := by
    intro z hz
    exact mem_closure_right_half_ball
      ((mem_ball_zero_iff.mp hz.1).trans (half_lt_self hR)) hz.2
  have hlim (c : ℂ) (hc : c ∈ ball (0 : ℂ) (R / 2)) (hc0 : c.re = 0) :
      ∃ a ∈ sphere (0 : ℂ) 1, Tendsto f (𝓝[S] c) (𝓝 a) := by
    have hsum (z : ℂ) (hz : z ∈ ball (0 : ℂ) (R / 2)) : c + 1 * z ∈ ball (0 : ℂ) R := by
      rw [one_mul, mem_ball, dist_zero_right]
      exact (norm_add_le _ _).trans_lt (by
        have hc' := mem_ball_zero_iff.mp hc
        have hz' := mem_ball_zero_iff.mp hz
        linarith)
    obtain ⟨a, ha, hfa⟩ := exists_boundary_limit_at_straight_side_in_coordinates
      hU hf hbij (c := c) (α := 1) one_ne_zero (half_pos hR)
      (fun z hz hz0 => hhalf _ (hsum z hz) (by simpa [hc0] using hz0))
      (fun z hz hz0 => hline _ (hsum z hz) (by simp [hc0, hz0]))
    refine ⟨a, ha, hfa.mono_left (nhdsWithin_mono _ ?_)⟩
    intro z hz
    exact ⟨hSU hz, by simpa [hc0] using hz.2⟩
  have hall : ∀ c ∈ B, ∃ a, Tendsto f (𝓝[S] c) (𝓝 a) := by
    intro c hc
    rcases eq_or_lt_of_le (show 0 ≤ c.re from hc.2) with hc0 | hcpos
    · obtain ⟨a, -, ha⟩ := hlim c hc.1 hc0.symm
      exact ⟨a, ha⟩
    · exact ⟨f c, (hf.continuousOn.continuousAt (hU.mem_nhds
        (hhalf c (ball_subset_ball (half_le_self hR.le) hc.1) hcpos))).mono_left nhdsWithin_le_nhds⟩
  refine ⟨extendFrom S f, continuousOn_extendFrom hBS hall, ?_, ?_⟩
  · intro z hz
    exact extendFrom_extends (hf.continuousOn.mono hSU) z
      ⟨ball_subset_ball (half_le_self hR.le) hz.1, hz.2⟩
  · intro z hz hz0
    obtain ⟨a, ha, hfa⟩ := hlim z hz hz0
    rwa [extendFrom_eq (hBS ⟨hz, hz0.ge⟩) hfa]

end FunctionTheory
