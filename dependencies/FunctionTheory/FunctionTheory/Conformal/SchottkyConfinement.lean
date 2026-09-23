import FunctionTheory.Conformal.SchottkyDisc
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Uniform confinement near the centre of an omitted-values disc map

Schottky bounds the images of the half-disc in terms of the central value.
Schwarz's lemma then gives a uniform bound for displacement from that value.
In particular, the radius is independent of any additional omitted values.
-/

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Uniform displacement on the half-disc for maps omitting zero and one. -/
theorem schottky_centre_displacement {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hzero : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    (hone : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1)
    (hbase : ‖f 0‖ ≤ R) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    ‖f z - f 0‖ ≤
      (2 * (schottkyZeroOneMajorant R (1 / 2) + R)) * ‖z‖ := by
  have hsub : ball (0 : ℂ) (1 / 2) ⊆ ball (0 : ℂ) 1 :=
    ball_subset_ball (by norm_num)
  have hmap : MapsTo f (ball (0 : ℂ) (1 / 2))
      (closedBall (f 0) (schottkyZeroOneMajorant R (1 / 2) + R)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (add_le_add
      (norm_le_schottkyZeroOneMajorant (by norm_num) (by norm_num)
        hf hzero hone hbase (mem_ball_zero_iff.mp hw).le) hbase)
  have H := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    (hf.differentiableOn.mono hsub) hmap (mem_ball_zero_iff.mpr hz)
  simpa only [dist_eq_norm, sub_zero, div_div_eq_mul_div, div_one,
    mul_comm (2 : ℝ)] using H

/-- A source radius uniform over all maps with bounded central value. -/
theorem exists_uniform_radius_of_two_omitted_values (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1) →
      ‖f 0‖ ≤ R → MapsTo f (ball (0 : ℂ) r) (ball (f 0) ε) := by
  let C := 2 * (schottkyZeroOneMajorant R (1 / 2) + R)
  let D := max C 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨min (1 / 4) (ε / D), lt_min (by norm_num) (div_pos hε hD),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro f hf hzero hone hbase z hz
  have hzn := mem_ball_zero_iff.mp hz
  have hzhalf : ‖z‖ < 1 / 2 := hzn.trans_le
    ((min_le_left _ _).trans (by norm_num))
  rw [mem_ball, dist_eq_norm]
  calc
    ‖f z - f 0‖ ≤ C * ‖z‖ := schottky_centre_displacement hf hzero hone hbase hzhalf
    _ ≤ D * ‖z‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ < D * (ε / D) := mul_lt_mul_of_pos_left
      (hzn.trans_le (min_le_right _ _)) hD
    _ = ε := mul_div_cancel₀ _ hD.ne'

/-- Compact central values give a uniform radius, without a separation
assumption between that compact set and the two omitted values. -/
theorem exists_uniform_radius_of_compact_centres {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1) →
      f 0 ∈ K → MapsTo f (ball (0 : ℂ) r) (ball (f 0) ε) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨r, hr, hr1, H⟩ := exists_uniform_radius_of_two_omitted_values R hε
  exact ⟨r, hr, hr1, fun f hf hzero hone hbase => H f hf hzero hone (hR _ hbase)⟩

/-- The same conclusion for any two distinct finite omitted values. The
constant depends on the values and central compact set, not on the map. -/
theorem exists_uniform_radius_of_compact_centres_omit_pair
    {K : Set ℂ} (hK : IsCompact K) {a b : ℂ} (hab : a ≠ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ a) →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ b) →
      f 0 ∈ K → MapsTo f (ball (0 : ℂ) r) (ball (f 0) ε) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hn : 0 < ‖b - a‖ := norm_pos_iff.mpr hba
  let T : ℂ → ℂ := fun w => (w - a) / (b - a)
  have hT : Continuous T := by dsimp [T]; fun_prop
  obtain ⟨r, hr, hr1, H⟩ := exists_uniform_radius_of_compact_centres
    (hK.image hT) (div_pos hε hn)
  refine ⟨r, hr, hr1, ?_⟩
  intro f hf ha hb hfK z hz
  have hg : AnalyticOnNhd ℂ (fun w => T (f w)) (ball (0 : ℂ) 1) :=
    (hf.sub analyticOnNhd_const).div_const
  have hg0 : ∀ w ∈ ball (0 : ℂ) 1, T (f w) ≠ 0 := by
    intro w hw
    exact div_ne_zero (sub_ne_zero.mpr (ha w hw)) hba
  have hg1 : ∀ w ∈ ball (0 : ℂ) 1, T (f w) ≠ 1 := by
    intro w hw he
    have he' : f w - a = b - a := (div_eq_one_iff_eq hba).mp he
    exact hb w hw (sub_left_injective he')
  have H' := H (fun w => T (f w)) hg hg0 hg1 (mem_image_of_mem T hfK) hz
  rw [mem_ball, dist_eq_norm] at H' ⊢
  have he : T (f z) - T (f 0) = (f z - f 0) / (b - a) := by
    dsimp [T]
    ring
  rw [he, norm_div] at H'
  exact (div_lt_div_iff_of_pos_right hn).mp H'

end FunctionTheory
