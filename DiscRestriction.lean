import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace AreaDeficit

/-- The Schwarz calculation underlying restriction comparison. If a
covering p restricted to a radius-r disc factors through a covering q by
a holomorphic disc map h fixing zero, then their normalised central
densities satisfy the required factor 1/r. Existence of these coverings
and of the lift h is not asserted here. -/
theorem covering_centre_restriction_bound
    {p q h : ℂ → ℂ} {p' q' : ℂ} {r : ℝ}
    (hr : 0 < r) (hp : HasDerivAt p p' 0) (hq : HasDerivAt q q' 0)
    (hp0 : p' ≠ 0) (hq0 : q' ≠ 0)
    (hh : DifferentiableOn ℂ h (ball 0 r)) (hh0 : h 0 = 0)
    (hmap : MapsTo h (ball 0 r) (ball 0 1))
    (hfactor : p =ᶠ[𝓝 0] fun z => q (h z)) :
    2 / ‖q'‖ ≤ (2 / ‖p'‖) / r := by
  have hd : DifferentiableAt ℂ h 0 := hh.differentiableAt (ball_mem_nhds _ hr)
  have hq' : HasDerivAt q q' (h 0) := by simpa only [hh0] using hq
  have he : p' = q' * deriv h 0 := by
    have hc := hq'.comp 0 hd.hasDerivAt
    exact hp.unique (hc.congr_of_eventuallyEq hfactor)
  have hm : MapsTo h (ball 0 r) (closedBall (h 0) 1) := by
    rw [hh0]
    exact hmap.mono_right ball_subset_closedBall
  have hs := Complex.norm_deriv_le_div_of_mapsTo_ball hh hm hr
  have hpq : ‖p'‖ ≤ ‖q'‖ / r := by
    rw [he, norm_mul]
    calc
      ‖q'‖ * ‖deriv h 0‖ ≤ ‖q'‖ * (1 / r) := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ = ‖q'‖ / r := by ring
  have hpn : 0 < ‖p'‖ := norm_pos_iff.mpr hp0
  have hqn : 0 < ‖q'‖ := norm_pos_iff.mpr hq0
  apply (le_div_iff₀ hr).mpr
  apply (le_div_iff₀ hpn).mpr
  have hc := (le_div_iff₀ hr).mp hpq
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hqn).mpr
  nlinarith

end AreaDeficit
