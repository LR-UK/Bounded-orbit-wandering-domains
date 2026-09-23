import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
import FunctionTheory.Conformal.StripCoordinates
import Mathlib.Topology.Order.IntermediateValue

open Set Metric Complex

namespace FunctionTheory

/-- A small boundary cap containing the zero barrier also contains the whole
side separated from a positive reference point. No boundary convergence of
the maps is required. -/
theorem nonpositive_side_subset_boundary_cap
    {q : ℂ → ℝ} {a b : ℂ} {δ : ℝ}
    (hq : ContinuousOn q (ball 0 1)) (ha : a ∈ sphere (0 : ℂ) 1)
    (hδ : 0 < δ) (hδ2 : δ < 2)
    (hb : b ∈ ball (0 : ℂ) 1 \ closedBall a δ) (hqb : 0 < q b)
    (hzero : ∀ w ∈ ball (0 : ℂ) 1, q w = 0 → w ∈ closedBall a δ) :
    {w ∈ ball (0 : ℂ) 1 | q w ≤ 0} ⊆ closedBall a δ := by
  intro w hw
  by_contra hout
  have hc := (TauCeti.isConnected_ball_diff_closedBall ha hδ (by simpa using hδ2)).isPreconnected
  obtain ⟨v, hv, hvq⟩ := hc.intermediate_value ⟨hw.1, hout⟩ hb
    (hq.mono sdiff_subset) ⟨hw.2, hqb.le⟩
  exact hv.2 (hzero v hv.1 hvq)

/-- Disk points close to minus one have uniformly large negative real part
in strip coordinates, even when approaching the horizontal strip boundary. -/
theorem re_discToHorizontalStrip_le_log_of_mem_left_cap
    {w : ℂ} {δ : ℝ} (hw : w ∈ ball (0 : ℂ) 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcap : w ∈ closedBall (-1 : ℂ) δ) :
    (discToHorizontalStrip w).re ≤ Real.log δ := by
  have hd : 0 < ‖1 + w‖ := norm_pos_iff.mpr (cayley_denominator_ne_zero_of_mem_ball hw)
  have hden : ‖1 + w‖ ≤ δ := by simpa [dist_eq_norm, add_comm] using hcap
  have hsum : (1 - w) + (1 + w) = (2 : ℂ) := by ring
  have hnum : 1 ≤ ‖1 - w‖ := by
    have hn := norm_add_le (1 - w) (1 + w)
    rw [hsum] at hn
    norm_num at hn
    linarith
  have hratio : δ⁻¹ ≤ ‖cayleyCoordinate w‖ := by
    rw [cayleyCoordinate, norm_div]
    apply (le_div_iff₀ hd).mpr
    have hprod : δ⁻¹ * ‖1 + w‖ ≤ 1 := by
      calc δ⁻¹ * ‖1 + w‖ ≤ δ⁻¹ * δ := mul_le_mul_of_nonneg_left hden (inv_nonneg.mpr hδ.le)
           _ = 1 := inv_mul_cancel₀ hδ.ne'
    exact hprod.trans hnum
  have hlog := Real.log_le_log (inv_pos.mpr hδ) hratio
  rw [Real.log_inv] at hlog
  change -(log (cayleyCoordinate w)).re ≤ Real.log δ
  rw [log_re]
  linarith

/-- A continuous inverse transports the disk barrier criterion to the source
domain. The conclusion is uniform on an arbitrary set on the left side. -/
theorem leftward_strip_bound_of_separating_barrier
    {U X : Set ℂ} {f g : ℂ → ℂ} {q : ℂ → ℝ} {b : ℂ} {δ : ℝ}
    (hg : ContinuousOn g (ball 0 1)) (hgU : MapsTo g (ball 0 1) U)
    (hq : ContinuousOn q U) (hfg : RightInvOn g f (ball 0 1))
    (hfX : MapsTo f X (ball 0 1)) (hgfX : LeftInvOn g f X)
    (hX : ∀ x ∈ X, q x ≤ 0)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hb : b ∈ ball (0 : ℂ) 1 \ closedBall (-1 : ℂ) δ) (hqb : 0 < q (g b))
    (hzero : ∀ z ∈ U, q z = 0 → f z ∈ closedBall (-1 : ℂ) δ) :
    ∀ x ∈ X, (discToHorizontalStrip (f x)).re ≤ Real.log δ := by
  have hcap := nonpositive_side_subset_boundary_cap (hq.comp hg hgU)
    (a := (-1 : ℂ)) (by simp) hδ (by linarith) hb hqb (by
      intro w hw hqw
      simpa only [hfg hw] using hzero (g w) (hgU hw) hqw)
  intro x hx
  apply re_discToHorizontalStrip_le_log_of_mem_left_cap (hfX hx) hδ hδ1.le
  apply hcap
  exact ⟨hfX hx, by simpa only [Function.comp_apply, hgfX hx] using hX x hx⟩

end FunctionTheory
