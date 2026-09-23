import DiscMetric
import RiemannMappingFull

open Set Metric Function Filter
open scoped Topology ComplexConjugate

namespace AreaDeficit

/-- Schwarz–Pick at the centre of a disc of radius r. -/
theorem disc_schwarz_centre {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r))
    (hm : MapsTo g (ball 0 r) (ball 0 1)) :
    discDensity (g 0) * ‖deriv g 0‖ ≤ 2 / r := by
  classical
  let F : ℂ → Complex.UnitDisc := fun z =>
    if hz : z ∈ ball (0 : ℂ) r then ⟨g z, hm hz⟩ else 0
  have hF : EqOn (fun z => (F z : ℂ)) g (ball 0 r) := by
    intro z hz
    change (F z).val = g z
    dsimp [F]
    simp_all
  have hF0 : (F 0 : ℂ) = g 0 := hF (mem_ball_self hr)
  have hFeq : (fun z => (F z : ℂ)) =ᶠ[𝓝 0] g :=
    Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) hr) hF
  have hFd : DifferentiableOn ℂ (fun z => (F z : ℂ)) (ball 0 r) := hg.congr hF
  let h : ℂ → ℂ := fun z => ((-F 0).shift (F z) : ℂ)
  have hh : DifferentiableOn ℂ h (ball 0 r) :=
    (Complex.UnitDisc.differentiableOn_shift_comp_iff (-F 0)).mpr hFd
  have hh0 : h 0 = 0 := by simp [h]
  have hmap : MapsTo h (ball 0 r) (closedBall (h 0) 1) := by
    intro z hz
    rw [hh0, mem_closedBall_zero_iff]
    exact ((-F 0).shift (F z)).norm_lt_one.le
  have hs := Complex.norm_deriv_le_div_of_mapsTo_ball hh hmap hr
  have hnorm : ‖g 0‖ < 1 := mem_ball_zero_iff.mp (hm (mem_ball_self hr))
  have hden : 0 < 1 - ‖g 0‖^2 := by nlinarith [norm_nonneg (g 0)]
  have he : deriv h 0 = (1 - (‖g 0‖ : ℂ)^2)⁻¹ * deriv g 0 := by
    rw [show deriv h 0 = _ from Complex.UnitDisc.deriv_shift_comp F 0 (-F 0)]
    rw [hFeq.deriv_eq]
    simp only [Complex.UnitDisc.coe_neg, norm_neg, hF0, map_neg, neg_mul, ← sub_eq_add_neg,
      Complex.conj_mul']
    field_simp
  have hnn : ‖(1 - (‖g 0‖ : ℂ)^2)⁻¹‖ = (1 - ‖g 0‖^2)⁻¹ := by
    rw [norm_inv]
    have hcast : 1 - (‖g 0‖ : ℂ)^2 = ((1 - ‖g 0‖^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  rw [he, norm_mul, hnn] at hs
  unfold discDensity discDenom
  rw [Complex.normSq_eq_norm_sq]
  calc
    2 / (1 - ‖g 0‖^2) * ‖deriv g 0‖ = 2 * ((1 - ‖g 0‖^2)⁻¹ * ‖deriv g 0‖) := by ring
    _ ≤ 2 * (1 / r) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = 2 / r := by ring

end AreaDeficit

#print axioms AreaDeficit.disc_schwarz_centre
