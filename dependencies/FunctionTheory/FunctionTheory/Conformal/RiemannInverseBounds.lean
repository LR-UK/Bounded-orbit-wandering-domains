import FunctionTheory.Conformal.RiemannMapping
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.NormalFamilies

/-! # Nondegeneration of inverse Riemann maps

A common disk in the source gives a uniform positive lower bound for the
derivatives of inverse Riemann maps. This is Cauchy's derivative estimate,
applied to the disk-valued direct map, followed by the inverse derivative rule.
-/

open Set Metric Function
open scoped Topology ComplexOrder

namespace FunctionTheory

theorem normalized_inverse_derivative_lower_bound
    {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hU : IsOpen U) (hf : TauCeti.IsNormalizedRiemannMapOn f U z₀)
    (hr : 0 < r) (hball : closedBall z₀ r ⊆ U) :
    r ≤ ‖deriv (invFunOn f U) 0‖ := by
  have hdf : 0 < ‖deriv f z₀‖ := norm_pos_iff.mpr hf.deriv_pos.ne'
  have hbound : ‖deriv f z₀‖ ≤ 1 / r :=
    TauCeti.norm_deriv_le_of_forall_mem_closedBall_norm_le hf.differentiableOn hr hball
      (fun z hz => (mem_ball_zero_iff.mp (hf.mapsTo (hball hz))).le)
  have hinv : deriv (invFunOn f U) 0 = (deriv f z₀)⁻¹ := by
    simpa only [hf.map_base] using
      (TauCeti.hasDerivAt_invFunOn hf.differentiableOn hU hf.injOn hf.base_mem).deriv
  rw [hinv, norm_inv, inv_eq_one_div]
  apply (le_div_iff₀ hdf).mpr
  have h := (le_div_iff₀ hr).mp hbound
  nlinarith

end FunctionTheory
