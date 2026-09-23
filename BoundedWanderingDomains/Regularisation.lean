import BoundedWanderingDomains.AreaDeficitCore
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal

namespace AreaDeficit

noncomputable def beta (t : ℝ) : ℝ := ∫ s in 0..t, Real.smoothTransition s

theorem beta_hasDerivAt (t : ℝ) : HasDerivAt beta (Real.smoothTransition t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (Real.smoothTransition.continuous.intervalIntegrable _ _)
    (Real.smoothTransition.continuous.stronglyMeasurableAtFilter _ _)
    Real.smoothTransition.continuousAt

theorem beta_deriv : deriv beta = Real.smoothTransition := by
  funext t
  exact (beta_hasDerivAt t).deriv

theorem beta_contDiff : ContDiff ℝ ∞ beta := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun t => (beta_hasDerivAt t).differentiableAt,
    by rw [beta_deriv]; exact Real.smoothTransition.contDiff⟩

theorem transition_hasDerivAt (t : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
  ((@Real.smoothTransition.contDiff 1).differentiable (by norm_num) t).hasDerivAt

theorem transition_deriv_nonneg (t : ℝ) : 0 ≤ deriv Real.smoothTransition t :=
  (transition_hasDerivAt t).nonneg_of_monotone Real.smoothTransition.monotone

theorem beta_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : beta t = 0 := by
  unfold beta
  apply intervalIntegral.integral_zero_ae
  filter_upwards with s hs
  apply Real.smoothTransition.zero_of_nonpos
  simp only [uIoc_of_ge ht, mem_Ioc] at hs
  exact hs.2

theorem beta_bounds (t : ℝ) : 0 ≤ beta t ∧ beta t ≤ max t 0 := by
  by_cases ht : t ≤ 0
  · simp [beta_zero_of_nonpos ht, max_eq_right ht]
  · have ht0 : 0 ≤ t := le_of_not_ge ht
    rw [max_eq_left ht0]
    constructor
    · exact intervalIntegral.integral_nonneg ht0 (fun s _ => Real.smoothTransition.nonneg s)
    · have h := intervalIntegral.integral_mono_on ht0
        (Real.smoothTransition.continuous.intervalIntegrable 0 t)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t)
        (fun s _ => Real.smoothTransition.le_one s)
      simpa [beta] using h

noncomputable def betaScaled (n : ℕ) (t : ℝ) : ℝ :=
  beta (((n : ℝ) + 1) * t) / ((n : ℝ) + 1)

theorem betaScaled_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (betaScaled n) (Real.smoothTransition (((n : ℝ) + 1) * t)) t := by
  have ha : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold betaScaled
  convert ((beta_hasDerivAt (((n : ℝ) + 1) * t)).comp t
    ((hasDerivAt_id t).const_mul ((n : ℝ) + 1))).div_const ((n : ℝ) + 1) using 1 <;>
    simp [ha]

theorem betaScaled_contDiff (n : ℕ) : ContDiff ℝ ∞ (betaScaled n) := by
  exact (beta_contDiff.comp (contDiff_const.mul contDiff_id)).div_const _

theorem betaScaled_bounds (n : ℕ) (t : ℝ) :
    0 ≤ betaScaled n t ∧ betaScaled n t ≤ max t 0 := by
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb := beta_bounds (((n : ℝ) + 1) * t)
  constructor
  · exact div_nonneg hb.1 ha.le
  · unfold betaScaled
    apply (div_le_iff₀ ha).mpr
    by_cases ht : 0 ≤ t
    · rw [max_eq_left (mul_nonneg ha.le ht)] at hb
      simpa only [max_eq_left ht, mul_comm] using hb.2
    · have ht0 : t ≤ 0 := le_of_not_ge ht
      simpa [max_eq_right ht0, max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha.le ht0)] using hb.2

theorem transition_scaled_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => Real.smoothTransition (((n : ℝ) + 1) * u)) atTop
      (𝓝 (if 0 < u then 1 else 0)) := by
  by_cases hu : 0 < u
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / u)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnr : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    have hnu : 1 < (N : ℝ) * u := (div_lt_iff₀ hu).mp hN
    simp only [ite_eq_left hu]
    exact (Real.smoothTransition.one_of_one_le (by nlinarith)).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards with n
    simp only [ite_eq_right hu]
    exact (Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hu))).symm

end AreaDeficit
