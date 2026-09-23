import BoundedWanderingDomains.DiscMetric
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Filter InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

theorem pd_comp_holomorphic {u : ℂ → ℝ} {f : ℂ → ℂ} {x v : ℂ}
    (hu : DifferentiableAt ℝ u (f x)) (hf : DifferentiableAt ℂ f x) :
    pd (u ∘ f) v x = fderiv ℝ u (f x) (deriv f x * v) := by
  have H := (hu.hasFDerivAt.comp x (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ)).fderiv
  unfold pd
  rw [H]
  simp [ContinuousLinearMap.comp_apply, mul_comm]

theorem pd2_comp_holomorphic {u : ℂ → ℝ} {f : ℂ → ℂ} {x v : ℂ}
    (hu : ContDiffAt ℝ 2 u (f x)) (hf : AnalyticAt ℂ f x) :
    pd (pd (u ∘ f) v) v x =
      fderiv ℝ (fderiv ℝ u) (f x) (deriv f x * v) (deriv f x * v) +
      fderiv ℝ u (f x) (deriv (deriv f) x * v * v) := by
  have he : pd (u ∘ f) v =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u (f y) (deriv f y * v)) := by
    filter_upwards [hf.eventually_analyticAt,
      hf.continuousAt.tendsto.eventually (hu.eventually (by norm_num))] with y hfy huy
    exact pd_comp_holomorphic (huy.differentiableAt (by norm_num)) hfy.differentiableAt
  have hu' : DifferentiableAt ℝ (fderiv ℝ u) (f x) :=
    (hu.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hfr := hf.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hleft := hu'.hasFDerivAt.comp x hfr
  have hright := ((hf.deriv.differentiableAt.hasDerivAt).mul_const v).hasFDerivAt.restrictScalars ℝ
  have H := hleft.clm_apply hright
  simp only [Function.comp_def] at H
  change fderiv ℝ (pd (u ∘ f) v) x v = _
  rw [he.fderiv_eq, H.fderiv]
  simp [ContinuousLinearMap.comp_apply, mul_comm, add_comm]

theorem laplacian_comp_holomorphic {u : ℂ → ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hu : ContDiffAt ℝ 2 u (f x)) (hf : AnalyticAt ℂ f x) :
    Δ (u ∘ f) x = ‖deriv f x‖^2 * Δ u (f x) := by
  have hcomp : ContDiffAt ℝ 2 (u ∘ f) x :=
    hu.comp x (hf.contDiffAt.restrict_scalars ℝ)
  rw [laplacian_eq_pd2 hcomp, pd2_comp_holomorphic hu hf,
    pd2_comp_holomorphic hu hf]
  have hess (v : ℂ) : pd (pd u v) v (f x) =
      fderiv ℝ (fderiv ℝ u) (f x) v v := by
    have hd : DifferentiableAt ℝ (fderiv ℝ u) (f x) :=
      (hu.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
    unfold pd
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [laplacian_eq_pd2 hu, hess, hess]
  let d := deriv f x
  have hd : d = d.re • (1 : ℂ) + d.im • Complex.I := by simp
  have hdi : d * Complex.I = (-d.im) • (1 : ℂ) + d.re • Complex.I := by
    apply Complex.ext <;> simp
  change _ = ‖d‖^2 * _
  simp only [mul_one]
  have hz : deriv (deriv f) x * Complex.I * Complex.I = -deriv (deriv f) x := by
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
  rw [hz, map_neg]
  calc
    _ = fderiv ℝ (fderiv ℝ u) (f x) d d +
        fderiv ℝ (fderiv ℝ u) (f x) (d * Complex.I) (d * Complex.I) := by
      dsimp [d]
      ring
    _ = _ := by
      rw [hdi]
      conv_lhs => rw [hd]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
        Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring

/-- Pullback by a locally conformal holomorphic map preserves the
curvature −1 equation. This is proved by the ordinary Laplacian chain
rule above, not included among the classical metric assumptions. -/
theorem pullback_density_curvature {rho : ℂ → ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hr : ContDiffAt ℝ 2 rho (f x)) (hrpos : 0 < rho (f x))
    (hcurv : Δ (fun w => Real.log (rho w)) (f x) = (rho (f x))^2)
    (hf : AnalyticAt ℂ f x) (hreg : deriv f x ≠ 0) :
    Δ (fun w => Real.log (‖deriv f w‖ * rho (f w))) x =
      (‖deriv f x‖ * rho (f x))^2 := by
  have hh := hf.deriv.harmonicAt_log_norm hreg
  have hlog := hr.log (ne_of_gt hrpos)
  have he : (fun w => Real.log (‖deriv f w‖ * rho (f w))) =ᶠ[𝓝 x]
      (fun w => Real.log ‖deriv f w‖ + Real.log (rho (f w))) := by
    filter_upwards [hf.deriv.continuousAt.eventually_ne hreg,
      (hr.continuousAt.comp hf.continuousAt).eventually_ne (ne_of_gt hrpos)] with w hd hrw
    exact Real.log_mul (norm_ne_zero_iff.mpr hd) hrw
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  have hc : ContDiffAt ℝ 2 (fun w => Real.log (rho (f w))) x :=
    hlog.comp x (hf.contDiffAt.restrict_scalars ℝ)
  have hadd := hh.1.laplacian_add hc
  simp only [Pi.add_def] at hadd
  rw [hadd, hh.2.eq_of_nhds]
  have H := laplacian_comp_holomorphic hlog hf
  simpa only [Function.comp_def, hcurv, Pi.zero_apply, zero_add, mul_pow] using H

theorem pullback_density_contDiffAt {rho : ℂ → ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hr : ContDiffAt ℝ 2 rho (f x)) (hf : AnalyticAt ℂ f x)
    (hreg : deriv f x ≠ 0) :
    ContDiffAt ℝ 2 (fun w => ‖deriv f w‖ * rho (f w)) x := by
  have hd : ContDiffAt ℝ 2 (deriv f) x := hf.deriv.contDiffAt.restrict_scalars ℝ
  exact (hd.norm ℝ hreg).mul
    (hr.comp x (hf.contDiffAt.restrict_scalars ℝ))

end AreaDeficit

#print axioms AreaDeficit.pullback_density_curvature
