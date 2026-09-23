import BoundedWanderingDomains.LaplacianChain
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set Filter InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

/-- The scalar chain rule only needs derivative identities near the value
u(x). This permits logarithms, whose derivative identity fails at zero. -/
theorem pd2_comp_local {u : ℂ → ℝ} {B B₁ : ℝ → ℝ} {b₂ : ℝ} {x : ℂ}
    (hu : ContDiffAt ℝ 2 u x)
    (hB : ∀ᶠ t in 𝓝 (u x), HasDerivAt B (B₁ t) t)
    (hB₁ : HasDerivAt B₁ b₂ (u x)) (v : ℂ) :
    pd (pd (fun y => B (u y)) v) v x =
      B₁ (u x) * pd (pd u v) v x + b₂ * (pd u v x)^2 := by
  have heq : pd (fun y => B (u y)) v =ᶠ[𝓝 x]
      (fun y => B₁ (u y) * pd u v y) := by
    filter_upwards [hu.eventually (by norm_num), hu.continuousAt.tendsto.eventually hB]
      with y hy hby
    exact pd_comp (hy.differentiableAt (by norm_num)) hby
  have hdu := hu.differentiableAt (by norm_num)
  have hdpu := (pd_contDiffAt (n := 1) hu v).differentiableAt (by norm_num)
  have hp := (hB₁.comp_hasFDerivAt x hdu.hasFDerivAt).mul hdpu.hasFDerivAt
  simp only [Function.comp_def, Pi.mul_def, pd] at hp
  unfold pd at heq ⊢
  rw [heq.fderiv_eq, hp.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change B₁ (u x) * pd (pd u v) v x + pd u v x * (b₂ * pd u v x) =
    B₁ (u x) * pd (pd u v) v x + b₂ * (pd u v x)^2
  ring

theorem laplacian_log {u : ℂ → ℝ} {x : ℂ}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x ≠ 0) :
    Δ (fun z => Real.log (u z)) x =
      (u x)⁻¹ * Δ u x - (u x)⁻¹^2 * gradientSq u x := by
  have hb : ∀ᶠ t in 𝓝 (u x), HasDerivAt Real.log t⁻¹ t := by
    filter_upwards [eventually_ne_nhds hx] with t ht
    exact Real.hasDerivAt_log ht
  have hb₁ : HasDerivAt (fun t : ℝ => t⁻¹) (-((u x)⁻¹^2)) (u x) := by
    convert hasDerivAt_inv hx using 1
    simp [inv_pow]
  rw [laplacian_eq_pd2 (hu.log hx), pd2_comp_local hu hb hb₁,
    pd2_comp_local hu hb hb₁, laplacian_eq_pd2 hu]
  unfold gradientSq
  ring

noncomputable def discDenom (z : ℂ) : ℝ := 1 - Complex.normSq z
noncomputable def discDensity (z : ℂ) : ℝ := 2 / discDenom z

theorem discDenom_contDiff : ContDiff ℝ ∞ discDenom := by
  exact contDiff_const.sub ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))

theorem pd_discDenom (z v : ℂ) :
    pd discDenom v z = -2 * (z.re * v.re + z.im * v.im) := by
  have hr : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have hi : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hd := (hr.mul hr).add (hi.mul hi)
  have hh := (hasFDerivAt_const (1 : ℝ) z).sub hd
  simp only [Pi.sub_def, Pi.add_def, Pi.mul_def] at hh
  change fderiv ℝ (fun w : ℂ => 1 - (w.re * w.re + w.im * w.im)) z v = _
  rw [hh.fderiv]
  simp
  ring

theorem pd2_discDenom (z v : ℂ) :
    pd (pd discDenom v) v z = -2 * (v.re^2 + v.im^2) := by
  have he : pd discDenom v = fun w : ℂ => -2 * (w.re * v.re + w.im * v.im) :=
    funext (fun w => pd_discDenom w v)
  rw [he]
  have hr : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have hi : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hh := ((hr.mul_const v.re).add (hi.mul_const v.im)).const_mul (-2)
  simp only [Pi.add_def] at hh
  unfold pd
  rw [hh.fderiv]
  simp
  ring

theorem laplacian_discDenom (z : ℂ) : Δ discDenom z = -4 := by
  rw [laplacian_eq_pd2 (discDenom_contDiff.of_le (by simp)).contDiffAt,
    pd2_discDenom, pd2_discDenom]
  norm_num

theorem gradientSq_discDenom (z : ℂ) : gradientSq discDenom z = 4 * Complex.normSq z := by
  simp only [gradientSq, pd_discDenom, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

theorem discDensity_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < discDensity z := by
  have hs : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  exact div_pos (by norm_num) (sub_pos.mpr hs)

/-- The actual curvature equation for the curvature −1 disc density. -/
theorem discDensity_curvature {z : ℂ} (hz : ‖z‖ < 1) :
    Δ (fun w => Real.log (discDensity w)) z = (discDensity z)^2 := by
  have hs : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hd : discDenom z ≠ 0 := ne_of_gt (sub_pos.mpr hs)
  have he : (fun w => Real.log (discDensity w)) =ᶠ[𝓝 z]
      (fun w => Real.log 2 - Real.log (discDenom w)) := by
    filter_upwards [discDenom_contDiff.continuous.continuousAt.eventually_ne hd] with w hw
    exact Real.log_div (by norm_num) hw
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  have hc : ContDiffAt ℝ 2 (fun w => Real.log (discDenom w)) z :=
    (discDenom_contDiff.of_le (by simp)).contDiffAt.log hd
  rw [show (fun w : ℂ => Real.log 2 - Real.log (discDenom w)) =
    (fun _ : ℂ => Real.log 2) - (fun w => Real.log (discDenom w)) from rfl,
    contDiffAt_const.laplacian_sub hc]
  simp only [laplacian_const, Pi.zero_apply]
  rw [laplacian_log (discDenom_contDiff.of_le (by simp)).contDiffAt hd,
    laplacian_discDenom, gradientSq_discDenom]
  unfold discDensity discDenom at *
  field_simp
  ring

end AreaDeficit
