import ComplexApproximation.CauchyTransformBounds

/-!
# Correcting a smooth holomorphic gluing

The compactly supported Cauchy–Riemann solver removes the defect of a smooth
interpolation. These identities are the analytic part of the Rosay–Rudin step.
-/

open Complex Set Function Runge
open scoped Topology ContDiff

namespace ComplexApproximation

theorem cauchyRiemannDefect_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    cauchyRiemannDefect (fun w => f w + g w) z =
      cauchyRiemannDefect f z + cauchyRiemannDefect g z := by
  simp only [cauchyRiemannDefect, fderiv_fun_add hf hg, add_apply]
  ring

theorem cauchyRiemannDefect_mul_real {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    cauchyRiemannDefect (fun w => f w * g w) z =
      f z * cauchyRiemannDefect g z + g z * cauchyRiemannDefect f z := by
  simp only [cauchyRiemannDefect, fderiv_fun_mul hf hg,
    add_apply, smul_apply, smul_eq_mul]
  ring

/-- A real smooth function becomes holomorphic where its defect is the
negative of the prescribed compactly supported density. -/
theorem differentiableAt_add_solveCauchyRiemann {h q : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℝ h z) (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (heq : cauchyRiemannDefect h z = -q z) :
    DifferentiableAt ℂ (fun w => h w + solveCauchyRiemann q w) z := by
  have hs := (contDiff_solveCauchyRiemann hq hc).differentiable (by simp) z
  apply (differentiableAt_complex_iff_defect_eq_zero (hh.add hs)).mpr
  change cauchyRiemannDefect (fun w => h w + solveCauchyRiemann q w) z = 0
  rw [cauchyRiemannDefect_add hh hs,
    cauchyRiemannDefect_solveCauchyRiemann q hq hc, heq, neg_add_cancel]

theorem differentiableOn_add_solveCauchyRiemann {h q : ℂ → ℂ} {U : Set ℂ}
    (hh : ∀ z ∈ U, DifferentiableAt ℝ h z)
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (heq : ∀ z ∈ U, cauchyRiemannDefect h z = -q z) :
    DifferentiableOn ℂ (fun w => h w + solveCauchyRiemann q w) U :=
  fun z hz => (differentiableAt_add_solveCauchyRiemann
    (hh z hz) hq hc (heq z hz)).differentiableWithinAt

/-- The defect of the usual smooth interpolation of two holomorphic maps. -/
theorem cauchyRiemannDefect_interpolate {φ f g : ℂ → ℂ} {z : ℂ}
    (hφ : DifferentiableAt ℝ φ z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) :
    cauchyRiemannDefect (fun w => φ w * f w + (1 - φ w) * g w) z =
      (f z - g z) * cauchyRiemannDefect φ z := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hφ' : DifferentiableAt ℝ (fun w => 1 - φ w) z :=
    (differentiableAt_const _).sub hφ
  rw [cauchyRiemannDefect_add (f := fun w => φ w * f w)
      (g := fun w => (1 - φ w) * g w) (hφ.mul hfR) (hφ'.mul hgR),
    cauchyRiemannDefect_mul_real hφ hfR,
    cauchyRiemannDefect_mul_real hφ' hgR,
    cauchyRiemannDefect_sub (differentiableAt_const _) hφ,
    cauchyRiemannDefect_eq_zero hf, cauchyRiemannDefect_eq_zero hg,
    cauchyRiemannDefect_eq_zero (differentiableAt_const _)]
  ring

end ComplexApproximation
