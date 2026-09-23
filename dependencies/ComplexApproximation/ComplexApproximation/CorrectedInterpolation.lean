import ComplexApproximation.SmoothLocalization

/-! # A holomorphic correction of a cutoff interpolation -/

open Complex Set Function Filter Runge
open scoped Topology ContDiff

namespace ComplexApproximation

noncomputable def interpolate (φ p f : ℂ → ℂ) (z : ℂ) : ℂ :=
  φ z * p z + (1 - φ z) * f z

noncomputable def interpolationDensity (χ φ p f : ℂ → ℂ) (z : ℂ) : ℂ :=
  χ z * ((f z - p z) * cauchyRiemannDefect φ z)

def gluingOpen (U : Set ℂ) (φ χ : ℂ → ℂ) : Set ℂ :=
  interior {z | φ z = 1} ∪
    (U ∩ ((tsupport (cauchyRiemannDefect φ))ᶜ ∪ interior {z | χ z = 1}))

theorem isOpen_gluingOpen {U : Set ℂ} (hU : IsOpen U) (φ χ : ℂ → ℂ) :
    IsOpen (gluingOpen U φ χ) :=
  isOpen_interior.union (hU.inter (isClosed_closure.isOpen_compl.union isOpen_interior))

theorem subset_gluingOpen {E U : Set ℂ} {φ χ : ℂ → ℂ} (hEU : E ⊆ U)
    (hχ : ∀ z ∈ E ∩ tsupport (cauchyRiemannDefect φ), χ =ᶠ[𝓝 z] (fun _ => 1)) :
    E ⊆ gluingOpen U φ χ := by
  intro z hz
  right
  refine ⟨hEU hz, ?_⟩
  by_cases hd : z ∈ tsupport (cauchyRiemannDefect φ)
  · right
    exact mem_interior_iff_mem_nhds.mpr (hχ z ⟨hz, hd⟩)
  · exact Or.inl hd

theorem differentiableAt_correctedInterpolation {U : Set ℂ} {φ χ p f : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hp : Differentiable ℂ p)
    (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    (hq : ContDiff ℝ ∞ (interpolationDensity χ φ p f))
    (hc : HasCompactSupport (interpolationDensity χ φ p f))
    {z : ℂ} (hz : z ∈ gluingOpen U φ χ) :
    DifferentiableAt ℂ
      (fun w => interpolate φ p f w + solveCauchyRiemann (interpolationDensity χ φ p f) w) z := by
  let q := interpolationDensity χ φ p f
  have hφR := hφ.differentiable (by simp) z
  rcases hz with hz | ⟨hzU, hz⟩
  · have hφ1 : φ =ᶠ[𝓝 z] (fun _ => 1) := mem_interior_iff_mem_nhds.mp hz
    have hi : interpolate φ p f =ᶠ[𝓝 z] p := by
      filter_upwards [hφ1] with w hw
      simp [interpolate, hw]
    have hD : cauchyRiemannDefect φ z = 0 :=
      (cauchyRiemannDefect_congr hφ1).trans
        (cauchyRiemannDefect_eq_zero (differentiableAt_const _))
    apply differentiableAt_add_solveCauchyRiemann
      ((hp z).restrictScalars ℝ |>.congr_of_eventuallyEq hi) hq hc
    rw [cauchyRiemannDefect_congr hi, cauchyRiemannDefect_eq_zero (hp z)]
    simp [interpolationDensity, hD]
  · have hfi := hf z hzU
    have hi : DifferentiableAt ℝ (interpolate φ p f) z :=
      (hφR.mul ((hp z).restrictScalars ℝ)).add
        (((differentiableAt_const _).sub hφR).mul (hfi.restrictScalars ℝ))
    apply differentiableAt_add_solveCauchyRiemann hi hq hc
    change cauchyRiemannDefect (fun w => φ w * p w + (1 - φ w) * f w) z = _
    rw [cauchyRiemannDefect_interpolate hφR (hp z) hfi]
    rcases hz with hz | hz
    · have hD : cauchyRiemannDefect φ z = 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hz |>.self_of_nhds
      simp [interpolationDensity, hD]
    · have hχ1 : χ z = 1 := interior_subset (s := {w | χ w = 1}) hz
      simp only [interpolationDensity, hχ1, one_mul]
      ring

theorem analyticOnNhd_correctedInterpolation {U : Set ℂ} {φ χ p f : ℂ → ℂ}
    (hU : IsOpen U) (hφ : ContDiff ℝ ∞ φ) (hp : Differentiable ℂ p)
    (hf : AnalyticOnNhd ℂ f U)
    (hq : ContDiff ℝ ∞ (interpolationDensity χ φ p f))
    (hc : HasCompactSupport (interpolationDensity χ φ p f)) :
    AnalyticOnNhd ℂ
      (fun w => interpolate φ p f w + solveCauchyRiemann (interpolationDensity χ φ p f) w)
      (gluingOpen U φ χ) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_gluingOpen hU φ χ)
  intro z hz
  exact (differentiableAt_correctedInterpolation hφ hp
    (fun z hz => (hf z hz).differentiableAt) hq hc hz).differentiableWithinAt

theorem norm_interpolate_sub_le {φ : ℂ → ℝ} {p f : ℂ → ℂ} {E : Set ℂ} {δ : ℝ}
    (hφ : ∀ z, φ z ∈ Icc 0 1) (hδ : 0 ≤ δ)
    (happrox : ∀ z ∈ E ∩ tsupport φ, ‖f z - p z‖ ≤ δ) {z : ℂ} (hz : z ∈ E) :
    ‖interpolate (fun w => (φ w : ℂ)) p f z - f z‖ ≤ δ := by
  have heq : interpolate (fun w => (φ w : ℂ)) p f z - f z =
      (φ z : ℂ) * (p z - f z) := by unfold interpolate; ring
  rw [heq]
  by_cases hs : z ∈ tsupport φ
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ z).1]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hφ z).2).trans
    rw [norm_sub_rev]
    exact happrox z ⟨hz, hs⟩
  · have hzero : φ z = 0 := notMem_tsupport_iff_eventuallyEq.mp hs |>.self_of_nhds
    simpa [hzero] using hδ

end ComplexApproximation
