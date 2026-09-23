import AreaTransport
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

open Set Function MeasureTheory
open scoped ENNReal

namespace AreaDeficit

noncomputable def complexDerivativeAsReal (c : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ

theorem det_complexDerivativeAsReal (c : ℂ) :
    (complexDerivativeAsReal c).det = ‖c‖^2 := by
  simp [complexDerivativeAsReal, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

theorem holomorphic_change_of_variables {f d : ℂ → ℂ} {W : Set ℂ}
    (hW : MeasurableSet W) (hf : ∀ z ∈ W, HasDerivAt f (d z) z)
    (hinj : InjOn f W) (b : ℂ → ℝ≥0∞) :
    (∫⁻ z in f '' W, b z) = ∫⁻ z in W, ENNReal.ofReal (‖d z‖^2) * b (f z) := by
  have hd : ∀ z ∈ W, HasFDerivWithinAt f (complexDerivativeAsReal (d z)) W z := by
    intro z hz
    exact ((hf z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  simpa only [det_complexDerivativeAsReal, abs_sq] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW hd hinj b

theorem holomorphic_pullback_weight (d : ℂ) (r : ℝ) :
    ENNReal.ofReal |(complexDerivativeAsReal d).det| * ENNReal.ofReal (r^2) =
      ENNReal.ofReal ((‖d‖ * r)^2) := by
  rw [det_complexDerivativeAsReal, abs_of_nonneg (sq_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _), mul_pow]

/-- The precise interface from density_deficit_on_set to area transport,
using the actual holomorphic Jacobian and the pullback length density. -/
theorem holomorphic_area_advance_of_density_deficit
    {f d : ℂ → ℂ} {W : Set ℂ} {a rho : ℂ → ℝ} {C : ℝ≥0∞}
    (hW : MeasurableSet W) (hf : ∀ z ∈ W, HasDerivAt f (d z) z)
    (hinj : InjOn f W) (hrho : Measurable rho)
    (hdef : (∫⁻ z in W, ENNReal.ofReal ((a z)^2) -
      ENNReal.ofReal ((‖d z‖ * rho (f z))^2)) ≤ C) :
    volume.withDensity (fun z => ENNReal.ofReal ((a z)^2)) W ≤
      volume.withDensity (fun z => ENNReal.ofReal ((rho z)^2)) (f '' W) + C := by
  have hd : ∀ z ∈ W, HasFDerivWithinAt f (complexDerivativeAsReal (d z)) W z := by
    intro z hz
    exact ((hf z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  apply area_advance_of_integrated_defect hW hd hinj (hrho.pow_const 2).ennreal_ofReal
  simpa only [holomorphic_pullback_weight] using hdef

end AreaDeficit
