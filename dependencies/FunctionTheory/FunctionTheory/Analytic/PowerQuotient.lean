import FunctionTheory.Analytic.FiniteInterpolation
import Mathlib.Analysis.Complex.AbsMax

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A zero of order at least `n` can be divided out on the whole working set,
retaining analyticity. The identity also holds for the ambient representatives. -/
theorem exists_analytic_power_quotient
    {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {a : ℂ} (ha : a ∈ U)
    {n : ℕ} (horder : (n : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z, f z = (z - a) ^ n * g z := by
  classical
  obtain ⟨h, hh, heq⟩ := (natCast_le_analyticOrderAt (hf a ha)).mp horder
  let g : ℂ → ℂ := fun z => if z = a then h a else f z / (z - a) ^ n
  have hnear : g =ᶠ[𝓝 a] h := by
    filter_upwards [heq] with z hz
    by_cases hza : z = a
    · simp [g, hza]
    · simp only [g, ite_eq_right hza]
      apply (div_eq_iff (pow_ne_zero n (sub_ne_zero.mpr hza))).mpr
      simpa only [smul_eq_mul, mul_comm] using hz
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    by_cases hza : z = a
    · subst z
      exact hh.congr hnear.symm
    · have hquot : AnalyticAt ℂ (fun w => f w / (w - a) ^ n) z :=
        (hf z hz).div ((analyticAt_id.sub analyticAt_const).pow n)
          (pow_ne_zero n (sub_ne_zero.mpr hza))
      apply hquot.congr
      filter_upwards [eventually_ne_nhds hza] with w hwa
      simp only [g, ite_eq_right hwa]
  · intro z
    by_cases hza : z = a
    · subst z
      simpa only [g, ite_eq_left rfl, smul_eq_mul] using heq.self_of_nhds
    · simp only [g, ite_eq_right hza]
      field_simp

/-- Dividing out a power amplifies a boundary error by at most `R⁻ⁿ` on the
whole closed disk, by the maximum modulus principle. -/
theorem norm_analytic_power_quotient_le
    {f g : ℂ → ℂ} {a : ℂ} {R δ : ℝ} {n : ℕ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall a R))
    (hfactor : ∀ z, f z = (z - a) ^ n * g z)
    (hbound : ∀ z ∈ sphere a R, ‖f z‖ ≤ δ) :
    ∀ z ∈ closedBall a R, ‖g z‖ ≤ δ / R ^ n := by
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hg.differentiableOn.diffContOnCl_ball subset_rfl)
  · intro w hw
    have hs := frontier_ball_subset_sphere hw
    apply (le_div_iff₀ (pow_pos hR n)).mpr
    simpa only [hfactor w, norm_mul, norm_pow, mem_sphere_iff_norm.mp hs, mul_comm]
      using hbound w hs
  · simpa only [closure_ball a hR.ne'] using hz

/-- Quantitative analytic division on a closed disk. -/
theorem exists_bounded_analytic_power_quotient
    {f : ℂ → ℂ} {a : ℂ} {R δ : ℝ} {n : ℕ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall a R))
    (horder : (n : ℕ∞) ≤ analyticOrderAt f a)
    (hbound : ∀ z ∈ sphere a R, ‖f z‖ ≤ δ) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall a R) ∧
      (∀ z, f z = (z - a) ^ n * g z) ∧
      ∀ z ∈ closedBall a R, ‖g z‖ ≤ δ / R ^ n := by
  obtain ⟨g, hg, heq⟩ := exists_analytic_power_quotient hf (mem_closedBall_self hR.le) horder
  exact ⟨g, hg, heq, norm_analytic_power_quotient_le hR hg heq hbound⟩

/-- Equal values and local degrees give the vanishing order needed to divide
the perturbation error by the common local-degree power. -/
theorem le_analyticOrderAt_sub_of_equal_local_degree
    {f g : ℂ → ℂ} {a : ℂ} {n : ℕ} (hvalue : g a = f a)
    (hf : analyticOrderAt (fun z => f z - f a) a = n)
    (hg : analyticOrderAt (fun z => g z - g a) a = n) :
    (n : ℕ∞) ≤ analyticOrderAt (fun z => f z - g z) a := by
  have heq : (fun z => f z - f a) - (fun z => g z - g a) =
      (fun z => f z - g z) := by
    funext z
    simp only [Pi.sub_apply, hvalue]
    ring
  simpa only [hf, hg, min_self, heq] using
    (le_analyticOrderAt_sub (f := fun z => f z - f a) (g := fun z => g z - g a) (z₀ := a))

end FunctionTheory
