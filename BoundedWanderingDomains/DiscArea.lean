import BoundedWanderingDomains.DiscMetric
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory Metric
open scoped Interval

namespace AreaDeficit

theorem complex_integral_radial_ball (g : ℝ → ℝ) (r : ℝ) :
    (∫ z in ball (0 : ℂ) r, g ‖z‖) = 2 * Real.pi * ∫ t in Ioo 0 r, t * g t := by
  have h := integral_fun_norm_addHaar (E := ℂ) volume ((Iio r).indicator g)
  have hl : (fun z : ℂ => (Iio r).indicator g ‖z‖) =
      (ball (0 : ℂ) r).indicator (fun z => g ‖z‖) := by
    ext z
    simp [indicator, mem_ball, dist_zero_right]
  have hr : (fun t : ℝ => t ^ (Module.finrank ℝ ℂ - 1) • (Iio r).indicator g t) =
      (Iio r).indicator (fun t => t * g t) := by
    ext t
    by_cases ht : t < r <;> simp [ht, indicator]
  rw [hl, integral_indicator measurableSet_ball, hr,
    integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio] at h
  have hi : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by ext t; simp [and_comm]
  simpa [hi, Measure.real, Complex.volume_ball, Real.pi_pos.le, nsmul_eq_mul, smul_eq_mul,
    mul_assoc] using h

theorem radial_disc_area_integral {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ t in (0 : ℝ)..r, 4 * t / (1 - t^2)^2) = 2 * r^2 / (1 - r^2) := by
  have hn (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) : 1 - t^2 ≠ 0 := by
    rw [uIcc_of_le hr] at ht
    nlinarith [ht.1, ht.2]
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) :
      HasDerivAt (fun t : ℝ => 2 / (1 - t^2)) (4 * t / (1 - t^2)^2) t := by
    have hh := (hasDerivAt_const t (2 : ℝ)).div
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)) (hn t ht)
    simp only [Pi.div_def, Pi.sub_def, Pi.pow_def, id_eq] at hh
    convert hh using 1
    norm_num
    ring
  have hc : ContinuousOn (fun t : ℝ => 4 * t / (1 - t^2)^2) (uIcc (0 : ℝ) r) := by
    exact (continuous_const.mul continuous_id).continuousOn.div
      ((continuous_const.sub (continuous_id.pow 2)).pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hn t ht))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have hn1 := hn r (right_mem_uIcc)
  norm_num
  field_simp
  ring

/-- The Euclidean-coordinate integral of the curvature −1 disc density.
Identification of these discs with intrinsic balls of radius R still
requires the distance formula r=tanh(R/2). -/
theorem disc_area_euclidean_radius {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ z in ball (0 : ℂ) r, (discDensity z)^2) =
      4 * Real.pi * r^2 / (1 - r^2) := by
  have hfun : (fun z : ℂ => (discDensity z)^2) =
      (fun z : ℂ => 4 / (1 - ‖z‖^2)^2) := by
    ext z
    simp [discDensity, discDenom, Complex.normSq_eq_norm_sq, div_pow]
    ring
  rw [hfun, complex_integral_radial_ball (fun t : ℝ => 4 / (1 - t^2)^2) r]
  have hg : (fun t : ℝ => t * (4 / (1 - t^2)^2)) =
      (fun t : ℝ => 4 * t / (1 - t^2)^2) := by ext t; ring
  rw [hg, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr,
    radial_disc_area_integral hr hr1]
  ring

theorem disc_area_lintegral {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫⁻ z in ball (0 : ℂ) r, ENNReal.ofReal ((discDensity z)^2)) =
      ENNReal.ofReal (4 * Real.pi * r^2 / (1 - r^2)) := by
  have hn (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) : discDenom z ≠ 0 := by
    have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    unfold discDenom
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hc : ContinuousOn (fun z => (discDensity z)^2) (closedBall (0 : ℂ) r) :=
    (continuousOn_const.div discDenom_contDiff.continuous.continuousOn hn).pow 2
  have hi : IntegrableOn (fun z => (discDensity z)^2) (ball (0 : ℂ) r) :=
    (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    disc_area_euclidean_radius hr hr1]

/-- An explicit sequence of smaller discs has area 4πn. This already
gives the needed unboundedness without a hyperbolic-distance formula. -/
theorem disc_area_sqrt_nat (n : ℕ) :
    (∫⁻ z in ball (0 : ℂ) (Real.sqrt ((n : ℝ) / (n + 1))),
      ENNReal.ofReal ((discDensity z)^2)) = ENNReal.ofReal (4 * Real.pi * n) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hq : 0 ≤ (n : ℝ) / (n + 1) := by positivity
  have hr : Real.sqrt ((n : ℝ) / (n + 1)) < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
    exact (div_lt_one hn).mpr (by linarith)
  rw [disc_area_lintegral (Real.sqrt_nonneg _) hr, Real.sq_sqrt hq]
  congr 1
  field_simp
  ring

theorem no_uniform_disc_area_bound (H : ℝ) :
    ¬ (∀ r : ℝ, 0 ≤ r → r < 1 →
      (∫⁻ z in ball (0 : ℂ) r, ENNReal.ofReal ((discDensity z)^2)) ≤ ENNReal.ofReal H) := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (max H 0 / (4 * Real.pi))
  have hden : 0 < 4 * Real.pi := by positivity
  have ha : max H 0 < 4 * Real.pi * n := by
    have hh := (div_lt_iff₀ hden).mp hn
    nlinarith
  have hr : Real.sqrt ((n : ℝ) / (n + 1)) < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
    exact (div_lt_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith)
  have hh := h _ (Real.sqrt_nonneg _) hr
  rw [disc_area_sqrt_nat] at hh
  have hmax : ENNReal.ofReal H = ENNReal.ofReal (max H 0) := by simp
  rw [hmax] at hh
  exact (not_le_of_gt ha) ((ENNReal.ofReal_le_ofReal_iff (le_max_right H 0)).mp hh)

end AreaDeficit
