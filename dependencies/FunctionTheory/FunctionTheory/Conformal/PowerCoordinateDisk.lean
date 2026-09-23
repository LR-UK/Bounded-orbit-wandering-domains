import FunctionTheory.Conformal.LocalPowerCoordinate
import FunctionTheory.Analytic.FiniteInterpolation

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A local power coordinate and its nonvanishing unit factor can be fixed on
an arbitrarily small closed disk inside a prescribed open neighbourhood. -/
theorem exists_power_coordinate_disk
    {φ : ℂ → ℂ} {c : ℂ} (hφ : AnalyticAt ℂ φ c)
    {n : ℕ} (hn : n ≠ 0) (horder : analyticOrderAt (fun z => φ z - φ c) c = n)
    {U : Set ℂ} (hU : IsOpen U) (hc : c ∈ U) {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, R ≤ η ∧ closedBall c R ⊆ U ∧ ∃ α u : ℂ → ℂ,
      AnalyticOnNhd ℂ α (closedBall c R) ∧ AnalyticOnNhd ℂ u (closedBall c R) ∧
      (∀ z ∈ closedBall c R, u z ≠ 0) ∧ α c = 0 ∧
      (∀ z ∈ closedBall c R, deriv α z ≠ 0) ∧
      (∀ z ∈ closedBall c R, φ z = φ c + α z ^ n) ∧
      ∀ z, α z ^ n = (z - c) ^ n * u z := by
  obtain ⟨α, hα, hα0, hαd, hpower⟩ := exists_local_power_coordinate_of_order hφ hn horder
  have hds : AnalyticAt ℂ (dslope α c) c :=
    analyticOnNhd_dslope (U := {z | AnalyticAt ℂ α z}) (fun _ hz => hz) c c hα
  let u : ℂ → ℂ := fun z => dslope α c z ^ n
  have hu : AnalyticAt ℂ u c := hds.pow n
  have hu0 : u c ≠ 0 := by
    simpa only [u, dslope_same] using pow_ne_zero n hαd
  have hfactor : ∀ z, α z ^ n = (z - c) ^ n * u z := by
    intro z
    have hdiv : (z - c) * dslope α c z = α z := by
      simpa only [hα0, sub_zero, smul_eq_mul] using sub_smul_dslope α c z
    rw [← hdiv, mul_pow]
  have hev : ∀ᶠ z in 𝓝 c, z ∈ U ∧ AnalyticAt ℂ α z ∧ AnalyticAt ℂ u z ∧
      u z ≠ 0 ∧ deriv α z ≠ 0 ∧ φ z = φ c + α z ^ n := by
    filter_upwards [hU.mem_nhds hc, hα.eventually_analyticAt, hu.eventually_analyticAt,
      hu.continuousAt.eventually_ne hu0, hα.deriv.continuousAt.eventually_ne hαd,
      hpower] with z hzU hzα hzu hz0 hzd hzp
    exact ⟨hzU, hzα, hzu, hz0, hzd, hzp⟩
  obtain ⟨ρ, hρ, H⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hev
  have hsub : closedBall c (min ρ η) ⊆ closedBall c ρ :=
    closedBall_subset_closedBall (min_le_left _ _)
  refine ⟨min ρ η, lt_min hρ hη, min_le_right _ _,
    fun z hz => (H (hsub hz)).1, α, u, ?_, ?_, ?_, hα0, ?_, ?_, hfactor⟩
  · exact fun z hz => (H (hsub hz)).2.1
  · exact fun z hz => (H (hsub hz)).2.2.1
  · exact fun z hz => (H (hsub hz)).2.2.2.1
  · exact fun z hz => (H (hsub hz)).2.2.2.2.1
  · exact fun z hz => (H (hsub hz)).2.2.2.2.2

end FunctionTheory
