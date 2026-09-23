/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.Barrier

/-!
# Bipolar Green: the dipole limit

`exists_bipolar_green`: the dipole differences of the piece Green's
functions converge along the shrinking exhaustion to a bipolar Green's
function — harmonic off the two poles, with a positive logarithmic pole at
`p₁` and a negative one at `p₂`. The convergence brick is a
Cauchy-on-a-sphere criterion for sequences of harmonic functions on a disk.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

/-- A sequence of harmonic functions on a disk which is uniformly Cauchy on an interior
circle converges on the enclosed disk, with harmonic limit: the Poisson kernel bounds
propagate the circle oscillation inward with a two-point comparison constant. -/
private theorem exists_harmonicOnNhd_tendsto_of_cauchy_sphere {ca : ℂ} {ra : ℝ}
    (hs : ℕ → ℂ → ℝ) (hra : 0 < ra)
    (hharm : ∀ n : ℕ, HarmonicOnNhd (hs n) (ball ca (2 * ra)))
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ sphere ca (3 * ra /
        2),
      |hs m ζ - hs n ζ| ≤ ε) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H (ball ca (3 * ra / 2)) ∧
      ∀ w ∈ ball ca (3 * ra / 2), Tendsto (fun n ↦ hs n w) atTop (𝓝 (H w)) := by
  classical
  /- ## The Poisson kernel is continuous on the circle, for interior points. -/
  have hKcont : ∀ (c z : ℂ) (ρ : ℝ), z ∈ ball c ρ →
      ContinuousOn (poissonKernel c z) (sphere c ρ) := by
    intro c z ρ hz
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    apply Complex.continuous_re.comp_continuousOn
    rw [herglotzRieszKernel_fun_def]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro w hw
    have hwn : ‖w - c‖ = ρ := by rw [← dist_eq_norm]; simpa using (mem_sphere.1 hw)
    have hzlt : ‖z - c‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hz
    intro hcontra
    have hwz : w - c = z - c := by linear_combination (norm := ring_nf) hcontra
    rw [hwz] at hwn
    linarith only [hwn, hzlt]
  /- ## Circle averages of uniformly close functions are close. -/
  have havg_diff : ∀ (F g : ℂ → ℝ) (c : ℂ) (ρ A : ℝ), 0 < ρ →
      ContinuousOn F (sphere c ρ) → ContinuousOn g (sphere c ρ) →
      (∀ ζ ∈ sphere c ρ, |F ζ - g ζ| ≤ A) →
      |Real.circleAverage F c ρ - Real.circleAverage g c ρ| ≤ A := by
    intro F g c ρ A hρ hF hg hbd
    have hFi : CircleIntegrable F c ρ := hF.circleIntegrable hρ.le
    have hgi : CircleIntegrable g c ρ := hg.circleIntegrable hρ.le
    have habsci : CircleIntegrable (fun ζ ↦ |F ζ - g ζ|) c ρ :=
      ((hF.sub hg).abs).circleIntegrable hρ.le
    rw [← Real.circleAverage_fun_sub hFi hgi]
    calc |Real.circleAverage (fun ζ ↦ F ζ - g ζ) c ρ|
        ≤ Real.circleAverage |fun ζ ↦ F ζ - g ζ| c ρ :=
          Real.abs_circleAverage_le_circleAverage_abs
      _ ≤ A := by
          apply Real.circleAverage_mono_on_of_le_circle habsci
          intro ζ hζ
          rw [abs_of_pos hρ] at hζ
          exact hbd ζ hζ
  /- ## The Poisson comparison: two harmonic functions close on a circle are close inside. -/
  have poissonDiff : ∀ (h₁ h₂ : ℂ → ℝ) (c : ℂ) (ρ ε : ℝ), 0 < ρ → 0 ≤ ε →
      HarmonicOnNhd h₁ (closedBall c ρ) → HarmonicOnNhd h₂ (closedBall c ρ) →
      (∀ ζ ∈ sphere c ρ, |h₁ ζ - h₂ ζ| ≤ ε) →
      ∀ w ∈ ball c ρ, |h₁ w - h₂ w| ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) * ε := by
    intro h₁ h₂ c ρ ε hρ hε hh₁ hh₂ hsp w hw
    have haz : ‖w - c‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hw
    have haz0 : 0 ≤ ‖w - c‖ := norm_nonneg _
    have hKb0 : 0 ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) :=
      div_nonneg (by linarith only [hρ, haz0]) (by linarith only [haz])
    have hKbound : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c w ζ| ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) := by
      intro ζ hζ
      have hup : poissonKernel c w ζ ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        exact re_herglotzRieszKernel_le hζ hw
      have hlo : 0 ≤ poissonKernel c w ζ := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        refine le_trans ?_ (le_re_herglotzRieszKernel hζ hw)
        apply div_nonneg <;> linarith only [hρ, haz0, haz]
      rw [abs_of_nonneg hlo]
      exact hup
    have hrep1 := hh₁.circleAverage_poissonKernel_smul hw
    have hrep2 := hh₂.circleAverage_poissonKernel_smul hw
    have hrep1' : Real.circleAverage (fun ζ ↦ poissonKernel c w ζ * h₁ ζ) c ρ = h₁ w := by
      rw [← hrep1]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    have hrep2' : Real.circleAverage (fun ζ ↦ poissonKernel c w ζ * h₂ ζ) c ρ = h₂ w := by
      rw [← hrep2]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    have hc₁ : ContinuousOn (fun ζ ↦ poissonKernel c w ζ * h₁ ζ) (sphere c ρ) :=
      (hKcont c w ρ hw).mul (hh₁.continuousOn.mono sphere_subset_closedBall)
    have hc₂ : ContinuousOn (fun ζ ↦ poissonKernel c w ζ * h₂ ζ) (sphere c ρ) :=
      (hKcont c w ρ hw).mul (hh₂.continuousOn.mono sphere_subset_closedBall)
    have hptbd : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c w ζ * h₁ ζ - poissonKernel c w ζ * h₂ ζ|
          ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) * ε := by
      intro ζ hζ
      have h1 : |poissonKernel c w ζ * h₁ ζ - poissonKernel c w ζ * h₂ ζ|
          = |poissonKernel c w ζ| * |h₁ ζ - h₂ ζ| := by
        rw [← mul_sub, abs_mul]
      rw [h1]
      exact mul_le_mul (hKbound ζ hζ) (hsp ζ hζ) (abs_nonneg _) hKb0
    have hkey := havg_diff _ _ c ρ ((ρ + ‖w - c‖) / (ρ - ‖w - c‖) * ε) hρ hc₁ hc₂
        hptbd
    rw [hrep1', hrep2'] at hkey
    exact hkey
  /- ## A locally uniform limit of plane-harmonic functions is harmonic. -/
  have planeLimitHarm : ∀ (F : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (c : ℂ) (ρ : ℝ), 0 < ρ
      →
      (∀ n, HarmonicOnNhd (F n) (closedBall c ρ)) →
      TendstoUniformlyOn F g atTop (closedBall c ρ) →
      HarmonicOnNhd g (ball c ρ) := by
    intro F g c ρ hρ hF hunif
    have hcont_n : ∀ n, ContinuousOn (F n) (closedBall c ρ) := fun n ↦ (hF n).continuousOn
    have hGcont : ContinuousOn g (closedBall c ρ) :=
      hunif.continuousOn ((Filter.Eventually.of_forall hcont_n).frequently)
    have hPI : ∀ z ∈ ball c ρ, g z = poissonIntegral g c ρ z := by
      intro z hz
      have haz : ‖z - c‖ < ρ := by
        rw [← dist_eq_norm]
        exact mem_ball.1 hz
      have haz0 : 0 ≤ ‖z - c‖ := norm_nonneg _
      set Kb : ℝ := (ρ + ‖z - c‖) / (ρ - ‖z - c‖) with hKbdef
      have hKb0 : 0 ≤ Kb := div_nonneg (by linarith only [hρ, haz0])
        (by linarith only [haz])
      have hKbound : ∀ ζ ∈ sphere c ρ, |poissonKernel c z ζ| ≤ Kb := by
        intro ζ hζ
        have hup : poissonKernel c z ζ ≤ Kb := by
          rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
            herglotzRieszKernel_def]
          exact re_herglotzRieszKernel_le hζ hz
        have hlo : 0 ≤ poissonKernel c z ζ := by
          rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
            herglotzRieszKernel_def]
          refine le_trans ?_ (le_re_herglotzRieszKernel hζ hz)
          apply div_nonneg <;> linarith only [hρ, haz0, haz]
        rw [abs_of_nonneg hlo]
        exact hup
      have hrep : ∀ n : ℕ, F n z = poissonIntegral (F n) c ρ z := by
        intro n
        have h1 := (hF n).circleAverage_poissonKernel_smul hz
        rw [← h1, poissonIntegral]
        apply Real.circleAverage_congr_sphere
        intro ζ _
        simp [smul_eq_mul]
      have hlimPI : Tendsto (fun n ↦ poissonIntegral (F n) c ρ z)
          atTop (𝓝 (poissonIntegral g c ρ z)) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        have hsphunif := hunif.mono sphere_subset_closedBall
        rw [Metric.tendstoUniformlyOn_iff] at hsphunif
        have hev := hsphunif (ε / (2 * (Kb + 1)))
          (div_pos hε (by linarith only [hKb0]))
        rw [Filter.eventually_atTop] at hev
        obtain ⟨N, hN⟩ := hev
        refine ⟨N, fun n hn ↦ ?_⟩
        rw [Real.dist_eq]
        have hbd : ∀ ζ ∈ sphere c ρ,
            |poissonKernel c z ζ * F n ζ - poissonKernel c z ζ * g ζ|
              ≤ Kb * (ε / (2 * (Kb + 1))) := by
          intro ζ hζ
          have h1 : |poissonKernel c z ζ * F n ζ - poissonKernel c z ζ * g ζ|
              = |poissonKernel c z ζ| * |F n ζ - g ζ| := by
            rw [← mul_sub, abs_mul]
          rw [h1]
          have h2 : |F n ζ - g ζ| ≤ ε / (2 * (Kb + 1)) := by
            have h3 := hN n hn ζ hζ
            rw [Real.dist_eq, abs_sub_comm] at h3
            exact h3.le
          exact mul_le_mul (hKbound ζ hζ) h2 (abs_nonneg _) hKb0
        have hcF : ContinuousOn (fun ζ ↦ poissonKernel c z ζ * F n ζ) (sphere c ρ) :=
          (hKcont c z ρ hz).mul ((hcont_n n).mono sphere_subset_closedBall)
        have hcG : ContinuousOn (fun ζ ↦ poissonKernel c z ζ * g ζ) (sphere c ρ) :=
          (hKcont c z ρ hz).mul (hGcont.mono sphere_subset_closedBall)
        have hkey := havg_diff _ _ c ρ (Kb * (ε / (2 * (Kb + 1)))) hρ hcF hcG hbd
        have hfin : Kb * (ε / (2 * (Kb + 1))) < ε := by
          rw [div_eq_mul_inv]
          have h4 : Kb * (ε * (2 * (Kb + 1))⁻¹) ≤ (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) := by
            apply mul_le_mul_of_nonneg_right (by linarith only [])
              (mul_nonneg hε.le (inv_nonneg.2 (by linarith only [hKb0])))
          have h5 : (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) = ε / 2 := by
            field_simp
          rw [h5] at h4
          linarith only [h4, hε]
        exact lt_of_le_of_lt hkey hfin
      have hGz : Tendsto (fun n ↦ poissonIntegral (F n) c ρ z)
          atTop (𝓝 (g z)) := by
        have h1 := hunif.tendsto_at (ball_subset_closedBall hz)
        exact h1.congr hrep
      exact tendsto_nhds_unique hGz hlimPI
    have hPharm : HarmonicOnNhd (poissonIntegral g c ρ) (ball c ρ) :=
      poissonIntegral_harmonicOn _ _ hρ (hGcont.mono sphere_subset_closedBall)
    intro w hw
    have hev : g =ᶠ[𝓝 w] poissonIntegral g c ρ :=
      eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) hPI
    exact (harmonicAt_congr_nhds hev).mpr (hPharm _ hw)
  have hkey : ∀ ρ : ℝ, 0 < ρ → ρ < 3 * ra / 2 → ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ w ∈ closedBall ca ρ,
        |hs m w - hs n w| ≤ (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) * ε := by
    intro ρ hρ0 hρlt ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun m hm n hn w hw ↦ ?_⟩
    have hsub : closedBall ca (3 * ra / 2) ⊆ ball ca (2 * ra) :=
      closedBall_subset_ball (by linarith only [hra])
    have hwball : w ∈ ball ca (3 * ra / 2) :=
      mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hw) hρlt)
    have hcmp := poissonDiff (hs m) (hs n) ca (3 * ra / 2) ε
      (by linarith only [hra])
      hε.le (fun v hv ↦ hharm m v (hsub hv))
      (fun v hv ↦ hharm n v (hsub hv))
      (fun ζ hζ ↦ hN m hm n hn ζ hζ) w hwball
    have h1 : ‖w - ca‖ ≤ ρ := by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 hw
    have hwlt : ‖w - ca‖ < 3 * ra / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hwball
    have hK : (3 * ra / 2 + ‖w - ca‖) / (3 * ra / 2 - ‖w - ca‖)
        ≤ (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) := by
      have hn0 : 0 ≤ ‖w - ca‖ := norm_nonneg _
      apply div_le_div₀ (by linarith only [hn0, h1, hra, hρ0])
        (by linarith only [h1]) (by linarith only [hρlt]) (by linarith only [h1])
    calc |hs m w - hs n w|
        ≤ (3 * ra / 2 + ‖w - ca‖) / (3 * ra / 2 - ‖w - ca‖) * ε := hcmp
      _ ≤ (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) * ε :=
          mul_le_mul_of_nonneg_right hK hε.le
  have hptw : ∀ w ∈ ball ca (3 * ra / 2),
      ∃ l, Tendsto (fun n ↦ hs n w) atTop (𝓝 l) := by
    intro w hw
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set ρ : ℝ := (dist w ca + 3 * ra / 2) / 2 with hρdef
    have hd : dist w ca < 3 * ra / 2 := mem_ball.1 hw
    have hdnn : 0 ≤ dist w ca := dist_nonneg
    have hρ0 : 0 < ρ := by rw [hρdef]; linarith only [hdnn, hra]
    have hρlt : ρ < 3 * ra / 2 := by rw [hρdef]; linarith only [hd]
    set κ : ℝ := (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) with hκ
    have hκ0 : 0 < κ := by
      rw [hκ]
      exact div_pos (by linarith only [hρ0, hra]) (by linarith only [hρlt])
    obtain ⟨N, hN⟩ := hkey ρ hρ0 hρlt (ε / (2 * κ))
      (div_pos hε (by linarith only [hκ0]))
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [Real.dist_eq]
    have h1 := hN m hm n hn w
      (by rw [mem_closedBall, hρdef]; linarith only [hd, hdnn])
    have h2 : κ * (ε / (2 * κ)) = ε / 2 := by
      field_simp
    calc |hs m w - hs n w| ≤ κ * (ε / (2 * κ)) := h1
      _ = ε / 2 := h2
      _ < ε := by linarith only [hε]
  set H : ℂ → ℝ := fun w ↦ limUnder atTop (fun n ↦ hs n w) with hH
  have hHtend : ∀ w ∈ ball ca (3 * ra / 2),
      Tendsto (fun n ↦ hs n w) atTop (𝓝 (H w)) := by
    intro w hw
    obtain ⟨l, hl⟩ := hptw w hw
    have h1 : H w = l := hl.limUnder_eq
    rw [h1]
    exact hl
  refine ⟨H, ?_, hHtend⟩
  intro w₀ hw₀
  set ρw : ℝ := (3 * ra / 2 - dist w₀ ca) / 2 with hρw
  have hd0 : dist w₀ ca < 3 * ra / 2 := mem_ball.1 hw₀
  have hρw0 : 0 < ρw := by rw [hρw]; linarith only [hd0]
  have hsubw : closedBall w₀ ρw ⊆ ball ca (3 * ra / 2) := by
    intro v hv
    have h1 : dist v ca ≤ dist v w₀ + dist w₀ ca := dist_triangle _ _ _
    have h2 : dist v w₀ ≤ ρw := mem_closedBall.1 hv
    rw [mem_ball]
    rw [hρw] at h2
    linarith only [h1, h2, hd0]
  have hunif : TendstoUniformlyOn (fun n ↦ hs n) H atTop (closedBall w₀ ρw) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set ρ : ℝ := dist w₀ ca + ρw with hρdef2
    have hdnn : 0 ≤ dist w₀ ca := dist_nonneg
    have hρlt : ρ < 3 * ra / 2 := by rw [hρdef2, hρw]; linarith only [hd0]
    have hρ0 : 0 < ρ := by rw [hρdef2]; linarith only [hdnn, hρw0]
    set κ : ℝ := (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) with hκ
    have hκ0 : 0 < κ := by
      rw [hκ]
      exact div_pos (by linarith only [hρ0, hra]) (by linarith only [hρlt])
    obtain ⟨N, hN⟩ := hkey ρ hρ0 hρlt (ε / (4 * κ))
      (div_pos hε (by linarith only [hκ0]))
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn v hv ↦ ?_⟩
    have hvcb : v ∈ closedBall ca ρ := by
      rw [mem_closedBall, hρdef2]
      have h1 := dist_triangle v w₀ ca
      have h2 := mem_closedBall.1 hv
      linarith only [h1, h2]
    have h3 : ∀ m ≥ N, |hs m v - hs n v| ≤ κ * (ε / (4 * κ)) :=
      fun m hm ↦ hN m hm n hn v hvcb
    have h4 : Tendsto (fun m ↦ |hs m v - hs n v|) atTop
        (𝓝 |H v - hs n v|) :=
      ((hHtend v (hsubw hv)).sub tendsto_const_nhds).abs
    have h5 : |H v - hs n v| ≤ κ * (ε / (4 * κ)) := by
      apply le_of_tendsto h4
      rw [Filter.eventually_atTop]
      exact ⟨N, h3⟩
    have h6 : κ * (ε / (4 * κ)) = ε / 4 := by
      field_simp
    rw [Real.dist_eq]
    calc |H v - hs n v| ≤ ε / 4 := by rw [← h6]; exact h5
      _ < ε := by linarith only [hε]
  have hHharm := planeLimitHarm (fun n ↦ hs n) H w₀ ρw hρw0
    (fun n v hv ↦ hharm n v
      (mem_ball.2 (lt_of_lt_of_le (mem_ball.1 (hsubw hv))
        (by linarith only [hra]))))
    hunif
  exact hHharm w₀ (mem_ball_self hρw0)

/-- **The bipolar Green's function**: a dipole limit of the piece Green's
function differences along the shrinking exhaustion — harmonic off the two
poles, with a positive logarithmic pole at `p₁` and a negative one at
`p₂`. -/
theorem exists_bipolar_green [SecondCountableTopology M] (D₀ : CoordDisk M)
    {p₁ p₂ : M} (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hne : p₁ ≠ p₂) :
    ∃ G : M → ℝ, MHarmonicOn G ({p₁, p₂}ᶜ) ∧
      (∃ r > 0, ball (chartAt ℂ p₁ p₁) r ⊆ (chartAt ℂ p₁).target ∧
        ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₁ p₁) r) ∧
          ∀ w ∈ ball (chartAt ℂ p₁ p₁) r \ {chartAt ℂ p₁ p₁},
            h w = G ((chartAt ℂ p₁).symm w) + Real.log ‖w - chartAt ℂ p₁ p₁‖) ∧
      (∃ r > 0, ball (chartAt ℂ p₂ p₂) r ⊆ (chartAt ℂ p₂).target ∧
        ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₂ p₂) r) ∧
          ∀ w ∈ ball (chartAt ℂ p₂ p₂) r \ {chartAt ℂ p₂ p₂},
            h w = G ((chartAt ℂ p₂).symm w) -
              Real.log ‖w - chartAt ℂ p₂ p₂‖) ∧
      (∃ C : ℝ, ∃ V₁ ∈ 𝓝 p₁, ∃ V₂ ∈ 𝓝 p₂, IsCompact (closure V₁) ∧
        IsCompact (closure V₂) ∧ ∀ x ∉ V₁ ∪ V₂, |G x| ≤ C) := by
  classical
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Chart reading of a harmonic surface function is plane-harmonic. -/
  have htransfer : ∀ (x : M) (Ωt : Set M) (v : M → ℝ), MHarmonicOn v Ωt →
      ∀ w ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ωt,
        HarmonicAt (v ∘ (chartAt ℂ x).symm) w := by
    intro x Ωt v hv w hw
    obtain ⟨hwt, hwΩ⟩ := hw
    have hwΩ' : (chartAt ℂ x).symm w ∈ Ωt := hwΩ
    have hyy : (chartAt ℂ x).symm w ∈ (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
      mem_chart_source ℂ ((chartAt ℂ x).symm w)
    have htrans : AnalyticAt ℂ
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w := by
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hwt
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ ((chartAt ℂ x).symm w)))
          ((chartAt ℂ x).symm w) :=
        contMDiffAt_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas ((chartAt ℂ x).symm w)) hyy
      exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
    have hmh : HarmonicAt (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        ((⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w) := hv _ hwΩ'
    have hcomp := harmonicAt_comp_analyticAt hmh htrans
    have hev : (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 w]
        v ∘ ⇑(chartAt ℂ x).symm := by
      have hS : IsOpen ((chartAt ℂ x).target ∩
          ⇑(chartAt ℂ x).symm ⁻¹' (chartAt ℂ ((chartAt ℂ x).symm w)).source) :=
        (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ x).open_target
          (chartAt ℂ ((chartAt ℂ x).symm w)).open_source
      filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with ζ hζ
      simp only [Function.comp_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hζ.2]
    exact (harmonicAt_congr_nhds hev).mp hcomp
  /- ## A plane-harmonic function reads back through a chart as surface-harmonic. -/
  have pullback : ∀ (x₀ : M) (H : ℂ → ℝ) (x : M), x ∈ (chartAt ℂ x₀).source →
      HarmonicAt H (chartAt ℂ x₀ x) → MHarmonicAt (fun y ↦ H (chartAt ℂ x₀ y)) x := by
    intro x₀ H x hx hH
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hx]
    have hev : H =ᶠ[𝓝 (chartAt ℂ x₀ x)]
        ((fun y ↦ H (chartAt ℂ x₀ y)) ∘ (chartAt ℂ x₀).symm) := by
      filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
        ((chartAt ℂ x₀).map_source hx)] with w hw
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x₀).right_inv hw]
    exact (harmonicAt_congr_nhds hev).mp hH
  have mharmSub : ∀ (f g : M → ℝ) (z : M), MHarmonicAt f z → MHarmonicAt g z →
      MHarmonicAt (fun y ↦ f y - g y) z := by
    intro f g z hf hg
    refine mharm_congr (f + -g) _ z (Filter.Eventually.of_forall fun y ↦ ?_) (hf.add hg.neg)
    simp only [Pi.add_apply, Pi.neg_apply]
    exact (sub_eq_add_neg (f y) (g y)).symm
  /- ## The chart logarithm barrier: harmonicity and continuity off the singularity. -/
  have logHarm : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      MHarmonicAt (fun q ↦ Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hzs]
    have hharm : HarmonicAt (fun w : ℂ ↦ Real.log ‖w - c‖) (chartAt ℂ x₀ z) := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ ↦ w - c)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hzne
    have heqv : (fun w : ℂ ↦ Real.log ‖w - c‖) =ᶠ[𝓝 (chartAt ℂ x₀ z)]
        ((fun q ↦ Real.log (dist (chartAt ℂ x₀ q) c)) ∘ (chartAt ℂ x₀).symm) := by
      filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
        ((chartAt ℂ x₀).map_source hzs)] with w hw
      simp only [Function.comp_apply, (chartAt ℂ x₀).right_inv hw, dist_eq_norm]
    exact (harmonicAt_congr_nhds heqv).1 hharm
  have logCont : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      ContinuousAt (fun q ↦ Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    have h2 : ContinuousAt (chartAt ℂ x₀) z := (chartAt ℂ x₀).continuousAt hzs
    have h3 : dist (chartAt ℂ x₀ z) c ≠ 0 := (dist_pos.2 hzne).ne'
    exact (h2.dist continuousAt_const).log h3
  /- ## Negation of a plane-harmonic function. -/
  have harmNeg : ∀ (h : ℂ → ℝ) (s : Set ℂ), HarmonicOnNhd h s →
      HarmonicOnNhd (fun w ↦ -h w) s := by
    intro h s hh z hz
    have h1 := (hh z hz).const_smul (c := (-1 : ℝ))
    have hev : ((-1 : ℝ) • h) =ᶠ[𝓝 z] fun w ↦ -h w := by
      filter_upwards with w
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    exact (harmonicAt_congr_nhds hev).mp h1
  /- ## Membership through an inverse chart: closed balls and spheres. -/
  have hmemCB : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      closedBall c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' closedBall c s ↔ z ∈ e.source ∧ dist (e z) c ≤ s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_closedBall.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_closedBall.2 hzd, e.left_inv hzs⟩
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dite_eq_left ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dite_eq_right]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    have := hcs
    have := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon ↦ hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z ↦ pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## The pole radii and the master bound. -/
  obtain ⟨r₁, r₂, C₀, hr₁, hr₂, hC₀1, htgt1', htgt2', hav1', hav2', hGBraw⟩ :=
    exists_pieceGreen_dipole_exterior_bound D₀ hp₁ hp₂ hne
  have hC₀0 : (0 : ℝ) ≤ C₀ := by linarith only [hC₀1]
  /- ## The center chart and the shrinking pieces. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D₀.center with he₀
  set c₀ : ℂ := e₀ D₀.center with hc₀
  set r₀ : ℝ := D₀.radius with hr₀def
  have hr₀ : 0 < r₀ := D₀.radius_pos
  have hcb₀tgt : closedBall c₀ r₀ ⊆ e₀.target := D₀.closedBall_subset
  have hcar₀ : D₀.closedCarrier = e₀.symm '' closedBall c₀ r₀ := rfl
  have hcen₀src : D₀.center ∈ e₀.source := mem_chart_source ℂ D₀.center
  have hcen₀car : D₀.center ∈ D₀.closedCarrier :=
    ⟨c₀, mem_closedBall_self hr₀.le, e₀.left_inv hcen₀src⟩
  set t : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 2) with ht
  have ht0 : ∀ n, 0 < t n := fun n ↦ by rw [ht]; positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n ↦ pow_le_one₀ (by norm_num) (by norm_num)
  have htq : ∀ n, t n ≤ 1 / 4 := by
    intro n
    calc t n = (1 / 2 : ℝ) ^ (n + 2) := rfl
      _ ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have htanti : ∀ n m, n ≤ m → t m ≤ t n := fun n m h ↦
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htlim : ∀ δ : ℝ, 0 < δ → ∃ n, t n < δ := by
    intro δ hδ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn⟩
  set DN : ℕ → CoordDisk M := fun n ↦ D₀.shrink (t n) (ht0 n) (ht1 n) with hDN
  set Wp : ℕ → Opens M := fun n ↦ (DN n).compl with hWp
  have hcarN : ∀ n, (DN n).closedCarrier = e₀.symm '' closedBall c₀ (t n * r₀) :=
    fun n ↦ rfl
  have hcarNsub : ∀ n, (DN n).closedCarrier ⊆ D₀.closedCarrier := by
    intro n
    rw [hcarN n, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le (ht1 n)))
  have hcarmono : ∀ n m, n ≤ m → (DN m).closedCarrier ⊆ (DN n).closedCarrier := by
    intro n m hnm
    rw [hcarN n, hcarN m]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (htanti n m hnm) hr₀.le))
  have hcbtgtN : ∀ n, closedBall c₀ (t n * r₀) ⊆ e₀.target := fun n ↦
    (closedBall_subset_closedBall (mul_le_of_le_one_left hr₀.le (ht1 n))).trans hcb₀tgt
  have hcarmem : ∀ n (z : M), z ∈ (DN n).closedCarrier ↔
      z ∈ e₀.source ∧ dist (e₀ z) c₀ ≤ t n * r₀ := by
    intro n z
    rw [hcarN n]
    exact hmemCB e₀ c₀ (t n * r₀) (hcbtgtN n) z
  have hp₁W : ∀ n, p₁ ∈ Wp n := fun n hmem ↦ hp₁ (hcarNsub n hmem)
  have hp₂W : ∀ n, p₂ ∈ Wp n := fun n hmem ↦ hp₂ (hcarNsub n hmem)
  have hConnW : ∀ n, ConnectedSpace ↥(Wp n) := fun n ↦
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl (DN n))
  have hNcW : ∀ n, NoncompactSpace ↥(Wp n) := fun n ↦
    noncompactSpace_coordDisk_compl (DN n)
  have hGF1 : ∀ n, HasGreenFunction (⟨p₁, hp₁W n⟩ : ↥(Wp n)) := fun n ↦
    hasGreenFunction_coordDisk_compl (DN n) p₁ (hp₁W n)
  have hGF2 : ∀ n, HasGreenFunction (⟨p₂, hp₂W n⟩ : ↥(Wp n)) := fun n ↦
    hasGreenFunction_coordDisk_compl (DN n) p₂ (hp₂W n)
  set Gs : ℕ → M → ℝ :=
    fun n x ↦ pieceGreen (Wp n) p₁ x - pieceGreen (Wp n) p₂ x with hGs
  /- ## The pole charts, the avoidance sets and the pole balls. -/
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  have htgt1 : closedBall c₁ (2 * r₁) ⊆ e₁.target := htgt1'
  have htgt2 : closedBall c₂ (2 * r₂) ⊆ e₂.target := htgt2'
  have hav1 : ∀ w ∈ closedBall c₁ (2 * r₁),
      e₁.symm w ∉ D₀.closedCarrier ∧ e₁.symm w ≠ p₂ := hav1'
  have hav2 : ∀ w ∈ closedBall c₂ (2 * r₂),
      e₂.symm w ∉ D₀.closedCarrier ∧
        e₂.symm w ∉ e₁.symm '' closedBall c₁ (2 * r₁) := hav2'
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ := by
    rintro z ⟨w, hw, rfl⟩
    exact hav1 w hw
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 := by
    rintro z ⟨w, hw, rfl⟩
    exact hav2 w hw
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  set B₁ : Set M := e₁.source ∩ e₁ ⁻¹' ball c₁ r₁ with hB₁
  set B₂ : Set M := e₂.source ∩ e₂ ⁻¹' ball c₂ r₂ with hB₂
  have hB₁open : IsOpen B₁ := e₁.isOpen_inter_preimage isOpen_ball
  have hB₂open : IsOpen B₂ := e₂.isOpen_inter_preimage isOpen_ball
  have hp₁B₁ : p₁ ∈ B₁ :=
    ⟨hp₁src, by rw [Set.mem_preimage, ← hc₁]; exact mem_ball_self hr₁⟩
  have hp₂B₂ : p₂ ∈ B₂ :=
    ⟨hp₂src, by rw [Set.mem_preimage, ← hc₂]; exact mem_ball_self hr₂⟩
  have hB₁img : e₁.symm '' ball c₁ r₁ = B₁ :=
    himg e₁ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1)
  have hB₂img : e₂.symm '' ball c₂ r₂ = B₂ :=
    himg e₂ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2)
  have hB₁Car : B₁ ⊆ Car1 := by
    rw [← hB₁img, hCar1]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁])))
  have hB₂Car : B₂ ⊆ Car2 := by
    rw [← hB₂img, hCar2]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂])))
  /- ## The quarter disk at the center and the half pole disks. -/
  set Dq : CoordDisk M := D₀.shrink (1 / 4) (by norm_num) (by norm_num) with hDq
  have hDqcar : Dq.closedCarrier = e₀.symm '' closedBall c₀ (1 / 4 * r₀) := rfl
  have hDqsub : Dq.closedCarrier ⊆ D₀.closedCarrier := by
    rw [hDqcar, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₀]))
  have hcarNq : ∀ n, (DN n).closedCarrier ⊆ Dq.closedCarrier := by
    intro n
    rw [hcarN n, hDqcar]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (htq n) hr₀.le))
  set half1 : CoordDisk M := ⟨p₁, r₁ / 2, by linarith only [hr₁],
    (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1⟩ with hhalf1
  set half2 : CoordDisk M := ⟨p₂, r₂ / 2, by linarith only [hr₂],
    (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2⟩ with hhalf2
  have hhalf1car : half1.closedCarrier = e₁.symm '' closedBall c₁ (r₁ / 2) := rfl
  have hhalf2car : half2.closedCarrier = e₂.symm '' closedBall c₂ (r₂ / 2) := rfl
  have hhalf1Car : half1.closedCarrier ⊆ Car1 := by
    rw [hhalf1car, hCar1]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₁]))
  have hhalf2Car : half2.closedCarrier ⊆ Car2 := by
    rw [hhalf2car, hCar2]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₂]))
  have hp₁half : p₁ ∈ half1.closedCarrier := by
    rw [hhalf1car]
    exact ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂half : p₂ ∈ half2.closedCarrier := by
    rw [hhalf2car]
    exact ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  /- ## The master bound along the shrinking sequence. -/
  have hGB : ∀ n, ∀ x : M, x ∉ B₁ → x ∉ B₂ → |Gs n x| ≤ C₀ :=
    fun n x h1 h2 ↦ hGBraw (t n) (ht0 n) (ht1 n) (htq n) x h1 h2
  /- ## The pole companion sequences from the per-piece companions. -/
  have hdisj12' : ∀ w ∈ closedBall c₁ (2 * r₁),
      e₁.symm w ∉ e₂.symm '' closedBall c₂ (2 * r₂) := by
    intro w hw hmem
    obtain ⟨v, hv, hveq⟩ := hmem
    have h1 := (hav2 v hv).2
    rw [hveq] at h1
    exact h1 ⟨w, hw, rfl⟩
  have hpole1 : ∀ n, ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball c₁ (2 * r₁)) ∧
      (∀ w ∈ ball c₁ (2 * r₁) \ {c₁},
        h w = Gs n (e₁.symm w) + Real.log ‖w - c₁‖) ∧
      ∀ w ∈ ball c₁ (2 * r₁), |h w| ≤ C₀ + (|Real.log r₁| + |Real.log (2 * r₁)|) := by
    intro n
    obtain ⟨h, hharm, hval, hbd⟩ := exists_harmonicOnNhd_pieceGreen_dipole_add_log
      D₀ hr₁ hr₂ htgt1 (fun w hw ↦ (hav1 w hw).1) (fun w hw ↦ (hav1 w hw).2)
      (fun w hw ↦ (hav2 w hw).1) hdisj12' (t n) (ht0 n) (ht1 n)
      (fun x h1 h2 ↦ hGB n x h1 h2)
    exact ⟨h, hharm, fun w hw ↦ hval w hw, hbd⟩
  have hpole2 : ∀ n, ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball c₂ (2 * r₂)) ∧
      (∀ w ∈ ball c₂ (2 * r₂) \ {c₂},
        h w = -Gs n (e₂.symm w) + Real.log ‖w - c₂‖) ∧
      ∀ w ∈ ball c₂ (2 * r₂), |h w| ≤ C₀ + (|Real.log r₂| + |Real.log (2 * r₂)|) := by
    intro n
    obtain ⟨h, hharm, hval, hbd⟩ := exists_harmonicOnNhd_pieceGreen_dipole_add_log D₀ hr₂ hr₁ htgt2
      (fun w hw ↦ (hav2 w hw).1)
      (fun w hw ↦ fun hcon ↦ (hav2 w hw).2 (hcon ▸ hp₁Car1))
      (fun w hw ↦ (hav1 w hw).1) (fun w hw ↦ (hav2 w hw).2) (t n) (ht0 n) (ht1 n)
      (fun x h1 h2 ↦ by
        have h3 := hGB n x h2 h1
        have h4 := abs_sub_comm (pieceGreen (Wp n) p₁ x) (pieceGreen (Wp n) p₂ x)
        simp only [hGs] at h3
        rw [← h4]
        exact h3)
    refine ⟨h, hharm, fun w hw ↦ ?_, hbd⟩
    have h5 := hval w hw
    simp only [hGs]
    linarith only [h5]
  choose h1s hh1harm hh1val hh1bd using hpole1
  choose h2s hh2harm hh2val hh2bd using hpole2
  have hGsharmAt : ∀ n (z : M), z ∈ Wp n → z ≠ p₁ → z ≠ p₂ → MHarmonicAt (Gs n) z
      := by
    intro n z hzP hz1 hz2
    exact mharmSub _ _ z
      (pgharm (Wp n) p₁ (hp₁W n) (hConnW n) (hNcW n) (hGF1 n) z hzP hz1)
      (pgharm (Wp n) p₂ (hp₂W n) (hConnW n) (hNcW n) (hGF2 n) z hzP hz2)
  /- ## The fixed outer circle for the center estimate. -/
  set ρs : ℝ := 3 * r₀ / 4 with hρs
  have hρs0 : 0 < ρs := by rw [hρs]; linarith only [hr₀]
  have hρsr₀ : ρs < r₀ := by rw [hρs]; linarith only [hr₀]
  have hsph0tgt : sphere c₀ ρs ⊆ e₀.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall hρsr₀.le)).trans hcb₀tgt
  set Γ₀ : Set M := e₀.symm '' sphere c₀ ρs with hΓ₀
  have hΓ₀cp : IsCompact Γ₀ := (isCompact_sphere _ _).image_of_continuousOn
    (e₀.continuousOn_symm.mono hsph0tgt)
  have hδlt : ∀ n, t n * r₀ < ρs := by
    intro n
    have h1 := htq n
    have h2 : t n * r₀ ≤ 1 / 4 * r₀ := mul_le_mul_of_nonneg_right h1 hr₀.le
    rw [hρs]
    linarith only [h2, hr₀]
  have hden : ∀ n, 0 < Real.log ρs - Real.log (t n * r₀) := by
    intro n
    have h1 : Real.log (t n * r₀) < Real.log ρs := by
      apply Real.log_lt_log
      · exact mul_pos (ht0 n) hr₀
      · exact hδlt n
    linarith only [h1]
  /- ## The absolute logarithm on a sandwiched radius. -/
  have hlogsand : ∀ (a b d : ℝ), 0 < a → a < d → d < b →
      |Real.log d| ≤ |Real.log a| + |Real.log b| := by
    intro a b d ha had hdb
    have h1 : Real.log a ≤ Real.log d := Real.log_le_log ha had.le
    have h2 : Real.log d ≤ Real.log b := Real.log_le_log (lt_trans ha had) hdb.le
    rw [abs_le]
    constructor
    · linarith only [h1, neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
    · linarith only [h2, le_abs_self (Real.log b), abs_nonneg (Real.log a)]
  /- ## The fixed extraction domain. -/
  set Ωqq : Set M := (Dq.closedCarrier ∪ half1.closedCarrier ∪ half2.closedCarrier)ᶜ
    with hΩqq
  have hΩqqopen : IsOpen Ωqq := ((Dq.isCompact_closedCarrier.union
    half1.isCompact_closedCarrier).union
      half2.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩqqW : ∀ x ∈ Ωqq, ∀ n, x ∈ Wp n := by
    intro x hx n hmem
    exact hx (Or.inl (Or.inl (hcarNq n hmem)))
  have hΩqqp₁ : ∀ x ∈ Ωqq, x ≠ p₁ := by
    intro x hx hcon
    exact hx (Or.inl (Or.inr (hcon ▸ hp₁half)))
  have hΩqqp₂ : ∀ x ∈ Ωqq, x ≠ p₂ := by
    intro x hx hcon
    exact hx (Or.inr (hcon ▸ hp₂half))
  have hGsharmΩqq : ∀ n, MHarmonicOn (Gs n) Ωqq := fun n x hx ↦
    hGsharmAt n x (hΩqqW x hx n) (hΩqqp₁ x hx) (hΩqqp₂ x hx)
  /- ## The dipole differences read through the pole companions inside the balls. -/
  have hGsB₁ : ∀ n, ∀ x ∈ B₁, x ≠ p₁ →
      Gs n x = h1s n (e₁ x) - Real.log ‖e₁ x - c₁‖ := by
    intro n x hx hxne
    obtain ⟨hxsrc, hxpre⟩ := hx
    rw [Set.mem_preimage] at hxpre
    have hw : e₁ x ∈ ball c₁ (2 * r₁) :=
      ball_subset_ball (by linarith only [hr₁]) hxpre
    have hwne : e₁ x ≠ c₁ := by
      intro hcon
      have h2 := congrArg (⇑e₁.symm) hcon
      rw [e₁.left_inv hxsrc] at h2
      rw [hc₁, e₁.left_inv hp₁src] at h2
      exact hxne h2
    have hval := hh1val n (e₁ x) ⟨hw, by simpa using hwne⟩
    rw [e₁.left_inv hxsrc] at hval
    linarith only [hval]
  have hGsB₂ : ∀ n, ∀ x ∈ B₂, x ≠ p₂ →
      Gs n x = Real.log ‖e₂ x - c₂‖ - h2s n (e₂ x) := by
    intro n x hx hxne
    obtain ⟨hxsrc, hxpre⟩ := hx
    rw [Set.mem_preimage] at hxpre
    have hw : e₂ x ∈ ball c₂ (2 * r₂) :=
      ball_subset_ball (by linarith only [hr₂]) hxpre
    have hwne : e₂ x ≠ c₂ := by
      intro hcon
      have h2 := congrArg (⇑e₂.symm) hcon
      rw [e₂.left_inv hxsrc] at h2
      rw [hc₂, e₂.left_inv hp₂src] at h2
      exact hxne h2
    have hval := hh2val n (e₂ x) ⟨hw, by simpa using hwne⟩
    rw [e₂.left_inv hxsrc] at hval
    linarith only [hval]
  /- ## The uniform bound on the extraction domain. -/
  set Cq : ℝ := C₀ + (C₀ + (|Real.log r₁| + |Real.log (2 * r₁)|) +
      (|Real.log (r₁ / 2)| + |Real.log r₁|)) +
      (C₀ + (|Real.log r₂| + |Real.log (2 * r₂)|) +
      (|Real.log (r₂ / 2)| + |Real.log r₂|)) with hCq
  have hΩqqbd : ∀ n, ∀ x ∈ Ωqq, |Gs n x| ≤ Cq := by
    intro n x hx
    have hpad1 : (0 : ℝ) ≤ C₀ + (|Real.log r₁| + |Real.log (2 * r₁)|) +
        (|Real.log (r₁ / 2)| + |Real.log r₁|) :=
      add_nonneg (add_nonneg hC₀0 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hpad2 : (0 : ℝ) ≤ C₀ + (|Real.log r₂| + |Real.log (2 * r₂)|) +
        (|Real.log (r₂ / 2)| + |Real.log r₂|) :=
      add_nonneg (add_nonneg hC₀0 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    by_cases hx1 : x ∈ B₁
    · have hxne : x ≠ p₁ := hΩqqp₁ x hx
      have hxnothalf : x ∉ half1.closedCarrier := fun hmem ↦ hx (Or.inl (Or.inr hmem))
      have hcbsub1 : closedBall c₁ (r₁ / 2) ⊆ closedBall c₁ (2 * r₁) :=
        closedBall_subset_closedBall (by linarith only [hr₁])
      have hd : r₁ / 2 < dist (e₁ x) c₁ := by
        by_contra hcon
        push Not at hcon
        apply hxnothalf
        rw [hhalf1car]
        exact (hmemCB e₁ c₁ (r₁ / 2) (hcbsub1.trans htgt1) x).2 ⟨hx1.1, hcon⟩
      have hd2 : dist (e₁ x) c₁ < r₁ := by
        have h1 := hx1.2
        rw [Set.mem_preimage, mem_ball] at h1
        exact h1
      have hhalfpos : 0 < r₁ / 2 := half_pos hr₁
      have hlog : |Real.log ‖e₁ x - c₁‖| ≤ |Real.log (r₁ / 2)| + |Real.log r₁| := by
        have hn : ‖e₁ x - c₁‖ = dist (e₁ x) c₁ := (dist_eq_norm _ _).symm
        rw [hn]
        exact hlogsand (r₁ / 2) r₁ (dist (e₁ x) c₁) hhalfpos hd hd2
      have hxball : e₁ x ∈ ball c₁ (2 * r₁) := by
        rw [mem_ball]
        linarith only [hd2, hr₁]
      have hb := hh1bd n (e₁ x) hxball
      rw [hGsB₁ n x hx1 hxne]
      calc |h1s n (e₁ x) - Real.log ‖e₁ x - c₁‖|
          ≤ |h1s n (e₁ x)| + |Real.log ‖e₁ x - c₁‖| := abs_sub _ _
        _ ≤ Cq := by
            rw [hCq]
            linarith only [hb, hlog, hC₀0, hpad2]
    · by_cases hx2 : x ∈ B₂
      · have hxne : x ≠ p₂ := hΩqqp₂ x hx
        have hxnothalf : x ∉ half2.closedCarrier := fun hmem ↦ hx (Or.inr hmem)
        have hcbsub2 : closedBall c₂ (r₂ / 2) ⊆ closedBall c₂ (2 * r₂) :=
          closedBall_subset_closedBall (by linarith only [hr₂])
        have hd : r₂ / 2 < dist (e₂ x) c₂ := by
          by_contra hcon
          push Not at hcon
          apply hxnothalf
          rw [hhalf2car]
          exact (hmemCB e₂ c₂ (r₂ / 2) (hcbsub2.trans htgt2) x).2 ⟨hx2.1, hcon⟩
        have hd2 : dist (e₂ x) c₂ < r₂ := by
          have h1 := hx2.2
          rw [Set.mem_preimage, mem_ball] at h1
          exact h1
        have hhalfpos : 0 < r₂ / 2 := half_pos hr₂
        have hlog : |Real.log ‖e₂ x - c₂‖| ≤ |Real.log (r₂ / 2)| + |Real.log r₂| := by
          have hn : ‖e₂ x - c₂‖ = dist (e₂ x) c₂ := (dist_eq_norm _ _).symm
          rw [hn]
          exact hlogsand (r₂ / 2) r₂ (dist (e₂ x) c₂) hhalfpos hd hd2
        have hxball : e₂ x ∈ ball c₂ (2 * r₂) := by
          rw [mem_ball]
          linarith only [hd2, hr₂]
        have hb := hh2bd n (e₂ x) hxball
        rw [hGsB₂ n x hx2 hxne]
        calc |Real.log ‖e₂ x - c₂‖ - h2s n (e₂ x)|
            ≤ |Real.log ‖e₂ x - c₂‖| + |h2s n (e₂ x)| := abs_sub _ _
          _ ≤ Cq := by
              rw [hCq]
              linarith only [hb, hlog, hC₀0, hpad1]
      · have h1 := hGB n x hx1 hx2
        rw [hCq]
        linarith only [h1, hpad1, hpad2]
  /- ## The normal-families extraction on the fixed domain. -/
  obtain ⟨φ, hφmono, Gout, hGoutharm, hGoutunif⟩ :=
    exists_mharmonicOn_limit_of_locally_bounded hΩqqopen hGsharmΩqq
      (fun K hK hKsub ↦ ⟨Cq, fun n x hx ↦ hΩqqbd n x (hKsub hx)⟩)
  /- ## Uniform Cauchy control on compact subsets of the extraction domain. -/
  have hcompCau : ∀ (T : Set M), IsCompact T → T ⊆ Ωqq → ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ z ∈ T, |Gs (φ m) z - Gs (φ n) z| ≤ ε := by
    intro T hT hTsub ε hε
    have h1 := hGoutunif T hT hTsub
    rw [Metric.tendstoUniformlyOn_iff] at h1
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h1 (ε / 2) (half_pos hε))
    refine ⟨N, fun m hm n hn z hz ↦ ?_⟩
    have hm1 := hN m hm z hz
    have hn1 := hN n hn z hz
    rw [Real.dist_eq] at hm1 hn1
    have hm2 : |Gs (φ m) z - Gout z| ≤ ε / 2 := by
      rw [abs_sub_comm]
      exact hm1.le
    calc |Gs (φ m) z - Gs (φ n) z|
        ≤ |Gs (φ m) z - Gout z| + |Gout z - Gs (φ n) z| := abs_sub_le _ _ _
      _ ≤ ε := by linarith only [hm2, hn1]
  /- ## The sphere Cauchy inputs for the two poles. -/
  have hsph1tgt' : sphere c₁ (3 * r₁ / 2) ⊆ e₁.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1
  have hsph2tgt' : sphere c₂ (3 * r₂ / 2) ⊆ e₂.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2
  have hcau1 : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ sphere c₁ (3 *
      r₁ / 2),
      |h1s (φ m) ζ - h1s (φ n) ζ| ≤ ε := by
    intro ε hε
    have hΓcp : IsCompact (e₁.symm '' sphere c₁ (3 * r₁ / 2)) :=
      (isCompact_sphere _ _).image_of_continuousOn
        (e₁.continuousOn_symm.mono hsph1tgt')
    have hΓsub : e₁.symm '' sphere c₁ (3 * r₁ / 2) ⊆ Ωqq := by
      rintro z ⟨w, hw, rfl⟩
      have hzcar : e₁.symm w ∈ Car1 := ⟨w, sphere_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith only [hr₁])) hw, rfl⟩
      rintro ((hmem | hmem) | hmem)
      · exact (hCar1av _ hzcar).1 (hDqsub hmem)
      · rw [hhalf1car] at hmem
        obtain ⟨hsrc2, hd2⟩ := (hmemCB e₁ c₁ (r₁ / 2)
          ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1) _).1
          hmem
        have hd3 : dist (e₁ (e₁.symm w)) c₁ = 3 * r₁ / 2 := by
          rw [e₁.right_inv (hsph1tgt' hw)]
          exact mem_sphere.1 hw
        rw [hd3] at hd2
        linarith only [hd2, hr₁]
      · exact (hCar2av _ (hhalf2Car hmem)).2 hzcar
    obtain ⟨N, hN⟩ := hcompCau _ hΓcp hΓsub ε hε
    refine ⟨N, fun m hm n hn ζ hζ ↦ ?_⟩
    have hz : e₁.symm ζ ∈ e₁.symm '' sphere c₁ (3 * r₁ / 2) := ⟨ζ, hζ, rfl⟩
    have hζball : ζ ∈ ball c₁ (2 * r₁) \ {c₁} := by
      have hd : dist ζ c₁ = 3 * r₁ / 2 := mem_sphere.1 hζ
      constructor
      · rw [mem_ball, hd]
        linarith only [hr₁]
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        rw [hcon, dist_self] at hd
        linarith only [hd, hr₁]
    have hvm := hh1val (φ m) ζ hζball
    have hvn := hh1val (φ n) ζ hζball
    have heq : h1s (φ m) ζ - h1s (φ n) ζ =
        Gs (φ m) (e₁.symm ζ) - Gs (φ n) (e₁.symm ζ) := by
      rw [hvm, hvn]
      ring
    rw [heq]
    exact hN m hm n hn _ hz
  have hcau2 : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ sphere c₂ (3 *
      r₂ / 2),
      |h2s (φ m) ζ - h2s (φ n) ζ| ≤ ε := by
    intro ε hε
    have hΓcp : IsCompact (e₂.symm '' sphere c₂ (3 * r₂ / 2)) :=
      (isCompact_sphere _ _).image_of_continuousOn
        (e₂.continuousOn_symm.mono hsph2tgt')
    have hΓsub : e₂.symm '' sphere c₂ (3 * r₂ / 2) ⊆ Ωqq := by
      rintro z ⟨w, hw, rfl⟩
      have hzcar : e₂.symm w ∈ Car2 := ⟨w, sphere_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith only [hr₂])) hw, rfl⟩
      rintro ((hmem | hmem) | hmem)
      · exact (hCar2av _ hzcar).1 (hDqsub hmem)
      · exact (hCar2av _ hzcar).2 (hhalf1Car hmem)
      · rw [hhalf2car] at hmem
        obtain ⟨hsrc2, hd2⟩ := (hmemCB e₂ c₂ (r₂ / 2)
          ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2) _).1
          hmem
        have hd3 : dist (e₂ (e₂.symm w)) c₂ = 3 * r₂ / 2 := by
          rw [e₂.right_inv (hsph2tgt' hw)]
          exact mem_sphere.1 hw
        rw [hd3] at hd2
        linarith only [hd2, hr₂]
    obtain ⟨N, hN⟩ := hcompCau _ hΓcp hΓsub ε hε
    refine ⟨N, fun m hm n hn ζ hζ ↦ ?_⟩
    have hz : e₂.symm ζ ∈ e₂.symm '' sphere c₂ (3 * r₂ / 2) := ⟨ζ, hζ, rfl⟩
    have hζball : ζ ∈ ball c₂ (2 * r₂) \ {c₂} := by
      have hd : dist ζ c₂ = 3 * r₂ / 2 := mem_sphere.1 hζ
      constructor
      · rw [mem_ball, hd]
        linarith only [hr₂]
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        rw [hcon, dist_self] at hd
        linarith only [hd, hr₂]
    have hvm := hh2val (φ m) ζ hζball
    have hvn := hh2val (φ n) ζ hζball
    have heq : h2s (φ m) ζ - h2s (φ n) ζ =
        -(Gs (φ m) (e₂.symm ζ) - Gs (φ n) (e₂.symm ζ)) := by
      rw [hvm, hvn]
      ring
    rw [heq, abs_neg]
    exact hN m hm n hn _ hz
  obtain ⟨H1, hH1harm, hH1tend⟩ := exists_harmonicOnNhd_tendsto_of_cauchy_sphere
    (fun n ↦ h1s (φ n)) hr₁
    (fun n ↦ hh1harm (φ n)) hcau1
  obtain ⟨H2, hH2harm, hH2tend⟩ := exists_harmonicOnNhd_tendsto_of_cauchy_sphere
    (fun n ↦ h2s (φ n)) hr₂
    (fun n ↦ hh2harm (φ n)) hcau2
  /- ## The outer circle sits inside the extraction domain. -/
  have hQtgt : closedBall c₀ (1 / 4 * r₀) ⊆ e₀.target :=
    (closedBall_subset_closedBall (by linarith only [hr₀])).trans hcb₀tgt
  have hΓ₀sub : Γ₀ ⊆ Ωqq := by
    rw [hΓ₀]
    rintro z ⟨w, hw, rfl⟩
    have hwt : w ∈ e₀.target := hsph0tgt hw
    have hd : dist (e₀ (e₀.symm w)) c₀ = ρs := by
      rw [e₀.right_inv hwt]
      exact mem_sphere.1 hw
    have hcar : e₀.symm w ∈ D₀.closedCarrier := by
      rw [hcar₀]
      exact ⟨w, sphere_subset_closedBall.trans
        (closedBall_subset_closedBall hρsr₀.le) hw, rfl⟩
    rintro ((hmem | hmem) | hmem)
    · rw [hDqcar] at hmem
      obtain ⟨hsrc2, hd2⟩ := (hmemCB e₀ c₀ (1 / 4 * r₀) hQtgt _).1 hmem
      rw [hd] at hd2
      linarith only [hd2, hr₀, hρs]
    · exact (hCar1av _ (hhalf1Car hmem)).1 hcar
    · exact (hCar2av _ (hhalf2Car hmem)).1 hcar
  /- ## The barrier constant decays along the shrinking pieces. -/
  have hbarrier : ∀ (ε Lx : ℝ), 0 < ε → 0 ≤ Lx → ∃ N : ℕ, ∀ k ≥ N,
      4 * C₀ / (Real.log ρs - Real.log (t k * r₀)) * Lx ≤ ε := by
    intro ε Lx hε hLx
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hgrow : ∀ k : ℕ, Real.log ρs - Real.log (t k * r₀)
        = Real.log ρs - Real.log r₀ + ((k : ℝ) + 2) * Real.log 2 := by
      intro k
      have h1 : Real.log (t k * r₀) = Real.log (t k) + Real.log r₀ :=
        Real.log_mul (ht0 k).ne' hr₀.ne'
      have h2 : Real.log (t k) = -(((k : ℝ) + 2) * Real.log 2) := by
        have h3 : t k = (1 / 2 : ℝ) ^ (k + 2) := rfl
        rw [h3, Real.log_pow, one_div, Real.log_inv]
        push_cast
        ring
      rw [h1, h2]
      ring
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((4 * C₀ * Lx / ε - (Real.log ρs - Real.log r₀)) / Real.log 2 - 2)
    refine ⟨N, fun k hk ↦ ?_⟩
    have hden' := hden k
    rw [div_mul_eq_mul_div, div_le_iff₀ hden']
    have hkN : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
    have h5 : (4 * C₀ * Lx / ε - (Real.log ρs - Real.log r₀)) / Real.log 2
        < (k : ℝ) + 2 := by
      linarith only [hN, hkN]
    rw [div_lt_iff₀ hlog2] at h5
    have h6 : 4 * C₀ * Lx / ε < Real.log ρs - Real.log r₀ +
        ((k : ℝ) + 2) * Real.log 2 := by
      linarith only [h5]
    rw [div_lt_iff₀ hε] at h6
    rw [hgrow k]
    have h7 : ε * (Real.log ρs - Real.log r₀ + ((k : ℝ) + 2) * Real.log 2)
        = (Real.log ρs - Real.log r₀ + ((k : ℝ) + 2) * Real.log 2) * ε :=
      mul_comm _ _
    linarith only [h6, h7]
  /- ## The uniform Cauchy estimate through the log barrier. -/
  have hcauAt : ∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x : M, x ∈ e₀.source → a ≤ dist (e₀ x) c₀ → dist (e₀ x) c₀ < ρs →
      |Gs (φ m) x - Gs (φ n) x| ≤ ε := by
    intro a ha ε hε
    rcases lt_or_ge a ρs with haρ | haρ
    · have hLm0 : 0 ≤ Real.log ρs - Real.log a := by
        have h1 : Real.log a ≤ Real.log ρs := Real.log_le_log ha haρ.le
        linarith only [h1]
      obtain ⟨N₁, hN₁⟩ := hcompCau Γ₀ hΓ₀cp hΓ₀sub (ε / 3) (by linarith only
          [hε])
      obtain ⟨N₂, hN₂⟩ := hbarrier (ε / 3) (Real.log ρs - Real.log a)
        (by linarith only [hε]) hLm0
      obtain ⟨N₃, hN₃⟩ := htlim (a / r₀) (div_pos ha hr₀)
      refine ⟨max N₁ (max N₂ N₃), fun m hm n hn x hxsrc hxa hxρ ↦ ?_⟩
      have hmn : max N₁ (max N₂ N₃) ≤ min m n := le_min hm hn
      have hAk : min m n ≤ φ (min m n) := hφmono.le_apply
      have hN₂A : N₂ ≤ φ (min m n) :=
        le_trans (le_trans (le_trans (le_max_left N₂ N₃) (le_max_right N₁ _)) hmn) hAk
      have hN₃A : N₃ ≤ φ (min m n) :=
        le_trans (le_trans (le_trans (le_max_right N₂ N₃) (le_max_right N₁ _)) hmn) hAk
      have hδsm : t (φ (min m n)) * r₀ < dist (e₀ x) c₀ := by
        have h1 : t (φ (min m n)) ≤ t N₃ := htanti N₃ _ hN₃A
        have h3 : t (φ (min m n)) * r₀ ≤ t N₃ * r₀ :=
          mul_le_mul_of_nonneg_right h1 hr₀.le
        have h4 : t N₃ * r₀ < a / r₀ * r₀ := mul_lt_mul_of_pos_right hN₃ hr₀
        have h5 : a / r₀ * r₀ = a := div_mul_cancel₀ _ hr₀.ne'
        linarith only [h3, h4, h5, hxa]
      have hsub1 : (DN (φ m)).closedCarrier ⊆ (DN (φ (min m n))).closedCarrier :=
        hcarmono _ _ (hφmono.monotone (min_le_left m n))
      have hsub2 : (DN (φ n)).closedCarrier ⊆ (DN (φ (min m n))).closedCarrier :=
        hcarmono _ _ (hφmono.monotone (min_le_right m n))
      have hN₁m : N₁ ≤ m := le_trans (le_max_left _ _) hm
      have hN₁n : N₁ ≤ n := le_trans (le_max_left _ _) hn
      have hsph1 : ∀ z ∈ Γ₀, Gs (φ m) z - Gs (φ n) z ≤ ε / 3 := by
        intro z hz
        have h1 := (abs_le.1 (hN₁ m hN₁m n hN₁n z hz)).2
        linarith only [h1]
      have hsph2 : ∀ z ∈ Γ₀, Gs (φ n) z - Gs (φ m) z ≤ ε / 3 := by
        intro z hz
        have h1 := (abs_le.1 (hN₁ m hN₁m n hN₁n z hz)).1
        linarith only [h1]
      have hbar := hN₂ (φ (min m n)) hN₂A
      have hQ0 : 0 ≤ 4 * C₀ / (Real.log ρs - Real.log (t (φ (min m n)) * r₀)) :=
        div_nonneg (by linarith only [hC₀1]) (hden (φ (min m n))).le
      have hLζ : Real.log ρs - Real.log (dist (e₀ x) c₀) ≤
          Real.log ρs - Real.log a := by
        have h1 : Real.log a ≤ Real.log (dist (e₀ x) c₀) := Real.log_le_log ha hxa
        linarith only [h1]
      have hmono := mul_le_mul_of_nonneg_left hLζ hQ0
      have he1 : Gs (φ m) x - Gs (φ n) x ≤ ε / 3 +
          4 * C₀ / (Real.log ρs - Real.log (t (φ (min m n)) * r₀)) *
          (Real.log ρs - Real.log (dist (e₀ x) c₀)) :=
        pieceGreen_dipole_sub_le_log_barrier D₀ hr₁ hr₂ hC₀1 htgt1 htgt2
          (fun w hw ↦ (hav1 w hw).1) (fun w hw ↦ (hav1 w hw).2)
          (fun w hw ↦ (hav2 w hw).1) (fun w hw ↦ (hav2 w hw).2)
          (ht0 (φ (min m n))) (ht1 (φ (min m n))) (htq (φ (min m n)))
          (ht0 (φ m)) (ht1 (φ m)) (ht0 (φ n)) (ht1 (φ n)) hsub1 hsub2
          (ε := ε / 3) (by linarith only [hε])
          (fun y hy1 hy2 ↦ hGB (φ m) y hy1 hy2)
          (fun y hy1 hy2 ↦ hGB (φ n) y hy1 hy2) hsph1 x hxsrc hδsm hxρ
      have he2 : Gs (φ n) x - Gs (φ m) x ≤ ε / 3 +
          4 * C₀ / (Real.log ρs - Real.log (t (φ (min m n)) * r₀)) *
          (Real.log ρs - Real.log (dist (e₀ x) c₀)) :=
        pieceGreen_dipole_sub_le_log_barrier D₀ hr₁ hr₂ hC₀1 htgt1 htgt2
          (fun w hw ↦ (hav1 w hw).1) (fun w hw ↦ (hav1 w hw).2)
          (fun w hw ↦ (hav2 w hw).1) (fun w hw ↦ (hav2 w hw).2)
          (ht0 (φ (min m n))) (ht1 (φ (min m n))) (htq (φ (min m n)))
          (ht0 (φ n)) (ht1 (φ n)) (ht0 (φ m)) (ht1 (φ m)) hsub2 hsub1
          (ε := ε / 3) (by linarith only [hε])
          (fun y hy1 hy2 ↦ hGB (φ n) y hy1 hy2)
          (fun y hy1 hy2 ↦ hGB (φ m) y hy1 hy2) hsph2 x hxsrc hδsm hxρ
      rw [abs_le]
      constructor
      · linarith only [he2, hbar, hmono, hε]
      · linarith only [he1, hbar, hmono, hε]
    · refine ⟨0, fun m _ n _ x _ hxa hxρ ↦ ?_⟩
      exact absurd (lt_of_lt_of_le hxρ (le_trans haρ hxa)) (lt_irrefl _)
  /- ## The pointwise center limit. -/
  have hcen : ∀ x : M, x ∈ e₀.source → 0 < dist (e₀ x) c₀ → dist (e₀ x) c₀ < ρs
      →
      ∃ l, Tendsto (fun n ↦ Gs (φ n) x) atTop (𝓝 l) := by
    intro x hxsrc hx0 hxρ
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauAt (dist (e₀ x) c₀) hx0 (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [Real.dist_eq]
    have h1 := hN m hm n hn x hxsrc le_rfl hxρ
    linarith only [h1, hε]
  /- ## The limit function. -/
  set ℓs : M → ℝ := fun x ↦ limUnder atTop (fun n ↦ Gs (φ n) x) with hℓs
  have hhalftgt1 : closedBall c₁ (r₁ / 2) ⊆ e₁.target :=
    (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1
  have hhalftgt2 : closedBall c₂ (r₂ / 2) ⊆ e₂.target :=
    (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2
  have hρslt : 1 / 4 * r₀ < ρs := by linarith only [hr₀, hρs]
  have hℓtend : ∀ x : M, x ≠ p₁ → x ≠ p₂ → x ≠ D₀.center →
      Tendsto (fun n ↦ Gs (φ n) x) atTop (𝓝 (ℓs x)) := by
    intro x hx1 hx2 hx0
    by_cases hΩ : x ∈ Ωqq
    · have h2 := (hGoutunif {x} isCompact_singleton
        (Set.singleton_subset_iff.2 hΩ)).tendsto_at rfl
      have h3 : ℓs x = Gout x := h2.limUnder_eq
      rw [h3]
      exact h2
    · have hx3 : x ∈ Dq.closedCarrier ∪ half1.closedCarrier ∪ half2.closedCarrier := by
        by_contra hcon
        exact hΩ hcon
      rcases hx3 with (hmem | hmem) | hmem
      · rw [hDqcar] at hmem
        obtain ⟨hsrc, hd⟩ := (hmemCB e₀ c₀ (1 / 4 * r₀) hQtgt x).1 hmem
        have hd0 : 0 < dist (e₀ x) c₀ := by
          rw [dist_pos]
          intro hcon
          apply hx0
          have h4 : e₀.symm (e₀ x) = e₀.symm c₀ := by rw [hcon]
          rw [e₀.left_inv hsrc, hc₀, e₀.left_inv hcen₀src] at h4
          exact h4
        obtain ⟨l, hl⟩ := hcen x hsrc hd0 (lt_of_le_of_lt hd hρslt)
        have h3 : ℓs x = l := hl.limUnder_eq
        rw [h3]
        exact hl
      · have hxB : x ∈ B₁ := by
          rw [hhalf1car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₁ c₁ (r₁ / 2) hhalftgt1 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₁]⟩
        have hw : e₁ x ∈ ball c₁ (3 * r₁ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₁]
        have h4 : Tendsto (fun n ↦ h1s (φ n) (e₁ x) - Real.log ‖e₁ x - c₁‖) atTop
            (𝓝 (H1 (e₁ x) - Real.log ‖e₁ x - c₁‖)) :=
          (hH1tend (e₁ x) hw).sub tendsto_const_nhds
        have h5 : Tendsto (fun n ↦ Gs (φ n) x) atTop
            (𝓝 (H1 (e₁ x) - Real.log ‖e₁ x - c₁‖)) :=
          h4.congr fun n ↦ (hGsB₁ (φ n) x hxB hx1).symm
        have h6 : ℓs x = H1 (e₁ x) - Real.log ‖e₁ x - c₁‖ := h5.limUnder_eq
        rw [h6]
        exact h5
      · have hxB : x ∈ B₂ := by
          rw [hhalf2car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₂ c₂ (r₂ / 2) hhalftgt2 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₂]⟩
        have hw : e₂ x ∈ ball c₂ (3 * r₂ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₂]
        have h4 : Tendsto (fun n ↦ Real.log ‖e₂ x - c₂‖ - h2s (φ n) (e₂ x)) atTop
            (𝓝 (Real.log ‖e₂ x - c₂‖ - H2 (e₂ x))) :=
          tendsto_const_nhds.sub (hH2tend (e₂ x) hw)
        have h5 : Tendsto (fun n ↦ Gs (φ n) x) atTop
            (𝓝 (Real.log ‖e₂ x - c₂‖ - H2 (e₂ x))) := by
          refine h4.congr fun n ↦ ?_
          have h7 := hh2val (φ n) (e₂ x) ?_
          · have h8 := hGsB₂ (φ n) x hxB hx2
            linarith only [h8]
          · have h1 := hxB.2
            rw [Set.mem_preimage, mem_ball] at h1
            refine ⟨by rw [mem_ball]; linarith only [h1, hr₂], ?_⟩
            intro hcon
            rw [Set.mem_singleton_iff] at hcon
            apply hx2
            have h9 : e₂.symm (e₂ x) = e₂.symm c₂ := by rw [hcon]
            rw [e₂.left_inv hxB.1, hc₂, e₂.left_inv hp₂src] at h9
            exact h9
        have h6 : ℓs x = Real.log ‖e₂ x - c₂‖ - H2 (e₂ x) := h5.limUnder_eq
        rw [h6]
        exact h5
  /- ## The plane limit near the center: harmonicity and boundedness. -/
  have hcenharm : ∀ w₀ ∈ ball c₀ ρs \ {c₀}, HarmonicAt (fun w ↦ ℓs (e₀.symm w)) w₀
      := by
    intro w₀ hw₀
    obtain ⟨hw₀b, hw₀ne⟩ := hw₀
    have hw₀ne' : w₀ ≠ c₀ := by simpa using hw₀ne
    have hd0 : 0 < dist w₀ c₀ := dist_pos.2 hw₀ne'
    have hdρ : dist w₀ c₀ < ρs := mem_ball.1 hw₀b
    set ρw : ℝ := min (dist w₀ c₀ / 2) ((ρs - dist w₀ c₀) / 2) with hρw
    have hρw0 : 0 < ρw :=
      lt_min (by linarith only [hd0]) (by linarith only [hdρ])
    have hball : ∀ ζ ∈ closedBall w₀ ρw, ζ ∈ e₀.target ∧
        dist w₀ c₀ / 2 ≤ dist ζ c₀ ∧ dist ζ c₀ < ρs := by
      intro ζ hζ
      have h1 : dist ζ w₀ ≤ ρw := mem_closedBall.1 hζ
      have h2 : ρw ≤ dist w₀ c₀ / 2 := min_le_left _ _
      have h3 : ρw ≤ (ρs - dist w₀ c₀) / 2 := min_le_right _ _
      have h4 : dist ζ c₀ ≤ dist ζ w₀ + dist w₀ c₀ := dist_triangle _ _ _
      have h5 : dist w₀ c₀ ≤ dist w₀ ζ + dist ζ c₀ := dist_triangle _ _ _
      rw [dist_comm w₀ ζ] at h5
      have h6 : dist ζ c₀ < ρs := by linarith only [h1, h3, h4, hdρ]
      have h7 : dist w₀ c₀ / 2 ≤ dist ζ c₀ := by linarith only [h1, h2, h5]
      exact ⟨hcb₀tgt (mem_closedBall.2 (by linarith only [h6, hρsr₀])), h7, h6⟩
    have hsymm : ∀ ζ ∈ closedBall w₀ ρw, e₀.symm ζ ∈ e₀.source ∧
        dist (e₀ (e₀.symm ζ)) c₀ = dist ζ c₀ := by
      intro ζ hζ
      have h1 := (hball ζ hζ).1
      exact ⟨e₀.map_target h1, by rw [e₀.right_inv h1]⟩
    have hcarζ : ∀ ζ ∈ closedBall w₀ ρw, e₀.symm ζ ∈ D₀.closedCarrier := by
      intro ζ hζ
      rw [hcar₀]
      exact ⟨ζ, mem_closedBall.2 (by linarith only [(hball ζ hζ).2.2, hρsr₀]), rfl⟩
    have hunifC : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ closedBall
        w₀ ρw,
        |Gs (φ m) (e₀.symm ζ) - Gs (φ n) (e₀.symm ζ)| ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hcauAt (dist w₀ c₀ / 2) (by linarith only [hd0]) ε hε
      refine ⟨N, fun m hm n hn ζ hζ ↦ ?_⟩
      obtain ⟨hs1, hs2⟩ := hsymm ζ hζ
      obtain ⟨hb1, hb2, hb3⟩ := hball ζ hζ
      exact hN m hm n hn (e₀.symm ζ) hs1 (by rw [hs2]; exact hb2)
        (by rw [hs2]; exact hb3)
    have hptw : ∀ ζ ∈ closedBall w₀ ρw,
        Tendsto (fun n ↦ Gs (φ n) (e₀.symm ζ)) atTop (𝓝 (ℓs (e₀.symm ζ))) := by
      intro ζ hζ
      obtain ⟨hs1, hs2⟩ := hsymm ζ hζ
      obtain ⟨hb1, hb2, hb3⟩ := hball ζ hζ
      have h1 : 0 < dist (e₀ (e₀.symm ζ)) c₀ := by
        rw [hs2]
        linarith only [hb2, hd0]
      have h2 : dist (e₀ (e₀.symm ζ)) c₀ < ρs := by
        rw [hs2]
        exact hb3
      obtain ⟨l, hl⟩ := hcen (e₀.symm ζ) hs1 h1 h2
      have h3 : ℓs (e₀.symm ζ) = l := hl.limUnder_eq
      rw [h3]
      exact hl
    obtain ⟨n₀, hn₀t⟩ := htlim (dist w₀ c₀ / 2 / r₀)
      (div_pos (by linarith only [hd0]) hr₀)
    have hshift_harm : ∀ j : ℕ,
        HarmonicOnNhd (fun w ↦ Gs (φ (j + n₀)) (e₀.symm w))
          (ball w₀ (2 * (ρw / 2))) := by
      intro j ζ hζ
      have hζcb : ζ ∈ closedBall w₀ ρw := by
        have h1 : (2 : ℝ) * (ρw / 2) = ρw := by ring
        rw [h1] at hζ
        exact ball_subset_closedBall hζ
      obtain ⟨hs1, hs2⟩ := hsymm ζ hζcb
      obtain ⟨hb1, hb2, hb3⟩ := hball ζ hζcb
      have h1 : t (φ (j + n₀)) ≤ t n₀ :=
        htanti n₀ _ (le_trans (Nat.le_add_left n₀ j) hφmono.le_apply)
      have h3 : t n₀ * r₀ < dist w₀ c₀ / 2 := by
        have h4 : t n₀ * r₀ < dist w₀ c₀ / 2 / r₀ * r₀ :=
          mul_lt_mul_of_pos_right hn₀t hr₀
        have h5 : dist w₀ c₀ / 2 / r₀ * r₀ = dist w₀ c₀ / 2 := div_mul_cancel₀ _
            hr₀.ne'
        linarith only [h4, h5]
      have h6 : t (φ (j + n₀)) * r₀ ≤ t n₀ * r₀ :=
        mul_le_mul_of_nonneg_right h1 hr₀.le
      have hmemW : e₀.symm ζ ∈ Wp (φ (j + n₀)) := by
        intro hmem
        have h7 := ((hcarmem (φ (j + n₀)) (e₀.symm ζ)).1 hmem).2
        rw [hs2] at h7
        linarith only [h3, h6, h7, hb2]
      have hcar := hcarζ ζ hζcb
      have hnp1 : e₀.symm ζ ≠ p₁ := fun hcon ↦
        (hCar1av p₁ hp₁Car1).1 (hcon ▸ hcar)
      have hnp2 : e₀.symm ζ ≠ p₂ := fun hcon ↦
        (hCar2av p₂ hp₂Car2).1 (hcon ▸ hcar)
      refine htransfer D₀.center ((Wp (φ (j + n₀)) : Set M) ∩ ({p₁}ᶜ ∩ {p₂}ᶜ))
        (Gs (φ (j + n₀))) ?_ ζ ⟨hb1, ?_⟩
      · intro z hz
        exact hGsharmAt _ z hz.1 (Set.mem_compl_singleton_iff.1 hz.2.1)
          (Set.mem_compl_singleton_iff.1 hz.2.2)
      · rw [Set.mem_preimage]
        exact ⟨hmemW, Set.mem_compl_singleton_iff.2 hnp1,
          Set.mem_compl_singleton_iff.2 hnp2⟩
    have hcauw : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ∀ ζ ∈ sphere w₀ (3 * (ρw / 2) / 2),
        |Gs (φ (m + n₀)) (e₀.symm ζ) - Gs (φ (n + n₀)) (e₀.symm ζ)| ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hunifC ε hε
      refine ⟨N, fun m hm n hn ζ hζ ↦ ?_⟩
      have hζcb : ζ ∈ closedBall w₀ ρw := by
        have h1 : dist ζ w₀ = 3 * (ρw / 2) / 2 := mem_sphere.1 hζ
        rw [mem_closedBall, h1]
        linarith only [hρw0]
      exact hN (m + n₀) (le_trans hm (Nat.le_add_right m n₀)) (n + n₀)
        (le_trans hn (Nat.le_add_right n n₀)) ζ hζcb
    obtain ⟨Hw, hHwharm, hHwtend⟩ := exists_harmonicOnNhd_tendsto_of_cauchy_sphere
      (fun j w ↦ Gs (φ (j + n₀)) (e₀.symm w)) (half_pos hρw0) hshift_harm hcauw
    have hq0 : (0 : ℝ) < 3 * (ρw / 2) / 2 := by linarith only [hρw0]
    have hev : (fun w ↦ ℓs (e₀.symm w)) =ᶠ[𝓝 w₀] Hw := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hq0)] with v hv
      have hvcb : v ∈ closedBall w₀ ρw := by
        have h1 : dist v w₀ < 3 * (ρw / 2) / 2 := mem_ball.1 hv
        rw [mem_closedBall]
        linarith only [h1, hρw0]
      have h1 := hptw v hvcb
      have h2 : Tendsto (fun j ↦ Gs (φ (j + n₀)) (e₀.symm v)) atTop
          (𝓝 (ℓs (e₀.symm v))) := h1.comp (tendsto_add_atTop_nat n₀)
      exact tendsto_nhds_unique h2 (hHwtend v hv)
    exact (harmonicAt_congr_nhds hev).mpr (hHwharm w₀ (mem_ball_self hq0))
  have hcenbd : ∀ ζ ∈ ball c₀ ρs \ {c₀}, |ℓs (e₀.symm ζ)| ≤ C₀ := by
    intro ζ hζ
    obtain ⟨hζb, hζne⟩ := hζ
    have hζne' : ζ ≠ c₀ := by simpa using hζne
    have hζρ : dist ζ c₀ < ρs := mem_ball.1 hζb
    have hζt : ζ ∈ e₀.target :=
      hcb₀tgt (mem_closedBall.2 (by linarith only [hζρ, hρsr₀]))
    have hd1 : 0 < dist ζ c₀ := dist_pos.2 hζne'
    have hsrc := e₀.map_target hζt
    have hs2 : dist (e₀ (e₀.symm ζ)) c₀ = dist ζ c₀ := by rw [e₀.right_inv hζt]
    obtain ⟨l, hl⟩ := hcen (e₀.symm ζ) hsrc (by rw [hs2]; exact hd1)
      (by rw [hs2]; exact hζρ)
    have heq : ℓs (e₀.symm ζ) = l := hl.limUnder_eq
    have hcar : e₀.symm ζ ∈ D₀.closedCarrier := by
      rw [hcar₀]
      exact ⟨ζ, mem_closedBall.2 (by linarith only [hζρ, hρsr₀]), rfl⟩
    have hB1 : e₀.symm ζ ∉ B₁ := fun hmem ↦ (hCar1av _ (hB₁Car hmem)).1 hcar
    have hB2 : e₀.symm ζ ∉ B₂ := fun hmem ↦ (hCar2av _ (hB₂Car hmem)).1 hcar
    rw [heq]
    apply le_of_tendsto hl.abs
    exact Filter.Eventually.of_forall fun n ↦ hGB (φ n) _ hB1 hB2
  obtain ⟨Hc, hHcharm, hHceq⟩ := exists_harmonicOnNhd_of_bounded_punctured hρs0
    (fun w hw ↦ hcenharm w hw) ⟨C₀, hcenbd⟩
  /- ## Assembly of the bipolar Green's function. -/
  set Gfin : M → ℝ := fun x ↦ if x = D₀.center then Hc c₀ else ℓs x with hGfin
  have hballtgt1 : ball c₁ (3 * r₁ / 2) ⊆ e₁.target :=
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1
  have hballtgt2 : ball c₂ (3 * r₂ / 2) ⊆ e₂.target :=
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2
  -- the limit is the pole companion inside the enlarged pole balls
  have hval1 : ∀ w ∈ ball c₁ (3 * r₁ / 2) \ {c₁},
      e₁.symm w ≠ D₀.center ∧ ℓs (e₁.symm w) = H1 w - Real.log ‖w - c₁‖ := by
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwne' : w ≠ c₁ := by simpa using hwne
    have hwt : w ∈ e₁.target := hballtgt1 hwb
    have hcarw : e₁.symm w ∈ Car1 :=
      ⟨w, mem_closedBall.2 (by linarith only [mem_ball.1 hwb, hr₁]), rfl⟩
    have hnp1 : e₁.symm w ≠ p₁ := by
      intro hcon
      have h1 : e₁ (e₁.symm w) = w := e₁.right_inv hwt
      rw [hcon] at h1
      have h2 : c₁ = w := by rw [hc₁, h1]
      exact hwne' h2.symm
    have hnp2 : e₁.symm w ≠ p₂ := (hCar1av _ hcarw).2
    have hnc : e₁.symm w ≠ D₀.center := by
      intro hcon
      exact (hCar1av _ hcarw).1 (hcon ▸ hcen₀car)
    have h3 := hℓtend (e₁.symm w) hnp1 hnp2 hnc
    have hwball2 : w ∈ ball c₁ (2 * r₁) :=
      ball_subset_ball (by linarith only [hr₁]) hwb
    have h4 : ∀ n, Gs (φ n) (e₁.symm w) = h1s (φ n) w - Real.log ‖w - c₁‖ := by
      intro n
      have h5 := hh1val (φ n) w ⟨hwball2, by simpa using hwne'⟩
      linarith only [h5]
    have h6 : Tendsto (fun n ↦ h1s (φ n) w - Real.log ‖w - c₁‖) atTop
        (𝓝 (H1 w - Real.log ‖w - c₁‖)) := (hH1tend w hwb).sub tendsto_const_nhds
    have h7 : Tendsto (fun n ↦ Gs (φ n) (e₁.symm w)) atTop
        (𝓝 (H1 w - Real.log ‖w - c₁‖)) := h6.congr fun n ↦ (h4 n).symm
    exact ⟨hnc, tendsto_nhds_unique h3 h7⟩
  have hval2 : ∀ w ∈ ball c₂ (3 * r₂ / 2) \ {c₂},
      e₂.symm w ≠ D₀.center ∧ ℓs (e₂.symm w) = Real.log ‖w - c₂‖ - H2 w := by
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwne' : w ≠ c₂ := by simpa using hwne
    have hwt : w ∈ e₂.target := hballtgt2 hwb
    have hcarw : e₂.symm w ∈ Car2 :=
      ⟨w, mem_closedBall.2 (by linarith only [mem_ball.1 hwb, hr₂]), rfl⟩
    have hnp2 : e₂.symm w ≠ p₂ := by
      intro hcon
      have h1 : e₂ (e₂.symm w) = w := e₂.right_inv hwt
      rw [hcon] at h1
      have h2 : c₂ = w := by rw [hc₂, h1]
      exact hwne' h2.symm
    have hnp1 : e₂.symm w ≠ p₁ := fun hcon ↦ (hCar2av _ hcarw).2 (hcon ▸ hp₁Car1)
    have hnc : e₂.symm w ≠ D₀.center := by
      intro hcon
      exact (hCar2av _ hcarw).1 (hcon ▸ hcen₀car)
    have h3 := hℓtend (e₂.symm w) hnp1 hnp2 hnc
    have hwball2 : w ∈ ball c₂ (2 * r₂) :=
      ball_subset_ball (by linarith only [hr₂]) hwb
    have h4 : ∀ n, Gs (φ n) (e₂.symm w) = Real.log ‖w - c₂‖ - h2s (φ n) w := by
      intro n
      have h5 := hh2val (φ n) w ⟨hwball2, by simpa using hwne'⟩
      linarith only [h5]
    have h6 : Tendsto (fun n ↦ Real.log ‖w - c₂‖ - h2s (φ n) w) atTop
        (𝓝 (Real.log ‖w - c₂‖ - H2 w)) := tendsto_const_nhds.sub (hH2tend w hwb)
    have h7 : Tendsto (fun n ↦ Gs (φ n) (e₂.symm w)) atTop
        (𝓝 (Real.log ‖w - c₂‖ - H2 w)) := h6.congr fun n ↦ (h4 n).symm
    exact ⟨hnc, tendsto_nhds_unique h3 h7⟩
  refine ⟨Gfin, ?_, ⟨3 * r₁ / 2, by linarith only [hr₁], hballtgt1, H1, hH1harm, ?_⟩,
    ⟨3 * r₂ / 2, by linarith only [hr₂], hballtgt2, fun w ↦ -H2 w,
      harmNeg H2 _ hH2harm, ?_⟩, ⟨C₀, B₁, hB₁open.mem_nhds hp₁B₁, B₂,
      hB₂open.mem_nhds hp₂B₂, ?_, ?_, ?_⟩⟩
  · -- harmonicity on the doubly punctured surface
    intro x hx
    have hx1 : x ≠ p₁ := fun hcon ↦ hx (by rw [hcon]; exact Set.mem_insert _ _)
    have hx2 : x ≠ p₂ := fun hcon ↦ hx (by rw [hcon]; exact Set.mem_insert_of_mem _ rfl)
    by_cases hΩ : x ∈ Ωqq
    · have hev : ∀ᶠ z in 𝓝 x, Gout z = Gfin z := by
        filter_upwards [hΩqqopen.mem_nhds hΩ] with z hz
        have hz0 : z ≠ D₀.center := by
          intro hcon
          apply hz
          left; left
          rw [hcon, hDqcar]
          exact ⟨c₀, mem_closedBall_self (by linarith only [hr₀]),
            e₀.left_inv hcen₀src⟩
        have h3 := hℓtend z (hΩqqp₁ z hz) (hΩqqp₂ z hz) hz0
        have h4 := (hGoutunif {z} isCompact_singleton
          (Set.singleton_subset_iff.2 hz)).tendsto_at rfl
        have h5 : ℓs z = Gout z := tendsto_nhds_unique h3 h4
        simp only [hGfin]
        rw [ite_eq_right hz0, h5]
      exact mharm_congr Gout Gfin x hev (hGoutharm x hΩ)
    · have hx3 : x ∈ Dq.closedCarrier ∪ half1.closedCarrier ∪ half2.closedCarrier := by
        by_contra hcon
        exact hΩ hcon
      rcases hx3 with (hmem | hmem) | hmem
      · -- across the center
        rw [hDqcar] at hmem
        obtain ⟨hxsrc, hxd⟩ := (hmemCB e₀ c₀ (1 / 4 * r₀) hQtgt x).1 hmem
        have hxball : e₀ x ∈ ball c₀ ρs := by
          rw [mem_ball]
          exact lt_of_le_of_lt hxd hρslt
        have hev : ∀ᶠ z in 𝓝 x, Hc (e₀ z) = Gfin z := by
          have hN₀open : IsOpen (e₀.source ∩ e₀ ⁻¹' ball c₀ ρs) :=
            e₀.isOpen_inter_preimage isOpen_ball
          have hxN₀ : x ∈ e₀.source ∩ e₀ ⁻¹' ball c₀ ρs :=
            ⟨hxsrc, by rw [Set.mem_preimage]; exact hxball⟩
          filter_upwards [hN₀open.mem_nhds hxN₀] with z hz
          obtain ⟨hzsrc, hzb⟩ := hz
          rw [Set.mem_preimage] at hzb
          by_cases hzc : z = D₀.center
          · simp only [hGfin]
            rw [ite_eq_left hzc, hzc, ← hc₀]
          · have hzezc : e₀ z ≠ c₀ := by
              intro hcon
              apply hzc
              have h4 : e₀.symm (e₀ z) = e₀.symm c₀ := by rw [hcon]
              rw [e₀.left_inv hzsrc, hc₀, e₀.left_inv hcen₀src] at h4
              exact h4
            have h5 : e₀ z ∈ ball c₀ ρs \ {c₀} := ⟨hzb, by simpa using hzezc⟩
            have h6 : Hc (e₀ z) = ℓs (e₀.symm (e₀ z)) := hHceq h5
            rw [e₀.left_inv hzsrc] at h6
            simp only [hGfin]
            rw [ite_eq_right hzc]
            exact h6
        have h7 : HarmonicAt Hc (e₀ x) := hHcharm (e₀ x) hxball
        exact mharm_congr _ _ x hev (pullback D₀.center Hc x hxsrc h7)
      · -- across the first half disk
        have hxB : x ∈ B₁ := by
          rw [hhalf1car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₁ c₁ (r₁ / 2) hhalftgt1 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₁]⟩
        have hw : e₁ x ∈ ball c₁ (3 * r₁ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₁]
        have hxcne : e₁ x ≠ c₁ := by
          intro hcon
          apply hx1
          have h4 : e₁.symm (e₁ x) = e₁.symm c₁ := by rw [hcon]
          rw [e₁.left_inv hxB.1, hc₁, e₁.left_inv hp₁src] at h4
          exact h4
        have hev : ∀ᶠ z in 𝓝 x, H1 (e₁ z) - Real.log ‖e₁ z - c₁‖ = Gfin z := by
          have hNopen : IsOpen ((e₁.source ∩ e₁ ⁻¹' ball c₁ (3 * r₁ / 2)) ∩
              {p₁}ᶜ) :=
            (e₁.isOpen_inter_preimage isOpen_ball).inter isOpen_compl_singleton
          have hxN : x ∈ (e₁.source ∩ e₁ ⁻¹' ball c₁ (3 * r₁ / 2)) ∩ {p₁}ᶜ :=
            ⟨⟨hxB.1, by rw [Set.mem_preimage]; exact hw⟩,
              Set.mem_compl_singleton_iff.2 hx1⟩
          filter_upwards [hNopen.mem_nhds hxN] with z hz
          obtain ⟨⟨hzsrc, hzb⟩, hznp⟩ := hz
          rw [Set.mem_preimage] at hzb
          have hzcne : e₁ z ≠ c₁ := by
            intro hcon
            apply Set.mem_compl_singleton_iff.1 hznp
            have h4 : e₁.symm (e₁ z) = e₁.symm c₁ := by rw [hcon]
            rw [e₁.left_inv hzsrc, hc₁, e₁.left_inv hp₁src] at h4
            exact h4
          have h5 := hval1 (e₁ z) ⟨hzb, by simpa using hzcne⟩
          rw [e₁.left_inv hzsrc] at h5
          simp only [hGfin]
          rw [ite_eq_right h5.1]
          exact h5.2.symm
        have hharm1 : MHarmonicAt (fun z ↦ H1 (e₁ z) -
            Real.log (dist (e₁ z) c₁)) x :=
          mharmSub _ _ x (pullback p₁ H1 x hxB.1 (hH1harm (e₁ x) hw))
            (logHarm p₁ c₁ x hxB.1 hxcne)
        have hharm2 : MHarmonicAt (fun z ↦ H1 (e₁ z) - Real.log ‖e₁ z - c₁‖) x :=
          mharm_congr _ _ x
            (Filter.Eventually.of_forall fun z ↦ by rw [dist_eq_norm]) hharm1
        exact mharm_congr _ _ x hev hharm2
      · -- across the second half disk
        have hxB : x ∈ B₂ := by
          rw [hhalf2car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₂ c₂ (r₂ / 2) hhalftgt2 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₂]⟩
        have hw : e₂ x ∈ ball c₂ (3 * r₂ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₂]
        have hxcne : e₂ x ≠ c₂ := by
          intro hcon
          apply hx2
          have h4 : e₂.symm (e₂ x) = e₂.symm c₂ := by rw [hcon]
          rw [e₂.left_inv hxB.1, hc₂, e₂.left_inv hp₂src] at h4
          exact h4
        have hev : ∀ᶠ z in 𝓝 x, Real.log ‖e₂ z - c₂‖ - H2 (e₂ z) = Gfin z := by
          have hNopen : IsOpen ((e₂.source ∩ e₂ ⁻¹' ball c₂ (3 * r₂ / 2)) ∩
              {p₂}ᶜ) :=
            (e₂.isOpen_inter_preimage isOpen_ball).inter isOpen_compl_singleton
          have hxN : x ∈ (e₂.source ∩ e₂ ⁻¹' ball c₂ (3 * r₂ / 2)) ∩ {p₂}ᶜ :=
            ⟨⟨hxB.1, by rw [Set.mem_preimage]; exact hw⟩,
              Set.mem_compl_singleton_iff.2 hx2⟩
          filter_upwards [hNopen.mem_nhds hxN] with z hz
          obtain ⟨⟨hzsrc, hzb⟩, hznp⟩ := hz
          rw [Set.mem_preimage] at hzb
          have hzcne : e₂ z ≠ c₂ := by
            intro hcon
            apply Set.mem_compl_singleton_iff.1 hznp
            have h4 : e₂.symm (e₂ z) = e₂.symm c₂ := by rw [hcon]
            rw [e₂.left_inv hzsrc, hc₂, e₂.left_inv hp₂src] at h4
            exact h4
          have h5 := hval2 (e₂ z) ⟨hzb, by simpa using hzcne⟩
          rw [e₂.left_inv hzsrc] at h5
          simp only [hGfin]
          rw [ite_eq_right h5.1]
          exact h5.2.symm
        have hharm1 : MHarmonicAt (fun z ↦ Real.log (dist (e₂ z) c₂) -
            H2 (e₂ z)) x :=
          mharmSub _ _ x (logHarm p₂ c₂ x hxB.1 hxcne)
            (pullback p₂ H2 x hxB.1 (hH2harm (e₂ x) hw))
        have hharm2 : MHarmonicAt (fun z ↦ Real.log ‖e₂ z - c₂‖ - H2 (e₂ z)) x :=
          mharm_congr _ _ x
            (Filter.Eventually.of_forall fun z ↦ by rw [dist_eq_norm]) hharm1
        exact mharm_congr _ _ x hev hharm2
  · -- the pole identity at `p₁`
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have h1 := hval1 w ⟨hwb, hwne⟩
    simp only [hGfin]
    rw [ite_eq_right h1.1, h1.2]
    ring
  · -- the pole identity at `p₂`
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have h1 := hval2 w ⟨hwb, hwne⟩
    simp only [hGfin]
    rw [ite_eq_right h1.1, h1.2]
    ring
  · -- compact closure of the first pole ball
    have htgtr₁ : closedBall c₁ r₁ ⊆ e₁.target :=
      (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1
    have hcp : IsCompact (e₁.symm '' closedBall c₁ r₁) :=
      (isCompact_closedBall c₁ r₁).image_of_continuousOn
        (e₁.continuousOn_symm.mono htgtr₁)
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rw [← hB₁img]
    exact Set.image_mono ball_subset_closedBall
  · -- compact closure of the second pole ball
    have htgtr₂ : closedBall c₂ r₂ ⊆ e₂.target :=
      (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2
    have hcp : IsCompact (e₂.symm '' closedBall c₂ r₂) :=
      (isCompact_closedBall c₂ r₂).image_of_continuousOn
        (e₂.continuousOn_symm.mono htgtr₂)
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rw [← hB₂img]
    exact Set.image_mono ball_subset_closedBall
  · -- the global bound off the pole balls
    intro x hx
    have hx1 : x ∉ B₁ := fun h ↦ hx (Or.inl h)
    have hx2 : x ∉ B₂ := fun h ↦ hx (Or.inr h)
    by_cases hxc : x = D₀.center
    · simp only [hGfin]
      rw [ite_eq_left hxc]
      have h4 : Tendsto Hc (𝓝[≠] c₀) (𝓝 (Hc c₀)) :=
        ((hHcharm c₀ (mem_ball_self hρs0)).1.continuousAt).continuousWithinAt
      apply le_of_tendsto h4.abs
      have h5 : ball c₀ ρs ∈ 𝓝 c₀ := isOpen_ball.mem_nhds (mem_ball_self hρs0)
      filter_upwards [nhdsWithin_le_nhds h5, self_mem_nhdsWithin] with w hw1 hw2
      have hw3 : w ∈ ball c₀ ρs \ {c₀} := ⟨hw1, hw2⟩
      have h6 : Hc w = ℓs (e₀.symm w) := hHceq hw3
      rw [h6]
      exact hcenbd w hw3
    · simp only [hGfin]
      rw [ite_eq_right hxc]
      have hxp1 : x ≠ p₁ := fun hcon ↦ hx1 (hcon ▸ hp₁B₁)
      have hxp2 : x ≠ p₂ := fun hcon ↦ hx2 (hcon ▸ hp₂B₂)
      apply le_of_tendsto (hℓtend x hxp1 hxp2 hxc).abs
      exact Filter.Eventually.of_forall fun n ↦ hGB (φ n) x hx1 hx2

end RiemannDynamics
