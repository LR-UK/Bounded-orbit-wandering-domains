/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.CuspAreaIntegrability
import BoundedWanderingDomains.Surfaces.SurfaceSchwarz
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

/-! # Cusp bounds in a surface chart -/

open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The exponential test disc proving the planar isolated-puncture bound
works verbatim in any surface chart. -/
theorem chartDensity_upper_cusp (p : DiscCover M)
    {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a z : ℂ} {R : ℝ}
    (hball : ball a R \ {a} ⊆ d.target)
    (hz : z ≠ a) (hzR : ‖z - a‖ < R) :
    p.chartDensity d z ≤
      2 / (‖z - a‖ * Real.log (R / ‖z - a‖)) := by
  have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hR : 0 < R := hr.trans hzR
  let L : ℝ := Real.log (R / ‖z - a‖)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).mpr hzR)
  let t : ℂ → ℂ := fun w => a + (z - a) * Complex.exp ((L : ℂ) * w)
  have htmem : ∀ w : unitDisc, t (w : ℂ) ∈ d.target := by
    intro w
    apply hball
    have he : t (w : ℂ) - a =
        (z - a) * Complex.exp ((L : ℂ) * (w : ℂ)) := by
      dsimp [t]
      ring
    have hn : ‖t (w : ℂ) - a‖ =
        ‖z - a‖ * Real.exp (L * (w : ℂ).re) := by
      rw [he, norm_mul, Complex.norm_exp]
      congr 2
      simp
    have hwre : (w : ℂ).re < 1 :=
      (Complex.re_le_norm (w : ℂ)).trans_lt
        (mem_ball_zero_iff.mp w.property)
    have hnorm : ‖t (w : ℂ) - a‖ < R := by
      rw [hn]
      calc
        ‖z - a‖ * Real.exp (L * (w : ℂ).re) <
            ‖z - a‖ * Real.exp L := by gcongr; nlinarith
        _ = R := by
          dsimp [L]
          rw [Real.exp_log (div_pos hR hr)]
          field_simp
    refine ⟨by simpa only [mem_ball, dist_eq_norm] using hnorm, ?_⟩
    simp only [mem_singleton_iff]
    intro heq
    have hzero : t (w : ℂ) - a = 0 := sub_eq_zero.mpr heq
    rw [he] at hzero
    exact (mul_ne_zero (sub_ne_zero.mpr hz) (Complex.exp_ne_zero _)) hzero
  let g : unitDisc → M := fun w => d.symm (t (w : ℂ))
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    intro w
    have ht : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (fun v : unitDisc => t (v : ℂ)) w := by
      apply (mdifferentiableAt_subtype_iff
        (U := unitDisc) (f := t) (x := w)).mpr
      exact (show DifferentiableAt ℂ t (w : ℂ) by
        dsimp [t]
        fun_prop).mdifferentiableAt
    exact ((mdifferentiableOn_symm hd _ (htmem w)).mdifferentiableAt
      (d.open_target.mem_nhds (htmem w))).comp w ht
  let v0 : unitDisc := ⟨0, by simp [unitDisc]⟩
  have hg0 : g v0 = d.symm z := by
    change d.symm (a + (z - a) * Complex.exp ((L : ℂ) * 0)) = d.symm z
    simp
  have hgd : g v0 ∈ d.source := by
    rw [hg0]
    exact d.map_target (hball ⟨by
      simpa only [mem_ball, dist_eq_norm] using hzR, by
      simpa only [mem_singleton_iff] using hz⟩)
  have hevent : planeExtension (d ∘ g) =ᶠ[𝓝 (0 : ℂ)] t := by
    filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball 0 1 by simp)] with w hw
    rw [show w = ((⟨w, hw⟩ : unitDisc) : ℂ) from rfl, planeExtension_coe]
    exact d.right_inv (htmem ⟨w, hw⟩)
  have hder : deriv (planeExtension (d ∘ g)) 0 = (z - a) * (L : ℂ) := by
    rw [hevent.deriv_eq]
    have h := ((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).cexp.const_mul (z - a)
    have h' := h.const_add a
    simpa [t] using h'.deriv
  have hs := p.density_schwarz_disc hg hd v0 hgd
  rw [hg0, hder, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hL] at hs
  have hzt : z ∈ d.target := hball ⟨by
    simpa only [mem_ball, dist_eq_norm] using hzR, by
    simpa only [mem_singleton_iff] using hz⟩
  change p.density d (d.symm z) ≤ _
  have hs' : p.density d (d.symm z) * (‖z - a‖ * L) ≤ 2 := by
    simpa [v0, discDensity, discDenom] using hs
  exact (le_div_iff₀ (mul_pos hr hL)).mpr hs'

/-- Hence the intrinsic density of a disc-covered surface has finite area
in a smaller coordinate neighbourhood of an isolated puncture. -/
theorem integrableOn_chartDensity_sq_cusp (p : DiscCover M)
    {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ d.target) :
    IntegrableOn (fun z => (p.chartDensity d z) ^ 2)
      (ball a (R / 2) \ {a}) := by
  let B : Set ℂ := ball a (R / 2) \ {a}
  let g : ℂ → ℝ := fun z =>
    4 * if z ≠ a ∧ ‖z - a‖ < R / 2 then
      1 / (‖z - a‖ * Real.log (R / ‖z - a‖)) ^ 2
    else 0
  have hg : Integrable g :=
    (AreaDeficit.integrable_cusp_density_sq_majorant_at a hR).const_mul 4
  have hBmeas : MeasurableSet B :=
    measurableSet_ball.diff (measurableSet_singleton a)
  have hcont : ContinuousOn (fun z => (p.chartDensity d z) ^ 2) B := by
    intro z hz
    have hzR2 : ‖z - a‖ < R / 2 := by
      simpa only [mem_ball, dist_eq_norm] using hz.1
    have hzR : ‖z - a‖ < R := hzR2.trans (by linarith)
    have hza : z ≠ a := by simpa only [mem_singleton_iff] using hz.2
    exact ((p.chartDensity_contDiffAt hd (hball ⟨by
      simpa only [mem_ball, dist_eq_norm] using hzR, by
      simpa only [mem_singleton_iff] using hza⟩)).continuousAt.pow 2).continuousWithinAt
  apply Integrable.mono' hg.integrableOn
    (hcont.aestronglyMeasurable hBmeas)
  filter_upwards [ae_restrict_mem hBmeas] with z hz
  have hzR2 : ‖z - a‖ < R / 2 := by
    simpa only [B, mem_diff, mem_ball, dist_eq_norm, mem_singleton_iff] using hz.1
  have hzR : ‖z - a‖ < R := hzR2.trans (by linarith)
  have hza : z ≠ a := by
    simpa only [B, mem_diff, mem_ball, dist_eq_norm, mem_singleton_iff] using hz.2
  have hr : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hl : 0 < Real.log (R / ‖z - a‖) :=
    Real.log_pos ((one_lt_div hr).mpr hzR)
  have hdpos : 0 < ‖z - a‖ * Real.log (R / ‖z - a‖) := mul_pos hr hl
  have hu := p.chartDensity_upper_cusp hd hball hza hzR
  have hpos := p.chartDensity_pos hd (hball ⟨by
    simpa only [mem_ball, dist_eq_norm] using hzR, by
    simpa only [mem_singleton_iff] using hza⟩)
  change ‖(p.chartDensity d z) ^ 2‖ ≤ g z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hcond : z ≠ a ∧ ‖z - a‖ < R / 2 := ⟨hza, hzR2⟩
  dsimp only [g]
  rw [if_pos hcond]
  have hupper_nonneg : 0 ≤ 2 / (‖z - a‖ * Real.log (R / ‖z - a‖)) :=
    div_nonneg (by norm_num) hdpos.le
  have hsquare : (p.chartDensity d z) ^ 2 ≤
      (2 / (‖z - a‖ * Real.log (R / ‖z - a‖))) ^ 2 := by
    nlinarith
  calc
    (p.chartDensity d z) ^ 2 ≤
        (2 / (‖z - a‖ * Real.log (R / ‖z - a‖))) ^ 2 := hsquare
    _ = 4 * (1 / (‖z - a‖ * Real.log (R / ‖z - a‖)) ^ 2) := by ring

/-- Coordinate form of finite cusp area. -/
theorem lintegral_chartDensity_sq_cusp_lt_top (p : DiscCover M)
    {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ d.target) :
    (∫⁻ z in ball a (R / 2) \ {a},
      ENNReal.ofReal ((p.chartDensity d z) ^ 2)) < ⊤ := by
  have hi := p.integrableOn_chartDensity_sq_cusp hd hR hball
  exact lt_top_iff_ne_top.mpr
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (ae_of_all _ (fun _ => sq_nonneg _))).mpr hi)

end AreaDeficit.Surfaces.DiscCover
