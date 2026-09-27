/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AreaGainIntegration
import BoundedWanderingDomains.Surfaces.ChartZeroExtension
import BoundedWanderingDomains.GreenIdentity

/-! # Green's identity for a chart-supported surface cutoff -/

open Set Function Filter MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- A nonnegative compactly supported cutoff in one restricted ambient chart
converts intrinsic area gain into its planar Green boundary pairing. -/
theorem areaGain_lintegral_eq_chart_green
    (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {v : U → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v) (hvnonneg : ∀ x, 0 ≤ v x)
    (hvsource : tsupport v ⊆ (c.subtypeRestr hU).source)
    (hd : c.subtypeRestr hU ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 U) :
    (∫⁻ x, ENNReal.ofReal (v x) ∂p.areaGain q) =
      ENNReal.ofReal (∫ z, p.chartLogRatio q hU c z *
        Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
          (c.subtypeRestr hU) v) z) := by
  let d := c.subtypeRestr hU
  let test := AreaDeficit.Surfaces.chartZeroExtensionIn d v
  let f := p.chartLogRatio q hU c
  have htest : ContDiff ℝ 2 test :=
    AreaDeficit.Surfaces.contDiff_chartZeroExtensionIn
      hv hvcompact hvsource hd
  have htestCompact : HasCompactSupport test :=
    AreaDeficit.Surfaces.hasCompactSupport_chartZeroExtensionIn
      hvcompact hvsource
  have htestSupport : tsupport test ⊆ d '' tsupport v := by
    have hK : IsCompact (d '' tsupport v) :=
      hvcompact.image_of_continuousOn (d.continuousOn.mono hvsource)
    exact closure_minimal
      (AreaDeficit.Surfaces.support_chartZeroExtensionIn_subset.trans
        (image_mono subset_closure)) hK.isClosed
  have htestTarget : tsupport test ⊆ d.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := htestSupport hz
    exact d.map_source (hvsource hx)
  have hf : ∀ z ∈ tsupport test, ContDiffAt ℝ 2 f z := by
    intro z hz
    exact p.chartLogRatio_contDiffAt q hU hc (htestTarget hz)
  have hlap : ∀ z ∈ tsupport test,
      Δ f z = (q.chartDensity d z)^2 - (p.chartDensity c z)^2 := by
    intro z hz
    exact p.chartLogRatio_laplacian q hU hc (htestTarget hz)
  have hpos : ∀ z, 0 ≤ test z * Δ f z := by
    intro z
    by_cases hz : z ∈ tsupport test
    · have htv : test z = v (d.symm z) := by
        exact AreaDeficit.Surfaces.chartZeroExtensionIn_eq (htestTarget hz)
      rw [htv]
      exact mul_nonneg (hvnonneg _) (p.chartLogRatio_laplacian_nonneg
        q hU hc (htestTarget hz))
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hint : Integrable (fun z => test z * Δ f z) :=
    AreaDeficit.integrable_mul_of_local htest.continuous htestCompact
      (fun z hz => AreaDeficit.laplacian_continuousAt (hf z hz))
  have hfull : (∫⁻ x, ENNReal.ofReal (v x) ∂p.areaGain q) =
      ∫⁻ x in d.source, ENNReal.ofReal (v x) ∂p.areaGain q := by
    rw [← lintegral_add_compl (fun x => ENNReal.ofReal (v x))
      d.open_source.measurableSet]
    have hz : (∫⁻ x in d.sourceᶜ, ENNReal.ofReal (v x) ∂p.areaGain q) = 0 := by
      apply setLIntegral_eq_zero d.open_source.measurableSet.compl
      intro x hx
      change ENNReal.ofReal (v x) = 0
      have hvx : v x = 0 := by
        by_contra hvx
        exact hx (hvsource (subset_closure hvx))
      simp [hvx]
    rw [hz, add_zero]
  rw [hfull, p.areaGain_setLIntegral_coordinate_formula q hU hc
    d.open_source.measurableSet subset_rfl hv.continuous.measurable.ennreal_ofReal]
  rw [d.image_source_eq_target]
  have hcoord : (∫⁻ z in d.target,
      ENNReal.ofReal ((q.chartDensity d z)^2 - (p.chartDensity c z)^2) *
        ENNReal.ofReal (v (d.symm z))) =
      ∫⁻ z, ENNReal.ofReal (test z * Δ f z) := by
    rw [← lintegral_add_compl (fun z => ENNReal.ofReal (test z * Δ f z))
      d.open_target.measurableSet]
    have hout : (∫⁻ z in d.targetᶜ,
        ENNReal.ofReal (test z * Δ f z)) = 0 := by
      apply setLIntegral_eq_zero d.open_target.measurableSet.compl
      intro z hz
      change ENNReal.ofReal (test z * Δ f z) = 0
      have hzn : z ∉ d.target := hz
      have ht : test z = 0 := by
        simp [test, AreaDeficit.Surfaces.chartZeroExtensionIn, hzn]
      rw [ht, zero_mul, ENNReal.ofReal_zero]
    rw [hout, add_zero]
    apply setLIntegral_congr_fun d.open_target.measurableSet
    intro z hz
    change ENNReal.ofReal ((q.chartDensity d z)^2 - (p.chartDensity c z)^2) *
      ENNReal.ofReal (v (d.symm z)) = ENNReal.ofReal (test z * Δ f z)
    rw [show test z = v (d.symm z) from
      AreaDeficit.Surfaces.chartZeroExtensionIn_eq hz,
      p.chartLogRatio_laplacian q hU hc hz]
    rw [ENNReal.ofReal_mul (hvnonneg _)]
    exact mul_comm _ _
  rw [hcoord, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hpos)]
  congr 1
  exact AreaDeficit.green_laplacian hf htest htestCompact

/-- The chart Green boundary pairing above is nonnegative, because before
integration by parts it is the integral of the nonnegative area-gain
density. -/
theorem chart_green_nonneg
    (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {v : U → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v) (hvnonneg : ∀ x, 0 ≤ v x)
    (hvsource : tsupport v ⊆ (c.subtypeRestr hU).source)
    (hd : c.subtypeRestr hU ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 U) :
    0 ≤ ∫ z, p.chartLogRatio q hU c z *
      Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
        (c.subtypeRestr hU) v) z := by
  let d := c.subtypeRestr hU
  let test := AreaDeficit.Surfaces.chartZeroExtensionIn d v
  let f := p.chartLogRatio q hU c
  have htest : ContDiff ℝ 2 test :=
    AreaDeficit.Surfaces.contDiff_chartZeroExtensionIn
      hv hvcompact hvsource hd
  have htestCompact : HasCompactSupport test :=
    AreaDeficit.Surfaces.hasCompactSupport_chartZeroExtensionIn
      hvcompact hvsource
  have hK : IsCompact (d '' tsupport v) :=
    hvcompact.image_of_continuousOn (d.continuousOn.mono hvsource)
  have htestSupport : tsupport test ⊆ d '' tsupport v :=
    closure_minimal
      (AreaDeficit.Surfaces.support_chartZeroExtensionIn_subset.trans
        (image_mono subset_closure)) hK.isClosed
  have htarget : tsupport test ⊆ d.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := htestSupport hz
    exact d.map_source (hvsource hx)
  have hf : ∀ z ∈ tsupport test, ContDiffAt ℝ 2 f z :=
    fun z hz => p.chartLogRatio_contDiffAt q hU hc (htarget hz)
  change 0 ≤ ∫ z, f z * Δ test z
  rw [← AreaDeficit.green_laplacian hf htest htestCompact]
  apply integral_nonneg
  intro z
  change 0 ≤ test z * Δ f z
  by_cases hz : z ∈ tsupport test
  · rw [show test z = v (d.symm z) from
      AreaDeficit.Surfaces.chartZeroExtensionIn_eq (htarget hz)]
    exact mul_nonneg (hvnonneg _) (p.chartLogRatio_laplacian_nonneg
      q hU hc (htarget hz))
  · simp [image_eq_zero_of_notMem_tsupport hz]

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.areaGain_lintegral_eq_chart_green
#print axioms AreaDeficit.Surfaces.DiscCover.chart_green_nonneg
