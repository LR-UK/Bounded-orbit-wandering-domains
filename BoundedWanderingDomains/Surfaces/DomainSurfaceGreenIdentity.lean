/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainAreaGainIntegration
import BoundedWanderingDomains.Surfaces.DomainLogRatio
import BoundedWanderingDomains.Surfaces.ChartZeroExtension
import BoundedWanderingDomains.GreenIdentity

/-! # Green's identity for ambient domain-area gain -/

open Set Function Filter MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- A nonnegative cutoff supported in the smaller of two nested ambient
domains converts domain-area gain into a planar Green pairing.  Keeping the
cutoff and chart on the ambient surface permits one fixed partition of unity
to serve all finite-puncture stages. -/
theorem domainAreaGain_lintegral_eq_chart_green
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {v : M → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v) (hvnonneg : ∀ x, 0 ≤ v x)
    (hvsource : tsupport v ⊆ c.source)
    (hvV : tsupport v ⊆ V)
    (hcReal : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M) :
    (∫⁻ x, ENNReal.ofReal (v x) ∂p.domainAreaGain U V) =
      ENNReal.ofReal (∫ z, p.domainChartLogRatio U V c z *
        Δ (AreaDeficit.Surfaces.chartZeroExtensionIn c v) z) := by
  let test := AreaDeficit.Surfaces.chartZeroExtensionIn c v
  let f := p.domainChartLogRatio U V c
  have htest : ContDiff ℝ 2 test :=
    AreaDeficit.Surfaces.contDiff_chartZeroExtensionIn
      hv hvcompact hvsource hcReal
  have htestCompact : HasCompactSupport test :=
    AreaDeficit.Surfaces.hasCompactSupport_chartZeroExtensionIn
      hvcompact hvsource
  have htestSupport : tsupport test ⊆ c '' tsupport v := by
    have hK : IsCompact (c '' tsupport v) :=
      hvcompact.image_of_continuousOn (c.continuousOn.mono hvsource)
    exact closure_minimal
      (AreaDeficit.Surfaces.support_chartZeroExtensionIn_subset.trans
        (image_mono subset_closure)) hK.isClosed
  have htestDomain : tsupport test ⊆ domainChartSet V c := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := htestSupport hz
    refine ⟨c.map_source (hvsource hx), ?_⟩
    change c.symm (c x) ∈ V
    rw [c.left_inv (hvsource hx)]
    exact hvV hx
  have hf : ∀ z ∈ tsupport test, ContDiffAt ℝ 2 f z := by
    intro z hz
    exact p.domainChartLogRatio_contDiffAt hVU hc (htestDomain hz)
  have hlap : ∀ z ∈ tsupport test,
      Δ f z = (p.domainChartDensity V c z)^2 -
        (p.domainChartDensity U c z)^2 := by
    intro z hz
    exact p.domainChartLogRatio_laplacian hVU hc (htestDomain hz)
  have hpos : ∀ z, 0 ≤ test z * Δ f z := by
    intro z
    by_cases hz : z ∈ tsupport test
    · rw [show test z = v (c.symm z) from
        AreaDeficit.Surfaces.chartZeroExtensionIn_eq (htestDomain hz).1]
      exact mul_nonneg (hvnonneg _)
        (p.domainChartLogRatio_laplacian_nonneg hVU hc (htestDomain hz))
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hint : Integrable (fun z => test z * Δ f z) :=
    AreaDeficit.integrable_mul_of_local htest.continuous htestCompact
      (fun z hz => AreaDeficit.laplacian_continuousAt (hf z hz))
  have hfull : (∫⁻ x, ENNReal.ofReal (v x) ∂p.domainAreaGain U V) =
      ∫⁻ x in c.source, ENNReal.ofReal (v x) ∂p.domainAreaGain U V := by
    rw [← lintegral_add_compl (fun x => ENNReal.ofReal (v x))
      c.open_source.measurableSet]
    have hz : (∫⁻ x in c.sourceᶜ, ENNReal.ofReal (v x)
        ∂p.domainAreaGain U V) = 0 := by
      apply setLIntegral_eq_zero c.open_source.measurableSet.compl
      intro x hx
      change ENNReal.ofReal (v x) = 0
      have hvx : v x = 0 := by
        by_contra hvx
        exact hx (hvsource (subset_closure hvx))
      simp [hvx]
    rw [hz, add_zero]
  rw [hfull, p.domainAreaGain_setLIntegral_coordinate_formula U V hc
    c.open_source.measurableSet subset_rfl hv.continuous.measurable.ennreal_ofReal]
  rw [c.image_source_eq_target]
  have hcoord : (∫⁻ z in c.target,
      ENNReal.ofReal ((p.domainChartDensity V c z)^2 -
        (p.domainChartDensity U c z)^2) * ENNReal.ofReal (v (c.symm z))) =
      ∫⁻ z, ENNReal.ofReal (test z * Δ f z) := by
    rw [← lintegral_add_compl (fun z => ENNReal.ofReal (test z * Δ f z))
      c.open_target.measurableSet]
    have hout : (∫⁻ z in c.targetᶜ,
        ENNReal.ofReal (test z * Δ f z)) = 0 := by
      apply setLIntegral_eq_zero c.open_target.measurableSet.compl
      intro z hz
      change ENNReal.ofReal (test z * Δ f z) = 0
      have ht : test z = 0 := by
        have hzn : z ∉ c.target := hz
        simp [test, AreaDeficit.Surfaces.chartZeroExtensionIn, hzn]
      rw [ht, zero_mul, ENNReal.ofReal_zero]
    rw [hout, add_zero]
    apply setLIntegral_congr_fun c.open_target.measurableSet
    intro z hz
    change ENNReal.ofReal ((p.domainChartDensity V c z)^2 -
        (p.domainChartDensity U c z)^2) * ENNReal.ofReal (v (c.symm z)) =
      ENNReal.ofReal (test z * Δ f z)
    by_cases hzs : z ∈ tsupport test
    · rw [show test z = v (c.symm z) from
          AreaDeficit.Surfaces.chartZeroExtensionIn_eq hz,
        hlap z hzs, ENNReal.ofReal_mul (hvnonneg _)]
      exact mul_comm _ _
    · have ht : test z = 0 := image_eq_zero_of_notMem_tsupport hzs
      have hvz : v (c.symm z) = 0 := by
        have he : test z = v (c.symm z) :=
          AreaDeficit.Surfaces.chartZeroExtensionIn_eq hz
        exact he.symm.trans ht
      simp [ht, hvz]
  rw [hcoord, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hpos)]
  congr 1
  exact AreaDeficit.green_laplacian hf htest htestCompact

/-- Each local Green pairing in the ambient-domain formula is nonnegative. -/
theorem domain_chart_green_nonneg
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {v : M → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v) (hvnonneg : ∀ x, 0 ≤ v x)
    (hvsource : tsupport v ⊆ c.source) (hvV : tsupport v ⊆ V)
    (hcReal : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M) :
    0 ≤ ∫ z, p.domainChartLogRatio U V c z *
      Δ (AreaDeficit.Surfaces.chartZeroExtensionIn c v) z := by
  let test := AreaDeficit.Surfaces.chartZeroExtensionIn c v
  let f := p.domainChartLogRatio U V c
  have htest : ContDiff ℝ 2 test :=
    AreaDeficit.Surfaces.contDiff_chartZeroExtensionIn
      hv hvcompact hvsource hcReal
  have htestCompact : HasCompactSupport test :=
    AreaDeficit.Surfaces.hasCompactSupport_chartZeroExtensionIn
      hvcompact hvsource
  have hK : IsCompact (c '' tsupport v) :=
    hvcompact.image_of_continuousOn (c.continuousOn.mono hvsource)
  have htestSupport : tsupport test ⊆ c '' tsupport v :=
    closure_minimal
      (AreaDeficit.Surfaces.support_chartZeroExtensionIn_subset.trans
        (image_mono subset_closure)) hK.isClosed
  have hdomain : tsupport test ⊆ domainChartSet V c := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := htestSupport hz
    refine ⟨c.map_source (hvsource hx), ?_⟩
    change c.symm (c x) ∈ V
    rw [c.left_inv (hvsource hx)]
    exact hvV hx
  have hf : ∀ z ∈ tsupport test, ContDiffAt ℝ 2 f z :=
    fun z hz => p.domainChartLogRatio_contDiffAt hVU hc (hdomain hz)
  change 0 ≤ ∫ z, f z * Δ test z
  rw [← AreaDeficit.green_laplacian hf htest htestCompact]
  apply integral_nonneg
  intro z
  change 0 ≤ test z * Δ f z
  by_cases hz : z ∈ tsupport test
  · rw [show test z = v (c.symm z) from
      AreaDeficit.Surfaces.chartZeroExtensionIn_eq (hdomain hz).1]
    exact mul_nonneg (hvnonneg _)
      (p.domainChartLogRatio_laplacian_nonneg hVU hc (hdomain hz))
  · simp [image_eq_zero_of_notMem_tsupport hz]

end AreaDeficit.Surfaces.DiscCover
