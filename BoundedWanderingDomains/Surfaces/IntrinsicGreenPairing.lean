module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.IntrinsicSurfaceLaplacian
public import BoundedWanderingDomains.Surfaces.DomainSurfaceGreenIdentity
public import BoundedWanderingDomains.Surfaces.AreaIntegration

@[expose] public section

/-! # Coordinate Green pairings as intrinsic surface integrals -/

open Set Function Filter MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- A chart Green pairing is the integral of the intrinsic logarithmic
quotient against the intrinsic Laplacian of the test function. -/
theorem domainChartGreen_eq_intrinsic
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {v : M → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v)
    (hvsource : tsupport v ⊆ c.source)
    (hvV : tsupport (p.intrinsicLaplacian v) ⊆ V)
    (hcReal : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M) :
    (∫ z, p.domainChartLogRatio U V c z *
      Δ (AreaDeficit.Surfaces.chartZeroExtensionIn c v) z) =
      ∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian v x
        ∂p.hyperbolicArea := by
  let test := AreaDeficit.Surfaces.chartZeroExtensionIn c v
  let b : M → ℝ := fun x =>
    p.domainLogRatio U V x * p.intrinsicLaplacian v x
  have hb : Measurable b :=
    (p.domainLogRatio_measurable U V).mul
      (p.intrinsicLaplacian_continuous hv).measurable
  have hbzero : ∀ x ∉ c.source, b x = 0 := by
    intro x hxc
    have hxnot : x ∉ tsupport v := fun hx => hxc (hvsource hx)
    simp [b, p.intrinsicLaplacian_eq_zero_of_notMem_tsupport hxnot]
  have hglobal : (∫ x, b x ∂p.hyperbolicArea) =
      ∫ x in c.source, b x ∂p.hyperbolicArea := by
    rw [← integral_indicator c.open_source.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ c.source
    · simp [hx]
    · simp [hx, hbzero x hx]
  rw [show (∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian v x
      ∂p.hyperbolicArea) = ∫ x, b x ∂p.hyperbolicArea from rfl,
    hglobal, p.hyperbolicArea_setIntegral_chart_source hc hb]
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
  have htestTarget : tsupport test ⊆ c.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := htestSupport hz
    exact c.map_source (hvsource hx)
  have hIntrinsicSupport : tsupport (p.intrinsicLaplacian v) ⊆ tsupport v :=
    p.tsupport_intrinsicLaplacian_subset v
  have htestLapSupport : tsupport (Δ test) ⊆
      c '' tsupport (p.intrinsicLaplacian v) := by
    have hK : IsCompact (c '' tsupport (p.intrinsicLaplacian v)) :=
      (hvcompact.of_isClosed_subset (isClosed_tsupport _)
        hIntrinsicSupport).image_of_continuousOn
          (c.continuousOn.mono (hIntrinsicSupport.trans hvsource))
    apply closure_minimal _ hK.isClosed
    intro z hz
    have hztest : z ∈ tsupport test :=
      AreaDeficit.laplacian_tsupport_subset test (subset_closure hz)
    have hzt := htestTarget hztest
    let x := c.symm z
    have hxs : x ∈ c.source := c.map_target hzt
    have hcx : c x = z := c.right_inv hzt
    refine ⟨x, ?_, hcx⟩
    apply subset_closure
    intro hzero
    have hlapIntrinsic : p.intrinsicLaplacian v x =
        Δ (v ∘ c.symm) z / (p.density c x) ^ 2 := by
      simpa only [hcx] using
        p.intrinsicLaplacian_eq_in_chart_of_contMDiff hc hv hxs
    have hlocal : test =ᶠ[𝓝 z] v ∘ c.symm := by
      filter_upwards [c.open_target.mem_nhds hzt] with w hw
      exact AreaDeficit.Surfaces.chartZeroExtensionIn_eq hw
    have hlaptest : Δ test z = Δ (v ∘ c.symm) z :=
      (laplacian_congr_nhds hlocal).eq_of_nhds
    have hdens : p.density c x ≠ 0 := ne_of_gt (p.density_pos hc hxs)
    have hlapzero : Δ (v ∘ c.symm) z = 0 := by
      rw [hzero] at hlapIntrinsic
      field_simp [hdens] at hlapIntrinsic
      simpa using hlapIntrinsic.symm
    exact hz (by rw [hlaptest, hlapzero])
  have hf : ∀ z ∈ tsupport (Δ test), ContDiffAt ℝ 2 f z := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := htestLapSupport hz
    have hxt : x ∈ tsupport v := hIntrinsicSupport hx
    have hzt : z ∈ c.target := hzx ▸ c.map_source (hvsource hxt)
    have hzV : z ∈ domainChartSet V c := by
      refine ⟨hzt, ?_⟩
      change c.symm z ∈ V
      rw [← hzx, c.left_inv (hvsource hxt)]
      exact hvV hx
    exact p.domainChartLogRatio_contDiffAt hVU hc hzV
  have hLapCont : Continuous (Δ test) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact AreaDeficit.laplacian_continuousAt htest.contDiffAt
  have hint : Integrable (fun z => f z * Δ test z) := by
    have h := AreaDeficit.integrable_mul_of_local hLapCont
      (AreaDeficit.laplacian_hasCompactSupport htestCompact)
      (fun z hz => (hf z hz).continuousAt)
    simpa only [mul_comm] using h
  have hleft : (∫ z, f z * Δ test z) =
      ∫ z in c.target, f z * Δ test z := by
    rw [← integral_indicator c.open_target.measurableSet]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ c.target
    · simp [hz]
    · have hzts : z ∉ tsupport test := fun h => hz (htestTarget h)
      have hlap : Δ test z = 0 := by
        have he := notMem_tsupport_iff_eventuallyEq.mp hzts
        calc
          Δ test z = Δ (fun _ : ℂ => (0 : ℝ)) z :=
            (laplacian_congr_nhds he).eq_of_nhds
          _ = 0 := by simp
      simp [hz, hlap]
  rw [show (∫ z, p.domainChartLogRatio U V c z * Δ test z) =
      ∫ z, f z * Δ test z from rfl, hleft]
  apply setIntegral_congr_fun c.open_target.measurableSet
  intro z hz
  let x := c.symm z
  have hxs : x ∈ c.source := c.map_target hz
  have hcx : c x = z := c.right_inv hz
  by_cases hx : x ∈ tsupport (p.intrinsicLaplacian v)
  · have hlog := p.domainLogRatio_eq_chart hVU hc (hvV hx) hxs
    have hlap := p.intrinsicLaplacian_eq_in_chart_of_contMDiff hc hv hxs
    have htestLocal : test =ᶠ[𝓝 z] v ∘ c.symm := by
      filter_upwards [c.open_target.mem_nhds hz] with w hw
      exact AreaDeficit.Surfaces.chartZeroExtensionIn_eq hw
    have hlaptest : Δ test z = Δ (v ∘ c.symm) z :=
      (laplacian_congr_nhds htestLocal).eq_of_nhds
    have hdens : p.chartDensity c z = p.density c x := by
      change p.density c (c.symm z) = p.density c x
      rfl
    have hlogz : p.domainLogRatio U V x = f z := by
      simpa only [f, hcx] using hlog
    have hlapz : p.intrinsicLaplacian v x =
        Δ (v ∘ c.symm) z / (p.density c x) ^ 2 := by
      simpa only [hcx] using hlap
    dsimp only [b]
    change f z * Δ test z = p.chartDensity c z ^ 2 *
      (p.domainLogRatio U V x * p.intrinsicLaplacian v x)
    rw [hlogz, hlapz, hlaptest, hdens]
    have hdp : p.density c x ≠ 0 := ne_of_gt (p.density_pos hc hxs)
    field_simp
  · have hLint : p.intrinsicLaplacian v x = 0 :=
      by
        by_contra hne
        exact hx (subset_closure hne)
    have hlapIntrinsic :=
      p.intrinsicLaplacian_eq_in_chart_of_contMDiff hc hv hxs
    have htestLocal : test =ᶠ[𝓝 z] v ∘ c.symm := by
      filter_upwards [c.open_target.mem_nhds hz] with w hw
      exact AreaDeficit.Surfaces.chartZeroExtensionIn_eq hw
    have hlap : Δ test z = 0 := by
      have hlaptest : Δ test z = Δ (v ∘ c.symm) z :=
        (laplacian_congr_nhds htestLocal).eq_of_nhds
      have hdens : p.density c x ≠ 0 := ne_of_gt (p.density_pos hc hxs)
      rw [hLint, hcx] at hlapIntrinsic
      have hzero : Δ (v ∘ c.symm) z = 0 := by
        field_simp [hdens] at hlapIntrinsic
        simpa using hlapIntrinsic.symm
      rw [hlaptest, hzero]
    simp [hlap, b, x, hLint]

/-- Coordinate transport for an intrinsic Green integrand when only the
Laplacian, rather than the test function, has compactly localised support.
This is the form needed for cutoffs which tend to a constant at a deleted
compactification point. -/
theorem domainChartLaplacianIntegral_eq_intrinsic
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {v : M → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    {w : ℂ → ℝ}
    (hvsource : tsupport (p.intrinsicLaplacian v) ⊆ c.source)
    (hvV : tsupport (p.intrinsicLaplacian v) ⊆ V)
    (hw : ∀ z ∈ c.target, Δ w z = Δ (v ∘ c.symm) z)
    (hwsupport : tsupport (Δ w) ⊆ c.target)
    (_hint : Integrable (fun x => p.domainLogRatio U V x *
      p.intrinsicLaplacian v x) p.hyperbolicArea) :
    (∫ z, p.domainChartLogRatio U V c z * Δ w z) =
      ∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian v x
        ∂p.hyperbolicArea := by
  let b : M → ℝ := fun x =>
    p.domainLogRatio U V x * p.intrinsicLaplacian v x
  have hb : Measurable b :=
    (p.domainLogRatio_measurable U V).mul
      (p.intrinsicLaplacian_continuous hv).measurable
  have hbzero : ∀ x ∉ c.source, b x = 0 := by
    intro x hxc
    have hxnot : x ∉ tsupport (p.intrinsicLaplacian v) :=
      fun hx => hxc (hvsource hx)
    have hzero : p.intrinsicLaplacian v x = 0 := by
      by_contra hne
      exact hxnot (subset_closure hne)
    simp [b, hzero]
  have hglobal : (∫ x, b x ∂p.hyperbolicArea) =
      ∫ x in c.source, b x ∂p.hyperbolicArea := by
    rw [← integral_indicator c.open_source.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ c.source
    · simp [hx]
    · simp [hx, hbzero x hx]
  rw [show (∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian v x
      ∂p.hyperbolicArea) = ∫ x, b x ∂p.hyperbolicArea from rfl,
    hglobal, p.hyperbolicArea_setIntegral_chart_source hc hb]
  have htarget : (∫ z in c.target,
      p.chartDensity c z ^ 2 * b (c.symm z)) =
      ∫ z in c.target, p.domainChartLogRatio U V c z * Δ w z := by
    apply setIntegral_congr_fun c.open_target.measurableSet
    intro z hz
    let x := c.symm z
    have hxs : x ∈ c.source := c.map_target hz
    have hcx : c x = z := c.right_inv hz
    have hlap := p.intrinsicLaplacian_eq_in_chart_of_contMDiff hc hv hxs
    have hdens : p.chartDensity c z = p.density c x := by rfl
    by_cases hx : x ∈ tsupport (p.intrinsicLaplacian v)
    · have hlog := p.domainLogRatio_eq_chart hVU hc (hvV hx) hxs
      have hlogz : p.domainLogRatio U V x =
          p.domainChartLogRatio U V c z := by
        simpa only [hcx] using hlog
      have hlapz : p.intrinsicLaplacian v x =
          Δ (v ∘ c.symm) z / (p.density c x) ^ 2 := by
        simpa only [hcx] using hlap
      dsimp only [b]
      rw [hlogz, hlapz, ← hw z hz, hdens]
      have hdp : p.density c x ≠ 0 := ne_of_gt (p.density_pos hc hxs)
      field_simp
    · have hLint : p.intrinsicLaplacian v x = 0 := by
        by_contra hne
        exact hx (subset_closure hne)
      have hzero : Δ (v ∘ c.symm) z = 0 := by
        rw [hLint, hcx] at hlap
        have hdp : p.density c x ≠ 0 := ne_of_gt (p.density_pos hc hxs)
        field_simp [hdp] at hlap
        simpa using hlap.symm
      simp [b, x, hLint, hw z hz, hzero]
  rw [htarget]
  rw [← integral_indicator c.open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ c.target
  · simp [hz]
  · have hznot : z ∉ tsupport (Δ w) := fun h => hz (hwsupport h)
    have hzero : Δ w z = 0 := by
      by_contra hne
      exact hznot (subset_closure hne)
    simp [hz, hzero]

end AreaDeficit.Surfaces.DiscCover
