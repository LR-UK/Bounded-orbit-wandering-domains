/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.GlobalDomainSurfaceGreen
import BoundedWanderingDomains.Surfaces.IntrinsicGreenPairing
import BoundedWanderingDomains.Surfaces.HyperbolicAreaFinite

/-! # Cancellation of chart-partition terms in the global Green formula -/

open Set Function Filter MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ContDiff BigOperators

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem integrable_domainLogRatio_mul_intrinsicLaplacian
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {v : M → ℝ} (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v)
    (hvcompact : HasCompactSupport v)
    (hvV : tsupport (p.intrinsicLaplacian v) ⊆ V) :
    Integrable (fun x => p.domainLogRatio U V x *
      p.intrinsicLaplacian v x) p.hyperbolicArea := by
  letI : IsLocallyFiniteMeasure p.hyperbolicArea :=
    p.hyperbolicArea_locallyFinite
  have hLcont := p.intrinsicLaplacian_continuous hv
  have hLsupport := p.tsupport_intrinsicLaplacian_subset v
  have hprod : Continuous (fun x => p.domainLogRatio U V x *
      p.intrinsicLaplacian v x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport (p.intrinsicLaplacian v)
    · exact (p.domainLogRatio_continuousAt hVU (hvV hx)).mul
        hLcont.continuousAt
    · apply (show ContinuousAt (fun _ : M => (0 : ℝ)) x from
        continuousAt_const).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  have hLcompact : HasCompactSupport (p.intrinsicLaplacian v) :=
    hvcompact.of_isClosed_subset (isClosed_tsupport _)
      (p.tsupport_intrinsicLaplacian_subset v)
  exact hprod.integrable_of_hasCompactSupport hLcompact.mul_left

/-- The finite ambient chart sum is independent of the chosen partition:
all partition derivatives cancel in the intrinsic Laplacian. -/
theorem finite_chart_green_eq_intrinsic
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    (P : AreaDeficit.Surfaces.AmbientChartPartition M)
    {chi : M → ℝ} (hchi : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 chi)
    (hcompact : HasCompactSupport chi) (hchiV : tsupport chi ⊆ V) :
    (∑ i ∈ P.active chi hcompact,
      ∫ z, p.domainChartLogRatio U V (chartAt ℂ i) z *
        Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
          (chartAt ℂ i) (fun x => P.rho i x * chi x)) z) =
      ∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian chi x
        ∂p.hyperbolicArea := by
  let S := P.active chi hcompact
  let v : M → M → ℝ := fun i x => P.rho i x * chi x
  have hvSmooth : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (v i) := by
    intro i
    exact ((P.rho i).contMDiff.of_le (by norm_num)).mul hchi
  have hvCompact : ∀ i, HasCompactSupport (v i) := fun _ => hcompact.mul_left
  have hvSource : ∀ i, tsupport (v i) ⊆ (chartAt ℂ i).source := fun i =>
    tsupport_mul_subset_left.trans (P.subordinate i)
  have hvV : ∀ i, tsupport (v i) ⊆ V := fun _ =>
    tsupport_mul_subset_right.trans hchiV
  have hc : ∀ i : M, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (chartAt ℂ i) (chartAt ℂ i).source := fun i =>
    (mdifferentiable_chart (I := 𝓘(ℂ)) i).1
  have hcReal : ∀ i : M, chartAt ℂ i ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M :=
    AreaDeficit.Surfaces.ambientChart_mem_real_maximalAtlas
  have hvInt : ∀ i ∈ S, Integrable (fun x =>
      p.domainLogRatio U V x * p.intrinsicLaplacian (v i) x)
      p.hyperbolicArea := fun i _ =>
    p.integrable_domainLogRatio_mul_intrinsicLaplacian hVU
      (hvSmooth i) (hvCompact i)
      ((p.tsupport_intrinsicLaplacian_subset (v i)).trans (hvV i))
  calc
    (∑ i ∈ S, ∫ z, p.domainChartLogRatio U V (chartAt ℂ i) z *
        Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
          (chartAt ℂ i) (v i)) z) =
        ∑ i ∈ S, ∫ x, p.domainLogRatio U V x *
          p.intrinsicLaplacian (v i) x ∂p.hyperbolicArea := by
      apply Finset.sum_congr rfl
      intro i hi
      exact p.domainChartGreen_eq_intrinsic hVU (hc i) (hvSmooth i)
        (hvCompact i) (hvSource i)
        ((p.tsupport_intrinsicLaplacian_subset (v i)).trans (hvV i))
        (hcReal i)
    _ = ∫ x, ∑ i ∈ S, (p.domainLogRatio U V x *
          p.intrinsicLaplacian (v i) x) ∂p.hyperbolicArea := by
      rw [integral_finset_sum S hvInt]
    _ = ∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian chi x
          ∂p.hyperbolicArea := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← Finset.mul_sum]
      congr 1
      have hlap := p.intrinsicLaplacian_finsetSum S v
        (fun i _ => hvSmooth i) x
      have hfun : (fun y => ∑ i ∈ S, v i y) = chi := by
        funext y
        exact P.sum_active_mul hcompact y
      rw [hfun] at hlap
      exact hlap.symm

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.finite_chart_green_eq_intrinsic
