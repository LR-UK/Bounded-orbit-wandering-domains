/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AmbientChartPartition

/-! # Global Green identity for nested ambient domains -/

open Set Function MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff BigOperators

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- A compactly supported cutoff in the smaller nested domain is reduced to
a finite sum over one fixed ambient chart partition. -/
theorem domainAreaGain_lintegral_eq_finite_chart_green
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    (P : AreaDeficit.Surfaces.AmbientChartPartition M)
    {chi : M → ℝ} (hchi : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 chi)
    (hcompact : HasCompactSupport chi) (hnonneg : ∀ x, 0 ≤ chi x)
    (hchiV : tsupport chi ⊆ V) :
    (∫⁻ x, ENNReal.ofReal (chi x) ∂p.domainAreaGain U V) =
      ENNReal.ofReal
        (∑ i ∈ P.active chi hcompact,
          ∫ z, p.domainChartLogRatio U V (chartAt ℂ i) z *
            Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
              (chartAt ℂ i) (fun x => P.rho i x * chi x)) z) := by
  let S := P.active chi hcompact
  let v : M → M → ℝ := fun i x => P.rho i x * chi x
  let boundary : M → ℝ := fun i =>
    ∫ z, p.domainChartLogRatio U V (chartAt ℂ i) z *
      Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
        (chartAt ℂ i) (v i)) z
  have hvSmooth : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (v i) := by
    intro i
    exact ((P.rho i).contMDiff.of_le (by norm_num)).mul hchi
  have hvCompact : ∀ i, HasCompactSupport (v i) := by
    intro i
    exact hcompact.mul_left
  have hvNonneg : ∀ i x, 0 ≤ v i x := by
    intro i x
    exact mul_nonneg (P.rho.nonneg i x) (hnonneg x)
  have hvSource : ∀ i, tsupport (v i) ⊆ (chartAt ℂ i).source := by
    intro i
    exact tsupport_mul_subset_left.trans (P.subordinate i)
  have hvV : ∀ i, tsupport (v i) ⊆ V := by
    intro i
    exact tsupport_mul_subset_right.trans hchiV
  have hc : ∀ i : M, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (chartAt ℂ i) (chartAt ℂ i).source := fun i =>
    (mdifferentiable_chart (I := 𝓘(ℂ)) i).1
  have hcReal : ∀ i : M, chartAt ℂ i ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M :=
    AreaDeficit.Surfaces.ambientChart_mem_real_maximalAtlas
  have hlocal : ∀ i, (∫⁻ x, ENNReal.ofReal (v i x)
      ∂p.domainAreaGain U V) = ENNReal.ofReal (boundary i) := by
    intro i
    exact p.domainAreaGain_lintegral_eq_chart_green hVU (hc i)
      (hvSmooth i) (hvCompact i) (hvNonneg i) (hvSource i) (hvV i)
      (hcReal i)
  have hboundary : ∀ i, 0 ≤ boundary i := by
    intro i
    exact p.domain_chart_green_nonneg hVU (hc i)
      (hvSmooth i) (hvCompact i) (hvNonneg i) (hvSource i) (hvV i)
      (hcReal i)
  have hpoint : ∀ x, ENNReal.ofReal (chi x) =
      ∑ i ∈ S, ENNReal.ofReal (v i x) := by
    intro x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hvNonneg i x)]
    congr 1
    simpa only [S, v] using (P.sum_active_mul hcompact x).symm
  calc
    (∫⁻ x, ENNReal.ofReal (chi x) ∂p.domainAreaGain U V) =
        ∫⁻ x, ∑ i ∈ S, ENNReal.ofReal (v i x)
          ∂p.domainAreaGain U V := lintegral_congr hpoint
    _ = ∑ i ∈ S, ∫⁻ x, ENNReal.ofReal (v i x)
          ∂p.domainAreaGain U V := by
      apply MeasureTheory.lintegral_finsetSum
      intro i hi
      exact (hvSmooth i).continuous.measurable.ennreal_ofReal
    _ = ∑ i ∈ S, ENNReal.ofReal (boundary i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hlocal i
    _ = ENNReal.ofReal (∑ i ∈ S, boundary i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hboundary i)]
    _ = _ := by rfl

end AreaDeficit.Surfaces.DiscCover
