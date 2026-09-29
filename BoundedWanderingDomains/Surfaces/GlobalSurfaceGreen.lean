module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SurfaceChartPartition

@[expose] public section

/-! # Global surface Green identity from a finite active chart partition -/

open Set Function MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff BigOperators

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- An arbitrary smooth compactly supported nonnegative cutoff is reduced to
finitely many chart Green pairings.  Local finiteness of the smooth partition
is what makes the displayed boundary sum finite. -/
theorem areaGain_lintegral_eq_finite_chart_green
    (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U)
    (P : AreaDeficit.Surfaces.RestrictedChartPartition U hU)
    {chi : U → ℝ} (hchi : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 chi)
    (hcompact : HasCompactSupport chi) (hnonneg : ∀ x, 0 ≤ chi x) :
    (∫⁻ x, ENNReal.ofReal (chi x) ∂p.areaGain q) =
      ENNReal.ofReal
        (∑ i ∈ P.active chi hcompact,
          ∫ z, p.chartLogRatio q hU (chartAt ℂ (i : M)) z *
            Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
              ((chartAt ℂ (i : M)).subtypeRestr hU)
              (fun x => P.rho i x * chi x)) z) := by
  let S := P.active chi hcompact
  let v : U → U → ℝ := fun i x => P.rho i x * chi x
  let boundary : U → ℝ := fun i =>
    ∫ z, p.chartLogRatio q hU (chartAt ℂ (i : M)) z *
      Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
        ((chartAt ℂ (i : M)).subtypeRestr hU) (v i)) z
  have hvSmooth : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (v i) := by
    intro i
    exact ((P.rho i).contMDiff.of_le (by norm_num)).mul hchi
  have hvCompact : ∀ i, HasCompactSupport (v i) := by
    intro i
    exact hcompact.mul_left
  have hvNonneg : ∀ i x, 0 ≤ v i x := by
    intro i x
    exact mul_nonneg (P.rho.nonneg i x) (hnonneg x)
  have hvSource : ∀ i, tsupport (v i) ⊆
      ((chartAt ℂ (i : M)).subtypeRestr hU).source := by
    intro i
    exact tsupport_mul_subset_left.trans (P.subordinate i)
  have hc : ∀ i : U, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (chartAt ℂ (i : M)) (chartAt ℂ (i : M)).source := fun i =>
    (mdifferentiable_chart (I := 𝓘(ℂ)) (i : M)).1
  have hd : ∀ i : U, (chartAt ℂ (i : M)).subtypeRestr hU ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 U :=
    AreaDeficit.Surfaces.restrictedAmbientChart_mem_real_maximalAtlas hU
  have hlocal : ∀ i, (∫⁻ x, ENNReal.ofReal (v i x) ∂p.areaGain q) =
      ENNReal.ofReal (boundary i) := by
    intro i
    exact p.areaGain_lintegral_eq_chart_green q hU (hc i)
      (hvSmooth i) (hvCompact i) (hvNonneg i) (hvSource i) (hd i)
  have hboundary : ∀ i, 0 ≤ boundary i := by
    intro i
    exact p.chart_green_nonneg q hU (hc i)
      (hvSmooth i) (hvCompact i) (hvNonneg i) (hvSource i) (hd i)
  have hpoint : ∀ x, ENNReal.ofReal (chi x) =
      ∑ i ∈ S, ENNReal.ofReal (v i x) := by
    intro x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hvNonneg i x)]
    congr 1
    simpa only [S, v] using (P.sum_active_mul hcompact x).symm
  calc
    (∫⁻ x, ENNReal.ofReal (chi x) ∂p.areaGain q) =
        ∫⁻ x, ∑ i ∈ S, ENNReal.ofReal (v i x) ∂p.areaGain q :=
      lintegral_congr hpoint
    _ = ∑ i ∈ S, ∫⁻ x, ENNReal.ofReal (v i x) ∂p.areaGain q := by
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
