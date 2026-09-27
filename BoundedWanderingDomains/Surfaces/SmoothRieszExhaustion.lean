/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.GlobalSurfaceGreen
import BoundedWanderingDomains.Surfaces.FiniteBoundaryMassAssembly
import BoundedWanderingDomains.Surfaces.SmoothCompactExhaustion

/-! # Smooth Riesz exhaustions imply finite global area gain -/

open Set Function Filter MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff BigOperators

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Concrete smooth-exhaustion form of the Riesz hypothesis.  Unlike the
measure-only interface, its boundary term is the finite chart sum furnished
by the global surface Green identity. -/
def SmoothRieszExhaustionBound
    (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∃ (P : AreaDeficit.Surfaces.RestrictedChartPartition U hU)
    (chi : ℕ → U → ℝ),
    ∃ hcompact : ∀ n, HasCompactSupport (chi n),
    (∀ n, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (chi n)) ∧
    (∀ n x, 0 ≤ chi n x) ∧
    (∀ᵐ x ∂p.areaGain q,
      Tendsto (fun n => ENNReal.ofReal (chi n x)) atTop (𝓝 1)) ∧
    ∀ᶠ n : ℕ in atTop,
      |∑ i ∈ P.active (chi n) (hcompact n),
        ∫ z, p.chartLogRatio q hU (chartAt ℂ (i : M)) z *
          Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
            ((chartAt ℂ (i : M)).subtypeRestr hU)
            (fun x => P.rho i x * chi n x)) z| ≤ B

/-- The qualitative part of the smooth Riesz package is automatic.  Thus
all remaining content of `SmoothRieszExhaustionBound` is the quantitative
bound on the displayed finite Green sums. -/
theorem exists_smoothRiesz_exhaustion_data
    (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) :
    ∃ (P : AreaDeficit.Surfaces.RestrictedChartPartition U hU)
      (chi : ℕ → U → ℝ) (hcompact : ∀ n, HasCompactSupport (chi n)),
      (∀ n, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (chi n)) ∧
      (∀ n x, 0 ≤ chi n x) ∧
      ∀ᵐ x ∂p.areaGain q,
        Tendsto (fun n => ENNReal.ofReal (chi n x)) atTop (𝓝 1) := by
  obtain ⟨P⟩ := AreaDeficit.Surfaces.exists_restrictedChartPartition U hU
  obtain ⟨chi, hsmooth, hcompact, hbounds, hOne⟩ :=
    AreaDeficit.Surfaces.exists_smooth_compact_exhaustion (M := U)
  refine ⟨P, chi, hcompact, fun n => (hsmooth n).of_le (by norm_num),
    fun n x => (hbounds n x).1, ?_⟩
  filter_upwards with x
  apply tendsto_const_nhds.congr'
  filter_upwards [hOne x] with n hn
  simp [hn]

/-- A bounded smooth Riesz exhaustion controls the complete intrinsic
area-gain mass. -/
theorem areaGain_univ_le_of_smoothRieszExhaustion
    (p : DiscCover M) {U : TopologicalSpace.Opens M}
    (q : DiscCover U) (hU : Nonempty U) {B : ℝ}
    (h : p.SmoothRieszExhaustionBound q hU B) :
    p.areaGain q Set.univ ≤ ENNReal.ofReal B := by
  obtain ⟨hB, P, chi, hcompact, hsmooth, hnonneg, hlim, hbound⟩ := h
  let boundary : ℕ → ℝ := fun n =>
    ∑ i ∈ P.active (chi n) (hcompact n),
      ∫ z, p.chartLogRatio q hU (chartAt ℂ (i : M)) z *
        Δ (AreaDeficit.Surfaces.chartZeroExtensionIn
          ((chartAt ℂ (i : M)).subtypeRestr hU)
          (fun x => P.rho i x * chi n x)) z
  apply AreaDeficit.Surfaces.measure_univ_le_of_eventually_bounded_riesz_cutoffs
    (p.areaGain q) (fun n x => ENNReal.ofReal (chi n x))
  · intro n
    exact (hsmooth n).continuous.measurable.ennreal_ofReal.aemeasurable
  · exact hlim
  · intro n
    simpa only [boundary] using p.areaGain_lintegral_eq_finite_chart_green
      q hU P (hsmooth n) (hcompact n) (hnonneg n)
  · exact hB
  · simpa only [boundary] using hbound

end AreaDeficit.Surfaces.DiscCover
