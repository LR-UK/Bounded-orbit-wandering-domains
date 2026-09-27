/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.GlobalIntrinsicGreen
import BoundedWanderingDomains.Surfaces.FiniteSurfacePunctureCutoff

/-! # Green pairings for finite surface-puncture cutoffs -/

open Set Function Filter Metric MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ContDiff BigOperators

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

namespace FinitePunctureDiscs

private theorem center_mem_closedCarrier {F : Finset M}
    (D : FinitePunctureDiscs F) (i : ↥F) :
    (i : M) ∈ (D.disc i).closedCarrier := by
  rw [← D.center i]
  refine ⟨chartAt ℂ (D.disc i).center (D.disc i).center, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_self] using (D.disc i).radius_pos.le
  · exact (chartAt ℂ (D.disc i).center).left_inv
      (mem_chart_source ℂ (D.disc i).center)

/-- The intrinsic Laplacian of one puncture cutoff is supported away from
every puncture in the chosen pairwise-disjoint family. -/
theorem tsupport_intrinsicLaplacian_surfaceLogCutoff_subset
    (p : DiscCover M) {F : Finset M} (D : FinitePunctureDiscs F)
    {t : ℝ} (ht : D.Admissible t) (i : ↥F) :
    tsupport (p.intrinsicLaplacian (surfaceLogCutoff (D.disc i) t)) ⊆
      (↑F : Set M)ᶜ := by
  intro x hx hxF
  let j : ↥F := ⟨x, hxF⟩
  by_cases hji : j = i
  · have hxi : x = (i : M) := congrArg Subtype.val hji
    subst x
    have hone := surfaceLogCutoff_eventuallyEq_one_center
      (D.disc i) ht.1
    have hzero : (surfaceLogCutoff (D.disc i) t - fun _ => (1 : ℝ))
        =ᶠ[𝓝 (i : M)] 0 := by
      rw [← D.center i]
      filter_upwards [hone] with y hy
      simp [hy]
    have hnot : (i : M) ∉ tsupport
        (surfaceLogCutoff (D.disc i) t - fun _ => (1 : ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mpr hzero
    have hlap : p.intrinsicLaplacian
        (surfaceLogCutoff (D.disc i) t - fun _ => (1 : ℝ)) =
        p.intrinsicLaplacian (surfaceLogCutoff (D.disc i) t) := by
      funext y
      rw [p.intrinsicLaplacian_sub
        (surfaceLogCutoff_contMDiff (D.disc i) ht.1 (ht.2 i))
        contMDiff_const y, p.intrinsicLaplacian_const]
      ring
    have hx' : (i : M) ∈ tsupport (p.intrinsicLaplacian
        (surfaceLogCutoff (D.disc i) t - fun _ => (1 : ℝ))) := by
      simpa only [hlap] using hx
    exact hnot (p.tsupport_intrinsicLaplacian_subset _ hx')
  · have hxj : x ∈ (D.disc j).closedCarrier :=
      D.center_mem_closedCarrier j
    have hxi : x ∉ (D.disc i).closedCarrier := by
      intro hxi
      exact Set.disjoint_left.mp
        (D.pairwise (mem_univ j) (mem_univ i) hji) hxj hxi
    have hxeta : x ∉ tsupport (surfaceLogCutoff (D.disc i) t) :=
      fun h => hxi (surfaceLogCutoff_tsupport_subset_closedCarrier
        (D.disc i) ht.1 (ht.2 i) h)
    exact hxeta (p.tsupport_intrinsicLaplacian_subset _ hx)

private theorem surfaceLogCutoff_tsupport_subset_chartSource
    {F : Finset M} (D : FinitePunctureDiscs F)
    {t : ℝ} (ht : D.Admissible t) (i : ↥F) :
    tsupport (surfaceLogCutoff (D.disc i) t) ⊆
      (chartAt ℂ (D.disc i).center).source := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := surfaceLogCutoff_tsupport_subset_closedCarrier
    (D.disc i) ht.1 (ht.2 i) hx
  exact (chartAt ℂ (D.disc i).center).map_target
    ((D.disc i).closedBall_subset hz)

/-- A surface puncture cutoff has exactly the planar logarithmic boundary
pairing in its defining chart. -/
theorem domainChartGreen_surfaceLogCutoff
    (p : DiscCover M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {F : Finset M} (D : FinitePunctureDiscs F)
    {t : ℝ} (ht : D.Admissible t) (i : ↥F)
    (hV : tsupport (p.intrinsicLaplacian
      (surfaceLogCutoff (D.disc i) t)) ⊆ V) :
    (∫ z, p.domainChartLogRatio U V
        (chartAt ℂ (D.disc i).center) z *
      Δ (AreaDeficit.logCutoff
        (chartAt ℂ (D.disc i).center (D.disc i).center)
        (-2 * t) (-t)) z) =
      ∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian
        (surfaceLogCutoff (D.disc i) t) x ∂p.hyperbolicArea := by
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (chartAt ℂ (D.disc i).center)
      (chartAt ℂ (D.disc i).center).source :=
    (mdifferentiable_chart (I := 𝓘(ℂ)) (D.disc i).center).1
  have hcReal : chartAt ℂ (D.disc i).center ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M :=
    ambientChart_mem_real_maximalAtlas (M := M) (D.disc i).center
  rw [← chartZeroExtensionIn_surfaceLogCutoff
    (D.disc i) ht.1 (ht.2 i)]
  exact p.domainChartGreen_eq_intrinsic hVU hc
    (surfaceLogCutoff_contMDiff (D.disc i) ht.1 (ht.2 i))
    (surfaceLogCutoff_hasCompactSupport (D.disc i) ht.1 (ht.2 i))
    (D.surfaceLogCutoff_tsupport_subset_chartSource ht i) hV hcReal

/-- The global intrinsic Green boundary of the finite cutoff is the negative
sum of the pure planar puncture boundary pairings. -/
theorem DiscCover.intrinsicGreen_finitePunctureCutoff
    [CompactSpace M] (p : DiscCover M) {U : TopologicalSpace.Opens M}
    {F : Finset M} (hVU : finitePunctureDomain F ≤ U)
    (D : FinitePunctureDiscs F) {t : ℝ} (ht : D.Admissible t) :
    (∫ x, p.domainLogRatio U (finitePunctureDomain F) x *
        p.intrinsicLaplacian (D.cutoff t) x ∂p.hyperbolicArea) =
      - ∑ i : ↥F, ∫ z, p.domainChartLogRatio U
          (finitePunctureDomain F) (chartAt ℂ (D.disc i).center) z *
        Δ (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * t) (-t)) z := by
  let eta : ↥F → M → ℝ := fun i => surfaceLogCutoff (D.disc i) t
  have hetaSmooth : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (eta i) :=
    fun i => surfaceLogCutoff_contMDiff (D.disc i) ht.1 (ht.2 i)
  have hetaCompact : ∀ i, HasCompactSupport (eta i) :=
    fun i => surfaceLogCutoff_hasCompactSupport (D.disc i) ht.1 (ht.2 i)
  have hetaV : ∀ i, tsupport (p.intrinsicLaplacian (eta i)) ⊆
      finitePunctureDomain F := by
    intro i x hx
    exact D.tsupport_intrinsicLaplacian_surfaceLogCutoff_subset p ht i hx
  have hetaInt : ∀ i : ↥F, Integrable (fun x =>
      p.domainLogRatio U (finitePunctureDomain F) x *
        p.intrinsicLaplacian (eta i) x) p.hyperbolicArea := fun i =>
    p.integrable_domainLogRatio_mul_intrinsicLaplacian hVU
      (hetaSmooth i) (hetaCompact i) (hetaV i)
  have hlap : ∀ x, p.intrinsicLaplacian (D.cutoff t) x =
      - ∑ i : ↥F, p.intrinsicLaplacian (eta i) x := by
    intro x
    rw [show D.cutoff t = (fun _ => (1 : ℝ)) -
        (fun y => ∑ i : ↥F, eta i y) by rfl,
      p.intrinsicLaplacian_sub contMDiff_const
        (ContMDiff.sum fun i _ => hetaSmooth i) x,
      p.intrinsicLaplacian_const,
      p.intrinsicLaplacian_finsetSum Finset.univ eta
        (fun i _ => hetaSmooth i) x]
    simp
  calc
    (∫ x, p.domainLogRatio U (finitePunctureDomain F) x *
        p.intrinsicLaplacian (D.cutoff t) x ∂p.hyperbolicArea) =
        ∫ x, - ∑ i : ↥F, (p.domainLogRatio U
          (finitePunctureDomain F) x * p.intrinsicLaplacian (eta i) x)
            ∂p.hyperbolicArea := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hlap x, mul_neg, Finset.mul_sum]
    _ = - ∑ i : ↥F, ∫ x, p.domainLogRatio U
          (finitePunctureDomain F) x * p.intrinsicLaplacian (eta i) x
            ∂p.hyperbolicArea := by
      rw [integral_neg, integral_finsetSum Finset.univ]
      exact fun i _ => hetaInt i
    _ = - ∑ i : ↥F, ∫ z, p.domainChartLogRatio U
          (finitePunctureDomain F) (chartAt ℂ (D.disc i).center) z *
        Δ (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * t) (-t)) z := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (domainChartGreen_surfaceLogCutoff p hVU D ht i
        (hetaV i)).symm

end FinitePunctureDiscs
end AreaDeficit.Surfaces
