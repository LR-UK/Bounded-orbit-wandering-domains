/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactificationCutoff
import BoundedWanderingDomains.Surfaces.GlobalIntrinsicGreen
import BoundedWanderingDomains.Surfaces.SurfaceChartPartition

/-! # Green pairings for compactification end cutoffs -/

open Set Function Filter Metric MeasureTheory InnerProductSpace Laplacian
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X]

namespace FinitePunctureDiscs

private theorem closedCarrier_subset_chartSource
    (D : RiemannDynamics.CoordDisk X) :
    D.closedCarrier ⊆ (chartAt ℂ D.center).source := by
  rintro x ⟨z, hz, rfl⟩
  exact (chartAt ℂ D.center).map_target (D.closedBall_subset hz)

/-- The difference of two end cutoffs is supported in the restricted ambient
chart even when the common centre is a missing compactification point. -/
theorem tsupport_restrictedSurfaceLogCutoffDiff_subset_chartSource
    {F : Finset X} (D : FinitePunctureDiscs F) (i : ↑F)
    (O : TopologicalSpace.Opens X) (hON : Nonempty O)
    {t s : ℝ} (ht : D.Admissible t) (hs : D.Admissible s) :
    tsupport (restrictedSurfaceLogCutoffDiff (D.disc i) O t s) ⊆
      ((chartAt ℂ (D.disc i).center).subtypeRestr hON).source := by
  intro x hx
  have hxg : (x : X) ∈ tsupport
      (surfaceLogCutoff (D.disc i) t -
        surfaceLogCutoff (D.disc i) s) :=
    (tsupport_comp_subset_preimage _ continuous_subtype_val) hx
  have hxu : (x : X) ∈
      tsupport (surfaceLogCutoff (D.disc i) t) ∪
        tsupport (surfaceLogCutoff (D.disc i) s) :=
    tsupport_sub _ _ hxg
  have hxcarrier : (x : X) ∈ (D.disc i).closedCarrier := by
    rcases hxu with hxt | hxs
    · exact surfaceLogCutoff_tsupport_subset_closedCarrier
        (D.disc i) ht.1 (ht.2 i) hxt
    · exact surfaceLogCutoff_tsupport_subset_closedCarrier
        (D.disc i) hs.1 (hs.2 i) hxs
  simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using
    closedCarrier_subset_chartSource (D.disc i) hxcarrier

/-- Green's identity for the compactly supported difference of two readings
of a single compactification end cutoff. -/
theorem DiscCover.domainChartGreen_restrictedSurfaceLogCutoffDiff
    {O : TopologicalSpace.Opens X} (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    (p : DiscCover O) {U V : TopologicalSpace.Opens O} (hVU : V ≤ U)
    {F : Finset X} (D : FinitePunctureDiscs F) (i : ↑F)
    (E : Finset X) (hO : ∀ x : X, x ∈ O ↔ x ∉ E)
    (hEF : E ⊆ F) {t s : ℝ}
    (ht : D.Admissible t) (hs : D.Admissible s)
    (hvV : tsupport (p.intrinsicLaplacian
      (restrictedSurfaceLogCutoffDiff (D.disc i) O t s)) ⊆ V) :
    (let c := (chartAt ℂ (D.disc i).center).subtypeRestr hON
     let a := chartAt ℂ (D.disc i).center (D.disc i).center
     ∫ z, p.domainChartLogRatio U V c z *
       Δ (AreaDeficit.logCutoff a (-2 * t) (-t) -
         AreaDeficit.logCutoff a (-2 * s) (-s)) z) =
      ∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian
        (restrictedSurfaceLogCutoffDiff (D.disc i) O t s) x
          ∂p.hyperbolicArea := by
  let cX := chartAt ℂ (D.disc i).center
  let c := cX.subtypeRestr hON
  let v := restrictedSurfaceLogCutoffDiff (D.disc i) O t s
  have hcX : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cX cX.source :=
    (mdifferentiable_chart (I := 𝓘(ℂ)) (D.disc i).center).1
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    mdifferentiableOn_subtypeRestr hON hcX
  have hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v :=
    restrictedSurfaceLogCutoffDiff_contMDiff (D.disc i) O
      ht.1 (ht.2 i) hs.1 (hs.2 i)
  have hvcompact : HasCompactSupport v :=
    D.restrictedSurfaceLogCutoffDiff_hasCompactSupport i O E hO hEF ht hs
  have hvsource : tsupport v ⊆ c.source :=
    D.tsupport_restrictedSurfaceLogCutoffDiff_subset_chartSource i O hON ht hs
  have hcReal : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 O := by
    letI : IsManifold 𝓘(ℝ, ℂ) ∞ X := isManifold_real_of_complex
    letI : IsManifold 𝓘(ℝ, ℂ) ∞ O := isManifold_real_of_complex
    exact StructureGroupoid.subtypeRestr_mem_maximalAtlas
      (G := contDiffGroupoid 2 𝓘(ℝ, ℂ))
        (chart_mem_atlas ℂ (D.disc i).center) hON
  have hgreen := p.domainChartGreen_eq_intrinsic hVU hc hv hvcompact
    hvsource hvV hcReal
  have hchart := D.chartZeroExtensionIn_restrictedSurfaceLogCutoffDiff
    i O hON E hO hEF ht hs
  dsimp only
  rw [← hchart]
  exact hgreen

/-- The intrinsic Green pairing of a normalized compactification cutoff is
the negative finite sum of the corresponding normalized planar end
pairings. -/
theorem DiscCover.intrinsicGreen_restrictedCutoff_sub
    {O : TopologicalSpace.Opens X} (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    (p : DiscCover O) {U V : TopologicalSpace.Opens O} (hVU : V ≤ U)
    {F : Finset X} (D : FinitePunctureDiscs F)
    (E : Finset X) (hO : ∀ x : X, x ∈ O ↔ x ∉ E)
    (hEF : E ⊆ F) {t s : ℝ}
    (ht : D.Admissible t) (hs : D.Admissible s)
    (hetaV : ∀ i : ↑F, tsupport (p.intrinsicLaplacian
      (restrictedSurfaceLogCutoffDiff (D.disc i) O t s)) ⊆ V) :
    (∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian
        (D.restrictedCutoff O t - D.restrictedCutoff O s) x
          ∂p.hyperbolicArea) =
      - ∑ i : ↑F, ∫ z,
        p.domainChartLogRatio U V
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
        Δ (AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * t) (-t) -
          AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * s) (-s)) z := by
  let eta : ↑F → O → ℝ := fun i =>
    restrictedSurfaceLogCutoffDiff (D.disc i) O t s
  have hetaSmooth : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (eta i) :=
    fun i => restrictedSurfaceLogCutoffDiff_contMDiff (D.disc i) O
      ht.1 (ht.2 i) hs.1 (hs.2 i)
  have hetaCompact : ∀ i, HasCompactSupport (eta i) := fun i =>
    D.restrictedSurfaceLogCutoffDiff_hasCompactSupport i O E hO hEF ht hs
  have hetaInt : ∀ i : ↑F, Integrable (fun x =>
      p.domainLogRatio U V x * p.intrinsicLaplacian (eta i) x)
        p.hyperbolicArea := fun i =>
    AreaDeficit.Surfaces.DiscCover.integrable_domainLogRatio_mul_intrinsicLaplacian
      p hVU
      (hetaSmooth i) (hetaCompact i) (hetaV i)
  have hcut : D.restrictedCutoff O t - D.restrictedCutoff O s =
      - fun x => ∑ i : ↑F, eta i x := by
    funext x
    simp only [Pi.sub_apply, Pi.neg_apply, restrictedCutoff,
      restrictedSurfaceLogCutoffDiff, Function.comp_apply, cutoff, eta]
    rw [Finset.sum_sub_distrib]
    ring
  have hlap : ∀ x, p.intrinsicLaplacian
      (D.restrictedCutoff O t - D.restrictedCutoff O s) x =
        - ∑ i : ↑F, p.intrinsicLaplacian (eta i) x := by
    intro x
    rw [hcut, p.intrinsicLaplacian_neg
      (ContMDiff.sum fun i _ => hetaSmooth i) x,
      p.intrinsicLaplacian_finsetSum Finset.univ eta
        (fun i _ => hetaSmooth i) x]
  calc
    (∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian
        (D.restrictedCutoff O t - D.restrictedCutoff O s) x
          ∂p.hyperbolicArea) =
        ∫ x, - ∑ i : ↑F, (p.domainLogRatio U V x *
          p.intrinsicLaplacian (eta i) x) ∂p.hyperbolicArea := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hlap x, mul_neg, Finset.mul_sum]
    _ = - ∑ i : ↑F, ∫ x, p.domainLogRatio U V x *
          p.intrinsicLaplacian (eta i) x ∂p.hyperbolicArea := by
      rw [integral_neg, integral_finsetSum Finset.univ]
      exact fun i _ => hetaInt i
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (DiscCover.domainChartGreen_restrictedSurfaceLogCutoffDiff
        hON p hVU D i E hO hEF ht hs (hetaV i)).symm

end FinitePunctureDiscs
end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.domainChartGreen_restrictedSurfaceLogCutoffDiff
