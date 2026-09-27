/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactificationCutoff
import BoundedWanderingDomains.Surfaces.GlobalIntrinsicGreen
import BoundedWanderingDomains.Surfaces.SurfaceChartPartition
import BoundedWanderingDomains.CutoffEndLimits

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

/-- Although a cutoff centred at a deleted compactification point need not
itself have compact support, its intrinsic Laplacian is supported in the
compact transition annulus. -/
theorem DiscCover.restrictedSurfaceLogCutoff_intrinsicLaplacian_hasCompactSupport
    {O : TopologicalSpace.Opens X} (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    (p : DiscCover O) (D : RiemannDynamics.CoordDisk X) {t : ℝ}
    (ht : 0 < t) (hrt : -Real.log D.radius < t)
    (hball : ball (chartAt ℂ D.center D.center) D.radius \
      {chartAt ℂ D.center D.center} ⊆
        ((chartAt ℂ D.center).subtypeRestr hON).target) :
    HasCompactSupport
      (p.intrinsicLaplacian (restrictedSurfaceLogCutoff D O t)) := by
  let cX := chartAt ℂ D.center
  let c := cX.subtypeRestr hON
  let v := restrictedSurfaceLogCutoff D O t
  let w := AreaDeficit.logCutoff (chartAt ℂ D.center D.center) (-2 * t) (-t)
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    mdifferentiableOn_subtypeRestr hON
      (mdifferentiable_chart (I := 𝓘(ℂ)) D.center).1
  have hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v :=
    restrictedSurfaceLogCutoff_contMDiff D O ht hrt.le
  have hvsource : tsupport (p.intrinsicLaplacian v) ⊆ c.source :=
    (p.tsupport_intrinsicLaplacian_subset v).trans <| by
      have hsub : tsupport v ⊆
          (Subtype.val : O → X) ⁻¹' cX.source :=
        (tsupport_comp_subset_preimage (surfaceLogCutoff D t)
          continuous_subtype_val).trans (preimage_mono <| by
          intro x hx
          exact closedCarrier_subset_chartSource D
            (surfaceLogCutoff_tsupport_subset_closedCarrier D ht hrt.le hx))
      simpa only [c, cX, OpenPartialHomeomorph.subtypeRestr_source] using hsub
  have hwlocal : ∀ z ∈ c.target, Δ w z = Δ (v ∘ c.symm) z := by
    intro z hz
    have heq : v ∘ c.symm =ᶠ[𝓝 z] w := by
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      have hyX : y ∈ cX.target := cX.subtypeRestr_target_subset hON hy
      have hsymm := cX.subtypeRestr_symm_apply hON hy
      have hsymm' : (((c.symm y : O) : X)) = cX.symm y := by
        simpa only [c, cX, Function.comp_apply] using hsymm
      have hzero := congrFun (chartZeroExtensionIn_surfaceLogCutoff D ht hrt.le) y
      rw [chartZeroExtensionIn_eq hyX] at hzero
      change surfaceLogCutoff D t (((c.symm y : O) : X)) = w y
      rw [hsymm']
      exact hzero
    exact (laplacian_congr_nhds heq).eq_of_nhds.symm
  have hwsupport : tsupport (Δ w) ⊆ c.target := by
    intro z hz
    obtain ⟨hzlower, hzupper⟩ :=
      AreaDeficit.logCutoff_laplacian_tsupport (by linarith) hz
    apply hball
    constructor
    · rw [mem_ball, dist_eq_norm]
      calc
        ‖z - chartAt ℂ D.center D.center‖ ≤ Real.exp (-t) := hzupper
        _ < D.radius := by
          rw [← Real.exp_log D.radius_pos]
          exact Real.exp_lt_exp.mpr (by linarith)
    · rw [mem_singleton_iff]
      intro hza
      rw [hza, sub_self, norm_zero] at hzlower
      exact (not_le_of_gt (Real.exp_pos _)) hzlower
  have hwcompact : IsCompact (tsupport (Δ w)) :=
    AreaDeficit.laplacian_hasCompactSupport
      (AreaDeficit.logCutoff_hasCompactSupport _ (by linarith))
  have hK : IsCompact (c.symm '' tsupport (Δ w)) :=
    hwcompact.image_of_continuousOn (c.symm.continuousOn.mono hwsupport)
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hxs : x ∈ c.source := hvsource (subset_closure hx)
  have hlap := p.intrinsicLaplacian_eq_in_chart_of_contMDiff hc hv hxs
  have hnonzero : Δ (v ∘ c.symm) (c x) ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hlap
    exact hx hlap
  have hct : c x ∈ c.target := c.map_source hxs
  refine ⟨c x, subset_closure ?_, c.left_inv hxs⟩
  change Δ w (c x) ≠ 0
  rw [hwlocal (c x) hct]
  exact hnonzero

/-- The intrinsic Laplacian of a restricted end cutoff avoids every centre
in its pairwise-disjoint ambient family. -/
theorem DiscCover.tsupport_intrinsicLaplacian_restrictedSurfaceLogCutoff_subset
    {O : TopologicalSpace.Opens X} [MeasurableSpace O] [BorelSpace O]
    (p : DiscCover O) {F : Finset X} (D : FinitePunctureDiscs F)
    {t : ℝ} (ht : D.Admissible t) (i : ↑F) :
    tsupport (p.intrinsicLaplacian
      (restrictedSurfaceLogCutoff (D.disc i) O t)) ⊆
        (Subtype.val : O → X) ⁻¹' ((↑F : Set X)ᶜ) := by
  intro x hx hxF
  let j : ↑F := ⟨(x : X), hxF⟩
  by_cases hji : j = i
  · have hxi : (x : X) = (i : X) := congrArg Subtype.val hji
    have hone := surfaceLogCutoff_eventuallyEq_one_center (D.disc i) ht.1
    have honeO : restrictedSurfaceLogCutoff (D.disc i) O t =ᶠ[𝓝 x]
        fun _ => (1 : ℝ) := by
      have hto : Tendsto (Subtype.val : O → X) (𝓝 x) (𝓝 (D.disc i).center) := by
        rw [D.center i, ← hxi]
        exact continuousAt_subtype_val
      filter_upwards [hto.eventually hone] with y hy
      exact hy
    have hzero : (restrictedSurfaceLogCutoff (D.disc i) O t -
        fun _ => (1 : ℝ)) =ᶠ[𝓝 x] 0 := by
      filter_upwards [honeO] with y hy
      simp [hy]
    have hnot : x ∉ tsupport
        (restrictedSurfaceLogCutoff (D.disc i) O t -
          fun _ => (1 : ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mpr hzero
    have hsmooth := restrictedSurfaceLogCutoff_contMDiff
      (D.disc i) O ht.1 (ht.2 i)
    have hlap : p.intrinsicLaplacian
        (restrictedSurfaceLogCutoff (D.disc i) O t - fun _ => (1 : ℝ)) =
        p.intrinsicLaplacian (restrictedSurfaceLogCutoff (D.disc i) O t) := by
      funext y
      rw [p.intrinsicLaplacian_sub hsmooth contMDiff_const y,
        p.intrinsicLaplacian_const]
      ring
    have hx' : x ∈ tsupport (p.intrinsicLaplacian
        (restrictedSurfaceLogCutoff (D.disc i) O t -
          fun _ => (1 : ℝ))) := by
      simpa only [hlap] using hx
    exact hnot (p.tsupport_intrinsicLaplacian_subset _ hx')
  · have hxj : (x : X) ∈ (D.disc j).closedCarrier := by
      rw [show (x : X) = (j : X) from rfl, ← D.center j]
      refine ⟨chartAt ℂ (D.disc j).center (D.disc j).center, ?_, ?_⟩
      · simpa only [mem_closedBall, dist_self] using (D.disc j).radius_pos.le
      · exact (chartAt ℂ (D.disc j).center).left_inv
          (mem_chart_source ℂ (D.disc j).center)
    have hxi : (x : X) ∉ (D.disc i).closedCarrier := by
      intro hxi
      exact Set.disjoint_left.mp
        (D.pairwise (mem_univ j) (mem_univ i) hji) hxj hxi
    have hxeta : x ∉ tsupport
        (restrictedSurfaceLogCutoff (D.disc i) O t) := by
      intro h
      have h' : (x : X) ∈ tsupport (surfaceLogCutoff (D.disc i) t) :=
        (tsupport_comp_subset_preimage _ continuous_subtype_val) h
      exact hxi (surfaceLogCutoff_tsupport_subset_closedCarrier
        (D.disc i) ht.1 (ht.2 i) h')
    exact hxeta (p.tsupport_intrinsicLaplacian_subset _ hx)

/-- A single end cutoff may fail to have compact support after its centre is
deleted, but its intrinsic Laplacian is compactly supported in the transition
annulus and its Green pairing is still the planar logarithmic pairing. -/
theorem DiscCover.domainChartGreen_restrictedSurfaceLogCutoff
    {O : TopologicalSpace.Opens X} (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    (p : DiscCover O) {U V : TopologicalSpace.Opens O} (hVU : V ≤ U)
    (D : RiemannDynamics.CoordDisk X) {t : ℝ}
    (ht : 0 < t) (hrt : -Real.log D.radius < t)
    (hball : ball (chartAt ℂ D.center D.center) D.radius \
      {chartAt ℂ D.center D.center} ⊆
        ((chartAt ℂ D.center).subtypeRestr hON).target)
    (hV : tsupport (p.intrinsicLaplacian
      (restrictedSurfaceLogCutoff D O t)) ⊆ V) :
    (∫ z, p.domainChartLogRatio U V
        ((chartAt ℂ D.center).subtypeRestr hON) z *
      Δ (AreaDeficit.logCutoff
        (chartAt ℂ D.center D.center) (-2 * t) (-t)) z) =
      ∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian
        (restrictedSurfaceLogCutoff D O t) x ∂p.hyperbolicArea := by
  let cX := chartAt ℂ D.center
  let c := cX.subtypeRestr hON
  let v := restrictedSurfaceLogCutoff D O t
  let w := AreaDeficit.logCutoff (chartAt ℂ D.center D.center) (-2 * t) (-t)
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    mdifferentiableOn_subtypeRestr hON
      (mdifferentiable_chart (I := 𝓘(ℂ)) D.center).1
  have hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v :=
    restrictedSurfaceLogCutoff_contMDiff D O ht hrt.le
  have hvsource : tsupport (p.intrinsicLaplacian v) ⊆ c.source :=
    (p.tsupport_intrinsicLaplacian_subset v).trans <| by
      have hsub : tsupport v ⊆
          (Subtype.val : O → X) ⁻¹' cX.source :=
        (tsupport_comp_subset_preimage (surfaceLogCutoff D t)
          continuous_subtype_val).trans (preimage_mono <| by
          intro x hx
          exact closedCarrier_subset_chartSource D
            (surfaceLogCutoff_tsupport_subset_closedCarrier D ht hrt.le hx))
      simpa only [c, cX, OpenPartialHomeomorph.subtypeRestr_source] using hsub
  have hwlocal : ∀ z ∈ c.target, Δ w z = Δ (v ∘ c.symm) z := by
    intro z hz
    have heq : v ∘ c.symm =ᶠ[𝓝 z] w := by
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      have hyX : y ∈ cX.target := cX.subtypeRestr_target_subset hON hy
      have hsymm := cX.subtypeRestr_symm_apply hON hy
      have hsymm' : (((c.symm y : O) : X)) = cX.symm y := by
        simpa only [c, cX, Function.comp_apply] using hsymm
      have hzero := congrFun (chartZeroExtensionIn_surfaceLogCutoff D ht hrt.le) y
      rw [chartZeroExtensionIn_eq hyX] at hzero
      change surfaceLogCutoff D t (((c.symm y : O) : X)) = w y
      rw [hsymm']
      exact hzero
    exact (laplacian_congr_nhds heq).eq_of_nhds.symm
  have hwsupport : tsupport (Δ w) ⊆ c.target := by
    intro z hz
    obtain ⟨hzlower, hzupper⟩ :=
      AreaDeficit.logCutoff_laplacian_tsupport (by linarith) hz
    apply hball
    constructor
    · rw [mem_ball, dist_eq_norm]
      calc
        ‖z - chartAt ℂ D.center D.center‖ ≤ Real.exp (-t) := hzupper
        _ < D.radius := by
          rw [← Real.exp_log D.radius_pos]
          exact Real.exp_lt_exp.mpr (by linarith)
    · rw [mem_singleton_iff]
      intro hza
      rw [hza, sub_self, norm_zero] at hzlower
      exact (not_le_of_gt (Real.exp_pos _)) hzlower
  have hLcompact : HasCompactSupport (p.intrinsicLaplacian v) :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.restrictedSurfaceLogCutoff_intrinsicLaplacian_hasCompactSupport
      hON p D ht hrt hball
  have hint :=
    p.integrable_domainLogRatio_mul_intrinsicLaplacian_of_laplacian_compact
      hVU hv hLcompact hV
  exact p.domainChartLaplacianIntegral_eq_intrinsic hVU hc hv hvsource hV
    hwlocal hwsupport hint

/-- The intrinsic Green pairing of a compactification cutoff is the negative
sum of its raw planar end pairings.  This version does not normalize at a
fixed cutoff, so its bound is uniform in the puncture stage. -/
theorem DiscCover.intrinsicGreen_restrictedCutoff
    {O : TopologicalSpace.Opens X} (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    (p : DiscCover O) {U V : TopologicalSpace.Opens O} (hVU : V ≤ U)
    {F : Finset X} (D : FinitePunctureDiscs F) {t : ℝ}
    (ht : D.Admissible t)
    (hrt : ∀ i : ↑F, -Real.log (D.disc i).radius < t)
    (hball : ∀ i : ↑F,
      ball (chartAt ℂ (D.disc i).center (D.disc i).center)
          (D.disc i).radius \
        {chartAt ℂ (D.disc i).center (D.disc i).center} ⊆
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON).target)
    (hetaV : ∀ i : ↑F, tsupport (p.intrinsicLaplacian
      (restrictedSurfaceLogCutoff (D.disc i) O t)) ⊆ V) :
    (∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian
        (D.restrictedCutoff O t) x ∂p.hyperbolicArea) =
      - ∑ i : ↑F, ∫ z,
        p.domainChartLogRatio U V
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
        Δ (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * t) (-t)) z := by
  let eta : ↑F → O → ℝ := fun i =>
    restrictedSurfaceLogCutoff (D.disc i) O t
  have hetaSmooth : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (eta i) :=
    fun i => restrictedSurfaceLogCutoff_contMDiff (D.disc i) O
      ht.1 (ht.2 i)
  have hetaCompactLap : ∀ i, HasCompactSupport
      (p.intrinsicLaplacian (eta i)) := fun i =>
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.restrictedSurfaceLogCutoff_intrinsicLaplacian_hasCompactSupport
      hON p (D.disc i) ht.1 (hrt i) (hball i)
  have hetaInt : ∀ i : ↑F, Integrable (fun x =>
      p.domainLogRatio U V x * p.intrinsicLaplacian (eta i) x)
        p.hyperbolicArea := fun i =>
    p.integrable_domainLogRatio_mul_intrinsicLaplacian_of_laplacian_compact
      hVU (hetaSmooth i) (hetaCompactLap i) (hetaV i)
  have hlap : ∀ x, p.intrinsicLaplacian (D.restrictedCutoff O t) x =
      - ∑ i : ↑F, p.intrinsicLaplacian (eta i) x := by
    intro x
    rw [show D.restrictedCutoff O t = (fun _ => (1 : ℝ)) -
        (fun y => ∑ i : ↑F, eta i y) by rfl,
      p.intrinsicLaplacian_sub contMDiff_const
        (ContMDiff.sum fun i _ => hetaSmooth i) x,
      p.intrinsicLaplacian_const,
      p.intrinsicLaplacian_finsetSum Finset.univ eta
        (fun i _ => hetaSmooth i) x]
    simp
  calc
    (∫ x, p.domainLogRatio U V x * p.intrinsicLaplacian
        (D.restrictedCutoff O t) x ∂p.hyperbolicArea) =
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
      exact (AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.domainChartGreen_restrictedSurfaceLogCutoff
        hON p hVU (D.disc i) ht.1 (hrt i) (hball i) (hetaV i)).symm

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




