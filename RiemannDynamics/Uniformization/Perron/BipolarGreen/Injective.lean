/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.DipoleMap

/-!
# Bipolar Green: injectivity of the dipole map

`injective_bipolar_map`: on a surface carrying no Green's function at any
point, the dipole map is injective, by the Blaschke comparison against the
extremal property of the piece Green's functions.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

/-- **Injectivity of the dipole map** on a surface carrying no Green's function at
any point, by the Blaschke comparison against the extremal property of the piece
Green's functions. -/
theorem injective_bipolar_map [SimplyConnectedSpace M]
    [SecondCountableTopology M] (hnon : ∀ p₀ : M, ¬ HasGreenFunction p₀)
    {p₁ p₂ : M} (hne : p₁ ≠ p₂) {G : M → ℝ} {φ : M → ℂ̂}
    (hpole₂ : ∃ r > 0, ball (chartAt ℂ p₂ p₂) r ⊆ (chartAt ℂ p₂).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₂ p₂) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₂ p₂) r \ {chartAt ℂ p₂ p₂},
          h w = G ((chartAt ℂ p₂).symm w) - Real.log ‖w - chartAt ℂ p₂ p₂‖)
    (hbdd : ∃ C : ℝ, ∃ V₁ ∈ 𝓝 p₁, ∃ V₂ ∈ 𝓝 p₂, IsCompact (closure V₁) ∧
      IsCompact (closure V₂) ∧ ∀ x ∉ V₁ ∪ V₂, |G x| ≤ C)
    (hφ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ) (h₁ : φ p₁ = ((0 : ℂ) : ℂ̂))
    (h₂ : φ p₂ = OnePoint.infty)
    (habs : ∀ x : M, x ≠ p₁ → x ≠ p₂ →
      ∃ w : ℂ, φ x = (w : ℂ̂) ∧ ‖w‖ = Real.exp (-(G x))) :
    Function.Injective φ := by
  classical
  /- ## Generic brick: `ContMDiffAt` from an analytic source-chart reading. -/
  have hbuild : ∀ (f : M → ℂ) (x : M),
      AnalyticAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
    intro f x hf
    have hb1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
        :=
      contMDiffAt_iff_contDiffAt.mpr hf.contDiffAt
    have hb2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x)) x :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_source ℂ x)
    refine (hb1.comp x hb2).congr_of_eventuallyEq ?_
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]
  /- ## Generic brick: reading a sphere-valued map through a target chart. -/
  have hread : ∀ f : M → ℂ̂, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ∀ e : OpenPartialHomeomorph ℂ̂ ℂ, e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ →
      ∀ (x : M) (w : ℂ), w ∈ (chartAt ℂ x).target →
      f ((chartAt ℂ x).symm w) ∈ e.source →
      AnalyticAt ℂ (fun v ↦ e (f ((chartAt ℂ x).symm v))) w := by
    intro f hf e hemax x w hw hsrc
    have hr1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hw
    have hr3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) (f ((chartAt ℂ x).symm w)) :=
      contMDiffAt_of_mem_maximalAtlas hemax hsrc
    exact (contMDiffAt_iff_contDiffAt.mp
      ((hr3.comp _ hf.contMDiffAt).comp w hr1)).analyticAt
  /- ## Sphere-chart bookkeeping. -/
  have hfinmax : sphereChartFinite ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.chart_mem_maximalAtlas ((0 : ℂ) : ℂ̂)
  have hinfmax : sphereChartInfty ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.chart_mem_maximalAtlas (OnePoint.infty : ℂ̂)
  have hfinsrc : ∀ z : ℂ̂, z ≠ OnePoint.infty → z ∈ sphereChartFinite.source := by
    intro z hz
    rw [sphereChartFinite_source]
    exact hz
  have hinfsrc : ∀ z : ℂ̂, z ≠ ((0 : ℂ) : ℂ̂) → z ∈ sphereChartInfty.source := by
    intro z hz
    rw [sphereChartInfty_source]
    exact hz
  have hinfval : ∀ b : ℂ, b ≠ 0 → sphereChartInfty ((b : ℂ̂)) = b⁻¹ := by
    intro b hb
    rw [sphereChartInfty_apply, inversionGL_smul_coe, ite_eq_right hb, sphereChartFinite_coe]
  have hinfval0 : sphereChartInfty (OnePoint.infty : ℂ̂) = 0 := by
    rw [sphereChartInfty_apply, inversionGL_smul_infty, sphereChartFinite_coe]
  /- ## Plane-level transfer of subharmonicity along a pointwise equality. -/
  have htransfer : ∀ (F₁ F₂ : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F₁ U → W ⊆ U
      →
      Set.EqOn F₁ F₂ W → SubharmonicOn F₂ W := by
    intro F₁ F₂ U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro c hc ρc hρc hb
    have ht1 : F₂ c = F₁ c := (hFG hc).symm
    have ht2 : Real.circleAverage F₁ c ρc = Real.circleAverage F₂ c ρc := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρc] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [ht1, ← ht2]
    exact hF.2 c (hWU hc) ρc hρc (hb.trans hWU)
  /- ## Surface-level: subharmonicity at a point respects equality near the point. -/
  have hcongM : ∀ (F₁ F₂ : M → ℝ) (x : M) (O : Set M), IsOpen O → x ∈ O →
      Set.EqOn F₁ F₂ O → MSubharmonicAt F₁ x → MSubharmonicAt F₂ x := by
    intro F₁ F₂ x O hO hxO hFG hF
    obtain ⟨r, hr, -, hsub⟩ := hF
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm hO
    have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O := by
      refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
      exact hxO
    obtain ⟨ρc, hρc, hρsubc⟩ := Metric.isOpen_iff.1 (isOpen_ball.inter hopen)
      (chartAt ℂ x x) ⟨mem_ball_self hr, hmem⟩
    refine ⟨ρc, hρc, fun w hw ↦ ((hρsubc hw).2).1, ?_⟩
    refine htransfer _ _ _ _ hsub (fun w hw ↦ (hρsubc hw).1) ?_
    intro w hw
    exact hFG ((hρsubc hw).2).2
  /- ## Sums of subharmonic functions are subharmonic. -/
  have haddM : ∀ (F₁ F₂ : M → ℝ) (x : M), MSubharmonicAt F₁ x → MSubharmonicAt F₂ x
      →
      MSubharmonicAt (fun y ↦ F₁ y + F₂ y) x := by
    intro F₁ F₂ x hF hG2
    obtain ⟨r₁, hr₁, hb₁, hs₁⟩ := hF
    obtain ⟨r₂, hr₂, -, hs₂⟩ := hG2
    have hmono : ∀ (f : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn f U → V ⊆ U →
        SubharmonicOn f V := fun f U V hf hVU ↦
      ⟨hf.1.mono hVU, fun c hc ρc hρc hball ↦ hf.2 c (hVU hc) ρc hρc (hball.trans hVU)⟩
    have hs₁' := hmono _ _ _ hs₁ (ball_subset_ball (min_le_left r₁ r₂))
    have hs₂' := hmono _ _ _ hs₂ (ball_subset_ball (min_le_right r₁ r₂))
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (ball_subset_ball (min_le_left r₁ r₂)).trans hb₁, ?_, ?_⟩
    · exact hs₁'.1.add hs₂'.1
    · intro c hc ρc hρc hb
      have hsph : sphere c ρc ⊆ ball (chartAt ℂ x x) (min r₁ r₂) :=
        sphere_subset_closedBall.trans hb
      have hci₁ : CircleIntegrable (F₁ ∘ (chartAt ℂ x).symm) c ρc :=
        (hs₁'.1.mono hsph).circleIntegrable hρc.le
      have hci₂ : CircleIntegrable (F₂ ∘ (chartAt ℂ x).symm) c ρc :=
        (hs₂'.1.mono hsph).circleIntegrable hρc.le
      have havg := Real.circleAverage_fun_add hci₁ hci₂
      have hp₁' := hs₁'.2 c hc ρc hρc hb
      have hp₂' := hs₂'.2 c hc ρc hρc hb
      calc ((fun y ↦ F₁ y + F₂ y) ∘ (chartAt ℂ x).symm) c
          = (F₁ ∘ (chartAt ℂ x).symm) c + (F₂ ∘ (chartAt ℂ x).symm) c := rfl
        _ ≤ Real.circleAverage (F₁ ∘ (chartAt ℂ x).symm) c ρc
            + Real.circleAverage (F₂ ∘ (chartAt ℂ x).symm) c ρc := add_le_add hp₁' hp₂'
        _ = Real.circleAverage
            (fun w ↦ (F₁ ∘ (chartAt ℂ x).symm) w + (F₂ ∘ (chartAt ℂ x).symm) w) c ρc
                :=
            havg.symm
        _ = Real.circleAverage ((fun y ↦ F₁ y + F₂ y) ∘ (chartAt ℂ x).symm) c ρc := rfl
  /- ## The log-modulus of a nonvanishing holomorphic function is harmonic. -/
  have hlogM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M,
      Ψ x ≠ 0 →
      MHarmonicAt (fun y ↦ Real.log ‖Ψ y‖) x := by
    intro Ψ hΨm x hx
    have hl1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have hl2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) hl1
    have hl3 : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_iff_contDiffAt.mp hl2).analyticAt
    have hl4 : (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hx
    exact hl3.harmonicAt_log_norm hl4
  /- ## The chart reading of a holomorphic function is analytic at the center. -/
  have hreadM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M,
      AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
    intro Ψ hΨm x
    have hm1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have hm2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) hm1
    exact (contMDiffAt_iff_contDiffAt.mp hm2).analyticAt
  /- ## The singleton `{0}` is not open in the plane. -/
  have hnotopen0 : ¬ IsOpen ({(0 : ℂ)} : Set ℂ) := by
    intro hcon
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcon 0 rfl
    have hn1 : (↑(ε / 2) : ℂ) ∈ ball (0 : ℂ) ε := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    have hn2 := hball hn1
    rw [Set.mem_singleton_iff, Complex.ofReal_eq_zero] at hn2
    linarith
  /- ## Zeros of a nonconstant holomorphic function are isolated. -/
  have hisoM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → (∃ y₀,
      Ψ y₀ ≠ 0) →
      ∀ z : M, Ψ z = 0 → ∀ᶠ y in 𝓝[≠] z, Ψ y ≠ 0 := by
    intro Ψ hΨm hex z hz
    obtain ⟨y₀, hy₀⟩ := hex
    have hzsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    rcases (hreadM Ψ hΨm z).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      have hop : IsOpenMap Ψ := by
        refine isOpenMap_of_contMDiff_of_not_const (fun y ↦ hΨm y) ?_
        rintro ⟨c, hc⟩
        rw [hc z] at hz
        rw [hc y₀, hz] at hy₀
        exact hy₀ rfl
      have hi2 : ∀ᶠ y in 𝓝 z, Ψ y = 0 := by
        have hc : ContinuousAt (chartAt ℂ z) z := (chartAt ℂ z).continuousAt hzsrc
        filter_upwards [hc.eventually hcase,
          (chartAt ℂ z).open_source.mem_nhds hzsrc] with y h1y hsy
        have hyy : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := h1y
        rwa [(chartAt ℂ z).left_inv hsy] at hyy
      obtain ⟨O, hOsub, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp hi2
      have himg : Ψ '' O = {0} := by
        apply Set.Subset.antisymm
        · rintro w ⟨y, hy, rfl⟩
          exact hOsub hy
        · rintro w hw
          rw [Set.mem_singleton_iff] at hw
          exact ⟨z, hzO, by rw [hw, hz]⟩
      have hi3 := hop O hOopen
      rw [himg] at hi3
      exact hnotopen0 hi3
    · have htend : Tendsto (chartAt ℂ z) (𝓝[≠] z) (𝓝[≠] (chartAt ℂ z z)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · exact ((chartAt ℂ z).continuousAt hzsrc).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ z).open_source.mem_nhds hzsrc),
            self_mem_nhdsWithin] with y hys hyz
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hyz ((chartAt ℂ z).injOn hys hzsrc hcon)
      filter_upwards [htend.eventually hcase,
        nhdsWithin_le_nhds ((chartAt ℂ z).open_source.mem_nhds hzsrc)] with y h1 hys
      intro hcon
      apply h1
      have hyy : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := by
        rw [(chartAt ℂ z).left_inv hys]
        exact hcon
      exact hyy
  /- ## dslope toolkit: evaluation, punctured differentiability, nonvanishing. -/
  have hdslope_eval : ∀ (F : ℂ → ℂ) (c w : ℂ), F c = 0 → w ≠ c →
      dslope F c w = F w / (w - c) := by
    intro F c w hFc hwc
    rw [dslope_of_ne F hwc, slope_def_field, hFc, sub_zero]
  have hdslope_diff : ∀ (F : ℂ → ℂ) (c w : ℂ), F c = 0 → w ≠ c → AnalyticAt ℂ F w
      →
      DifferentiableAt ℂ (dslope F c) w := by
    intro F c w hFc hwc hFan
    have hEq : (fun v ↦ F v / (v - c)) =ᶠ[𝓝 w] dslope F c := by
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hwc)] with v hv
      have hvc : v ≠ c := Set.mem_compl_singleton_iff.mp hv
      rw [dslope_of_ne F hvc, slope_def_field, hFc, sub_zero]
    have hq : DifferentiableAt ℂ (fun v ↦ F v / (v - c)) w :=
      DifferentiableAt.div hFan.differentiableAt
        (differentiableAt_id.sub (differentiableAt_const c)) (sub_ne_zero_of_ne hwc)
    exact hq.congr_of_eventuallyEq hEq.symm
  have hdslope_ne : ∀ (F : ℂ → ℂ) (c w : ℂ), F c = 0 → w ≠ c → F w ≠ 0 →
      dslope F c w ≠ 0 := by
    intro F c w hFc hwc hFw
    rw [hdslope_eval F c w hFc hwc]
    exact div_ne_zero hFw (sub_ne_zero_of_ne hwc)
  /- ## A zero whose modulus is exactly first order has nonzero derivative. -/
  have hderiv_ne : ∀ (F : ℂ → ℂ) (c : ℂ) (rF : ℝ) (hF : ℂ → ℝ), 0 < rF → F c = 0
      →
      (∀ w ∈ ball c rF, AnalyticAt ℂ F w) → ContinuousAt hF c →
      (∀ w ∈ ball c rF, w ≠ c → ‖F w‖ = Real.exp (hF w) * ‖w - c‖) →
      deriv F c ≠ 0 := by
    intro F c rF hF hrF hFc hFan hhc hFnorm hd0
    have hdiff : DifferentiableAt ℂ F c := (hFan c (mem_ball_self hrF)).differentiableAt
    have hcont : ContinuousAt (dslope F c) c := continuousAt_dslope_same.mpr hdiff
    have hT1 : Tendsto (fun w ↦ ‖dslope F c w‖) (𝓝[≠] c) (𝓝 0) := by
      have hu1 : Tendsto (dslope F c) (𝓝 c) (𝓝 (dslope F c c)) := hcont
      rw [dslope_same, hd0] at hu1
      have hu2 := hu1.norm
      rw [norm_zero] at hu2
      exact hu2.mono_left nhdsWithin_le_nhds
    have hT2 : Tendsto (fun w ↦ Real.exp (hF w)) (𝓝[≠] c) (𝓝 (Real.exp (hF c))) :=
      Filter.Tendsto.mono_left (Real.continuous_exp.continuousAt.comp hhc)
        nhdsWithin_le_nhds
    have hEq : (fun w ↦ ‖dslope F c w‖) =ᶠ[𝓝[≠] c] fun w ↦ Real.exp (hF w) := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c hrF), self_mem_nhdsWithin]
        with w hwb hwm
      have hwc : w ≠ c := Set.mem_compl_singleton_iff.mp hwm
      rw [dslope_of_ne F hwc, slope_def_field, hFc, sub_zero, norm_div,
        hFnorm w hwb hwc, mul_div_assoc,
        div_self (norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hwc)), mul_one]
    have hun := tendsto_nhds_unique (hT1.congr' hEq) hT2
    exact (Real.exp_pos (hF c)).ne' hun.symm
  /- ## The special values `0` and `∞` are attained only at the poles. -/
  have hzero : ∀ x : M, φ x = ((0 : ℂ) : ℂ̂) → x = p₁ := by
    intro x hx
    by_contra hxp₁
    by_cases hxp₂ : x = p₂
    · rw [hxp₂, h₂] at hx
      exact OnePoint.infty_ne_coe 0 hx
    · obtain ⟨w, hw, hwn⟩ := habs x hxp₁ hxp₂
      rw [hx] at hw
      have hw0 : (0 : ℂ) = w := OnePoint.coe_eq_coe.mp hw
      rw [← hw0, norm_zero] at hwn
      exact (Real.exp_pos _).ne' hwn.symm
  have hinfty : ∀ x : M, φ x = OnePoint.infty → x = p₂ := by
    intro x hx
    by_contra hxp₂
    by_cases hxp₁ : x = p₁
    · rw [hxp₁, h₁] at hx
      exact OnePoint.coe_ne_infty 0 hx
    · obtain ⟨w, hw, -⟩ := habs x hxp₁ hxp₂
      rw [hx] at hw
      exact OnePoint.infty_ne_coe w hw
  /- ## Fix a collision and dispose of the pole values. -/
  intro q q' hcol
  by_contra hqq'
  by_cases hq0 : φ q = ((0 : ℂ) : ℂ̂)
  · have hcz : φ q' = ((0 : ℂ) : ℂ̂) := by rw [← hcol]; exact hq0
    exact hqq' ((hzero q hq0).trans (hzero q' hcz).symm)
  by_cases hqi : φ q = OnePoint.infty
  · have hci : φ q' = OnePoint.infty := by rw [← hcol]; exact hqi
    exact hqq' ((hinfty q hqi).trans (hinfty q' hci).symm)
  have hqp₁ : q ≠ p₁ := fun h ↦ hq0 (by rw [h, h₁])
  have hqp₂ : q ≠ p₂ := fun h ↦ hqi (by rw [h, h₂])
  obtain ⟨w₀, hφq, hw₀n⟩ := habs q hqp₁ hqp₂
  have hw₀0 : w₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw₀n
    exact (Real.exp_pos _).ne' hw₀n.symm
  have hφq' : φ q' = (w₀ : ℂ̂) := by rw [← hcol]; exact hφq
  have hq'p₁ : q' ≠ p₁ := by
    intro h
    rw [h, h₁] at hφq'
    exact hw₀0 (OnePoint.coe_eq_coe.mp hφq'.symm)
  have hq'p₂ : q' ≠ p₂ := by
    intro h
    rw [h, h₂] at hφq'
    exact OnePoint.infty_ne_coe w₀ hφq'
  /- ## A fresh coordinate disk centered at `p₁` avoiding `q'` and `p₂`. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₀def
  have hp₁src : p₁ ∈ e₀.source := mem_chart_source ℂ p₁
  have hUopen : IsOpen (e₀.target ∩ ⇑e₀.symm ⁻¹' ({q'}ᶜ ∩ {p₂}ᶜ)) :=
    e₀.isOpen_inter_preimage_symm (isOpen_compl_singleton.inter isOpen_compl_singleton)
  have hp₁U : e₀ p₁ ∈ e₀.target ∩ ⇑e₀.symm ⁻¹' ({q'}ᶜ ∩ {p₂}ᶜ) := by
    refine ⟨e₀.map_source hp₁src, ?_⟩
    rw [Set.mem_preimage, e₀.left_inv hp₁src]
    exact ⟨Set.mem_compl_singleton_iff.mpr hq'p₁.symm,
      Set.mem_compl_singleton_iff.mpr hne⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hUopen _ hp₁U
  have hra0 : (0 : ℝ) < εa / 2 := half_pos hεa
  have hrsub : closedBall (e₀ p₁) (εa / 2) ⊆ e₀.target ∩ ⇑e₀.symm ⁻¹' ({q'}ᶜ ∩
      {p₂}ᶜ) :=
    (Metric.closedBall_subset_ball (half_lt_self hεa)).trans hballa
  set D₀ : CoordDisk M := ⟨p₁, εa / 2, hra0, fun w hw ↦ (hrsub hw).1⟩ with hD₀def
  have hD₀avoid : ∀ y ∈ D₀.closedCarrier, y ≠ q' ∧ y ≠ p₂ := by
    rintro y ⟨w, hw, rfl⟩
    have hav := (hrsub hw).2
    rw [Set.mem_preimage] at hav
    exact ⟨Set.mem_compl_singleton_iff.mp hav.1, Set.mem_compl_singleton_iff.mp hav.2⟩
  have hq'D : q' ∉ D₀.closedCarrier := fun hmem ↦ (hD₀avoid q' hmem).1 rfl
  have hp₂D : p₂ ∉ D₀.closedCarrier := fun hmem ↦ (hD₀avoid p₂ hmem).2 rfl
  /- ## The second dipole at the pole pair `(q', p₂)`. -/
  obtain ⟨G', hG'h, hpole₁', hpole₂', hbdd'⟩ := exists_bipolar_green D₀ hq'D hp₂D hq'p₂
  obtain ⟨φ', hφ', hφ'z, hφ'i, habs'⟩ := exists_bipolar_map hq'p₂ hG'h hpole₁' hpole₂'
  have hinfty' : ∀ x : M, φ' x = OnePoint.infty → x = p₂ := by
    intro x hx
    by_contra hxp₂
    by_cases hxq' : x = q'
    · rw [hxq', hφ'z] at hx
      exact OnePoint.coe_ne_infty 0 hx
    · obtain ⟨u, hu, -⟩ := habs' x hxq' hxp₂
      rw [hx] at hu
      exact OnePoint.infty_ne_coe u hu
  have hφdat : ∀ x : M, x ≠ p₁ → x ≠ p₂ → ∃ u : ℂ, φ x = (u : ℂ̂) ∧ u ≠ 0
      ∧
      ‖u‖ = Real.exp (-(G x)) := by
    intro x hx1 hx2
    obtain ⟨u, hu, hun⟩ := habs x hx1 hx2
    refine ⟨u, hu, ?_, hun⟩
    intro h
    rw [h, norm_zero] at hun
    exact (Real.exp_pos _).ne' hun.symm
  have hφ'dat : ∀ x : M, x ≠ q' → x ≠ p₂ → ∃ u : ℂ, φ' x = (u : ℂ̂) ∧ u ≠ 0
      ∧
      ‖u‖ = Real.exp (-(G' x)) := by
    intro x hx1 hx2
    obtain ⟨u, hu, hun⟩ := habs' x hx1 hx2
    refine ⟨u, hu, ?_, hun⟩
    intro h
    rw [h, norm_zero] at hun
    exact (Real.exp_pos _).ne' hun.symm
  /- ## Chart notation at the two singular points of the ratio. -/
  set χ₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ q' with hχ₁def
  have hq'src : q' ∈ χ₁.source := mem_chart_source ℂ q'
  set c₁ : ℂ := χ₁ q' with hc₁def
  have hsymmc₁ : χ₁.symm c₁ = q' := χ₁.left_inv hq'src
  set χ₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with hχ₂def
  have hp₂src : p₂ ∈ χ₂.source := mem_chart_source ℂ p₂
  set c₂ : ℂ := χ₂ p₂ with hc₂def
  have hsymmc₂ : χ₂.symm c₂ = p₂ := χ₂.left_inv hp₂src
  obtain ⟨r₁, hr₁pos, hr₁sub, ηq, hηqharm, hηqval⟩ := hpole₁'
  obtain ⟨s₁, hs₁pos, hs₁sub, ηp, hηpharm, hηpval⟩ := hpole₂
  /- ## The finite-part ratio `H = (φ − w₀)/φ'` with its removable values. -/
  obtain ⟨g, hgdef⟩ : ∃ f : ℂ → ℂ,
      f = fun w ↦ sphereChartFinite (φ (χ₁.symm w)) - w₀ := ⟨_, rfl⟩
  obtain ⟨g', hg'def⟩ : ∃ f : ℂ → ℂ,
      f = fun w ↦ sphereChartFinite (φ' (χ₁.symm w)) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ f : ℂ → ℂ,
      f = fun w ↦ sphereChartInfty (φ (χ₂.symm w)) := ⟨_, rfl⟩
  obtain ⟨ρ', hρ'def⟩ : ∃ f : ℂ → ℂ,
      f = fun w ↦ sphereChartInfty (φ' (χ₂.symm w)) := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ Hf : M → ℂ, Hf = fun x ↦
      if x = q' then dslope g c₁ c₁ / dslope g' c₁ c₁
      else if x = p₂ then dslope ρ' c₂ c₂ / dslope ρ c₂ c₂
      else (sphereChartFinite (φ x) - w₀) / sphereChartFinite (φ' x) := ⟨_, rfl⟩
  /- ## The two decisive values of `H`. -/
  have hHq : H q = 0 := by
    simp only [hHdef]
    rw [ite_eq_right hqq', ite_eq_right hqp₂, hφq, sphereChartFinite_coe, sub_self, zero_div]
  have hHp₁ : H p₁ ≠ 0 := by
    obtain ⟨u', hu', hu'0, -⟩ := hφ'dat p₁ (Ne.symm hq'p₁) hne
    simp only [hHdef]
    rw [ite_eq_right (Ne.symm hq'p₁), ite_eq_right hne, h₁, sphereChartFinite_coe, hu',
      sphereChartFinite_coe, zero_sub]
    exact div_ne_zero (neg_ne_zero.mpr hw₀0) hu'0
  /- ## Holomorphy of `H` away from the two singular points. -/
  have hHsm_gen : ∀ x : M, x ≠ q' → x ≠ p₂ → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H x := by
    intro x hx1 hx2
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hφfin : φ x ≠ OnePoint.infty := fun h ↦ hx2 (hinfty x h)
    have hφ'fin : φ' x ≠ OnePoint.infty := fun h ↦ hx2 (hinfty' x h)
    obtain ⟨u', hu', hu'0, -⟩ := hφ'dat x hx1 hx2
    have hT : IsOpen ((chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          ({q'}ᶜ ∩ {p₂}ᶜ))) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm
        (((sphereChartFinite.open_source.preimage hφ.continuous).inter
          (sphereChartFinite.open_source.preimage hφ'.continuous)).inter
          (isOpen_compl_singleton.inter isOpen_compl_singleton))
    have hxT : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          ({q'}ᶜ ∩ {p₂}ᶜ)) := by
      refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
      exact ⟨⟨hfinsrc _ hφfin, hfinsrc _ hφ'fin⟩,
        Set.mem_compl_singleton_iff.mpr hx1, Set.mem_compl_singleton_iff.mpr hx2⟩
    obtain ⟨R₀, hR₀def⟩ : ∃ f : ℂ → ℂ, f = fun v ↦
        (sphereChartFinite (φ ((chartAt ℂ x).symm v)) - w₀) /
          sphereChartFinite (φ' ((chartAt ℂ x).symm v)) := ⟨_, rfl⟩
    have hnum : AnalyticAt ℂ (fun v ↦ sphereChartFinite (φ ((chartAt ℂ x).symm v)))
        (chartAt ℂ x x) :=
      hread φ hφ sphereChartFinite hfinmax x _ ((chartAt ℂ x).map_source hxsrc)
        (by rw [(chartAt ℂ x).left_inv hxsrc]; exact hfinsrc _ hφfin)
    have hden : AnalyticAt ℂ (fun v ↦ sphereChartFinite (φ' ((chartAt ℂ x).symm v)))
        (chartAt ℂ x x) :=
      hread φ' hφ' sphereChartFinite hfinmax x _ ((chartAt ℂ x).map_source hxsrc)
        (by rw [(chartAt ℂ x).left_inv hxsrc]; exact hfinsrc _ hφ'fin)
    have hden0 : sphereChartFinite (φ' ((chartAt ℂ x).symm (chartAt ℂ x x))) ≠ 0 := by
      rw [(chartAt ℂ x).left_inv hxsrc, hu', sphereChartFinite_coe]
      exact hu'0
    have hR₀an : AnalyticAt ℂ R₀ (chartAt ℂ x x) := by
      rw [hR₀def]
      exact (hnum.sub analyticAt_const).div hden hden0
    have hHeq : R₀ =ᶠ[𝓝 (chartAt ℂ x x)] H ∘ ⇑(chartAt ℂ x).symm := by
      filter_upwards [hT.mem_nhds hxT] with v hv
      have he1 : (chartAt ℂ x).symm v ≠ q' := Set.mem_compl_singleton_iff.mp hv.2.2.1
      have he2 : (chartAt ℂ x).symm v ≠ p₂ := Set.mem_compl_singleton_iff.mp hv.2.2.2
      simp only [hR₀def, Function.comp_apply, hHdef]
      rw [ite_eq_right he1, ite_eq_right he2]
    exact hbuild H x (hR₀an.congr hHeq)
  /- ## Holomorphy of `H` at `q'` (zero-over-zero removable singularity). -/
  have hHsm_q' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H q' := by
    have hOq' : IsOpen (χ₁.target ∩ ⇑χ₁.symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          {p₂}ᶜ)) :=
      χ₁.isOpen_inter_preimage_symm
        (((sphereChartFinite.open_source.preimage hφ.continuous).inter
          (sphereChartFinite.open_source.preimage hφ'.continuous)).inter
          isOpen_compl_singleton)
    have hc₁mem : c₁ ∈ χ₁.target ∩ ⇑χ₁.symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          {p₂}ᶜ) := by
      refine ⟨χ₁.map_source hq'src, ?_⟩
      rw [Set.mem_preimage, hsymmc₁]
      refine ⟨⟨hfinsrc _ ?_, hfinsrc _ ?_⟩, Set.mem_compl_singleton_iff.mpr hq'p₂⟩
      · rw [hφq']
        exact OnePoint.coe_ne_infty w₀
      · rw [hφ'z]
        exact OnePoint.coe_ne_infty 0
    obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp hOq' _ hc₁mem
    set r : ℝ := min r₁ r₂ with hrdef
    have hr : 0 < r := lt_min hr₁pos hr₂pos
    have hrb₁ : ball c₁ r ⊆ ball c₁ r₁ := ball_subset_ball (min_le_left _ _)
    have hrb₂ : ball c₁ r ⊆ χ₁.target ∩ ⇑χ₁.symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          {p₂}ᶜ) := (ball_subset_ball (min_le_right _ _)).trans hr₂sub
    have hgan : ∀ w ∈ ball c₁ r, AnalyticAt ℂ g w := by
      intro w hw
      have h1 := hread φ hφ sphereChartFinite hfinmax q' w (hrb₂ hw).1 (hrb₂ hw).2.1.1
      simp only [hgdef]
      exact h1.sub analyticAt_const
    have hg'an : ∀ w ∈ ball c₁ r, AnalyticAt ℂ g' w := by
      intro w hw
      have h1 := hread φ' hφ' sphereChartFinite hfinmax q' w (hrb₂ hw).1 (hrb₂ hw).2.1.2
      simp only [hg'def]
      exact h1
    have hg0 : g c₁ = 0 := by
      simp only [hgdef]
      rw [hsymmc₁, hφq', sphereChartFinite_coe, sub_self]
    have hg'0 : g' c₁ = 0 := by
      simp only [hg'def]
      rw [hsymmc₁, hφ'z, sphereChartFinite_coe]
    have hsymm_ne₁ : ∀ w ∈ ball c₁ r, w ≠ c₁ → χ₁.symm w ≠ q' := by
      intro w hw hwc h
      have hwt : w ∈ χ₁.target := (hrb₂ hw).1
      have h2 : χ₁ (χ₁.symm w) = w := χ₁.right_inv hwt
      rw [h] at h2
      exact hwc h2.symm
    have hg'dat : ∀ w ∈ ball c₁ r, w ≠ c₁ →
        g' w ≠ 0 ∧ ‖g' w‖ = Real.exp (-(ηq w)) * ‖w - c₁‖ := by
      intro w hw hwc
      have hnq' : χ₁.symm w ≠ q' := hsymm_ne₁ w hw hwc
      have hnp₂ : χ₁.symm w ≠ p₂ := Set.mem_compl_singleton_iff.mp (hrb₂ hw).2.2
      obtain ⟨u, hu, hu0, hun⟩ := hφ'dat (χ₁.symm w) hnq' hnp₂
      have hval : g' w = u := by
        simp only [hg'def]
        rw [hu, sphereChartFinite_coe]
      have hballm : w ∈ ball c₁ r₁ \ {c₁} :=
        ⟨hrb₁ hw, fun h ↦ hwc (Set.mem_singleton_iff.mp h)⟩
      have hη := hηqval w hballm
      have hGval : -(G' (χ₁.symm w)) = -(ηq w) + Real.log ‖w - c₁‖ := by linarith
      have hpos : 0 < ‖w - c₁‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hwc)
      refine ⟨by rw [hval]; exact hu0, ?_⟩
      rw [hval, hun, hGval, Real.exp_add, Real.exp_log hpos]
    have hg'deriv : deriv g' c₁ ≠ 0 := by
      refine hderiv_ne g' c₁ r (fun w ↦ -(ηq w)) hr hg'0 hg'an ?_
        (fun w hw hwc ↦ (hg'dat w hw hwc).2)
      exact (hηqharm c₁ (mem_ball_self hr₁pos)).1.continuousAt.neg
    obtain ⟨A₁, hA₁def⟩ : ∃ f : ℂ → ℂ,
        f = fun w ↦ dslope g c₁ w / dslope g' c₁ w := ⟨_, rfl⟩
    have hA₁cont : ContinuousAt A₁ c₁ := by
      have hc1 : ContinuousAt (dslope g c₁) c₁ :=
        continuousAt_dslope_same.mpr (hgan c₁ (mem_ball_self hr)).differentiableAt
      have hc2 : ContinuousAt (dslope g' c₁) c₁ :=
        continuousAt_dslope_same.mpr (hg'an c₁ (mem_ball_self hr)).differentiableAt
      have hc3 : dslope g' c₁ c₁ ≠ 0 := by
        rw [dslope_same]
        exact hg'deriv
      simp only [hA₁def]
      exact hc1.div hc2 hc3
    have hA₁diff : ∀ᶠ w in 𝓝[≠] c₁, DifferentiableAt ℂ A₁ w := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c₁ hr), self_mem_nhdsWithin]
        with w hwb hwm
      have hwc : w ≠ c₁ := Set.mem_compl_singleton_iff.mp hwm
      have hd1 := hdslope_diff g c₁ w hg0 hwc (hgan w hwb)
      have hd2 := hdslope_diff g' c₁ w hg'0 hwc (hg'an w hwb)
      have hd3 : dslope g' c₁ w ≠ 0 :=
        hdslope_ne g' c₁ w hg'0 hwc (hg'dat w hwb hwc).1
      simp only [hA₁def]
      exact hd1.div hd2 hd3
    have hA₁an : AnalyticAt ℂ A₁ c₁ :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        hA₁diff hA₁cont
    have hHq'eq : A₁ =ᶠ[𝓝 c₁] H ∘ ⇑χ₁.symm := by
      filter_upwards [ball_mem_nhds c₁ hr] with w hwb
      by_cases hwc : w = c₁
      · subst hwc
        simp only [hA₁def, Function.comp_apply]
        rw [hsymmc₁]
        simp only [hHdef]
        rw [ite_eq_left trivial]
      · have hnq' : χ₁.symm w ≠ q' := hsymm_ne₁ w hwb hwc
        have hnp₂ : χ₁.symm w ≠ p₂ := Set.mem_compl_singleton_iff.mp (hrb₂ hwb).2.2
        simp only [hA₁def, Function.comp_apply, hHdef]
        rw [ite_eq_right hnq', ite_eq_right hnp₂, hdslope_eval g c₁ w hg0 hwc,
          hdslope_eval g' c₁ w hg'0 hwc,
          div_div_div_cancel_right₀ (sub_ne_zero_of_ne hwc)]
        simp only [hgdef, hg'def]
    exact hbuild H q' (hA₁an.congr hHq'eq)
  /- ## Holomorphy of `H` at `p₂` (pole-over-pole removable singularity). -/
  have hHsm_p₂ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H p₂ := by
    have hOp₂ : IsOpen (χ₂.target ∩ ⇑χ₂.symm ⁻¹'
        ((φ ⁻¹' sphereChartInfty.source ∩ φ' ⁻¹' sphereChartInfty.source) ∩
          ({p₁}ᶜ ∩ {q'}ᶜ))) :=
      χ₂.isOpen_inter_preimage_symm
        (((sphereChartInfty.open_source.preimage hφ.continuous).inter
          (sphereChartInfty.open_source.preimage hφ'.continuous)).inter
          (isOpen_compl_singleton.inter isOpen_compl_singleton))
    have hc₂mem : c₂ ∈ χ₂.target ∩ ⇑χ₂.symm ⁻¹'
        ((φ ⁻¹' sphereChartInfty.source ∩ φ' ⁻¹' sphereChartInfty.source) ∩
          ({p₁}ᶜ ∩ {q'}ᶜ)) := by
      refine ⟨χ₂.map_source hp₂src, ?_⟩
      rw [Set.mem_preimage, hsymmc₂]
      refine ⟨⟨hinfsrc _ ?_, hinfsrc _ ?_⟩, Set.mem_compl_singleton_iff.mpr hne.symm,
        Set.mem_compl_singleton_iff.mpr (Ne.symm hq'p₂)⟩
      · rw [h₂]
        exact OnePoint.infty_ne_coe 0
      · rw [hφ'i]
        exact OnePoint.infty_ne_coe 0
    obtain ⟨s₂, hs₂pos, hs₂sub⟩ := Metric.isOpen_iff.mp hOp₂ _ hc₂mem
    set s : ℝ := min s₁ s₂ with hsdef
    have hs : 0 < s := lt_min hs₁pos hs₂pos
    have hsb₁ : ball c₂ s ⊆ ball c₂ s₁ := ball_subset_ball (min_le_left _ _)
    have hsb₂ : ball c₂ s ⊆ χ₂.target ∩ ⇑χ₂.symm ⁻¹'
        ((φ ⁻¹' sphereChartInfty.source ∩ φ' ⁻¹' sphereChartInfty.source) ∩
          ({p₁}ᶜ ∩ {q'}ᶜ)) := (ball_subset_ball (min_le_right _ _)).trans hs₂sub
    have hρan : ∀ w ∈ ball c₂ s, AnalyticAt ℂ ρ w := by
      intro w hw
      have h1 := hread φ hφ sphereChartInfty hinfmax p₂ w (hsb₂ hw).1 (hsb₂ hw).2.1.1
      simp only [hρdef]
      exact h1
    have hρ'an : ∀ w ∈ ball c₂ s, AnalyticAt ℂ ρ' w := by
      intro w hw
      have h1 := hread φ' hφ' sphereChartInfty hinfmax p₂ w (hsb₂ hw).1 (hsb₂ hw).2.1.2
      simp only [hρ'def]
      exact h1
    have hρ0 : ρ c₂ = 0 := by
      simp only [hρdef]
      rw [hsymmc₂, h₂, hinfval0]
    have hρ'0 : ρ' c₂ = 0 := by
      simp only [hρ'def]
      rw [hsymmc₂, hφ'i, hinfval0]
    have hsymm_ne₂ : ∀ w ∈ ball c₂ s, w ≠ c₂ → χ₂.symm w ≠ p₂ := by
      intro w hw hwc h
      have hwt : w ∈ χ₂.target := (hsb₂ hw).1
      have h2 : χ₂ (χ₂.symm w) = w := χ₂.right_inv hwt
      rw [h] at h2
      exact hwc h2.symm
    have hρdat : ∀ w ∈ ball c₂ s, w ≠ c₂ →
        ρ w ≠ 0 ∧ ‖ρ w‖ = Real.exp (ηp w) * ‖w - c₂‖ := by
      intro w hw hwc
      have hnp₁ : χ₂.symm w ≠ p₁ := Set.mem_compl_singleton_iff.mp (hsb₂ hw).2.2.1
      have hnp₂ : χ₂.symm w ≠ p₂ := hsymm_ne₂ w hw hwc
      obtain ⟨u, hu, hu0, hun⟩ := hφdat (χ₂.symm w) hnp₁ hnp₂
      have hval : ρ w = u⁻¹ := by
        simp only [hρdef]
        rw [hu, hinfval u hu0]
      have hballm : w ∈ ball c₂ s₁ \ {c₂} :=
        ⟨hsb₁ hw, fun h ↦ hwc (Set.mem_singleton_iff.mp h)⟩
      have hη := hηpval w hballm
      have hpos : 0 < ‖w - c₂‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hwc)
      have hGx : G (χ₂.symm w) = ηp w + Real.log ‖w - c₂‖ := by linarith
      refine ⟨by rw [hval]; exact inv_ne_zero hu0, ?_⟩
      rw [hval, norm_inv, hun, ← Real.exp_neg, neg_neg, hGx, Real.exp_add,
        Real.exp_log hpos]
    have hρderiv : deriv ρ c₂ ≠ 0 := by
      refine hderiv_ne ρ c₂ s ηp hs hρ0 hρan ?_ (fun w hw hwc ↦ (hρdat w hw hwc).2)
      exact (hηpharm c₂ (mem_ball_self hs₁pos)).1.continuousAt
    obtain ⟨A₂, hA₂def⟩ : ∃ f : ℂ → ℂ,
        f = fun w ↦ dslope ρ' c₂ w / dslope ρ c₂ w * (1 - w₀ * ρ w) := ⟨_, rfl⟩
    have hA₂cont : ContinuousAt A₂ c₂ := by
      have hc1 : ContinuousAt (dslope ρ' c₂) c₂ :=
        continuousAt_dslope_same.mpr (hρ'an c₂ (mem_ball_self hs)).differentiableAt
      have hc2 : ContinuousAt (dslope ρ c₂) c₂ :=
        continuousAt_dslope_same.mpr (hρan c₂ (mem_ball_self hs)).differentiableAt
      have hc3 : dslope ρ c₂ c₂ ≠ 0 := by
        rw [dslope_same]
        exact hρderiv
      have hc4 : ContinuousAt (fun w ↦ 1 - w₀ * ρ w) c₂ :=
        continuousAt_const.sub
          (continuousAt_const.mul (hρan c₂ (mem_ball_self hs)).continuousAt)
      simp only [hA₂def]
      exact (hc1.div hc2 hc3).mul hc4
    have hA₂diff : ∀ᶠ w in 𝓝[≠] c₂, DifferentiableAt ℂ A₂ w := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c₂ hs), self_mem_nhdsWithin]
        with w hwb hwm
      have hwc : w ≠ c₂ := Set.mem_compl_singleton_iff.mp hwm
      have hd1 := hdslope_diff ρ' c₂ w hρ'0 hwc (hρ'an w hwb)
      have hd2 := hdslope_diff ρ c₂ w hρ0 hwc (hρan w hwb)
      have hd3 : dslope ρ c₂ w ≠ 0 :=
        hdslope_ne ρ c₂ w hρ0 hwc (hρdat w hwb hwc).1
      have hd4 : DifferentiableAt ℂ (fun v ↦ 1 - w₀ * ρ v) w :=
        (differentiableAt_const _).sub
          ((differentiableAt_const _).mul (hρan w hwb).differentiableAt)
      simp only [hA₂def]
      exact (hd1.div hd2 hd3).mul hd4
    have hA₂an : AnalyticAt ℂ A₂ c₂ :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        hA₂diff hA₂cont
    have hHp₂eq : A₂ =ᶠ[𝓝 c₂] H ∘ ⇑χ₂.symm := by
      filter_upwards [ball_mem_nhds c₂ hs] with w hwb
      by_cases hwc : w = c₂
      · subst hwc
        simp only [hA₂def, Function.comp_apply]
        rw [hρ0, mul_zero, sub_zero, mul_one, hsymmc₂]
        simp only [hHdef]
        rw [ite_eq_right (Ne.symm hq'p₂), ite_eq_left trivial]
      · have hnp₂ : χ₂.symm w ≠ p₂ := hsymm_ne₂ w hwb hwc
        have hnq' : χ₂.symm w ≠ q' := Set.mem_compl_singleton_iff.mp (hsb₂ hwb).2.2.2
        have hnp₁ : χ₂.symm w ≠ p₁ := Set.mem_compl_singleton_iff.mp (hsb₂ hwb).2.2.1
        obtain ⟨u, hu, hu0, -⟩ := hφdat (χ₂.symm w) hnp₁ hnp₂
        obtain ⟨u', hu', hu'0, -⟩ := hφ'dat (χ₂.symm w) hnq' hnp₂
        have hρw : ρ w = u⁻¹ := by
          simp only [hρdef]
          rw [hu, hinfval u hu0]
        have hρ'w : ρ' w = u'⁻¹ := by
          simp only [hρ'def]
          rw [hu', hinfval u' hu'0]
        simp only [hA₂def, Function.comp_apply, hHdef]
        rw [ite_eq_right hnq', ite_eq_right hnp₂, hu, hu', sphereChartFinite_coe,
          sphereChartFinite_coe, hdslope_eval ρ' c₂ w hρ'0 hwc,
          hdslope_eval ρ c₂ w hρ0 hwc,
          div_div_div_cancel_right₀ (sub_ne_zero_of_ne hwc), hρw, hρ'w]
        field_simp
    exact hbuild H p₂ (hA₂an.congr hHp₂eq)
  have hHsm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H := by
    intro x
    by_cases hx1 : x = q'
    · subst hx1
      exact hHsm_q'
    by_cases hx2 : x = p₂
    · subst hx2
      exact hHsm_p₂
    exact hHsm_gen x hx1 hx2
  /- ## Endgame case split on compactness of the surface. -/
  by_cases hcpt : CompactSpace M
  · -- Compact: a nonconstant holomorphic function has clopen plane image.
    have := hcpt
    have hnc : ¬ ∃ cc : ℂ, ∀ x : M, H x = cc := by
      rintro ⟨cc, hcc⟩
      apply hHp₁
      rw [hcc p₁, ← hcc q]
      exact hHq
    have hopen : IsOpenMap H := isOpenMap_of_contMDiff_of_not_const hHsm hnc
    have hclopen : IsClopen (Set.range H) :=
      ⟨(isCompact_range hHsm.continuous).isClosed, hopen.isOpen_range⟩
    have hrange : Set.range H = Set.univ :=
      hclopen.eq_univ ⟨H q, Set.mem_range_self q⟩
    obtain ⟨CB, hCB⟩ := isBounded_iff_forall_norm_le.mp
      (isCompact_range hHsm.continuous).isBounded
    have hmem : ((max CB 0 + 1 : ℝ) : ℂ) ∈ Set.range H := by
      rw [hrange]
      exact Set.mem_univ _
    have hle := hCB _ hmem
    have h0C : (0 : ℝ) ≤ max CB 0 := le_max_right CB 0
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hle
    have hCle : CB ≤ max CB 0 := le_max_left CB 0
    linarith
  · -- Noncompact: the bounded-ratio comparison forces a Green's function at `q`.
    have hncM : NoncompactSpace M := not_compactSpace_iff.mp hcpt
    /- ## The per-candidate Blaschke-type comparison at the pole `q`. -/
    have MAIN : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) →
        (∀ y, ‖Ψ y‖ < 1) → Ψ q = 0 → (∃ y₀, Ψ y₀ ≠ 0) →
        ∀ x, x ≠ q → BddAbove ((fun v ↦ v x) '' greenFamily q) := by
      intro Ψ hΨm hΨlt hΨq hΨex
      have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun y ↦ (hΨm y).continuousAt
      have hqsrc : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
      have hcq : (chartAt ℂ q).symm (chartAt ℂ q q) = q := (chartAt ℂ q).left_inv hqsrc
      -- Punctured-neighborhood nonvanishing at the pole, in the chart.
      have hisoq := hisoM Ψ hΨm hΨex q hΨq
      obtain ⟨W0, hW0sub, hW0open, hqW0⟩ :=
        _root_.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hisoq)
      -- A chart ball around the pole inside the chart target whose pullback lies in `W0`.
      have hopen1 : IsOpen ((chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0) :=
        (chartAt ℂ q).isOpen_inter_preimage_symm hW0open
      have hmem1 : chartAt ℂ q q ∈ (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0 := by
        refine ⟨(chartAt ℂ q).map_source hqsrc, ?_⟩
        rw [Set.mem_preimage, hcq]
        exact hqW0
      obtain ⟨rr, hrr, hrrsub⟩ := Metric.isOpen_iff.1 hopen1 (chartAt ℂ q q) hmem1
      -- The small pole disk `V'` and its compact closure barrel `K'`.
      have hrr2 : 0 < rr / 2 := by linarith
      have hcbsub : closedBall (chartAt ℂ q q) (rr / 2) ⊆
          (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0 :=
        (Metric.closedBall_subset_ball (by linarith)).trans hrrsub
      obtain ⟨V', hV'def⟩ : ∃ S : Set M,
          S = (chartAt ℂ q).source ∩ chartAt ℂ q ⁻¹' ball (chartAt ℂ q q) (rr / 2) :=
              ⟨_, rfl⟩
      have hV'open : IsOpen V' := by
        rw [hV'def]
        exact (chartAt ℂ q).continuousOn.isOpen_inter_preimage (chartAt ℂ q).open_source
          isOpen_ball
      have hqV' : q ∈ V' := by
        rw [hV'def]
        exact ⟨hqsrc, by rw [Set.mem_preimage]; exact mem_ball_self hrr2⟩
      -- Nonvanishing of `Ψ` on the punctured pole disk (pullback of `W0`).
      have hV'ne : ∀ y ∈ V', y ≠ q → Ψ y ≠ 0 := by
        intro y hy hyq
        rw [hV'def] at hy
        have h1 : chartAt ℂ q y ∈ ball (chartAt ℂ q q) rr :=
          ball_subset_ball (by linarith) hy.2
        have h2 : (chartAt ℂ q).symm (chartAt ℂ q y) ∈ W0 := (hrrsub h1).2
        rw [(chartAt ℂ q).left_inv hy.1] at h2
        exact hW0sub h2 hyq
      -- The compact barrel and the boundary sphere.
      obtain ⟨K', hK'def⟩ : ∃ S : Set M,
          S = (chartAt ℂ q).symm '' closedBall (chartAt ℂ q q) (rr / 2) := ⟨_, rfl⟩
      have hK'cp : IsCompact K' := by
        rw [hK'def]
        exact (isCompact_closedBall _ _).image_of_continuousOn
          ((chartAt ℂ q).continuousOn_symm.mono (hcbsub.trans Set.inter_subset_left))
      have hV'K' : V' ⊆ K' := by
        intro y hy
        rw [hV'def] at hy
        rw [hK'def]
        exact ⟨chartAt ℂ q y, ball_subset_closedBall hy.2, (chartAt ℂ q).left_inv hy.1⟩
      have hclosV' : closure V' ⊆ K' :=
        closure_minimal hV'K' hK'cp.isClosed
      -- Points of the barrel off the disk sit on the boundary sphere, where `Ψ ≠ 0`.
      have hK'edge : ∀ y ∈ K', y ∉ V' →
          y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2) := by
        intro y hy hyV'
        rw [hK'def] at hy
        obtain ⟨w, hw, rfl⟩ := hy
        have hwt : w ∈ (chartAt ℂ q).target := (hcbsub hw).1
        have hysrc : (chartAt ℂ q).symm w ∈ (chartAt ℂ q).source := (chartAt ℂ q).map_target
            hwt
        have hwch : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
        have hnb : w ∉ ball (chartAt ℂ q q) (rr / 2) := by
          intro hwb
          apply hyV'
          rw [hV'def]
          exact ⟨hysrc, by rw [Set.mem_preimage, hwch]; exact hwb⟩
        have hd : dist w (chartAt ℂ q q) = rr / 2 := by
          have h1 := mem_closedBall.1 hw
          have h2 : ¬ dist w (chartAt ℂ q q) < rr / 2 := fun h ↦ hnb (mem_ball.2 h)
          linarith [not_lt.mp h2]
        exact ⟨w, mem_sphere.2 hd, rfl⟩
      have hedge_ne : ∀ y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2), Ψ y ≠
          0 := by
        rintro y ⟨w, hw, rfl⟩
        have hwb : w ∈ ball (chartAt ℂ q q) rr := by
          rw [mem_ball]
          rw [mem_sphere.1 hw]
          linarith
        have hwt : w ∈ (chartAt ℂ q).target := (hrrsub hwb).1
        have hW0mem : (chartAt ℂ q).symm w ∈ W0 := (hrrsub hwb).2
        have hyne : (chartAt ℂ q).symm w ≠ q := by
          intro hcon
          have h1 : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
          rw [hcon] at h1
          have h2 : dist w (chartAt ℂ q q) = rr / 2 := mem_sphere.1 hw
          rw [← h1, dist_self] at h2
          linarith
        exact hW0sub hW0mem hyne
      -- The minimum of `‖Ψ‖` on the boundary sphere is positive.
      have hS'cp : IsCompact ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2)) := by
        refine (isCompact_sphere _ _).image_of_continuousOn ?_
        refine (chartAt ℂ q).continuousOn_symm.mono ?_
        refine (sphere_subset_closedBall.trans ?_)
        exact hcbsub.trans Set.inter_subset_left
      have hS'ne : ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2)).Nonempty :=
        Set.Nonempty.image _ (NormedSpace.sphere_nonempty.2 hrr2.le)
      obtain ⟨ym, hymS, hymmin⟩ := hS'cp.exists_isMinOn hS'ne (hΨc.norm.continuousOn)
      have hm0 : 0 < ‖Ψ ym‖ := norm_pos_iff.2 (hedge_ne ym hymS)
      -- The truncated pole-adapted logarithm family.
      obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ → M → ℝ, Λ = fun N x ↦
          if x ∈ V' then Real.log ‖Ψ x‖
          else if Ψ x = 0 then -N else max (Real.log ‖Ψ x‖) (-N) := ⟨_, rfl⟩
      have hΛ1 : ∀ N (x : M), x ∈ V' → Λ N x = Real.log ‖Ψ x‖ := by
        intro N x hx
        simp only [hΛdef]
        exact ite_eq_left hx
      have hΛ2 : ∀ N (x : M), x ∉ V' → Ψ x = 0 → Λ N x = -N := by
        intro N x hx hx0
        simp only [hΛdef]
        rw [ite_eq_right hx, ite_eq_left hx0]
      have hΛ3 : ∀ N (x : M), x ∉ V' → Ψ x ≠ 0 → Λ N x = max (Real.log ‖Ψ x‖) (-N)
          := by
        intro N x hx hx0
        simp only [hΛdef]
        rw [ite_eq_right hx, ite_eq_right hx0]
      -- The truncation is nonpositive.
      have hΛle : ∀ N, 0 < N → ∀ x : M, Λ N x ≤ 0 := by
        intro N hN x
        by_cases hx : x ∈ V'
        · rw [hΛ1 N x hx]
          exact Real.log_nonpos (norm_nonneg _) (hΨlt x).le
        · by_cases hx0 : Ψ x = 0
          · rw [hΛ2 N x hx hx0]; linarith
          · rw [hΛ3 N x hx hx0]
            refine max_le ?_ (by linarith)
            exact Real.log_nonpos (norm_nonneg _) (hΨlt x).le
      -- Subharmonicity of the truncation off the pole, for large truncation levels.
      have hΛsub : ∀ N, -Real.log (‖Ψ ym‖ / 2) ≤ N → ∀ x : M, x ≠ q →
          MSubharmonicAt (Λ N) x := by
        intro N hN x hxq
        by_cases hxV' : x ∈ V'
        · -- near the pole: the truncation is the genuine `log‖Ψ‖`, harmonic there
          have hO : IsOpen (V' ∩ {q}ᶜ) := hV'open.inter isOpen_compl_singleton
          have hxO : x ∈ V' ∩ {q}ᶜ := ⟨hxV', hxq⟩
          have hEq : Set.EqOn (fun y ↦ Real.log ‖Ψ y‖) (Λ N) (V' ∩ {q}ᶜ) := by
            intro y hy
            exact (hΛ1 N y hy.1).symm
          exact hcongM _ _ x _ hO hxO hEq
            ((hlogM Ψ hΨm x (hV'ne x hxV' hxq)).msubharmonicAt)
        · by_cases hxm : ‖Ψ ym‖ / 2 < ‖Ψ x‖
          · -- moderate modulus: the truncation agrees with the genuine `log‖Ψ‖`
            have hO : IsOpen {y : M | ‖Ψ ym‖ / 2 < ‖Ψ y‖} :=
              isOpen_lt continuous_const hΨc.norm
            have hEq : Set.EqOn (fun y ↦ Real.log ‖Ψ y‖) (Λ N)
                {y : M | ‖Ψ ym‖ / 2 < ‖Ψ y‖} := by
              intro y hy
              have hy' : ‖Ψ ym‖ / 2 < ‖Ψ y‖ := hy
              by_cases hyV' : y ∈ V'
              · exact (hΛ1 N y hyV').symm
              · have hy0 : Ψ y ≠ 0 := by
                  intro hcon
                  rw [hcon, norm_zero] at hy'
                  linarith
                rw [hΛ3 N y hyV' hy0]
                have h1 : -N ≤ Real.log ‖Ψ y‖ := by
                  have h2 : Real.log (‖Ψ ym‖ / 2) ≤ Real.log ‖Ψ y‖ :=
                    Real.log_le_log (by linarith) hy'.le
                  linarith
                exact (max_eq_left h1).symm
            have hx0 : Ψ x ≠ 0 := by
              intro hcon
              rw [hcon, norm_zero] at hxm
              linarith
            exact hcongM _ _ x _ hO hxm hEq ((hlogM Ψ hΨm x hx0).msubharmonicAt)
          · -- small modulus away from the pole disk: use the plain truncated form
            have hxK' : x ∉ closure V' := by
              intro hcon
              by_cases hxV2 : x ∈ V'
              · exact hxV' hxV2
              · have h1 := hK'edge x (hclosV' hcon) hxV2
                have h4 : ‖Ψ ym‖ ≤ ‖Ψ x‖ := hymmin h1
                have h5 : 0 < ‖Ψ ym‖ := hm0
                linarith [not_lt.mp hxm]
            have hOc : IsOpen ((closure V')ᶜ : Set M) := isClosed_closure.isOpen_compl
            by_cases hx0 : Ψ x = 0
            · -- constant `−N` near a zero of `Ψ`
              have hO : IsOpen ((closure V')ᶜ ∩ Ψ ⁻¹' ball 0 (Real.exp (-N))) :=
                hOc.inter (isOpen_ball.preimage hΨc)
              have hxO : x ∈ (closure V')ᶜ ∩ Ψ ⁻¹' ball 0 (Real.exp (-N)) := by
                refine ⟨hxK', ?_⟩
                rw [Set.mem_preimage, hx0]
                exact mem_ball_self (Real.exp_pos _)
              have hEq : Set.EqOn (fun _ : M ↦ (-N : ℝ)) (Λ N)
                  ((closure V')ᶜ ∩ Ψ ⁻¹' ball 0 (Real.exp (-N))) := by
                rintro y ⟨hy1, hy2⟩
                have hyV' : y ∉ V' := fun hcon ↦ hy1 (subset_closure hcon)
                by_cases hy0 : Ψ y = 0
                · exact (hΛ2 N y hyV' hy0).symm
                · rw [Set.mem_preimage, mem_ball_zero_iff] at hy2
                  have h2 : Real.log ‖Ψ y‖ ≤ -N := by
                    have h3 := Real.log_lt_log (norm_pos_iff.mpr hy0) hy2
                    rw [Real.log_exp] at h3
                    exact h3.le
                  rw [hΛ3 N y hyV' hy0]
                  exact (max_eq_right h2).symm
              exact hcongM _ _ x _ hO hxO hEq
                ((mharmonicAt_const (x := x) (a := (-N : ℝ))).msubharmonicAt)
            · -- the max of the harmonic `log‖Ψ‖` and the constant `−N`
              have hO : IsOpen ((closure V')ᶜ ∩ Ψ ⁻¹' {(0 : ℂ)}ᶜ) :=
                hOc.inter (isOpen_compl_singleton.preimage hΨc)
              have hxO : x ∈ (closure V')ᶜ ∩ Ψ ⁻¹' {(0 : ℂ)}ᶜ := ⟨hxK', hx0⟩
              have hEq : Set.EqOn (fun y ↦ max (Real.log ‖Ψ y‖) (-N)) (Λ N)
                  ((closure V')ᶜ ∩ Ψ ⁻¹' {(0 : ℂ)}ᶜ) := by
                rintro y ⟨hy1, hy2⟩
                have hyV' : y ∉ V' := fun hcon ↦ hy1 (subset_closure hcon)
                exact (hΛ3 N y hyV' hy2).symm
              have hmax : MSubharmonicAt (fun y ↦ max (Real.log ‖Ψ y‖) (-N)) x :=
                MSubharmonicAt.max ((hlogM Ψ hΨm x hx0).msubharmonicAt)
                  ((mharmonicAt_const (x := x) (a := (-N : ℝ))).msubharmonicAt)
              exact hcongM _ _ x _ hO hxO hEq hmax
      -- The chart map sends the punctured filter at `q` into the punctured filter at `c_q`.
      have htendq : Tendsto (chartAt ℂ q) (𝓝[≠] q) (𝓝[≠] (chartAt ℂ q q)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · exact ((chartAt ℂ q).continuousAt hqsrc).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ q).open_source.mem_nhds hqsrc),
            self_mem_nhdsWithin] with y hys hyq
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hyq ((chartAt ℂ q).injOn hys hqsrc hcon)
      -- First-order vanishing of `Ψ` at the pole: `log‖Ψ‖ ≤ C + log‖poleCoord‖` nearby.
      have hslope : ∃ Cs : ℝ, ∀ᶠ x in 𝓝[≠] q,
          Real.log ‖Ψ x‖ ≤ Cs + Real.log ‖poleCoord q x‖ := by
        have hgan : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) := hreadM Ψ hΨm
            q
        have hg0 : (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) = 0 := by
          simp only [Function.comp_apply, hcq]
          exact hΨq
        have hd : HasDerivAt (Ψ ∘ (chartAt ℂ q).symm)
            (deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)) (chartAt ℂ q q) :=
          hgan.differentiableAt.hasDerivAt
        have hsl := hasDerivAt_iff_tendsto_slope.mp hd
        have hd1 : (0 : ℝ) ≤ ‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ :=
          norm_nonneg _
        have hbnd : ∀ᶠ w in 𝓝[≠] (chartAt ℂ q q),
            ‖slope (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) w‖
              < ‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ + 1 :=
          hsl.norm.eventually_lt_const (by linarith)
        refine ⟨Real.log (‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ + 1), ?_⟩
        filter_upwards [htendq.eventually hbnd,
          nhdsWithin_le_nhds ((chartAt ℂ q).open_source.mem_nhds hqsrc),
          self_mem_nhdsWithin, hisoq] with x hx hxs hxq hx0
        have hxcne : chartAt ℂ q x ≠ chartAt ℂ q q := by
          intro hcon
          exact hxq ((chartAt ℂ q).injOn hxs hqsrc hcon)
        have hslval : slope (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) (chartAt ℂ q x)
            = Ψ x / (chartAt ℂ q x - chartAt ℂ q q) := by
          rw [slope_def_field, hg0, sub_zero]
          congr 1
          simp only [Function.comp_apply, (chartAt ℂ q).left_inv hxs]
        have hx' := hx
        rw [hslval] at hx'
        have hpne : chartAt ℂ q x - chartAt ℂ q q ≠ 0 := sub_ne_zero_of_ne hxcne
        have hΨbound : ‖Ψ x‖ ≤ (‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖
            + 1)
            * ‖chartAt ℂ q x - chartAt ℂ q q‖ := by
          rw [norm_div] at hx'
          have h2 : 0 < ‖chartAt ℂ q x - chartAt ℂ q q‖ := norm_pos_iff.mpr hpne
          rw [div_lt_iff₀ h2] at hx'
          exact hx'.le
        have h3 : Real.log ‖Ψ x‖ ≤
            Real.log ((‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ + 1)
              * ‖chartAt ℂ q x - chartAt ℂ q q‖) :=
          Real.log_le_log (norm_pos_iff.mpr hx0) hΨbound
        rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hpne)] at h3
        exact h3
      obtain ⟨Cs, hCs⟩ := hslope
      -- The per-candidate comparison via the puncture-tolerant maximum principle.
      have key : ∀ N, -Real.log (‖Ψ ym‖ / 2) ≤ N → 0 < N →
          ∀ v ∈ greenFamily q, ∀ x, x ≠ q → v x + Λ N x ≤ 0 := by
        intro N hN0 hNpos v hv x hx
        obtain ⟨hvsub, -, ⟨K, hKcp, -, hK0⟩, C, hC⟩ := hv
        have h1 : MSubharmonicOn (fun y ↦ v y + Λ N y) {q}ᶜ :=
          fun y hy ↦ haddM v (Λ N) y (hvsub y hy) (hΛsub N hN0 y hy)
        have h2 : ∃ K' : Set M, IsCompact K' ∧ ∀ y ∉ K', v y + Λ N y ≤ 0 :=
          ⟨K, hKcp, fun y hy ↦ by rw [hK0 y hy, zero_add]; exact hΛle N hNpos y⟩
        have h3 : ∃ C', ∀ᶠ y in 𝓝[≠] q, v y + Λ N y ≤ C' := by
          refine ⟨C + Cs, ?_⟩
          have hV'mem : ∀ᶠ y in 𝓝[≠] q, y ∈ V' :=
            nhdsWithin_le_nhds (hV'open.mem_nhds hqV')
          filter_upwards [hC, hCs, hV'mem] with y h1y h2y h3y
          rw [hΛ1 N y h3y]
          linarith
        exact msubharmonic_le_zero_of_puncture h1 h2 h3 x hx
      -- Boundedness of the family at every point off the pole.
      intro x hx
      refine ⟨-Λ (max (-Real.log (‖Ψ ym‖ / 2)) 1) x, ?_⟩
      rintro t ⟨v, hv, rfl⟩
      have h1 := key (max (-Real.log (‖Ψ ym‖ / 2)) 1) (le_max_left _ _)
        (lt_of_lt_of_le one_pos (le_max_right _ _)) v hv x hx
      have h2 : (fun v : M → ℝ ↦ v x) v = v x := rfl
      rw [h2]
      linarith
    /- ## A global bound on `H`: off the compact closures by the two modulus
    bounds, on them by continuity. -/
    obtain ⟨CG, V₁, hV₁n, V₂, hV₂n, hV₁c, hV₂c, hGb⟩ := hbdd
    obtain ⟨CG', V₁', hV₁'n, V₂', hV₂'n, hV₁'c, hV₂'c, hG'b⟩ := hbdd'
    have hKBcp : IsCompact ((closure V₁ ∪ closure V₂) ∪ (closure V₁' ∪ closure V₂'))
        :=
      (hV₁c.union hV₂c).union (hV₁'c.union hV₂'c)
    obtain ⟨B₁, hB₁⟩ := hKBcp.exists_bound_of_continuousOn hHsm.continuous.continuousOn
    have hoff : ∀ x : M, x ∉ (closure V₁ ∪ closure V₂) ∪ (closure V₁' ∪ closure
        V₂') →
        ‖H x‖ ≤ (Real.exp CG + ‖w₀‖) * Real.exp CG' := by
      intro x hx
      have hx1 : x ∉ V₁ ∪ V₂ := by
        intro hmem
        apply hx
        rcases hmem with hm | hm
        · exact Or.inl (Or.inl (subset_closure hm))
        · exact Or.inl (Or.inr (subset_closure hm))
      have hx2 : x ∉ V₁' ∪ V₂' := by
        intro hmem
        apply hx
        rcases hmem with hm | hm
        · exact Or.inr (Or.inl (subset_closure hm))
        · exact Or.inr (Or.inr (subset_closure hm))
      have hxp₁ : x ≠ p₁ := by
        rintro rfl
        exact hx1 (Or.inl (mem_of_mem_nhds hV₁n))
      have hxp₂ : x ≠ p₂ := by
        rintro rfl
        exact hx1 (Or.inr (mem_of_mem_nhds hV₂n))
      have hxq' : x ≠ q' := by
        rintro rfl
        exact hx2 (Or.inl (mem_of_mem_nhds hV₁'n))
      obtain ⟨u, hu, hu0, hun⟩ := hφdat x hxp₁ hxp₂
      obtain ⟨u', hu', hu'0, hu'n⟩ := hφ'dat x hxq' hxp₂
      have hHval : H x = (u - w₀) / u' := by
        simp only [hHdef]
        rw [ite_eq_right hxq', ite_eq_right hxp₂, hu, hu', sphereChartFinite_coe,
          sphereChartFinite_coe]
      have hGx := hGb x hx1
      have hG'x := hG'b x hx2
      have hb1 : ‖u‖ ≤ Real.exp CG := by
        rw [hun]
        apply Real.exp_le_exp.mpr
        have habsle := abs_le.mp hGx
        linarith [habsle.1]
      have hb2 : Real.exp (-CG') ≤ ‖u'‖ := by
        rw [hu'n]
        apply Real.exp_le_exp.mpr
        have habsle := abs_le.mp hG'x
        linarith [habsle.2]
      have hb3 : ‖u - w₀‖ ≤ Real.exp CG + ‖w₀‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_nonneg w₀])
      rw [hHval, norm_div]
      calc ‖u - w₀‖ / ‖u'‖ ≤ (Real.exp CG + ‖w₀‖) / Real.exp (-CG') :=
            div_le_div₀ (by positivity) hb3 (Real.exp_pos _) hb2
        _ = (Real.exp CG + ‖w₀‖) * Real.exp CG' := by
            rw [Real.exp_neg, div_eq_mul_inv, inv_inv]
    set B : ℝ := max B₁ ((Real.exp CG + ‖w₀‖) * Real.exp CG') with hBdef
    have hB : ∀ x : M, ‖H x‖ ≤ B := by
      intro x
      by_cases hx : x ∈ (closure V₁ ∪ closure V₂) ∪ (closure V₁' ∪ closure V₂')
      · exact (hB₁ x hx).trans (le_max_left _ _)
      · exact (hoff x hx).trans (le_max_right _ _)
    have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg (H q)) (hB q)
    have hD0 : (0 : ℝ) < 2 * B + 1 := by linarith
    have hDC0 : ((2 * B + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD0.ne'
    /- ## The normalized transplant `Ψ = (H − H q)/(2B + 1)`. -/
    obtain ⟨Ψ, hΨdef⟩ : ∃ f : M → ℂ,
        f = fun x ↦ (H x - H q) / ((2 * B + 1 : ℝ) : ℂ) := ⟨_, rfl⟩
    have hΨm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y := by
      intro y
      apply hbuild
      have hm1 : AnalyticAt ℂ (H ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y y) :=
        hreadM H (fun z ↦ hHsm z) y
      have hm2 : AnalyticAt ℂ
          (fun w ↦ (H ((chartAt ℂ y).symm w) - H q) / ((2 * B + 1 : ℝ) : ℂ))
          (chartAt ℂ y y) := (hm1.sub analyticAt_const).div analyticAt_const hDC0
      rw [hΨdef]
      exact hm2
    have hΨlt : ∀ y, ‖Ψ y‖ < 1 := by
      intro y
      simp only [hΨdef]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0,
        div_lt_one hD0]
      have hb1 := hB y
      have hb2 := hB q
      have hb3 := norm_sub_le (H y) (H q)
      linarith
    have hΨq : Ψ q = 0 := by
      simp only [hΨdef]
      rw [sub_self, zero_div]
    have hΨex : ∃ y₀, Ψ y₀ ≠ 0 := by
      refine ⟨p₁, ?_⟩
      simp only [hΨdef]
      rw [hHq, sub_zero]
      exact div_ne_zero hHp₁ hDC0
    exact hnon q ⟨p₁, Ne.symm hqp₁, MAIN Ψ hΨm hΨlt hΨq hΨex p₁ (Ne.symm hqp₁)⟩

end RiemannDynamics
