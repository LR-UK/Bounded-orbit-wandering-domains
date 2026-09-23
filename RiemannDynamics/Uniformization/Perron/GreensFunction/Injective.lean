/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreensFunction.GreenMap

/-!
# Injectivity of the Green map and the chart diffeomorphism

The global Green map is injective, an injective holomorphic function on a
surface is a biholomorphism onto a plane domain, and the hyperbolic case of
the planarity theorem follows.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-! ## Injectivity and the chart diffeomorphism -/

/-- **Injectivity** of the Green's map, via the Blaschke-transplant
comparison with the extremal property of the envelope. -/
theorem injective_green_map [T2Space M] [SimplyConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) {φ : M → ℂ}
    (hφ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ) (h0 : φ p₀ = 0)
    (habs : ∀ x, x ≠ p₀ → ‖φ x‖ = Real.exp (-(greenEnvelope p₀ x))) :
    Function.Injective φ := by
  classical
  -- ## Step 0: the map sends the surface into the unit disc, vanishing only at the pole.
  have hGpos := greenEnvelope_pos hG
  have hlt : ∀ x : M, ‖φ x‖ < 1 := by
    intro x
    by_cases hx : x = p₀
    · rw [hx, h0, norm_zero]; exact one_pos
    · rw [habs x hx]
      calc Real.exp (-(greenEnvelope p₀ x)) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith [hGpos x hx])
        _ = 1 := Real.exp_zero
  have hne0 : ∀ x : M, x ≠ p₀ → φ x ≠ 0 := by
    intro x hx h
    have h1 := habs x hx
    rw [h, norm_zero] at h1
    exact absurd h1.symm (ne_of_gt (Real.exp_pos _))
  -- ## Step 1: fix a collision and reduce to two points distinct from the pole.
  intro q₁ q₂ hq
  by_contra hne
  have hq₁ : q₁ ≠ p₀ := by
    intro h
    have h2 : φ q₂ = 0 := by rw [← hq, h]; exact h0
    have h3 : q₂ = p₀ := by
      by_contra h4
      exact hne0 q₂ h4 h2
    exact hne (h.trans h3.symm)
  have hq₂q₁ : q₂ ≠ q₁ := fun h => hne h.symm
  -- ## Step 2: generic bricks.
  -- Plane-level transfer of subharmonicity along equality of functions.
  have htransfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro c hc ρ hρ hb
    have h1 : G c = F c := (hFG hc).symm
    have h2 : Real.circleAverage F c ρ = Real.circleAverage G c ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 c (hWU hc) ρ hρ (hb.trans hWU)
  -- Surface-level: subharmonicity at a point respects equality near the point.
  have hcongM : ∀ (F G : M → ℝ) (x : M) (O : Set M), IsOpen O → x ∈ O →
      Set.EqOn F G O → MSubharmonicAt F x → MSubharmonicAt G x := by
    intro F G x O hO hxO hFG hF
    obtain ⟨r, hr, -, hsub⟩ := hF
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm hO
    have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O := by
      refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
      exact hxO
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 (isOpen_ball.inter hopen)
      (chartAt ℂ x x) ⟨mem_ball_self hr, hmem⟩
    refine ⟨ρ, hρ, fun w hw => ((hρsub hw).2).1, ?_⟩
    refine htransfer _ _ _ _ hsub (fun w hw => (hρsub hw).1) ?_
    intro w hw
    exact hFG ((hρsub hw).2).2
  -- Sums of subharmonic functions are subharmonic.
  have haddM : ∀ (F G : M → ℝ) (x : M), MSubharmonicAt F x → MSubharmonicAt G x →
      MSubharmonicAt (fun y => F y + G y) x := by
    intro F G x hF hG
    obtain ⟨r₁, hr₁, hb₁, hs₁⟩ := hF
    obtain ⟨r₂, hr₂, -, hs₂⟩ := hG
    have hmono : ∀ (f : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn f U → V ⊆ U →
        SubharmonicOn f V := fun f U V hf hVU =>
      ⟨hf.1.mono hVU, fun c hc ρ hρ hball => hf.2 c (hVU hc) ρ hρ (hball.trans hVU)⟩
    have hs₁' := hmono _ _ _ hs₁ (ball_subset_ball (min_le_left r₁ r₂))
    have hs₂' := hmono _ _ _ hs₂ (ball_subset_ball (min_le_right r₁ r₂))
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (ball_subset_ball (min_le_left r₁ r₂)).trans hb₁, ?_, ?_⟩
    · exact hs₁'.1.add hs₂'.1
    · intro c hc ρ hρ hb
      have hsph : sphere c ρ ⊆ ball (chartAt ℂ x x) (min r₁ r₂) :=
        sphere_subset_closedBall.trans hb
      have hci₁ : CircleIntegrable (F ∘ (chartAt ℂ x).symm) c ρ :=
        (hs₁'.1.mono hsph).circleIntegrable hρ.le
      have hci₂ : CircleIntegrable (G ∘ (chartAt ℂ x).symm) c ρ :=
        (hs₂'.1.mono hsph).circleIntegrable hρ.le
      have havg := Real.circleAverage_fun_add hci₁ hci₂
      have h₁ := hs₁'.2 c hc ρ hρ hb
      have h₂ := hs₂'.2 c hc ρ hρ hb
      calc ((fun y => F y + G y) ∘ (chartAt ℂ x).symm) c
          = (F ∘ (chartAt ℂ x).symm) c + (G ∘ (chartAt ℂ x).symm) c := rfl
        _ ≤ Real.circleAverage (F ∘ (chartAt ℂ x).symm) c ρ
            + Real.circleAverage (G ∘ (chartAt ℂ x).symm) c ρ := add_le_add h₁ h₂
        _ = Real.circleAverage
            (fun w => (F ∘ (chartAt ℂ x).symm) w + (G ∘ (chartAt ℂ x).symm) w) c ρ :=
            havg.symm
        _ = Real.circleAverage ((fun y => F y + G y) ∘ (chartAt ℂ x).symm) c ρ := rfl
  -- The logarithm of the modulus of a nonvanishing holomorphic function is harmonic.
  have hlogM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M,
      Ψ x ≠ 0 →
      MHarmonicAt (fun y => Real.log ‖Ψ y‖) x := by
    intro Ψ hΨm x hx
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have h2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) h1
    have h3 : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
    have h4 : (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hx
    exact h3.harmonicAt_log_norm h4
  -- The chart reading of a holomorphic function is analytic at the chart image.
  have hreadM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M,
      AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
    intro Ψ hΨm x
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have h2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) h1
    exact (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
  -- The singleton `{0}` is not open in the plane.
  have hnotopen0 : ¬ IsOpen ({(0 : ℂ)} : Set ℂ) := by
    intro hcon
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcon 0 rfl
    have h1 : (↑(ε / 2) : ℂ) ∈ ball (0 : ℂ) ε := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    have h2 := hball h1
    rw [Set.mem_singleton_iff, Complex.ofReal_eq_zero] at h2
    linarith
  -- Zeros of a nonconstant holomorphic function on the surface are isolated.
  have hisoM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → (∃ y₀,
      Ψ y₀ ≠ 0) →
      ∀ z : M, Ψ z = 0 → ∀ᶠ y in 𝓝[≠] z, Ψ y ≠ 0 := by
    intro Ψ hΨm hex z hz
    obtain ⟨y₀, hy₀⟩ := hex
    have hzsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    rcases (hreadM Ψ hΨm z).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      -- `Ψ` would vanish on an open set, contradicting the open mapping theorem.
      have hop : IsOpenMap Ψ := by
        refine isOpenMap_of_contMDiff_of_not_const (fun y => hΨm y) ?_
        rintro ⟨c, hc⟩
        rw [hc z] at hz
        rw [hc y₀, hz] at hy₀
        exact hy₀ rfl
      have h2 : ∀ᶠ y in 𝓝 z, Ψ y = 0 := by
        have hc : ContinuousAt (chartAt ℂ z) z := (chartAt ℂ z).continuousAt hzsrc
        filter_upwards [hc.eventually hcase,
          (chartAt ℂ z).open_source.mem_nhds hzsrc] with y h1y hsy
        have : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := h1y
        rwa [(chartAt ℂ z).left_inv hsy] at this
      obtain ⟨O, hOsub, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp h2
      have himg : Ψ '' O = {0} := by
        apply Set.Subset.antisymm
        · rintro w ⟨y, hy, rfl⟩
          exact hOsub hy
        · rintro w hw
          rw [Set.mem_singleton_iff] at hw
          exact ⟨z, hzO, by rw [hw, hz]⟩
      have := hop O hOopen
      rw [himg] at this
      exact hnotopen0 this
    · -- Transfer the punctured-neighborhood nonvanishing through the chart.
      have htend : Tendsto (chartAt ℂ z) (𝓝[≠] z) (𝓝[≠] (chartAt ℂ z z)) := by
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
      have : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := by
        rw [(chartAt ℂ z).left_inv hys]
        exact hcon
      exact this
  -- Punctured coordinate balls are connected (polar parametrization).
  have hpunc : ∀ (c : ℂ) (r : ℝ), 0 < r → IsConnected (ball c r \ {c}) := by
    intro c r hr
    have hcont : Continuous fun p : ℝ × ℝ =>
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo 0 r ×ˢ (Set.univ : Set ℝ)) = ball c r \ {c} := by
      apply Set.Subset.antisymm
      · rintro w ⟨⟨t, θ⟩, ⟨⟨ht0, htr⟩, -⟩, hw⟩
        rw [← hw]
        change c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball c r \ {c}
        have hd : dist (c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) c = t := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, hd]; exact htr
        · intro h
          rw [Set.mem_singleton_iff] at h
          rw [h, dist_self] at hd
          exact ht0.ne hd
      · rintro w ⟨hwb, hwc⟩
        rw [Set.mem_singleton_iff] at hwc
        have ht0 : 0 < ‖w - c‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hwc)
        have htr : ‖w - c‖ < r := by rw [← dist_eq_norm]; exact mem_ball.1 hwb
        refine ⟨(‖w - c‖, (w - c).arg), ⟨⟨ht0, htr⟩, Set.mem_univ _⟩, ?_⟩
        change c + (‖w - c‖ : ℂ) * Complex.exp (((w - c).arg : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    rw [← himg]
    refine ⟨Set.Nonempty.image _
      ⟨(r / 2, 0), ⟨half_pos hr, half_lt_self hr⟩, Set.mem_univ _⟩, ?_⟩
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn
  -- Plane propagation: a nonpositive subharmonic function vanishing at one point of a
  -- preconnected open set vanishes identically.
  have hprop : ∀ (S : Set ℂ) (F : ℂ → ℝ), IsOpen S → IsPreconnected S →
      SubharmonicOn F S → (∀ w ∈ S, F w ≤ 0) → ∀ w₀ ∈ S, F w₀ = 0 → ∀ w ∈ S,
          F w = 0 := by
    intro S F hSopen hSpre hFsub hFle w₀ hw₀ hFw₀
    have hu : IsOpen {w : ℂ | ∀ᶠ z in 𝓝 w, F z = 0} := isOpen_setOfPred_eventually_nhds
    have hv : IsOpen (S ∩ F ⁻¹' {(0 : ℝ)}ᶜ) :=
      hFsub.1.isOpen_inter_preimage hSopen isOpen_compl_singleton
    have hdisj : Disjoint {w : ℂ | ∀ᶠ z in 𝓝 w, F z = 0} (S ∩ F ⁻¹' {(0 :
        ℝ)}ᶜ) := by
      rw [Set.disjoint_left]
      rintro w hw ⟨-, hw2⟩
      exact hw2 hw.self_of_nhds
    have hzero_mem : ∀ w ∈ S, F w = 0 → ∀ᶠ z in 𝓝 w, F z = 0 := by
      intro w hw hFw
      have hmax : ∀ z ∈ S, F z ≤ F w := by
        intro z hz
        rw [hFw]
        exact hFle z hz
      filter_upwards [SubharmonicOn.eventually_eq_of_le hSopen hFsub hw hmax] with z hz
      rw [hz, hFw]
    have hcover : S ⊆ {w : ℂ | ∀ᶠ z in 𝓝 w, F z = 0} ∪ (S ∩ F ⁻¹' {(0 :
        ℝ)}ᶜ) := by
      intro w hw
      by_cases hFw : F w = 0
      · exact Or.inl (hzero_mem w hw hFw)
      · exact Or.inr ⟨hw, hFw⟩
    have hkey := IsPreconnected.subset_left_of_subset_union hu hv hdisj hcover
      ⟨w₀, hw₀, hzero_mem w₀ hw₀ hFw₀⟩ hSpre
    intro w hw
    exact (hkey hw).self_of_nhds
  -- Nearby-point picker: every neighborhood of a point contains a distinct point.
  have hpick : ∀ (z : M) (A : Set M), A ∈ 𝓝 z → ∃ y ∈ A, y ≠ z := by
    intro z A hA
    obtain ⟨O, hOsub, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp hA
    have hzsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    have hVopen : IsOpen (O ∩ (chartAt ℂ z).source) :=
      hOopen.inter (chartAt ℂ z).open_source
    have himg : IsOpen ((chartAt ℂ z) '' (O ∩ (chartAt ℂ z).source)) :=
      (chartAt ℂ z).isOpen_image_of_subset_source hVopen Set.inter_subset_right
    obtain ⟨s, hs, hballs⟩ := Metric.isOpen_iff.mp himg (chartAt ℂ z z)
      ⟨z, ⟨hzO, hzsrc⟩, rfl⟩
    have hmem : chartAt ℂ z z + (↑(s / 2) : ℂ) ∈ ball (chartAt ℂ z z) s := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    obtain ⟨y, ⟨hyO, hysrc⟩, hyeq⟩ := hballs hmem
    refine ⟨y, hOsub hyO, ?_⟩
    intro hcon
    rw [hcon] at hyeq
    have h3 : (↑(s / 2) : ℂ) = 0 := by
      have h4 : chartAt ℂ z z + (↑(s / 2) : ℂ) = chartAt ℂ z z + 0 := by
        rw [add_zero]; exact hyeq.symm
      exact add_left_cancel h4
    rw [Complex.ofReal_eq_zero] at h3
    linarith
  -- The Blaschke transplant package: denominator, disc bound, holomorphy.
  have hBLA : ∀ (f : M → ℂ) (b : ℂ), (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f y) →
      (∀ y, ‖f y‖ < 1) → ‖b‖ < 1 → ∀ y : M,
      (1 - (starRingEnd ℂ) b * f y ≠ 0) ∧
      ‖(f y - b) / (1 - (starRingEnd ℂ) b * f y)‖ < 1 ∧
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun x => (f x - b) / (1 - (starRingEnd ℂ) b * f x))
          y := by
    intro f b hfm hflt hb y
    have hden : ∀ x : M, 1 - (starRingEnd ℂ) b * f x ≠ 0 := by
      intro x h
      have h1 : ‖(starRingEnd ℂ) b * f x‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        calc ‖b‖ * ‖f x‖ ≤ ‖b‖ * 1 :=
              mul_le_mul_of_nonneg_left (hflt x).le (norm_nonneg b)
          _ = ‖b‖ := mul_one _
          _ < 1 := hb
      rw [← sub_eq_zero.mp h, norm_one] at h1
      exact lt_irrefl 1 h1
    refine ⟨hden y, ?_, ?_⟩
    · rw [norm_div, div_lt_one (norm_pos_iff.mpr (hden y))]
      have hid : Complex.normSq (1 - (starRingEnd ℂ) b * f y) - Complex.normSq (f y - b)
          = (1 - Complex.normSq b) * (1 - Complex.normSq (f y)) := by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
          Complex.mul_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
        ring
      have hnb : Complex.normSq b < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg b]
      have hnz : Complex.normSq (f y) < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg (f y), hflt y]
      have hlt2 : Complex.normSq (f y - b) < Complex.normSq (1 - (starRingEnd ℂ) b * f y) := by
        nlinarith [hid, hnb, hnz]
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt2
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt2
    · have houter : ContDiffAt ℂ ω (fun z : ℂ => (z - b) / (1 - (starRingEnd ℂ) b * z))
          (f y) :=
        ContDiffAt.div (contDiffAt_id.sub contDiffAt_const)
          (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) (hden y)
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
          (fun z : ℂ => (z - b) / (1 - (starRingEnd ℂ) b * z)) (f y) :=
        contMDiffAt_iff_contDiffAt.mpr houter
      exact h1.comp y (hfm y)
  -- ## Step 3: the comparison engine (per-candidate Blaschke comparison at a pole).
  -- For a holomorphic `Ψ` into the disc vanishing at `q`, the Perron family at `q`
  -- is bounded and the envelope is dominated by `−log‖Ψ‖`.
  have MAIN : ∀ (q : M) (Ψ : M → ℂ), (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) →
      (∀ y, ‖Ψ y‖ < 1) → Ψ q = 0 → (∃ y₀, Ψ y₀ ≠ 0) →
      (∀ x, x ≠ q → BddAbove ((fun v => v x) '' greenFamily q)) ∧
      ∀ x, x ≠ q → Ψ x ≠ 0 → greenEnvelope q x ≤ -Real.log ‖Ψ x‖ := by
    intro q Ψ hΨm hΨlt hΨq hΨex
    have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun y => (hΨm y).continuousAt
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
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen1 (chartAt ℂ q q) hmem1
    -- The small pole disk `V'` and its compact closure barrel `K'`.
    have hρ2 : 0 < ρ / 2 := by linarith
    have hcbsub : closedBall (chartAt ℂ q q) (ρ / 2) ⊆
        (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0 :=
      (Metric.closedBall_subset_ball (by linarith)).trans hρsub
    obtain ⟨V', hV'def⟩ : ∃ S : Set M,
        S = (chartAt ℂ q).source ∩ chartAt ℂ q ⁻¹' ball (chartAt ℂ q q) (ρ / 2) := ⟨_,
            rfl⟩
    have hV'open : IsOpen V' := by
      rw [hV'def]
      exact (chartAt ℂ q).continuousOn.isOpen_inter_preimage (chartAt ℂ q).open_source
        isOpen_ball
    have hqV' : q ∈ V' := by
      rw [hV'def]
      exact ⟨hqsrc, by rw [Set.mem_preimage]; exact mem_ball_self hρ2⟩
    -- Nonvanishing of `Ψ` on the punctured pole disk (pullback of `W0`).
    have hV'ne : ∀ y ∈ V', y ≠ q → Ψ y ≠ 0 := by
      intro y hy hyq
      rw [hV'def] at hy
      have h1 : chartAt ℂ q y ∈ ball (chartAt ℂ q q) ρ :=
        ball_subset_ball (by linarith) hy.2
      have h2 : (chartAt ℂ q).symm (chartAt ℂ q y) ∈ W0 := (hρsub h1).2
      rw [(chartAt ℂ q).left_inv hy.1] at h2
      exact hW0sub h2 hyq
    -- The compact barrel and the boundary sphere.
    obtain ⟨K', hK'def⟩ : ∃ S : Set M,
        S = (chartAt ℂ q).symm '' closedBall (chartAt ℂ q q) (ρ / 2) := ⟨_, rfl⟩
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
        y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2) := by
      intro y hy hyV'
      rw [hK'def] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      have hwt : w ∈ (chartAt ℂ q).target := (hcbsub hw).1
      have hysrc : (chartAt ℂ q).symm w ∈ (chartAt ℂ q).source := (chartAt ℂ q).map_target
          hwt
      have hwch : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
      have hnb : w ∉ ball (chartAt ℂ q q) (ρ / 2) := by
        intro hwb
        apply hyV'
        rw [hV'def]
        exact ⟨hysrc, by rw [Set.mem_preimage, hwch]; exact hwb⟩
      have hd : dist w (chartAt ℂ q q) = ρ / 2 := by
        have h1 := mem_closedBall.1 hw
        have h2 : ¬ dist w (chartAt ℂ q q) < ρ / 2 := fun h => hnb (mem_ball.2 h)
        linarith [not_lt.mp h2]
      exact ⟨w, mem_sphere.2 hd, rfl⟩
    have hedge_ne : ∀ y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2), Ψ y ≠
        0 := by
      rintro y ⟨w, hw, rfl⟩
      have hwb : w ∈ ball (chartAt ℂ q q) ρ := by
        rw [mem_ball]
        rw [mem_sphere.1 hw]
        linarith
      have hwt : w ∈ (chartAt ℂ q).target := (hρsub hwb).1
      have hW0mem : (chartAt ℂ q).symm w ∈ W0 := (hρsub hwb).2
      have hyne : (chartAt ℂ q).symm w ≠ q := by
        intro hcon
        have h1 : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
        rw [hcon] at h1
        have h2 : dist w (chartAt ℂ q q) = ρ / 2 := mem_sphere.1 hw
        rw [← h1, dist_self] at h2
        linarith
      exact hW0sub hW0mem hyne
    -- The minimum of `‖Ψ‖` on the boundary sphere is positive.
    have hS'cp : IsCompact ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2)) := by
      refine (isCompact_sphere _ _).image_of_continuousOn ?_
      refine (chartAt ℂ q).continuousOn_symm.mono ?_
      refine (sphere_subset_closedBall.trans ?_)
      exact hcbsub.trans Set.inter_subset_left
    have hS'ne : ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2)).Nonempty :=
      Set.Nonempty.image _ (NormedSpace.sphere_nonempty.2 hρ2.le)
    obtain ⟨ym, hymS, hymmin⟩ := hS'cp.exists_isMinOn hS'ne (hΨc.norm.continuousOn)
    have hm0 : 0 < ‖Ψ ym‖ := norm_pos_iff.2 (hedge_ne ym hymS)
    -- The truncated pole-adapted logarithm family.
    obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ → M → ℝ, Λ = fun N x =>
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
    have hΛ3 : ∀ N (x : M), x ∉ V' → Ψ x ≠ 0 → Λ N x = max (Real.log ‖Ψ x‖)
        (-N) := by
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
        have hEq : Set.EqOn (fun y => Real.log ‖Ψ y‖) (Λ N) (V' ∩ {q}ᶜ) := by
          intro y hy
          exact (hΛ1 N y hy.1).symm
        exact hcongM _ _ x _ hO hxO hEq
          ((hlogM Ψ hΨm x (hV'ne x hxV' hxq)).msubharmonicAt)
      · by_cases hxm : ‖Ψ ym‖ / 2 < ‖Ψ x‖
        · -- moderate modulus: the truncation agrees with the genuine `log‖Ψ‖`
          have hO : IsOpen {y : M | ‖Ψ ym‖ / 2 < ‖Ψ y‖} :=
            isOpen_lt continuous_const hΨc.norm
          have hEq : Set.EqOn (fun y => Real.log ‖Ψ y‖) (Λ N)
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
            have hEq : Set.EqOn (fun _ : M => (-N : ℝ)) (Λ N)
                ((closure V')ᶜ ∩ Ψ ⁻¹' ball 0 (Real.exp (-N))) := by
              rintro y ⟨hy1, hy2⟩
              have hyV' : y ∉ V' := fun hcon => hy1 (subset_closure hcon)
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
            have hEq : Set.EqOn (fun y => max (Real.log ‖Ψ y‖) (-N)) (Λ N)
                ((closure V')ᶜ ∩ Ψ ⁻¹' {(0 : ℂ)}ᶜ) := by
              rintro y ⟨hy1, hy2⟩
              have hyV' : y ∉ V' := fun hcon => hy1 (subset_closure hcon)
              exact (hΛ3 N y hyV' hy2).symm
            have hmax : MSubharmonicAt (fun y => max (Real.log ‖Ψ y‖) (-N)) x :=
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
      have hgan : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) := hreadM Ψ hΨm q
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
      have hΨbound : ‖Ψ x‖ ≤ (‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ +
          1)
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
      have h1 : MSubharmonicOn (fun y => v y + Λ N y) {q}ᶜ :=
        fun y hy => haddM v (Λ N) y (hvsub y hy) (hΛsub N hN0 y hy)
      have h2 : ∃ K' : Set M, IsCompact K' ∧ ∀ y ∉ K', v y + Λ N y ≤ 0 :=
        ⟨K, hKcp, fun y hy => by rw [hK0 y hy, zero_add]; exact hΛle N hNpos y⟩
      have h3 : ∃ C', ∀ᶠ y in 𝓝[≠] q, v y + Λ N y ≤ C' := by
        refine ⟨C + Cs, ?_⟩
        have hV'mem : ∀ᶠ y in 𝓝[≠] q, y ∈ V' :=
          nhdsWithin_le_nhds (hV'open.mem_nhds hqV')
        filter_upwards [hC, hCs, hV'mem] with y h1y h2y h3y
        rw [hΛ1 N y h3y]
        linarith
      exact msubharmonic_le_zero_of_puncture h1 h2 h3 x hx
    constructor
    · -- Boundedness of the family at every point off the pole (point-independence).
      intro x hx
      refine ⟨-Λ (max (-Real.log (‖Ψ ym‖ / 2)) 1) x, ?_⟩
      rintro t ⟨v, hv, rfl⟩
      have h1 := key (max (-Real.log (‖Ψ ym‖ / 2)) 1) (le_max_left _ _)
        (lt_of_lt_of_le one_pos (le_max_right _ _)) v hv x hx
      have h2 : (fun v : M → ℝ => v x) v = v x := rfl
      rw [h2]
      linarith
    · -- The envelope bound `greenEnvelope q ≤ −log‖Ψ‖`.
      intro x hx hx0
      have hlogneg : Real.log ‖Ψ x‖ < 0 :=
        Real.log_neg (norm_pos_iff.mpr hx0) (hΨlt x)
      have hNpos : 0 < max (max (-Real.log (‖Ψ ym‖ / 2)) 1) (-Real.log ‖Ψ x‖) :=
        lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _))
      have hΛval : Λ (max (max (-Real.log (‖Ψ ym‖ / 2)) 1) (-Real.log ‖Ψ x‖)) x
          = Real.log ‖Ψ x‖ := by
        by_cases hxV' : x ∈ V'
        · exact hΛ1 _ x hxV'
        · rw [hΛ3 _ x hxV' hx0]
          refine max_eq_left ?_
          have h1 : -Real.log ‖Ψ x‖
              ≤ max (max (-Real.log (‖Ψ ym‖ / 2)) 1) (-Real.log ‖Ψ x‖) :=
            le_max_right _ _
          linarith
      have hsup : sSup ((fun v => v x) '' greenFamily q) ≤ -Real.log ‖Ψ x‖ := by
        refine Real.sSup_le ?_ (by linarith)
        rintro t ⟨v, hv, rfl⟩
        have h1 := key _ (le_trans (le_max_left _ _) (le_max_left _ _)) hNpos v hv x hx
        rw [hΛval] at h1
        have h2 : (fun v : M → ℝ => v x) v = v x := rfl
        rw [h2]
        linarith
      exact hsup
  -- ## Step 4: instantiate the engine at the collision transplant `ψ = B_a ∘ φ`.
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = φ q₁ := ⟨_, rfl⟩
  have ha1 : ‖a‖ < 1 := by rw [ha]; exact hlt q₁
  have ha0 : a ≠ 0 := by rw [ha]; exact hne0 q₁ hq₁
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : M → ℂ,
      ψ = fun x => (φ x - a) / (1 - (starRingEnd ℂ) a * φ x) := ⟨_, rfl⟩
  have hφm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ y := fun y => hφ y
  have hψm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ y := by
    intro y
    rw [hψdef]
    exact (hBLA φ a hφm hlt ha1 y).2.2
  have hψlt : ∀ y, ‖ψ y‖ < 1 := by
    intro y
    rw [hψdef]
    exact (hBLA φ a hφm hlt ha1 y).2.1
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun y => (hψm y).continuousAt
  have hψq₁ : ψ q₁ = 0 := by
    simp only [hψdef]
    rw [← ha, sub_self, zero_div]
  have hψq₂ : ψ q₂ = 0 := by
    simp only [hψdef]
    have h2 : φ q₂ = a := by rw [ha, hq]
    rw [h2, sub_self, zero_div]
  have hψp₀ : ψ p₀ = -a := by
    simp only [hψdef, h0, mul_zero, sub_zero, zero_sub, div_one]
  have hψp₀ne : ψ p₀ ≠ 0 := by
    rw [hψp₀]
    exact neg_ne_zero.mpr ha0
  obtain ⟨hbdd₁, hb₁⟩ := MAIN q₁ ψ hψm hψlt hψq₁ ⟨p₀, hψp₀ne⟩
  -- Point-independence (A5b): the Green function at `q₁` exists.
  have hGF₁ : HasGreenFunction q₁ := ⟨p₀, Ne.symm hq₁, hbdd₁ p₀ (Ne.symm hq₁)⟩
  -- ## Step 5: swap the roles of the poles via the Green map at `q₁` (A6+A7 at `q₁`).
  obtain ⟨φ', hφ'sm, hφ'0, hφ'abs⟩ := exists_green_map hGF₁
  have hG₁pos := greenEnvelope_pos hGF₁
  have hφ'lt : ∀ y : M, ‖φ' y‖ < 1 := by
    intro y
    by_cases hy : y = q₁
    · rw [hy, hφ'0, norm_zero]; exact one_pos
    · rw [hφ'abs y hy]
      calc Real.exp (-(greenEnvelope q₁ y)) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith [hG₁pos y hy])
        _ = 1 := Real.exp_zero
  have hφ'm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ' y := fun y => hφ'sm y
  obtain ⟨a', ha'⟩ : ∃ b : ℂ, b = φ' p₀ := ⟨_, rfl⟩
  have ha'1 : ‖a'‖ < 1 := by rw [ha']; exact hφ'lt p₀
  have ha'norm : ‖a'‖ = Real.exp (-(greenEnvelope q₁ p₀)) := by
    rw [ha']
    exact hφ'abs p₀ (Ne.symm hq₁)
  have ha'0 : a' ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha'norm
    exact absurd ha'norm.symm (ne_of_gt (Real.exp_pos _))
  obtain ⟨ψ', hψ'def⟩ : ∃ g : M → ℂ,
      g = fun x => (φ' x - a') / (1 - (starRingEnd ℂ) a' * φ' x) := ⟨_, rfl⟩
  have hψ'm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ' y := by
    intro y
    rw [hψ'def]
    exact (hBLA φ' a' hφ'm hφ'lt ha'1 y).2.2
  have hψ'lt : ∀ y, ‖ψ' y‖ < 1 := by
    intro y
    rw [hψ'def]
    exact (hBLA φ' a' hφ'm hφ'lt ha'1 y).2.1
  have hψ'p₀ : ψ' p₀ = 0 := by
    simp only [hψ'def]
    rw [← ha', sub_self, zero_div]
  have hψ'q₁ : ψ' q₁ = -a' := by
    simp only [hψ'def, hφ'0, mul_zero, sub_zero, zero_sub, div_one]
  have hψ'q₁ne : ψ' q₁ ≠ 0 := by
    rw [hψ'q₁]
    exact neg_ne_zero.mpr ha'0
  obtain ⟨-, hb₀⟩ := MAIN p₀ ψ' hψ'm hψ'lt hψ'p₀ ⟨q₁, hψ'q₁ne⟩
  -- Evaluate the two comparisons: equality holds at the base point (symmetry byproduct).
  have hGq₁ : greenEnvelope p₀ q₁ = -Real.log ‖a‖ := by
    have h1 : ‖a‖ = Real.exp (-(greenEnvelope p₀ q₁)) := by
      rw [ha]
      exact habs q₁ hq₁
    rw [h1, Real.log_exp]
    ring
  have hswap : greenEnvelope p₀ q₁ ≤ greenEnvelope q₁ p₀ := by
    have h1 := hb₀ q₁ hq₁ hψ'q₁ne
    rw [hψ'q₁, norm_neg, ha'norm, Real.log_exp] at h1
    linarith
  have hfwd : greenEnvelope q₁ p₀ ≤ -Real.log ‖a‖ := by
    have h1 := hb₁ p₀ (Ne.symm hq₁) hψp₀ne
    rwa [hψp₀, norm_neg] at h1
  have heqp₀ : greenEnvelope q₁ p₀ + Real.log ‖ψ p₀‖ = 0 := by
    have h2 : -Real.log ‖a‖ ≤ greenEnvelope q₁ p₀ := by
      rw [← hGq₁]
      exact hswap
    have h3 : greenEnvelope q₁ p₀ = -Real.log ‖a‖ := le_antisymm hfwd h2
    rw [hψp₀, norm_neg, h3]
    ring
  -- ## Step 6: the extremality analysis — `G₁ + log‖ψ‖` vanishes identically.
  obtain ⟨u, hudef⟩ : ∃ u : M → ℝ,
      u = fun y => greenEnvelope q₁ y + Real.log ‖ψ y‖ := ⟨_, rfl⟩
  have hGE₁ := mharmonicOn_greenEnvelope hGF₁
  have huharm : ∀ x : M, ψ x ≠ 0 → MHarmonicAt u x := by
    intro x hx
    have hxq₁ : x ≠ q₁ := by
      intro hcon
      rw [hcon] at hx
      exact hx hψq₁
    have h1 : MHarmonicAt (greenEnvelope q₁) x := hGE₁.1 x hxq₁
    have h2 : MHarmonicAt (fun y => Real.log ‖ψ y‖) x := hlogM ψ hψm x hx
    have h3 := h1.add h2
    rw [hudef]
    exact h3
  have hule : ∀ x : M, ψ x ≠ 0 → u x ≤ 0 := by
    intro x hx
    have hxq₁ : x ≠ q₁ := by
      intro hcon
      rw [hcon] at hx
      exact hx hψq₁
    have h1 := hb₁ x hxq₁ hx
    rw [hudef]
    change greenEnvelope q₁ x + Real.log ‖ψ x‖ ≤ 0
    linarith
  have hup₀ : u p₀ = 0 := by
    rw [hudef]
    exact heqp₀
  -- The propagation set: `u` vanishes near the point, wherever `ψ ≠ 0`.
  obtain ⟨P, hPdef⟩ : ∃ P : Set M,
      P = {x : M | ∀ᶠ y in 𝓝 x, ψ y ≠ 0 → u y = 0} := ⟨_, rfl⟩
  have hPopen : IsOpen P := by
    rw [hPdef]
    exact isOpen_setOfPred_eventually_nhds
  -- The chart reading of `u` is subharmonic on plane sets avoiding the zero set.
  have hplane : ∀ (x : M) (S : Set ℂ), S ⊆ (chartAt ℂ x).target →
      (∀ w ∈ S, ψ ((chartAt ℂ x).symm w) ≠ 0) →
      SubharmonicOn (u ∘ (chartAt ℂ x).symm) S := by
    intro x S hSsub hSne
    refine HarmonicOnNhd.subharmonicOn ?_
    intro w hw
    have hwsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).map_target (hSsub hw)
    have h1 : MHarmonicAt u ((chartAt ℂ x).symm w) := huharm _ (hSne w hw)
    have h2 := (mharmonicAt_iff_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas x) hwsrc).mp h1
    rwa [(chartAt ℂ x).right_inv (hSsub hw)] at h2
  -- `P` is closed: vanishing propagates over chart balls and across isolated zeros.
  have hPclosed : IsClosed P := by
    refine isClosed_of_closure_subset fun x hx => ?_
    by_cases hxP : x ∈ P
    · exact hxP
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    by_cases hx0 : ψ x = 0
    · -- an isolated zero of `ψ`: propagate over the punctured chart ball
      obtain ⟨W1, hW1sub, hW1open, hxW1⟩ := _root_.mem_nhds_iff.mp
        (eventually_nhdsWithin_iff.mp (hisoM ψ hψm ⟨p₀, hψp₀ne⟩ x hx0))
      have hopen1 : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' W1) :=
        (chartAt ℂ x).isOpen_inter_preimage_symm hW1open
      have hmem1 : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹'
          W1 := by
        refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
        rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
        exact hxW1
      obtain ⟨s, hs, hssub⟩ := Metric.isOpen_iff.1 hopen1 _ hmem1
      have hSne : ∀ w ∈ ball (chartAt ℂ x x) s \ {chartAt ℂ x x},
          ψ ((chartAt ℂ x).symm w) ≠ 0 := by
        rintro w ⟨hwb, hwc⟩
        have h1 : (chartAt ℂ x).symm w ∈ W1 := (hssub hwb).2
        refine hW1sub h1 ?_
        intro hcon
        apply hwc
        rw [Set.mem_singleton_iff]
        have h2 : chartAt ℂ x ((chartAt ℂ x).symm w) = w :=
          (chartAt ℂ x).right_inv (hssub hwb).1
        rw [hcon] at h2
        exact h2.symm
      have hBopen : IsOpen
          ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s) :=
        (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
          isOpen_ball
      have hxB : x ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s :=
        ⟨hxsrc, by rw [Set.mem_preimage]; exact mem_ball_self hs⟩
      obtain ⟨p, hpB, hpP⟩ := _root_.mem_closure_iff.mp hx _ hBopen hxB
      have hpx : p ≠ x := by
        intro hcon
        rw [hcon] at hpP
        exact hxP hpP
      have hw₀S : chartAt ℂ x p ∈ ball (chartAt ℂ x x) s \ {chartAt ℂ x x} := by
        refine ⟨hpB.2, ?_⟩
        intro hcon
        rw [Set.mem_singleton_iff] at hcon
        exact hpx ((chartAt ℂ x).injOn hpB.1 hxsrc hcon)
      have hw₀0 : (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x p) = 0 := by
        have h1 : ψ p ≠ 0 := by
          have h2 := hSne (chartAt ℂ x p) hw₀S
          rwa [(chartAt ℂ x).left_inv hpB.1] at h2
        have hpP' : ∀ᶠ y in 𝓝 p, ψ y ≠ 0 → u y = 0 := by
          rw [hPdef] at hpP
          exact hpP
        have h3 : u p = 0 := hpP'.self_of_nhds h1
        change u ((chartAt ℂ x).symm (chartAt ℂ x p)) = 0
        rw [(chartAt ℂ x).left_inv hpB.1]
        exact h3
      have hall := hprop (ball (chartAt ℂ x x) s \ {chartAt ℂ x x})
        (u ∘ (chartAt ℂ x).symm) (isOpen_ball.sdiff isClosed_singleton)
        (hpunc (chartAt ℂ x x) s hs).isPreconnected
        (hplane x _ (fun w hw => (hssub hw.1).1) hSne)
        (fun w hw => hule _ (hSne w hw)) (chartAt ℂ x p) hw₀S hw₀0
      rw [hPdef]
      change ∀ᶠ y in 𝓝 x, ψ y ≠ 0 → u y = 0
      filter_upwards [hBopen.mem_nhds hxB] with y hy hy0
      by_cases hyx : y = x
      · exfalso
        rw [hyx] at hy0
        exact hy0 hx0
      · have h1 : chartAt ℂ x y ∈ ball (chartAt ℂ x x) s \ {chartAt ℂ x x} := by
          refine ⟨hy.2, ?_⟩
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hyx ((chartAt ℂ x).injOn hy.1 hxsrc hcon)
        have h2 := hall (chartAt ℂ x y) h1
        change u ((chartAt ℂ x).symm (chartAt ℂ x y)) = 0 at h2
        rwa [(chartAt ℂ x).left_inv hy.1] at h2
    · -- a nonvanishing point of `ψ`: propagate over a full chart ball
      have hopen1 : IsOpen
          ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {y : M | ψ y ≠ 0}) :=
        (chartAt ℂ x).isOpen_inter_preimage_symm
          (isOpen_compl_singleton.preimage hψc)
      have hmem1 : chartAt ℂ x x ∈
          (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {y : M | ψ y ≠ 0} := by
        refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
        rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
        exact hx0
      obtain ⟨s, hs, hssub⟩ := Metric.isOpen_iff.1 hopen1 _ hmem1
      have hSne : ∀ w ∈ ball (chartAt ℂ x x) s, ψ ((chartAt ℂ x).symm w) ≠ 0 :=
        fun w hw => (hssub hw).2
      have hBopen : IsOpen
          ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s) :=
        (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
          isOpen_ball
      have hxB : x ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s :=
        ⟨hxsrc, by rw [Set.mem_preimage]; exact mem_ball_self hs⟩
      obtain ⟨p, hpB, hpP⟩ := _root_.mem_closure_iff.mp hx _ hBopen hxB
      have hw₀0 : (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x p) = 0 := by
        have h1 : ψ p ≠ 0 := by
          have h2 := hSne (chartAt ℂ x p) hpB.2
          rwa [(chartAt ℂ x).left_inv hpB.1] at h2
        have hpP' : ∀ᶠ y in 𝓝 p, ψ y ≠ 0 → u y = 0 := by
          rw [hPdef] at hpP
          exact hpP
        have h3 : u p = 0 := hpP'.self_of_nhds h1
        change u ((chartAt ℂ x).symm (chartAt ℂ x p)) = 0
        rw [(chartAt ℂ x).left_inv hpB.1]
        exact h3
      have hall := hprop (ball (chartAt ℂ x x) s) (u ∘ (chartAt ℂ x).symm)
        isOpen_ball (convex_ball _ _).isPreconnected
        (hplane x _ (fun w hw => (hssub hw).1) hSne)
        (fun w hw => hule _ (hSne w hw)) (chartAt ℂ x p) hpB.2 hw₀0
      rw [hPdef]
      change ∀ᶠ y in 𝓝 x, ψ y ≠ 0 → u y = 0
      filter_upwards [hBopen.mem_nhds hxB] with y hy hy0
      have h2 := hall (chartAt ℂ x y) hy.2
      change u ((chartAt ℂ x).symm (chartAt ℂ x y)) = 0 at h2
      rwa [(chartAt ℂ x).left_inv hy.1] at h2
  -- `P` is nonempty: the strong maximum principle at the equality point `p₀`.
  have hPuniv : P = Set.univ := by
    refine IsClopen.eq_univ ⟨hPclosed, hPopen⟩ ⟨p₀, ?_⟩
    rw [hPdef]
    change ∀ᶠ y in 𝓝 p₀, ψ y ≠ 0 → u y = 0
    have hUopen : IsOpen {y : M | ψ y ≠ 0} := isOpen_compl_singleton.preimage hψc
    have hUsub : MSubharmonicOn u {y : M | ψ y ≠ 0} :=
      fun y hy => (huharm y hy).msubharmonicAt
    have hmax : ∀ y ∈ {y : M | ψ y ≠ 0}, u y ≤ u p₀ := by
      intro y hy
      rw [hup₀]
      exact hule y hy
    have hev := MSubharmonicAt.eventually_eq_of_le hUopen hψp₀ne hUsub hmax
    filter_upwards [hev] with y hy hy0
    rw [hy]
    exact hup₀
  -- ## Step 7: contradiction at the second collision point `q₂`.
  have hq₂P : q₂ ∈ P := by rw [hPuniv]; exact Set.mem_univ q₂
  rw [hPdef] at hq₂P
  have hq₂P' : ∀ᶠ y in 𝓝 q₂, ψ y ≠ 0 → u y = 0 := hq₂P
  have hG₁cont : ContinuousAt (greenEnvelope q₁) q₂ := (hGE₁.1 q₂ hq₂q₁).continuousAt
  have hE3 : ∀ᶠ y in 𝓝 q₂, greenEnvelope q₁ y < greenEnvelope q₁ q₂ + 1 :=
    hG₁cont.tendsto.eventually_lt_const (by linarith)
  have hE4 : ∀ᶠ y in 𝓝 q₂, ‖ψ y‖ < Real.exp (-(greenEnvelope q₁ q₂ + 1)) := by
    have h1 : ContinuousAt (fun y => ‖ψ y‖) q₂ := hψc.norm.continuousAt
    have h2 : ‖ψ q₂‖ = 0 := by rw [hψq₂, norm_zero]
    have h3 := h1.tendsto
    rw [h2] at h3
    exact h3.eventually_lt_const (Real.exp_pos _)
  have hE2 : ∀ᶠ y in 𝓝 q₂, y ∈ ({q₂}ᶜ : Set M) → ψ y ≠ 0 :=
    eventually_nhdsWithin_iff.mp (hisoM ψ hψm ⟨p₀, hψp₀ne⟩ q₂ hψq₂)
  obtain ⟨z, hzE, hzne⟩ := hpick q₂ _ (hq₂P'.and (hE3.and (hE4.and hE2)))
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hzE
  have hzψ : ψ z ≠ 0 := hz4 hzne
  have hzu : u z = 0 := hz1 hzψ
  have hzlog : Real.log ‖ψ z‖ < -(greenEnvelope q₁ q₂ + 1) := by
    have h1 := Real.log_lt_log (norm_pos_iff.mpr hzψ) hz3
    rwa [Real.log_exp] at h1
  have hzu' : u z < 0 := by
    rw [hudef]
    change greenEnvelope q₁ z + Real.log ‖ψ z‖ < 0
    linarith
  rw [hzu] at hzu'
  exact lt_irrefl 0 hzu'

/-- An injective holomorphic function on a connected surface is a
biholomorphism onto a plane domain. -/
theorem exists_diffeomorph_opens_complex_of_injective [ConnectedSpace M]
    {f : M → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hinj : Function.Injective f) :
    ∃ U : Opens ℂ, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  classical
  -- `M` has at least two points: pull two points of a chart target back to `M`.
  obtain ⟨p⟩ : Nonempty M := inferInstance
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp (chartAt ℂ p).open_target (chartAt
      ℂ p p)
    ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have hcmem : chartAt ℂ p p + ((r₀ / 2 : ℝ) : ℂ) ∈ (chartAt ℂ p).target := by
    apply hball₀
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hpq : p ≠ (chartAt ℂ p).symm (chartAt ℂ p p + ((r₀ / 2 : ℝ) : ℂ)) := by
    intro heqp
    have h2 := congrArg (⇑(chartAt ℂ p)) heqp
    rw [(chartAt ℂ p).right_inv hcmem] at h2
    have h3 : ((r₀ / 2 : ℝ) : ℂ) = 0 := by
      have h4 : chartAt ℂ p p + ((r₀ / 2 : ℝ) : ℂ) = chartAt ℂ p p + 0 := by
        rw [add_zero]; exact h2.symm
      exact add_left_cancel h4
    rw [Complex.ofReal_eq_zero] at h3
    linarith
  -- An injective map on a space with two points is nonconstant, hence open.
  have hnc : ¬ ∃ c, ∀ x, f x = c := by
    rintro ⟨c, hc⟩
    exact hpq (hinj ((hc p).trans (hc _).symm))
  have hopen : IsOpenMap f := isOpenMap_of_contMDiff_of_not_const hf hnc
  -- The image domain and the two structure maps.
  let U : Opens ℂ := ⟨Set.range f, hopen.isOpen_range⟩
  -- Forward smoothness: the range restriction of `f`.
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun x : M => (⟨f x, Set.mem_range_self x⟩ : ↥U)) := by
    intro x
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (Subtype.val ∘ fun x : M => (⟨f x, Set.mem_range_self x⟩ : ↥U)) x := hf.contMDiffAt
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  -- Inverse smoothness: read the inverse in a chart around the preimage point,
  -- where it is the local inverse of the injective analytic chart reading of `f`.
  have hG : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun y : ↥U => Function.invFun f (y : ℂ)) := by
    intro y₀
    obtain ⟨x₀, hfx₀⟩ : ∃ x, f x = (y₀ : ℂ) := y₀.2
    obtain ⟨φ, hx₀src, hmax⟩ : ∃ φ : OpenPartialHomeomorph M ℂ,
        x₀ ∈ φ.source ∧ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M :=
      ⟨chartAt ℂ x₀, mem_chart_source ℂ x₀, IsManifold.chart_mem_maximalAtlas x₀⟩
    have hw₀tgt : φ x₀ ∈ φ.target := φ.map_source hx₀src
    -- The chart reading of `f` is analytic and injective on the chart target.
    have hgan : ∀ w ∈ φ.target, AnalyticAt ℂ (f ∘ ⇑φ.symm) w := by
      intro w hw
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑φ.symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas hmax hw
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f ∘ ⇑φ.symm) w :=
        ContMDiffAt.comp w hf.contMDiffAt h1
      exact (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
    have hginj : Set.InjOn (f ∘ ⇑φ.symm) φ.target := by
      intro w₁ h₁ w₂ h₂ hgw
      have h3 : φ.symm w₁ = φ.symm w₂ := hinj hgw
      have h4 := congrArg (⇑φ) h3
      rwa [φ.right_inv h₁, φ.right_inv h₂] at h4
    obtain ⟨r, hr, hBsub⟩ := Metric.isOpen_iff.mp φ.open_target (φ x₀) hw₀tgt
    -- The inverse chart reading.
    let η : ℂ → ℂ := fun ζ => φ (Function.invFun f ζ)
    have hηg : ∀ w ∈ ball (φ x₀) r, η (f (φ.symm w)) = w := by
      intro w hwB
      have h5 : Function.invFun f (f (φ.symm w)) = φ.symm w :=
        Function.leftInverse_invFun hinj (φ.symm w)
      change φ (Function.invFun f (f (φ.symm w))) = w
      rw [h5]
      exact φ.right_inv (hBsub hwB)
    -- The image `W` of the coordinate ball, an open neighborhood of `y₀`.
    have hWopen : IsOpen (f '' (⇑φ.symm '' ball (φ x₀) r)) :=
      hopen _ (φ.isOpen_image_symm_of_subset_target isOpen_ball hBsub)
    have hy₀W : (y₀ : ℂ) ∈ f '' (⇑φ.symm '' ball (φ x₀) r) :=
      ⟨x₀, ⟨φ x₀, mem_ball_self hr, φ.left_inv hx₀src⟩, hfx₀⟩
    have himg : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r),
        ∃ w ∈ ball (φ x₀) r, f (φ.symm w) = ζ := by
      rintro ζ ⟨x, ⟨w, hwB, rfl⟩, rfl⟩
      exact ⟨w, hwB, rfl⟩
    have hgη : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), f (φ.symm (η ζ)) = ζ := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
    have hηB : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), η ζ ∈ ball (φ x₀) r := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
      exact hwB
    -- Continuity of the inverse reading, from openness of `f`.
    have hηc : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), ContinuousAt η ζ := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      have hgoal : Filter.Tendsto η (𝓝 (f (φ.symm w))) (𝓝 w) := by
        rw [Filter.tendsto_def]
        intro N hN
        obtain ⟨N', hN'sub, hN'open, hwN'⟩ :=
          _root_.mem_nhds_iff.mp (Filter.inter_mem hN (isOpen_ball.mem_nhds hwB))
        have hsub' : N' ⊆ φ.target := fun z hz => hBsub (hN'sub hz).2
        have hopenimg : IsOpen (f '' (⇑φ.symm '' N')) :=
          hopen _ (φ.isOpen_image_symm_of_subset_target hN'open hsub')
        have hgmem : f (φ.symm w) ∈ f '' (⇑φ.symm '' N') := ⟨φ.symm w, ⟨w, hwN', rfl⟩,
            rfl⟩
        refine Filter.mem_of_superset (hopenimg.mem_nhds hgmem) ?_
        rintro ζ' ⟨x', ⟨w', hw'N', rfl⟩, rfl⟩
        rw [Set.mem_preimage, hηg w' (hN'sub hw'N').2]
        exact (hN'sub hw'N').1
      have hηw : η (f (φ.symm w)) = w := hηg w hwB
      change Filter.Tendsto η (𝓝 (f (φ.symm w))) (𝓝 (η (f (φ.symm w))))
      rw [hηw]
      exact hgoal
    -- Differentiability of the inverse reading at noncritical values.
    have hd_nc : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r),
        deriv (f ∘ ⇑φ.symm) (η ζ) ≠ 0 → DifferentiableAt ℂ η ζ := by
      intro ζ hζ hder
      have hfd : HasDerivAt (f ∘ ⇑φ.symm) (deriv (f ∘ ⇑φ.symm) (η ζ)) (η ζ) :=
        ((hgan (η ζ) (hBsub (hηB ζ hζ))).differentiableAt).hasDerivAt
      have hev : ∀ᶠ ζ' in 𝓝 ζ, (f ∘ ⇑φ.symm) (η ζ') = ζ' := by
        filter_upwards [hWopen.mem_nhds hζ] with ζ' hζ' using hgη ζ' hζ'
      exact (HasDerivAt.of_local_left_inverse (hηc ζ hζ) hfd hder hev).differentiableAt
    -- Critical points of the chart reading are isolated (injectivity).
    have hganN : AnalyticOnNhd ℂ (f ∘ ⇑φ.symm) φ.target := fun w hw => hgan w hw
    have hcrit : ∀ w ∈ φ.target, ∀ᶠ w' in 𝓝[≠] w, deriv (f ∘ ⇑φ.symm) w' ≠
        0 := by
      intro w hw
      rcases (hganN.deriv w hw).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · exfalso
        obtain ⟨ρ, hρ0, hballρ⟩ :=
          Metric.eventually_nhds_iff_ball.mp (h0.and (φ.open_target.eventually_mem hw))
        have hconst : ∀ w' ∈ ball w ρ, (f ∘ ⇑φ.symm) w' = (f ∘ ⇑φ.symm) w := by
          intro w' hw'
          refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball w ρ)
            (fun q hq => ((hgan q (hballρ q hq).2).differentiableAt).differentiableWithinAt)
            ?_ hw' (mem_ball_self hρ0)
          intro q hq
          rw [fderivWithin_of_isOpen isOpen_ball hq]
          refine ContinuousLinearMap.ext_ring ?_
          rw [fderiv_apply_one_eq_deriv, (hballρ q hq).1]
          simp
        have hmem : w + ((ρ / 2 : ℝ) : ℂ) ∈ ball w ρ := by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith
        have heq2 : w + ((ρ / 2 : ℝ) : ℂ) = w :=
          hginj (hballρ _ hmem).2 hw (hconst _ hmem)
        have hρ2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
          have h4 : w + ((ρ / 2 : ℝ) : ℂ) = w + 0 := by rw [add_zero]; exact heq2
          exact add_left_cancel h4
        rw [Complex.ofReal_eq_zero] at hρ2
        linarith
      · exact hne
    -- Differentiability everywhere on `W` (removable singularity at critical values).
    have hdiff : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), DifferentiableAt ℂ η ζ := by
      intro ζ hζ
      by_cases hder : deriv (f ∘ ⇑φ.symm) (η ζ) = 0
      swap
      · exact hd_nc ζ hζ hder
      obtain ⟨ρ, hρ0, hballρ⟩ := Metric.eventually_nhds_iff_ball.mp
        ((eventually_nhdsWithin_iff.mp (hcrit (η ζ) (hBsub (hηB ζ hζ)))).and
          (isOpen_ball.eventually_mem (hηB ζ hζ)))
      have hsub' : ball (η ζ) ρ ⊆ φ.target := fun z hz => hBsub (hballρ z hz).2
      have hW'open : IsOpen (f '' (⇑φ.symm '' ball (η ζ) ρ)) :=
        hopen _ (φ.isOpen_image_symm_of_subset_target isOpen_ball hsub')
      have hζW' : ζ ∈ f '' (⇑φ.symm '' ball (η ζ) ρ) :=
        ⟨φ.symm (η ζ), ⟨η ζ, mem_ball_self hρ0, rfl⟩, hgη ζ hζ⟩
      have hW'W : f '' (⇑φ.symm '' ball (η ζ) ρ) ⊆ f '' (⇑φ.symm '' ball (φ x₀)
          r) := by
        rintro ζ' ⟨x', ⟨w', hw', rfl⟩, rfl⟩
        exact ⟨φ.symm w', ⟨w', (hballρ w' hw').2, rfl⟩, rfl⟩
      have hoff : DifferentiableOn ℂ η (f '' (⇑φ.symm '' ball (η ζ) ρ) \ {ζ}) := by
        rintro ζ' ⟨hζ'W', hζ'ne⟩
        obtain ⟨x', ⟨w', hw'ball, rfl⟩, rfl⟩ := hζ'W'
        refine (hd_nc _ (hW'W ⟨φ.symm w', ⟨w', hw'ball, rfl⟩, rfl⟩)
            ?_).differentiableWithinAt
        rw [hηg w' (hballρ w' hw'ball).2]
        refine (hballρ w' hw'ball).1 ?_
        intro hmem
        apply hζ'ne
        rw [Set.mem_singleton_iff] at hmem ⊢
        rw [hmem]
        exact hgη ζ hζ
      have hW'diff : DifferentiableOn ℂ η (f '' (⇑φ.symm '' ball (η ζ) ρ)) :=
        (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
          (hW'open.mem_nhds hζW')).mp ⟨hoff, hηc ζ hζ⟩
      exact hW'diff.differentiableAt (hW'open.mem_nhds hζW')
    -- The inverse reading is analytic at the base point; assemble the smooth composite.
    have hWdiff : DifferentiableOn ℂ η (f '' (⇑φ.symm '' ball (φ x₀) r)) :=
      fun ζ hζ => (hdiff ζ hζ).differentiableWithinAt
    have hηan : AnalyticAt ℂ η (y₀ : ℂ) := (hWdiff.analyticOnNhd hWopen) _ hy₀W
    have hval : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : ↥U → ℂ) y₀ :=
      contMDiff_subtype_val.contMDiffAt
    have hηsm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω η ((y₀ : ℂ)) :=
      contMDiffAt_iff_contDiffAt.mpr hηan.contDiffAt
    have hφsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑φ.symm) (η (y₀ : ℂ)) :=
      contMDiffAt_symm_of_mem_maximalAtlas hmax (hBsub (hηB _ hy₀W))
    have hcomp2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((⇑φ.symm ∘ η) ∘ (Subtype.val : ↥U
        → ℂ)) y₀ :=
      ContMDiffAt.comp y₀ (ContMDiffAt.comp ((y₀ : ℂ)) hφsymm hηsm) hval
    refine hcomp2.congr_of_eventuallyEq ?_
    have hmemW : (Subtype.val : ↥U → ℂ) ⁻¹' (f '' (⇑φ.symm '' ball (φ x₀) r)) ∈
        𝓝 y₀ :=
      (hWopen.preimage continuous_subtype_val).mem_nhds hy₀W
    filter_upwards [hmemW] with y hy
    obtain ⟨x, ⟨w, hwB, rfl⟩, hfy⟩ := hy
    change Function.invFun f (y : ℂ) = φ.symm (η (y : ℂ))
    have h6 : η (y : ℂ) = w := by
      rw [← hfy]
      exact hηg w hwB
    rw [h6, ← hfy, Function.leftInverse_invFun hinj (φ.symm w)]
  exact ⟨U, ⟨{
    toFun := fun x => ⟨f x, Set.mem_range_self x⟩
    invFun := fun y => Function.invFun f (y : ℂ)
    left_inv := fun x => Function.leftInverse_invFun hinj x
    right_inv := fun y => Subtype.ext (Function.invFun_eq y.2)
    contMDiff_toFun := hF
    contMDiff_invFun := hG }⟩⟩

/-- **The hyperbolic case of planarity**: a simply connected surface carrying
a Green's function embeds onto a domain of the Riemann sphere. -/
theorem exists_diffeomorph_opens_of_hasGreenFunction [T2Space M] [SimplyConnectedSpace M]
    [NoncompactSpace M] {p₀ : M} (hG : HasGreenFunction p₀) :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  have : ConnectedSpace M := PathConnectedSpace.connectedSpace
  obtain ⟨φ, hφ, h0, habs⟩ := exists_green_map hG
  have hinj : Function.Injective φ := injective_green_map hG hφ h0 habs
  obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_complex_of_injective hφ hinj
  let V : Opens ℂ̂ :=
    ⟨((↑) : ℂ → ℂ̂) '' (U : Set ℂ),
      OnePoint.isOpenEmbedding_coe.isOpenMap _ U.isOpen⟩
  have hinfty : OnePoint.infty ∉ (V : Set ℂ̂) := by
    rintro ⟨w, -, hw⟩
    exact OnePoint.coe_ne_infty w hw
  obtain ⟨W, hWimg, ⟨e₂⟩⟩ := exists_diffeomorph_opens_planar V hinfty
  have hWU : W = U := by
    apply Opens.ext
    have himg : ((↑) : ℂ → ℂ̂) '' (W : Set ℂ) = ((↑) : ℂ → ℂ̂) '' (U : Set ℂ)
        :=
      hWimg
    exact Set.image_injective.mpr OnePoint.coe_injective himg
  subst hWU
  exact ⟨V, ⟨e.trans e₂.symm⟩⟩

end RiemannDynamics
