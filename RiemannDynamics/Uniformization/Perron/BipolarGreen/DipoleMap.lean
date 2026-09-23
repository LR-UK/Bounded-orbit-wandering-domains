/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.Limit

/-!
# Bipolar Green: the dipole map

`exists_bipolar_map`: on a simply connected surface the bipolar Green's
function integrates, globalized by monodromy, to a holomorphic map to the
sphere with a simple zero at `p₁` and a pole at `p₂`, of modulus
`e^{−G}` elsewhere.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- **The dipole map**: on a simply connected surface the bipolar Green's
function integrates to a holomorphic map to the sphere with a simple zero at
`p₁` and a pole at `p₂`, of modulus `e^{−G}` elsewhere. -/
theorem exists_bipolar_map [SimplyConnectedSpace M]
    {p₁ p₂ : M} (hne : p₁ ≠ p₂) {G : M → ℝ} (hG : MHarmonicOn G ({p₁, p₂}ᶜ))
    (hpole₁ : ∃ r > 0, ball (chartAt ℂ p₁ p₁) r ⊆ (chartAt ℂ p₁).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₁ p₁) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₁ p₁) r \ {chartAt ℂ p₁ p₁},
          h w = G ((chartAt ℂ p₁).symm w) + Real.log ‖w - chartAt ℂ p₁ p₁‖)
    (hpole₂ : ∃ r > 0, ball (chartAt ℂ p₂ p₂) r ⊆ (chartAt ℂ p₂).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₂ p₂) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₂ p₂) r \ {chartAt ℂ p₂ p₂},
          h w = G ((chartAt ℂ p₂).symm w) - Real.log ‖w - chartAt ℂ p₂ p₂‖) :
    ∃ φ : M → ℂ̂, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ ∧ φ p₁ = ((0 : ℂ) : ℂ̂) ∧
      φ p₂ = OnePoint.infty ∧
      ∀ x : M, x ≠ p₁ → x ≠ p₂ →
        ∃ w : ℂ, φ x = (w : ℂ̂) ∧ ‖w‖ = Real.exp (-(G x)) := by
  classical
  -- ## §0 Plane bricks: punctured-ball connectivity and constant-ratio rigidity.
  have hpunc : ∀ (c : ℂ) (r : ℝ), 0 < r → IsPreconnected (ball c r \ {c}) := by
    intro c r hr
    have hcont : Continuous fun p : ℝ × ℝ ↦
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ ↦ c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
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
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn
  have hcore : ∀ (f g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ), 0 < ρ →
      AnalyticOnNhd ℂ f (ball z₀ ρ) → AnalyticOnNhd ℂ g (ball z₀ ρ) →
      (∀ w ∈ ball z₀ ρ, ‖f w‖ = ‖g w‖) →
      (∀ w ∈ ball z₀ ρ, w ≠ z₀ → g w ≠ 0) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ Set.EqOn f (fun w ↦ c * g w) (ball z₀ ρ) := by
    intro f g z₀ ρ hρ hf hg hnorm hgne
    set U : Set ℂ := ball z₀ ρ \ {z₀} with hU
    have hUopen : IsOpen U := isOpen_ball.sdiff isClosed_singleton
    have hUconn : IsPreconnected U := hpunc z₀ ρ hρ
    set z₁ : ℂ := z₀ + ((ρ / 2 : ℝ) : ℂ) with hz₁
    have hz₁U : z₁ ∈ U := by
      constructor
      · rw [mem_ball, dist_eq_norm, hz₁, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
        linarith
      · intro h
        rw [Set.mem_singleton_iff, hz₁, add_eq_left] at h
        have h2 : (ρ / 2 : ℝ) = 0 := by exact_mod_cast h
        linarith
    have hgU : ∀ w ∈ U, g w ≠ 0 := fun w hw ↦ hgne w hw.1 hw.2
    have hr : AnalyticOnNhd ℂ (f / g) U := fun w hw ↦
      (hf w hw.1).div (hg w hw.1) (hgU w hw)
    have hrnorm : ∀ w ∈ U, ‖(f / g) w‖ = 1 := by
      intro w hw
      rw [Pi.div_apply, norm_div, hnorm w hw.1,
        div_self (norm_ne_zero_iff.mpr (hgU w hw))]
    rcases (hr z₁ hz₁U).eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · -- the ratio is constant on the punctured ball
      have heq : Set.EqOn (f / g) (fun _ ↦ (f / g) z₁) U :=
        hr.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUconn hz₁U hconst
      refine ⟨(f / g) z₁, hrnorm z₁ hz₁U, ?_⟩
      have hEqU : ∀ w ∈ U, f w = (f / g) z₁ * g w := by
        intro w hw
        have h1 := heq hw
        rw [Pi.div_apply, div_eq_iff (hgU w hw)] at h1
        exact h1
      intro w hw
      by_cases hwz : w = z₀
      · have hz₀b : z₀ ∈ ball z₀ ρ := mem_ball_self hρ
        have hfc : Filter.Tendsto f (𝓝[U] z₀) (𝓝 (f z₀)) :=
          ((hf z₀ hz₀b).continuousAt).continuousWithinAt
        have hgc : Filter.Tendsto (fun v ↦ (f / g) z₁ * g v) (𝓝[U] z₀)
            (𝓝 ((f / g) z₁ * g z₀)) :=
          (continuousAt_const.mul (hg z₀ hz₀b).continuousAt).continuousWithinAt
        have : (𝓝[U] z₀).NeBot := by
          have h2 : U = {z₀}ᶜ ∩ ball z₀ ρ := by rw [hU, Set.sdiff_eq, Set.inter_comm]
          rw [h2,
            nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz₀b))]
          exact Module.punctured_nhds_neBot ℝ ℂ z₀
        have h5 : f =ᶠ[𝓝[U] z₀] fun v ↦ (f / g) z₁ * g v :=
          eventually_nhdsWithin_of_forall hEqU
        have hcenter := tendsto_nhds_unique (hfc.congr' h5) hgc
        rw [hwz]
        exact hcenter
      · exact hEqU w ⟨hw, hwz⟩
    · -- open image: impossible for a map into the unit circle
      exfalso
      have hUnh : U ∈ 𝓝 z₁ := hUopen.mem_nhds hz₁U
      have himg : (f / g) '' U ∈ 𝓝 ((f / g) z₁) := hopen (Filter.image_mem_map hUnh)
      obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp himg
      have hwS : ((1 + δ / 2 : ℝ) : ℂ) * (f / g) z₁ ∈ ball ((f / g) z₁) δ := by
        rw [mem_ball, dist_eq_norm]
        have h1 : ((1 + δ / 2 : ℝ) : ℂ) * (f / g) z₁ - (f / g) z₁ =
            ((δ / 2 : ℝ) : ℂ) * (f / g) z₁ := by
          push_cast
          ring
        rw [h1, norm_mul, Complex.norm_real, hrnorm z₁ hz₁U, mul_one,
          Real.norm_of_nonneg (by linarith)]
        linarith
      obtain ⟨u, huU, huw⟩ := hball hwS
      have h6 : ‖(f / g) u‖ = 1 := hrnorm u huU
      rw [huw, norm_mul, Complex.norm_real, hrnorm z₁ hz₁U, mul_one,
        Real.norm_of_nonneg (by linarith)] at h6
      linarith
  -- ## §0b Sphere toolkit: charts, values, inverses, and Möbius scalings.
  have hpolesopen : IsOpen ({p₁, p₂}ᶜ : Set M) := by
    rw [isOpen_compl_iff, Set.insert_eq]
    exact isClosed_singleton.union isClosed_singleton
  have hpolemem : ∀ y : M, y ∈ ({p₁, p₂}ᶜ : Set M) ↔ y ≠ p₁ ∧ y ≠ p₂ := by
    intro y
    rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hfinrec : ∀ z : ℂ̂, z ≠ OnePoint.infty → z = ((sphereChartFinite z : ℂ) : ℂ̂)
      := by
    intro z hz
    cases z with
    | infty => exact absurd rfl hz
    | coe w => rw [sphereChartFinite_coe]
  have hIapp_coe : ∀ w : ℂ, w ≠ 0 → sphereChartInfty ((w : ℂ̂)) = w⁻¹ := by
    intro w hw
    rw [sphereChartInfty_apply, inversionGL_smul_coe, ite_eq_right hw, sphereChartFinite_coe]
  have hIapp_infty : sphereChartInfty (OnePoint.infty : ℂ̂) = 0 := by
    rw [sphereChartInfty_apply, inversionGL_smul_infty, sphereChartFinite_coe]
  have hITmem : ∀ w : ℂ, w ∈ sphereChartInfty.target := by
    intro w
    have hz : (inversionGL • ((w : ℂ̂))) ∈ sphereChartInfty.source := by
      rw [sphereChartInfty_source, inversionGL_smul_coe]
      by_cases hw : w = 0
      · rw [ite_eq_left hw]
        exact OnePoint.infty_ne_coe 0
      · rw [ite_eq_right hw]
        intro hcon
        exact hw (by simpa [inv_eq_zero] using OnePoint.coe_eq_coe.mp hcon)
    have h2 : sphereChartInfty (inversionGL • ((w : ℂ̂))) = w := by
      rw [sphereChartInfty_apply, inversionGL_smul_smul, sphereChartFinite_coe]
    have h3 := sphereChartInfty.map_source hz
    rwa [h2] at h3
  have hISmem : ∀ z : ℂ̂, z ≠ ((0 : ℂ) : ℂ̂) → z ∈ sphereChartInfty.source := by
    intro z hz
    rw [sphereChartInfty_source]
    exact hz
  have hFmem : ∀ z : ℂ̂, z ≠ OnePoint.infty → z ∈ sphereChartFinite.source := by
    intro z hz
    rw [sphereChartFinite_source]
    exact hz
  have hatlasF : sphereChartFinite ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.subset_maximalAtlas (Set.mem_insert _ _)
  have hatlasI : sphereChartInfty ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.subset_maximalAtlas (Set.mem_insert_of_mem _ rfl)
  have hcoeSm : ∀ w : ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun v : ℂ ↦ ((v : ℂ) : ℂ̂))
      w := by
    intro w
    have h1 : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω sphereChartFinite.symm sphereChartFinite.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hatlasF
    have h2 : sphereChartFinite.target ∈ 𝓝 w := by
      rw [show sphereChartFinite.target = Set.univ from rfl]
      exact Filter.univ_mem
    refine (h1.contMDiffAt h2).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun v ↦ (sphereChartFinite_symm_apply v).symm
  have hIsymmSm : ∀ w : ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereChartInfty.symm w := by
    intro w
    exact (contMDiffOn_symm_of_mem_maximalAtlas hatlasI).contMDiffAt
      (sphereChartInfty.open_target.mem_nhds (hITmem w))
  have hFSm : ∀ z : ℂ̂, z ≠ OnePoint.infty →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereChartFinite z := by
    intro z hz
    exact (contMDiffOn_of_mem_maximalAtlas hatlasF).contMDiffAt
      (sphereChartFinite.open_source.mem_nhds (hFmem z hz))
  have hISm : ∀ z : ℂ̂, z ≠ ((0 : ℂ) : ℂ̂) →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereChartInfty z := by
    intro z hz
    exact (contMDiffOn_of_mem_maximalAtlas hatlasI).contMDiffAt
      (sphereChartInfty.open_source.mem_nhds (hISmem z hz))
  have hmulCex : ∀ c : ℂ, c ≠ 0 → ∃ mc : ℂ̂ → ℂ̂, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      mc ∧
      (∀ w : ℂ, mc ((w : ℂ̂)) = ((c * w : ℂ) : ℂ̂)) ∧
      mc OnePoint.infty = OnePoint.infty := by
    intro c hc
    have hdet : (!![c, 0; 0, (1 : ℂ)]).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      simpa using hc
    obtain ⟨e, he⟩ := exists_gl_smul_diffeomorph
      (Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet)
    refine ⟨fun z ↦ Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet • z,
      ?_, ?_, ?_⟩
    · rw [← he]
      exact e.contMDiff
    · intro w
      change Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet •
        ((w : ℂ̂)) = ((c * w : ℂ) : ℂ̂)
      rw [OnePoint.smul_some_eq_ite]
      norm_num
    · change Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet •
        (OnePoint.infty : ℂ̂) = OnePoint.infty
      rw [OnePoint.smul_infty_eq_ite]
      norm_num
  choose! mulC hmulCsm hmulCco hmulCinf using hmulCex
  have hmulC1 : ∀ z : ℂ̂, mulC 1 z = z := by
    intro z
    cases z with
    | infty => exact hmulCinf 1 one_ne_zero
    | coe w => rw [hmulCco 1 one_ne_zero w, one_mul]
  -- ## §1 The pointwise element predicate and its stability.
  obtain ⟨Q, hQ⟩ : ∃ Q : (M → ℂ̂) → M → Prop, ∀ ψ x, Q ψ x ↔
      (ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ x ∧
        (x ≠ p₁ → x ≠ p₂ → ∃ w : ℂ, ψ x = ((w : ℂ) : ℂ̂) ∧
          ‖w‖ = Real.exp (-(G x))) ∧
        (x = p₁ → ψ x = ((0 : ℂ) : ℂ̂)) ∧ (x = p₂ → ψ x = OnePoint.infty)) :=
    ⟨_, fun _ _ ↦ Iff.rfl⟩
  have hfin : ∀ (ψ : M → ℂ̂) (y : M), Q ψ y → y ≠ p₂ → ψ y ≠ OnePoint.infty := by
    intro ψ y hq hy2
    rw [hQ] at hq
    by_cases hy1 : y = p₁
    · rw [hq.2.2.1 hy1]
      exact OnePoint.coe_ne_infty 0
    · obtain ⟨w, hw1, -⟩ := hq.2.1 hy1 hy2
      rw [hw1]
      exact OnePoint.coe_ne_infty w
  have hne0 : ∀ (ψ : M → ℂ̂) (y : M), Q ψ y → y ≠ p₁ → ψ y ≠ ((0 : ℂ) : ℂ̂)
      := by
    intro ψ y hq hy1
    rw [hQ] at hq
    by_cases hy2 : y = p₂
    · rw [hq.2.2.2 hy2]
      exact OnePoint.infty_ne_coe 0
    · obtain ⟨w, hw1, hw2⟩ := hq.2.1 hy1 hy2
      rw [hw1]
      intro hcon
      have hw0 : w = 0 := OnePoint.coe_eq_coe.mp hcon
      rw [hw0, norm_zero] at hw2
      exact absurd hw2.symm (ne_of_gt (Real.exp_pos _))
  have hreadFin : ∀ (ψ : M → ℂ̂) (x₀ : M), ∀ z ∈ (chartAt ℂ x₀).target,
      ψ ((chartAt ℂ x₀).symm z) ≠ OnePoint.infty →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ ((chartAt ℂ x₀).symm z) →
      AnalyticAt ℂ (fun w ↦ sphereChartFinite (ψ ((chartAt ℂ x₀).symm w))) z := by
    intro ψ x₀ z hz hnei hψ
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x₀).symm z :=
      contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x₀).open_target.mem_nhds hz)
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun w ↦ sphereChartFinite (ψ ((chartAt ℂ x₀).symm w))) z :=
      (hFSm _ hnei).comp z (hψ.comp z hsymm)
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).analyticAt
  have hreadInf : ∀ (ψ : M → ℂ̂) (x₀ : M), ∀ z ∈ (chartAt ℂ x₀).target,
      ψ ((chartAt ℂ x₀).symm z) ≠ ((0 : ℂ) : ℂ̂) →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ ((chartAt ℂ x₀).symm z) →
      AnalyticAt ℂ (fun w ↦ sphereChartInfty (ψ ((chartAt ℂ x₀).symm w))) z := by
    intro ψ x₀ z hz hnez hψ
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x₀).symm z :=
      contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x₀).open_target.mem_nhds hz)
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun w ↦ sphereChartInfty (ψ ((chartAt ℂ x₀).symm w))) z :=
      (hISm _ hnez).comp z (hψ.comp z hsymm)
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).analyticAt
  have hQsmul : ∀ (c : ℂ), ‖c‖ = 1 → ∀ (ψ : M → ℂ̂) (y : M), Q ψ y →
      Q (fun z ↦ mulC c (ψ z)) y := by
    intro c hc ψ y hq
    have hc0 : c ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hc
      exact one_ne_zero hc.symm
    rw [hQ] at hq ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hq
    refine ⟨((hmulCsm c hc0).contMDiffAt).comp y h1, ?_, ?_, ?_⟩
    · intro hy1 hy2
      obtain ⟨w, hw1, hw2⟩ := h2 hy1 hy2
      refine ⟨c * w, ?_, ?_⟩
      · rw [hw1]
        exact hmulCco c hc0 w
      · rw [norm_mul, hc, one_mul]
        exact hw2
    · intro hy
      rw [h3 hy, hmulCco c hc0 0, mul_zero]
    · intro hy
      rw [h4 hy, hmulCinf c hc0]
  have hEtrans : ∀ (ψ ψ' : M → ℂ̂) (x : M), (∀ᶠ y in 𝓝 x, Q ψ y) → ψ' =ᶠ[𝓝
      x] ψ →
      ∀ᶠ y in 𝓝 x, Q ψ' y := by
    intro ψ ψ' x hE heq
    obtain ⟨W, hWnh, hWeq⟩ := eventuallyEq_iff_exists_mem.mp heq
    obtain ⟨W', hW'sub, hW'open, hxW'⟩ := mem_nhds_iff.mp hWnh
    filter_upwards [hE, hW'open.mem_nhds hxW'] with y hy hyW'
    rw [hQ] at hy ⊢
    have heqy : ψ' =ᶠ[𝓝 y] ψ :=
      eventuallyEq_of_mem (hW'open.mem_nhds hyW') (fun z hz ↦ hWeq (hW'sub hz))
    refine ⟨hy.1.congr_of_eventuallyEq heqy, fun h1 h2 ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨w, hw1, hw2⟩ := hy.2.1 h1 h2
      exact ⟨w, by rw [hWeq (hW'sub hyW')]; exact hw1, hw2⟩
    · rw [hWeq (hW'sub hyW')]
      exact hy.2.2.1 h
    · rw [hWeq (hW'sub hyW')]
      exact hy.2.2.2 h
  -- ## §2 Existence of local elements: generic, zero-pole, and infinity-pole types.
  have helt : ∀ x : M, ∃ ψ : M → ℂ̂, ∀ᶠ y in 𝓝 x, Q ψ y := by
    intro x
    by_cases hx1 : x = p₁
    · -- the zero element `(z - c₁) e^{-F z}` read through the chart at `p₁`
      subst hx1
      obtain ⟨r, hr0, hrsub, h, hharm, hhval⟩ := hpole₁
      set e := chartAt ℂ x with he
      set c₁ : ℂ := e x with hc₁
      have hxs : x ∈ e.source := mem_chart_source ℂ x
      obtain ⟨F, hFa, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
      refine ⟨fun y ↦ (((e y - c₁) * Complex.exp (-F (e y)) : ℂ) : ℂ̂), ?_⟩
      have hVopen : IsOpen (e.source ∩ e ⁻¹' ball c₁ r ∩ {p₂}ᶜ) :=
        (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).inter
          isOpen_compl_singleton
      have hxV : x ∈ e.source ∩ e ⁻¹' ball c₁ r ∩ {p₂}ᶜ := by
        refine ⟨⟨hxs, ?_⟩, hne⟩
        rw [Set.mem_preimage, ← hc₁]
        exact mem_ball_self hr0
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      obtain ⟨⟨hys, hyb'⟩, hyp2⟩ := hy
      have hyb : e y ∈ ball c₁ r := hyb'
      have hyp2' : y ≠ p₂ := hyp2
      rw [hQ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have houter : AnalyticAt ℂ (fun w : ℂ ↦ (w - c₁) * Complex.exp (-F w)) (e y) := by
          have h1 : AnalyticAt ℂ (fun w : ℂ ↦ -F w) (e y) := (hFa _ hyb).neg
          have h2 : AnalyticAt ℂ (Complex.exp ∘ fun w : ℂ ↦ -F w) (e y) := h1.cexp
          exact (analyticAt_id.sub analyticAt_const).mul h2
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
            (fun w : ℂ ↦ (w - c₁) * Complex.exp (-F w)) (e y) :=
          contMDiffAt_iff_contDiffAt.mpr houter.contDiffAt
        have h4 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e y :=
          contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hys)
        exact (hcoeSm _).comp y (h3.comp y h4)
      · intro hyp1 _
        have hyc : e y ≠ c₁ := by
          intro hcon
          exact hyp1 (e.injOn hys hxs (by rw [hcon, hc₁]))
        refine ⟨(e y - c₁) * Complex.exp (-F (e y)), rfl, ?_⟩
        have hval : h (e y) = G y + Real.log ‖e y - c₁‖ := by
          have h5 := hhval (e y) ⟨hyb, hyc⟩
          rw [e.left_inv hys] at h5
          exact h5
        have hpos : 0 < ‖e y - c₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyc)
        have hre0 : (F (e y)).re = h (e y) := hFre hyb
        rw [norm_mul, Complex.norm_exp, Complex.neg_re, hre0, hval, neg_add,
          Real.exp_add, Real.exp_neg (Real.log ‖e y - c₁‖), Real.exp_log hpos,
          mul_comm, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
      · intro hyp
        rw [hyp, ← hc₁, sub_self, zero_mul]
      · intro hyp
        exact absurd hyp hyp2'
    by_cases hx2 : x = p₂
    · -- the infinity element `1 / ((z - c₂) e^{f₂ z})` read through the chart at `p₂`
      subst hx2
      obtain ⟨r, hr0, hrsub, h, hharm, hhval⟩ := hpole₂
      set e := chartAt ℂ x with he
      set c₂ : ℂ := e x with hc₂
      have hxs : x ∈ e.source := mem_chart_source ℂ x
      obtain ⟨F, hFa, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
      refine ⟨fun y ↦ sphereChartInfty.symm ((e y - c₂) * Complex.exp (F (e y))), ?_⟩
      have hVopen : IsOpen (e.source ∩ e ⁻¹' ball c₂ r ∩ {p₁}ᶜ) :=
        (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).inter
          isOpen_compl_singleton
      have hxV : x ∈ e.source ∩ e ⁻¹' ball c₂ r ∩ {p₁}ᶜ := by
        refine ⟨⟨hxs, ?_⟩, fun hcon ↦ hne hcon.symm⟩
        rw [Set.mem_preimage, ← hc₂]
        exact mem_ball_self hr0
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      obtain ⟨⟨hys, hyb'⟩, hyp1⟩ := hy
      have hyb : e y ∈ ball c₂ r := hyb'
      have hyp1' : y ≠ p₁ := hyp1
      rw [hQ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have houter : AnalyticAt ℂ (fun w : ℂ ↦ (w - c₂) * Complex.exp (F w)) (e y) := by
          have h2 : AnalyticAt ℂ (Complex.exp ∘ F) (e y) := (hFa _ hyb).cexp
          exact (analyticAt_id.sub analyticAt_const).mul h2
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
            (fun w : ℂ ↦ (w - c₂) * Complex.exp (F w)) (e y) :=
          contMDiffAt_iff_contDiffAt.mpr houter.contDiffAt
        have h4 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e y :=
          contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hys)
        exact (hIsymmSm _).comp y (h3.comp y h4)
      · intro _ hyp2
        have hyc : e y ≠ c₂ := by
          intro hcon
          exact hyp2 (e.injOn hys hxs (by rw [hcon, hc₂]))
        have hgne0 : (e y - c₂) * Complex.exp (F (e y)) ≠ 0 :=
          mul_ne_zero (sub_ne_zero.mpr hyc) (Complex.exp_ne_zero _)
        refine ⟨((e y - c₂) * Complex.exp (F (e y)))⁻¹, ?_, ?_⟩
        · rw [sphereChartInfty_symm_apply, inversionGL_smul_coe, ite_eq_right hgne0]
        · have hval : h (e y) = G y - Real.log ‖e y - c₂‖ := by
            have h5 := hhval (e y) ⟨hyb, hyc⟩
            rw [e.left_inv hys] at h5
            exact h5
          have hpos : 0 < ‖e y - c₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyc)
          have hre0 : (F (e y)).re = h (e y) := hFre hyb
          rw [norm_inv, norm_mul, Complex.norm_exp, hre0, hval, Real.exp_sub,
            Real.exp_log hpos, mul_comm, div_mul_cancel₀ _ (ne_of_gt hpos),
            ← Real.exp_neg]
      · intro hyp
        exact absurd hyp hyp1'
      · intro hyp
        rw [hyp, ← hc₂, sub_self, zero_mul, sphereChartInfty_symm_apply,
          inversionGL_smul_coe, ite_eq_left rfl]
    · -- the generic element `e^{-F}` from a chart-ball harmonic conjugate
      set e := chartAt ℂ x with he
      have hxs : x ∈ e.source := mem_chart_source ℂ x
      have hSopen : IsOpen (e.target ∩ e.symm ⁻¹' ({p₁, p₂}ᶜ)) :=
        e.isOpen_inter_preimage_symm hpolesopen
      have hxS : e x ∈ e.target ∩ e.symm ⁻¹' ({p₁, p₂}ᶜ) := by
        refine ⟨e.map_source hxs, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxs, hpolemem]
        exact ⟨hx1, hx2⟩
      obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hSopen _ hxS
      have hharm : HarmonicOnNhd (G ∘ e.symm) (ball (e x) ρ) := by
        intro w hw
        have hwt : w ∈ e.target := (hρsub hw).1
        have hwp : e.symm w ∈ ({p₁, p₂}ᶜ : Set M) := (hρsub hw).2
        have h1 : MHarmonicAt G (e.symm w) := hG _ hwp
        have h2 := (mharmonicAt_iff_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x) (e.map_target hwt)).mp h1
        rwa [e.right_inv hwt] at h2
      obtain ⟨F, hFa, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
      refine ⟨fun y ↦ ((Complex.exp (-F (e y)) : ℂ) : ℂ̂), ?_⟩
      have hVopen : IsOpen (e.source ∩ e ⁻¹' ball (e x) ρ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hxV : x ∈ e.source ∩ e ⁻¹' ball (e x) ρ :=
        ⟨hxs, by rw [Set.mem_preimage]; exact mem_ball_self hρ0⟩
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      obtain ⟨hys, hyb'⟩ := hy
      have hyb : e y ∈ ball (e x) ρ := hyb'
      have hyp : y ≠ p₁ ∧ y ≠ p₂ := by
        have h1 := (hρsub hyb).2
        rw [Set.mem_preimage, e.left_inv hys, hpolemem] at h1
        exact h1
      rw [hQ]
      refine ⟨?_, fun _ _ ↦ ?_, fun hcon ↦ absurd hcon hyp.1,
        fun hcon ↦ absurd hcon hyp.2⟩
      · have houter : AnalyticAt ℂ (fun w : ℂ ↦ Complex.exp (-F w)) (e y) :=
          ((hFa _ hyb).neg).cexp
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℂ ↦ Complex.exp (-F w)) (e y) :=
          contMDiffAt_iff_contDiffAt.mpr houter.contDiffAt
        have h4 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e y :=
          contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hys)
        exact (hcoeSm _).comp y (h3.comp y h4)
      · refine ⟨Complex.exp (-F (e y)), rfl, ?_⟩
        have hre0 : (F (e y)).re = (G ∘ e.symm) (e y) := hFre hyb
        rw [Complex.norm_exp, Complex.neg_re, hre0]
        simp only [Function.comp_apply, e.left_inv hys]
  -- ## §3 Generic helpers: germ spreading, nearby non-pole points, path-continuity radii.
  have hOpen : ∀ (f g : M → ℂ̂) (x : M), f =ᶠ[𝓝 x] g →
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∀ z ∈ O, f =ᶠ[𝓝 z] g := by
    intro f g x heq
    obtain ⟨S, hS, hSeq⟩ := eventuallyEq_iff_exists_mem.mp heq
    obtain ⟨O, hOS, hO, hxO⟩ := mem_nhds_iff.mp hS
    exact ⟨O, hO, hxO, fun z hz ↦ (hSeq.mono hOS).eventuallyEq_of_mem (hO.mem_nhds hz)⟩
  have hQopen : ∀ (ψ : M → ℂ̂) (x : M), (∀ᶠ y in 𝓝 x, Q ψ y) →
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ W, Q ψ z ∧ ∀ᶠ y in 𝓝 z, Q ψ y := by
    intro ψ x h
    obtain ⟨S, hSnh, hSQ⟩ := eventually_iff_exists_mem.mp h
    obtain ⟨W, hWS, hWo, hxW⟩ := mem_nhds_iff.mp hSnh
    refine ⟨W, hWo, hxW, fun z hz ↦ ⟨hSQ z (hWS hz), ?_⟩⟩
    filter_upwards [hWo.mem_nhds hz] with y hy using hSQ y (hWS hy)
  have hnear : ∀ (x : M) (O : Set M), IsOpen O → x ∈ O →
      ∃ z ∈ O, z ≠ p₁ ∧ z ≠ p₂ := by
    intro x O hO hxO
    set e := chartAt ℂ x with he
    have hxs : x ∈ e.source := mem_chart_source ℂ x
    have hB : IsOpen (e.target ∩ e.symm ⁻¹' O) := e.isOpen_inter_preimage_symm hO
    have hxB : e x ∈ e.target ∩ e.symm ⁻¹' O :=
      ⟨e.map_source hxs, by rw [Set.mem_preimage, e.left_inv hxs]; exact hxO⟩
    obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hB _ hxB
    have hmem : ∀ t : ℝ, 0 ≤ t → t < 1 →
        e x + ((t * r : ℝ) : ℂ) ∈ e.target ∩ e.symm ⁻¹' O := by
      intro t ht0 ht1
      refine hrsub ?_
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      nlinarith
    have hOmem : ∀ t : ℝ, 0 ≤ t → t < 1 → e.symm (e x + ((t * r : ℝ) : ℂ)) ∈ O := by
      intro t ht0 ht1
      have h5 := (hmem t ht0 ht1).2
      rwa [Set.mem_preimage] at h5
    have hinj : ∀ t s : ℝ, 0 ≤ t → t < 1 → 0 ≤ s → s < 1 →
        e.symm (e x + ((t * r : ℝ) : ℂ)) = e.symm (e x + ((s * r : ℝ) : ℂ)) → t = s := by
      intro t s ht0 ht1 hs0 hs1 heq
      have hw1 : e x + ((t * r : ℝ) : ℂ) ∈ e.symm.source := by
        rw [e.symm_source]
        exact (hmem t ht0 ht1).1
      have hw2 : e x + ((s * r : ℝ) : ℂ) ∈ e.symm.source := by
        rw [e.symm_source]
        exact (hmem s hs0 hs1).1
      have h1 : e x + ((t * r : ℝ) : ℂ) = e x + ((s * r : ℝ) : ℂ) :=
        e.symm.injOn hw1 hw2 heq
      have h2 : ((t * r : ℝ) : ℂ) = ((s * r : ℝ) : ℂ) := add_left_cancel h1
      have h3 : t * r = s * r := by exact_mod_cast h2
      exact mul_right_cancel₀ (ne_of_gt hr0) h3
    have hd01 : e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠
        e.symm (e x + ((1/2 * r : ℝ) : ℂ)) := by
      intro hcon
      have h5 := hinj 0 (1/2) le_rfl one_pos (by norm_num) (by norm_num) hcon
      norm_num at h5
    have hd02 : e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠
        e.symm (e x + ((1/4 * r : ℝ) : ℂ)) := by
      intro hcon
      have h5 := hinj 0 (1/4) le_rfl one_pos (by norm_num) (by norm_num) hcon
      norm_num at h5
    have hd12 : e.symm (e x + ((1/2 * r : ℝ) : ℂ)) ≠
        e.symm (e x + ((1/4 * r : ℝ) : ℂ)) := by
      intro hcon
      have h5 := hinj (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hcon
      norm_num at h5
    by_cases h01 : e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠ p₁ ∧
        e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠ p₂
    · exact ⟨_, hOmem 0 le_rfl one_pos, h01.1, h01.2⟩
    by_cases h11 : e.symm (e x + ((1/2 * r : ℝ) : ℂ)) ≠ p₁ ∧
        e.symm (e x + ((1/2 * r : ℝ) : ℂ)) ≠ p₂
    · exact ⟨_, hOmem (1/2) (by norm_num) (by norm_num), h11.1, h11.2⟩
    by_cases h21 : e.symm (e x + ((1/4 * r : ℝ) : ℂ)) ≠ p₁ ∧
        e.symm (e x + ((1/4 * r : ℝ) : ℂ)) ≠ p₂
    · exact ⟨_, hOmem (1/4) (by norm_num) (by norm_num), h21.1, h21.2⟩
    exfalso
    rw [not_and_or, not_not, not_not] at h01 h11 h21
    rcases h01 with h0 | h0 <;> rcases h11 with h1 | h1 <;> rcases h21 with h2 | h2
    all_goals first
      | exact hd01 (h0.trans h1.symm)
      | exact hd02 (h0.trans h2.symm)
      | exact hd12 (h1.trans h2.symm)
  have hγnb : ∀ (γ : ℝ → M) (S : Set ℝ) (b : ℝ), ContinuousOn γ S → b ∈ S →
      ∀ O : Set M, IsOpen O → γ b ∈ O → ∃ δ > 0, ∀ u ∈ S, |u - b| < δ → γ u ∈
          O := by
    intro γ S b hγ hbS O hO hbO
    have h1 : γ ⁻¹' O ∈ 𝓝[S] b :=
      (hγ b hbS).preimage_mem_nhdsWithin (hO.mem_nhds hbO)
    obtain ⟨δ, hδ0, hδ⟩ := mem_nhdsWithin_iff.mp h1
    refine ⟨δ, hδ0, fun u huS hub ↦ ?_⟩
    exact hδ ⟨by rwa [mem_ball, Real.dist_eq], huS⟩
  -- ## §4 Phase rigidity: two elements at a point differ by a unimodular Möbius
  -- scaling near it, read through the finite chart away from `p₂` and through the
  -- infinity chart at `p₂`.
  have hrigid : ∀ (ψ ψ' : M → ℂ̂) (x : M), (∀ᶠ y in 𝓝 x, Q ψ y) →
      (∀ᶠ y in 𝓝 x, Q ψ' y) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ψ =ᶠ[𝓝 x] fun y ↦ mulC c (ψ' y) := by
    intro ψ ψ' x hψ hψ'
    obtain ⟨W, hWnh, hWQ⟩ := eventually_iff_exists_mem.mp hψ
    obtain ⟨W1, hW1W, hW1o, hxW1⟩ := mem_nhds_iff.mp hWnh
    obtain ⟨W', hW'nh, hW'Q⟩ := eventually_iff_exists_mem.mp hψ'
    obtain ⟨W1', hW1'W, hW1'o, hxW1'⟩ := mem_nhds_iff.mp hW'nh
    set e := chartAt ℂ x with he
    have hxs : x ∈ e.source := mem_chart_source ℂ x
    by_cases hx2 : x = p₂
    · -- at the infinity pole: invert the readings
      have hT : IsOpen (e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ {p₁}ᶜ)) :=
        e.isOpen_inter_preimage_symm ((hW1o.inter hW1'o).inter isOpen_compl_singleton)
      have hxT : e x ∈ e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ {p₁}ᶜ) := by
        refine ⟨e.map_source hxs, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxs]
        exact ⟨⟨hxW1, hxW1'⟩, by rw [hx2]; exact fun hcon ↦ hne hcon.symm⟩
      obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hT _ hxT
      have hmem : ∀ w ∈ ball (e x) ρ, w ∈ e.target ∧ e.symm w ∈ W1 ∧
          e.symm w ∈ W1' ∧ e.symm w ≠ p₁ := by
        intro w hw
        obtain ⟨h1, h2⟩ := hρsub hw
        rw [Set.mem_preimage] at h2
        exact ⟨h1, h2.1.1, h2.1.2, h2.2⟩
      have hQmem : ∀ w ∈ ball (e x) ρ, Q ψ (e.symm w) ∧ Q ψ' (e.symm w) := by
        intro w hw
        exact ⟨hWQ _ (hW1W (hmem w hw).2.1), hW'Q _ (hW1'W (hmem w hw).2.2.1)⟩
      have hcenter : ∀ w ∈ ball (e x) ρ, e.symm w = p₂ → w = e x := by
        intro w hw hwp
        have h9 : e.symm w = e.symm (e x) := by rw [hwp, ← hx2, e.left_inv hxs]
        have hw1 : w ∈ e.symm.source := by
          rw [e.symm_source]
          exact (hmem w hw).1
        have hw2 : e x ∈ e.symm.source := by
          rw [e.symm_source]
          exact e.map_source hxs
        exact e.symm.injOn hw1 hw2 h9
      have hfa : AnalyticOnNhd ℂ (fun z ↦ sphereChartInfty (ψ (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).1
        have h6 : ψ (e.symm w) ≠ ((0 : ℂ) : ℂ̂) :=
          hne0 ψ (e.symm w) h5 (hmem w hw).2.2.2
        rw [hQ] at h5
        exact hreadInf ψ x w (hmem w hw).1 h6 h5.1
      have hga : AnalyticOnNhd ℂ (fun z ↦ sphereChartInfty (ψ' (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).2
        have h6 : ψ' (e.symm w) ≠ ((0 : ℂ) : ℂ̂) :=
          hne0 ψ' (e.symm w) h5 (hmem w hw).2.2.2
        rw [hQ] at h5
        exact hreadInf ψ' x w (hmem w hw).1 h6 h5.1
      have hnorm : ∀ w ∈ ball (e x) ρ,
          ‖(fun z ↦ sphereChartInfty (ψ (e.symm z))) w‖ =
          ‖(fun z ↦ sphereChartInfty (ψ' (e.symm z))) w‖ := by
        intro w hw
        obtain ⟨h5, h5'⟩ := hQmem w hw
        rw [hQ] at h5 h5'
        change ‖sphereChartInfty (ψ (e.symm w))‖ = ‖sphereChartInfty (ψ' (e.symm w))‖
        by_cases h6 : e.symm w = p₂
        · rw [h5.2.2.2 h6, h5'.2.2.2 h6]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 (hmem w hw).2.2.2 h6
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 (hmem w hw).2.2.2 h6
          have hv0 : v ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv2
            exact absurd hv2.symm (ne_of_gt (Real.exp_pos _))
          have hv'0 : v' ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv'2
            exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
          rw [hv1, hv'1, hIapp_coe v hv0, hIapp_coe v' hv'0, norm_inv, norm_inv,
            hv2, hv'2]
      have hgne : ∀ w ∈ ball (e x) ρ, w ≠ e x →
          (fun z ↦ sphereChartInfty (ψ' (e.symm z))) w ≠ 0 := by
        intro w hw hwx
        have h5' := (hQmem w hw).2
        rw [hQ] at h5'
        have h6 : e.symm w ≠ p₂ := fun hcon ↦ hwx (hcenter w hw hcon)
        obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 (hmem w hw).2.2.2 h6
        have hv'0 : v' ≠ 0 := by
          intro hcon
          rw [hcon, norm_zero] at hv'2
          exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
        change sphereChartInfty (ψ' (e.symm w)) ≠ 0
        rw [hv'1, hIapp_coe v' hv'0]
        exact inv_ne_zero hv'0
      obtain ⟨cc, hcc1, hcceq⟩ := hcore _ _ (e x) ρ hρ0 hfa hga hnorm hgne
      have hcc0 : cc ≠ 0 := by
        intro hcon
        rw [hcon, norm_zero] at hcc1
        exact one_ne_zero hcc1.symm
      refine ⟨cc⁻¹, by rw [norm_inv, hcc1, inv_one], ?_⟩
      have hNo : IsOpen (e.source ∩ e ⁻¹' ball (e x) ρ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hxN : x ∈ e.source ∩ e ⁻¹' ball (e x) ρ :=
        ⟨hxs, by rw [Set.mem_preimage]; exact mem_ball_self hρ0⟩
      have hEq : Set.EqOn ψ (fun y ↦ mulC cc⁻¹ (ψ' y))
          (e.source ∩ e ⁻¹' ball (e x) ρ) := by
        intro y hy
        have h1 : sphereChartInfty (ψ (e.symm (e y))) =
            cc * sphereChartInfty (ψ' (e.symm (e y))) := hcceq hy.2
        rw [e.left_inv hy.1] at h1
        have hyb : e y ∈ ball (e x) ρ := hy.2
        obtain ⟨h5, h5'⟩ := hQmem (e y) hyb
        rw [e.left_inv hy.1] at h5 h5'
        have h7 : y ≠ p₁ := by
          have h7' := (hmem (e y) hyb).2.2.2
          rwa [e.left_inv hy.1] at h7'
        rw [hQ] at h5 h5'
        by_cases h6 : y = p₂
        · change ψ y = mulC cc⁻¹ (ψ' y)
          rw [h5.2.2.2 h6, h5'.2.2.2 h6, hmulCinf cc⁻¹ (inv_ne_zero hcc0)]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 h7 h6
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h7 h6
          have hv0 : v ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv2
            exact absurd hv2.symm (ne_of_gt (Real.exp_pos _))
          have hv'0 : v' ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv'2
            exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
          rw [hv1, hv'1, hIapp_coe v hv0, hIapp_coe v' hv'0] at h1
          have h8 : v = cc⁻¹ * v' := by
            have h9 : (v⁻¹)⁻¹ = (cc * v'⁻¹)⁻¹ := by rw [h1]
            rw [inv_inv, mul_inv, inv_inv] at h9
            exact h9
          change ψ y = mulC cc⁻¹ (ψ' y)
          rw [hv1, hv'1, hmulCco cc⁻¹ (inv_ne_zero hcc0) v', ← h8]
      exact hEq.eventuallyEq_of_mem (hNo.mem_nhds hxN)
    · -- away from the infinity pole: finite readings
      set X : Set M := (if x = p₁ then Set.univ else {p₁}ᶜ) ∩ {p₂}ᶜ with hX
      have hXo : IsOpen X := by
        rw [hX]
        refine IsOpen.inter ?_ isOpen_compl_singleton
        split_ifs
        exacts [isOpen_univ, isOpen_compl_singleton]
      have hxX : x ∈ X := by
        rw [hX]
        refine ⟨?_, hx2⟩
        split_ifs with hx1
        exacts [Set.mem_univ x, hx1]
      have hT : IsOpen (e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ X)) :=
        e.isOpen_inter_preimage_symm ((hW1o.inter hW1'o).inter hXo)
      have hxT : e x ∈ e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ X) := by
        refine ⟨e.map_source hxs, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxs]
        exact ⟨⟨hxW1, hxW1'⟩, hxX⟩
      obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hT _ hxT
      have hmem : ∀ w ∈ ball (e x) ρ, w ∈ e.target ∧ e.symm w ∈ W1 ∧
          e.symm w ∈ W1' ∧ e.symm w ≠ p₂ ∧ (x ≠ p₁ → e.symm w ≠ p₁) := by
        intro w hw
        obtain ⟨h1, h2⟩ := hρsub hw
        rw [Set.mem_preimage] at h2
        refine ⟨h1, h2.1.1, h2.1.2, ?_, ?_⟩
        · have h3 := h2.2
          rw [hX] at h3
          exact h3.2
        · intro hx1
          have h3 := h2.2
          rw [hX, ite_eq_right hx1] at h3
          exact h3.1
      have hQmem : ∀ w ∈ ball (e x) ρ, Q ψ (e.symm w) ∧ Q ψ' (e.symm w) := by
        intro w hw
        exact ⟨hWQ _ (hW1W (hmem w hw).2.1), hW'Q _ (hW1'W (hmem w hw).2.2.1)⟩
      have hcenter : ∀ w ∈ ball (e x) ρ, e.symm w = p₁ → x = p₁ → w = e x := by
        intro w hw hwp hx1
        have h9 : e.symm w = e.symm (e x) := by rw [hwp, ← hx1, e.left_inv hxs]
        have hw1 : w ∈ e.symm.source := by
          rw [e.symm_source]
          exact (hmem w hw).1
        have hw2 : e x ∈ e.symm.source := by
          rw [e.symm_source]
          exact e.map_source hxs
        exact e.symm.injOn hw1 hw2 h9
      have hfa : AnalyticOnNhd ℂ (fun z ↦ sphereChartFinite (ψ (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).1
        have h6 : ψ (e.symm w) ≠ OnePoint.infty :=
          hfin ψ (e.symm w) h5 (hmem w hw).2.2.2.1
        rw [hQ] at h5
        exact hreadFin ψ x w (hmem w hw).1 h6 h5.1
      have hga : AnalyticOnNhd ℂ (fun z ↦ sphereChartFinite (ψ' (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).2
        have h6 : ψ' (e.symm w) ≠ OnePoint.infty :=
          hfin ψ' (e.symm w) h5 (hmem w hw).2.2.2.1
        rw [hQ] at h5
        exact hreadFin ψ' x w (hmem w hw).1 h6 h5.1
      have hnorm : ∀ w ∈ ball (e x) ρ,
          ‖(fun z ↦ sphereChartFinite (ψ (e.symm z))) w‖ =
          ‖(fun z ↦ sphereChartFinite (ψ' (e.symm z))) w‖ := by
        intro w hw
        obtain ⟨h5, h5'⟩ := hQmem w hw
        rw [hQ] at h5 h5'
        change ‖sphereChartFinite (ψ (e.symm w))‖ = ‖sphereChartFinite (ψ' (e.symm w))‖
        by_cases h6 : e.symm w = p₁
        · rw [h5.2.2.1 h6, h5'.2.2.1 h6]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 h6 (hmem w hw).2.2.2.1
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h6 (hmem w hw).2.2.2.1
          rw [hv1, hv'1, sphereChartFinite_coe, sphereChartFinite_coe, hv2, hv'2]
      have hgne : ∀ w ∈ ball (e x) ρ, w ≠ e x →
          (fun z ↦ sphereChartFinite (ψ' (e.symm z))) w ≠ 0 := by
        intro w hw hwx
        have h5' := (hQmem w hw).2
        rw [hQ] at h5'
        have h6 : e.symm w ≠ p₁ := by
          by_cases hx1 : x = p₁
          · exact fun hcon ↦ hwx (hcenter w hw hcon hx1)
          · exact (hmem w hw).2.2.2.2 hx1
        obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h6 (hmem w hw).2.2.2.1
        have hv'0 : v' ≠ 0 := by
          intro hcon
          rw [hcon, norm_zero] at hv'2
          exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
        change sphereChartFinite (ψ' (e.symm w)) ≠ 0
        rw [hv'1, sphereChartFinite_coe]
        exact hv'0
      obtain ⟨c, hc1, hceq⟩ := hcore _ _ (e x) ρ hρ0 hfa hga hnorm hgne
      have hc0 : c ≠ 0 := by
        intro hcon
        rw [hcon, norm_zero] at hc1
        exact one_ne_zero hc1.symm
      refine ⟨c, hc1, ?_⟩
      have hNo : IsOpen (e.source ∩ e ⁻¹' ball (e x) ρ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hxN : x ∈ e.source ∩ e ⁻¹' ball (e x) ρ :=
        ⟨hxs, by rw [Set.mem_preimage]; exact mem_ball_self hρ0⟩
      have hEq : Set.EqOn ψ (fun y ↦ mulC c (ψ' y))
          (e.source ∩ e ⁻¹' ball (e x) ρ) := by
        intro y hy
        have h1 : sphereChartFinite (ψ (e.symm (e y))) =
            c * sphereChartFinite (ψ' (e.symm (e y))) := hceq hy.2
        rw [e.left_inv hy.1] at h1
        have hyb : e y ∈ ball (e x) ρ := hy.2
        obtain ⟨h5, h5'⟩ := hQmem (e y) hyb
        rw [e.left_inv hy.1] at h5 h5'
        have h7 : y ≠ p₂ := by
          have h7' := (hmem (e y) hyb).2.2.2.1
          rwa [e.left_inv hy.1] at h7'
        rw [hQ] at h5 h5'
        by_cases h6 : y = p₁
        · change ψ y = mulC c (ψ' y)
          rw [h5.2.2.1 h6, h5'.2.2.1 h6, hmulCco c hc0 0, mul_zero]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 h6 h7
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h6 h7
          rw [hv1, hv'1, sphereChartFinite_coe, sphereChartFinite_coe] at h1
          change ψ y = mulC c (ψ' y)
          rw [hv1, hv'1, hmulCco c hc0 v', h1]
      exact hEq.eventuallyEq_of_mem (hNo.mem_nhds hxN)
  -- ## §5 Germ agreement is closed among elements: cluster equality forces equality.
  have hgermclosed : ∀ (ψ ψ' : M → ℂ̂) (x : M),
      (∀ᶠ y in 𝓝 x, Q ψ y) → (∀ᶠ y in 𝓝 x, Q ψ' y) →
      (∀ O : Set M, IsOpen O → x ∈ O → ∃ z ∈ O, ψ =ᶠ[𝓝 z] ψ') → ψ =ᶠ[𝓝 x]
          ψ' := by
    intro ψ ψ' x hψ hψ' hclu
    obtain ⟨c, hc1, hcev⟩ := hrigid ψ ψ' x hψ hψ'
    have hc0 : c ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hc1
      exact one_ne_zero hc1.symm
    obtain ⟨O₀, hO₀o, hxO₀, hO₀⟩ := hOpen ψ (fun y ↦ mulC c (ψ' y)) x hcev
    obtain ⟨W', hW'nh, hW'Q⟩ := eventually_iff_exists_mem.mp hψ'
    obtain ⟨W1, hW1W, hW1o, hxW1⟩ := mem_nhds_iff.mp hW'nh
    obtain ⟨z, hz, hzeq⟩ := hclu (O₀ ∩ W1) (hO₀o.inter hW1o) ⟨hxO₀, hxW1⟩
    obtain ⟨O₁, hO₁o, hzO₁, hO₁⟩ := hOpen ψ ψ' z hzeq
    obtain ⟨w, hw, hwp1, hwp2⟩ := hnear z (O₀ ∩ W1 ∩ O₁)
      ((hO₀o.inter hW1o).inter hO₁o) ⟨hz, hzO₁⟩
    have h1 : ψ =ᶠ[𝓝 w] fun y ↦ mulC c (ψ' y) := hO₀ w hw.1.1
    have h2 : ψ =ᶠ[𝓝 w] ψ' := hO₁ w hw.2
    have h3 : Q ψ' w := hW'Q w (hW1W hw.1.2)
    rw [hQ] at h3
    obtain ⟨v', hv'1, hv'2⟩ := h3.2.1 hwp1 hwp2
    have hv'0 : v' ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hv'2
      exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
    have h5 : ψ w = mulC c (ψ' w) := h1.eq_of_nhds
    have h6 : ψ w = ψ' w := h2.eq_of_nhds
    have h7 : c = 1 := by
      rw [hv'1, hmulCco c hc0 v'] at h5
      rw [hv'1] at h6
      rw [h6] at h5
      have h8 : v' = c * v' := OnePoint.coe_eq_coe.mp h5
      have h9 : (1 : ℂ) * v' = c * v' := by
        rw [one_mul]
        exact h8
      exact (mul_right_cancel₀ hv'0 h9).symm
    have h9 : (fun y ↦ mulC c (ψ' y)) =ᶠ[𝓝 x] ψ' := by
      refine Filter.Eventually.of_forall fun y ↦ ?_
      change mulC c (ψ' y) = ψ' y
      rw [h7, hmulC1]
    exact hcev.trans h9
  -- ## §6 The initial element and the continuation predicate.
  obtain ⟨Ψ, hΨ⟩ := helt p₁
  obtain ⟨IsCont, hIC⟩ : ∃ P : (ℝ → M) → ℝ → (ℝ → M → ℂ̂) → Prop, ∀ γ
      b Φ, P γ b Φ ↔
      ((∀ t ∈ Set.Icc (0:ℝ) b, ∀ᶠ y in 𝓝 (γ t), Q (Φ t) y) ∧ Φ 0 =ᶠ[𝓝 p₁]
          Ψ ∧
        ∀ t ∈ Set.Icc (0:ℝ) b, ∃ ε > 0, ∀ u ∈ Set.Icc (0:ℝ) b, |u - t| < ε →
          Φ u =ᶠ[𝓝 (γ u)] Φ t) :=
    ⟨_, fun _ _ _ ↦ Iff.rfl⟩
  -- ## §6b Real-interval induction: nonempty at the left end, closed from the left,
  -- open to the right, forces membership of the right end.
  have hind : ∀ (a b : ℝ) (A : Set ℝ), a ≤ b → (∀ x ∈ A, x ∈ Set.Icc a b) → a ∈
      A →
      (∀ c ∈ Set.Icc a b, (∀ δ > 0, ∃ x ∈ A, c - δ < x ∧ x ≤ c) → c ∈ A) →
      (∀ c ∈ A, c < b → ∃ δ > 0, ∀ x ∈ Set.Icc a b, c ≤ x → x < c + δ → x ∈ A)
          →
      b ∈ A := by
    intro a b A hab hsub haA hclosed hopen
    have hne : A.Nonempty := ⟨a, haA⟩
    have hbdd : BddAbove A := ⟨b, fun x hx ↦ (hsub x hx).2⟩
    have hcIcc : sSup A ∈ Set.Icc a b :=
      ⟨le_csSup hbdd haA, csSup_le hne fun x hx ↦ (hsub x hx).2⟩
    have hcA : sSup A ∈ A := by
      refine hclosed _ hcIcc ?_
      intro δ hδ0
      obtain ⟨x, hxA, hxgt⟩ := exists_lt_of_lt_csSup hne
        (by linarith : sSup A - δ < sSup A)
      exact ⟨x, hxA, hxgt, le_csSup hbdd hxA⟩
    rcases eq_or_lt_of_le hcIcc.2 with hcb | hcb
    · exact hcb ▸ hcA
    · exfalso
      obtain ⟨δ, hδ0, hδA⟩ := hopen _ hcA hcb
      have hx : min (sSup A + δ / 2) b ∈ A := by
        refine hδA _ ⟨le_min (by linarith [hcIcc.1]) hab,
          min_le_right _ _⟩ (le_min (by linarith) hcb.le) ?_
        calc min (sSup A + δ / 2) b ≤ sSup A + δ / 2 := min_le_left _ _
          _ < sSup A + δ := by linarith
      have hle : min (sSup A + δ / 2) b ≤ sSup A := le_csSup hbdd hx
      have hgt : sSup A < min (sSup A + δ / 2) b := lt_min (by linarith) hcb
      linarith
  -- ## §7 Existence of continuations.
  have hexist : ∀ γ : ℝ → M, ContinuousOn γ (Set.Icc 0 1) → γ 0 = p₁ →
      ∃ Φ, IsCont γ 1 Φ := by
    intro γ hγ hγ0
    -- one-step gluing: near any parameter c, a continuation up to a point near c
    -- extends past c using the element at γ c and phase rigidity.
    have hglue : ∀ c ∈ Set.Icc (0:ℝ) 1, ∃ δ > 0, ∀ a ∈ Set.Icc (0:ℝ) 1, |a - c| < δ
        →
        (∃ Φ, IsCont γ a Φ) → ∀ b' ∈ Set.Icc (0:ℝ) 1, a ≤ b' → |b' - c| < δ →
        ∃ Φ', IsCont γ b' Φ' := by
      intro c hc
      obtain ⟨ψ, hψev⟩ := helt (γ c)
      obtain ⟨W, hWo, hWc, hWQ⟩ := hQopen ψ (γ c) hψev
      obtain ⟨δ, hδ0, hδW⟩ := hγnb γ (Set.Icc 0 1) c hγ hc W hWo hWc
      refine ⟨δ, hδ0, ?_⟩
      rintro a ha hac ⟨Φ, hΦ⟩ b' hb' hab' hb'c
      rw [hIC] at hΦ
      obtain ⟨hΦa, hΦ0, hΦc⟩ := hΦ
      have hγaW : γ a ∈ W := hδW a ha hac
      obtain ⟨u₀, hu₀, hu₀ev⟩ := hrigid (Φ a) ψ (γ a)
        (hΦa a ⟨ha.1, le_refl a⟩) (hWQ (γ a) hγaW).2
      obtain ⟨Oa, hOao, hγaOa, hOa⟩ := hOpen (Φ a) (fun y ↦ mulC u₀ (ψ y)) (γ a) hu₀ev
      refine ⟨fun t ↦ if t ≤ a then Φ t else fun y ↦ mulC u₀ (ψ y), ?_⟩
      rw [hIC]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        by_cases hta : t ≤ a
        · rw [ite_eq_left hta]
          exact hΦa t ⟨ht.1, hta⟩
        · rw [not_le] at hta
          rw [ite_eq_right (not_le.mpr hta)]
          have htc : |t - c| < δ := by
            rw [abs_sub_lt_iff] at hac hb'c ⊢
            constructor
            · linarith [ht.2, hb'c.1]
            · linarith [hac.2]
          have htW : γ t ∈ W := hδW t ⟨ht.1, ht.2.trans hb'.2⟩ htc
          filter_upwards [(hWQ (γ t) htW).2] with y hy using hQsmul u₀ hu₀ ψ y hy
      · rw [ite_eq_left ha.1]
        exact hΦ0
      · intro t ht
        rcases lt_trichotomy t a with hta | hta | hta
        · obtain ⟨ε, hε0, hεp⟩ := hΦc t ⟨ht.1, hta.le⟩
          refine ⟨min ε (a - t), lt_min hε0 (by linarith), ?_⟩
          intro u hu huε
          rw [lt_min_iff] at huε
          have hua : u ≤ a := by
            have h6 := abs_sub_lt_iff.mp huε.2
            linarith [h6.1]
          rw [ite_eq_left hua, ite_eq_left hta.le]
          exact hεp u ⟨hu.1, hua⟩ huε.1
        · obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc a ⟨ha.1, le_refl a⟩
          obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hγnb γ (Set.Icc 0 1) a hγ ha Oa hOao hγaOa
          refine ⟨min ε₁ δ₂, lt_min hε₁0 hδ₂0, ?_⟩
          intro u hu huε
          rw [lt_min_iff] at huε
          have hut : |u - a| < ε₁ := by rw [← hta]; exact huε.1
          have hut2 : |u - a| < δ₂ := by rw [← hta]; exact huε.2
          by_cases hua : u ≤ a
          · rw [ite_eq_left hua, ite_eq_left hta.le, hta]
            exact hε₁p u ⟨hu.1, hua⟩ hut
          · rw [not_le] at hua
            rw [ite_eq_right (not_le.mpr hua), ite_eq_left hta.le, hta]
            have h3 : γ u ∈ Oa := hδ₂ u ⟨hu.1, hu.2.trans hb'.2⟩ hut2
            exact (hOa (γ u) h3).symm
        · refine ⟨t - a, by linarith, ?_⟩
          intro u hu huε
          rw [abs_sub_lt_iff] at huε
          have hua : a < u := by linarith [huε.2]
          rw [ite_eq_right (not_le.mpr hua), ite_eq_right (not_le.mpr hta)]
    have h1A : (1:ℝ) ∈ {b | b ∈ Set.Icc (0:ℝ) 1 ∧ ∃ Φ, IsCont γ b Φ} := by
      refine hind 0 1 _ zero_le_one (fun x hx ↦ hx.1) ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩ ?_ ?_
      · refine ⟨fun _ ↦ Ψ, ?_⟩
        rw [hIC]
        refine ⟨?_, Filter.EventuallyEq.refl _ _, ?_⟩
        · intro t ht
          have ht0 : t = 0 := le_antisymm ht.2 ht.1
          rw [ht0, hγ0]
          exact hΨ
        · intro t ht
          exact ⟨1, one_pos, fun u hu _ ↦ Filter.EventuallyEq.refl _ _⟩
      · intro c hc hap
        obtain ⟨δ, hδ0, hglued⟩ := hglue c hc
        obtain ⟨x, hxA, hxgt, hxle⟩ := hap δ hδ0
        refine ⟨hc, hglued x hxA.1 ?_ hxA.2 c hc hxle ?_⟩
        · rw [abs_sub_lt_iff]
          constructor <;> linarith
        · rw [sub_self, abs_zero]
          exact hδ0
      · intro c hcA hclt
        obtain ⟨δ, hδ0, hglued⟩ := hglue c hcA.1
        refine ⟨δ, hδ0, ?_⟩
        intro x hx hcx hxδ
        refine ⟨hx, hglued c hcA.1 ?_ hcA.2 x hx hcx ?_⟩
        · rw [sub_self, abs_zero]
          exact hδ0
        · rw [abs_sub_lt_iff]
          constructor <;> linarith
    exact h1A.2
  -- ## §8 Uniqueness of continuations.
  have huniq : ∀ γ : ℝ → M, ContinuousOn γ (Set.Icc 0 1) → γ 0 = p₁ →
      ∀ Φ Φ', IsCont γ 1 Φ → IsCont γ 1 Φ' →
      ∀ t ∈ Set.Icc (0:ℝ) 1, Φ t =ᶠ[𝓝 (γ t)] Φ' t := by
    intro γ hγ hγ0 Φ Φ' hΦ hΦ'
    rw [hIC] at hΦ hΦ'
    obtain ⟨hΦa, hΦ0, hΦc⟩ := hΦ
    obtain ⟨hΦ'a, hΦ'0, hΦ'c⟩ := hΦ'
    have h1A : (1:ℝ) ∈ {b | b ∈ Set.Icc (0:ℝ) 1 ∧
        ∀ t ∈ Set.Icc (0:ℝ) b, Φ t =ᶠ[𝓝 (γ t)] Φ' t} := by
      refine hind 0 1 _ zero_le_one (fun x hx ↦ hx.1) ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩ ?_ ?_
      · intro t ht
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        rw [ht0, hγ0]
        exact hΦ0.trans hΦ'0.symm
      · intro c hc hap
        refine ⟨hc, ?_⟩
        intro t ht
        rcases eq_or_lt_of_le ht.2 with htc | htc
        · -- t = c: germ closure via approximants
          have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, htc.le.trans hc.2⟩
          refine hgermclosed (Φ t) (Φ' t) (γ t) (hΦa t htI) (hΦ'a t htI) ?_
          intro O hOo hγtO
          obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb γ (Set.Icc 0 1) t hγ htI O hOo hγtO
          obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc t htI
          obtain ⟨ε₂, hε₂0, hε₂p⟩ := hΦ'c t htI
          have hmin0 : 0 < min δ₁ (min ε₁ ε₂) := lt_min hδ₁0 (lt_min hε₁0 hε₂0)
          obtain ⟨x, hxA, hxgt, hxle⟩ := hap (min δ₁ (min ε₁ ε₂)) hmin0
          have hxd : |x - t| < min δ₁ (min ε₁ ε₂) := by
            rw [abs_sub_lt_iff]
            constructor <;> linarith
          have hxI : x ∈ Set.Icc (0:ℝ) 1 := hxA.1
          have hd1 : |x - t| < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
          have hd2 : |x - t| < ε₁ :=
            lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_left _ _))
          have hd3 : |x - t| < ε₂ :=
            lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_right _ _))
          refine ⟨γ x, hδ₁ x hxI hd1, ?_⟩
          have e1 : Φ x =ᶠ[𝓝 (γ x)] Φ t := hε₁p x hxI hd2
          have e2 : Φ' x =ᶠ[𝓝 (γ x)] Φ' t := hε₂p x hxI hd3
          have e3 : Φ x =ᶠ[𝓝 (γ x)] Φ' x := hxA.2 x ⟨hxI.1, le_refl x⟩
          exact e1.symm.trans (e3.trans e2)
        · -- t < c: an approximant already covers t
          obtain ⟨x, hxA, hxgt, hxle⟩ := hap (c - t) (by linarith)
          exact hxA.2 t ⟨ht.1, by linarith⟩
      · intro c hcA hclt
        obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc c hcA.1
        obtain ⟨ε₂, hε₂0, hε₂p⟩ := hΦ'c c hcA.1
        have hagr : Φ c =ᶠ[𝓝 (γ c)] Φ' c := hcA.2 c ⟨hcA.1.1, le_refl c⟩
        obtain ⟨Oc, hOco, hγcOc, hOc⟩ := hOpen (Φ c) (Φ' c) (γ c) hagr
        obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb γ (Set.Icc 0 1) c hγ hcA.1 Oc hOco hγcOc
        have hmin0 : 0 < min δ₁ (min ε₁ ε₂) := lt_min hδ₁0 (lt_min hε₁0 hε₂0)
        refine ⟨min δ₁ (min ε₁ ε₂), hmin0, ?_⟩
        intro x hx hcx hxδ
        refine ⟨hx, ?_⟩
        intro t ht
        by_cases htc : t ≤ c
        · exact hcA.2 t ⟨ht.1, htc⟩
        · rw [not_le] at htc
          have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
          have htd : |t - c| < min δ₁ (min ε₁ ε₂) := by
            rw [abs_sub_lt_iff]
            constructor
            · linarith [ht.2]
            · linarith
          have hd1 : |t - c| < δ₁ := lt_of_lt_of_le htd (min_le_left _ _)
          have hd2 : |t - c| < ε₁ :=
            lt_of_lt_of_le htd ((min_le_right _ _).trans (min_le_left _ _))
          have hd3 : |t - c| < ε₂ :=
            lt_of_lt_of_le htd ((min_le_right _ _).trans (min_le_right _ _))
          have e1 : Φ t =ᶠ[𝓝 (γ t)] Φ c := hε₁p t htI hd2
          have e2 : Φ' t =ᶠ[𝓝 (γ t)] Φ' c := hε₂p t htI hd3
          have e4 : Φ c =ᶠ[𝓝 (γ t)] Φ' c := hOc (γ t) (hδ₁ t htI hd1)
          exact e1.trans (e4.trans e2.symm)
    exact h1A.2
  -- ## §8b Transport of germ equality along a path through common element territory.
  have htransport : ∀ (ψ ψ' : M → ℂ̂) (ζ : ℝ → M) (a b : ℝ), a ≤ b →
      ContinuousOn ζ (Set.Icc a b) →
      (∀ σ ∈ Set.Icc a b, ∀ᶠ y in 𝓝 (ζ σ), Q ψ y) →
      (∀ σ ∈ Set.Icc a b, ∀ᶠ y in 𝓝 (ζ σ), Q ψ' y) →
      ψ =ᶠ[𝓝 (ζ a)] ψ' → ∀ σ ∈ Set.Icc a b, ψ =ᶠ[𝓝 (ζ σ)] ψ' := by
    intro ψ ψ' ζ a b hab hζ hQ1 hQ2 heq0
    have hbA : b ∈ {σ | σ ∈ Set.Icc a b ∧ ∀ τ ∈ Set.Icc a σ, ψ =ᶠ[𝓝 (ζ τ)]
        ψ'} := by
      refine hind a b _ hab (fun x hx ↦ hx.1) ⟨⟨le_refl a, hab⟩, ?_⟩ ?_ ?_
      · intro τ hτ
        have hτa : τ = a := le_antisymm hτ.2 hτ.1
        rw [hτa]
        exact heq0
      · intro c hc hap
        refine ⟨hc, ?_⟩
        intro τ hτ
        rcases eq_or_lt_of_le hτ.2 with hτc | hτc
        · have hτI : τ ∈ Set.Icc a b := ⟨hτ.1, hτc.le.trans hc.2⟩
          refine hgermclosed ψ ψ' (ζ τ) (hQ1 τ hτI) (hQ2 τ hτI) ?_
          intro O hOo hζτO
          obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb ζ (Set.Icc a b) τ hζ hτI O hOo hζτO
          obtain ⟨x, hxA, hxgt, hxle⟩ := hap δ₁ hδ₁0
          have hxd : |x - τ| < δ₁ := by
            rw [abs_sub_lt_iff]
            constructor <;> linarith
          exact ⟨ζ x, hδ₁ x hxA.1 hxd, hxA.2 x ⟨hxA.1.1, le_refl x⟩⟩
        · obtain ⟨x, hxA, hxgt, hxle⟩ := hap (c - τ) (by linarith)
          exact hxA.2 τ ⟨hτ.1, by linarith⟩
      · intro c hcA hclt
        have hagr : ψ =ᶠ[𝓝 (ζ c)] ψ' := hcA.2 c ⟨hcA.1.1, le_refl c⟩
        obtain ⟨Oc, hOco, hζcOc, hOc⟩ := hOpen ψ ψ' (ζ c) hagr
        obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb ζ (Set.Icc a b) c hζ hcA.1 Oc hOco hζcOc
        refine ⟨δ₁, hδ₁0, ?_⟩
        intro x hx hcx hxδ
        refine ⟨hx, ?_⟩
        intro τ hτ
        by_cases hτc : τ ≤ c
        · exact hcA.2 τ ⟨hτ.1, hτc⟩
        · rw [not_le] at hτc
          have hτI : τ ∈ Set.Icc a b := ⟨hτ.1, hτ.2.trans hx.2⟩
          have hτd : |τ - c| < δ₁ := by
            rw [abs_sub_lt_iff]
            constructor
            · linarith [hτ.2]
            · linarith
          exact hOc (ζ τ) (hδ₁ τ hτI hτd)
    exact fun σ hσ ↦ hbA.2 σ hσ
  -- ## §9 The adjacent-path lemma (fixed endpoints).
  have hadj : ∀ (η : ℝ × ℝ → M), Continuous η → (∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 0)
      = p₁) →
      (∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 1) = η (0, 1)) →
      ∀ s₀ ∈ Set.Icc (0:ℝ) 1, ∀ Φ, IsCont (fun t ↦ η (s₀, t)) 1 Φ →
      ∃ ε > 0, ∀ s' ∈ Set.Icc (0:ℝ) 1, |s' - s₀| < ε →
        ∃ Φ', IsCont (fun t ↦ η (s', t)) 1 Φ' ∧ Φ' 1 =ᶠ[𝓝 (η (0, 1))] Φ 1 := by
    intro η hη hη0 hη1 s₀ hs₀ Φ hΦ
    rw [hIC] at hΦ
    obtain ⟨hΦa, hΦ0, hΦc⟩ := hΦ
    -- per-time data: an element window around the s₀-path with a stability radius
    have hdata : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ d > 0, ∃ W : Set M, IsOpen W ∧
        (∀ z ∈ W, Q (Φ t) z) ∧
        (∀ p : ℝ × ℝ, |p.1 - s₀| < d → |p.2 - t| < d → η p ∈ W) ∧
        (∀ u ∈ Set.Icc (0:ℝ) 1, |u - t| < d → Φ u =ᶠ[𝓝 (η (s₀, u))] Φ t) := by
      intro t ht
      obtain ⟨W, hWo, hWmem, hWall⟩ := hQopen (Φ t) (η (s₀, t)) (hΦa t ht)
      obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc t ht
      have hpre : η ⁻¹' W ∈ 𝓝 (s₀, t) :=
        hη.continuousAt.preimage_mem_nhds (hWo.mem_nhds hWmem)
      obtain ⟨r, hr0, hrsub⟩ := Metric.mem_nhds_iff.mp hpre
      refine ⟨min r ε₁, lt_min hr0 hε₁0, W, hWo, fun z hz ↦ (hWall z hz).1, ?_, ?_⟩
      · intro p hp1 hp2
        apply hrsub
        rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt (lt_of_lt_of_le hp1 (min_le_left _ _))
          (lt_of_lt_of_le hp2 (min_le_left _ _))
      · intro u hu hud
        exact hε₁p u hu (lt_of_lt_of_le hud (min_le_right _ _))
    choose! dfun hd0 W hWo hWQ hWnear hloc using hdata
    -- a uniform radius: cover [0,1] with half-windows, finite subcover, finite minimum
    have hcover : Set.Icc (0:ℝ) 1 ⊆
        ⋃ t : ↥(Set.Icc (0:ℝ) 1), ball (t : ℝ) (dfun (t : ℝ) / 2) := by
      intro x hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self ?_⟩
      have h1 := hd0 x hx
      linarith
    obtain ⟨T, hTcov⟩ := isCompact_Icc.elim_finite_subcover
      (fun t : ↥(Set.Icc (0:ℝ) 1) ↦ ball (t : ℝ) (dfun (t : ℝ) / 2))
      (fun _ ↦ isOpen_ball) hcover
    have hTne : T.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have h0 := hTcov (Set.left_mem_Icc.mpr zero_le_one)
      rw [hemp] at h0
      simp at h0
    have hε0 : 0 < T.inf' hTne (fun t ↦ dfun (t : ℝ) / 2) := by
      rw [Finset.lt_inf'_iff]
      intro t htT
      have h1 := hd0 (t : ℝ) t.2
      linarith
    refine ⟨T.inf' hTne (fun t ↦ dfun (t : ℝ) / 2), hε0, ?_⟩
    intro s' hs' hss
    -- the grid: N₀ with 1 / (N₀ + 1) below the uniform radius
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε0
    -- interval assignment: each grid interval sits inside one data window
    have hassign : ∀ i : ℕ, i ≤ N₀ → ∃ t ∈ Set.Icc (0:ℝ) 1,
        (∀ u : ℝ, (i : ℝ) / ((N₀ : ℝ) + 1) ≤ u → u ≤ ((i : ℝ) + 1) / ((N₀ : ℝ)
            + 1) →
          |u - t| < dfun t) ∧ |s' - s₀| < dfun t := by
      intro i hi
      have hgi : (i : ℝ) / ((N₀ : ℝ) + 1) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · positivity
        · rw [div_le_one (by positivity)]
          have h1 : (i : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hi
          linarith
      have hmem := hTcov hgi
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨t, htT, hgt⟩ := hmem
      have hεle : T.inf' hTne (fun t ↦ dfun (t : ℝ) / 2) ≤ dfun (t : ℝ) / 2 :=
        Finset.inf'_le _ htT
      have hdt0 : 0 < dfun (t : ℝ) := hd0 (t : ℝ) t.2
      have hdist : |(i : ℝ) / ((N₀ : ℝ) + 1) - (t : ℝ)| < dfun (t : ℝ) / 2 := by
        have h1 := mem_ball.mp hgt
        rwa [Real.dist_eq] at h1
      rw [abs_sub_lt_iff] at hdist
      refine ⟨(t : ℝ), t.2, ?_, ?_⟩
      · intro u hu1 hu2
        have hstep : u - (i : ℝ) / ((N₀ : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
          rw [add_div] at hu2
          linarith
        rw [abs_sub_lt_iff]
        constructor
        · linarith [hdist.1, hN₀, hεle]
        · linarith [hdist.2, hu1]
      · calc |s' - s₀| < T.inf' hTne (fun t ↦ dfun (t : ℝ) / 2) := hss
          _ ≤ dfun (t : ℝ) / 2 := hεle
          _ < dfun (t : ℝ) := by linarith
    choose! tc htcI htcwin htcs using hassign
    -- segment membership and distance comparison
    have hsegI : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → σ ∈ Set.Icc (0:ℝ) 1 := by
      intro σ h1 h2
      constructor
      · rcases le_total s₀ s' with h | h
        · rw [min_eq_left h] at h1; linarith [hs₀.1]
        · rw [min_eq_right h] at h1; linarith [hs'.1]
      · rcases le_total s₀ s' with h | h
        · rw [max_eq_right h] at h2; linarith [hs'.2]
        · rw [max_eq_left h] at h2; linarith [hs₀.2]
    have habs : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → |σ - s₀| ≤ |s' - s₀| := by
      intro σ h1 h2
      rcases le_total s₀ s' with hle | hle
      · rw [min_eq_left hle] at h1
        rw [max_eq_right hle] at h2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · rw [min_eq_right hle] at h1
        rw [max_eq_left hle] at h2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    -- transport specialised to the σ-segment at a fixed height
    have hseg : ∀ (u : ℝ) (ψ ψ' : M → ℂ̂),
        (∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → ∀ᶠ y in 𝓝 (η (σ, u)), Q ψ
            y) →
        (∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → ∀ᶠ y in 𝓝 (η (σ, u)), Q ψ'
            y) →
        ψ =ᶠ[𝓝 (η (s₀, u))] ψ' → ψ =ᶠ[𝓝 (η (s', u))] ψ' := by
      intro u ψ ψ' hq1 hq2 heq
      rcases le_total s₀ s' with hle | hle
      · have hcont1 : Continuous fun σ : ℝ ↦ η (σ, u) :=
          hη.comp (continuous_id.prodMk continuous_const)
        exact htransport ψ ψ' (fun σ ↦ η (σ, u)) s₀ s' hle hcont1.continuousOn
          (fun σ hσ ↦ hq1 σ (by rw [min_eq_left hle]; exact hσ.1)
            (by rw [max_eq_right hle]; exact hσ.2))
          (fun σ hσ ↦ hq2 σ (by rw [min_eq_left hle]; exact hσ.1)
            (by rw [max_eq_right hle]; exact hσ.2))
          heq s' ⟨hle, le_refl s'⟩
      · have hcont2 : Continuous fun σ : ℝ ↦ η (s₀ + s' - σ, u) :=
          hη.comp ((continuous_const.sub continuous_id).prodMk continuous_const)
        have h1 := htransport ψ ψ' (fun σ ↦ η (s₀ + s' - σ, u)) s' s₀ hle
          hcont2.continuousOn
          (fun σ hσ ↦ hq1 (s₀ + s' - σ)
            (by rw [min_eq_right hle]; linarith [hσ.2])
            (by rw [max_eq_left hle]; linarith [hσ.1]))
          (fun σ hσ ↦ hq2 (s₀ + s' - σ)
            (by rw [min_eq_right hle]; linarith [hσ.2])
            (by rw [max_eq_left hle]; linarith [hσ.1]))
          (by
            have h2 : s₀ + s' - s' = s₀ := by ring
            simpa [h2] using heq)
          s₀ ⟨hle, le_refl s₀⟩
        have h3 : s₀ + s' - s₀ = s' := by ring
        simpa [h3] using h1
    -- grid induction: continuation along the s'-path up to each grid point,
    -- with the terminal germ locked to that of the s₀-continuation
    have hkey : ∀ i : ℕ, i ≤ N₀ + 1 →
        ∃ Φ', IsCont (fun t ↦ η (s', t)) ((i : ℝ) / ((N₀ : ℝ) + 1)) Φ' ∧
        ∀ ψtar : M → ℂ̂,
          Φ ((i : ℝ) / ((N₀ : ℝ) + 1)) =ᶠ[𝓝 (η (s₀, (i : ℝ) / ((N₀ : ℝ) + 1)))]
              ψtar →
          (∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' →
            ∀ᶠ y in 𝓝 (η (σ, (i : ℝ) / ((N₀ : ℝ) + 1))), Q ψtar y) →
          Φ' ((i : ℝ) / ((N₀ : ℝ) + 1)) =ᶠ[𝓝 (η (s', (i : ℝ) / ((N₀ : ℝ) + 1)))]
              ψtar := by
      intro i
      induction i with
      | zero =>
        intro _
        have h00 : ((0 : ℕ) : ℝ) / ((N₀ : ℝ) + 1) = 0 := by norm_num
        rw [h00]
        have hp0' : η (s', 0) = p₁ := hη0 s' hs'
        have hp0 : η (s₀, 0) = p₁ := hη0 s₀ hs₀
        refine ⟨fun _ ↦ Φ 0, ?_, ?_⟩
        · rw [hIC]
          refine ⟨?_, ?_, ?_⟩
          · intro t ht
            have ht0 : t = 0 := le_antisymm ht.2 ht.1
            rw [ht0, hp0']
            have h1 := hΦa 0 ⟨le_refl 0, zero_le_one⟩
            rw [hp0] at h1
            exact h1
          · exact hΦ0
          · intro t ht
            exact ⟨1, one_pos, fun u hu _ ↦ Filter.EventuallyEq.refl _ _⟩
        · intro ψtar htar hQtar
          rw [hp0] at htar
          rw [hp0']
          exact htar
      | succ i ih =>
        intro hi1
        have hiN : i ≤ N₀ := Nat.succ_le_succ_iff.mp hi1
        obtain ⟨Φ', hΦ'IC, hΦ'germ⟩ := ih (Nat.le_succ_of_le hiN)
        have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hNR : (0:ℝ) < (N₀ : ℝ) + 1 := by positivity
        have hgiI : (i : ℝ) / ((N₀ : ℝ) + 1) ∈ Set.Icc (0:ℝ) 1 := by
          constructor
          · positivity
          · rw [div_le_one hNR]
            have h1 : (i : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hiN
            linarith
        have hgi1I : ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) ∈ Set.Icc (0:ℝ) 1 := by
          constructor
          · positivity
          · rw [div_le_one hNR]
            have h1 : (i : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hiN
            linarith
        have hgilt : (i : ℝ) / ((N₀ : ℝ) + 1) < ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) := by
          have h1 : ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) - (i : ℝ) / ((N₀ : ℝ) + 1) =
              1 / ((N₀ : ℝ) + 1) := by
            rw [div_sub_div_same]
            norm_num
          have h2 : (0:ℝ) < 1 / ((N₀ : ℝ) + 1) := by positivity
          linarith
        -- window facts for interval i
        have hIci : tc i ∈ Set.Icc (0:ℝ) 1 := htcI i hiN
        have hwin := htcwin i hiN
        have hswin : |s' - s₀| < dfun (tc i) := htcs i hiN
        have hK1 : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → ∀ u, (i : ℝ) / ((N₀ :
            ℝ) + 1) ≤ u →
            u ≤ ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) → η (σ, u) ∈ W (tc i) := by
          intro σ h1 h2 u h3 h4
          refine hWnear (tc i) hIci (σ, u) ?_ (hwin u h3 h4)
          calc |σ - s₀| ≤ |s' - s₀| := habs σ h1 h2
            _ < dfun (tc i) := hswin
        have hK2 : ∀ u, (i : ℝ) / ((N₀ : ℝ) + 1) ≤ u → u ≤ ((i : ℝ) + 1) / ((N₀ :
            ℝ) + 1) →
            u ∈ Set.Icc (0:ℝ) 1 → Φ u =ᶠ[𝓝 (η (s₀, u))] Φ (tc i) := by
          intro u h1 h2 hu
          exact hloc (tc i) hIci u hu (hwin u h1 h2)
        -- junction germ at the grid point gi
        have hjunc : Φ' ((i : ℝ) / ((N₀ : ℝ) + 1))
            =ᶠ[𝓝 (η (s', (i : ℝ) / ((N₀ : ℝ) + 1)))] Φ (tc i) := by
          refine hΦ'germ (Φ (tc i)) (hK2 _ (le_refl _) hgilt.le hgiI) ?_
          intro σ hσ1 hσ2
          have hmem : η (σ, (i : ℝ) / ((N₀ : ℝ) + 1)) ∈ W (tc i) :=
            hK1 σ hσ1 hσ2 _ (le_refl _) hgilt.le
          filter_upwards [(hWo (tc i) hIci).mem_nhds hmem] with y hy using
            hWQ (tc i) hIci y hy
        refine ⟨fun u ↦ if u ≤ (i : ℝ) / ((N₀ : ℝ) + 1) then Φ' u else Φ (tc i), ?_,
            ?_⟩
        · rw [hIC] at hΦ'IC ⊢
          obtain ⟨hpa, hp0, hpc⟩ := hΦ'IC
          refine ⟨?_, ?_, ?_⟩
          · intro t ht
            by_cases hta : t ≤ (i : ℝ) / ((N₀ : ℝ) + 1)
            · rw [ite_eq_left hta]
              exact hpa t ⟨ht.1, hta⟩
            · rw [not_le] at hta
              rw [ite_eq_right (not_le.mpr hta)]
              have hmem : η (s', t) ∈ W (tc i) :=
                hK1 s' (min_le_right _ _) (le_max_right _ _) t hta.le ht.2
              filter_upwards [(hWo (tc i) hIci).mem_nhds hmem] with y hy using
                hWQ (tc i) hIci y hy
          · have hnn : (0:ℝ) ≤ (i : ℝ) / ((N₀ : ℝ) + 1) := by positivity
            rw [ite_eq_left hnn]
            exact hp0
          · intro t ht
            rcases lt_trichotomy t ((i : ℝ) / ((N₀ : ℝ) + 1)) with hta | hta | hta
            · obtain ⟨ε', hε'0, hε'p⟩ := hpc t ⟨ht.1, hta.le⟩
              refine ⟨min ε' ((i : ℝ) / ((N₀ : ℝ) + 1) - t), lt_min hε'0 (by linarith),
                  ?_⟩
              intro u hu huε
              rw [lt_min_iff] at huε
              have hua : u ≤ (i : ℝ) / ((N₀ : ℝ) + 1) := by
                have h6 := abs_sub_lt_iff.mp huε.2
                linarith [h6.1]
              rw [ite_eq_left hua, ite_eq_left hta.le]
              exact hε'p u ⟨hu.1, hua⟩ huε.1
            · rw [hta]
              obtain ⟨ε', hε'0, hε'p⟩ := hpc ((i : ℝ) / ((N₀ : ℝ) + 1))
                ⟨by positivity, le_refl _⟩
              obtain ⟨O₂, hO₂o, hO₂mem, hO₂⟩ := hOpen _ _ _ hjunc
              have hcont' : Continuous fun t : ℝ ↦ η (s', t) :=
                hη.comp (continuous_const.prodMk continuous_id)
              obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hγnb (fun t ↦ η (s', t)) (Set.Icc 0 1)
                ((i : ℝ) / ((N₀ : ℝ) + 1)) hcont'.continuousOn hgiI O₂ hO₂o hO₂mem
              refine ⟨min ε' δ₂, lt_min hε'0 hδ₂0, ?_⟩
              intro u hu huε
              rw [lt_min_iff] at huε
              have huI : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1, hu.2.trans hgi1I.2⟩
              by_cases hua : u ≤ (i : ℝ) / ((N₀ : ℝ) + 1)
              · rw [ite_eq_left hua, ite_eq_left (le_refl _)]
                exact hε'p u ⟨hu.1, hua⟩ huε.1
              · rw [not_le] at hua
                rw [ite_eq_right (not_le.mpr hua), ite_eq_left (le_refl _)]
                have hmem2 : η (s', u) ∈ O₂ := hδ₂ u huI huε.2
                exact (hO₂ (η (s', u)) hmem2).symm
            · refine ⟨t - (i : ℝ) / ((N₀ : ℝ) + 1), by linarith, ?_⟩
              intro u hu huε
              rw [abs_sub_lt_iff] at huε
              have hua : (i : ℝ) / ((N₀ : ℝ) + 1) < u := by linarith [huε.2]
              rw [ite_eq_right (not_le.mpr hua), ite_eq_right (not_le.mpr hta)]
        · intro ψtar htar hQtar
          have hne1 : ¬(((i : ℝ) + 1) / ((N₀ : ℝ) + 1) ≤ (i : ℝ) / ((N₀ : ℝ) + 1)) :=
            not_le.mpr hgilt
          have hval : (fun u ↦ if u ≤ (i : ℝ) / ((N₀ : ℝ) + 1) then Φ' u else Φ (tc i))
              (((i : ℝ) + 1) / ((N₀ : ℝ) + 1)) = Φ (tc i) := ite_eq_right hne1
          rw [hval]
          have h1 : Φ (tc i) =ᶠ[𝓝 (η (s₀, ((i : ℝ) + 1) / ((N₀ : ℝ) + 1)))] ψtar :=
            (hK2 _ hgilt.le (le_refl _) hgi1I).symm.trans htar
          refine hseg _ (Φ (tc i)) ψtar ?_ hQtar h1
          intro σ hσ1 hσ2
          have hmem : η (σ, ((i : ℝ) + 1) / ((N₀ : ℝ) + 1)) ∈ W (tc i) :=
            hK1 σ hσ1 hσ2 _ hgilt.le (le_refl _)
          filter_upwards [(hWo (tc i) hIci).mem_nhds hmem] with y hy using
            hWQ (tc i) hIci y hy
    -- conclude at the last grid point
    obtain ⟨Φ', hΦ'IC, hΦ'germ⟩ := hkey (N₀ + 1) (le_refl _)
    have hNN : ((N₀ + 1 : ℕ) : ℝ) / ((N₀ : ℝ) + 1) = 1 := by
      push_cast
      exact div_self (by positivity : (0:ℝ) < (N₀ : ℝ) + 1).ne'
    rw [hNN] at hΦ'IC hΦ'germ
    have hQ1seg : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' →
        ∀ᶠ y in 𝓝 (η (σ, 1)), Q (Φ 1) y := by
      intro σ hσ1 hσ2
      have hσI : σ ∈ Set.Icc (0:ℝ) 1 := hsegI σ hσ1 hσ2
      have h2 : η (σ, 1) = η (s₀, 1) := by rw [hη1 σ hσI, hη1 s₀ hs₀]
      rw [h2]
      exact hΦa 1 ⟨zero_le_one, le_refl 1⟩
    have hfin := hΦ'germ (Φ 1) (Filter.EventuallyEq.refl _ _) hQ1seg
    rw [hη1 s' hs'] at hfin
    exact ⟨Φ', hΦ'IC, hfin⟩
  -- ## §10 Homotopy invariance of the terminal germ.
  have hhomo : ∀ (η : ℝ × ℝ → M), Continuous η → (∀ s ∈ Set.Icc (0:ℝ) 1, η (s,
      0) = p₁) →
      (∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 1) = η (0, 1)) →
      ∀ Φ₀ Φ₁, IsCont (fun t ↦ η (0, t)) 1 Φ₀ → IsCont (fun t ↦ η (1, t)) 1 Φ₁
          →
        Φ₁ 1 =ᶠ[𝓝 (η (0, 1))] Φ₀ 1 := by
    intro η hη hη0 hη1 Φ₀ Φ₁ hΦ₀ hΦ₁
    have h1A : (1:ℝ) ∈ {s | s ∈ Set.Icc (0:ℝ) 1 ∧ ∃ Φ, IsCont (fun t ↦ η (s, t)) 1 Φ
        ∧
        Φ 1 =ᶠ[𝓝 (η (0, 1))] Φ₀ 1} := by
      refine hind 0 1 _ zero_le_one (fun x hx ↦ hx.1)
        ⟨⟨le_refl 0, zero_le_one⟩, Φ₀, hΦ₀, Filter.EventuallyEq.refl _ _⟩ ?_ ?_
      · -- closed from the left: adjacency at the limit parameter
        intro c hc hap
        have hγc : ContinuousOn (fun t ↦ η (c, t)) (Set.Icc 0 1) :=
          (hη.comp (continuous_const.prodMk continuous_id)).continuousOn
        obtain ⟨Φc, hΦc⟩ := hexist (fun t ↦ η (c, t)) hγc (hη0 c hc)
        obtain ⟨ε, hε0, hεadj⟩ := hadj η hη hη0 hη1 c hc Φc hΦc
        obtain ⟨x, hxA, hxgt, hxle⟩ := hap ε hε0
        obtain ⟨Φx, hΦx, hΦxeq⟩ := hxA.2
        have hxd : |x - c| < ε := by
          rw [abs_sub_lt_iff]
          constructor <;> linarith
        obtain ⟨Φ'x, hΦ'x, hΦ'xeq⟩ := hεadj x hxA.1 hxd
        have huu := huniq (fun t ↦ η (x, t))
          ((hη.comp (continuous_const.prodMk continuous_id)).continuousOn)
          (hη0 x hxA.1) Φx Φ'x hΦx hΦ'x 1 ⟨zero_le_one, le_refl 1⟩
        have hpt : η (x, 1) = η (0, 1) := hη1 x hxA.1
        have huu' : Φx 1 =ᶠ[𝓝 (η (0, 1))] Φ'x 1 := by
          rw [← hpt]
          exact huu
        exact ⟨hc, Φc, hΦc, hΦ'xeq.symm.trans (huu'.symm.trans hΦxeq)⟩
      · -- open to the right: adjacency from a member parameter
        intro c hcA hclt
        obtain ⟨Φc, hΦc, hΦceq⟩ := hcA.2
        obtain ⟨ε, hε0, hεadj⟩ := hadj η hη hη0 hη1 c hcA.1 Φc hΦc
        refine ⟨ε, hε0, ?_⟩
        intro x hx hcx hxδ
        have hxd : |x - c| < ε := by
          rw [abs_sub_lt_iff]
          constructor <;> linarith
        obtain ⟨Φ'x, hΦ'x, hΦ'xeq⟩ := hεadj x hx hxd
        exact ⟨hx, Φ'x, hΦ'x, hΦ'xeq.trans hΦceq⟩
    obtain ⟨-, Φ, hΦ, hΦeq⟩ := h1A
    have huu := huniq (fun t ↦ η (1, t))
      ((hη.comp (continuous_const.prodMk continuous_id)).continuousOn)
      (hη0 1 ⟨zero_le_one, le_refl 1⟩) Φ₁ Φ hΦ₁ hΦ 1 ⟨zero_le_one, le_refl 1⟩
    have hpt : η (1, 1) = η (0, 1) := hη1 1 ⟨zero_le_one, le_refl 1⟩
    have huu' : Φ₁ 1 =ᶠ[𝓝 (η (0, 1))] Φ 1 := by
      rw [← hpt]
      exact huu
    exact huu'.trans hΦeq
  -- ## §11 Global assembly along paths.
  have hsel : ∀ q : M,
      ∃ Φ, IsCont (fun u ↦ (PathConnectedSpace.somePath p₁ q).extend u) 1 Φ := by
    intro q
    refine hexist _ (Path.continuous_extend _).continuousOn ?_
    exact Path.extend_zero _
  choose ΦF hΦF using hsel
  have hQq : ∀ q : M, Q (ΦF q 1) q ∧ ∀ᶠ y in 𝓝 q, Q (ΦF q 1) y := by
    intro q
    have h1 := ((hIC _ _ _).mp (hΦF q)).1 1 ⟨zero_le_one, le_refl 1⟩
    rw [Path.extend_one] at h1
    exact ⟨Eventually.self_of_nhds h1, h1⟩
  -- local agreement: near any point, every chosen terminal element realises the
  -- same germ, by comparing paths through a chart-ball concatenation.
  have hlocal : ∀ q : M, ∃ B : Set M, IsOpen B ∧ q ∈ B ∧
      ∀ q' ∈ B, ΦF q' 1 =ᶠ[𝓝 q'] ΦF q 1 := by
    intro q
    obtain ⟨W, hWo, hqW, hWall⟩ := hQopen (ΦF q 1) q (hQq q).2
    have hqs : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
    have hT : IsOpen ((chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W) :=
      (chartAt ℂ q).isOpen_inter_preimage_symm hWo
    have hqT : chartAt ℂ q q ∈ (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W := by
      refine ⟨(chartAt ℂ q).map_source hqs, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ q).left_inv hqs]
      exact hqW
    obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hT _ hqT
    refine ⟨(chartAt ℂ q).source ∩ chartAt ℂ q ⁻¹' ball (chartAt ℂ q q) r,
      (chartAt ℂ q).continuousOn.isOpen_inter_preimage (chartAt ℂ q).open_source
        isOpen_ball,
      ⟨hqs, by rw [Set.mem_preimage]; exact mem_ball_self hr0⟩, ?_⟩
    intro q' hq'
    have hq's : q' ∈ (chartAt ℂ q).source := hq'.1
    have hq'b : chartAt ℂ q q' ∈ ball (chartAt ℂ q q) r := hq'.2
    -- the straight chart segment from q to q' stays in the ball
    have hsegmem : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
        (1 - (σ:ℂ)) * chartAt ℂ q q + (σ:ℂ) * chartAt ℂ q q' ∈
          ball (chartAt ℂ q q) r := by
      intro σ h0 h1
      rw [mem_ball, dist_eq_norm]
      have h2 : (1 - (σ:ℂ)) * chartAt ℂ q q + (σ:ℂ) * chartAt ℂ q q' -
          chartAt ℂ q q = (σ:ℂ) * (chartAt ℂ q q' - chartAt ℂ q q) := by ring
      have h3 : ‖chartAt ℂ q q' - chartAt ℂ q q‖ < r := by
        have h4 := mem_ball.mp hq'b
        rwa [dist_eq_norm] at h4
      rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
      calc σ * ‖chartAt ℂ q q' - chartAt ℂ q q‖ ≤
          1 * ‖chartAt ℂ q q' - chartAt ℂ q q‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖chartAt ℂ q q' - chartAt ℂ q q‖ := one_mul _
        _ < r := h3
    have hinner : Continuous fun σ : ℝ ↦
        (1 - (σ:ℂ)) * chartAt ℂ q q + (σ:ℂ) * chartAt ℂ q q' :=
      ((continuous_const.sub Complex.continuous_ofReal).mul continuous_const).add
        (Complex.continuous_ofReal.mul continuous_const)
    have hρc : Continuous fun σ : unitInterval ↦ (chartAt ℂ q).symm
        ((1 - ((σ:ℝ):ℂ)) * chartAt ℂ q q + ((σ:ℝ):ℂ) * chartAt ℂ q q') := by
      refine (chartAt ℂ q).continuousOn_symm.comp_continuous
        (hinner.comp continuous_subtype_val) ?_
      intro σ
      exact (hrsub (hsegmem (σ:ℝ) σ.2.1 σ.2.2)).1
    obtain ⟨ρpath, hρW⟩ : ∃ ρ : Path q q',
        ∀ σ : ℝ, σ ∈ Set.Icc (0:ℝ) 1 → ρ.extend σ ∈ W := by
      refine ⟨{ toFun := fun σ ↦ (chartAt ℂ q).symm
                  ((1 - ((σ:ℝ):ℂ)) * chartAt ℂ q q + ((σ:ℝ):ℂ) * chartAt ℂ q q'),
                continuous_toFun := hρc,
                source' := ?_,
                target' := ?_ }, ?_⟩
      · have h0 : (1 - (((0 : unitInterval) : ℝ) : ℂ)) * chartAt ℂ q q +
            (((0 : unitInterval) : ℝ) : ℂ) * chartAt ℂ q q' = chartAt ℂ q q := by
          norm_num
        rw [h0]
        exact (chartAt ℂ q).left_inv hqs
      · have h1 : (1 - (((1 : unitInterval) : ℝ) : ℂ)) * chartAt ℂ q q +
            (((1 : unitInterval) : ℝ) : ℂ) * chartAt ℂ q q' = chartAt ℂ q q' := by
          norm_num
        rw [h1]
        exact (chartAt ℂ q).left_inv hq's
      · intro σ hσ
        rw [Path.extend_apply _ hσ]
        change (chartAt ℂ q).symm ((1 - (σ:ℂ)) * chartAt ℂ q q +
          (σ:ℂ) * chartAt ℂ q q') ∈ W
        have h5 := (hrsub (hsegmem σ hσ.1 hσ.2)).2
        rwa [Set.mem_preimage] at h5
    -- the concatenated path realises the same terminal element as the base point
    have htrans_le : ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 → u ≤ 1/2 →
        ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend u =
          (PathConnectedSpace.somePath p₁ q).extend (2*u) := by
      intro u hu hle
      have h2u : (2*u : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hu.1], by linarith⟩
      rw [Path.extend_apply _ hu, Path.extend_apply _ h2u, Path.trans_apply]
      have hcond : ((⟨u, hu⟩ : unitInterval) : ℝ) ≤ 1/2 := hle
      rw [dite_eq_left hcond]
    have htrans_gt : ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 → ¬(u ≤ 1/2) →
        ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend u =
          ρpath.extend (2*u - 1) := by
      intro u hu hgt
      have h2u : (2*u - 1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · linarith [not_le.mp hgt]
        · linarith [hu.2]
      rw [Path.extend_apply _ hu, Path.extend_apply _ h2u, Path.trans_apply]
      have hcond : ¬(((⟨u, hu⟩ : unitInterval) : ℝ) ≤ 1/2) := hgt
      rw [dite_eq_right hcond]
    -- glued continuation along the concatenated path
    have hICτ : IsCont (fun u ↦ ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend u)
        1 (fun u ↦ if u ≤ 1/2 then ΦF q (2*u) else ΦF q 1) := by
      obtain ⟨hΦqa, hΦq0, hΦqc⟩ := (hIC _ _ _).mp (hΦF q)
      rw [hIC]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        by_cases hth : t ≤ 1/2
        · rw [ite_eq_left hth, htrans_le t ht hth]
          exact hΦqa (2*t) ⟨by linarith [ht.1], by linarith⟩
        · rw [ite_eq_right hth, htrans_gt t ht hth]
          have hmem : ρpath.extend (2*t - 1) ∈ W := by
            refine hρW (2*t - 1) ⟨?_, ?_⟩
            · linarith [not_le.mp hth]
            · linarith [ht.2]
          filter_upwards [hWo.mem_nhds hmem] with y hy using (hWall y hy).1
      · have h012 : (0:ℝ) ≤ 1/2 := by norm_num
        rw [ite_eq_left h012]
        have h20 : (2:ℝ) * 0 = 0 := by norm_num
        rw [h20]
        exact hΦq0
      · intro t ht
        rcases lt_trichotomy t (1/2 : ℝ) with hth | hth | hth
        · obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦqc (2*t) ⟨by linarith [ht.1], by linarith⟩
          refine ⟨min (ε₁/2) (1/2 - t), lt_min (by linarith) (by linarith), ?_⟩
          intro u hu huε
          rw [lt_min_iff] at huε
          have huh : u ≤ 1/2 := by
            have h6 := abs_sub_lt_iff.mp huε.2
            linarith [h6.1]
          have hu2 : |2*u - 2*t| < ε₁ := by
            have h6 := abs_sub_lt_iff.mp huε.1
            rw [abs_sub_lt_iff]
            constructor <;> linarith [h6.1, h6.2]
          rw [ite_eq_left huh, ite_eq_left hth.le, htrans_le u hu huh]
          exact hε₁p (2*u) ⟨by linarith [hu.1], by linarith⟩ hu2
        · obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦqc 1 ⟨zero_le_one, le_refl 1⟩
          refine ⟨ε₁/2, by linarith, ?_⟩
          intro u hu huε
          have h2t : (2:ℝ)*t = 1 := by rw [hth]; norm_num
          by_cases huh : u ≤ 1/2
          · rw [ite_eq_left huh, ite_eq_left hth.le, h2t, htrans_le u hu huh]
            have hu2 : |2*u - 1| < ε₁ := by
              have h6 := abs_sub_lt_iff.mp huε
              rw [abs_sub_lt_iff]
              constructor <;> linarith [h6.1, h6.2]
            exact hε₁p (2*u) ⟨by linarith [hu.1], by linarith⟩ hu2
          · rw [ite_eq_right huh, ite_eq_left hth.le, h2t]
        · refine ⟨t - 1/2, by linarith, ?_⟩
          intro u hu huε
          have huh : ¬(u ≤ 1/2) := by
            rw [abs_sub_lt_iff] at huε
            rw [not_le]
            linarith [huε.2]
          rw [ite_eq_right huh, ite_eq_right (not_le.mpr hth)]
    -- the homotopy between the chosen path of q' and the concatenation
    obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic
      (PathConnectedSpace.somePath p₁ q') ((PathConnectedSpace.somePath p₁ q).trans ρpath)
    obtain ⟨η, hηeq⟩ : ∃ η' : ℝ × ℝ → M, η' = fun p ↦
        H (Set.projIcc 0 1 zero_le_one p.1, Set.projIcc 0 1 zero_le_one p.2) := ⟨_, rfl⟩
    have happ : ∀ a b : ℝ, η (a, b) =
        H (Set.projIcc 0 1 zero_le_one a, Set.projIcc 0 1 zero_le_one b) := by
      intro a b
      rw [hηeq]
    have h0I : Set.projIcc (0:ℝ) 1 zero_le_one (0:ℝ) = (0 : unitInterval) := by
      apply Subtype.ext
      rw [Set.coe_projIcc]
      have h1 : ((0 : unitInterval) : ℝ) = 0 := rfl
      rw [h1]
      norm_num
    have h1I : Set.projIcc (0:ℝ) 1 zero_le_one (1:ℝ) = (1 : unitInterval) := by
      apply Subtype.ext
      rw [Set.coe_projIcc]
      have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
      rw [h1]
      norm_num
    have hηc : Continuous η := by
      rw [hηeq]
      exact H.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk
        (continuous_projIcc.comp continuous_snd))
    have hbdry0 : ∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 0) = p₁ := by
      intro s hs
      rw [happ, h0I]
      exact Path.Homotopy.source H _
    have hbdry1 : ∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 1) = η (0, 1) := by
      intro s hs
      rw [happ s 1, happ 0 1, h1I]
      rw [Path.Homotopy.target, Path.Homotopy.target]
    have hη01 : η (0, 1) = q' := by
      rw [happ 0 1, h1I]
      exact Path.Homotopy.target H _
    have hpath0 : (fun t : ℝ ↦ η (0, t)) =
        (fun t : ℝ ↦ (PathConnectedSpace.somePath p₁ q').extend t) := by
      funext t
      rw [happ, h0I]
      exact ContinuousMap.HomotopyWith.apply_zero H (Set.projIcc 0 1 zero_le_one t)
    have hpath1 : (fun t : ℝ ↦ η (1, t)) =
        (fun t : ℝ ↦ ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend t) := by
      funext t
      rw [happ, h1I]
      exact ContinuousMap.HomotopyWith.apply_one H (Set.projIcc 0 1 zero_le_one t)
    have hIC0 : IsCont (fun t ↦ η (0, t)) 1 (ΦF q') := by
      rw [hpath0]
      exact hΦF q'
    have hIC1 : IsCont (fun t ↦ η (1, t)) 1
        (fun u ↦ if u ≤ 1/2 then ΦF q (2*u) else ΦF q 1) := by
      rw [hpath1]
      exact hICτ
    have hfinal := hhomo η hηc hbdry0 hbdry1 (ΦF q')
      (fun u ↦ if u ≤ 1/2 then ΦF q (2*u) else ΦF q 1) hIC0 hIC1
    rw [hη01] at hfinal
    have hn12 : ¬((1:ℝ) ≤ 1/2) := by norm_num
    rw [ite_eq_right hn12] at hfinal
    exact hfinal.symm
  -- the global map and its four properties
  refine ⟨fun q ↦ ΦF q 1 q, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨B, hBo, hqB, hBloc⟩ := hlocal q
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ΦF q 1) q := by
      have h2 := (hQq q).1
      rw [hQ] at h2
      exact h2.1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hBo.mem_nhds hqB] with q'' hq''
    exact (hBloc q'' hq'').eq_of_nhds
  · have h2 := (hQq p₁).1
    rw [hQ] at h2
    exact h2.2.2.1 rfl
  · have h2 := (hQq p₂).1
    rw [hQ] at h2
    exact h2.2.2.2 rfl
  · intro x hx1 hx2
    have h2 := (hQq x).1
    rw [hQ] at h2
    exact h2.2.1 hx1 hx2

end RiemannDynamics
