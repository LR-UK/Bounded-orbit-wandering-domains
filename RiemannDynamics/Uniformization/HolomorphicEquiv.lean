/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.SphereManifold
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Biholomorphic equivalences of one-dimensional complex manifolds

Shared infrastructure for the uniformization trichotomy: a biholomorphism
between one-dimensional complex-analytic manifolds is an analytic
`Diffeomorph` over the model `𝓘(ℂ)`, written `M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ N`. This
file provides the production and transport lemmas that every case of the
trichotomy consumes:

* an injective holomorphic map between plane domains is biholomorphic onto its
  image (`nonempty_diffeomorph_of_injOn_differentiableOn`);
* the full space `M` is biholomorphic to the open set `⊤ : Opens M`
  (`nonempty_diffeomorph_top`);
* every Möbius transformation of `ℂ̂` is a biholomorphism
  (`exists_gl_smul_diffeomorph`);
* a biholomorphism restricts to a biholomorphism between an open set and its
  image (`exists_diffeomorph_opens_image`);
* a domain in `ℂ̂` avoiding `∞` reads as a plane domain through the finite
  chart (`exists_diffeomorph_opens_planar`);
* simple connectivity transfers along homeomorphisms
  (`simplyConnectedSpace_of_homeomorph`).
-/

open OnePoint Topology TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

/-! ## Topological transfer -/

/-- Simple connectivity is a topological invariant: it transfers along any
homeomorphism. -/
theorem simplyConnectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (h : SimplyConnectedSpace X) :
    SimplyConnectedSpace Y := by
  have := h
  exact e.toHomotopyEquiv.symm.simplyConnectedSpace

/-! ## Producing biholomorphisms -/

/-- The open set `⊤ : Opens M` of a one-dimensional complex manifold is
biholomorphic to `M` itself. -/
theorem nonempty_diffeomorph_top (M : Type*) [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] :
    Nonempty (↥(⊤ : Opens M) ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ M) := by
  refine ⟨{
    toFun := Subtype.val
    invFun := fun x => ⟨x, trivial⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl
    contMDiff_toFun := contMDiff_subtype_val
    contMDiff_invFun := fun x => ?_ }⟩
  have h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y : ↥(⊤ : Opens M) => ((⟨y, trivial⟩ : ↥(⊤ : Opens M))))
      (⟨x, trivial⟩ : ↥(⊤ : Opens M)) := by
    have hid : (fun y : ↥(⊤ : Opens M) => ((⟨y, trivial⟩ : ↥(⊤ : Opens M)))) = id := rfl
    rw [hid]
    exact contMDiffAt_id
  exact (contMDiffAt_subtype_iff
    (f := fun z : M => (⟨z, trivial⟩ : ↥(⊤ : Opens M)))
    (x := (⟨x, trivial⟩ : ↥(⊤ : Opens M)))).mp h

/-- An injective holomorphic map between plane domains is a biholomorphism
onto its image: the inverse is automatically holomorphic. -/
theorem nonempty_diffeomorph_of_injOn_differentiableOn (U V : Opens ℂ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    (himg : f '' U = V) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥V) := by
  classical
  have hUo : IsOpen (U : Set ℂ) := U.isOpen
  have hVo : IsOpen (V : Set ℂ) := V.isOpen
  have hAn : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hUo
  set g : ℂ → ℂ := Function.invFunOn f U
  have hex : ∀ w ∈ (V : Set ℂ), ∃ z ∈ (U : Set ℂ), f z = w := by
    intro w hw
    rw [← himg] at hw
    exact hw
  have hgU : ∀ w ∈ (V : Set ℂ), g w ∈ (U : Set ℂ) := fun w hw =>
    Function.invFunOn_mem (hex w hw)
  have hfg : ∀ w ∈ (V : Set ℂ), f (g w) = w := fun w hw =>
    Function.invFunOn_eq (hex w hw)
  have hgf : ∀ z ∈ (U : Set ℂ), g (f z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hfV : ∀ z ∈ (U : Set ℂ), f z ∈ (V : Set ℂ) := by
    intro z hz
    rw [← himg]
    exact Set.mem_image_of_mem f hz
  -- The local open-mapping property of `f` at every point of `U`.
  have hopen : ∀ z ∈ (U : Set ℂ), 𝓝 (f z) ≤ Filter.map f (𝓝 z) := by
    intro z hz
    rcases (hAn z hz).eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have h1 : ∀ᶠ z' in 𝓝[≠] z, f z' = f z ∧ z' ∈ (U : Set ℂ) :=
        (hconst.and (hUo.eventually_mem hz)).filter_mono nhdsWithin_le_nhds
      obtain ⟨z', ⟨hfz', hz'U⟩, hz'ne⟩ := (h1.and eventually_mem_nhdsWithin).exists
      exact hz'ne (Set.mem_singleton_iff.mpr (hinj hz'U hz hfz'))
    · exact hle
  -- `f` maps open subsets of `U` to open sets.
  have himgOpen : ∀ S : Set ℂ, S ⊆ (U : Set ℂ) → IsOpen S → IsOpen (f '' S) := by
    intro S hSU hSo
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hzS, rfl⟩
    exact Filter.le_def.mp (hopen z (hSU hzS)) _
      (Filter.image_mem_map (hSo.mem_nhds hzS))
  -- The global inverse is continuous on `V`.
  have hgc : ∀ w ∈ (V : Set ℂ), ContinuousAt g w := by
    intro w hw
    have ht : Filter.Tendsto g (𝓝 w) (𝓝 (g w)) := by
      rw [Filter.tendsto_def]
      intro N hN
      have hSo : IsOpen (interior N ∩ (U : Set ℂ)) := isOpen_interior.inter hUo
      have hgwS : g w ∈ interior N ∩ (U : Set ℂ) :=
        ⟨mem_interior_iff_mem_nhds.mpr hN, hgU w hw⟩
      have hfSo : IsOpen (f '' (interior N ∩ (U : Set ℂ))) :=
        himgOpen _ Set.inter_subset_right hSo
      have hwfS : w ∈ f '' (interior N ∩ (U : Set ℂ)) := ⟨g w, hgwS, hfg w hw⟩
      refine Filter.mem_of_superset (hfSo.mem_nhds hwfS) ?_
      rintro w' ⟨z, hzS, rfl⟩
      rw [Set.mem_preimage, hgf z hzS.2]
      exact interior_subset hzS.1
    exact ht
  -- The global inverse is differentiable at every non-critical value.
  have hgd_nc : ∀ w ∈ (V : Set ℂ), deriv f (g w) ≠ 0 → DifferentiableAt ℂ g w := by
    intro w hw hder
    have hfd : HasDerivAt f (deriv f (g w)) (g w) :=
      ((hAn (g w) (hgU w hw)).differentiableAt).hasDerivAt
    have hev : ∀ᶠ y in 𝓝 w, f (g y) = y := by
      filter_upwards [hVo.mem_nhds hw] with y hy using hfg y hy
    exact (HasDerivAt.of_local_left_inverse (hgc w hw) hfd hder hev).differentiableAt
  -- Critical points of `f` are isolated in `U`.
  have hcrit : ∀ z ∈ (U : Set ℂ), ∀ᶠ z' in 𝓝[≠] z, deriv f z' ≠ 0 := by
    intro z hz
    rcases (hAn.deriv z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      obtain ⟨r, hr0, hball⟩ :=
        Metric.eventually_nhds_iff_ball.mp (h0.and (hUo.eventually_mem hz))
      have hconst : ∀ z' ∈ Metric.ball z r, f z' = f z := by
        intro z' hz'
        refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball z r)
          (hf.mono fun p hp => (hball p hp).2) ?_ hz' (Metric.mem_ball_self hr0)
        intro p hp
        rw [fderivWithin_of_isOpen Metric.isOpen_ball hp]
        refine ContinuousLinearMap.ext_ring ?_
        rw [fderiv_apply_one_eq_deriv, (hball p hp).1]
        simp
      have hmem : z + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have heq : z + ((r / 2 : ℝ) : ℂ) = z :=
        hinj (hball _ hmem).2 hz (hconst _ hmem)
      have hr2 : ((r / 2 : ℝ) : ℂ) = 0 := by simpa using heq
      have : (r / 2 : ℝ) = 0 := by exact_mod_cast hr2
      linarith
    · exact hne
  -- The global inverse is differentiable everywhere on `V`
  -- (removable singularity at critical values).
  have hgd : ∀ w ∈ (V : Set ℂ), DifferentiableAt ℂ g w := by
    intro w hw
    by_cases hder : deriv f (g w) = 0
    swap
    · exact hgd_nc w hw hder
    have hz₀U : g w ∈ (U : Set ℂ) := hgU w hw
    obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      ((eventually_nhdsWithin_iff.mp (hcrit (g w) hz₀U)).and (hUo.eventually_mem hz₀U))
    have hballU : Metric.ball (g w) r ⊆ (U : Set ℂ) := fun p hp => (hball p hp).2
    have hWo : IsOpen (f '' Metric.ball (g w) r) :=
      himgOpen _ hballU Metric.isOpen_ball
    have hwW : w ∈ f '' Metric.ball (g w) r :=
      ⟨g w, Metric.mem_ball_self hr0, hfg w hw⟩
    have hWV : f '' Metric.ball (g w) r ⊆ (V : Set ℂ) := by
      rw [← himg]
      exact Set.image_mono hballU
    have hoff : DifferentiableOn ℂ g (f '' Metric.ball (g w) r \ {w}) := by
      rintro w' ⟨⟨z', hz'b, rfl⟩, hw'ne⟩
      have hgz' : g (f z') = z' := hgf z' (hballU hz'b)
      have hz'ne : z' ∈ ({g w}ᶜ : Set ℂ) := by
        intro hmem
        refine hw'ne (Set.mem_singleton_iff.mpr ?_)
        rw [Set.mem_singleton_iff.mp hmem]
        exact hfg w hw
      refine ((hgd_nc (f z') (hWV ⟨z', hz'b, rfl⟩) ?_).differentiableWithinAt)
      rw [hgz']
      exact (hball z' hz'b).1 hz'ne
    have hgW : DifferentiableOn ℂ g (f '' Metric.ball (g w) r) :=
      (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (hWo.mem_nhds hwW)).mp ⟨hoff, hgc w hw⟩
    exact hgW.differentiableAt (hWo.mem_nhds hwW)
  have hgDiff : DifferentiableOn ℂ g (V : Set ℂ) := fun w hw =>
    (hgd w hw).differentiableWithinAt
  have hgAn : AnalyticOnNhd ℂ g V := hgDiff.analyticOnNhd hVo
  -- Bridge: a map into an open subtype is `ω`-smooth wherever its value part is analytic.
  have bridge : ∀ (W : Opens ℂ) (F : ℂ → ↥W) (z : ℂ),
      AnalyticAt ℂ (fun p => (F p : ℂ)) z → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F z := by
    intro W F z hFa
    rw [contMDiffAt_iff]
    constructor
    · exact IsInducing.subtypeVal.continuousAt_iff.mpr hFa.continuousAt
    · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_symm,
        Function.comp_id, modelWithCornersSelf_coe, Set.range_id, id_eq]
      rw [contDiffWithinAt_univ]
      exact hFa.contDiffAt
  refine ⟨{
      toFun := fun x => ⟨f x, hfV x x.2⟩
      invFun := fun y => ⟨g y, hgU y y.2⟩
      left_inv := fun x => Subtype.ext (hgf x x.2)
      right_inv := fun y => Subtype.ext (hfg y y.2)
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }⟩
  · intro x
    have hxV : f ↑x ∈ (V : Set ℂ) := hfV ↑x x.2
    have key : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun x' : ↥U =>
          if h : f ↑x' ∈ (V : Set ℂ) then (⟨f ↑x', h⟩ : ↥V)
          else ⟨f ↑x, hxV⟩) x := by
      refine contMDiffAt_subtype_iff.mpr (bridge V
        (fun z =>
          if h : f z ∈ (V : Set ℂ) then (⟨f z, h⟩ : ↥V) else ⟨f ↑x, hxV⟩) ↑x ?_)
      refine (hAn ↑x x.2).congr ?_
      filter_upwards [hUo.mem_nhds x.2] with p hp
      rw [dite_eq_left (hfV p hp)]
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x' => ?_)
    exact (dite_eq_left (hfV ↑x' x'.2)).symm
  · intro y
    have hyU : g ↑y ∈ (U : Set ℂ) := hgU ↑y y.2
    have key : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun y' : ↥V =>
          if h : g ↑y' ∈ (U : Set ℂ) then (⟨g ↑y', h⟩ : ↥U)
          else ⟨g ↑y, hyU⟩) y := by
      refine contMDiffAt_subtype_iff.mpr (bridge U
        (fun w =>
          if h : g w ∈ (U : Set ℂ) then (⟨g w, h⟩ : ↥U) else ⟨g ↑y, hyU⟩) ↑y ?_)
      refine (hgAn ↑y y.2).congr ?_
      filter_upwards [hVo.mem_nhds y.2] with p hp
      rw [dite_eq_left (hgU p hp)]
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    exact (dite_eq_left (hgU ↑y' y'.2)).symm

/-- Every Möbius transformation acts on the Riemann sphere as a
biholomorphism. -/
theorem exists_gl_smul_diffeomorph (g : GL (Fin 2) ℂ) :
    ∃ e : ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂, ⇑e = (g • ·) := by
  classical
  -- Chart bookkeeping: the chart at a finite point is the finite chart, at `∞` the infinity
  -- chart.
  have hchart_coe : ∀ w : ℂ, chartAt ℂ ((w : ℂ̂)) = sphereChartFinite := fun _ => rfl
  have hchart_infty : chartAt ℂ (∞ : ℂ̂) = sphereChartInfty := rfl
  have hinv0 : inversionGL • ((0 : ℂ) : ℂ̂) = (∞ : ℂ̂) := by
    rw [inversionGL_smul_coe, ite_eq_left rfl]
  -- Step (A): affine elements (lower-left entry zero) act analytically.
  have haff : ∀ u : GL (Fin 2) ℂ, (u : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 →
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ̂ => u • z) := by
    intro u h10
    have hdet := u.det_ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    have ha : (u : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hd : (u : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hval_coe : ∀ x : ℂ,
        u • (x : ℂ̂) = (((u 0 0 * x + u 0 1) / u 1 1 : ℂ) : ℂ̂) := by
      intro x
      rw [OnePoint.smul_some_eq_ite, h10, zero_mul, zero_add, ite_eq_right hd]
    have hval_infty : u • (∞ : ℂ̂) = (∞ : ℂ̂) := by
      rw [OnePoint.smul_infty_eq_ite, ite_eq_left h10]
    intro z
    cases z with
    | coe x =>
      rw [contMDiffAt_iff]
      refine ⟨(continuous_gl_smul u).continuousAt, ?_⟩
      simp only [hval_coe, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, Set.range_id,
        contDiffWithinAt_univ, hchart_coe, Function.comp_apply, id_eq, sphereChartFinite_coe]
      have hnice : ContDiffAt ℂ ω (fun w : ℂ => (u 0 0 * w + u 0 1) / u 1 1) x :=
        (((contDiff_const.mul contDiff_id).add contDiff_const).div_const _).contDiffAt
      refine hnice.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only [Function.comp_apply, sphereChartFinite_symm_apply, hval_coe,
        sphereChartFinite_coe]
    | infty =>
      rw [contMDiffAt_iff]
      refine ⟨(continuous_gl_smul u).continuousAt, ?_⟩
      simp only [hval_infty, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, Set.range_id,
        contDiffWithinAt_univ, hchart_infty, Function.comp_apply, id_eq,
        sphereChartInfty_apply, inversionGL_smul_infty, sphereChartFinite_coe]
      have hne : ∀ᶠ w : ℂ in nhds 0,
          (u : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + u 0 1 * w ≠ 0 := by
        have hc : ContinuousAt
            (fun w : ℂ => (u : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + u 0 1 * w) 0 :=
          (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        exact hc.eventually_ne (by simpa using ha)
      have hnice : ContDiffAt ℂ ω
          (fun w : ℂ => u 1 1 * w / (u 0 0 + u 0 1 * w)) 0 := by
        refine ContDiffAt.div ((contDiff_const.mul contDiff_id).contDiffAt)
          ((contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffAt) ?_
        simpa using ha
      refine hnice.congr_of_eventuallyEq ?_
      filter_upwards [hne] with w hw
      rcases eq_or_ne w 0 with rfl | hw0
      · simp only [Function.comp_apply]
        rw [sphereChartInfty_symm_apply, inversionGL_smul_coe, ite_eq_left rfl, hval_infty,
          sphereChartInfty_apply, inversionGL_smul_infty, sphereChartFinite_coe]
        simp
      · have hnum : (u : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * w⁻¹ + u 0 1 ≠ 0 := by
          intro h
          apply hw
          have h' := congrArg (fun t => t * w) h
          simp only [add_mul, zero_mul] at h'
          rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one] at h'
          exact h'
        simp only [Function.comp_apply]
        rw [sphereChartInfty_symm_apply, inversionGL_smul_coe, ite_eq_right hw0, hval_coe,
          sphereChartInfty_apply, inversionGL_smul_coe, ite_eq_right (div_ne_zero hnum hd),
          sphereChartFinite_coe, inv_div, div_eq_div_iff hnum hw]
        field_simp
  -- Step (B): the inversion acts analytically (its chart readings are the identity).
  have hinvS : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ̂ => inversionGL • z) := by
    intro z
    cases z with
    | coe x =>
      by_cases hx : x = 0
      · subst hx
        rw [contMDiffAt_iff]
        refine ⟨(continuous_gl_smul inversionGL).continuousAt, ?_⟩
        simp only [hinv0, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
          modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, Set.range_id,
          contDiffWithinAt_univ, hchart_coe, hchart_infty, Function.comp_apply, id_eq,
          sphereChartFinite_coe]
        refine contDiffAt_id.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
        simp only [Function.comp_apply, sphereChartFinite_symm_apply, sphereChartInfty_apply,
          inversionGL_smul_smul, sphereChartFinite_coe, id_eq]
      · rw [contMDiffAt_iff]
        refine ⟨(continuous_gl_smul inversionGL).continuousAt, ?_⟩
        have hvx : inversionGL • ((x : ℂ̂)) = ((x⁻¹ : ℂ) : ℂ̂) := by
          rw [inversionGL_smul_coe, ite_eq_right hx]
        simp only [hvx, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
          modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, Set.range_id,
          contDiffWithinAt_univ, hchart_coe, Function.comp_apply, id_eq, sphereChartFinite_coe]
        refine (contDiffAt_inv ℂ hx).congr_of_eventuallyEq ?_
        filter_upwards [eventually_ne_nhds hx] with w hw
        simp only [Function.comp_apply, sphereChartFinite_symm_apply]
        rw [inversionGL_smul_coe, ite_eq_right hw, sphereChartFinite_coe]
    | infty =>
      rw [contMDiffAt_iff]
      refine ⟨(continuous_gl_smul inversionGL).continuousAt, ?_⟩
      simp only [inversionGL_smul_infty, extChartAt_coe, extChartAt_coe_symm,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
        Function.id_comp, Set.range_id, contDiffWithinAt_univ, hchart_coe, hchart_infty,
        Function.comp_apply, id_eq, sphereChartInfty_apply, sphereChartFinite_coe]
      refine contDiffAt_id.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only [Function.comp_apply, sphereChartInfty_symm_apply, inversionGL_smul_smul,
        sphereChartFinite_coe, id_eq]
  -- Step (C): every element factors through the two special cases.
  have hsmooth : ∀ u : GL (Fin 2) ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ̂ => u • z) := by
    intro u
    by_cases hc : (u : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
    · exact haff u hc
    · obtain ⟨a, b, c, d, hu⟩ : ∃ a b c d : ℂ,
          (u : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; c, d] :=
        ⟨_, _, _, _, Matrix.eta_fin_two _⟩
      rw [hu] at hc
      have hc' : c ≠ 0 := by simpa using hc
      have hdet := u.det_ne_zero
      rw [hu, Matrix.det_fin_two_of] at hdet
      have hbcad : b * c - a * d ≠ 0 := by
        intro h0
        apply hdet
        linear_combination -h0
      have h1det :
          (!![(b * c - a * d) / c, a / c; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
        rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
        exact div_ne_zero hbcad hc'
      have h2det : (!![c, d; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
        rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
        exact hc'
      obtain ⟨A1, hA1⟩ : ∃ A1 : GL (Fin 2) ℂ,
          (A1 : Matrix (Fin 2) (Fin 2) ℂ) = !![(b * c - a * d) / c, a / c; 0, 1] :=
        ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h1det, rfl⟩
      obtain ⟨A2, hA2⟩ : ∃ A2 : GL (Fin 2) ℂ,
          (A2 : Matrix (Fin 2) (Fin 2) ℂ) = !![c, d; 0, 1] :=
        ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h2det, rfl⟩
      have hmatJ : (inversionGL : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] := rfl
      have hfact : u = A1 * inversionGL * A2 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hA1, hA2, hmatJ, hu,
          Matrix.mul_fin_two, Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> field_simp
        ring
      have h1lower : (A1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [hA1]; simp
      have h2lower : (A2 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [hA2]; simp
      have heq : (fun z : ℂ̂ => u • z)
          = (fun z : ℂ̂ => A1 • z) ∘ (fun z : ℂ̂ => inversionGL • z) ∘
            (fun z : ℂ̂ => A2 • z) := by
        funext z
        simp only [Function.comp_apply]
        rw [hfact, SemigroupAction.mul_smul, SemigroupAction.mul_smul]
      rw [heq]
      exact (haff A1 h1lower).comp (hinvS.comp (haff A2 h2lower))
  -- Assemble the diffeomorphism.
  exact ⟨⟨⟨fun z => g • z, fun z => g⁻¹ • z, fun z => inv_smul_smul g z,
    fun z => smul_inv_smul g z⟩, hsmooth g, hsmooth g⁻¹⟩, rfl⟩

/-! ## Transporting biholomorphisms -/

/-- A biholomorphism restricts to a biholomorphism from any open set onto its
image. -/
theorem exists_diffeomorph_opens_image {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]
    (e : M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ N) (U : Opens M) :
    ∃ V : Opens N, (V : Set N) = ⇑e '' U ∧
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥V) := by
  let V : Opens N := ⟨⇑e '' U, e.toHomeomorph.isOpenMap _ U.isOpen⟩
  have hmem : ∀ y : V, e.symm (y : N) ∈ U := by
    rintro ⟨-, x, hx, rfl⟩
    simpa using hx
  let F : U → V := fun x => ⟨e x, Set.mem_image_of_mem ⇑e x.2⟩
  let G : V → U := fun y => ⟨e.symm y, hmem y⟩
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F := by
    intro x
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ F) x :=
      (e.contMDiff.comp contMDiff_subtype_val).contMDiffAt
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  have hG : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω G := by
    intro y
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ G) y :=
      (e.symm.contMDiff.comp contMDiff_subtype_val).contMDiffAt
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  exact ⟨V, rfl, ⟨{
    toFun := F
    invFun := G
    left_inv := fun x => Subtype.ext (e.symm_apply_apply (x : M))
    right_inv := fun y => Subtype.ext (e.apply_symm_apply (y : N))
    contMDiff_toFun := hF
    contMDiff_invFun := hG }⟩⟩

/-- A domain in the Riemann sphere avoiding `∞` is biholomorphic, through the
finite chart, to a plane domain whose points are the finite points of the
domain. -/
theorem exists_diffeomorph_opens_planar (U : Opens ℂ̂)
    (hU : (∞ : ℂ̂) ∉ (U : Set ℂ̂)) :
    ∃ V : Opens ℂ, ((↑) : ℂ → ℂ̂) '' V = U ∧
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥V) := by
  -- Every point of `U` is finite.
  have hfin : ∀ z ∈ (U : Set ℂ̂), ∃ w : ℂ, (w : ℂ̂) = z := fun z hz =>
    OnePoint.ne_infty_iff_exists.mp fun h => hU (h ▸ hz)
  have hsrc : ∀ z : ↥U, (z : ℂ̂) ∈ sphereChartFinite.source := by
    intro z
    rw [sphereChartFinite_source]
    exact fun h => hU (h ▸ z.2)
  let V : Opens ℂ :=
    ⟨((↑) : ℂ → ℂ̂) ⁻¹' U, U.isOpen.preimage OnePoint.continuous_coe⟩
  refine ⟨V, ?_, ?_⟩
  · -- The image of `V` under the coercion recovers `U`.
    change ((↑) : ℂ → ℂ̂) '' (((↑) : ℂ → ℂ̂) ⁻¹' ↑U) = ↑U
    rw [Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_left.mpr fun z hz => hfin z hz
  · -- The finite chart maps points of `U` into `V`.
    have hmemV : ∀ z : ↥U,
        ((sphereChartFinite (z : ℂ̂) : ℂ) : ℂ̂) ∈ (U : Set ℂ̂) := by
      intro z
      obtain ⟨w, hw⟩ := hfin z.1 z.2
      rw [← hw, sphereChartFinite_coe, hw]
      exact z.2
    -- The finite chart belongs to the maximal analytic atlas of the sphere.
    have hmax : sphereChartFinite ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
      IsManifold.chart_mem_maximalAtlas (((0 : ℂ) : ℂ̂))
    -- Smoothness of the chart reading `U → V`.
    have hto : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
        (fun z : ↥U => (⟨sphereChartFinite (z : ℂ̂), hmemV z⟩ : ↥V)) := by
      intro x
      rw [contMDiffAt_iff_target]
      constructor
      · exact (Continuous.subtype_mk
          (sphereChartFinite.continuousOn.comp_continuous continuous_subtype_val hsrc)
          hmemV).continuousAt
      · exact (contMDiffAt_of_mem_maximalAtlas hmax (hsrc x)).comp x
          contMDiff_subtype_val.contMDiffAt
    -- Smoothness of the inclusion `V → U`.
    have hinv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
        (fun v : ↥V => (⟨((v : ℂ) : ℂ̂), v.2⟩ : ↥U)) := by
      intro v
      rw [contMDiffAt_iff_target]
      constructor
      · exact (Continuous.subtype_mk
          (OnePoint.continuous_coe.comp continuous_subtype_val) fun u => u.2).continuousAt
      · exact contMDiff_subtype_val.contMDiffAt.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun u => sphereChartFinite_coe (u : ℂ))
    refine ⟨{ toFun := fun z => ⟨sphereChartFinite (z : ℂ̂), hmemV z⟩
              invFun := fun v => ⟨((v : ℂ) : ℂ̂), v.2⟩
              left_inv := ?_
              right_inv := ?_
              contMDiff_toFun := hto
              contMDiff_invFun := hinv }⟩
    · intro z
      apply Subtype.ext
      obtain ⟨w, hw⟩ := hfin z.1 z.2
      change ((sphereChartFinite (z : ℂ̂) : ℂ) : ℂ̂) = (z : ℂ̂)
      rw [← hw, sphereChartFinite_coe]
    · intro v
      exact Subtype.ext (sphereChartFinite_coe (v : ℂ))

end RiemannDynamics
