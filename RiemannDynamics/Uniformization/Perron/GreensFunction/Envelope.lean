/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreensFunction.Basic

/-!
# Harmonicity, positivity, and the pole extension of the Green envelope

On a noncompact connected surface the Green envelope is harmonic off the pole
and positive, and `G + log|z|` extends harmonically across the pole.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-! ## The dichotomy and the Green's function -/

/-- In the hyperbolic case the envelope is harmonic on the punctured surface
and the family is bounded above at every point of it. -/
theorem mharmonicOn_greenEnvelope [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) :
    MHarmonicOn (greenEnvelope p₀) {p₀}ᶜ ∧
      ∀ x ≠ p₀, BddAbove ((fun v => v x) '' greenFamily p₀) := by
  classical
  -- Transfer of subharmonicity along a pointwise equality on a subdomain.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  -- ### The zero function belongs to the Green's family.
  have hbase : (fun _ : M => (0 : ℝ)) ∈ greenFamily p₀ := by
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord p₀) p₀ := by
      have h1 : ContinuousAt (chartAt ℂ p₀) p₀ :=
        (chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)
      exact h1.sub continuousAt_const
    have h0 : ‖poleCoord p₀ p₀‖ < 1 := by
      simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have hx1 : ‖poleCoord p₀ x‖ < 1 := hx
    have h6 : Real.log ‖poleCoord p₀ x‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hx1.le
    simpa using h6
  have hne_im : ∀ x : M, ((fun v => v x) '' greenFamily p₀).Nonempty :=
    fun x => ⟨0, ⟨fun _ => 0, hbase, rfl⟩⟩
  -- ### Closure of the family under pointwise maximum.
  have hmax_mem : ∀ v w : M → ℝ, v ∈ greenFamily p₀ → w ∈ greenFamily p₀ →
      (fun y => max (v y) (w y)) ∈ greenFamily p₀ := by
    intro v w hv hw
    obtain ⟨hv1, hv2, ⟨Kv, hKv, hKvne, hKv0⟩, ⟨Cv, hCv⟩⟩ := hv
    obtain ⟨hw1, hw2, ⟨Kw, hKw, hKwne, hKw0⟩, ⟨Cw, hCw⟩⟩ := hw
    refine ⟨fun x hx => (hv1 x hx).max (hw1 x hx),
      fun x hx => (hv2 x hx).max (hw2 x hx),
      ⟨Kv ∪ Kw, hKv.union hKw, ?_, ?_⟩, ⟨max Cv Cw, ?_⟩⟩
    · intro hcon
      exact noncompact_univ M (hcon ▸ (hKv.union hKw))
    · intro x hxK
      change max (v x) (w x) = 0
      rw [hKv0 x (fun h => hxK (Set.mem_union_left Kw h)),
        hKw0 x (fun h => hxK (Set.mem_union_right Kv h)), max_self]
    · filter_upwards [hCv, hCw] with x h1 h2
      have h3 : max (v x) (w x) + Real.log ‖poleCoord p₀ x‖ =
          max (v x + Real.log ‖poleCoord p₀ x‖) (w x + Real.log ‖poleCoord p₀ x‖) :=
        (max_add_add_right _ _ _).symm
      rw [h3]
      exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))
  /- ### The key local block at a point `p ≠ p₀`: a Harnack-pair neighbourhood
  (for the clopen boundedness argument) and, given global boundedness, the
  harmonicity of the envelope at `p` via the Perron/Harnack monotone limit. -/
  have key : ∀ p : M, p ≠ p₀ →
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ ({p₀}ᶜ : Set M) ∧
      (∃ wb : M → ℝ, wb ∈ greenFamily p₀ ∧ ∀ v ∈ greenFamily p₀,
        ∃ q ∈ greenFamily p₀, (∀ x, x ≠ p₀ → v x ≤ q x) ∧
          ∀ y ∈ U, q y - wb y ≤ 3 * (q p - wb p) ∧ q p - wb p ≤ 3 * (q y - wb y)) ∧
      ((∀ x, x ≠ p₀ → BddAbove ((fun v => v x) '' greenFamily p₀)) →
        MHarmonicAt (greenEnvelope p₀) p) := by
    intro p hp
    -- ## Chart set-up at `p`.
    set E : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hE
    have hpsrc : p ∈ E.source := by rw [hE]; exact mem_chart_source ℂ p
    have hEatlas : E ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
      rw [hE]; exact IsManifold.chart_mem_maximalAtlas p
    set cΔ : ℂ := E p with hcΔ
    have hct : cΔ ∈ E.target := by rw [hcΔ]; exact E.map_source hpsrc
    set T' : Set ℂ := E.target ∩ ⇑E.symm ⁻¹' {p₀}ᶜ with hT'
    have hT'open : IsOpen T' := E.isOpen_inter_preimage_symm isOpen_compl_singleton
    have hsymmc : E.symm cΔ = p := by rw [hcΔ]; exact E.left_inv hpsrc
    have hcT' : cΔ ∈ T' := by
      refine ⟨hct, ?_⟩
      rw [Set.mem_preimage, hsymmc]
      exact Set.mem_compl_singleton_iff.mpr hp
    obtain ⟨R, hR0, hRsub⟩ := (nhds_basis_closedBall.mem_iff).1 (hT'open.mem_nhds hcT')
    have hT'tgt : T' ⊆ E.target := Set.inter_subset_left
    have hsymm_ne : ∀ w ∈ T', E.symm w ≠ p₀ :=
      fun w hw => Set.mem_compl_singleton_iff.mp hw.2
    have hsymm_src : ∀ w ∈ T', E.symm w ∈ E.source := fun w hw => E.map_target hw.1
    have hEE : ∀ w ∈ E.target, E (E.symm w) = w := fun w hw => E.right_inv hw
    have hsrc_ne : ∀ x, x ∈ E.source → x ≠ p₀ → E x ∈ T' := by
      intro x hxs hxne
      refine ⟨E.map_source hxs, ?_⟩
      rw [Set.mem_preimage, E.left_inv hxs]
      exact Set.mem_compl_singleton_iff.mpr hxne
    have hballT : ball cΔ R ⊆ T' := ball_subset_closedBall.trans hRsub
    -- ## The chart reading of a family member is subharmonic on `T'`.
    have hread : ∀ v, v ∈ greenFamily p₀ → SubharmonicOn (v ∘ ⇑E.symm) T' := by
      intro v hv
      obtain ⟨hvsub, hvcont, -, -⟩ := hv
      apply subharmonicOn_of_locally hT'open
      · intro w hw
        have h1 : ContinuousAt (⇑E.symm) w := E.continuousAt_symm (hT'tgt hw)
        have h2 : ContinuousAt v (E.symm w) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr (hsymm_ne w hw)))
        exact (h2.comp h1).continuousWithinAt
      · intro w hw
        have hxs : E.symm w ∈ E.source := hsymm_src w hw
        have hMS : MSubharmonicAt v (E.symm w) :=
          hvsub _ (Set.mem_compl_singleton_iff.mpr (hsymm_ne w hw))
        obtain ⟨ρ, hρ, -, hsub⟩ :=
          (msubharmonicAt_iff_of_mem_maximalAtlas hEatlas hxs).mp hMS
        rw [hEE w (hT'tgt hw)] at hsub
        refine ⟨ρ, hρ, ?_⟩
        intro ρ' hρ'0 hρ'lt _
        exact hsub.2 w (mem_ball_self hρ) ρ' hρ'0 (Metric.closedBall_subset_ball hρ'lt)
    -- ## Plane-side Poisson-modification bricks.
    have hPMsub : ∀ v, v ∈ greenFamily p₀ →
        SubharmonicOn (poissonModify (v ∘ ⇑E.symm) cΔ R) T' :=
      fun v hv => SubharmonicOn.poissonModify (hread v hv) hR0 hRsub
    have hPMharm : ∀ v, v ∈ greenFamily p₀ →
        HarmonicOnNhd (poissonModify (v ∘ ⇑E.symm) cΔ R) (ball cΔ R) :=
      fun v hv => poissonModify_harmonicOn (hread v hv) hR0 hRsub
    have hPMge : ∀ v, v ∈ greenFamily p₀ → ∀ w ∈ T',
        (v ∘ ⇑E.symm) w ≤ poissonModify (v ∘ ⇑E.symm) cΔ R w :=
      fun v hv => poissonModify_ge (hread v hv) hR0 hRsub
    have hPMoff : ∀ (f : ℂ → ℝ) (w : ℂ), w ∉ ball cΔ R →
        poissonModify f cΔ R w = f w := by
      intro f w hw
      simp only [poissonModify, ite_eq_right hw]
    -- ## Monotonicity of the modification in the modified function.
    have hplane_mono : ∀ f g : M → ℝ, f ∈ greenFamily p₀ → g ∈ greenFamily p₀ →
        (∀ x, x ≠ p₀ → f x ≤ g x) → ∀ z ∈ ball cΔ R,
          poissonModify (f ∘ ⇑E.symm) cΔ R z ≤ poissonModify (g ∘ ⇑E.symm) cΔ R z := by
      intro f g hf hg hfg
      set d : ℂ → ℝ := fun z =>
        poissonModify (f ∘ ⇑E.symm) cΔ R z - poissonModify (g ∘ ⇑E.symm) cΔ R z with hddef
      have hdharm : HarmonicOnNhd d (ball cΔ R) := by
        intro z hz
        exact (hPMharm f hf z hz).sub (hPMharm g hg z hz)
      have hdsub : SubharmonicOn d (ball cΔ R) := HarmonicOnNhd.subharmonicOn hdharm
      have hdcont : ContinuousOn d (closure (ball cΔ R)) := by
        rw [closure_ball cΔ hR0.ne']
        exact ((hPMsub f hf).1.mono hRsub).sub ((hPMsub g hg).1.mono hRsub)
      have hfr : ∀ z ∈ frontier (ball cΔ R), d z ≤ 0 := by
        intro z hz
        rw [frontier_ball cΔ hR0.ne'] at hz
        have hzd : dist z cΔ = R := mem_sphere.1 hz
        have hznb : z ∉ ball cΔ R := by
          rw [mem_ball, hzd]
          exact lt_irrefl R
        have hzT : z ∈ T' := hRsub (sphere_subset_closedBall hz)
        have h1 := hfg (E.symm z) (hsymm_ne z hzT)
        have e1 : poissonModify (f ∘ ⇑E.symm) cΔ R z = f (E.symm z) := hPMoff _ z hznb
        have e2 : poissonModify (g ∘ ⇑E.symm) cΔ R z = g (E.symm z) := hPMoff _ z hznb
        simp only [hddef]
        rw [e1, e2]
        linarith
      intro z hz
      have h2 := hdsub.le_of_frontier_le isOpen_ball isBounded_ball hdcont hfr z hz
      simp only [hddef] at h2
      linarith
    -- ## The surface-level Poisson modification.
    set Pm : (M → ℝ) → M → ℝ := fun v x =>
      if x ∈ E.source then poissonModify (v ∘ ⇑E.symm) cΔ R (E x) else v x with hPmdef
    have hPmsrc : ∀ (v : M → ℝ) (x : M), x ∈ E.source →
        Pm v x = poissonModify (v ∘ ⇑E.symm) cΔ R (E x) := by
      intro v x hxs
      simp only [hPmdef, ite_eq_left hxs]
    have hPmread : ∀ (v : M → ℝ) (w : ℂ), w ∈ E.target →
        Pm v (E.symm w) = poissonModify (v ∘ ⇑E.symm) cΔ R w := by
      intro v w hw
      rw [hPmsrc v _ (E.map_target hw), hEE w hw]
    set D : Set M := ⇑E.symm '' closedBall cΔ R with hDdef
    have hDcomp : IsCompact D := (isCompact_closedBall cΔ R).image_of_continuousOn
      (E.continuousOn_symm.mono (hRsub.trans hT'tgt))
    have hDcl : IsClosed D := hDcomp.isClosed
    have hDsrc : D ⊆ E.source := by
      rintro x ⟨w, hw, rfl⟩
      exact E.map_target (hT'tgt (hRsub hw))
    have hp₀D : p₀ ∉ D := by
      rintro ⟨w, hw, hwp⟩
      exact hsymm_ne w (hRsub hw) hwp
    have hPmoff : ∀ (v : M → ℝ) (x : M), x ∉ D → Pm v x = v x := by
      intro v x hx
      by_cases hxs : x ∈ E.source
      · have hxb : E x ∉ ball cΔ R := by
          intro hb
          exact hx ⟨E x, ball_subset_closedBall hb, E.left_inv hxs⟩
        rw [hPmsrc v x hxs, hPMoff _ _ hxb]
        simp only [Function.comp_apply, E.left_inv hxs]
      · simp only [hPmdef, ite_eq_right hxs]
    have hPmge : ∀ v, v ∈ greenFamily p₀ → ∀ x, x ≠ p₀ → v x ≤ Pm v x := by
      intro v hv x hx
      by_cases hxs : x ∈ E.source
      · rw [hPmsrc v x hxs]
        have h1 := hPMge v hv (E x) (hsrc_ne x hxs hx)
        simpa [E.left_inv hxs] using h1
      · rw [(by simp only [hPmdef, ite_eq_right hxs] : Pm v x = v x)]
    -- ## Membership of the modification in the family.
    have hPmmem : ∀ v, v ∈ greenFamily p₀ → Pm v ∈ greenFamily p₀ := by
      intro v hv
      have hPMs := hPMsub v hv
      obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKval⟩, ⟨C, hC⟩⟩ := hv
      refine ⟨?_, ?_, ⟨K ∪ D, hKcomp.union hDcomp, ?_, ?_⟩, ⟨C, ?_⟩⟩
      · -- subharmonicity on the punctured surface
        intro x hx
        have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
        by_cases hxs : x ∈ E.source
        · refine (msubharmonicAt_iff_of_mem_maximalAtlas hEatlas hxs).mpr ?_
          obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hT'open _ (hsrc_ne x hxs hxp)
          have heqon : Set.EqOn (poissonModify (v ∘ ⇑E.symm) cΔ R) (Pm v ∘ ⇑E.symm)
              (ball (E x) ρ) := by
            intro z hz
            exact (hPmread v z (hT'tgt (hρsub hz))).symm
          exact ⟨ρ, hρ, fun z hz => hT'tgt (hρsub hz),
            transfer _ _ _ _ hPMs (fun z hz => hρsub hz) heqon⟩
        · have hxD : x ∉ D := fun h => hxs (hDsrc h)
          obtain ⟨r₁, hr₁, hball₁, hsub₁⟩ := hvsub x hx
          have hopen2 : IsOpen (ball (chartAt ℂ x x) r₁ ∩
              ((chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹' Dᶜ)) :=
            isOpen_ball.inter
              ((chartAt ℂ x).isOpen_inter_preimage_symm hDcl.isOpen_compl)
          have hmem2 : chartAt ℂ x x ∈ ball (chartAt ℂ x x) r₁ ∩
              ((chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹' Dᶜ) := by
            refine ⟨mem_ball_self hr₁,
              (chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
            rw [Set.mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
            exact hxD
          obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
          have heqon : Set.EqOn (v ∘ ⇑(chartAt ℂ x).symm) (Pm v ∘ ⇑(chartAt ℂ x).symm)
              (ball (chartAt ℂ x x) ρ) := by
            intro z hz
            exact (hPmoff v _ ((hρsub hz).2.2)).symm
          exact ⟨ρ, hρ, fun z hz => (hρsub hz).2.1,
            transfer _ _ _ _ hsub₁ (fun z hz => (hρsub hz).1) heqon⟩
      · -- continuity on the punctured surface
        intro x hx
        have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
        apply ContinuousAt.continuousWithinAt
        by_cases hxs : x ∈ E.source
        · have h1 : ContinuousAt (poissonModify (v ∘ ⇑E.symm) cΔ R) (E x) :=
            hPMs.1.continuousAt (hT'open.mem_nhds (hsrc_ne x hxs hxp))
          refine (h1.comp (E.continuousAt hxs)).congr_of_eventuallyEq ?_
          filter_upwards [E.open_source.mem_nhds hxs] with y hy
          exact hPmsrc v y hy
        · have hxD : x ∉ D := fun h => hxs (hDsrc h)
          have h1 : ContinuousAt v x :=
            hvcont.continuousAt (isOpen_compl_singleton.mem_nhds hx)
          refine h1.congr_of_eventuallyEq ?_
          filter_upwards [hDcl.isOpen_compl.mem_nhds hxD] with y hy
          exact hPmoff v y hy
      · -- the support is not everything
        intro hcon
        exact noncompact_univ M (hcon ▸ (hKcomp.union hDcomp))
      · -- vanishing off the enlarged support
        intro x hxKD
        rw [hPmoff v x (fun h => hxKD (Set.mem_union_right K h))]
        exact hKval x (fun h => hxKD (Set.mem_union_left D h))
      · -- logarithmic pole growth is untouched
        filter_upwards [hC,
          nhdsWithin_le_nhds (hDcl.isOpen_compl.mem_nhds hp₀D)] with x h1 h2
        rw [hPmoff v x h2]
        exact h1
    -- ## The Harnack-pair neighbourhood.
    have hhalf : 0 < R / 2 := by linarith
    set U : Set M := E.source ∩ ⇑E ⁻¹' ball cΔ (R / 2) with hUdef
    have hUopen : IsOpen U :=
      E.continuousOn.isOpen_inter_preimage E.open_source isOpen_ball
    have hpU : p ∈ U := by
      refine ⟨hpsrc, ?_⟩
      rw [Set.mem_preimage, ← hcΔ]
      exact mem_ball_self hhalf
    have hhalfsub : ball cΔ (R / 2) ⊆ ball cΔ R := ball_subset_ball (by linarith)
    have hUsub : U ⊆ ({p₀}ᶜ : Set M) := by
      rintro y ⟨hys, hyb⟩
      rw [Set.mem_preimage] at hyb
      have h1 : E y ∈ T' := hballT (hhalfsub hyb)
      have h2 := hsymm_ne _ h1
      rw [E.left_inv hys] at h2
      exact Set.mem_compl_singleton_iff.mpr h2
    refine ⟨U, hUopen, hpU, hUsub, ⟨Pm (fun _ => 0), hPmmem _ hbase, ?_⟩, ?_⟩
    · -- the two-sided Harnack bounds for the modified competitor
      intro v hv
      have hmaxF : (fun y => max (v y) ((fun _ : M => (0 : ℝ)) y)) ∈ greenFamily p₀ :=
        hmax_mem v (fun _ => 0) hv hbase
      refine ⟨Pm (fun y => max (v y) ((fun _ : M => (0 : ℝ)) y)), hPmmem _ hmaxF, ?_, ?_⟩
      · intro x hx
        exact (le_max_left (v x) _).trans (hPmge _ hmaxF x hx)
      · set h : ℂ → ℝ := fun z =>
          poissonModify ((fun y => max (v y) ((fun _ : M => (0 : ℝ)) y)) ∘ ⇑E.symm) cΔ R z -
            poissonModify ((fun _ : M => (0 : ℝ)) ∘ ⇑E.symm) cΔ R z with hhdef
        have h2R : 2 * (R / 2) = R := by ring
        have hharm : HarmonicOnNhd h (ball cΔ (2 * (R / 2))) := by
          rw [h2R]
          intro z hz
          exact (hPMharm _ hmaxF z hz).sub (hPMharm _ hbase z hz)
        have hpos : ∀ z ∈ ball cΔ (2 * (R / 2)), 0 ≤ h z := by
          rw [h2R]
          intro z hz
          have h1 := hplane_mono (fun _ => 0) (fun y => max (v y) ((fun _ : M => (0 : ℝ)) y))
            hbase hmaxF (fun x _ => le_max_right _ _) z hz
          simp only [hhdef]
          linarith
        have hHar := harnack_inequality_ball hhalf hharm hpos
        intro y hy
        obtain ⟨hlo, hup⟩ := hHar (E y) hy.2
        have hval_y : h (E y) =
            Pm (fun y' => max (v y') ((fun _ : M => (0 : ℝ)) y')) y -
              Pm (fun _ : M => (0 : ℝ)) y := by
          simp only [hhdef]
          rw [hPmsrc (fun y' => max (v y') ((fun _ : M => (0 : ℝ)) y')) y hy.1,
            hPmsrc (fun _ : M => (0 : ℝ)) y hy.1]
        have hval_c : h cΔ =
            Pm (fun y' => max (v y') ((fun _ : M => (0 : ℝ)) y')) p -
              Pm (fun _ : M => (0 : ℝ)) p := by
          simp only [hhdef]
          rw [hPmsrc (fun y' => max (v y') ((fun _ : M => (0 : ℝ)) y')) p hpsrc,
            hPmsrc (fun _ : M => (0 : ℝ)) p hpsrc, ← hcΔ]
        rw [hval_y, hval_c] at hlo hup
        exact ⟨by linarith, by linarith⟩
    · -- ## Harmonicity of the envelope at `p`, given boundedness everywhere.
      intro hAllBdd
      obtain ⟨a, hamono, hatend, hamem⟩ :=
        exists_seq_tendsto_sSup (hne_im p) (hAllBdd p hp)
      have hamem' : ∀ n, ∃ v, v ∈ greenFamily p₀ ∧ v p = a n := by
        intro n
        obtain ⟨v, hvF, hvv⟩ := hamem n
        exact ⟨v, hvF, hvv⟩
      choose v' hv'F hv'p using hamem'
      -- the running maxima of the approximating sequence
      set V : ℕ → M → ℝ := fun n => Nat.rec (motive := fun _ => M → ℝ) (v' 0)
        (fun k Vk x => max (Vk x) (v' (k + 1) x)) n with hVdef
      have hVF : ∀ n, V n ∈ greenFamily p₀ := by
        intro n
        induction n with
        | zero => exact hv'F 0
        | succ k ih => exact hmax_mem _ _ ih (hv'F (k + 1))
      have hVmono : ∀ x : M, Monotone fun n => V n x :=
        fun x => monotone_nat_of_le_succ fun n => le_max_left _ _
      have hv'leV : ∀ n, v' n p ≤ V n p := by
        intro n
        cases n with
        | zero => exact le_rfl
        | succ k => exact le_max_right _ _
      -- plane readings of the modified running maxima
      set W : ℕ → ℂ → ℝ := fun n => poissonModify (V n ∘ ⇑E.symm) cΔ R with hWdef
      have hWharm : ∀ n, HarmonicOnNhd (W n) (ball cΔ R) := fun n => hPMharm _ (hVF n)
      have hWmono : ∀ z ∈ ball cΔ R, Monotone fun n => W n z := by
        intro z hz
        refine monotone_nat_of_le_succ fun n => ?_
        exact hplane_mono (V n) (V (n + 1)) (hVF n) (hVF (n + 1))
          (fun x _ => hVmono x (Nat.le_succ n)) z hz
      have hWmem : ∀ (n : ℕ) (z : ℂ), z ∈ ball cΔ R → W n z = Pm (V n) (E.symm z) :=
        fun n z hz => (hPmread (V n) z (hT'tgt (hballT hz))).symm
      have hWle : ∀ z ∈ ball cΔ R, ∀ n, W n z ≤ greenEnvelope p₀ (E.symm z) := by
        intro z hz n
        rw [hWmem n z hz]
        exact le_csSup (hAllBdd _ (hsymm_ne z (hballT hz)))
          ⟨Pm (V n), hPmmem _ (hVF n), rfl⟩
      have hWbdd : ∀ z ∈ ball cΔ R, BddAbove (Set.range fun n => W n z) := by
        intro z hz
        refine ⟨greenEnvelope p₀ (E.symm z), ?_⟩
        rintro b ⟨n, rfl⟩
        exact hWle z hz n
      set flim : ℂ → ℝ := fun z => ⨆ n, W n z with hflimdef
      have hWtends : ∀ z ∈ ball cΔ R, Tendsto (fun n => W n z) atTop (𝓝 (flim z)) :=
        fun z hz => tendsto_atTop_ciSup (hWmono z hz) (hWbdd z hz)
      have hWlelim : ∀ z ∈ ball cΔ R, ∀ n, W n z ≤ flim z :=
        fun z hz n => le_ciSup (hWbdd z hz) n
      have hflimharm : HarmonicOnNhd flim (ball cΔ R) :=
        harmonicOnNhd_of_monotone_tendsto hWharm hWmono hWlelim hWtends
      have hcball : cΔ ∈ ball cΔ R := mem_ball_self hR0
      -- the limit attains the envelope value at the centre
      have henvp : greenEnvelope p₀ p = sSup ((fun v => v p) '' greenFamily p₀) := rfl
      have hWatc : ∀ n, W n cΔ = Pm (V n) p := by
        intro n
        rw [hWmem n cΔ hcball, hsymmc]
      have hcup : ∀ n, W n cΔ ≤ greenEnvelope p₀ p := by
        intro n
        rw [hWatc n]
        exact le_csSup (hAllBdd p hp) ⟨Pm (V n), hPmmem _ (hVF n), rfl⟩
      have hclow : ∀ n, a n ≤ W n cΔ := by
        intro n
        rw [hWatc n, ← hv'p n]
        exact (hv'leV n).trans (hPmge _ (hVF n) p hp)
      have htendc : Tendsto (fun n => W n cΔ) atTop (𝓝 (greenEnvelope p₀ p)) := by
        rw [henvp]
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le hatend
          tendsto_const_nhds hclow (fun n => hcup n)
      have hflimc : flim cΔ = greenEnvelope p₀ p :=
        tendsto_nhds_unique (hWtends cΔ hcball) htendc
      -- the limit attains the envelope value everywhere on the disc
      have hflimge : ∀ zq ∈ ball cΔ R, greenEnvelope p₀ (E.symm zq) ≤ flim zq := by
        intro zq hzq
        have hqne : E.symm zq ≠ p₀ := hsymm_ne zq (hballT hzq)
        obtain ⟨b, hbmono, hbtend, hbmem⟩ :=
          exists_seq_tendsto_sSup (hne_im (E.symm zq)) (hAllBdd _ hqne)
        have hbmem' : ∀ n, ∃ v, v ∈ greenFamily p₀ ∧ v (E.symm zq) = b n := by
          intro n
          obtain ⟨v, hvF, hvv⟩ := hbmem n
          exact ⟨v, hvF, hvv⟩
        choose g' hg'F hg'q using hbmem'
        -- combined running maxima of the two approximating sequences
        set G : ℕ → M → ℝ := fun n => Nat.rec (motive := fun _ => M → ℝ)
          (fun x => max (V 0 x) (g' 0 x))
          (fun k Gk x => max (Gk x) (max (V (k + 1) x) (g' (k + 1) x))) n with hGdef
        have hGF : ∀ n, G n ∈ greenFamily p₀ := by
          intro n
          induction n with
          | zero => exact hmax_mem _ _ (hVF 0) (hg'F 0)
          | succ k ih => exact hmax_mem _ _ ih (hmax_mem _ _ (hVF (k + 1)) (hg'F (k + 1)))
        have hVleG : ∀ (n : ℕ) (x : M), V n x ≤ G n x := by
          intro n x
          cases n with
          | zero => exact le_max_left _ _
          | succ k => exact le_max_of_le_right (le_max_left _ _)
        have hg'leG : ∀ (n : ℕ) (x : M), g' n x ≤ G n x := by
          intro n x
          cases n with
          | zero => exact le_max_right _ _
          | succ k => exact le_max_of_le_right (le_max_right _ _)
        have hGmono : ∀ x : M, Monotone fun n => G n x :=
          fun x => monotone_nat_of_le_succ fun n => le_max_left _ _
        set H : ℕ → ℂ → ℝ := fun n => poissonModify (G n ∘ ⇑E.symm) cΔ R with hHdef
        have hHharm : ∀ n, HarmonicOnNhd (H n) (ball cΔ R) := fun n => hPMharm _ (hGF n)
        have hHmono : ∀ z ∈ ball cΔ R, Monotone fun n => H n z := by
          intro z hz
          refine monotone_nat_of_le_succ fun n => ?_
          exact hplane_mono (G n) (G (n + 1)) (hGF n) (hGF (n + 1))
            (fun x _ => hGmono x (Nat.le_succ n)) z hz
        have hHmem : ∀ (n : ℕ) (z : ℂ), z ∈ ball cΔ R → H n z = Pm (G n) (E.symm z) :=
          fun n z hz => (hPmread (G n) z (hT'tgt (hballT hz))).symm
        have hHle : ∀ z ∈ ball cΔ R, ∀ n, H n z ≤ greenEnvelope p₀ (E.symm z) := by
          intro z hz n
          rw [hHmem n z hz]
          exact le_csSup (hAllBdd _ (hsymm_ne z (hballT hz)))
            ⟨Pm (G n), hPmmem _ (hGF n), rfl⟩
        have hHbdd : ∀ z ∈ ball cΔ R, BddAbove (Set.range fun n => H n z) := by
          intro z hz
          refine ⟨greenEnvelope p₀ (E.symm z), ?_⟩
          rintro c ⟨n, rfl⟩
          exact hHle z hz n
        set glim : ℂ → ℝ := fun z => ⨆ n, H n z with hglimdef
        have hHtends : ∀ z ∈ ball cΔ R, Tendsto (fun n => H n z) atTop (𝓝 (glim z)) :=
          fun z hz => tendsto_atTop_ciSup (hHmono z hz) (hHbdd z hz)
        have hHlelim : ∀ z ∈ ball cΔ R, ∀ n, H n z ≤ glim z :=
          fun z hz n => le_ciSup (hHbdd z hz) n
        have hglimharm : HarmonicOnNhd glim (ball cΔ R) :=
          harmonicOnNhd_of_monotone_tendsto hHharm hHmono hHlelim hHtends
        -- `W n ≤ H n` on the disc, hence `flim ≤ glim`
        have hWH : ∀ z ∈ ball cΔ R, ∀ n, W n z ≤ H n z := by
          intro z hz n
          exact hplane_mono (V n) (G n) (hVF n) (hGF n) (fun x _ => hVleG n x) z hz
        have hfg : ∀ z ∈ ball cΔ R, flim z ≤ glim z := by
          intro z hz
          simp only [hflimdef, hglimdef]
          exact ciSup_mono (hHbdd z hz) (fun n => hWH z hz n)
        -- `glim` also attains the envelope value at the centre
        have hHatc : ∀ n, H n cΔ = Pm (G n) p := by
          intro n
          rw [hHmem n cΔ hcball, hsymmc]
        have hHcup : ∀ n, H n cΔ ≤ greenEnvelope p₀ p := by
          intro n
          rw [hHatc n]
          exact le_csSup (hAllBdd p hp) ⟨Pm (G n), hPmmem _ (hGF n), rfl⟩
        have hHclow : ∀ n, a n ≤ H n cΔ := by
          intro n
          rw [hHatc n, ← hv'p n]
          exact ((hv'leV n).trans (hVleG n p)).trans (hPmge _ (hGF n) p hp)
        have htendcH : Tendsto (fun n => H n cΔ) atTop (𝓝 (greenEnvelope p₀ p)) := by
          rw [henvp]
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le hatend
            tendsto_const_nhds hHclow (fun n => hHcup n)
        have hglimc : glim cΔ = greenEnvelope p₀ p :=
          tendsto_nhds_unique (hHtends cΔ hcball) htendcH
        -- the nonnegative harmonic difference vanishes at the centre, hence everywhere
        set d : ℂ → ℝ := fun z => glim z - flim z with hd2def
        have hdharm : HarmonicOnNhd d (ball cΔ R) := by
          intro z hz
          exact (hglimharm z hz).sub (hflimharm z hz)
        have hdnn : ∀ z ∈ ball cΔ R, 0 ≤ d z := by
          intro z hz
          simp only [hd2def]
          linarith [hfg z hz]
        have hdc : d cΔ = 0 := by
          simp only [hd2def]
          rw [hglimc, hflimc]
          ring
        have hdzero := harmonic_eq_zero_of_nonneg_eq_zero isOpen_ball
          (convex_ball cΔ R).isPreconnected hdharm hdnn hcball hdc
        have hdq : glim zq = flim zq := by
          have h1 := hdzero zq hzq
          simp only [hd2def] at h1
          linarith
        -- the second sequence pins the envelope value from below
        have hbup : ∀ n, b n ≤ glim zq := by
          intro n
          have h1 : b n ≤ Pm (G n) (E.symm zq) := by
            rw [← hg'q n]
            exact (hg'leG n _).trans (hPmge _ (hGF n) _ hqne)
          rw [← hHmem n zq hzq] at h1
          exact h1.trans (hHlelim zq hzq n)
        have henvq : greenEnvelope p₀ (E.symm zq) =
            sSup ((fun v => v (E.symm zq)) '' greenFamily p₀) := rfl
        rw [henvq, ← hdq]
        exact le_of_tendsto' hbtend hbup
      -- assemble: the envelope reading agrees with `flim` near the centre
      have hev : flim =ᶠ[𝓝 cΔ] greenEnvelope p₀ ∘ ⇑E.symm := by
        filter_upwards [isOpen_ball.mem_nhds hcball] with z hz
        have h1 : flim z ≤ greenEnvelope p₀ (E.symm z) := by
          simp only [hflimdef]
          exact ciSup_le fun n => hWle z hz n
        exact le_antisymm h1 (hflimge z hz)
      have hHc : HarmonicAt (greenEnvelope p₀ ∘ ⇑E.symm) cΔ :=
        (harmonicAt_congr_nhds hev).mp (hflimharm cΔ hcball)
      exact (mharmonicAt_iff_of_mem_maximalAtlas hEatlas hpsrc).mpr (hcΔ ▸ hHc)
  -- ### Two distinct points exist (the surface is noncompact).
  have hnt : ∃ x y : M, x ≠ y := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton M := ⟨fun a b => hcon a b⟩
    have : CompactSpace M := Finite.compactSpace
    exact NoncompactSpace.noncompact_univ (X := M) isCompact_univ
  have hconn : IsConnected ({p₀}ᶜ : Set M) :=
    isConnected_compl_singleton_of_connected hnt p₀
  -- ### Boundedness at every point, by the clopen argument.
  have hBddAll : ∀ x, x ≠ p₀ → BddAbove ((fun v => v x) '' greenFamily p₀) := by
    obtain ⟨x₀, hx₀ne, hx₀bdd⟩ := hG
    set S1 : Set M := {x : M | x ∈ ({p₀}ᶜ : Set M) ∧
      BddAbove ((fun v => v x) '' greenFamily p₀)} with hS1def
    set S2 : Set M := {x : M | x ∈ ({p₀}ᶜ : Set M) ∧
      ¬ BddAbove ((fun v => v x) '' greenFamily p₀)} with hS2def
    have hS1open : IsOpen S1 := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxmem, hxbdd⟩
      obtain ⟨U, hUopen, hxU, hUsub, ⟨wb, hwbF, hHar⟩, -⟩ :=
        key x (Set.mem_compl_singleton_iff.mp hxmem)
      refine Filter.mem_of_superset (hUopen.mem_nhds hxU) fun y hyU => ?_
      refine ⟨hUsub hyU,
        ⟨wb y + 3 * (sSup ((fun v => v x) '' greenFamily p₀) - wb x), ?_⟩⟩
      rintro c ⟨v, hvF, rfl⟩
      obtain ⟨q, hqF, hqge, hqpair⟩ := hHar v hvF
      obtain ⟨h1, -⟩ := hqpair y hyU
      have h2 : q x ≤ sSup ((fun v => v x) '' greenFamily p₀) :=
        le_csSup hxbdd ⟨q, hqF, rfl⟩
      have h3 : v y ≤ q y := hqge y (Set.mem_compl_singleton_iff.mp (hUsub hyU))
      change v y ≤ wb y + 3 * (sSup ((fun v => v x) '' greenFamily p₀) - wb x)
      linarith
    have hS2open : IsOpen S2 := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxmem, hxnb⟩
      obtain ⟨U, hUopen, hxU, hUsub, ⟨wb, hwbF, hHar⟩, -⟩ :=
        key x (Set.mem_compl_singleton_iff.mp hxmem)
      refine Filter.mem_of_superset (hUopen.mem_nhds hxU) fun y hyU => ?_
      refine ⟨hUsub hyU, fun hybdd => hxnb ?_⟩
      refine ⟨wb x + 3 * (sSup ((fun v => v y) '' greenFamily p₀) - wb y), ?_⟩
      rintro c ⟨v, hvF, rfl⟩
      obtain ⟨q, hqF, hqge, hqpair⟩ := hHar v hvF
      obtain ⟨-, h1⟩ := hqpair y hyU
      have h2 : q y ≤ sSup ((fun v => v y) '' greenFamily p₀) :=
        le_csSup hybdd ⟨q, hqF, rfl⟩
      have h3 : v x ≤ q x := hqge x (Set.mem_compl_singleton_iff.mp hxmem)
      change v x ≤ wb x + 3 * (sSup ((fun v => v y) '' greenFamily p₀) - wb y)
      linarith
    have hdisj : Disjoint S1 S2 := by
      rw [Set.disjoint_left]
      rintro x ⟨-, h0⟩ ⟨-, hne⟩
      exact hne h0
    have hunion : ({p₀}ᶜ : Set M) ⊆ S1 ∪ S2 := by
      intro x hx
      by_cases h : BddAbove ((fun v => v x) '' greenFamily p₀)
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    have hkey := IsPreconnected.subset_left_of_subset_union hS1open hS2open hdisj hunion
      ⟨x₀, Set.mem_compl_singleton_iff.mpr hx₀ne,
        Set.mem_compl_singleton_iff.mpr hx₀ne, hx₀bdd⟩ hconn.isPreconnected
    intro x hx
    exact (hkey (Set.mem_compl_singleton_iff.mpr hx)).2
  refine ⟨?_, hBddAll⟩
  intro x hxmem
  obtain ⟨U, -, -, -, -, hHarm⟩ := key x (Set.mem_compl_singleton_iff.mp hxmem)
  exact hHarm hBddAll

/-- The Green's function is strictly positive off the pole. -/
theorem greenEnvelope_pos [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) :
    ∀ x ≠ p₀, 0 < greenEnvelope p₀ x := by
  classical
  -- Transfer of subharmonicity along a pointwise equality on a subdomain.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  -- ### Setup: the pole chart and a small closed ball inside its target.
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he
  set c : ℂ := e p₀ with hc
  have hp₀src : p₀ ∈ e.source := by rw [he]; exact mem_chart_source ℂ p₀
  have heatlas : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
    rw [he]; exact IsManifold.chart_mem_maximalAtlas p₀
  have hctgt : c ∈ e.target := by rw [hc]; exact e.map_source hp₀src
  obtain ⟨ε, hε, hballε⟩ := Metric.isOpen_iff.mp e.open_target c hctgt
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hcbsub : closedBall c r ⊆ e.target :=
    (Metric.closedBall_subset_ball (by rw [hr]; linarith)).trans hballε
  have hbsub : ball c r ⊆ e.target := ball_subset_closedBall.trans hcbsub
  -- ### The plane profile: a truncated logarithm.
  set g : ℂ → ℝ := fun z => max (Real.log r - Real.log ‖z - c‖) 0 with hg
  have hgnonneg : ∀ z, 0 ≤ g z := fun z => le_max_right _ _
  have hharm : HarmonicOnNhd (fun z => Real.log r - Real.log ‖z - c‖) {c}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun t : ℂ => t - c) z := by
      exact analyticAt_id.sub analyticAt_const
    have hne : z - c ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log r)).sub (hana.harmonicAt_log_norm hne)
  have hgsub : SubharmonicOn g {c}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) {c}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hharm) h0
  have hgcont : ContinuousOn g {c}ᶜ := hgsub.1
  have hgzero : ∀ z, z ∉ ball c r → g z = 0 := by
    intro z hz
    have hzr : r ≤ ‖z - c‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hz
      exact hz
    have hle : Real.log r ≤ Real.log ‖z - c‖ := Real.log_le_log hr0 hzr
    simp only [hg]
    exact max_eq_right (by linarith)
  -- ### The family member: the truncated logarithm read through the chart.
  set v₀ : M → ℝ := fun x => if x ∈ e.source then g (e x) else 0 with hv₀
  have hv₀nonneg : ∀ x, 0 ≤ v₀ x := by
    intro x
    simp only [hv₀]
    split_ifs
    · exact hgnonneg _
    · exact le_rfl
  set K : Set M := e.symm '' closedBall c r
  have hKcompact : IsCompact K :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn_symm.mono hcbsub)
  have hKsource : K ⊆ e.source := by
    rintro x ⟨w, hw, rfl⟩
    exact e.map_target (hcbsub hw)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hv₀zero : ∀ x, x ∉ K → v₀ x = 0 := by
    intro x hx
    by_cases hxs : x ∈ e.source
    · simp only [hv₀, ite_eq_left hxs]
      by_contra hne
      have hball2 : e x ∈ ball c r := by
        by_contra hnb
        exact hne (hgzero _ hnb)
      exact hx ⟨e x, ball_subset_closedBall hball2, e.left_inv hxs⟩
    · simp only [hv₀, ite_eq_right hxs]
  have hexc : ∀ x, x ∈ e.source → x ≠ p₀ → e x ≠ c := by
    intro x hxs hxp heq
    exact hxp (e.injOn hxs hp₀src (by rw [← hc]; exact heq))
  -- ### Membership in the Green's family.
  have hv₀mem : v₀ ∈ greenFamily p₀ := by
    refine ⟨?_, ?_, ⟨K, hKcompact, ?_, hv₀zero⟩, ⟨Real.log r, ?_⟩⟩
    · -- subharmonicity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      by_cases hxs : x ∈ e.source
      · -- read in the pole chart: `v₀ ∘ e.symm` agrees with `g` near `e x`
        refine (msubharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mpr ?_
        have hopen2 : IsOpen (e.target ∩ {c}ᶜ) :=
          e.open_target.inter isOpen_compl_singleton
        have hmem2 : e x ∈ e.target ∩ {c}ᶜ :=
          ⟨e.map_source hxs, Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)⟩
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqon : Set.EqOn g (v₀ ∘ e.symm) (ball (e x) ρ) := by
          intro z hz
          have hzt : z ∈ e.target := (hρsub hz).1
          have hzs : e.symm z ∈ e.source := e.map_target hzt
          simp only [Function.comp_apply, hv₀, ite_eq_left hzs, e.right_inv hzt]
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ hgsub (fun z hz => (hρsub hz).2) heqon⟩
      · -- off the chart: `v₀` vanishes on the open complement of `K`
        have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hopen2 : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ) :=
          (chartAt ℂ x).isOpen_inter_preimage_symm hKclosed.isOpen_compl
        have hmem2 : chartAt ℂ x x ∈
            (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ := by
          refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
          rw [Set.mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
          exact hxK
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqz : Set.EqOn (fun _ : ℂ => (0 : ℝ)) (v₀ ∘ (chartAt ℂ x).symm)
            (ball (chartAt ℂ x x) ρ) := by
          intro z hz
          exact (hv₀zero _ ((hρsub hz).2)).symm
        have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ x x) ρ) :=
          HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ h0 subset_rfl heqz⟩
    · -- continuity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      apply ContinuousAt.continuousWithinAt
      by_cases hxs : x ∈ e.source
      · have hgc : ContinuousAt g (e x) := hgcont.continuousAt
          (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)))
        refine (hgc.comp (e.continuousAt hxs)).congr_of_eventuallyEq ?_
        filter_upwards [e.open_source.mem_nhds hxs] with y hy
        simp only [Function.comp_apply, hv₀, ite_eq_left hy]
      · have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hev : v₀ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [hKclosed.isOpen_compl.mem_nhds hxK] with y hy
          exact hv₀zero y hy
        exact continuousAt_const.congr_of_eventuallyEq hev
    · -- the support is not everything
      intro hKuniv
      exact noncompact_univ M (hKuniv ▸ hKcompact)
    · -- logarithmic pole growth
      have hopen2 : IsOpen (e.source ∩ e ⁻¹' ball c r) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hnb : e.source ∩ e ⁻¹' ball c r ∈ 𝓝 p₀ := by
        refine hopen2.mem_nhds ⟨hp₀src, ?_⟩
        rw [Set.mem_preimage, ← hc]
        exact mem_ball_self hr0
      filter_upwards [nhdsWithin_le_nhds hnb, eventually_mem_nhdsWithin] with x hx hxp
      have hxsrc : x ∈ e.source := hx.1
      have hxne : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hxp
      have hpole_eq : poleCoord p₀ x = e x - c := by
        simp only [poleCoord, ← he, ← hc]
      rw [hpole_eq]
      have hpos : 0 < ‖e x - c‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (hexc x hxsrc hxne))
      have hlt : ‖e x - c‖ < r := by
        have hxball : e x ∈ ball c r := hx.2
        rw [mem_ball, dist_eq_norm] at hxball
        exact hxball
      have hBA : Real.log ‖e x - c‖ < Real.log r := Real.log_lt_log hpos hlt
      simp only [hv₀, ite_eq_left hxsrc, hg]
      rw [max_eq_left (by linarith)]
      linarith
  -- ### The envelope dominates the member, hence is nonnegative off the pole.
  obtain ⟨hGh, hGbdd⟩ := mharmonicOn_greenEnvelope hG
  have hge : ∀ z, z ≠ p₀ → v₀ z ≤ greenEnvelope p₀ z := by
    intro z hz
    exact le_csSup (hGbdd z hz) ⟨v₀, hv₀mem, rfl⟩
  have hGnonneg : ∀ z, z ≠ p₀ → 0 ≤ greenEnvelope p₀ z :=
    fun z hz => (hv₀nonneg z).trans (hge z hz)
  -- ### A witness point where the envelope is strictly positive.
  set w : ℂ := c + ((r / 2 : ℝ) : ℂ) with hwdef
  have hwc : ‖w - c‖ = r / 2 := by
    rw [hwdef, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hwball : w ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, hwc]
    linarith
  have hwt : w ∈ e.target := hbsub hwball
  have hys : e.symm w ∈ e.source := e.map_target hwt
  have hyw : e (e.symm w) = w := e.right_inv hwt
  have hynp : e.symm w ≠ p₀ := by
    intro h
    have h2 := congrArg (e : M → ℂ) h
    rw [hyw] at h2
    have h0 : (0 : ℝ) = r / 2 := by
      rw [← hwc, h2, ← hc, sub_self, norm_zero]
    linarith
  have hv₀y : 0 < v₀ (e.symm w) := by
    have hlog : Real.log (r / 2) < Real.log r :=
      Real.log_lt_log (by linarith) (by linarith)
    simp only [hv₀, ite_eq_left hys, hyw, hg, hwc]
    exact lt_max_iff.mpr (Or.inl (by linarith))
  have hGy : 0 < greenEnvelope p₀ (e.symm w) := lt_of_lt_of_le hv₀y (hge _ hynp)
  -- ### Strong-maximum propagation on the connected punctured surface.
  intro x hxp
  rcases (hGnonneg x hxp).lt_or_eq with hpos | heq0
  · exact hpos
  · exfalso
    have hxmem : x ∈ ({p₀}ᶜ : Set M) := Set.mem_compl_singleton_iff.mpr hxp
    have hsopen : IsOpen ({p₀}ᶜ : Set M) := isOpen_compl_singleton
    have hsconn : IsConnected ({p₀}ᶜ : Set M) :=
      isConnected_compl_singleton_of_connected ⟨e.symm w, p₀, hynp⟩ p₀
    have hsub : MSubharmonicOn (-(greenEnvelope p₀)) ({p₀}ᶜ : Set M) :=
      fun z hz => ((hGh z hz).neg).msubharmonicAt
    have hSopen : IsOpen {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z = 0} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzs, hz0⟩
      have hmax : ∀ a ∈ ({p₀}ᶜ : Set M),
          (-(greenEnvelope p₀)) a ≤ (-(greenEnvelope p₀)) z := by
        intro a ha
        have h1 : 0 ≤ greenEnvelope p₀ a :=
          hGnonneg a (Set.mem_compl_singleton_iff.mp ha)
        simp only [Pi.neg_apply, hz0, neg_zero]
        linarith
      have hev := MSubharmonicAt.eventually_eq_of_le hsopen hzs hsub hmax
      filter_upwards [hev, hsopen.mem_nhds hzs] with a ha has
      refine ⟨has, ?_⟩
      simp only [Pi.neg_apply, hz0, neg_zero, neg_eq_zero] at ha
      exact ha
    have hVopen : IsOpen {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z ≠ 0} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzs, hzne⟩
      have hcont : ContinuousAt (greenEnvelope p₀) z := (hGh z hzs).continuousAt
      filter_upwards [hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hzne),
        hsopen.mem_nhds hzs] with a ha has
      exact ⟨has, ha⟩
    have hdisj : Disjoint {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z = 0}
        {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z ≠ 0} := by
      rw [Set.disjoint_left]
      rintro z ⟨_, h0⟩ ⟨_, hne⟩
      exact hne h0
    have hunion : ({p₀}ᶜ : Set M) ⊆
        {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z = 0} ∪
          {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z ≠ 0} := by
      intro z hz
      by_cases h : greenEnvelope p₀ z = 0
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    have hkey := IsPreconnected.subset_left_of_subset_union hSopen hVopen hdisj hunion
      ⟨x, hxmem, hxmem, heq0.symm⟩ hsconn.isPreconnected
    have hy0 : greenEnvelope p₀ (e.symm w) = 0 :=
      (hkey (Set.mem_compl_singleton_iff.mpr hynp)).2
    linarith

/-- **Pole behavior**: near the pole, `G + log|z|` extends to a harmonic
function of the local coordinate. -/
theorem exists_harmonic_pole_extension [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) :
    ∃ r > 0, ball (chartAt ℂ p₀ p₀) r ⊆ (chartAt ℂ p₀).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₀ p₀) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₀ p₀) r \ {chartAt ℂ p₀ p₀},
          h w = greenEnvelope p₀ ((chartAt ℂ p₀).symm w) +
            Real.log ‖w - chartAt ℂ p₀ p₀‖ := by
  classical
  -- ### Generic plane-side helpers.
  -- Restriction of subharmonicity to a subset.
  have smono : ∀ (f : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn f U → V ⊆ U →
      SubharmonicOn f V := fun f U V hf hVU =>
    ⟨hf.1.mono hVU, fun a ha ρ hρ hb => hf.2 a (hVU ha) ρ hρ (hb.trans hVU)⟩
  -- Transfer of subharmonicity along a pointwise equality on a subdomain.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  -- Subharmonic plus harmonic is subharmonic.
  have subAdd : ∀ (f g : ℂ → ℝ) (U : Set ℂ), SubharmonicOn f U → HarmonicOnNhd g U →
      SubharmonicOn (fun z => f z + g z) U := by
    intro f g U hf hgh
    refine ⟨hf.1.add hgh.continuousOn, ?_⟩
    intro a ha ρ hρ hb
    have hsphere : sphere a ρ ⊆ U := sphere_subset_closedBall.trans hb
    have hfci : CircleIntegrable f a ρ := (hf.1.mono hsphere).circleIntegrable hρ.le
    have hgci : CircleIntegrable g a ρ :=
      (hgh.continuousOn.mono hsphere).circleIntegrable hρ.le
    rw [Real.circleAverage_fun_add hfci hgci]
    have hgavg : Real.circleAverage g a ρ = g a := by
      apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      rw [abs_of_pos hρ]
      exact hgh.mono hb
    have hfavg : f a ≤ Real.circleAverage f a ρ := hf.2 a ha ρ hρ hb
    rw [hgavg]
    linarith
  -- ### Setup: the pole chart and a small closed ball inside its target.
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he
  set c : ℂ := e p₀ with hc
  have hp₀src : p₀ ∈ e.source := by rw [he]; exact mem_chart_source ℂ p₀
  have heatlas : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
    rw [he]; exact IsManifold.chart_mem_maximalAtlas p₀
  have hctgt : c ∈ e.target := by rw [hc]; exact e.map_source hp₀src
  obtain ⟨ε, hε, hballε⟩ := Metric.isOpen_iff.mp e.open_target c hctgt
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hcbsub : closedBall c r ⊆ e.target :=
    (Metric.closedBall_subset_ball (by rw [hr]; linarith)).trans hballε
  have hbsub : ball c r ⊆ e.target := ball_subset_closedBall.trans hcbsub
  have hsymmc : e.symm c = p₀ := by rw [hc]; exact e.left_inv hp₀src
  have hexc : ∀ x, x ∈ e.source → x ≠ p₀ → e x ≠ c := by
    intro x hxs hxp heq
    exact hxp (e.injOn hxs hp₀src (by rw [← hc]; exact heq))
  have hsymm_ne : ∀ w, w ∈ e.target → w ≠ c → e.symm w ≠ p₀ := by
    intro w hwt hwne hcon
    apply hwne
    have h2 := congrArg (e : M → ℂ) hcon
    rw [e.right_inv hwt] at h2
    rw [h2, hc]
  have hsymm_src : ∀ w, w ∈ e.target → e.symm w ∈ e.source :=
    fun w hw => e.map_target hw
  have hsymm_eq : ∀ w, w ∈ e.target → e (e.symm w) = w := fun w hw => e.right_inv hw
  -- ### Envelope facts: harmonicity off the pole and pointwise boundedness.
  obtain ⟨hGh, hGbdd⟩ := mharmonicOn_greenEnvelope hG
  -- ### The plane profile: a truncated logarithm.
  set g : ℂ → ℝ := fun z => max (Real.log r - Real.log ‖z - c‖) 0 with hg
  have hgnonneg : ∀ z, 0 ≤ g z := fun z => le_max_right _ _
  have hgkharm : HarmonicOnNhd (fun z => Real.log r - Real.log ‖z - c‖) {c}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun t : ℂ => t - c) z := by
      exact analyticAt_id.sub analyticAt_const
    have hne : z - c ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log r)).sub (hana.harmonicAt_log_norm hne)
  have hgsub : SubharmonicOn g {c}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) {c}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hgkharm) h0
  have hgcont : ContinuousOn g {c}ᶜ := hgsub.1
  have hgzero : ∀ z, z ∉ ball c r → g z = 0 := by
    intro z hz
    have hzr : r ≤ ‖z - c‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hz
      exact hz
    have hle : Real.log r ≤ Real.log ‖z - c‖ := Real.log_le_log hr0 hzr
    simp only [hg]
    exact max_eq_right (by linarith)
  -- ### The family member: the truncated logarithm read through the chart.
  set v₀ : M → ℝ := fun x => if x ∈ e.source then g (e x) else 0 with hv₀
  set K : Set M := e.symm '' closedBall c r
  have hKcompact : IsCompact K :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn_symm.mono hcbsub)
  have hKsource : K ⊆ e.source := by
    rintro x ⟨w, hw, rfl⟩
    exact e.map_target (hcbsub hw)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hv₀zero : ∀ x, x ∉ K → v₀ x = 0 := by
    intro x hx
    by_cases hxs : x ∈ e.source
    · simp only [hv₀, ite_eq_left hxs]
      by_contra hne
      have hball2 : e x ∈ ball c r := by
        by_contra hnb
        exact hne (hgzero _ hnb)
      exact hx ⟨e x, ball_subset_closedBall hball2, e.left_inv hxs⟩
    · simp only [hv₀, ite_eq_right hxs]
  -- ### Membership of the truncated logarithm in the Green's family.
  have hv₀mem : v₀ ∈ greenFamily p₀ := by
    refine ⟨?_, ?_, ⟨K, hKcompact, ?_, hv₀zero⟩, ⟨Real.log r, ?_⟩⟩
    · -- subharmonicity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      by_cases hxs : x ∈ e.source
      · -- read in the pole chart: `v₀ ∘ e.symm` agrees with `g` near `e x`
        refine (msubharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mpr ?_
        have hopen2 : IsOpen (e.target ∩ {c}ᶜ) :=
          e.open_target.inter isOpen_compl_singleton
        have hmem2 : e x ∈ e.target ∩ {c}ᶜ :=
          ⟨e.map_source hxs, Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)⟩
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqon : Set.EqOn g (v₀ ∘ e.symm) (ball (e x) ρ) := by
          intro z hz
          have hzt : z ∈ e.target := (hρsub hz).1
          have hzs : e.symm z ∈ e.source := e.map_target hzt
          simp only [Function.comp_apply, hv₀, ite_eq_left hzs, e.right_inv hzt]
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ hgsub (fun z hz => (hρsub hz).2) heqon⟩
      · -- off the chart: `v₀` vanishes on the open complement of `K`
        have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hopen2 : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ) :=
          (chartAt ℂ x).isOpen_inter_preimage_symm hKclosed.isOpen_compl
        have hmem2 : chartAt ℂ x x ∈
            (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ := by
          refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
          rw [Set.mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
          exact hxK
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqz : Set.EqOn (fun _ : ℂ => (0 : ℝ)) (v₀ ∘ (chartAt ℂ x).symm)
            (ball (chartAt ℂ x x) ρ) := by
          intro z hz
          exact (hv₀zero _ ((hρsub hz).2)).symm
        have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ x x) ρ) :=
          HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ h0 subset_rfl heqz⟩
    · -- continuity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      apply ContinuousAt.continuousWithinAt
      by_cases hxs : x ∈ e.source
      · have hgc : ContinuousAt g (e x) := hgcont.continuousAt
          (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)))
        refine (hgc.comp (e.continuousAt hxs)).congr_of_eventuallyEq ?_
        filter_upwards [e.open_source.mem_nhds hxs] with y hy
        simp only [Function.comp_apply, hv₀, ite_eq_left hy]
      · have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hev : v₀ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [hKclosed.isOpen_compl.mem_nhds hxK] with y hy
          exact hv₀zero y hy
        exact continuousAt_const.congr_of_eventuallyEq hev
    · -- the support is not everything
      intro hKuniv
      exact noncompact_univ M (hKuniv ▸ hKcompact)
    · -- logarithmic pole growth
      have hopen2 : IsOpen (e.source ∩ e ⁻¹' ball c r) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hnb : e.source ∩ e ⁻¹' ball c r ∈ 𝓝 p₀ := by
        refine hopen2.mem_nhds ⟨hp₀src, ?_⟩
        rw [Set.mem_preimage, ← hc]
        exact mem_ball_self hr0
      filter_upwards [nhdsWithin_le_nhds hnb, eventually_mem_nhdsWithin] with x hx hxp
      have hxsrc : x ∈ e.source := hx.1
      have hxne : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hxp
      have hpole_eq : poleCoord p₀ x = e x - c := by
        simp only [poleCoord, ← he, ← hc]
      rw [hpole_eq]
      have hpos : 0 < ‖e x - c‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (hexc x hxsrc hxne))
      have hlt : ‖e x - c‖ < r := by
        have hxball : e x ∈ ball c r := hx.2
        rw [mem_ball, dist_eq_norm] at hxball
        exact hxball
      have hBA : Real.log ‖e x - c‖ < Real.log r := Real.log_lt_log hpos hlt
      simp only [hv₀, ite_eq_left hxsrc, hg]
      rw [max_eq_left (by linarith)]
      linarith
  -- ### Members lie below the envelope.
  have hmem_le : ∀ v ∈ greenFamily p₀, ∀ x : M, x ≠ p₀ → v x ≤ greenEnvelope p₀ x
      :=
    fun v hv x hx => le_csSup (hGbdd x hx) ⟨v, hv, rfl⟩
  -- ### The half-radius disc.
  set s : ℝ := r / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsr : s < r := by rw [hs]; linarith
  have hssub : ball c s ⊆ e.target := (ball_subset_ball hsr.le).trans hbsub
  -- ### Readings of the envelope are harmonic on the punctured target.
  have hGread : ∀ w, w ∈ e.target → w ≠ c →
      HarmonicAt (greenEnvelope p₀ ∘ ⇑e.symm) w := by
    intro w hwt hwne
    have hxs : e.symm w ∈ e.source := hsymm_src w hwt
    have hxne : e.symm w ≠ p₀ := hsymm_ne w hwt hwne
    have hmh : MHarmonicAt (greenEnvelope p₀) (e.symm w) :=
      hGh _ (Set.mem_compl_singleton_iff.mpr hxne)
    have h2 := (mharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mp hmh
    rwa [hsymm_eq w hwt] at h2
  -- ### The logarithmic kernel is harmonic off the centre.
  have hLg : ∀ w : ℂ, w ≠ c → HarmonicAt (fun q : ℂ => Real.log ‖q - c‖) w := by
    intro w hw
    have h1 : AnalyticAt ℂ (fun q : ℂ => q - c) w := analyticAt_id.sub analyticAt_const
    exact h1.harmonicAt_log_norm (sub_ne_zero.2 hw)
  -- ### The outer circle and its envelope maximum `B`.
  have hsphsub : sphere c s ⊆ e.target := fun w hw =>
    hbsub (mem_ball.2 (lt_of_eq_of_lt (mem_sphere.1 hw) hsr))
  have hsphne : ∀ w ∈ sphere c s, w ≠ c := by
    intro w hw hcon
    have h1 := mem_sphere.1 hw
    rw [hcon, dist_self] at h1
    exact hs0.ne h1
  have hGcontS : ContinuousOn (greenEnvelope p₀ ∘ ⇑e.symm) (sphere c s) := fun w hw =>
    ((hGread w (hsphsub hw) (hsphne w hw)).1.continuousAt).continuousWithinAt
  obtain ⟨wB, -, hwBmax⟩ := (isCompact_sphere c s).exists_isMaxOn
    ((NormedSpace.sphere_nonempty).2 hs0.le) hGcontS
  set B : ℝ := (greenEnvelope p₀ ∘ ⇑e.symm) wB with hB
  have hBle : ∀ w ∈ sphere c s, greenEnvelope p₀ (e.symm w) ≤ B := fun w hw => hwBmax hw
  -- ### Per-member reading is subharmonic on the punctured disc.
  have hVsub : ∀ v ∈ greenFamily p₀,
      SubharmonicOn (v ∘ ⇑e.symm) (ball c r \ {c}) := by
    intro v hv
    obtain ⟨hvsub, hvcont, -, -⟩ := hv
    have hUopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
    apply subharmonicOn_of_locally hUopen
    · -- continuity of the reading
      intro w hw
      have hwt : w ∈ e.target := hbsub hw.1
      have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
      have h1 : ContinuousAt (⇑e.symm) w := e.continuousAt_symm hwt
      have h2 : ContinuousAt v (e.symm w) :=
        hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.mpr (hsymm_ne w hwt hwne)))
      exact (h2.comp h1).continuousWithinAt
    · -- the local sub-mean-value inequality, from the chart-independent reading
      intro w hw
      have hwt : w ∈ e.target := hbsub hw.1
      have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
      have hxs : e.symm w ∈ e.source := hsymm_src w hwt
      have hMS : MSubharmonicAt v (e.symm w) :=
        hvsub _ (Set.mem_compl_singleton_iff.mpr (hsymm_ne w hwt hwne))
      obtain ⟨ρ, hρ, -, hsub⟩ :=
        (msubharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mp hMS
      rw [hsymm_eq w hwt] at hsub
      refine ⟨ρ, hρ, ?_⟩
      intro ρ' hρ'0 hρ'lt _hcb
      exact hsub.2 w (mem_ball_self hρ) ρ' hρ'0 (Metric.closedBall_subset_ball hρ'lt)
  -- ### Per-member pole bound through the chart.
  have hpole' : ∀ v ∈ greenFamily p₀, ∃ Cv : ℝ, ∃ δ > 0,
      ∀ w ∈ ball c δ, w ≠ c → v (e.symm w) + Real.log ‖w - c‖ ≤ Cv := by
    intro v hv
    obtain ⟨-, -, -, Cv, hCv⟩ := hv
    refine ⟨Cv, ?_⟩
    have h1 : Tendsto (⇑e.symm) (𝓝 c) (𝓝 p₀) := by
      have h2 : ContinuousAt (⇑e.symm) c := e.continuousAt_symm hctgt
      rwa [ContinuousAt, hsymmc] at h2
    have h3 : ∀ᶠ x in 𝓝 p₀, x ∈ ({p₀}ᶜ : Set M) →
        v x + Real.log ‖poleCoord p₀ x‖ ≤ Cv := eventually_nhdsWithin_iff.mp hCv
    have h4 := h1.eventually h3
    have h5 : ∀ᶠ w in 𝓝 c, w ∈ e.target := e.open_target.mem_nhds hctgt
    have h6 : ∀ᶠ w in 𝓝 c, w ≠ c → v (e.symm w) + Real.log ‖w - c‖ ≤ Cv := by
      filter_upwards [h4, h5] with w h4w h5w hwne
      have hne2 : e.symm w ≠ p₀ := hsymm_ne w h5w hwne
      have hpc : poleCoord p₀ (e.symm w) = w - c := by
        simp only [poleCoord, ← he, ← hc, hsymm_eq w h5w]
      have h7 := h4w (Set.mem_compl_singleton_iff.mpr hne2)
      rwa [hpc] at h7
    rw [Metric.eventually_nhds_iff_ball] at h6
    exact h6
  -- ### The key annulus estimate, per member.
  have key : ∀ v ∈ greenFamily p₀, ∀ w₀ ∈ ball c s \ {c},
      v (e.symm w₀) + (Real.log ‖w₀ - c‖ - Real.log s) ≤ B := by
    intro v hv w₀ hw₀
    obtain ⟨Cv, δv, hδv0, hδv⟩ := hpole' v hv
    have hsubV : SubharmonicOn (v ∘ ⇑e.symm) (ball c r \ {c}) := hVsub v hv
    have hw₀ne : w₀ ≠ c := fun hcon => hw₀.2 (Set.mem_singleton_iff.2 hcon)
    have hw₀n : 0 < ‖w₀ - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hw₀ne)
    have hw₀lt : ‖w₀ - c‖ < s := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hw₀.1
    have ht0 : Real.log ‖w₀ - c‖ - Real.log s < 0 :=
      sub_neg.2 (Real.log_lt_log hw₀n hw₀lt)
    set t : ℝ := Real.log ‖w₀ - c‖ - Real.log s with htdef
    have htne : t ≠ 0 := ne_of_lt ht0
    refine le_of_forall_pos_le_add ?_
    intro η hη
    set ε : ℝ := η / (-t) with hεdef
    have hε0 : 0 < ε := div_pos hη (by linarith)
    have hεt : ε * t = -η := by
      calc ε * t = η / (-t) * t := by rw [hεdef]
        _ = -(η / t * t) := by rw [div_neg]; ring
        _ = -η := by rw [div_mul_cancel₀ η htne]
    -- The inner excision radius `σ`, small enough for the barrier to win.
    set Q : ℝ := (B - Cv + (1 + ε) * Real.log s) / ε with hQdef
    set σ : ℝ := min (min (δv / 2) (‖w₀ - c‖ / 2)) (min (s / 2) (Real.exp Q)) with hσdef
    have hσ0 : 0 < σ :=
      lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (Real.exp_pos Q))
    have hσδ : σ < δv :=
      lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
    have hσw : σ < ‖w₀ - c‖ :=
      lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
    have hσs : σ < s :=
      lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have hσQ : Real.log σ ≤ Q := by
      have h1 : σ ≤ Real.exp Q := (min_le_right _ _).trans (min_le_right _ _)
      calc Real.log σ ≤ Real.log (Real.exp Q) := Real.log_le_log hσ0 h1
        _ = Q := Real.log_exp Q
    have hbarrier : Cv - Real.log σ + (1 + ε) * (Real.log σ - Real.log s) ≤ B := by
      have h5 : ε * Real.log σ ≤ ε * Q := mul_le_mul_of_nonneg_left hσQ hε0.le
      have h6 : ε * Q = B - Cv + (1 + ε) * Real.log s := by
        rw [hQdef, mul_comm]
        exact div_mul_cancel₀ _ hε0.ne'
      nlinarith [h5, h6]
    -- The annulus `A` and its closure/frontier geometry.
    set A : Set ℂ := ball c s \ closedBall c σ with hAdef
    have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
    have hAbdd : Bornology.IsBounded A := isBounded_ball.subset Set.sdiff_subset
    have hAsub : A ⊆ ball c r \ {c} := by
      intro z hz
      refine ⟨ball_subset_ball hsr.le hz.1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hz.2 (by rw [hcon]; exact mem_closedBall_self hσ0.le)
    have hclA : closure A ⊆ closedBall c s \ ball c σ := by
      intro z hz
      rw [hAdef, Set.sdiff_eq] at hz
      have h2 := closure_inter_subset_inter_closure (ball c s) ((closedBall c σ)ᶜ) hz
      rw [closure_ball c hs0.ne', closure_compl, interior_closedBall c hσ0.ne'] at h2
      exact ⟨h2.1, h2.2⟩
    have hfrA : frontier A ⊆ sphere c s ∪ sphere c σ := by
      intro z hz
      rw [hAdef, Set.sdiff_eq] at hz
      rcases frontier_inter_subset (ball c s) ((closedBall c σ)ᶜ) hz with h2 | h2
      · have h3 := h2.1
        rw [frontier_ball c hs0.ne'] at h3
        exact Or.inl h3
      · have h3 := h2.2
        rw [frontier_compl, frontier_closedBall c hσ0.ne'] at h3
        exact Or.inr h3
    have hKsub : closedBall c s \ ball c σ ⊆ ball c r \ {c} := by
      intro z hz
      constructor
      · exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz.1) hsr)
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        apply hz.2
        rw [hcon]
        exact mem_ball_self hσ0
    -- The barriered competitor `F` is subharmonic on the annulus.
    set F : ℂ → ℝ := fun z => v (e.symm z) + (1 + ε) * (Real.log ‖z - c‖ - Real.log s)
      with hFdef
    have hFsub : SubharmonicOn F A := by
      have h1 : SubharmonicOn (v ∘ ⇑e.symm) A := smono _ _ _ hsubV hAsub
      have h2 : HarmonicOnNhd
          (fun z => (1 + ε) * (Real.log ‖z - c‖ - Real.log s)) A := by
        intro z hz
        have hzne : z ≠ c := by
          intro hcon
          exact (hAsub hz).2 (Set.mem_singleton_iff.2 hcon)
        have h3 := ((hLg z hzne).sub (harmonicAt_const (Real.log s))).const_smul
          (c := 1 + ε)
        have heq3 : (1 + ε) • ((fun q : ℂ => Real.log ‖q - c‖) - fun _ => Real.log s)
            = fun z => (1 + ε) * (Real.log ‖z - c‖ - Real.log s) := by
          funext q
          simp [smul_eq_mul]
        rw [heq3] at h3
        exact h3
      exact subAdd _ _ _ h1 h2
    -- Continuity of `F` up to the closure of the annulus.
    have hVcontK : ContinuousOn (fun z => v (e.symm z)) (closedBall c s \ ball c σ) := by
      intro z hz
      have hzt : z ∈ e.target := hbsub (hKsub hz).1
      have hzne : z ≠ c := fun hcon => (hKsub hz).2 (Set.mem_singleton_iff.2 hcon)
      obtain ⟨-, hvcont, -, -⟩ := hv
      have h1 : ContinuousAt (⇑e.symm) z := e.continuousAt_symm hzt
      have h2 : ContinuousAt v (e.symm z) :=
        hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.mpr (hsymm_ne z hzt hzne)))
      exact (h2.comp h1).continuousWithinAt
    have hlogK : ContinuousOn (fun z : ℂ => Real.log ‖z - c‖)
        (closedBall c s \ ball c σ) := by
      apply ContinuousOn.log
      · fun_prop
      · intro z hz
        have h1 : σ ≤ dist z c := not_lt.1 fun hlt => hz.2 (mem_ball.2 hlt)
        rw [dist_eq_norm] at h1
        exact ne_of_gt (lt_of_lt_of_le hσ0 h1)
    have hFcont : ContinuousOn F (closure A) := by
      refine ContinuousOn.mono ?_ hclA
      exact hVcontK.add (continuousOn_const.mul (hlogK.sub continuousOn_const))
    -- The frontier bound `F ≤ B` on both circles.
    have hFfr : ∀ z ∈ frontier A, F z ≤ B := by
      intro z hz
      rcases hfrA hz with hzs | hzσ
      · -- outer circle: the barrier vanishes and the envelope maximum bounds `v`
        have hzn : ‖z - c‖ = s := by rw [← dist_eq_norm]; exact mem_sphere.1 hzs
        have hzt : z ∈ e.target := hsphsub hzs
        have hzne : z ≠ c := hsphne z hzs
        have h1 : v (e.symm z) ≤ greenEnvelope p₀ (e.symm z) :=
          hmem_le v hv _ (hsymm_ne z hzt hzne)
        have h2 : greenEnvelope p₀ (e.symm z) ≤ B := hBle z hzs
        simp only [hFdef]
        rw [hzn, sub_self, mul_zero, add_zero]
        linarith
      · -- inner circle: the pole bound and the barrier choice
        have hzn : ‖z - c‖ = σ := by rw [← dist_eq_norm]; exact mem_sphere.1 hzσ
        have hzne : z ≠ c := by
          intro hcon
          rw [hcon, sub_self, norm_zero] at hzn
          exact hσ0.ne' hzn.symm
        have hzball : z ∈ ball c δv := by
          rw [mem_ball, dist_eq_norm, hzn]
          exact hσδ
        have h1 : v (e.symm z) + Real.log ‖z - c‖ ≤ Cv := hδv z hzball hzne
        rw [hzn] at h1
        simp only [hFdef]
        rw [hzn]
        linarith [hbarrier]
    -- The maximum principle, evaluated at `w₀`.
    have hw₀A : w₀ ∈ A := by
      refine ⟨hw₀.1, ?_⟩
      intro hcon
      rw [mem_closedBall, dist_eq_norm] at hcon
      linarith
    have hFw₀ : F w₀ ≤ B :=
      hFsub.le_of_frontier_le hAopen hAbdd hFcont hFfr w₀ hw₀A
    simp only [hFdef] at hFw₀
    have hexp : (1 + ε) * (Real.log ‖w₀ - c‖ - Real.log s) = t + ε * t := by
      rw [htdef]; ring
    rw [hexp, hεt] at hFw₀
    linarith
  -- ### The two-sided bound on `G∘e.symm + log‖·−c‖` near the pole.
  have hup : ∀ w ∈ ball c s \ {c},
      greenEnvelope p₀ (e.symm w) + Real.log ‖w - c‖ ≤ B + Real.log s := by
    intro w hw
    have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
    have h1 : greenEnvelope p₀ (e.symm w) ≤ B - (Real.log ‖w - c‖ - Real.log s) := by
      refine csSup_le ⟨v₀ (e.symm w), ⟨v₀, hv₀mem, rfl⟩⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      have h2 := key v hv w hw
      linarith
    linarith
  have hlow : ∀ w ∈ ball c s \ {c},
      Real.log r ≤ greenEnvelope p₀ (e.symm w) + Real.log ‖w - c‖ := by
    intro w hw
    have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
    have hwt : w ∈ e.target := hssub hw.1
    have hne : e.symm w ≠ p₀ := hsymm_ne w hwt hwne
    have hxs : e.symm w ∈ e.source := hsymm_src w hwt
    have h1 : v₀ (e.symm w) ≤ greenEnvelope p₀ (e.symm w) := hmem_le v₀ hv₀mem _ hne
    have h2 : Real.log r - Real.log ‖w - c‖ ≤ v₀ (e.symm w) := by
      simp only [hv₀, ite_eq_left hxs, hg, hsymm_eq w hwt]
      exact le_max_left _ _
    linarith
  -- ### Harmonicity of `G∘e.symm + log‖·−c‖` on the punctured disc.
  set u : ℂ → ℝ := fun w => greenEnvelope p₀ (e.symm w) + Real.log ‖w - c‖ with hu
  have huharm : HarmonicOnNhd u (ball c s \ {c}) := by
    intro w hw
    have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
    have hwt : w ∈ e.target := hssub hw.1
    have h1 := (hGread w hwt hwne).add (hLg w hwne)
    have heq2 : ((greenEnvelope p₀ ∘ ⇑e.symm) + fun q : ℂ => Real.log ‖q - c‖) = u := by
      funext q
      simp only [hu, Pi.add_apply, Function.comp_apply]
    rw [heq2] at h1
    exact h1
  have hub : ∃ C, ∀ z ∈ ball c s \ {c}, |u z| ≤ C := by
    refine ⟨max (B + Real.log s) (-Real.log r), ?_⟩
    intro z hz
    rw [abs_le]
    constructor
    · have h1 := hlow z hz
      have h2 : -Real.log r ≤ max (B + Real.log s) (-Real.log r) := le_max_right _ _
      simp only [hu]
      linarith
    · have h1 := hup z hz
      simp only [hu]
      exact h1.trans (le_max_left _ _)
  -- ### Removable singularity and packaging.
  obtain ⟨h, hharm, heqon⟩ := exists_harmonicOnNhd_of_bounded_punctured hs0 huharm hub
  refine ⟨s, hs0, hssub, h, hharm, ?_⟩
  intro w hw
  have h5 := heqon hw
  simp only [hu] at h5
  exact h5

end RiemannDynamics
