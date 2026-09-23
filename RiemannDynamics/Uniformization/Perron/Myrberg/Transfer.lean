/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.Myrberg.DeckSum

/-!
# The Myrberg transfer and symmetry of the Green envelope

The Green property descends along the covering (the Myrberg argument), and
the Green envelope of a noncompact connected surface is symmetric.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff unitInterval

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Pole independence of hyperbolicity**: a connected surface hyperbolic at
one pole is hyperbolic at every pole. The finite fiber sums of the cover at
the new pole are dominated, through the symmetry of the simply connected
cover and the deck reindexing, by the value of the Green's function at the
old pole, and their supremum descends to a harmonic majorant with the exact
logarithmic pole, bounding the Perron family at the new pole. -/
theorem hasGreenFunction_of_hasGreenFunction [T2Space M] [ConnectedSpace M]
    [NoncompactSpace M] {p q : M} (hG : HasGreenFunction p) :
    HasGreenFunction q := by
  classical
  by_cases hqp : q = p
  · rwa [hqp]
  have hpq : p ≠ q := fun h => hqp h.symm
  -- ## Downstairs path connectivity and the two distinguished lifts.
  have : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace ℂ M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  obtain ⟨sp⟩ := PathConnectedSpace.joined p q
  obtain ⟨pb, hpb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = p :=
    ⟨pathCoverBase p, rfl⟩
  obtain ⟨qb, hqb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = q :=
    ⟨⟨q, ⟦sp⟧⟩, rfl⟩
  -- ## Topology of the universal path cover.
  have : PathConnectedSpace (PathCover p) := pathConnectedSpace_pathCover p
  have : ConnectedSpace (PathCover p) := PathConnectedSpace.connectedSpace
  have : SimplyConnectedSpace (PathCover p) := simplyConnectedSpace_pathCover p
  have : T2Space (PathCover p) := t2space_pathCover p
  have : NoncompactSpace (PathCover p) := noncompactSpace_pathCover p
  have : Nonempty (PathCover p) := ⟨pb⟩
  have : Nonempty (Finset {qc : PathCover p // pathCoverProj p qc = q}) := ⟨∅⟩
  -- ## Green's functions upstairs: at the base lift, hence everywhere.
  have hGpb : HasGreenFunction pb := hasGreenFunction_pathCover p hG hpb_proj
  have hGup : ∀ rc : PathCover p, HasGreenFunction rc := fun rc =>
    hasGreenFunction_of_simplyConnected hGpb
  -- ## Generic toolkit.
  have hproj_cont : Continuous (pathCoverProj p) :=
    (pathCoverProj_isCoveringMap p).continuous
  have hfibq_closed : IsClosed (pathCoverProj p ⁻¹' {q}) :=
    isClosed_singleton.preimage hproj_cont
  have hΩopen : IsOpen ((pathCoverProj p ⁻¹' {q})ᶜ : Set (PathCover p)) :=
    hfibq_closed.isOpen_compl
  -- Trivializing data at each cover point.
  have hloc : ∀ xc : PathCover p, ∃ e : OpenPartialHomeomorph (PathCover p) M,
      xc ∈ e.source ∧ (∀ qc ∈ e.source, e qc = pathCoverProj p qc) ∧
      e.target ⊆ (chartAt ℂ (pathCoverProj p xc)).source ∧
      chartAt ℂ xc = e ≫ₕ chartAt ℂ (pathCoverProj p xc) := by
    intro xc
    obtain ⟨h1, h2, h3⟩ :=
      Classical.choose_spec (exists_pathCover_openPartialHomeomorph p xc)
    exact ⟨Classical.choose (exists_pathCover_openPartialHomeomorph p xc), h1, h2, h3, rfl⟩
  -- Canonical lifts of downstairs points.
  have hcls : ∀ y : M, ∃ qc : PathCover p, pathCoverProj p qc = y :=
    fun y => ⟨⟨y, ⟦PathConnectedSpace.somePath p y⟧⟩, rfl⟩
  choose lift hlift using hcls
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
  -- ## The zero function and nonnegativity of envelopes.
  have hzero_memU : ∀ qc : PathCover p,
      (fun _ : PathCover p => (0 : ℝ)) ∈ greenFamily qc := by
    intro qc
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord qc) qc :=
      ((chartAt ℂ qc).continuousAt (mem_chart_source ℂ qc)).sub continuousAt_const
    have h0 : ‖poleCoord qc qc‖ < 1 := by simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have h6 : Real.log ‖poleCoord qc x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (le_of_lt hx)
    simpa using h6
  have hzero_memD : ∀ y : M, (fun _ : M => (0 : ℝ)) ∈ greenFamily y := by
    intro y
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord y) y :=
      ((chartAt ℂ y).continuousAt (mem_chart_source ℂ y)).sub continuousAt_const
    have h0 : ‖poleCoord y y‖ < 1 := by simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have h6 : Real.log ‖poleCoord y x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (le_of_lt hx)
    simpa using h6
  have henvU : ∀ (qc xc : PathCover p), 0 ≤ greenEnvelope qc xc := by
    intro qc xc
    by_cases hbb : BddAbove ((fun v => v xc) '' greenFamily qc)
    · exact le_csSup hbb ⟨_, hzero_memU qc, rfl⟩
    · have h1 : greenEnvelope qc xc = 0 := Real.sSup_of_not_bddAbove hbb
      rw [h1]
  have henvD : ∀ y : M, 0 ≤ greenEnvelope p y := by
    intro y
    by_cases hbb : BddAbove ((fun v => v y) '' greenFamily p)
    · exact le_csSup hbb ⟨_, hzero_memD p, rfl⟩
    · have h1 : greenEnvelope p y = 0 := Real.sSup_of_not_bddAbove hbb
      rw [h1]
  -- ## Hyperbolicity upstairs and the harmonic envelopes.
  have hup : ∀ qc : PathCover p, MHarmonicOn (greenEnvelope qc) {qc}ᶜ ∧
      ∀ xc, xc ≠ qc → BddAbove ((fun v => v xc) '' greenFamily qc) :=
    fun qc => mharmonicOn_greenEnvelope (hGup qc)
  obtain ⟨hgharm, -⟩ := mharmonicOn_greenEnvelope hG
  -- ## Chart transfer bricks.
  have hread : ∀ (xc : PathCover p) (f : PathCover p → ℝ) (w : M → ℝ),
      (∀ yc, w (pathCoverProj p yc) = f yc) →
      (chartAt ℂ xc xc = chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) ∧
      (f ∘ (chartAt ℂ xc).symm) =ᶠ[𝓝 (chartAt ℂ xc xc)]
        (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm) := by
    intro xc f w hdesc
    obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc xc
    have hex : e xc = pathCoverProj p xc := heq xc hmem
    have hbase : chartAt ℂ xc xc =
        chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, hex]
    refine ⟨hbase, ?_⟩
    have hcm : pathCoverProj p xc ∈ (chartAt ℂ (pathCoverProj p xc)).source :=
      mem_chart_source ℂ (pathCoverProj p xc)
    have hcont : ContinuousAt (chartAt ℂ (pathCoverProj p xc)).symm
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) :=
      (chartAt ℂ (pathCoverProj p xc)).continuousAt_symm
        ((chartAt ℂ (pathCoverProj p xc)).map_source hcm)
    have hetgt : e.target ∈ 𝓝 ((chartAt ℂ (pathCoverProj p xc)).symm
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc))) := by
      rw [(chartAt ℂ (pathCoverProj p xc)).left_inv hcm]
      refine e.open_target.mem_nhds ?_
      rw [← hex]
      exact e.map_source hmem
    have hnb : ∀ᶠ z in 𝓝 (chartAt ℂ xc xc),
        (chartAt ℂ (pathCoverProj p xc)).symm z ∈ e.target := by
      rw [hbase]
      exact hcont.eventually_mem hetgt
    filter_upwards [hnb] with z hz
    have hzs : (chartAt ℂ xc).symm z =
        e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z) := by
      rw [hch]
      rfl
    have hmem2 : e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z) ∈ e.source :=
      e.map_target hz
    calc (f ∘ (chartAt ℂ xc).symm) z
        = f (e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z)) := by
          rw [Function.comp_apply, hzs]
      _ = w (pathCoverProj p (e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z))) :=
          (hdesc _).symm
      _ = w (e (e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z))) := by
          rw [heq _ hmem2]
      _ = (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm) z := by
          rw [e.right_inv hz, Function.comp_apply]
  have hup_harm : ∀ (w : M → ℝ) (xc : PathCover p),
      MHarmonicAt w (pathCoverProj p xc) → MHarmonicAt (w ∘ pathCoverProj p) xc := by
    intro w xc hw
    obtain ⟨hbase, hev⟩ := hread xc (w ∘ pathCoverProj p) w (fun _ => rfl)
    have hw' : HarmonicAt (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm)
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) := hw
    have hgoal : HarmonicAt ((w ∘ pathCoverProj p) ∘ (chartAt ℂ xc).symm)
        (chartAt ℂ xc xc) := by
      refine (harmonicAt_congr_nhds hev).mpr ?_
      rw [hbase]
      exact hw'
    exact hgoal
  have hdown_harm : ∀ (W : PathCover p → ℝ) (w : M → ℝ) (xc : PathCover p),
      (∀ yc, w (pathCoverProj p yc) = W yc) → MHarmonicAt W xc →
      MHarmonicAt w (pathCoverProj p xc) := by
    intro W w xc hdesc hW
    obtain ⟨hbase, hev⟩ := hread xc W w hdesc
    have hW' : HarmonicAt (W ∘ (chartAt ℂ xc).symm) (chartAt ℂ xc xc) := hW
    have hgoal : HarmonicAt (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm)
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) := by
      rw [← hbase]
      exact (harmonicAt_congr_nhds hev).mp hW'
    exact hgoal
  have hsub_congr : ∀ (f g : PathCover p → ℝ) (xc : PathCover p), f =ᶠ[𝓝 xc] g →
      MSubharmonicAt f xc → MSubharmonicAt g xc := by
    intro f g xc hev hf
    obtain ⟨r, hr, hrsub, hsh⟩ := hf
    have hcont : ContinuousAt (chartAt ℂ xc).symm (chartAt ℂ xc xc) :=
      (chartAt ℂ xc).continuousAt_symm
        ((chartAt ℂ xc).map_source (mem_chart_source ℂ xc))
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ xc xc),
        f ((chartAt ℂ xc).symm z) = g ((chartAt ℂ xc).symm z) := by
      have h3 : {yc | f yc = g yc} ∈ 𝓝 ((chartAt ℂ xc).symm (chartAt ℂ xc xc)) := by
        rw [(chartAt ℂ xc).left_inv (mem_chart_source ℂ xc)]
        exact hev
      exact hcont.eventually_mem h3
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.mp h2
    refine ⟨min r r₂, lt_min hr hr₂,
      (ball_subset_ball (min_le_left _ _)).trans hrsub, ?_⟩
    refine transfer _ _ _ _ hsh (ball_subset_ball (min_le_left _ _)) ?_
    intro z hz
    exact hball₂ z (ball_subset_ball (min_le_right _ _) hz)
  have hharm_congrD : ∀ (f g : M → ℝ) (y : M), f =ᶠ[𝓝 y] g →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm
        ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
    have h2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : {z | f z = g z} ∈ 𝓝 ((chartAt ℂ y).symm (chartAt ℂ y y)) := by
        rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
        exact hev
      filter_upwards [hcont.eventually_mem h3] with z hz
      exact hz
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds h2).mp hf'
  have hpolecoord : ∀ zc : PathCover p, ∀ yc ∈ (chartAt ℂ zc).source,
      poleCoord zc yc = poleCoord (pathCoverProj p zc) (pathCoverProj p yc) := by
    intro zc yc hyc
    obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc zc
    have h1 : yc ∈ e.source := by
      rw [hch, OpenPartialHomeomorph.trans_source] at hyc
      exact hyc.1
    have h2 : chartAt ℂ zc yc =
        chartAt ℂ (pathCoverProj p zc) (pathCoverProj p yc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, heq yc h1]
    have h3 : chartAt ℂ zc zc =
        chartAt ℂ (pathCoverProj p zc) (pathCoverProj p zc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, heq zc hmem]
    simp only [poleCoord]
    rw [h2, h3]
  have hproj_tendsto : ∀ zc : PathCover p,
      Tendsto (pathCoverProj p) (𝓝[≠] zc) (𝓝[≠] (pathCoverProj p zc)) := by
    intro zc
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (hproj_cont.tendsto zc).mono_left nhdsWithin_le_nhds
    · obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc zc
      have h2 : ∀ᶠ yc in 𝓝 zc, yc ∈ e.source := e.open_source.mem_nhds hmem
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h2] with yc h3 h4
      have h5 : yc ≠ zc := h4
      have h6 : pathCoverProj p yc ≠ pathCoverProj p zc := by
        intro hcon
        apply h5
        refine e.injOn h3 hmem ?_
        rw [heq yc h3, heq zc hmem]
        exact hcon
      exact h6
  -- ## The pole behaviour of the envelope downstairs at `p`.
  obtain ⟨B₀, hgp_lower, hgp_large⟩ : ∃ B₀ : ℝ,
      (∀ᶠ y in 𝓝[≠] p, -Real.log ‖poleCoord p y‖ - B₀ ≤ greenEnvelope p y) ∧
      (∀ᶠ y in 𝓝[≠] p, 1 ≤ greenEnvelope p y) := by
    obtain ⟨r₀, hr₀, -, h₀, hh₀harm, hh₀eq⟩ := exists_harmonic_pole_extension hG
    have hc₀ : ContinuousAt h₀ (chartAt ℂ p p) :=
      (hh₀harm _ (mem_ball_self hr₀)).1.continuousAt
    set B₀ : ℝ := |h₀ (chartAt ℂ p p)| + 1 with hB₀def
    have hB₀ : ∀ᶠ w in 𝓝 (chartAt ℂ p p), |h₀ w| ≤ B₀ := by
      have h1 := hc₀ (Metric.ball_mem_nhds (h₀ (chartAt ℂ p p)) one_pos)
      filter_upwards [h1] with w hw
      have h2 : |h₀ w - h₀ (chartAt ℂ p p)| < 1 := by
        simpa [Real.dist_eq] using hw
      have h3 := abs_sub_abs_le_abs_sub (h₀ w) (h₀ (chartAt ℂ p p))
      rw [hB₀def]
      linarith
    have hcp : ContinuousAt (chartAt ℂ p) p :=
      (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
    have hev_src : ∀ᶠ y in 𝓝[≠] p, y ∈ (chartAt ℂ p).source :=
      nhdsWithin_le_nhds
        ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hev_ball : ∀ᶠ y in 𝓝[≠] p,
        chartAt ℂ p y ∈ ball (chartAt ℂ p p) r₀ ∧ |h₀ (chartAt ℂ p y)| ≤ B₀ := by
      have h0 : ∀ᶠ w in 𝓝 (chartAt ℂ p p), w ∈ ball (chartAt ℂ p p) r₀ :=
        isOpen_ball.eventually_mem (mem_ball_self hr₀)
      have h1 : ∀ᶠ w in 𝓝 (chartAt ℂ p p),
          w ∈ ball (chartAt ℂ p p) r₀ ∧ |h₀ w| ≤ B₀ := h0.and hB₀
      exact nhdsWithin_le_nhds (hcp.eventually_mem h1)
    have hg_repr' : ∀ᶠ y in 𝓝[≠] p,
        greenEnvelope p y = h₀ (chartAt ℂ p y) - Real.log ‖poleCoord p y‖ := by
      filter_upwards [hev_src, hev_ball, self_mem_nhdsWithin] with y h1 h2 h3
      have hyne : y ≠ p := h3
      have hne0 : chartAt ℂ p y ≠ chartAt ℂ p p := by
        intro hcon
        exact hyne ((chartAt ℂ p).injOn h1 (mem_chart_source ℂ p) hcon)
      have hmem2 : chartAt ℂ p y ∈ ball (chartAt ℂ p p) r₀ \ {chartAt ℂ p p} :=
        ⟨h2.1, hne0⟩
      have h4 := hh₀eq _ hmem2
      rw [(chartAt ℂ p).left_inv h1] at h4
      have h5 : Real.log ‖chartAt ℂ p y - chartAt ℂ p p‖ =
          Real.log ‖poleCoord p y‖ := rfl
      rw [h5] at h4
      linarith
    have hpc0 : ContinuousAt (fun y => ‖poleCoord p y‖) p := by
      have h1 : ContinuousAt (poleCoord p) p :=
        ((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)).sub continuousAt_const
      exact h1.norm
    have hpc0v : ‖poleCoord p p‖ = 0 := by simp [poleCoord]
    have hev_small : ∀ᶠ y in 𝓝[≠] p,
        ‖poleCoord p y‖ < Real.exp (-(B₀ + 1)) ∧ 0 < ‖poleCoord p y‖ := by
      have h1 : ∀ᶠ y in 𝓝 p, ‖poleCoord p y‖ < Real.exp (-(B₀ + 1)) := by
        refine hpc0.eventually_lt_const ?_
        change ‖poleCoord p p‖ < Real.exp (-(B₀ + 1))
        rw [hpc0v]
        positivity
      filter_upwards [nhdsWithin_le_nhds h1, hev_src, self_mem_nhdsWithin]
        with y h2 h3 h4
      refine ⟨h2, ?_⟩
      have hyne : y ≠ p := h4
      have hne0 : poleCoord p y ≠ 0 := by
        intro hcon
        apply hyne
        refine (chartAt ℂ p).injOn h3 (mem_chart_source ℂ p) ?_
        have h6 : chartAt ℂ p y - chartAt ℂ p p = 0 := hcon
        linear_combination (norm := module) h6
      exact norm_pos_iff.mpr hne0
    refine ⟨B₀, ?_, ?_⟩
    · filter_upwards [hg_repr', hev_ball] with y h1 h2
      have h3 := (abs_le.mp h2.2).1
      rw [h1]
      linarith
    · filter_upwards [hg_repr', hev_ball, hev_small] with y h1 h2 h3
      have h4 := (abs_le.mp h2.2).1
      have h5 : Real.log ‖poleCoord p y‖ < -(B₀ + 1) :=
        (Real.log_lt_iff_lt_exp h3.2).mpr h3.1
      rw [h1]
      linarith
  -- ## Sums of subharmonic and harmonic functions on the cover.
  have hplane_add : ∀ (f g : ℂ → ℝ) (U : Set ℂ), SubharmonicOn f U → SubharmonicOn g U →
      SubharmonicOn (fun z => f z + g z) U := by
    intro f g U hf hg
    refine ⟨fun x hx => (hf.1 x hx).add (hg.1 x hx), ?_⟩
    intro c hc r hr hsub
    have hsphere : Metric.sphere c r ⊆ U :=
      Metric.sphere_subset_closedBall.trans hsub
    have hfci : CircleIntegrable f c r := (hf.1.mono hsphere).circleIntegrable hr.le
    have hgci : CircleIntegrable g c r := (hg.1.mono hsphere).circleIntegrable hr.le
    have hadd : Real.circleAverage (fun z => f z + g z) c r =
        Real.circleAverage f c r + Real.circleAverage g c r :=
      Real.circleAverage_fun_add hfci hgci
    rw [hadd]
    exact add_le_add (hf.2 c hc r hr hsub) (hg.2 c hc r hr hsub)
  have hmsub_add : ∀ (f g : PathCover p → ℝ) (xc : PathCover p), MSubharmonicAt f xc →
      MSubharmonicAt g xc → MSubharmonicAt (fun yc => f yc + g yc) xc := by
    intro f g xc hf hg
    obtain ⟨r₁, hr₁, hb₁, hs₁⟩ := hf
    obtain ⟨r₂, hr₂, -, hs₂⟩ := hg
    have hmono : ∀ (F : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn F U → V ⊆ U →
        SubharmonicOn F V := fun F U V hF hVU =>
      ⟨hF.1.mono hVU, fun c hc ρ hρ hball => hF.2 c (hVU hc) ρ hρ (hball.trans hVU)⟩
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (ball_subset_ball (min_le_left r₁ r₂)).trans hb₁, ?_⟩
    exact hplane_add _ _ _
      (hmono _ _ _ hs₁ (ball_subset_ball (min_le_left r₁ r₂)))
      (hmono _ _ _ hs₂ (ball_subset_ball (min_le_right r₁ r₂)))
  have hmsub_sum : ∀ (y : M) (w : {qc : PathCover p // pathCoverProj p qc = y} →
      PathCover p → ℝ) (G : Finset {qc : PathCover p // pathCoverProj p qc = y})
      (xc : PathCover p), (∀ j ∈ G, MSubharmonicAt (w j) xc) →
      MSubharmonicAt (fun yc => ∑ j ∈ G, w j yc) xc := by
    intro y w G
    induction G using Finset.cons_induction with
    | empty =>
      intro xc _
      have h0 : (fun yc : PathCover p => ∑ j ∈ (∅ : Finset
          {qc : PathCover p // pathCoverProj p qc = y}), w j yc) =
          fun _ => (0 : ℝ) := by
        funext yc
        simp
      rw [h0]
      exact mharmonicAt_const.msubharmonicAt
    | cons a G' ha IH =>
      intro xc hall
      have h1 : (fun yc : PathCover p => ∑ j ∈ Finset.cons a G' ha, w j yc) =
          fun yc => w a yc + ∑ j ∈ G', w j yc := by
        funext yc
        rw [Finset.sum_cons]
      rw [h1]
      exact hmsub_add _ _ xc (hall a (Finset.mem_cons_self a G'))
        (IH xc fun j hj => hall j (Finset.mem_cons_of_mem hj))
  have hmharm_sum : ∀ (y : M) (G : Finset {qc : PathCover p // pathCoverProj p qc = y})
      (xc : PathCover p), (∀ j ∈ G, MHarmonicAt (greenEnvelope j.1) xc) →
      MHarmonicAt (fun yc => ∑ j ∈ G, greenEnvelope j.1 yc) xc := by
    intro y G
    induction G using Finset.cons_induction with
    | empty =>
      intro xc _
      have h0 : (fun yc : PathCover p => ∑ j ∈ (∅ : Finset
          {qc : PathCover p // pathCoverProj p qc = y}), greenEnvelope j.1 yc) =
          fun _ => (0 : ℝ) := by
        funext yc
        simp
      rw [h0]
      exact mharmonicAt_const
    | cons a G' ha IH =>
      intro xc hall
      have h1 : (fun yc : PathCover p => ∑ j ∈ Finset.cons a G' ha, greenEnvelope j.1 yc) =
          fun yc => greenEnvelope a.1 yc + ∑ j ∈ G', greenEnvelope j.1 yc := by
        funext yc
        rw [Finset.sum_cons]
      rw [h1]
      exact MHarmonicAt.add (hall a (Finset.mem_cons_self a G'))
        (IH xc fun j hj => hall j (Finset.mem_cons_of_mem hj))
  -- ## Finite `p`-fiber sums are dominated by the pulled-back envelope at `p`.
  have hpart1p : ∀ (F : Finset {qc : PathCover p // pathCoverProj p qc = p})
      (xc : PathCover p), pathCoverProj p xc ≠ p →
      (∑ j ∈ F, greenEnvelope j.1 xc) ≤ greenEnvelope p (pathCoverProj p xc) := by
    intro F xc hxc
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hεn : (0 : ℝ) < ε / (F.card + 1) := by positivity
    have hex : ∀ j : {qc : PathCover p // pathCoverProj p qc = p},
        ∃ v : PathCover p → ℝ, v ∈ greenFamily j.1 ∧
          greenEnvelope j.1 xc - ε / (F.card + 1) < v xc := by
      intro j
      have hne_im : ((fun v => v xc) '' greenFamily j.1).Nonempty :=
        ⟨0, ⟨fun _ => 0, hzero_memU j.1, rfl⟩⟩
      have hlt : greenEnvelope j.1 xc - ε / (F.card + 1) <
          sSup ((fun v => v xc) '' greenFamily j.1) := sub_lt_self _ hεn
      obtain ⟨b, hbmem, hb⟩ := exists_lt_of_lt_csSup hne_im hlt
      obtain ⟨v, hv, rfl⟩ := hbmem
      exact ⟨v, hv, hb⟩
    choose v hv hvx using hex
    have hvsub : ∀ j, MSubharmonicOn (v j) {j.1}ᶜ := fun j => (hv j).1
    have hvcont : ∀ j, ContinuousOn (v j) {j.1}ᶜ := fun j => (hv j).2.1
    choose K hKc hKne hKz using fun j => (hv j).2.2.1
    choose Cj hCj using fun j => (hv j).2.2.2
    set Khat : Set (PathCover p) := ⋃ j ∈ F, K j with hKhatdef
    have hKhatc : IsCompact Khat := F.isCompact_biUnion fun j _ => hKc j
    have hKhatcl : IsClosed Khat := hKhatc.isClosed
    have hfibK : (pathCoverProj p ⁻¹' {p} ∩ Khat).Finite :=
      finite_fiber_inter_compact p hKhatc p
    set F' : Finset (PathCover p) := F.image Subtype.val ∪ hfibK.toFinset with hF'def
    have hF'fib : ∀ zc ∈ F', pathCoverProj p zc = p := by
      intro zc hzc
      rw [hF'def, Finset.mem_union] at hzc
      rcases hzc with h | h
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
        exact j.2
      · exact ((Set.Finite.mem_toFinset hfibK).mp h).1
    set G₁ : M → ℝ := fun y => if y = p then 1 else greenEnvelope p y with hG₁def
    have hG₁eq : ∀ y, y ≠ p → G₁ y = greenEnvelope p y := by
      intro y hy
      simp only [hG₁def]
      rw [ite_eq_right hy]
    have hG₁nonneg : ∀ y, 0 ≤ G₁ y := by
      intro y
      by_cases hy : y = p
      · simp only [hG₁def]
        rw [ite_eq_left hy]
        norm_num
      · rw [hG₁eq y hy]
        exact henvD y
    have hG₁one : ∀ᶠ y in 𝓝 p, 1 ≤ G₁ y := by
      have h1 := eventually_nhdsWithin_iff.mp hgp_large
      filter_upwards [h1] with y hy
      by_cases hyp : y = p
      · simp only [hG₁def]
        rw [ite_eq_left hyp]
      · rw [hG₁eq y hyp]
        exact hy hyp
    have hG₁harm : ∀ y, y ≠ p → MHarmonicAt G₁ y := by
      intro y hy
      have hev : greenEnvelope p =ᶠ[𝓝 y] G₁ := by
        have h1 : ({p}ᶜ : Set M) ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds hy
        filter_upwards [h1] with z hz
        exact (hG₁eq z hz).symm
      exact hharm_congrD _ _ y hev (hgharm y hy)
    obtain ⟨O₀, hO₀p, hO₀open, hO₀mem⟩ := eventually_nhds_iff.mp hG₁one
    set wt : PathCover p → ℝ :=
      fun yc => max ((∑ j ∈ F, v j yc) - G₁ (pathCoverProj p yc)) (-1) with hwtdef
    have hwsub : MSubharmonicOn wt ((↑F' : Set (PathCover p)))ᶜ := by
      intro yc hyc
      by_cases hproj : pathCoverProj p yc = p
      · have hycK : yc ∉ Khat := by
          intro hK
          apply hyc
          rw [Finset.mem_coe, hF'def, Finset.mem_union]
          right
          rw [Set.Finite.mem_toFinset]
          exact ⟨hproj, hK⟩
        have hnb : ∀ᶠ zc in 𝓝 yc, wt zc = -1 := by
          have h1 : IsOpen (Khatᶜ ∩ pathCoverProj p ⁻¹' O₀) :=
            hKhatcl.isOpen_compl.inter (hO₀open.preimage hproj_cont)
          have h2 : yc ∈ Khatᶜ ∩ pathCoverProj p ⁻¹' O₀ := by
            refine ⟨hycK, ?_⟩
            rw [Set.mem_preimage, hproj]
            exact hO₀mem
          filter_upwards [h1.eventually_mem h2] with zc hzc
          have hsum0 : (∑ j ∈ F, v j zc) = 0 := Finset.sum_eq_zero fun j hj =>
            hKz j zc fun hK => hzc.1 (Set.mem_biUnion hj hK)
          have hG1 : 1 ≤ G₁ (pathCoverProj p zc) := hO₀p _ hzc.2
          simp only [hwtdef]
          rw [hsum0, max_eq_right (by linarith)]
        have hconst : MSubharmonicAt (fun _ : PathCover p => (-1 : ℝ)) yc :=
          mharmonicAt_const.msubharmonicAt
        refine hsub_congr _ _ yc ?_ hconst
        filter_upwards [hnb] with zc h
        exact h.symm
      · have hsum_sub : MSubharmonicAt (fun zc => ∑ j ∈ F, v j zc) yc :=
          hmsub_sum p v F yc fun j hj => hvsub j yc
            (fun h => hproj (by rw [h]; exact j.2))
        have hGproj : MHarmonicAt (G₁ ∘ pathCoverProj p) yc :=
          hup_harm G₁ yc (hG₁harm _ hproj)
        have hconst : MSubharmonicAt (fun _ : PathCover p => (-1 : ℝ)) yc :=
          mharmonicAt_const.msubharmonicAt
        have hmax := (hsum_sub.sub_mharmonicAt hGproj).max hconst
        simp only [hwtdef]
        exact hmax
    have hsupp : ∀ zc, zc ∉ Khat → wt zc ≤ 0 := by
      intro zc hzc
      have hsum0 : (∑ j ∈ F, v j zc) = 0 := Finset.sum_eq_zero fun j hj =>
        hKz j zc fun hK => hzc (Set.mem_biUnion hj hK)
      have h1 := hG₁nonneg (pathCoverProj p zc)
      simp only [hwtdef]
      rw [hsum0]
      exact max_le (by linarith) (by norm_num)
    have hpole : ∀ zc ∈ F', ∃ C, ∀ᶠ yc in 𝓝[≠] zc, wt yc ≤ C := by
      intro zc hzc
      have hzcp : pathCoverProj p zc = p := hF'fib zc hzc
      have hG₁log : ∀ᶠ yc in 𝓝[≠] zc,
          -G₁ (pathCoverProj p yc) ≤ Real.log ‖poleCoord zc yc‖ + B₀ := by
        have h1 : ∀ᶠ y in 𝓝[≠] p, -Real.log ‖poleCoord p y‖ - B₀ ≤ G₁ y := by
          filter_upwards [hgp_lower, self_mem_nhdsWithin] with y h2 h3
          rw [hG₁eq y h3]
          exact h2
        have hpcev : ∀ᶠ yc in 𝓝[≠] zc,
            poleCoord zc yc = poleCoord p (pathCoverProj p yc) := by
          have h4 : ∀ᶠ yc in 𝓝 zc, yc ∈ (chartAt ℂ zc).source :=
            (chartAt ℂ zc).open_source.eventually_mem (mem_chart_source ℂ zc)
          filter_upwards [nhdsWithin_le_nhds h4] with yc h5
          have h6 := hpolecoord zc yc h5
          rw [hzcp] at h6
          exact h6
        have htz := hproj_tendsto zc
        rw [hzcp] at htz
        filter_upwards [htz.eventually h1, hpcev] with yc h2 h3
        rw [h3]
        linarith
      by_cases hzF : ∃ j ∈ F, j.1 = zc
      · obtain ⟨j₀, hj₀F, hj₀⟩ := hzF
        have hhead : ∀ᶠ yc in 𝓝[≠] zc,
            v j₀ yc ≤ Cj j₀ - Real.log ‖poleCoord zc yc‖ := by
          have h1 := hCj j₀
          rw [hj₀] at h1
          filter_upwards [h1] with yc h2
          linarith
        have hrest : ∀ᶠ yc in 𝓝[≠] zc, ∀ j ∈ F.erase j₀,
            v j yc ≤ v j zc + 1 := by
          rw [eventually_all_finset]
          intro j hj
          have hjne : j.1 ≠ zc := by
            intro hcon
            exact (Finset.mem_erase.mp hj).1 (Subtype.ext (by rw [hcon, hj₀]))
          have hcont : ContinuousAt (v j) zc :=
            (hvcont j).continuousAt (isOpen_compl_singleton.mem_nhds
              fun h => hjne (id (Eq.symm h)))
          have h3 : ∀ᶠ yc in 𝓝 zc, v j yc < v j zc + 1 :=
            hcont.eventually_lt_const (lt_add_one _)
          exact nhdsWithin_le_nhds (h3.mono fun yc h => h.le)
        refine ⟨max (Cj j₀ + (∑ j ∈ F.erase j₀, (v j zc + 1)) + B₀) (-1), ?_⟩
        filter_upwards [hhead, hrest, hG₁log] with yc h1 h2 h3
        have hsplit : (∑ j ∈ F, v j yc) = v j₀ yc + ∑ j ∈ F.erase j₀, v j yc :=
          (Finset.add_sum_erase F (fun j => v j yc) hj₀F).symm
        have h4 : (∑ j ∈ F.erase j₀, v j yc) ≤ ∑ j ∈ F.erase j₀, (v j zc + 1) :=
          Finset.sum_le_sum h2
        simp only [hwtdef]
        refine max_le ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_left _ _)
        rw [hsplit]
        linarith
      · have hall : ∀ᶠ yc in 𝓝[≠] zc, ∀ j ∈ F, v j yc ≤ v j zc + 1 := by
          rw [eventually_all_finset]
          intro j hj
          have hjne : j.1 ≠ zc := fun hcon => hzF ⟨j, hj, hcon⟩
          have hcont : ContinuousAt (v j) zc :=
            (hvcont j).continuousAt (isOpen_compl_singleton.mem_nhds
              fun h => hjne (id (Eq.symm h)))
          have h3 : ∀ᶠ yc in 𝓝 zc, v j yc < v j zc + 1 :=
            hcont.eventually_lt_const (lt_add_one _)
          exact nhdsWithin_le_nhds (h3.mono fun yc h => h.le)
        refine ⟨max (∑ j ∈ F, (v j zc + 1)) (-1), ?_⟩
        filter_upwards [hall] with yc h1
        have h2 : (∑ j ∈ F, v j yc) ≤ ∑ j ∈ F, (v j zc + 1) := Finset.sum_le_sum h1
        have h3 := hG₁nonneg (pathCoverProj p yc)
        simp only [hwtdef]
        refine max_le ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_left _ _)
        linarith
    have hle := msubharmonic_le_zero_of_finite_punctures (F := F') hwsub
      ⟨Khat, hKhatc, hsupp⟩ hpole
    have hxcF' : xc ∉ F' := fun h => hxc (hF'fib xc h)
    have h1 : wt xc ≤ 0 := hle xc hxcF'
    simp only [hwtdef] at h1
    have h2 : (∑ j ∈ F, v j xc) - G₁ (pathCoverProj p xc) ≤ 0 :=
      le_trans (le_max_left _ _) h1
    have h3 : (∑ j ∈ F, v j xc) ≤ greenEnvelope p (pathCoverProj p xc) := by
      rw [← hG₁eq _ hxc]
      linarith
    have h4 : (∑ j ∈ F, (greenEnvelope j.1 xc - ε / (F.card + 1))) ≤
        ∑ j ∈ F, v j xc := Finset.sum_le_sum fun j _ => (hvx j).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h4
    have h5 : (F.card : ℝ) * (ε / (F.card + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (Nat.cast_add_one_pos F.card)]
      nlinarith [hε.le]
    linarith
  -- ## Groupoid algebra of the deck action.
  have hdeck_comp : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ (pathCoverDeck p δ pc) = pathCoverDeck p (γ.trans δ) pc := by
    intro γ δ pc
    change (⟨pc.pt, γ.trans (δ.trans pc.cls)⟩ : PathCover p)
      = ⟨pc.pt, (γ.trans δ).trans pc.cls⟩
    exact congrArg (PathCover.mk pc.pt)
      (Path.Homotopic.Quotient.trans_assoc γ δ pc.cls).symm
  have hdeck_refl : ∀ pc : PathCover p,
      pathCoverDeck p (Path.Homotopic.Quotient.refl p) pc = pc := by
    intro pc
    change (⟨pc.pt, (Path.Homotopic.Quotient.refl p).trans pc.cls⟩ : PathCover p) = pc
    exact congrArg (PathCover.mk pc.pt) (Path.Homotopic.Quotient.refl_trans pc.cls)
  have hdeck_free : ∀ (δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p δ pc = pc → δ = Path.Homotopic.Quotient.refl p := by
    intro δ pc h
    have h' : (⟨pc.pt, δ.trans pc.cls⟩ : PathCover p) = ⟨pc.pt, pc.cls⟩ := h
    rw [PathCover.mk.injEq] at h'
    have h1 : δ.trans pc.cls = pc.cls := eq_of_heq h'.2
    calc δ = δ.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl δ).symm
      _ = δ.trans (pc.cls.trans pc.cls.symm) := by
          rw [Path.Homotopic.Quotient.trans_symm]
      _ = (δ.trans pc.cls).trans pc.cls.symm :=
          (Path.Homotopic.Quotient.trans_assoc δ pc.cls pc.cls.symm).symm
      _ = pc.cls.trans pc.cls.symm := by rw [h1]
      _ = Path.Homotopic.Quotient.refl p := Path.Homotopic.Quotient.trans_symm pc.cls
  have hdeck_inj : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ pc = pathCoverDeck p δ pc → γ = δ := by
    intro γ δ pc h
    have h2 : pathCoverDeck p (δ.symm.trans γ) pc = pc := by
      rw [← hdeck_comp, h, hdeck_comp, Path.Homotopic.Quotient.symm_trans, hdeck_refl]
    have h3 := hdeck_free _ _ h2
    calc γ = (Path.Homotopic.Quotient.refl p).trans γ :=
          (Path.Homotopic.Quotient.refl_trans γ).symm
      _ = (δ.trans δ.symm).trans γ := by rw [Path.Homotopic.Quotient.trans_symm]
      _ = δ.trans (δ.symm.trans γ) := Path.Homotopic.Quotient.trans_assoc δ δ.symm γ
      _ = δ.trans (Path.Homotopic.Quotient.refl p) := by rw [h3]
      _ = δ := Path.Homotopic.Quotient.trans_refl δ
  have hsymm_symm : ∀ γ : Path.Homotopic.Quotient p p, γ.symm.symm = γ := by
    intro γ
    calc γ.symm.symm = γ.symm.symm.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl γ.symm.symm).symm
      _ = γ.symm.symm.trans (γ.symm.trans γ) := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = (γ.symm.symm.trans γ.symm).trans γ :=
          (Path.Homotopic.Quotient.trans_assoc γ.symm.symm γ.symm γ).symm
      _ = (Path.Homotopic.Quotient.refl p).trans γ := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = γ := Path.Homotopic.Quotient.refl_trans γ
  -- ## Choices: fiber loops and deck diffeomorphisms.
  have hfibA : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      ∃ γ : Path.Homotopic.Quotient p p, pathCoverDeck p γ pb = a.1 := fun a =>
    pathCoverDeck_transitive p pb a.1 (hpb_proj.trans a.2.symm)
  choose γfn hγfn using hfibA
  choose Efn hEfn using fun γ : Path.Homotopic.Quotient p p =>
    exists_pathCoverDeck_diffeomorph p γ
  -- ## The fiber reindexing map: conjugate `p`-fiber points into the `q`-fiber.
  obtain ⟨Φ, hΦspec⟩ : ∃ Φ : {qc : PathCover p // pathCoverProj p qc = p} →
      {qc : PathCover p // pathCoverProj p qc = q},
      ∀ a, (Φ a).1 = pathCoverDeck p (γfn a).symm qb :=
    ⟨fun a => ⟨pathCoverDeck p (γfn a).symm qb,
      (pathCoverProj_deck p (γfn a).symm qb).trans hqb_proj⟩, fun _ => rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro a₁ a₂ h
    have h1 : pathCoverDeck p (γfn a₁).symm qb = pathCoverDeck p (γfn a₂).symm qb := by
      rw [← hΦspec a₁, ← hΦspec a₂, h]
    have h2 : (γfn a₁).symm = (γfn a₂).symm := hdeck_inj _ _ _ h1
    have h3 : γfn a₁ = γfn a₂ := by
      rw [← hsymm_symm (γfn a₁), h2, hsymm_symm]
    apply Subtype.ext
    rw [← hγfn a₁, ← hγfn a₂, h3]
  have hΦsurj : Function.Surjective Φ := by
    intro b
    obtain ⟨δ, hδ⟩ := pathCoverDeck_transitive p qb b.1 (hqb_proj.trans b.2.symm)
    have hmem : pathCoverProj p (pathCoverDeck p δ.symm pb) = p :=
      (pathCoverProj_deck p δ.symm pb).trans hpb_proj
    refine ⟨⟨pathCoverDeck p δ.symm pb, hmem⟩, ?_⟩
    have hloop : γfn ⟨pathCoverDeck p δ.symm pb, hmem⟩ = δ.symm := by
      apply hdeck_inj _ _ pb
      exact hγfn ⟨pathCoverDeck p δ.symm pb, hmem⟩
    apply Subtype.ext
    rw [hΦspec, hloop, hsymm_symm, hδ]
  obtain ⟨e, he⟩ : ∃ e : {qc : PathCover p // pathCoverProj p qc = p} ≃
      {qc : PathCover p // pathCoverProj p qc = q}, ∀ a, e a = Φ a :=
    ⟨Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩, fun _ => rfl⟩
  -- ## Termwise symmetry: cover symmetry plus conformal invariance of the deck maps.
  have hterm : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      greenEnvelope a.1 qb = greenEnvelope (pathCoverDeck p (γfn a).symm qb) pb := by
    intro a
    have hne : a.1 ≠ qb := by
      intro h
      apply hpq
      rw [← a.2, h, hqb_proj]
    have h1 : greenEnvelope a.1 qb = greenEnvelope qb a.1 :=
      greenEnvelope_symm_of_simplyConnected (hGup a.1) hne
    have hEpb : Efn (γfn a) pb = a.1 := (hEfn (γfn a) pb).trans (hγfn a)
    have hEsymm_a : (Efn (γfn a)).symm a.1 = pb := by
      rw [← hEpb, Diffeomorph.symm_apply_apply]
    have h2 : Efn (γfn a) (pathCoverDeck p (γfn a).symm qb) = qb := by
      rw [hEfn (γfn a) (pathCoverDeck p (γfn a).symm qb), hdeck_comp,
        Path.Homotopic.Quotient.trans_symm, hdeck_refl]
    have hEsymm_q : (Efn (γfn a)).symm qb = pathCoverDeck p (γfn a).symm qb := by
      calc (Efn (γfn a)).symm qb
          = (Efn (γfn a)).symm (Efn (γfn a) (pathCoverDeck p (γfn a).symm qb)) := by
            rw [h2]
        _ = pathCoverDeck p (γfn a).symm qb := Diffeomorph.symm_apply_apply _ _
    have h3 : greenEnvelope ((Efn (γfn a)).symm qb) ((Efn (γfn a)).symm a.1)
        = greenEnvelope qb a.1 :=
      greenEnvelope_comp_diffeomorph (Efn (γfn a)).symm qb a.1
    rw [h1, ← h3, hEsymm_a, hEsymm_q]
  -- ## Reindexing of the `p`-fiber sums at `qb` into `q`-fiber sums at `pb`.
  have hFeq : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
      (∑ a ∈ F, greenEnvelope a.1 qb)
        = ∑ s ∈ e.finsetCongr F, greenEnvelope s.1 pb := by
    intro F
    rw [Equiv.finsetCongr_apply, Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [he a, hΦspec a]
    exact hterm a
  -- ## KEY BOUND: the `q`-fiber finite sums at the base lift are bounded.
  have hbdd_pb : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
      (∑ s ∈ F, greenEnvelope s.1 pb) ≤ greenEnvelope p q := by
    intro F
    have h1 := hFeq (e.finsetCongr.symm F)
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1]
    have h3 := hpart1p (e.finsetCongr.symm F) qb (by rw [hqb_proj]; exact Ne.symm hpq)
    rw [hqb_proj] at h3
    exact h3
  -- ## The `q`-fiber finite sums are harmonic off the `q`-fiber.
  have huq : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
      MHarmonicOn (fun xc => ∑ s ∈ F, greenEnvelope s.1 xc)
        (pathCoverProj p ⁻¹' {q})ᶜ := by
    intro F xc hxc
    have hxcp : pathCoverProj p xc ≠ q := by
      simpa [Set.mem_preimage] using hxc
    exact hmharm_sum q F xc fun j _ =>
      (hup j.1).1 xc (fun h => hxcp (by rw [h]; exact j.2))
  -- ## Local two-sided Harnack comparison for the `q`-fiber sums.
  have hlocH : ∀ xc : PathCover p, pathCoverProj p xc ≠ q →
      ∃ U : Set (PathCover p), IsOpen U ∧ xc ∈ U ∧
        (∀ yc ∈ U, pathCoverProj p yc ≠ q) ∧
        ∀ yc ∈ U, ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          (∑ s ∈ F, greenEnvelope s.1 yc) ≤ 3 * ∑ s ∈ F, greenEnvelope s.1 xc ∧
          (∑ s ∈ F, greenEnvelope s.1 xc) ≤ 3 * ∑ s ∈ F, greenEnvelope s.1 yc := by
    intro xc hxc
    set e₀ := chartAt ℂ xc with he₀def
    have hxsrc : xc ∈ e₀.source := mem_chart_source ℂ xc
    have hxcΩ : xc ∈ ((pathCoverProj p ⁻¹' {q})ᶜ : Set (PathCover p)) := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact hxc
    have hopen2 : IsOpen (e₀.target ∩ e₀.symm ⁻¹' (pathCoverProj p ⁻¹' {q})ᶜ) :=
      e₀.isOpen_inter_preimage_symm hΩopen
    have hmem2 : e₀ xc ∈ e₀.target ∩ e₀.symm ⁻¹' (pathCoverProj p ⁻¹' {q})ᶜ := by
      refine ⟨e₀.map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, e₀.left_inv hxsrc]
      exact hxcΩ
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    set r := ε / 4 with hrdef
    have hr0 : 0 < r := by rw [hrdef]; linarith
    have h2r : ball (e₀ xc) (2 * r) ⊆
        e₀.target ∩ e₀.symm ⁻¹' (pathCoverProj p ⁻¹' {q})ᶜ :=
      (ball_subset_ball (by rw [hrdef]; linarith)).trans hball
    have hread2 : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        HarmonicOnNhd ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘ ⇑e₀.symm)
          (ball (e₀ xc) (2 * r)) := by
      intro F w hw
      have hwt : w ∈ e₀.target := (h2r hw).1
      have hwΩ : e₀.symm w ∈ ((pathCoverProj p ⁻¹' {q})ᶜ : Set (PathCover p)) :=
        (h2r hw).2
      have hyy : e₀.symm w ∈ (chartAt ℂ (e₀.symm w)).source :=
        mem_chart_source ℂ (e₀.symm w)
      have htrans2 : AnalyticAt ℂ (⇑(chartAt ℂ (e₀.symm w)) ∘ ⇑e₀.symm) w := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e₀.symm) w :=
          contMDiffAt_symm_of_mem_maximalAtlas
            (IsManifold.chart_mem_maximalAtlas xc) hwt
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (e₀.symm w))) (e₀.symm w) :=
          contMDiffAt_of_mem_maximalAtlas
            (IsManifold.chart_mem_maximalAtlas (e₀.symm w)) hyy
        exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
      have hmh : HarmonicAt ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘
          ⇑(chartAt ℂ (e₀.symm w)).symm) ((⇑(chartAt ℂ (e₀.symm w)) ∘ ⇑e₀.symm) w) :=
        huq F (e₀.symm w) hwΩ
      have hcomp := harmonicAt_comp_analyticAt hmh htrans2
      have hev : ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘
          ⇑(chartAt ℂ (e₀.symm w)).symm) ∘ (⇑(chartAt ℂ (e₀.symm w)) ∘ ⇑e₀.symm)
          =ᶠ[𝓝 w] (fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘ ⇑e₀.symm := by
        have hS : IsOpen (e₀.target ∩ ⇑e₀.symm ⁻¹' (chartAt ℂ (e₀.symm w)).source) :=
          e₀.continuousOn_symm.isOpen_inter_preimage e₀.open_target
            (chartAt ℂ (e₀.symm w)).open_source
        filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with z hz
        simp only [Function.comp_apply]
        rw [(chartAt ℂ (e₀.symm w)).left_inv hz.2]
      exact (harmonicAt_congr_nhds hev).mp hcomp
    have hpos2 : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∀ z ∈ ball (e₀ xc) (2 * r),
          0 ≤ ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘ ⇑e₀.symm) z := by
      intro F z _
      exact Finset.sum_nonneg fun j _ => henvU j.1 (e₀.symm z)
    have hcx : e₀.symm (e₀ xc) = xc := e₀.left_inv hxsrc
    refine ⟨e₀.source ∩ ⇑e₀ ⁻¹' ball (e₀ xc) r,
      e₀.continuousOn.isOpen_inter_preimage e₀.open_source isOpen_ball,
      ⟨hxsrc, mem_ball_self hr0⟩, ?_, ?_⟩
    · intro yc hy
      have h1 : e₀ yc ∈ ball (e₀ xc) (2 * r) :=
        ball_subset_ball (by rw [hrdef]; linarith) hy.2
      have h2 := (h2r h1).2
      rw [Set.mem_preimage, e₀.left_inv hy.1] at h2
      simpa [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] using h2
    · intro yc hy F
      obtain ⟨hlow, hup2⟩ :=
        harnack_inequality_ball hr0 (hread2 F) (hpos2 F) (e₀ yc) hy.2
      have hcy : e₀.symm (e₀ yc) = yc := e₀.left_inv hy.1
      simp only [Function.comp_apply, hcx, hcy] at hlow hup2
      exact ⟨hup2, by linarith⟩
  -- ## Deck invariance of the `q`-fiber sum ranges along a fiber.
  have hrange_fib : ∀ xc yc : PathCover p,
      pathCoverProj p xc = pathCoverProj p yc →
      (Set.range fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 yc) =
      Set.range fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 xc := by
    intro xc yc hxy
    obtain ⟨γ, hγ⟩ := pathCoverDeck_transitive p xc yc hxy
    obtain ⟨E, hE⟩ := exists_pathCoverDeck_diffeomorph p γ
    have hprojE : ∀ zc, pathCoverProj p (E zc) = pathCoverProj p zc := by
      intro zc
      rw [hE zc]
      exact pathCoverProj_deck p γ zc
    have hprojEsymm : ∀ zc, pathCoverProj p (E.symm zc) = pathCoverProj p zc := by
      intro zc
      have h1 := hprojE (E.symm zc)
      rw [E.apply_symm_apply] at h1
      exact h1.symm
    have hinj₁ : Function.Injective
        (fun s : {qc : PathCover p // pathCoverProj p qc = q} =>
          (⟨E.symm s.1, by rw [hprojEsymm]; exact s.2⟩ :
            {qc : PathCover p // pathCoverProj p qc = q})) := by
      intro a b h
      have h1 : E.symm a.1 = E.symm b.1 := congrArg Subtype.val h
      have h2 : E (E.symm a.1) = E (E.symm b.1) := congrArg (⇑E) h1
      rw [E.apply_symm_apply, E.apply_symm_apply] at h2
      exact Subtype.ext h2
    have hinj₂ : Function.Injective
        (fun s : {qc : PathCover p // pathCoverProj p qc = q} =>
          (⟨E s.1, by rw [hprojE]; exact s.2⟩ :
            {qc : PathCover p // pathCoverProj p qc = q})) := by
      intro a b h
      have h1 : E a.1 = E b.1 := congrArg Subtype.val h
      have h2 : E.symm (E a.1) = E.symm (E b.1) := congrArg (⇑E.symm) h1
      rw [E.symm_apply_apply, E.symm_apply_apply] at h2
      exact Subtype.ext h2
    have hterm2 : ∀ s : {qc : PathCover p // pathCoverProj p qc = q},
        greenEnvelope s.1 (pathCoverDeck p γ xc) = greenEnvelope (E.symm s.1) xc := by
      intro s
      have h1 := greenEnvelope_comp_diffeomorph E (E.symm s.1) xc
      rw [E.apply_symm_apply, hE xc] at h1
      exact h1
    have hterm2' : ∀ s : {qc : PathCover p // pathCoverProj p qc = q},
        greenEnvelope (E s.1) (pathCoverDeck p γ xc) = greenEnvelope s.1 xc := by
      intro s
      have h1 := greenEnvelope_comp_diffeomorph E s.1 xc
      rw [hE xc] at h1
      exact h1
    have hrange : (Set.range
        fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
          ∑ s ∈ F, greenEnvelope s.1 (pathCoverDeck p γ xc)) =
        Set.range fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
          ∑ s ∈ F, greenEnvelope s.1 xc := by
      ext b
      constructor
      · rintro ⟨F, rfl⟩
        refine ⟨F.map ⟨_, hinj₁⟩, ?_⟩
        beta_reduce
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl fun s _ => (hterm2 s).symm
      · rintro ⟨F, rfl⟩
        refine ⟨F.map ⟨_, hinj₂⟩, ?_⟩
        beta_reduce
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl fun s _ => hterm2' s
    rw [hγ] at hrange
    exact hrange
  -- ## Boundedness at the base lift, transported to the canonical lift of `p`.
  have hApb : BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 pb) := by
    refine ⟨greenEnvelope p q, ?_⟩
    rintro t ⟨F, rfl⟩
    exact hbdd_pb F
  have hPp : BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift p)) := by
    rw [hrange_fib pb (lift p) (by rw [hpb_proj, hlift p])]
    exact hApb
  -- ## Downstairs neighborhoods propagating the boundedness both ways.
  have hkeyA : ∀ y : M, y ≠ q → ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ (∀ z ∈ V, z ≠ q) ∧
      ((BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)) →
        ∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z))) ∧
      (∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z)) →
        BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)))) := by
    intro y hy
    have hly : pathCoverProj p (lift y) ≠ q := by rw [hlift y]; exact hy
    obtain ⟨U, hUopen, hxU, hUne, hUcomp⟩ := hlocH (lift y) hly
    obtain ⟨e₁, hmem, heq, htgt, hch⟩ := hloc (lift y)
    have hytgt : y ∈ e₁.target := by
      have h1 := e₁.map_source hmem
      rwa [heq _ hmem, hlift y] at h1
    have hesymm_y : e₁.symm y = lift y := by
      have h1 : e₁ (lift y) = y := by rw [heq _ hmem, hlift y]
      have h2 := e₁.left_inv hmem
      rw [h1] at h2
      exact h2
    refine ⟨e₁.target ∩ e₁.symm ⁻¹' U,
      e₁.continuousOn_symm.isOpen_inter_preimage e₁.open_target hUopen,
      ⟨hytgt, by rw [Set.mem_preimage, hesymm_y]; exact hxU⟩, ?_, ?_, ?_⟩
    · intro z hz
      have h1 : pathCoverProj p (e₁.symm z) ≠ q := hUne _ hz.2
      have h2 : pathCoverProj p (e₁.symm z) = z := by
        rw [← heq _ (e₁.map_target hz.1)]
        exact e₁.right_inv hz.1
      rwa [h2] at h1
    · intro hb z hz
      obtain ⟨C, hC⟩ := hb
      have h2 : pathCoverProj p (e₁.symm z) = z := by
        rw [← heq _ (e₁.map_target hz.1)]
        exact e₁.right_inv hz.1
      have hbz : BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (e₁.symm z)) := by
        refine ⟨3 * C, ?_⟩
        rintro t ⟨F, rfl⟩
        have h3 := (hUcomp (e₁.symm z) hz.2 F).1
        have h4 : (∑ s ∈ F, greenEnvelope s.1 (lift y)) ≤ C :=
          hC (Set.mem_range_self F)
        linarith
      rw [hrange_fib (e₁.symm z) (lift z) (by rw [h2, hlift z])]
      exact hbz
    · intro z hz hb
      have h2 : pathCoverProj p (e₁.symm z) = z := by
        rw [← heq _ (e₁.map_target hz.1)]
        exact e₁.right_inv hz.1
      have hbz : BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (e₁.symm z)) := by
        rw [hrange_fib (lift z) (e₁.symm z) (by rw [h2, hlift z])]
        exact hb
      obtain ⟨C, hC⟩ := hbz
      refine ⟨3 * C, ?_⟩
      rintro t ⟨F, rfl⟩
      have h3 := (hUcomp (e₁.symm z) hz.2 F).2
      have h4 : (∑ s ∈ F, greenEnvelope s.1 (e₁.symm z)) ≤ C :=
        hC (Set.mem_range_self F)
      linarith
  have hkeyA' : ∀ y : M, ∃ V : Set M, y ≠ q → IsOpen V ∧ y ∈ V ∧ (∀ z ∈ V, z ≠ q) ∧
      ((BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)) →
        ∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z))) ∧
      (∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z)) →
        BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)))) := by
    intro y
    by_cases hy : y = q
    · exact ⟨∅, fun h => absurd hy h⟩
    · obtain ⟨V, hV⟩ := hkeyA y hy
      exact ⟨V, fun _ => hV⟩
  choose V hV using hkeyA'
  -- ## The boundedness locus is clopen in the punctured base, hence everything.
  have hopen₁ : IsOpen {y : M | y ≠ q ∧ BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift y))} := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hy, hb⟩
    obtain ⟨ho, hm, hne, hfwd, hbwd⟩ := hV y hy
    exact ⟨V y, fun z hz => ⟨hne z hz, hfwd hb z hz⟩, ho, hm⟩
  have hopen₂ : IsOpen {y : M | y ≠ q ∧ ¬ BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift y))} := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hy, hb⟩
    obtain ⟨ho, hm, hne, hfwd, hbwd⟩ := hV y hy
    exact ⟨V y, fun z hz => ⟨hne z hz, fun hbz => hb (hbwd z hz hbz)⟩, ho, hm⟩
  have hPall : ∀ y : M, y ≠ q → BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift y)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₀, hz₀q, hz₀P⟩ := hcon
    have hconn : IsConnected ({q}ᶜ : Set M) :=
      isConnected_compl_singleton_of_connected ⟨p, q, hpq⟩ q
    have hcov : ({q}ᶜ : Set M) ⊆
        {y : M | y ≠ q ∧ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))} ∪
        {y : M | y ≠ q ∧ ¬ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))} := by
      intro y hy
      have hyq : y ≠ q := Set.mem_compl_singleton_iff.mp hy
      by_cases hb : BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))
      · exact Or.inl ⟨hyq, hb⟩
      · exact Or.inr ⟨hyq, hb⟩
    have hne₁ : (({q}ᶜ : Set M) ∩
        {y : M | y ≠ q ∧ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))}).Nonempty :=
      ⟨p, Set.mem_compl_singleton_iff.mpr hpq, hpq, hPp⟩
    have hne₂ : (({q}ᶜ : Set M) ∩
        {y : M | y ≠ q ∧ ¬ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))}).Nonempty :=
      ⟨z₀, Set.mem_compl_singleton_iff.mpr hz₀q, hz₀q, hz₀P⟩
    obtain ⟨w, -, ⟨-, hwb⟩, ⟨-, hwnb⟩⟩ :=
      hconn.2 _ _ hopen₁ hopen₂ hcov hne₁ hne₂
    exact hwnb hwb
  -- ## Boundedness of the `q`-fiber sums at every point off the fiber.
  have hSbdd_q : ∀ xc : PathCover p, pathCoverProj p xc ≠ q →
      BddAbove (Set.range
        fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
          ∑ s ∈ F, greenEnvelope s.1 xc) := by
    intro xc hxc
    have h1 := hPall (pathCoverProj p xc) hxc
    rw [hrange_fib (lift (pathCoverProj p xc)) xc (hlift (pathCoverProj p xc))]
    exact h1
  -- ## The deck sum is harmonic off the fiber.
  have hSharm : MHarmonicOn
      (fun xc => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 xc) (pathCoverProj p ⁻¹' {q})ᶜ := by
    have hdir : Directed (· ≤ ·)
        (fun (F : Finset {qc : PathCover p // pathCoverProj p qc = q})
          (xc : PathCover p) => ∑ s ∈ F, greenEnvelope s.1 xc) := by
      intro F₁ F₂
      refine ⟨F₁ ∪ F₂, fun xc => ?_, fun xc => ?_⟩
      · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          fun j _ _ => henvU j.1 xc
      · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          fun j _ _ => henvU j.1 xc
    have hbdd : ∀ xc ∈ (pathCoverProj p ⁻¹' {q})ᶜ,
        BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 xc) := by
      intro xc hxc
      have hxcp : pathCoverProj p xc ≠ q := by
        simpa [Set.mem_preimage] using hxc
      exact hSbdd_q xc hxcp
    exact mharmonicOn_iSup_directed hΩopen huq hdir hbdd
  -- ## The descended deck sum: descent identity, nonnegativity, harmonicity.
  have hS_desc : ∀ yc : PathCover p,
      (⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift (pathCoverProj p yc))) =
      ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 yc := by
    intro yc
    exact congrArg sSup (hrange_fib yc (lift (pathCoverProj p yc)) (hlift _).symm)
  have hs_nonneg : ∀ z : M,
      (0 : ℝ) ≤ ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift z) :=
    fun z => Real.iSup_nonneg fun F => Finset.sum_nonneg fun j _ => henvU j.1 (lift z)
  have hs_harm : MHarmonicOn
      (fun z => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift z)) {q}ᶜ := by
    intro z hz
    have hzp : z ≠ q := hz
    have hlnf : lift z ∈ (pathCoverProj p ⁻¹' {q})ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hlift z]
      exact hzp
    have hSat := hSharm (lift z) hlnf
    have h2 := hdown_harm
      (fun xc => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 xc)
      (fun z' => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift z'))
      (lift z) (fun yc => hS_desc yc) hSat
    rwa [hlift z] at h2
  -- ## The descended deck sum has the exact logarithmic pole at `q`.
  have hspole : ∃ C, ∀ᶠ y in 𝓝[≠] q,
      -Real.log ‖poleCoord q y‖ - C ≤
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift y) := by
    obtain ⟨e₂, hmem, heq, htgt, hch⟩ := hloc (lift q)
    obtain ⟨ρ, hρ, -, ht, htharm, hteq⟩ :=
      exists_harmonic_pole_extension (hGup (lift q))
    have htc : ContinuousAt ht (chartAt ℂ (lift q) (lift q)) :=
      (htharm _ (mem_ball_self hρ)).1.continuousAt
    set B : ℝ := |ht (chartAt ℂ (lift q) (lift q))| + 1 with hBdef
    have hB : ∀ᶠ w in 𝓝 (chartAt ℂ (lift q) (lift q)), |ht w| ≤ B := by
      have h1 := htc (Metric.ball_mem_nhds (ht (chartAt ℂ (lift q) (lift q))) one_pos)
      filter_upwards [h1] with w hw
      have h2 : |ht w - ht (chartAt ℂ (lift q) (lift q))| < 1 := by
        simpa [Real.dist_eq] using hw
      have h3 := abs_sub_abs_le_abs_sub (ht w) (ht (chartAt ℂ (lift q) (lift q)))
      rw [hBdef]
      linarith
    have hqtgt : q ∈ e₂.target := by
      have h1 := e₂.map_source hmem
      rwa [heq _ hmem, hlift q] at h1
    have hesymm_cont : ContinuousAt e₂.symm q := e₂.continuousAt_symm hqtgt
    have hesymm_val : e₂.symm q = lift q := by
      have h1 : e₂ (lift q) = q := by rw [heq _ hmem, hlift q]
      have h2 := e₂.left_inv hmem
      rw [h1] at h2
      exact h2
    have hev_sec : ∀ᶠ y in 𝓝[≠] q,
        e₂.symm y ∈ (chartAt ℂ (lift q)).source ∧
        chartAt ℂ (lift q) (e₂.symm y) ∈ ball (chartAt ℂ (lift q) (lift q)) ρ ∧
        |ht (chartAt ℂ (lift q) (e₂.symm y))| ≤ B := by
      have h1 : ∀ᶠ y in 𝓝 q, e₂.symm y ∈ (chartAt ℂ (lift q)).source := by
        refine hesymm_cont.eventually_mem ?_
        rw [hesymm_val]
        exact (chartAt ℂ (lift q)).open_source.mem_nhds (mem_chart_source ℂ (lift q))
      have hcc : ContinuousAt (chartAt ℂ (lift q)) (e₂.symm q) := by
        rw [hesymm_val]
        exact (chartAt ℂ (lift q)).continuousAt (mem_chart_source ℂ (lift q))
      have h2 : ContinuousAt (fun y => chartAt ℂ (lift q) (e₂.symm y)) q :=
        hcc.comp hesymm_cont
      have h3 : ∀ᶠ w in 𝓝 (chartAt ℂ (lift q) (e₂.symm q)),
          w ∈ ball (chartAt ℂ (lift q) (lift q)) ρ ∧ |ht w| ≤ B := by
        rw [hesymm_val]
        exact (isOpen_ball.eventually_mem (mem_ball_self hρ)).and hB
      have h4 := h2.eventually_mem h3
      exact nhdsWithin_le_nhds (h1.and h4)
    have hev_tgt : ∀ᶠ y in 𝓝[≠] q, y ∈ e₂.target :=
      nhdsWithin_le_nhds (e₂.open_target.mem_nhds hqtgt)
    have hev_src₀ : ∀ᶠ y in 𝓝[≠] q, y ∈ (chartAt ℂ q).source :=
      nhdsWithin_le_nhds
        ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q))
    refine ⟨B, ?_⟩
    filter_upwards [hev_sec, hev_tgt, hev_src₀, self_mem_nhdsWithin]
      with y hsec hbt hsrc₀ hyne'
    have hyne : y ≠ q := hyne'
    have hxs : e₂.symm y ∈ e₂.source := e₂.map_target hbt
    have hprojxy : pathCoverProj p (e₂.symm y) = y := by
      rw [← heq _ hxs]
      exact e₂.right_inv hbt
    have hpc_ne : poleCoord q y ≠ 0 := by
      intro hcon
      apply hyne
      refine (chartAt ℂ q).injOn hsrc₀ (mem_chart_source ℂ q) ?_
      have h6 : chartAt ℂ q y - chartAt ℂ q q = 0 := hcon
      linear_combination (norm := module) h6
    have hpc_eq : poleCoord (lift q) (e₂.symm y) = poleCoord q y := by
      have h1 := hpolecoord (lift q) (e₂.symm y) hsec.1
      rw [hlift q, hprojxy] at h1
      exact h1
    have hne_ctr : chartAt ℂ (lift q) (e₂.symm y) ≠ chartAt ℂ (lift q) (lift q) := by
      intro hcon
      apply hpc_ne
      rw [← hpc_eq]
      have h7 : poleCoord (lift q) (e₂.symm y) =
          chartAt ℂ (lift q) (e₂.symm y) - chartAt ℂ (lift q) (lift q) := rfl
      rw [h7, hcon, sub_self]
    have hmem3 : chartAt ℂ (lift q) (e₂.symm y) ∈
        ball (chartAt ℂ (lift q) (lift q)) ρ \ {chartAt ℂ (lift q) (lift q)} :=
      ⟨hsec.2.1, hne_ctr⟩
    have h8 := hteq _ hmem3
    rw [(chartAt ℂ (lift q)).left_inv hsec.1] at h8
    have h9 : Real.log ‖chartAt ℂ (lift q) (e₂.symm y) -
        chartAt ℂ (lift q) (lift q)‖ = Real.log ‖poleCoord q y‖ := by
      have h10 : chartAt ℂ (lift q) (e₂.symm y) - chartAt ℂ (lift q) (lift q) =
          poleCoord (lift q) (e₂.symm y) := rfl
      rw [h10, hpc_eq]
    rw [h9] at h8
    have hhead : greenEnvelope (lift q) (e₂.symm y) =
        ht (chartAt ℂ (lift q) (e₂.symm y)) - Real.log ‖poleCoord q y‖ := by
      linarith [h8]
    have hband := (abs_le.mp hsec.2.2).1
    have hsingle : greenEnvelope (lift q) (e₂.symm y) ≤
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (e₂.symm y) := by
      have hb1 : pathCoverProj p (e₂.symm y) ≠ q := by
        rw [hprojxy]
        exact hyne
      have hb2 := le_ciSup (hSbdd_q (e₂.symm y) hb1)
        ({⟨lift q, hlift q⟩} : Finset {qc : PathCover p // pathCoverProj p qc = q})
      rw [Finset.sum_singleton] at hb2
      exact hb2
    have hdesc := hS_desc (e₂.symm y)
    rw [hprojxy] at hdesc
    rw [hdesc]
    rw [hhead] at hsingle
    linarith
  -- ## Every candidate downstairs at `q` is dominated by the descended sum.
  have hpart2q : ∀ y : M, y ≠ q → ∀ v ∈ greenFamily q, v y ≤
      ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift y) := by
    intro y hy v hv
    obtain ⟨hvsub, hvcont, ⟨Kv, hKvc, -, hKvz⟩, Cv, hCv⟩ := hv
    have hwsub : MSubharmonicOn (fun z => v z -
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift z)) {q}ᶜ :=
      fun z hz => (hvsub z hz).sub_mharmonicAt (hs_harm z hz)
    have hsupp2 : ∃ K : Set M, IsCompact K ∧ ∀ z ∉ K, (v z -
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift z)) ≤ 0 := by
      refine ⟨Kv ∪ {q}, hKvc.union isCompact_singleton, fun z hz => ?_⟩
      have h1 : v z = 0 := hKvz z fun h => hz (Set.mem_union_left _ h)
      have h2 := hs_nonneg z
      rw [h1]
      linarith
    have hpole2 : ∃ C, ∀ᶠ z in 𝓝[≠] q, (v z -
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift z)) ≤ C := by
      obtain ⟨C₁, hC₁⟩ := hspole
      refine ⟨Cv + C₁, ?_⟩
      filter_upwards [hCv, hC₁] with z h1 h2
      linarith
    have h3 := msubharmonic_le_zero_of_puncture hwsub hsupp2 hpole2 y hy
    linarith
  -- ## Assembly: the family at `q` is bounded above at the witness `p`.
  refine ⟨p, hpq, ⟨⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
    ∑ s ∈ F, greenEnvelope s.1 (lift p), ?_⟩⟩
  rintro t ⟨v, hv, rfl⟩
  exact hpart2q p hpq v hv

/-- **Symmetry of the Green's function**: on a connected hyperbolic surface
the Green's envelope is symmetric in the pole and the evaluation point. The
deck-sum formula reduces the identity to the simply connected cover, where it
holds by the Riemann map and the disc kernel, and the deck action reindexes
the two fiber sums into one another. -/
theorem greenEnvelope_symm [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p q : M} (hG : HasGreenFunction p) (hpq : p ≠ q) :
    greenEnvelope p q = greenEnvelope q p := by
  classical
  -- ## A path from `p` to `q` downstairs, and the two distinguished lifts.
  have : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace ℂ M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  obtain ⟨sp⟩ := PathConnectedSpace.joined p q
  obtain ⟨pb, hpb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = p :=
    ⟨pathCoverBase p, rfl⟩
  obtain ⟨qb, hqb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = q :=
    ⟨⟨q, ⟦sp⟧⟩, rfl⟩
  -- ## Topology of the universal path cover.
  have : PathConnectedSpace (PathCover p) := pathConnectedSpace_pathCover p
  have : SimplyConnectedSpace (PathCover p) := simplyConnectedSpace_pathCover p
  have : T2Space (PathCover p) := t2space_pathCover p
  have : NoncompactSpace (PathCover p) := noncompactSpace_pathCover p
  -- ## Green's functions upstairs: at the base lift, hence everywhere.
  have hGpb : HasGreenFunction pb := hasGreenFunction_pathCover p hG hpb_proj
  have hGall : ∀ rc : PathCover p, HasGreenFunction rc := fun rc =>
    hasGreenFunction_of_simplyConnected hGpb
  -- ## Groupoid algebra of the deck action.
  have hdeck_comp : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ (pathCoverDeck p δ pc) = pathCoverDeck p (γ.trans δ) pc := by
    intro γ δ pc
    change (⟨pc.pt, γ.trans (δ.trans pc.cls)⟩ : PathCover p)
      = ⟨pc.pt, (γ.trans δ).trans pc.cls⟩
    exact congrArg (PathCover.mk pc.pt)
      (Path.Homotopic.Quotient.trans_assoc γ δ pc.cls).symm
  have hdeck_refl : ∀ pc : PathCover p,
      pathCoverDeck p (Path.Homotopic.Quotient.refl p) pc = pc := by
    intro pc
    change (⟨pc.pt, (Path.Homotopic.Quotient.refl p).trans pc.cls⟩ : PathCover p) = pc
    exact congrArg (PathCover.mk pc.pt) (Path.Homotopic.Quotient.refl_trans pc.cls)
  have hdeck_free : ∀ (δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p δ pc = pc → δ = Path.Homotopic.Quotient.refl p := by
    intro δ pc h
    have h' : (⟨pc.pt, δ.trans pc.cls⟩ : PathCover p) = ⟨pc.pt, pc.cls⟩ := h
    rw [PathCover.mk.injEq] at h'
    have h1 : δ.trans pc.cls = pc.cls := eq_of_heq h'.2
    calc δ = δ.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl δ).symm
      _ = δ.trans (pc.cls.trans pc.cls.symm) := by
          rw [Path.Homotopic.Quotient.trans_symm]
      _ = (δ.trans pc.cls).trans pc.cls.symm :=
          (Path.Homotopic.Quotient.trans_assoc δ pc.cls pc.cls.symm).symm
      _ = pc.cls.trans pc.cls.symm := by rw [h1]
      _ = Path.Homotopic.Quotient.refl p := Path.Homotopic.Quotient.trans_symm pc.cls
  have hdeck_inj : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ pc = pathCoverDeck p δ pc → γ = δ := by
    intro γ δ pc h
    have h2 : pathCoverDeck p (δ.symm.trans γ) pc = pc := by
      rw [← hdeck_comp, h, hdeck_comp, Path.Homotopic.Quotient.symm_trans, hdeck_refl]
    have h3 := hdeck_free _ _ h2
    calc γ = (Path.Homotopic.Quotient.refl p).trans γ :=
          (Path.Homotopic.Quotient.refl_trans γ).symm
      _ = (δ.trans δ.symm).trans γ := by rw [Path.Homotopic.Quotient.trans_symm]
      _ = δ.trans (δ.symm.trans γ) := Path.Homotopic.Quotient.trans_assoc δ δ.symm γ
      _ = δ.trans (Path.Homotopic.Quotient.refl p) := by rw [h3]
      _ = δ := Path.Homotopic.Quotient.trans_refl δ
  have hsymm_symm : ∀ γ : Path.Homotopic.Quotient p p, γ.symm.symm = γ := by
    intro γ
    calc γ.symm.symm = γ.symm.symm.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl γ.symm.symm).symm
      _ = γ.symm.symm.trans (γ.symm.trans γ) := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = (γ.symm.symm.trans γ.symm).trans γ :=
          (Path.Homotopic.Quotient.trans_assoc γ.symm.symm γ.symm γ).symm
      _ = (Path.Homotopic.Quotient.refl p).trans γ := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = γ := Path.Homotopic.Quotient.refl_trans γ
  -- ## Choices: fiber loops and deck diffeomorphisms.
  have hfibA : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      ∃ γ : Path.Homotopic.Quotient p p, pathCoverDeck p γ pb = a.1 := fun a =>
    pathCoverDeck_transitive p pb a.1 (hpb_proj.trans a.2.symm)
  choose γfn hγfn using hfibA
  choose Efn hEfn using fun γ : Path.Homotopic.Quotient p p =>
    exists_pathCoverDeck_diffeomorph p γ
  -- ## The fiber reindexing map: conjugate `p`-fiber points into the `q`-fiber.
  obtain ⟨Φ, hΦspec⟩ : ∃ Φ : {qc : PathCover p // pathCoverProj p qc = p} →
      {qc : PathCover p // pathCoverProj p qc = q},
      ∀ a, (Φ a).1 = pathCoverDeck p (γfn a).symm qb :=
    ⟨fun a => ⟨pathCoverDeck p (γfn a).symm qb,
      (pathCoverProj_deck p (γfn a).symm qb).trans hqb_proj⟩, fun _ => rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro a₁ a₂ h
    have h1 : pathCoverDeck p (γfn a₁).symm qb = pathCoverDeck p (γfn a₂).symm qb := by
      rw [← hΦspec a₁, ← hΦspec a₂, h]
    have h2 : (γfn a₁).symm = (γfn a₂).symm := hdeck_inj _ _ _ h1
    have h3 : γfn a₁ = γfn a₂ := by
      rw [← hsymm_symm (γfn a₁), h2, hsymm_symm]
    apply Subtype.ext
    rw [← hγfn a₁, ← hγfn a₂, h3]
  have hΦsurj : Function.Surjective Φ := by
    intro b
    obtain ⟨δ, hδ⟩ := pathCoverDeck_transitive p qb b.1 (hqb_proj.trans b.2.symm)
    have hmem : pathCoverProj p (pathCoverDeck p δ.symm pb) = p :=
      (pathCoverProj_deck p δ.symm pb).trans hpb_proj
    refine ⟨⟨pathCoverDeck p δ.symm pb, hmem⟩, ?_⟩
    have hloop : γfn ⟨pathCoverDeck p δ.symm pb, hmem⟩ = δ.symm := by
      apply hdeck_inj _ _ pb
      exact hγfn ⟨pathCoverDeck p δ.symm pb, hmem⟩
    apply Subtype.ext
    rw [hΦspec, hloop, hsymm_symm, hδ]
  obtain ⟨e, he⟩ : ∃ e : {qc : PathCover p // pathCoverProj p qc = p} ≃
      {qc : PathCover p // pathCoverProj p qc = q}, ∀ a, e a = Φ a :=
    ⟨Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩, fun _ => rfl⟩
  -- ## Termwise symmetry: cover symmetry plus conformal invariance of the deck maps.
  have hterm : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      greenEnvelope a.1 qb = greenEnvelope (pathCoverDeck p (γfn a).symm qb) pb := by
    intro a
    have hne : a.1 ≠ qb := by
      intro h
      apply hpq
      rw [← a.2, h, hqb_proj]
    have h1 : greenEnvelope a.1 qb = greenEnvelope qb a.1 :=
      greenEnvelope_symm_of_simplyConnected (hGall a.1) hne
    have hEpb : Efn (γfn a) pb = a.1 := (hEfn (γfn a) pb).trans (hγfn a)
    have hEsymm_a : (Efn (γfn a)).symm a.1 = pb := by
      rw [← hEpb, Diffeomorph.symm_apply_apply]
    have h2 : Efn (γfn a) (pathCoverDeck p (γfn a).symm qb) = qb := by
      rw [hEfn (γfn a) (pathCoverDeck p (γfn a).symm qb), hdeck_comp,
        Path.Homotopic.Quotient.trans_symm, hdeck_refl]
    have hEsymm_q : (Efn (γfn a)).symm qb = pathCoverDeck p (γfn a).symm qb := by
      calc (Efn (γfn a)).symm qb
          = (Efn (γfn a)).symm (Efn (γfn a) (pathCoverDeck p (γfn a).symm qb)) := by
            rw [h2]
        _ = pathCoverDeck p (γfn a).symm qb := Diffeomorph.symm_apply_apply _ _
    have h3 : greenEnvelope ((Efn (γfn a)).symm qb) ((Efn (γfn a)).symm a.1)
        = greenEnvelope qb a.1 :=
      greenEnvelope_comp_diffeomorph (Efn (γfn a)).symm qb a.1
    rw [h1, ← h3, hEsymm_a, hEsymm_q]
  -- ## The two deck-sum expansions and the reindexing of the fiber sums.
  have hne1 : pathCoverProj p qb ≠ p := by rw [hqb_proj]; exact Ne.symm hpq
  have hne2 : pathCoverProj p pb ≠ q := by rw [hpb_proj]; exact hpq
  have h1 := (greenEnvelope_deckSum p (p₀ := p) (pc := qb) hG hne1 ⟨pb, hpb_proj, hGpb⟩).2
  have hGq : HasGreenFunction q := hasGreenFunction_of_hasGreenFunction hG
  have h2 := (greenEnvelope_deckSum p (p₀ := q) (pc := pb) hGq hne2 ⟨qb, hqb_proj, hGall qb⟩).2
  rw [hqb_proj] at h1
  rw [hpb_proj] at h2
  have hFeq : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
      (∑ qc ∈ F, greenEnvelope qc.1 qb)
        = ∑ qc ∈ e.finsetCongr F, greenEnvelope qc.1 pb := by
    intro F
    rw [Equiv.finsetCongr_apply, Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [he a, hΦspec a]
    exact hterm a
  have hstep1 : (⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
        ∑ qc ∈ F, greenEnvelope qc.1 qb)
      = ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
        ∑ qc ∈ e.finsetCongr F, greenEnvelope qc.1 pb := iSup_congr hFeq
  have hstep2 : (⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
        ∑ qc ∈ e.finsetCongr F, greenEnvelope qc.1 pb)
      = ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ qc ∈ F, greenEnvelope qc.1 pb :=
    Equiv.iSup_comp
      (g := fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ qc ∈ F, greenEnvelope qc.1 pb) e.finsetCongr
  exact h1.trans ((hstep1.trans hstep2).trans h2.symm)

end RiemannDynamics
