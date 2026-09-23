/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.ExteriorBound

/-!
# Bipolar Green: pole companions and the log barrier

Two bricks for the dipole limit.
`exists_harmonicOnNhd_pieceGreen_dipole_add_log` extends a dipole difference
of piece Green's functions harmonically across the pole after subtracting
the logarithmic singularity, bounded by the exterior bound plus the
logarithms of the two ball radii. `pieceGreen_dipole_sub_le_log_barrier` is
the annulus log-barrier estimate: one dipole difference exceeds another by
at most the outer-circle gap plus a logarithmic barrier whose constant is
controlled by the exterior bound.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

/-- The pole companion of a dipole difference of piece Green's functions: after
subtracting the logarithmic pole at the first point, the difference extends to a
harmonic function on a fixed chart ball, bounded by the exterior bound plus the
logarithms of the two ball radii. -/
theorem exists_harmonicOnNhd_pieceGreen_dipole_add_log (D₀ : CoordDisk M)
    {pa pb : M} {ra rb C₀ : ℝ}
    (hra : 0 < ra) (hrb : 0 < rb)
    (htga : closedBall (chartAt ℂ pa pa) (2 * ra) ⊆ (chartAt ℂ pa).target)
    (havaCar : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      (chartAt ℂ pa).symm w ∉ D₀.closedCarrier)
    (havaNe : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      (chartAt ℂ pa).symm w ≠ pb)
    (havb : ∀ w ∈ closedBall (chartAt ℂ pb pb) (2 * rb),
      (chartAt ℂ pb).symm w ∉ D₀.closedCarrier)
    (hdisj : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      (chartAt ℂ pa).symm w ∉
        (chartAt ℂ pb).symm '' closedBall (chartAt ℂ pb pb) (2 * rb))
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hbd : ∀ x : M,
      x ∉ (chartAt ℂ pa).source ∩ ⇑(chartAt ℂ pa) ⁻¹' ball (chartAt ℂ pa pa) ra →
      x ∉ (chartAt ℂ pb).source ∩ ⇑(chartAt ℂ pb) ⁻¹' ball (chartAt ℂ pb pb) rb →
      |pieceGreen (D₀.shrink t ht ht1).compl pa x -
        pieceGreen (D₀.shrink t ht ht1).compl pb x| ≤ C₀) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ pa pa) (2 * ra)) ∧
      (∀ w ∈ ball (chartAt ℂ pa pa) (2 * ra) \ {chartAt ℂ pa pa},
        h w = pieceGreen (D₀.shrink t ht ht1).compl pa ((chartAt ℂ pa).symm w) -
          pieceGreen (D₀.shrink t ht ht1).compl pb ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖) ∧
      ∀ w ∈ ball (chartAt ℂ pa pa) (2 * ra),
        |h w| ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
  classical
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Chart reading of a harmonic surface function is plane-harmonic. -/
  have htransfer : ∀ (x : M) (Ωt : Set M) (v : M → ℝ), MHarmonicOn v Ωt →
      ∀ w ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ωt,
        HarmonicAt (v ∘ (chartAt ℂ x).symm) w := by
    intro x Ωt v hv w hw
    obtain ⟨hwt, hwΩ⟩ := hw
    have hwΩ' : (chartAt ℂ x).symm w ∈ Ωt := hwΩ
    have hyy : (chartAt ℂ x).symm w ∈ (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
      mem_chart_source ℂ ((chartAt ℂ x).symm w)
    have htrans : AnalyticAt ℂ
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w := by
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hwt
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ ((chartAt ℂ x).symm w)))
          ((chartAt ℂ x).symm w) :=
        contMDiffAt_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas ((chartAt ℂ x).symm w)) hyy
      exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
    have hmh : HarmonicAt (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        ((⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w) := hv _ hwΩ'
    have hcomp := harmonicAt_comp_analyticAt hmh htrans
    have hev : (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 w]
        v ∘ ⇑(chartAt ℂ x).symm := by
      have hS : IsOpen ((chartAt ℂ x).target ∩
          ⇑(chartAt ℂ x).symm ⁻¹' (chartAt ℂ ((chartAt ℂ x).symm w)).source) :=
        (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ x).open_target
          (chartAt ℂ ((chartAt ℂ x).symm w)).open_source
      filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with ζ hζ
      simp only [Function.comp_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hζ.2]
    exact (harmonicAt_congr_nhds hev).mp hcomp
  have mharmSub : ∀ (f g : M → ℝ) (z : M), MHarmonicAt f z → MHarmonicAt g z →
      MHarmonicAt (fun y ↦ f y - g y) z := by
    intro f g z hf hg
    refine mharm_congr (f + -g) _ z (Filter.Eventually.of_forall fun y ↦ ?_) (hf.add hg.neg)
    simp only [Pi.add_apply, Pi.neg_apply]
    exact (sub_eq_add_neg (f y) (g y)).symm
  /- ## Negation of a plane-harmonic function. -/
  have harmNeg : ∀ (h : ℂ → ℝ) (s : Set ℂ), HarmonicOnNhd h s →
      HarmonicOnNhd (fun w ↦ -h w) s := by
    intro h s hh z hz
    have h1 := (hh z hz).const_smul (c := (-1 : ℝ))
    have hev : ((-1 : ℝ) • h) =ᶠ[𝓝 z] fun w ↦ -h w := by
      filter_upwards with w
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    exact (harmonicAt_congr_nhds hev).mp h1
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dite_eq_left ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dite_eq_right]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    have := hcs
    have := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon ↦ hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z ↦ pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## The piece, its instances and the Green data. -/
  set P : Opens M := (D₀.shrink t ht ht1).compl with hPdef
  have hcarsub : (D₀.shrink t ht ht1).closedCarrier ⊆ D₀.closedCarrier := by
    have h1 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    have h2 : D₀.closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) D₀.radius := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left D₀.radius_pos.le ht1))
  have hpasrc : pa ∈ (chartAt ℂ pa).source := mem_chart_source ℂ pa
  have hpbsrc : pb ∈ (chartAt ℂ pb).source := mem_chart_source ℂ pb
  have hpaca : (chartAt ℂ pa).symm (chartAt ℂ pa pa) = pa :=
    (chartAt ℂ pa).left_inv hpasrc
  have hpbcb : (chartAt ℂ pb).symm (chartAt ℂ pb pb) = pb :=
    (chartAt ℂ pb).left_inv hpbsrc
  have hpacar : pa ∉ D₀.closedCarrier := by
    have h1 := havaCar (chartAt ℂ pa pa)
      (mem_closedBall_self (by linarith only [hra]))
    rwa [hpaca] at h1
  have hpbcar : pb ∉ D₀.closedCarrier := by
    have h1 := havb (chartAt ℂ pb pb) (mem_closedBall_self (by linarith only [hrb]))
    rwa [hpbcb] at h1
  have hpaP : pa ∈ P := fun hmem ↦ hpacar (hcarsub hmem)
  have hpbP : pb ∈ P := fun hmem ↦ hpbcar (hcarsub hmem)
  have hPconn : ConnectedSpace ↥P :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  have hPnc : NoncompactSpace ↥P := noncompactSpace_coordDisk_compl _
  have hGFa : HasGreenFunction (⟨pa, hpaP⟩ : ↥P) :=
    hasGreenFunction_coordDisk_compl _ pa hpaP
  have hGFb : HasGreenFunction (⟨pb, hpbP⟩ : ↥P) :=
    hasGreenFunction_coordDisk_compl _ pb hpbP
  /- ## The own-pole boundedness in the ambient chart. -/
  have poleData : ∃ ρ B : ℝ, 0 < ρ ∧
      ball (chartAt ℂ pa pa) ρ ⊆ (chartAt ℂ pa).target ∧
      ∀ w ∈ ball (chartAt ℂ pa pa) ρ \ {chartAt ℂ pa pa},
        (chartAt ℂ pa).symm w ∈ P ∧
        |pieceGreen P pa ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖| ≤ B := by
    obtain ⟨rE, hrE0, hrEsub, hE, hEharm, hEval⟩ :=
      exists_harmonic_pole_extension hGFa
    have hnety : Nonempty ↥(P) := ⟨⟨pa, hpaP⟩⟩
    set ea : OpenPartialHomeomorph M ℂ := chartAt ℂ pa with hea
    have hpasrc : pa ∈ ea.source := mem_chart_source ℂ pa
    have hct : chartAt ℂ (⟨pa, hpaP⟩ : ↥P) = ea.subtypeRestr hnety :=
      Opens.chartAt_eq
    have hcenter : chartAt ℂ (⟨pa, hpaP⟩ : ↥P) (⟨pa, hpaP⟩ : ↥P)
        = ea pa := by
      rw [hct, ea.subtypeRestr_coe hnety]
      rfl
    rw [hcenter] at hrEsub hEharm hEval
    have hcont : ContinuousOn hE (closedBall (ea pa) (rE / 2)) :=
      hEharm.continuousOn.mono (closedBall_subset_ball (by linarith only [hrE0]))
    obtain ⟨BE, hBE⟩ :=
      (isCompact_closedBall (ea pa) (rE / 2)).exists_bound_of_continuousOn hcont
    have heqOn : Set.EqOn (⇑ea.symm) (Subtype.val ∘ ⇑(ea.subtypeRestr hnety).symm)
        (ea.subtypeRestr hnety).target := ea.subtypeRestr_symm_eqOn hnety
    refine ⟨rE / 2, BE, half_pos hrE0, ?_, ?_⟩
    · intro w hw
      have h1 : w ∈ (chartAt ℂ (⟨pa, hpaP⟩ : ↥P)).target := by
        apply hrEsub
        exact ball_subset_ball (by linarith only [hrE0]) hw
      rw [hct] at h1
      exact ea.subtypeRestr_target_subset hnety h1
    · intro w hw
      obtain ⟨hwball, hwne⟩ := hw
      have hwne' : w ≠ ea pa := by simpa using hwne
      have hwball' : w ∈ ball (ea pa) rE :=
        ball_subset_ball (by linarith only [hrE0]) hwball
      have hwtgt : w ∈ (ea.subtypeRestr hnety).target := by
        have h1 := hrEsub hwball'
        rwa [hct] at h1
      have hmemP : ea.symm w ∈ P := by
        rw [heqOn hwtgt]
        exact ((ea.subtypeRestr hnety).symm w).2
      refine ⟨hmemP, ?_⟩
      have h2 := hEval w ⟨hwball', by simpa using hwne'⟩
      have h4 : ((chartAt ℂ (⟨pa, hpaP⟩ : ↥P)).symm w : ↥(P))
          = ⟨ea.symm w, hmemP⟩ := by
        apply Subtype.ext
        change ((chartAt ℂ (⟨pa, hpaP⟩ : ↥P)).symm w : M) = ea.symm w
        rw [hct]
        exact (heqOn hwtgt).symm
      rw [h4, ← pgval (P) pa hpaP (ea.symm w) hmemP] at h2
      rw [← h2]
      exact hBE w (ball_subset_closedBall hwball)
  /- ## The dipole difference and its data on the piece. -/
  set Fd : M → ℝ := fun z ↦ pieceGreen P pa z - pieceGreen P pb z with hFdd
  have hcarin : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      (chartAt ℂ pa).symm w ∈ P :=
    fun w hw hmem ↦ havaCar w hw (hcarsub hmem)
  have hnp : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra), w ≠ chartAt ℂ pa pa →
      (chartAt ℂ pa).symm w ≠ pa ∧ (chartAt ℂ pa).symm w ≠ pb := by
    intro w hw hwne
    constructor
    · intro hcon
      have hwt : w ∈ (chartAt ℂ pa).target := htga hw
      have h1 : chartAt ℂ pa ((chartAt ℂ pa).symm w) = w :=
        (chartAt ℂ pa).right_inv hwt
      rw [hcon] at h1
      exact hwne h1.symm
    · exact havaNe w hw
  have hsB : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      ra ≤ dist w (chartAt ℂ pa pa) →
      (chartAt ℂ pa).symm w ∉
        (chartAt ℂ pa).source ∩ ⇑(chartAt ℂ pa) ⁻¹' ball (chartAt ℂ pa pa) ra ∧
      (chartAt ℂ pa).symm w ∉
        (chartAt ℂ pb).source ∩ ⇑(chartAt ℂ pb) ⁻¹' ball (chartAt ℂ pb pb) rb := by
    intro w hw hdw
    constructor
    · intro hmem
      obtain ⟨hsrc, hpre⟩ := hmem
      rw [Set.mem_preimage] at hpre
      have hwt : w ∈ (chartAt ℂ pa).target := htga hw
      rw [(chartAt ℂ pa).right_inv hwt] at hpre
      rw [mem_ball] at hpre
      linarith only [hdw, hpre]
    · intro hmem
      obtain ⟨hsrc, hpre⟩ := hmem
      rw [Set.mem_preimage] at hpre
      refine hdisj w hw ⟨chartAt ℂ pb ((chartAt ℂ pa).symm w), ?_, ?_⟩
      · exact ball_subset_closedBall (ball_subset_ball (by linarith only [hrb]) hpre)
      · exact (chartAt ℂ pb).left_inv hsrc
  have hFharm : ∀ (z : M), z ∈ P → z ≠ pa → z ≠ pb → MHarmonicAt Fd z := by
    intro z hzP hz1 hz2
    exact mharmSub _ _ z
      (pgharm P pa hpaP hPconn hPnc hGFa z hzP hz1)
      (pgharm P pb hpbP hPconn hPnc hGFb z hzP hz2)
  have hFbd : ∀ (z : M),
      z ∉ (chartAt ℂ pa).source ∩ ⇑(chartAt ℂ pa) ⁻¹' ball (chartAt ℂ pa pa) ra →
      z ∉ (chartAt ℂ pb).source ∩ ⇑(chartAt ℂ pb) ⁻¹' ball (chartAt ℂ pb pb) rb →
      |Fd z| ≤ C₀ := fun z h1 h2 ↦ hbd z h1 h2
  /- ## The pole structure of the difference near `pa`. -/
  have hFpole : ∃ ρ B : ℝ, 0 < ρ ∧
      ∀ w ∈ ball (chartAt ℂ pa pa) ρ \ {chartAt ℂ pa pa},
        |Fd ((chartAt ℂ pa).symm w) + Real.log ‖w - chartAt ℂ pa pa‖| ≤ B := by
    obtain ⟨ρE, BE, hρE0, hballE, hEbd⟩ := poleData
    set ρ2 : ℝ := min ρE (2 * ra) with hρ2
    have hρ20 : 0 < ρ2 := lt_min hρE0 (by linarith only [hra])
    have hcont2 : ContinuousOn (fun w ↦ pieceGreen P pb ((chartAt ℂ pa).symm w))
        (closedBall (chartAt ℂ pa pa) ρ2) := by
      intro w hw
      have hwcb : w ∈ closedBall (chartAt ℂ pa pa) (2 * ra) :=
        closedBall_subset_closedBall (min_le_right _ _) hw
      have hwt : w ∈ (chartAt ℂ pa).target := htga hwcb
      have hHA : HarmonicAt (pieceGreen P pb ∘ ⇑(chartAt ℂ pa).symm) w := by
        refine htransfer pa ((P : Set M) ∩ {pb}ᶜ) (pieceGreen P pb) ?_ w ⟨hwt, ?_⟩
        · intro z hz
          exact pgharm P pb hpbP hPconn hPnc hGFb z hz.1
            (Set.mem_compl_singleton_iff.1 hz.2)
        · rw [Set.mem_preimage]
          exact ⟨hcarin w hwcb, Set.mem_compl_singleton_iff.2 (havaNe w hwcb)⟩
      exact (hHA.1.continuousAt).continuousWithinAt
    obtain ⟨B2c, hB2c⟩ :=
      (isCompact_closedBall (chartAt ℂ pa pa) ρ2).exists_bound_of_continuousOn hcont2
    refine ⟨ρ2, BE + B2c, hρ20, ?_⟩
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwbE : w ∈ ball (chartAt ℂ pa pa) ρE \ {chartAt ℂ pa pa} :=
      ⟨ball_subset_ball (min_le_left _ _) hwb, hwne⟩
    have h1 := (hEbd w hwbE).2
    have h2 := hB2c w (ball_subset_closedBall hwb)
    rw [Real.norm_eq_abs] at h2
    have heq : Fd ((chartAt ℂ pa).symm w) + Real.log ‖w - chartAt ℂ pa pa‖ =
        (pieceGreen P pa ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖) -
          pieceGreen P pb ((chartAt ℂ pa).symm w) := by
      simp only [hFdd]
      ring
    rw [heq]
    calc |(pieceGreen P pa ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖) -
          pieceGreen P pb ((chartAt ℂ pa).symm w)|
        ≤ |pieceGreen P pa ((chartAt ℂ pa).symm w) +
            Real.log ‖w - chartAt ℂ pa pa‖| +
          |pieceGreen P pb ((chartAt ℂ pa).symm w)| := abs_sub _ _
      _ ≤ BE + B2c := add_le_add h1 h2
  /- ## The companion via removability and the disk maximum principle. -/
  set ea : OpenPartialHomeomorph M ℂ := chartAt ℂ pa with hea
  set ca : ℂ := ea pa with hca
  have hpasrc : pa ∈ ea.source := mem_chart_source ℂ pa
  set u : ℂ → ℝ := fun w ↦ Fd (ea.symm w) + Real.log ‖w - ca‖ with hu
  have huharm : ∀ w ∈ ball ca (2 * ra) \ {ca}, HarmonicAt u w := by
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwne' : w ≠ ca := by simpa using hwne
    have hwcb : w ∈ closedBall ca (2 * ra) := ball_subset_closedBall hwb
    have hwt : w ∈ ea.target := htga hwcb
    have hnpw := hnp w hwcb hwne'
    have h1 : HarmonicAt (Fd ∘ ⇑ea.symm) w := by
      refine htransfer pa ((P : Set M) ∩ ({pa}ᶜ ∩ {pb}ᶜ)) (Fd) ?_ w ⟨hwt, ?_⟩
      · intro z hz
        exact hFharm z hz.1 (Set.mem_compl_singleton_iff.1 hz.2.1)
          (Set.mem_compl_singleton_iff.1 hz.2.2)
      · rw [Set.mem_preimage]
        exact ⟨hcarin w hwcb, Set.mem_compl_singleton_iff.2 hnpw.1,
          Set.mem_compl_singleton_iff.2 hnpw.2⟩
    have h2 : HarmonicAt (fun v : ℂ ↦ Real.log ‖v - ca‖) w := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun v : ℂ ↦ v - ca)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hwne'
    refine (harmonicAt_congr_nhds ?_).mp (h1.add h2)
    filter_upwards with v
    simp only [Pi.add_apply, Function.comp_apply, hu]
  obtain ⟨ρE, BE, hρE0, hEbd⟩ := hFpole
  set ρm : ℝ := min ρE ra with hρm
  have hρm0 : 0 < ρm := lt_min hρE0 hra
  have hρmra : ρm ≤ ra := min_le_right _ _
  have huharm' : HarmonicOnNhd u (ball ca ρm \ {ca}) := by
    intro w hw
    refine huharm w ⟨ball_subset_ball (by linarith only [hρmra, hra]) hw.1, hw.2⟩
  have hub : ∀ w ∈ ball ca ρm \ {ca}, |u w| ≤ BE := by
    intro w hw
    exact hEbd w ⟨ball_subset_ball (min_le_left _ _) hw.1, hw.2⟩
  obtain ⟨vloc, hvlocharm, hvloceq⟩ := exists_harmonicOnNhd_of_bounded_punctured
    hρm0 huharm' ⟨BE, hub⟩
  set hcomp : ℂ → ℝ := fun z ↦ if z = ca then vloc ca else u z with hhc
  have hcompharm : ∀ v ∈ ball ca (2 * ra), HarmonicAt hcomp v := by
    intro v hv
    by_cases hvc : v = ca
    · have hev : vloc =ᶠ[𝓝 v] hcomp := by
        have hvm : v ∈ ball ca ρm := by rw [hvc]; exact mem_ball_self hρm0
        filter_upwards [isOpen_ball.mem_nhds hvm] with z hz
        simp only [hhc]
        by_cases hzc : z = ca
        · rw [ite_eq_left hzc, hzc]
        · rw [ite_eq_right hzc]
          exact hvloceq ⟨hz, hzc⟩
      have hva : HarmonicAt vloc v := by
        rw [hvc]
        exact hvlocharm ca (mem_ball_self hρm0)
      exact (harmonicAt_congr_nhds hev).mp hva
    · have hopen : IsOpen (ball ca (2 * ra) ∩ {ca}ᶜ) :=
        isOpen_ball.inter isOpen_compl_singleton
      have hev : u =ᶠ[𝓝 v] hcomp := by
        filter_upwards [hopen.mem_nhds ⟨hv, hvc⟩] with z hz
        simp only [hhc]
        rw [ite_eq_right (Set.mem_compl_singleton_iff.1 hz.2)]
      exact (harmonicAt_congr_nhds hev).mp
        (huharm v ⟨hv, Set.mem_compl_singleton_iff.2 hvc⟩)
  have hcompval : ∀ w ∈ ball ca (2 * ra) \ {ca},
      hcomp w = Fd (⇑ea.symm w) + Real.log ‖w - ca‖ := by
    intro w hw
    have hwne' : w ≠ ca := by simpa using hw.2
    simp only [hhc]
    rw [ite_eq_right hwne']
  have hcompbd : ∀ w ∈ ball ca (2 * ra),
      |hcomp w| ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
    intro w hw
    set ρ' : ℝ := (max (dist w ca) ra + 2 * ra) / 2 with hρ'
    have hd2 : dist w ca < 2 * ra := mem_ball.1 hw
    have hmaxlt : max (dist w ca) ra < 2 * ra := by
      rw [max_lt_iff]
      exact ⟨hd2, by linarith only [hra]⟩
    have hρ'lt : ρ' < 2 * ra := by rw [hρ']; linarith only [hmaxlt]
    have hρ'gtra : ra < ρ' := by
      rw [hρ']
      have h1 : ra ≤ max (dist w ca) ra := le_max_right _ _
      linarith only [h1, hra]
    have hρ'0 : 0 < ρ' := lt_trans hra hρ'gtra
    have hwρ' : w ∈ ball ca ρ' := by
      rw [mem_ball, hρ']
      have h1 : dist w ca ≤ max (dist w ca) ra := le_max_left _ _
      linarith only [h1, hd2, hra]
    have hsubH : HarmonicOnNhd hcomp (closedBall ca ρ') := fun v hv ↦
      hcompharm v (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hv) hρ'lt))
    have hcl : ContinuousOn hcomp (closure (ball ca ρ')) := by
      rw [closure_ball ca hρ'0.ne']
      exact hsubH.continuousOn
    have hfrbd : ∀ ζ ∈ frontier (ball ca ρ'),
        |hcomp ζ| ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
      intro ζ hζ
      rw [frontier_ball ca hρ'0.ne'] at hζ
      have hζd : dist ζ ca = ρ' := mem_sphere.1 hζ
      have hζcb : ζ ∈ closedBall ca (2 * ra) := by
        rw [mem_closedBall, hζd]
        linarith only [hρ'lt]
      have hζne : ζ ≠ ca := by
        intro hcon
        rw [hcon, dist_self] at hζd
        linarith only [hζd, hρ'0]
      have hval : hcomp ζ = u ζ := by
        simp only [hhc]
        rw [ite_eq_right hζne]
      have hBs := hsB ζ hζcb (by rw [hζd]; linarith only [hρ'gtra])
      have h1 := hFbd (ea.symm ζ) hBs.1 hBs.2
      have hlogv : |Real.log ‖ζ - ca‖| ≤ |Real.log ra| + |Real.log (2 * ra)| := by
        have hn : ‖ζ - ca‖ = ρ' := by rw [← dist_eq_norm]; exact hζd
        rw [hn]
        have hl1 : Real.log ra ≤ Real.log ρ' := Real.log_le_log hra hρ'gtra.le
        have hl2 : Real.log ρ' ≤ Real.log (2 * ra) := Real.log_le_log hρ'0 hρ'lt.le
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (Real.log ra), abs_nonneg (Real.log (2 * ra))]
        · linarith [le_abs_self (Real.log (2 * ra)), abs_nonneg (Real.log ra)]
      rw [hval, hu]
      simp only
      calc |Fd (⇑ea.symm ζ) + Real.log ‖ζ - ca‖|
          ≤ |Fd (⇑ea.symm ζ)| + |Real.log ‖ζ - ca‖| := abs_add_le _ _
        _ ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
            linarith only [h1, hlogv]
    have hup := SubharmonicOn.le_of_frontier_le isOpen_ball isBounded_ball
      (HarmonicOnNhd.subharmonicOn
        (fun v hv ↦ hsubH v (ball_subset_closedBall hv)))
      hcl (fun ζ hζ ↦ le_trans (le_abs_self _) (hfrbd ζ hζ)) w hwρ'
    have hlow := SubharmonicOn.le_of_frontier_le isOpen_ball isBounded_ball
      (HarmonicOnNhd.subharmonicOn
        (harmNeg _ _ (fun v hv ↦ hsubH v (ball_subset_closedBall hv))))
      (by
        rw [closure_ball ca hρ'0.ne']
        exact (hsubH.continuousOn).neg)
      (fun ζ hζ ↦ le_trans (neg_le_abs _) (hfrbd ζ hζ)) w hwρ'
    rw [abs_le]
    constructor
    · linarith only [hlow]
    · exact hup
  exact ⟨hcomp, fun v hv ↦ hcompharm v hv, hcompval, hcompbd⟩

/-- The annulus log-barrier estimate: on the annulus between a shrunken disk and the fixed
three-quarter circle of the base disk, one dipole difference of piece Green's functions
exceeds another by at most the outer-circle gap plus a logarithmic barrier whose constant
is controlled by the exterior bound. -/
theorem pieceGreen_dipole_sub_le_log_barrier (D₀ : CoordDisk M) {p₁ p₂ : M} {r₁ r₂ C₀ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hC₀1 : 1 ≤ C₀)
    (htgt1 : closedBall (chartAt ℂ p₁ p₁) (2 * r₁) ⊆ (chartAt ℂ p₁).target)
    (htgt2 : closedBall (chartAt ℂ p₂ p₂) (2 * r₂) ⊆ (chartAt ℂ p₂).target)
    (hav1Car : ∀ w ∈ closedBall (chartAt ℂ p₁ p₁) (2 * r₁),
      (chartAt ℂ p₁).symm w ∉ D₀.closedCarrier)
    (hav1Ne : ∀ w ∈ closedBall (chartAt ℂ p₁ p₁) (2 * r₁),
      (chartAt ℂ p₁).symm w ≠ p₂)
    (hav2Car : ∀ w ∈ closedBall (chartAt ℂ p₂ p₂) (2 * r₂),
      (chartAt ℂ p₂).symm w ∉ D₀.closedCarrier)
    (hav2Disj : ∀ w ∈ closedBall (chartAt ℂ p₂ p₂) (2 * r₂),
      (chartAt ℂ p₂).symm w ∉
        (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) (2 * r₁))
    {tA tC tD : ℝ} (htA : 0 < tA) (htA1 : tA ≤ 1) (htA4 : tA ≤ 1 / 4)
    (htC : 0 < tC) (htC1 : tC ≤ 1) (htD : 0 < tD) (htD1 : tD ≤ 1)
    (hCA : (D₀.shrink tC htC htC1).closedCarrier ⊆
      (D₀.shrink tA htA htA1).closedCarrier)
    (hDA : (D₀.shrink tD htD htD1).closedCarrier ⊆
      (D₀.shrink tA htA htA1).closedCarrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdC : ∀ x : M,
      x ∉ (chartAt ℂ p₁).source ∩ ⇑(chartAt ℂ p₁) ⁻¹' ball (chartAt ℂ p₁ p₁)
          r₁ →
      x ∉ (chartAt ℂ p₂).source ∩ ⇑(chartAt ℂ p₂) ⁻¹' ball (chartAt ℂ p₂ p₂)
          r₂ →
      |pieceGreen (D₀.shrink tC htC htC1).compl p₁ x -
        pieceGreen (D₀.shrink tC htC htC1).compl p₂ x| ≤ C₀)
    (hbdD : ∀ x : M,
      x ∉ (chartAt ℂ p₁).source ∩ ⇑(chartAt ℂ p₁) ⁻¹' ball (chartAt ℂ p₁ p₁)
          r₁ →
      x ∉ (chartAt ℂ p₂).source ∩ ⇑(chartAt ℂ p₂) ⁻¹' ball (chartAt ℂ p₂ p₂)
          r₂ →
      |pieceGreen (D₀.shrink tD htD htD1).compl p₁ x -
        pieceGreen (D₀.shrink tD htD htD1).compl p₂ x| ≤ C₀)
    (hsph : ∀ z ∈ (chartAt ℂ D₀.center).symm ''
        sphere (chartAt ℂ D₀.center D₀.center) (3 * D₀.radius / 4),
      pieceGreen (D₀.shrink tC htC htC1).compl p₁ z -
        pieceGreen (D₀.shrink tC htC htC1).compl p₂ z -
        (pieceGreen (D₀.shrink tD htD htD1).compl p₁ z -
          pieceGreen (D₀.shrink tD htD htD1).compl p₂ z) ≤ ε)
    (x : M) (hxsrc : x ∈ (chartAt ℂ D₀.center).source)
    (hxlo : tA * D₀.radius <
      dist (chartAt ℂ D₀.center x) (chartAt ℂ D₀.center D₀.center))
    (hxhi : dist (chartAt ℂ D₀.center x) (chartAt ℂ D₀.center D₀.center) <
      3 * D₀.radius / 4) :
      pieceGreen (D₀.shrink tC htC htC1).compl p₁ x -
        pieceGreen (D₀.shrink tC htC htC1).compl p₂ x -
        (pieceGreen (D₀.shrink tD htD htD1).compl p₁ x -
          pieceGreen (D₀.shrink tD htD htD1).compl p₂ x) ≤
      ε + 4 * C₀ / (Real.log (3 * D₀.radius / 4) - Real.log (tA * D₀.radius)) *
        (Real.log (3 * D₀.radius / 4) -
          Real.log (dist (chartAt ℂ D₀.center x) (chartAt ℂ D₀.center D₀.center))) := by
  classical
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Plane-side helper: transfer of subharmonicity along a pointwise equality. -/
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
  /- ## Constancy propagation on a preconnected open set from an interior maximum. -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ z ∈ Ω, w z ≤ w xm) → ∀ z ∈ Ω, w z = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {z | z ∈ Ω ∧ w z = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hmax' : ∀ u ∈ Ω, w u ≤ w z := fun u hu ↦ (hmax u hu).trans_eq hzw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hzΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu.trans hzw⟩
    have hto : IsOpen {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hcont : ContinuousAt w z := (hwsub z hzΩ).continuousAt
      filter_upwards [hcont.eventually_ne hzw, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu⟩
    have hsub : Ω ⊆ {z | z ∈ Ω ∧ w z = w xm} ∪ {z | z ∈ Ω ∧ w z ≠ w xm} := by
      intro z hz
      by_cases hzw : w z = w xm
      · exact Or.inl ⟨hz, hzw⟩
      · exact Or.inr ⟨hz, hzw⟩
    have hdisj : Disjoint {z | z ∈ Ω ∧ w z = w xm} {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro z ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun z hz ↦ (hres hz).2
  /- ## Maximum principle on an open set `Ω ≠ univ` with compact exceptional set. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ z ∈ Ω, z ∉ Kc → w z ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ z ∈ Ω, w z ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ z ∈ Ω, w z ≤ w xm := by
      intro z hz
      by_cases hzK : z ∈ Kc
      · exact hxmax ⟨subset_closure hz, hzK⟩
      · exact (hout z hz hzK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun z hz ↦ hwsub z (hCcΩ hz)) (fun z hz ↦ hall z (hCcΩ hz))
    have hfrne :
        (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    have hne2 : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ ↦ (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ ↦ harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz ↦ (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz ↦ (hf0 _ ((hρsub hz).2)).symm
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Subharmonicity at a point transfers between the surface and an open piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hnety : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hnety := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hnety]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hnety).target :=
      e'.map_subtype_source hnety hzsrc
    have heqOn : Set.EqOn (⇑e'.symm) (Subtype.val ∘ ⇑(e'.subtypeRestr hnety).symm)
        (e'.subtypeRestr hnety).target := e'.subtypeRestr_symm_eqOn hnety
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hnety).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈ (e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw ↦ (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw ↦ (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hnety).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hnety), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hnety).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to the punctured filter of the surface. -/
  have mapval : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p, hpP⟩ : ↥P)) = 𝓝[≠] p := by
    intro P p hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀eq]; exact hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## Affine images of harmonic functions are harmonic. -/
  have mharmAffine : ∀ (g : M → ℝ) (x : M) (a c : ℝ), MHarmonicAt g x →
      MHarmonicAt (fun y ↦ a * g y + c) x := by
    intro g x a c hg
    have h1 : HarmonicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hg
    have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
    have heq2 : (a • (g ∘ (chartAt ℂ x).symm) + fun _ ↦ c) =
        (fun y ↦ a * g y + c) ∘ (chartAt ℂ x).symm := by
      funext w
      simp [smul_eq_mul]
    rw [heq2] at h2
    exact h2
  have mharmLin : ∀ (f g : M → ℝ) (a b : ℝ) (z : M), MHarmonicAt f z → MHarmonicAt g z →
      MHarmonicAt (fun y ↦ a * f y + b * g y) z := by
    intro f g a b z hf hg
    have h3 := (mharmAffine f z a 0 hf).add (mharmAffine g z b 0 hg)
    refine mharm_congr _ _ z (Filter.Eventually.of_forall fun y ↦ ?_) h3
    simp only [Pi.add_apply]
    ring
  /- ## The chart logarithm barrier: harmonicity and continuity off the singularity. -/
  have logHarm : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      MHarmonicAt (fun q ↦ Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hzs]
    have hharm : HarmonicAt (fun w : ℂ ↦ Real.log ‖w - c‖) (chartAt ℂ x₀ z) := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ ↦ w - c)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hzne
    have heqv : (fun w : ℂ ↦ Real.log ‖w - c‖) =ᶠ[𝓝 (chartAt ℂ x₀ z)]
        ((fun q ↦ Real.log (dist (chartAt ℂ x₀ q) c)) ∘ (chartAt ℂ x₀).symm) := by
      filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
        ((chartAt ℂ x₀).map_source hzs)] with w hw
      simp only [Function.comp_apply, (chartAt ℂ x₀).right_inv hw, dist_eq_norm]
    exact (harmonicAt_congr_nhds heqv).1 hharm
  have logCont : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      ContinuousAt (fun q ↦ Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    have h2 : ContinuousAt (chartAt ℂ x₀) z := (chartAt ℂ x₀).continuousAt hzs
    have h3 : dist (chartAt ℂ x₀ z) c ≠ 0 := (dist_pos.2 hzne).ne'
    exact (h2.dist continuousAt_const).log h3
  /- ## Membership through an inverse chart: closed balls and spheres. -/
  have hmemCB : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      closedBall c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' closedBall c s ↔ z ∈ e.source ∧ dist (e z) c ≤ s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_closedBall.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_closedBall.2 hzd, e.left_inv hzs⟩
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dite_eq_left ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dite_eq_right]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## The zero function belongs to every piece Green family. -/
  have zeroFam : ∀ (P : Opens M) (p : M) (hp : p ∈ P),
      (fun _ : ↥P ↦ (0 : ℝ)) ∈ greenFamily (⟨p, hp⟩ : ↥P) := by
    intro P p hp
    have : Nonempty ↥P := ⟨⟨p, hp⟩⟩
    refine ⟨fun z _ ↦ (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt,
      continuousOn_const, ⟨∅, isCompact_empty, Set.empty_ne_univ, fun z _ ↦ rfl⟩,
      ⟨0, ?_⟩⟩
    have hcont : ContinuousAt (poleCoord (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) := by
      have h1 : ContinuousAt (chartAt ℂ (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) :=
        (chartAt ℂ (⟨p, hp⟩ : ↥P)).continuousAt (mem_chart_source ℂ _)
      exact h1.sub continuousAt_const
    have h0 : poleCoord (⟨p, hp⟩ : ↥P) (⟨p, hp⟩ : ↥P) = 0 := sub_self _
    have hev : ∀ᶠ z in 𝓝 (⟨p, hp⟩ : ↥P), ‖poleCoord (⟨p, hp⟩ : ↥P) z‖ ≤ 1
        := by
      have h2 := hcont.tendsto
      rw [h0] at h2
      have h3 : closedBall (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ one_pos
      filter_upwards [h2 h3] with z hz
      rw [← dist_zero_right]
      exact mem_closedBall.1 hz
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
    have hlog := Real.log_nonpos (norm_nonneg _) hz
    simpa using hlog
  /- ## Zero extension of a piece candidate to the surface. -/
  have extendC : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (v : ↥P → ℝ),
      v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
      ∃ (vE : M → ℝ) (KE : Set M) (Cv : ℝ),
        (∀ z : ↥P, vE z = v z) ∧ MSubharmonicOn vE {p}ᶜ ∧ ContinuousOn vE {p}ᶜ ∧
        IsCompact KE ∧ KE ⊆ (P : Set M) ∧ (∀ y, y ∉ KE → vE y = 0) ∧
        ∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv := by
    intro P p hp v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y ↦ if h : y ∈ P then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥P, w z = v z := by
      intro z
      simp only [hwdef]
      rw [dite_eq_left z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (P : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ P
      · simp only [hwdef]
        rw [dite_eq_left hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dite_eq_right hyP]
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ P
      · have hoe : IsOpenEmbedding (Subtype.val : ↥P → M) :=
          P.2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥P) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥P)) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u ↦ (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥P → M) (𝓝 (⟨y, hyP⟩ : ↥P)) = 𝓝 y :=
          hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem ↦ hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ P
      · have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val P w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem ↦ hyP (hKwsub hmem)) (fun z hz ↦ hKwzero z hz)
    refine ⟨w, Kw, C, hwval, hwsub, hwcont, hKwcomp, hKwsub, hKwzero, ?_⟩
    rw [← mapval P p hp, Filter.eventually_map]
    filter_upwards [hC] with z hz
    have hpc : poleCoord (⟨p, hp⟩ : ↥P) z = poleCoord p (z : M) := rfl
    rw [hwval z, ← hpc]
    exact hz
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    have := hcs
    have := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon ↦ hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z ↦ pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## The center chart, the pieces and the pole-ball geometry. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D₀.center with he₀
  set c₀ : ℂ := e₀ D₀.center with hc₀
  set r₀ : ℝ := D₀.radius with hr₀def
  have hr₀ : 0 < r₀ := D₀.radius_pos
  have hcb₀tgt : closedBall c₀ r₀ ⊆ e₀.target := D₀.closedBall_subset
  have hcar₀ : D₀.closedCarrier = e₀.symm '' closedBall c₀ r₀ := rfl
  set ρs : ℝ := 3 * r₀ / 4 with hρs
  have hρs0 : 0 < ρs := by rw [hρs]; linarith only [hr₀]
  have hρsr₀ : ρs < r₀ := by rw [hρs]; linarith only [hr₀]
  set Γ₀ : Set M := e₀.symm '' sphere c₀ ρs with hΓ₀
  set PC : Opens M := (D₀.shrink tC htC htC1).compl with hPC
  set PD : Opens M := (D₀.shrink tD htD htD1).compl with hPD
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar1cp : IsCompact Car1 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono htgt1)
  have hCar2cp : IsCompact Car2 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₂.continuousOn_symm.mono htgt2)
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨hav1Car w hw, hav1Ne w hw⟩
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨hav2Car w hw, hav2Disj w hw⟩
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  set B₁ : Set M := e₁.source ∩ e₁ ⁻¹' ball c₁ r₁ with hB₁
  set B₂ : Set M := e₂.source ∩ e₂ ⁻¹' ball c₂ r₂ with hB₂
  have hp₁B₁ : p₁ ∈ B₁ :=
    ⟨hp₁src, by rw [Set.mem_preimage, ← hc₁]; exact mem_ball_self hr₁⟩
  have hp₂B₂ : p₂ ∈ B₂ :=
    ⟨hp₂src, by rw [Set.mem_preimage, ← hc₂]; exact mem_ball_self hr₂⟩
  have hB₁Car : B₁ ⊆ Car1 := by
    rintro x ⟨hxsrc, hxpre⟩
    rw [Set.mem_preimage] at hxpre
    exact ⟨e₁ x, ball_subset_closedBall (ball_subset_ball (by linarith only [hr₁]) hxpre),
      e₁.left_inv hxsrc⟩
  have hB₂Car : B₂ ⊆ Car2 := by
    rintro x ⟨hxsrc, hxpre⟩
    rw [Set.mem_preimage] at hxpre
    exact ⟨e₂ x, ball_subset_closedBall (ball_subset_ball (by linarith only [hr₂]) hxpre),
      e₂.left_inv hxsrc⟩
  have hp₁C : p₁ ∈ PC := fun hmem ↦ (hCar1av p₁ hp₁Car1).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htC1))) hmem)
  have hp₂C : p₂ ∈ PC := fun hmem ↦ (hCar2av p₂ hp₂Car2).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htC1))) hmem)
  have hp₁D : p₁ ∈ PD := fun hmem ↦ (hCar1av p₁ hp₁Car1).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htD1))) hmem)
  have hp₂D : p₂ ∈ PD := fun hmem ↦ (hCar2av p₂ hp₂Car2).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htD1))) hmem)
  have hconnC : ConnectedSpace ↥PC :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  have hncC : NoncompactSpace ↥PC := noncompactSpace_coordDisk_compl _
  have hconnD : ConnectedSpace ↥PD :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  have hncD : NoncompactSpace ↥PD := noncompactSpace_coordDisk_compl _
  have hGF1C : HasGreenFunction (⟨p₁, hp₁C⟩ : ↥PC) :=
    hasGreenFunction_coordDisk_compl _ p₁ hp₁C
  have hGF2C : HasGreenFunction (⟨p₂, hp₂C⟩ : ↥PC) :=
    hasGreenFunction_coordDisk_compl _ p₂ hp₂C
  have hGF1D : HasGreenFunction (⟨p₁, hp₁D⟩ : ↥PD) :=
    hasGreenFunction_coordDisk_compl _ p₁ hp₁D
  have hGF2D : HasGreenFunction (⟨p₂, hp₂D⟩ : ↥PD) :=
    hasGreenFunction_coordDisk_compl _ p₂ hp₂D
  have hcbtgtA : closedBall c₀ (tA * r₀) ⊆ e₀.target :=
    (closedBall_subset_closedBall (mul_le_of_le_one_left hr₀.le htA1)).trans hcb₀tgt
  have hcarmemA : ∀ z : M, z ∈ (D₀.shrink tA htA htA1).closedCarrier ↔
      z ∈ e₀.source ∧ dist (e₀ z) c₀ ≤ tA * r₀ := by
    intro z
    have hcarA : (D₀.shrink tA htA htA1).closedCarrier =
        e₀.symm '' closedBall c₀ (tA * r₀) := rfl
    rw [hcarA]
    exact hmemCB e₀ c₀ (tA * r₀) hcbtgtA z
  have hδltA : tA * r₀ < ρs := by
    have h2 : tA * r₀ ≤ 1 / 4 * r₀ := mul_le_mul_of_nonneg_right htA4 hr₀.le
    rw [hρs]
    linarith only [h2, hr₀]
  have hdenA0 : 0 < Real.log ρs - Real.log (tA * r₀) := by
    have h1 : Real.log (tA * r₀) < Real.log ρs := by
      apply Real.log_lt_log
      · exact mul_pos htA hr₀
      · exact hδltA
    linarith only [h1]
  set δA : ℝ := tA * r₀ with hδA
  have hδA0 : 0 < δA := by
    rw [hδA]
    exact mul_pos htA hr₀
  have hδAρ : δA < ρs := hδltA
  have hdenA : 0 < Real.log ρs - Real.log δA := hdenA0
  set η : ℝ := 4 * C₀ / (Real.log ρs - Real.log δA) with hη
  have hη0 : 0 < η := by
    rw [hη]
    exact div_pos (by linarith only [hC₀1]) hdenA
  have hcancel : η * (Real.log ρs - Real.log δA) = 4 * C₀ := by
    rw [hη]
    exact div_mul_cancel₀ _ hdenA.ne'
  set L : M → ℝ := fun q ↦ Real.log ρs - Real.log (dist (e₀ q) c₀) with hL
  set W : M → ℝ := fun q ↦ pieceGreen (PC) p₂ q +
    (pieceGreen (PD) p₁ q - pieceGreen (PD) p₂ q) + (ε + η * L q) with hW
  set Ωσ : Set M := e₀.symm '' (ball c₀ ρs \ closedBall c₀ δA) with hΩσ
  have hΩσsub : ball c₀ ρs \ closedBall c₀ δA ⊆ e₀.target :=
    (Set.sdiff_subset.trans ball_subset_closedBall).trans
      ((closedBall_subset_closedBall hρsr₀.le).trans hcb₀tgt)
  have hΩσopen : IsOpen Ωσ := by
    rw [hΩσ, himg e₀ _ hΩσsub]
    exact e₀.isOpen_inter_preimage (isOpen_ball.sdiff isClosed_closedBall)
  have hΩσmem : ∀ z ∈ Ωσ, z ∈ e₀.source ∧ δA < dist (e₀ z) c₀ ∧
      dist (e₀ z) c₀ < ρs := by
    intro z hz
    rw [hΩσ, himg e₀ _ hΩσsub] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall] at hz2
    exact ⟨hz1, not_le.1 hz2.2, hz2.1⟩
  have hΩσmem' : ∀ z : M, z ∈ e₀.source → δA < dist (e₀ z) c₀ →
      dist (e₀ z) c₀ < ρs → z ∈ Ωσ := by
    intro z hz1 hz2 hz3
    rw [hΩσ, himg e₀ _ hΩσsub]
    refine ⟨hz1, ?_⟩
    rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall]
    exact ⟨hz3, not_le.2 hz2⟩
  set Kσ : Set M := e₀.symm '' (closedBall c₀ ρs \ ball c₀ δA) with hKσ
  have hKσtgt : closedBall c₀ ρs \ ball c₀ δA ⊆ e₀.target :=
    Set.sdiff_subset.trans ((closedBall_subset_closedBall hρsr₀.le).trans hcb₀tgt)
  have hKσcomp : IsCompact Kσ :=
    ((isCompact_closedBall c₀ ρs).diff isOpen_ball).image_of_continuousOn
      (e₀.continuousOn_symm.mono hKσtgt)
  have hΩσKσ : Ωσ ⊆ Kσ := by
    rw [hΩσ, hKσ]
    exact Set.image_mono (fun w hw ↦ ⟨ball_subset_closedBall hw.1,
      fun h ↦ hw.2 (ball_subset_closedBall h)⟩)
  have hcenΩσ : D₀.center ∉ Ωσ := by
    intro hcon
    obtain ⟨-, h2, -⟩ := hΩσmem _ hcon
    rw [← hc₀, dist_self] at h2
    exact absurd h2 (not_lt.2 hδA0.le)
  have hΩσne : Ωσ ≠ Set.univ := by
    intro hcon
    apply hcenΩσ
    rw [hcon]
    trivial
  have hΩσCar : ∀ z ∈ Ωσ, z ∈ D₀.closedCarrier := by
    intro z hz
    obtain ⟨hz1, -, hz3⟩ := hΩσmem z hz
    rw [hcar₀]
    exact ⟨e₀ z, mem_closedBall.2 (by linarith only [hz3, hρsr₀]), e₀.left_inv hz1⟩
  have hΩσB : ∀ z ∈ Ωσ, z ∉ B₁ ∧ z ∉ B₂ := by
    intro z hz
    constructor
    · intro hmem
      exact (hCar1av z (hB₁Car hmem)).1 (hΩσCar z hz)
    · intro hmem
      exact (hCar2av z (hB₂Car hmem)).1 (hΩσCar z hz)
  have hΩσnp : ∀ z ∈ Ωσ, z ≠ p₁ ∧ z ≠ p₂ := by
    intro z hz
    constructor
    · intro hcon
      exact (hΩσB z hz).1 (hcon ▸ hp₁B₁)
    · intro hcon
      exact (hΩσB z hz).2 (hcon ▸ hp₂B₂)
  have hΩσW : ∀ z ∈ Ωσ, z ∈ PC ∧ z ∈ PD := by
    intro z hz
    obtain ⟨hz1, hz2, -⟩ := hΩσmem z hz
    have hnotA : z ∉ (D₀.shrink tA htA htA1).closedCarrier := by
      intro hmem
      have h3 := ((hcarmemA z).1 hmem).2
      linarith only [hδA, h3, hz2]
    exact ⟨fun hmem ↦ hnotA (hCA hmem), fun hmem ↦ hnotA (hDA hmem)⟩
  have hWharm : ∀ z ∈ Ωσ, MHarmonicAt W z := by
    intro z hz
    obtain ⟨hzsrc, hzlo, hzhi⟩ := hΩσmem z hz
    obtain ⟨hzC, hzD⟩ := hΩσW z hz
    obtain ⟨hznp₁, hznp₂⟩ := hΩσnp z hz
    have h1 : MHarmonicAt (pieceGreen (PC) p₂) z :=
      pgharm (PC) p₂ hp₂C hconnC hncC hGF2C z hzC hznp₂
    have h2 : MHarmonicAt (pieceGreen (PD) p₁) z :=
      pgharm (PD) p₁ hp₁D hconnD hncD hGF1D z hzD hznp₁
    have h3 : MHarmonicAt (pieceGreen (PD) p₂) z :=
      pgharm (PD) p₂ hp₂D hconnD hncD hGF2D z hzD hznp₂
    have hzcne : e₀ z ≠ c₀ := by
      intro hcon
      rw [hcon, dist_self] at hzlo
      exact absurd hzlo (not_lt.2 hδA0.le)
    have h4 : MHarmonicAt (fun q ↦ Real.log (dist (e₀ q) c₀)) z :=
      logHarm D₀.center c₀ z hzsrc hzcne
    have h5 := mharmLin _ _ 1 (-1) z h2 h3
    have h6 := mharmLin _ _ 1 1 z h1 h5
    have h7 := mharmAffine _ z (-η) (ε + η * Real.log ρs) h4
    have h8 := mharmLin _ _ 1 1 z h6 h7
    refine mharm_congr _ _ z (Filter.Eventually.of_forall fun y ↦ ?_) h8
    simp only [hW, hL]
    ring
  have hxΩσ : x ∈ Ωσ := hΩσmem' x hxsrc (by linarith only [hδA, hxlo]) hxhi
  have hxWC : x ∈ PC := (hΩσW x hxΩσ).1
  have hbddCC := (mharmonicOn_greenEnvelope hGF1C).2
  have hkey : pieceGreen (PC) p₁ x ≤ W x := by
    rw [pgval (PC) p₁ hp₁C x hxWC]
    simp only [greenEnvelope]
    refine csSup_le
      ⟨0, (fun _ : ↥(PC) ↦ (0 : ℝ)), zeroFam (PC) p₁ hp₁C, rfl⟩ ?_
    rintro b ⟨v, hv, rfl⟩
    obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
      extendC (PC) p₁ hp₁C v hv
    have hpairv : ∀ z : M, z ∉ B₁ → z ∉ B₂ →
        vE z - pieceGreen (PC) p₂ z ≤ C₀ := by
      intro z hz1 hz2
      have hznp₁ : z ≠ p₁ := fun hcon ↦ hz1 (hcon ▸ hp₁B₁)
      by_cases hzP : z ∈ PC
      · have h1 : vE z ≤ pieceGreen (PC) p₁ z := by
          have h2 : v ⟨z, hzP⟩ ≤ greenEnvelope (⟨p₁, hp₁C⟩ : ↥PC) ⟨z, hzP⟩ :=
            le_csSup (hbddCC _ (fun hcon ↦ hznp₁ (congrArg Subtype.val hcon)))
              ⟨v, hv, rfl⟩
          rw [pgval (PC) p₁ hp₁C z hzP]
          calc vE z = v ⟨z, hzP⟩ := hvEval ⟨z, hzP⟩
            _ ≤ _ := h2
        have h3 := (abs_le.1 (hbdC z hz1 hz2)).2
        linarith only [h1, h3]
      · have h1 : vE z = 0 := hKE0 z (fun hmem ↦ hzP (hKEP hmem))
        have h2 : pieceGreen (PC) p₂ z = 0 := pgzero _ _ _ hzP
        rw [h1, h2]
        linarith only [hC₀1]
    set wc : M → ℝ := fun z ↦ max (vE z - W z) 0 with hwc
    have hwcsub : MSubharmonicOn wc Ωσ := by
      intro z hz
      have h1 : MSubharmonicAt (fun q ↦ vE q - W q) z :=
        (hvEsub z (Set.mem_compl_singleton_iff.2 (hΩσnp z hz).1)).sub_mharmonicAt
          (hWharm z hz)
      have h2 : MSubharmonicAt (fun _ : M ↦ (0 : ℝ)) z :=
        (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt
      rw [hwc]
      exact h1.max h2
    have hwcout : ∀ z ∈ Ωσ, z ∉ Kσ → wc z ≤ 0 := by
      intro z hz hzK
      exact absurd (hΩσKσ hz) hzK
    have hwcfr : ∀ y ∈ closure Ωσ \ Ωσ, ContinuousAt wc y ∧ wc y ≤ 0 := by
      rintro y ⟨hycl, hyΩ⟩
      have hyK : y ∈ Kσ := (hKσcomp.isClosed.closure_subset_iff.2 hΩσKσ) hycl
      rw [hKσ] at hyK
      obtain ⟨w, ⟨hw1, hw2⟩, hwy⟩ := hyK
      have hwt : w ∈ e₀.target := hKσtgt ⟨hw1, hw2⟩
      have hysrc : y ∈ e₀.source := hwy ▸ e₀.map_target hwt
      have hyval : e₀ y = w := by rw [← hwy, e₀.right_inv hwt]
      have hyd1 : δA ≤ dist (e₀ y) c₀ := by
        rw [hyval]
        exact not_lt.1 (fun h ↦ hw2 (mem_ball.2 h))
      have hyd2 : dist (e₀ y) c₀ ≤ ρs := by
        rw [hyval]
        exact mem_closedBall.1 hw1
      have hyCar : y ∈ D₀.closedCarrier := by
        rw [hcar₀]
        exact ⟨e₀ y, mem_closedBall.2 (by linarith only [hyd2, hρsr₀]),
          e₀.left_inv hysrc⟩
      have hyB₁ : y ∉ B₁ := fun hmem ↦ (hCar1av y (hB₁Car hmem)).1 hyCar
      have hyB₂ : y ∉ B₂ := fun hmem ↦ (hCar2av y (hB₂Car hmem)).1 hyCar
      have hynp₁ : y ≠ p₁ := fun hcon ↦ hyB₁ (hcon ▸ hp₁B₁)
      have hynp₂ : y ≠ p₂ := fun hcon ↦ hyB₂ (hcon ▸ hp₂B₂)
      have hycne : e₀ y ≠ c₀ := by
        intro hcon
        rw [hcon, dist_self] at hyd1
        exact absurd hyd1 (not_le.2 hδA0)
      have hydisj : dist (e₀ y) c₀ = δA ∨ dist (e₀ y) c₀ = ρs := by
        rcases lt_or_eq_of_le hyd1 with h1 | h1
        · rcases lt_or_eq_of_le hyd2 with h2 | h2
          · exact absurd (hΩσmem' y hysrc h1 h2) hyΩ
          · exact Or.inr h2
        · exact Or.inl h1.symm
      have hLcont : ContinuousAt (fun q ↦ Real.log (dist (e₀ q) c₀)) y :=
        logCont D₀.center c₀ y hysrc hycne
      rcases hydisj with hyd | hyd
      · -- the inner circle: the capped competitor vanishes on a neighbourhood
        have hcbar : ContinuousAt (fun q : M ↦ 2 * C₀ - ε - η *
            (Real.log ρs - Real.log (dist (e₀ q) c₀))) y :=
          continuousAt_const.sub
            (continuousAt_const.mul (continuousAt_const.sub hLcont))
        have hcbarneg : 2 * C₀ - ε - η *
            (Real.log ρs - Real.log (dist (e₀ y) c₀)) < 0 := by
          rw [hyd]
          linarith only [hcancel, hε, hC₀1]
        have havoid : IsOpen ((Car1 ∪ Car2)ᶜ : Set M) :=
          (hCar1cp.union hCar2cp).isClosed.isOpen_compl
        have hyav : y ∈ ((Car1 ∪ Car2)ᶜ : Set M) := by
          rintro (h | h)
          · exact (hCar1av y h).1 hyCar
          · exact (hCar2av y h).1 hyCar
        have hev : ∀ᶠ z in 𝓝 y, wc z = 0 := by
          filter_upwards [havoid.mem_nhds hyav,
            hcbar.tendsto.eventually_lt_const hcbarneg] with z hzav hzneg
          have hz1 : z ∉ B₁ := fun hmem ↦ hzav (Or.inl (hB₁Car hmem))
          have hz2 : z ∉ B₂ := fun hmem ↦ hzav (Or.inr (hB₂Car hmem))
          have h1 := hpairv z hz1 hz2
          have h2 := (abs_le.1 (hbdD z hz1 hz2)).1
          have hle : vE z - W z ≤ 0 := by
            simp only [hW, hL]
            linarith only [h1, h2, hzneg]
          rw [hwc]
          simp only
          rw [max_eq_right hle]
        refine ⟨continuousAt_const.congr_of_eventuallyEq hev, ?_⟩
        rw [hev.self_of_nhds]
      · -- the outer circle: the sphere hypothesis applies
        have hyΓ₀ : y ∈ Γ₀ := by
          rw [hΓ₀]
          exact ⟨e₀ y, mem_sphere.2 hyd, e₀.left_inv hysrc⟩
        have hnotA : y ∉ (D₀.shrink tA htA htA1).closedCarrier := by
          intro hmem
          have h3 := ((hcarmemA y).1 hmem).2
          rw [hyd] at h3
          linarith only [hδA, h3, hδAρ]
        have hyWC : y ∈ PC := fun hmem ↦ hnotA (hCA hmem)
        have hyWD : y ∈ PD := fun hmem ↦ hnotA (hDA hmem)
        have hcv : ContinuousAt vE y := hvEcont.continuousAt
          (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hynp₁))
        have hcg1 : ContinuousAt (pieceGreen (PC) p₂) y :=
          (pgharm (PC) p₂ hp₂C hconnC hncC hGF2C
            y hyWC hynp₂).continuousAt
        have hcg2 : ContinuousAt (pieceGreen (PD) p₁) y :=
          (pgharm (PD) p₁ hp₁D hconnD hncD hGF1D
            y hyWD hynp₁).continuousAt
        have hcg3 : ContinuousAt (pieceGreen (PD) p₂) y :=
          (pgharm (PD) p₂ hp₂D hconnD hncD hGF2D
            y hyWD hynp₂).continuousAt
        have hcW : ContinuousAt W y :=
          (hcg1.add (hcg2.sub hcg3)).add
            (continuousAt_const.add
              (continuousAt_const.mul (continuousAt_const.sub hLcont)))
        have h1 : vE y ≤ pieceGreen (PC) p₁ y := by
          have h2 : v ⟨y, hyWC⟩ ≤ greenEnvelope (⟨p₁, hp₁C⟩ : ↥PC) ⟨y, hyWC⟩ :=
            le_csSup (hbddCC _ (fun hcon ↦ hynp₁ (congrArg Subtype.val hcon)))
              ⟨v, hv, rfl⟩
          rw [pgval (PC) p₁ hp₁C y hyWC]
          calc vE y = v ⟨y, hyWC⟩ := hvEval ⟨y, hyWC⟩
            _ ≤ _ := h2
        have h2 := hsph y hyΓ₀
        refine ⟨by rw [hwc]; exact (hcv.sub hcW).max continuousAt_const, ?_⟩
        rw [hwc]
        simp only
        apply max_le _ le_rfl
        simp only [hW, hL]
        rw [hyd, sub_self, mul_zero]
        linarith only [h1, h2]
    have hwcle := maxPrin Ωσ wc 0 Kσ hΩσopen hΩσne hwcsub hKσcomp hwcout hwcfr
    have h9 := hwcle x hxΩσ
    rw [hwc] at h9
    simp only at h9
    have h10 : vE x - W x ≤ 0 := le_trans (le_max_left _ _) h9
    change v ⟨x, hxWC⟩ ≤ W x
    have h11 : v ⟨x, hxWC⟩ = vE x := (hvEval ⟨x, hxWC⟩).symm
    rw [h11]
    linarith only [h10]
  have hfin : pieceGreen PC p₁ x - pieceGreen PC p₂ x -
      (pieceGreen PD p₁ x - pieceGreen PD p₂ x) ≤ ε + η * L x := by
    simp only [hW] at hkey
    linarith only [hkey]
  simp only [hL] at hfin
  rw [hη] at hfin
  exact hfin

end RiemannDynamics
