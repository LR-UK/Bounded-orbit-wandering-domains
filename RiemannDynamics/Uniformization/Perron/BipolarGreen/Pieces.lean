/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreensFunction.Injective
import RiemannDynamics.Uniformization.Perron.Myrberg.Transfer

/-!
# Bipolar Green: coordinate disks and hyperbolic pieces

First file of the bipolar Green construction, the non-hyperbolic half of the
planarity theorem: a surface without a Green's function (or a compact
surface) is exhausted by the complements of a shrinking closed coordinate
disk, and the dipole limit of the piece Green's functions embeds it onto a
domain of `ℂ̂`. This file removes a closed coordinate disk from the surface
and shows the complementary piece is connected, noncompact, and hyperbolic.

## Main definitions

* `CoordDisk` — a closed coordinate disk, with `CoordDisk.shrink`,
  `CoordDisk.closedCarrier`, and the complementary piece `CoordDisk.compl`;
* `pieceGreen` — the Green's function of a piece, as a function on the
  surface.

## Main statements

* `isConnected_coordDisk_compl`, `noncompactSpace_coordDisk_compl` — the
  pieces are connected and noncompact;
* `hasGreenFunction_coordDisk_compl` — every piece is hyperbolic.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A closed coordinate disk on a surface: a center together with a radius
whose closed chart ball lies inside the chart target. -/
structure CoordDisk (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] where
  /-- The center of the disk. -/
  center : M
  /-- The chart radius of the disk. -/
  radius : ℝ
  /-- The radius is positive, so the disk is not degenerate. -/
  radius_pos : 0 < radius
  /-- The closed chart ball of the given radius lies inside the chart target, so the
  inverse chart is defined on all of it. -/
  closedBall_subset :
    closedBall (chartAt ℂ center center) radius ⊆ (chartAt ℂ center).target

namespace CoordDisk

variable (D : CoordDisk M)

/-- The closed disk on the surface: the inverse-chart image of the closed
chart ball. -/
def closedCarrier : Set M :=
  (chartAt ℂ D.center).symm '' closedBall (chartAt ℂ D.center D.center) D.radius

/-- Shrinking a coordinate disk by a factor `t ∈ (0, 1]`. -/
def shrink (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : CoordDisk M where
  center := D.center
  radius := t * D.radius
  radius_pos := mul_pos ht D.radius_pos
  closedBall_subset :=
    (closedBall_subset_closedBall
      (by nlinarith [D.radius_pos])).trans D.closedBall_subset

/-- The closed disk of a coordinate disk is compact: it is the image of a compact closed ball of
`ℂ` under the inverse chart, which is continuous on the chart target. -/
theorem isCompact_closedCarrier : IsCompact D.closedCarrier :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt ℂ D.center).continuousOn_symm.mono D.closedBall_subset)

/-- The complementary piece of a coordinate disk, as an open set of the
surface. -/
def compl [T2Space M] : Opens M :=
  ⟨D.closedCarrierᶜ, D.isCompact_closedCarrier.isClosed.isOpen_compl⟩

end CoordDisk

variable [IsManifold 𝓘(ℂ) ω M]

/-- The Green's function of an open piece of the surface, read as a function on the
surface: the Perron upper envelope `greenEnvelope` computed inside `P`, extended by
zero when the pole or the argument leaves the piece. It is the Green's function
proper only where the piece is hyperbolic at `p`; on a non-hyperbolic piece the
envelope is a supremum of an unbounded set (see
`not_bddAbove_image_greenFamily_of_compactSpace`) and carries no such meaning. Every use
below is on a `CoordDisk.compl`, which `hasGreenFunction_coordDisk_compl` shows is
hyperbolic. -/
noncomputable def pieceGreen (P : Opens M) (p x : M) : ℝ :=
  open scoped Classical in
  if h : p ∈ P ∧ x ∈ P then greenEnvelope (⟨p, h.1⟩ : ↥P) ⟨x, h.2⟩ else 0

variable [T2Space M] [ConnectedSpace M]

/-! ### The pieces are hyperbolic -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- Removing a closed coordinate disk keeps the surface connected. -/
theorem isConnected_coordDisk_compl (D : CoordDisk M) :
    IsConnected (D.compl : Set M) := by
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center
  set c : ℂ := e D.center
  set r : ℝ := D.radius
  have hr : 0 < r := D.radius_pos
  have hsub : closedBall c r ⊆ e.target := D.closedBall_subset
  have hcarrier : D.closedCarrier = e.symm '' closedBall c r := rfl
  have hcompl : (D.compl : Set M) = D.closedCarrierᶜ := rfl
  -- A collar radius: a slightly larger open chart ball still inside the target.
  obtain ⟨δ, hδ0, hδsub⟩ :=
    (isCompact_closedBall c r).exists_thickening_subset_open e.open_target hsub
  set R : ℝ := δ + r with hRdef
  have hrR : r < R := lt_add_of_pos_left r hδ0
  have hballR : ball c R ⊆ e.target := by
    rw [hRdef, ← thickening_closedBall hδ0 hr.le c]
    exact hδsub
  -- The open chart annulus is connected, via polar coordinates.
  have hann : IsConnected (ball c R \ closedBall c r) := by
    have hcont : Continuous fun p : ℝ × ℝ ↦
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ ↦ c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo r R ×ˢ (Set.univ : Set ℝ)) = ball c R \ closedBall c r := by
      apply Set.Subset.antisymm
      · rintro w ⟨⟨t, θ⟩, ⟨⟨hrt, htR⟩, -⟩, hw⟩
        rw [← hw]
        change c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball c R \ closedBall c r
        have hd : dist (c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) c = t := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg (hr.le.trans hrt.le)]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, hd]; exact htR
        · intro hmem
          rw [mem_closedBall, hd] at hmem
          exact absurd hmem (not_le.2 hrt)
      · rintro w ⟨hwb, hwc⟩
        have hrt : r < ‖w - c‖ := by
          rw [← dist_eq_norm]
          exact not_le.1 fun h ↦ hwc (mem_closedBall.2 h)
        have htR : ‖w - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hwb
        refine ⟨(‖w - c‖, (w - c).arg), ⟨⟨hrt, htR⟩, Set.mem_univ _⟩, ?_⟩
        change c + (‖w - c‖ : ℂ) * Complex.exp (((w - c).arg : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    have hmid : (r + R) / 2 ∈ Set.Ioo r R := ⟨by linarith, by linarith⟩
    rw [← himg]
    exact ⟨Set.Nonempty.image _ ⟨((r + R) / 2, 0), hmid, Set.mem_univ _⟩,
      (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn⟩
  -- The chart-ball neighborhood of the closed disk.
  set N : Set M := e.source ∩ e ⁻¹' ball c R
  have hNopen : IsOpen N := e.isOpen_inter_preimage isOpen_ball
  have hcN : D.closedCarrier ⊆ N := by
    intro x hx
    rw [hcarrier] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hwt : w ∈ e.target := hsub hw
    refine ⟨e.map_target hwt, ?_⟩
    rw [Set.mem_preimage, e.right_inv hwt]
    exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hw) hrR)
  -- The image of the annulus is `N` minus the closed disk.
  have himgA : (e.symm : ℂ → M) '' (ball c R \ closedBall c r) = N \ D.closedCarrier := by
    apply Set.Subset.antisymm
    · rintro x ⟨w, ⟨hwb, hwc⟩, rfl⟩
      have hwt : w ∈ e.target := hballR hwb
      refine ⟨⟨e.map_target hwt, ?_⟩, ?_⟩
      · rw [Set.mem_preimage, e.right_inv hwt]; exact hwb
      · rw [hcarrier]
        rintro ⟨w', hw', hw'e⟩
        have hw't : w' ∈ e.target := hsub hw'
        have h2 : e (e.symm w') = e (e.symm w) := by rw [hw'e]
        rw [e.right_inv hw't, e.right_inv hwt] at h2
        exact hwc (h2 ▸ hw')
    · rintro x ⟨⟨hxsrc, hxb⟩, hxc⟩
      rw [Set.mem_preimage] at hxb
      refine ⟨e x, ⟨hxb, fun hmem ↦ hxc ?_⟩, e.left_inv hxsrc⟩
      rw [hcarrier]
      exact ⟨e x, hmem, e.left_inv hxsrc⟩
  have hA : IsConnected (N \ D.closedCarrier) := by
    rw [← himgA]
    exact hann.image _ (e.continuousOn_symm.mono fun w hw ↦ hballR hw.1)
  have hsub' : N \ D.closedCarrier ⊆ D.closedCarrierᶜ := fun z hz ↦ hz.2
  rw [hcompl]
  have hopen : IsOpen (D.closedCarrierᶜ) := D.isCompact_closedCarrier.isClosed.isOpen_compl
  have hcenter : D.center ∈ D.closedCarrier := by
    rw [hcarrier]
    exact ⟨c, mem_closedBall_self hr.le, e.left_inv (mem_chart_source ℂ D.center)⟩
  have hne : (D.closedCarrierᶜ : Set M).Nonempty := by
    obtain ⟨z, hz⟩ := hA.nonempty
    exact ⟨z, hsub' hz⟩
  refine ⟨hne, ?_⟩
  intro u v hu hv huv hsu hsv
  -- One-sided separation lemma: if the surface annulus lies in `u'`, the
  -- separation `u', v'` of the piece extends to a separation of `M`.
  have key : ∀ u' v' : Set M, IsOpen u' → IsOpen v' → D.closedCarrierᶜ ⊆ u' ∪ v' →
      (D.closedCarrierᶜ ∩ v').Nonempty → N \ D.closedCarrier ⊆ u' →
      (D.closedCarrierᶜ ∩ (u' ∩ v')).Nonempty := by
    intro u' v' hu' hv' hcov hv'ne hNu'
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hU : IsOpen (u' ∪ N) := hu'.union hNopen
    have hV : IsOpen (v' ∩ D.closedCarrierᶜ) := hv'.inter hopen
    have hcover : (Set.univ : Set M) ⊆ (u' ∪ N) ∪ v' ∩ D.closedCarrierᶜ := by
      intro z _
      by_cases hz : z ∈ D.closedCarrier
      · exact Or.inl (Or.inr (hcN hz))
      · rcases hcov hz with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hz⟩
    obtain ⟨w, hw1, hw2⟩ := hv'ne
    obtain ⟨z, -, hz⟩ := isPreconnected_univ (u' ∪ N) (v' ∩ D.closedCarrierᶜ) hU hV hcover
      ⟨D.center, Set.mem_univ _, Or.inr (hcN hcenter)⟩ ⟨w, Set.mem_univ w, hw2, hw1⟩
    obtain ⟨hz1, hzv, hzc⟩ := hz
    have hzu : z ∈ u' := by
      rcases hz1 with h | h
      · exact h
      · exact hNu' ⟨h, hzc⟩
    have hmem : z ∈ D.closedCarrierᶜ ∩ (u' ∩ v') := ⟨hzc, hzu, hzv⟩
    rw [hcon] at hmem
    exact hmem
  -- Case split on which side of the separation the surface annulus lies.
  rcases Set.eq_empty_or_nonempty ((N \ D.closedCarrier) ∩ v) with hv0 | hv1
  · have hNu : N \ D.closedCarrier ⊆ u := by
      intro z hz
      rcases huv (hsub' hz) with h | h
      · exact h
      · exact absurd hv0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
    exact key u v hu hv huv hsv hNu
  · rcases Set.eq_empty_or_nonempty ((N \ D.closedCarrier) ∩ u) with hu0 | hu1
    · have hNv : N \ D.closedCarrier ⊆ v := by
        intro z hz
        rcases huv (hsub' hz) with h | h
        · exact absurd hu0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
        · exact h
      have h := key v u hv hu (by rw [Set.union_comm]; exact huv) hsu hNv
      rwa [Set.inter_comm v u] at h
    · obtain ⟨z, hzN, hzuv⟩ := hA.2 u v hu hv (fun z hz ↦ huv (hsub' hz)) hu1 hv1
      exact ⟨z, hsub' hzN, hzuv⟩

omit [IsManifold 𝓘(ℂ) ω M] in
/-- The complement of a closed coordinate disk is noncompact: points near the
removed boundary circle escape every compact subset of the piece. -/
theorem noncompactSpace_coordDisk_compl (D : CoordDisk M) :
    NoncompactSpace ↥D.compl := by
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center
  set c : ℂ := e D.center
  set r : ℝ := D.radius
  have hr : 0 < r := D.radius_pos
  have hsub : closedBall c r ⊆ e.target := D.closedBall_subset
  have hcarrier : D.closedCarrier = e.symm '' closedBall c r := rfl
  have hcompl : (D.compl : Set M) = D.closedCarrierᶜ := rfl
  -- A collar radius: a slightly larger open chart ball still inside the target.
  obtain ⟨δ, hδ0, hδsub⟩ :=
    (isCompact_closedBall c r).exists_thickening_subset_open e.open_target hsub
  set R : ℝ := δ + r with hRdef
  have hrR : r < R := lt_add_of_pos_left r hδ0
  have hballR : ball c R ⊆ e.target := by
    rw [hRdef, ← thickening_closedBall hδ0 hr.le c]
    exact hδsub
  -- A collar point of the complement, at chart radius `(r + R) / 2`.
  set w₀ : ℂ := c + (((r + R) / 2 : ℝ) : ℂ) with hw₀def
  have hd₀ : dist w₀ c = (r + R) / 2 := by
    rw [hw₀def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hw₀ball : w₀ ∈ ball c R := by rw [mem_ball, hd₀]; linarith
  have hw₀t : w₀ ∈ e.target := hballR hw₀ball
  have hx₀ : e.symm w₀ ∈ D.closedCarrierᶜ := by
    intro hmem
    rw [hcarrier] at hmem
    obtain ⟨w', hw', hw'e⟩ := hmem
    have hw't : w' ∈ e.target := hsub hw'
    have h2 : e (e.symm w') = e (e.symm w₀) := by rw [hw'e]
    rw [e.right_inv hw't, e.right_inv hw₀t] at h2
    rw [h2, mem_closedBall, hd₀] at hw'
    linarith
  -- A compact piece would be clopen and nonempty, hence the whole connected
  -- surface — but the disk center is outside the piece.
  rw [← not_compactSpace_iff]
  intro hcomp
  have hK : IsCompact (D.compl : Set M) := by
    rw [isCompact_iff_compactSpace]
    exact hcomp
  have hclopen : IsClopen (D.compl : Set M) := ⟨hK.isClosed, D.compl.isOpen⟩
  have huniv : (D.compl : Set M) = Set.univ :=
    hclopen.eq_univ ⟨e.symm w₀, by rw [hcompl]; exact hx₀⟩
  have hcenter : D.center ∈ D.closedCarrier := by
    rw [hcarrier]
    exact ⟨c, mem_closedBall_self hr.le, e.left_inv (mem_chart_source ℂ D.center)⟩
  have hmem : D.center ∈ (D.compl : Set M) := huniv ▸ Set.mem_univ D.center
  rw [hcompl] at hmem
  exact hmem hcenter

/-- **Every piece is hyperbolic**: the complement of a closed coordinate disk
carries a Green's function at every pole, by the harmonic-measure estimate on
the collar between the removed circle and a pole disk. -/
theorem hasGreenFunction_coordDisk_compl (D : CoordDisk M) (p : M)
    (hp : p ∈ D.compl) : HasGreenFunction (⟨p, hp⟩ : ↥D.compl) := by
  classical
  -- ## Instances on the piece
  have hconnN : ConnectedSpace ↥D.compl :=
    Subtype.connectedSpace (isConnected_coordDisk_compl D)
  have hncpN : NoncompactSpace ↥D.compl := noncompactSpace_coordDisk_compl D
  have : LocallyConnectedSpace ↥D.compl := ChartedSpace.locallyConnectedSpace ℂ ↥D.compl
  set p₀ : ↥D.compl := ⟨p, hp⟩ with hp₀def
  -- ## Generic helpers
  -- Transfer of plane subharmonicity along a pointwise equality on a subdomain.
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
  -- Restriction of plane subharmonicity.
  have subMono : ∀ (F : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      SubharmonicOn F W :=
    fun F U W hF hWU ↦
      ⟨hF.1.mono hWU, fun c hc ρ hρ hball ↦ hF.2 c (hWU hc) ρ hρ (hball.trans hWU)⟩
  -- Chart images as intersections with preimages, on the piece and on the base.
  have himgN : ∀ (e : OpenPartialHomeomorph ↥D.compl ℂ) (s : Set ℂ), s ⊆ e.target →
      e.symm '' s = e.source ∩ e ⁻¹' s := by
    intro e s hs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e.map_target (hs hz), ?_⟩
      rw [Set.mem_preimage, e.right_inv (hs hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨e y, hy2, e.left_inv hy⟩
  -- Subharmonicity at a point transfers along local equality.
  have msubCongr : ∀ (f g : ↥D.compl → ℝ) (y : ↥D.compl), MSubharmonicAt f y →
      (∀ᶠ z in 𝓝 y, f z = g z) → MSubharmonicAt g y := by
    intro f g y hf hev
    obtain ⟨r, hr, hrsub, hsh⟩ := hf
    have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hev2 : ∀ᶠ w in 𝓝 (chartAt ℂ y y),
        f ((chartAt ℂ y).symm w) = g ((chartAt ℂ y).symm w) :=
      hcont.eventually (p := fun z ↦ f z = g z) (by rw [hyy]; exact hev)
    obtain ⟨r2, hr2, hball2⟩ := Metric.eventually_nhds_iff_ball.mp hev2
    refine ⟨min r r2, lt_min hr hr2, (ball_subset_ball (min_le_left _ _)).trans hrsub, ?_⟩
    exact transfer _ _ _ _ hsh (ball_subset_ball (min_le_left _ _))
      (fun w hw ↦ hball2 w (ball_subset_ball (min_le_right _ _) hw))
  -- Positive scaling preserves subharmonicity at a point.
  have msubSmul : ∀ (f : ↥D.compl → ℝ) (a : ℝ), 0 ≤ a → ∀ y : ↥D.compl,
      MSubharmonicAt f y → MSubharmonicAt (fun z ↦ a * f z) y := by
    intro f a ha y hf
    obtain ⟨r, hr, hrsub, hsh⟩ := hf
    refine ⟨r, hr, hrsub, ?_⟩
    refine ⟨continuousOn_const.mul hsh.1, ?_⟩
    intro c hc ρ hρ hcb
    have hsph : sphere c ρ ⊆ ball (chartAt ℂ y y) r :=
      sphere_subset_closedBall.trans hcb
    have hci : CircleIntegrable (f ∘ (chartAt ℂ y).symm) c ρ :=
      (hsh.1.mono hsph).circleIntegrable hρ.le
    have h1 := hsh.2 c hc ρ hρ hcb
    have h2 : Real.circleAverage (fun w ↦ a * (f ∘ (chartAt ℂ y).symm) w) c ρ
        = a * Real.circleAverage (f ∘ (chartAt ℂ y).symm) c ρ := by
      have := Real.circleAverage_fun_smul (a := a) (f := f ∘ (chartAt ℂ y).symm)
        (c := c) (R := ρ)
      simpa [smul_eq_mul] using this
    calc a * f ((chartAt ℂ y).symm c)
        ≤ a * Real.circleAverage (f ∘ (chartAt ℂ y).symm) c ρ :=
          mul_le_mul_of_nonneg_left h1 ha
      _ = Real.circleAverage ((fun z ↦ a * f z) ∘ (chartAt ℂ y).symm) c ρ := by
          rw [← h2]; rfl
  -- Affine images of harmonic functions are harmonic.
  have mharmAffine : ∀ (g : ↥D.compl → ℝ) (x : ↥D.compl) (a c : ℝ), MHarmonicAt g x →
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
  -- ## Constancy propagation from an interior maximum (clopen argument).
  have propagate : ∀ (Ω : Set ↥D.compl) (w : ↥D.compl → ℝ) (xm : ↥D.compl),
      IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ x ∈ Ω, w x ≤ w xm) → ∀ x ∈ Ω, w x = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {x | x ∈ Ω ∧ w x = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hmax' : ∀ y ∈ Ω, w y ≤ w x := fun y hy ↦ (hmax y hy).trans_eq hxw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hxΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy.trans hxw⟩
    have hto : IsOpen {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hcont : ContinuousAt w x := (hwsub x hxΩ).continuousAt
      filter_upwards [hcont.eventually_ne hxw, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy⟩
    have hsub : Ω ⊆ {x | x ∈ Ω ∧ w x = w xm} ∪ {x | x ∈ Ω ∧ w x ≠ w xm} := by
      intro x hx
      by_cases hxw : w x = w xm
      · exact Or.inl ⟨hx, hxw⟩
      · exact Or.inr ⟨hx, hxw⟩
    have hdisj : Disjoint {x | x ∈ Ω ∧ w x = w xm} {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro x ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun x hx ↦ (hres hx).2
  -- ## Maximum principle on a proper open subset of the piece.
  have maxPrin : ∀ (Ω : Set ↥D.compl) (w : ↥D.compl → ℝ) (m : ℝ) (Kc : Set ↥D.compl),
      IsOpen Ω → Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ x ∈ Ω, x ∉ Kc → w x ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ x ∈ Ω, w x ≤ m := by
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
    have hall : ∀ x ∈ Ω, w x ≤ w xm := by
      intro x hx
      by_cases hxK : x ∈ Kc
      · exact hxmax ⟨subset_closure hx, hxK⟩
      · exact (hout x hx hxK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun x hx ↦ hwsub x (hCcΩ hx)) (fun x hx ↦ hall x (hCcΩ hx))
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
    have hne : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  -- ## The collar of the removed circle
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center with he₀
  set c₀ : ℂ := e₀ D.center with hc₀
  have hρ₀pos : 0 < D.radius := D.radius_pos
  have hsub₀ : closedBall c₀ D.radius ⊆ e₀.target := D.closedBall_subset
  -- A slightly larger closed ball still inside the chart target and avoiding `p`.
  obtain ⟨ρ₁, hρ₁gt, hρ₁sub, hρ₁p⟩ : ∃ ρ₁, D.radius < ρ₁ ∧
      closedBall c₀ ρ₁ ⊆ e₀.target ∧ (p ∈ e₀.source → ρ₁ < dist (e₀ p) c₀)
          := by
    obtain ⟨δ, hδpos, hδsub⟩ :=
      (isCompact_closedBall c₀ D.radius).exists_cthickening_subset_open
        e₀.open_target hsub₀
    have hthick : ∀ ρ', D.radius < ρ' → ρ' ≤ D.radius + δ →
        closedBall c₀ ρ' ⊆ e₀.target := by
      intro ρ' _ hρ'le
      refine (closedBall_subset_closedBall hρ'le).trans ?_
      calc closedBall c₀ (D.radius + δ)
          = closedBall c₀ (δ + D.radius) := by rw [add_comm]
        _ = cthickening δ (closedBall c₀ D.radius) :=
            (cthickening_closedBall hδpos.le hρ₀pos.le c₀).symm
        _ ⊆ e₀.target := hδsub
    by_cases hps : p ∈ e₀.source
    · have hpd : D.radius < dist (e₀ p) c₀ := by
        by_contra hle
        push Not at hle
        have hmem : p ∈ D.closedCarrier := by
          refine ⟨e₀ p, ?_, e₀.left_inv hps⟩
          rwa [mem_closedBall]
        exact hp hmem
      refine ⟨min (D.radius + δ) ((D.radius + dist (e₀ p) c₀) / 2), ?_, ?_, ?_⟩
      · exact lt_min (by linarith) (by linarith)
      · exact hthick _ (lt_min (by linarith) (by linarith)) (min_le_left _ _)
      · intro _
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · exact ⟨D.radius + δ, by linarith, hthick _ (by linarith) le_rfl,
        fun hcon ↦ absurd hcon hps⟩
  have hρ₁pos : 0 < ρ₁ := hρ₀pos.trans hρ₁gt
  -- The compact collar on the base surface, and its preimage on the piece.
  set Ccol : Set M := e₀.symm '' (closedBall c₀ ρ₁ \ ball c₀ D.radius) with hCcol
  have hCcolcomp : IsCompact Ccol :=
    ((isCompact_closedBall c₀ ρ₁).diff isOpen_ball).image_of_continuousOn
      (e₀.continuousOn_symm.mono (Set.sdiff_subset.trans hρ₁sub))
  have hpCcol : p ∉ Ccol := by
    rintro ⟨w, hw, hwp⟩
    have hwt : w ∈ e₀.target := hρ₁sub hw.1
    have hpsrc : p ∈ e₀.source := hwp ▸ e₀.map_target hwt
    have hpe : e₀ p = w := by rw [← hwp, e₀.right_inv hwt]
    have h1 := hρ₁p hpsrc
    rw [hpe] at h1
    exact absurd (mem_closedBall.1 hw.1) (not_le.2 h1)
  set Chat : Set ↥D.compl := Subtype.val ⁻¹' Ccol with hChat
  have hChatcl : IsClosed Chat := hCcolcomp.isClosed.preimage continuous_subtype_val
  have hp₀Chat : p₀ ∉ Chat := hpCcol
  -- ## The pole chart and its two circles
  set eN : OpenPartialHomeomorph ↥D.compl ℂ := chartAt ℂ p₀ with heN
  set z₀ : ℂ := eN p₀ with hz₀
  have hp₀src : p₀ ∈ eN.source := by rw [heN]; exact mem_chart_source ℂ p₀
  have heNatlas : eN ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ↥D.compl := by
    rw [heN]; exact IsManifold.chart_mem_maximalAtlas p₀
  have hz₀tgt : z₀ ∈ eN.target := by rw [hz₀]; exact eN.map_source hp₀src
  have hsymz₀ : eN.symm z₀ = p₀ := by rw [hz₀]; exact eN.left_inv hp₀src
  have hpre₀ : eN.target ∩ eN.symm ⁻¹' Chatᶜ ∈ 𝓝 z₀ := by
    have h1 : ContinuousAt eN.symm z₀ := eN.continuousAt_symm hz₀tgt
    have h3 : eN.symm ⁻¹' Chatᶜ ∈ 𝓝 z₀ :=
      h1.preimage_mem_nhds (hChatcl.isOpen_compl.mem_nhds (hsymz₀ ▸ hp₀Chat))
    exact Filter.inter_mem (eN.open_target.mem_nhds hz₀tgt) h3
  obtain ⟨R, hR, hRsub⟩ := nhds_basis_closedBall.mem_iff.1 hpre₀
  have hRtgt : closedBall z₀ R ⊆ eN.target := fun z hz ↦ (hRsub hz).1
  have hR2tgt : closedBall (chartAt ℂ p₀ p₀) (R / 2) ⊆ (chartAt ℂ p₀).target := by
    rw [← heN, ← hz₀]
    exact (closedBall_subset_closedBall (by linarith)).trans hRtgt
  -- ## The inner coordinate disk and its complementary region
  set Dp : CoordDisk ↥D.compl := ⟨p₀, R / 2, by positivity, hR2tgt⟩ with hDp
  have hDpcar : Dp.closedCarrier = eN.symm '' closedBall z₀ (R / 2) := by
    rw [hDp]
    simp only [CoordDisk.closedCarrier]
    rw [← heN, ← hz₀]
  set Wset : Set ↥D.compl := (Dp.compl : Set ↥D.compl) with hWset
  have hWdef : Wset = Dp.closedCarrierᶜ := rfl
  have hWopen : IsOpen Wset := Dp.isCompact_closedCarrier.isClosed.isOpen_compl
  have hWconn : IsConnected Wset := isConnected_coordDisk_compl Dp
  have hp₀car : p₀ ∈ Dp.closedCarrier := by
    rw [hDpcar]
    exact ⟨z₀, mem_closedBall_self (by positivity), hsymz₀⟩
  have hp₀W : p₀ ∉ Wset := by
    rw [hWdef]
    exact fun hc ↦ hc hp₀car
  have hWne : Wset ≠ Set.univ := by
    intro hcon
    apply hp₀W
    rw [hcon]
    trivial
  -- Points of the closed carrier read into the chart.
  have hcarmem : ∀ y ∈ Dp.closedCarrier, y ∈ eN.source ∧ dist (eN y) z₀ ≤ R / 2 := by
    intro y hy
    rw [hDpcar] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwt : w ∈ eN.target := hRtgt (closedBall_subset_closedBall (by linarith) hw)
    refine ⟨eN.map_target hwt, ?_⟩
    rw [eN.right_inv hwt]
    exact mem_closedBall.1 hw
  have hWmem : ∀ y : ↥D.compl, y ∈ eN.source → R / 2 < dist (eN y) z₀ → y ∈ Wset := by
    intro y hys hyd
    rw [hWdef]
    intro hy
    exact absurd (hcarmem y hy).2 (not_le.2 hyd)
  -- Detecting the pole through the chart.
  have hnep : ∀ y : ↥D.compl, y ∈ eN.source → eN y ≠ z₀ → y ≠ p₀ := by
    intro y hys hyne hcon
    rw [hcon] at hyne
    exact hyne hz₀.symm
  -- The piece is punctured at the pole away from the pole.
  have hWsub : Wset ⊆ ({p₀}ᶜ : Set ↥D.compl) := by
    intro y hy
    rw [Set.mem_compl_singleton_iff]
    intro hcon
    rw [hcon] at hy
    exact hp₀W hy
  -- The circles of radii `R/2` and `R`.
  set Γin : Set ↥D.compl := eN.symm '' sphere z₀ (R / 2) with hΓin
  set Γout : Set ↥D.compl := eN.symm '' sphere z₀ R with hΓout
  have hsphtgt : ∀ r' : ℝ, r' ≤ R → sphere z₀ r' ⊆ eN.target := fun r' hr' ↦
    sphere_subset_closedBall.trans ((closedBall_subset_closedBall hr').trans hRtgt)
  have hΓincomp : IsCompact Γin :=
    (isCompact_sphere z₀ (R / 2)).image_of_continuousOn
      (eN.continuousOn_symm.mono (hsphtgt _ (by linarith)))
  have hΓoutcomp : IsCompact Γout :=
    (isCompact_sphere z₀ R).image_of_continuousOn
      (eN.continuousOn_symm.mono (hsphtgt _ le_rfl))
  have hΓinne : Γin.Nonempty :=
    (NormedSpace.sphere_nonempty.2 (by positivity)).image _
  have hΓoutne : Γout.Nonempty :=
    (NormedSpace.sphere_nonempty.2 hR.le).image _
  have hΓmem : ∀ r' : ℝ, r' ≤ R → ∀ y : ↥D.compl, y ∈ eN.source →
      dist (eN y) z₀ = r' → y ∈ eN.symm '' sphere z₀ r' := by
    intro r' hr' y hys hyd
    exact ⟨eN y, by rwa [mem_sphere], eN.left_inv hys⟩
  have hΓprop : ∀ r' : ℝ, 0 < r' → r' ≤ R → ∀ y ∈ eN.symm '' sphere z₀ r',
      y ∈ eN.source ∧ dist (eN y) z₀ = r' ∧ y ≠ p₀ := by
    intro r' hr'pos hr' y hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwt : w ∈ eN.target := hsphtgt r' hr' hw
    have h1 : eN (eN.symm w) = w := eN.right_inv hwt
    have h2 : dist (eN (eN.symm w)) z₀ = r' := by rw [h1]; exact mem_sphere.1 hw
    have h3 : eN (eN.symm w) ≠ z₀ := by
      intro hcon
      rw [hcon, dist_self] at h2
      exact hr'pos.ne h2
    exact ⟨eN.map_target hwt, h2, hnep _ (eN.map_target hwt) h3⟩
  have hΓinW : Γin ⊆ ({p₀}ᶜ : Set ↥D.compl) := by
    intro y hy
    exact Set.mem_compl_singleton_iff.2 (hΓprop (R / 2) (by positivity) (by linarith) y hy).2.2
  have hΓoutW : Γout ⊆ Wset := by
    intro y hy
    obtain ⟨hys, hyd, -⟩ := hΓprop R hR le_rfl y hy
    exact hWmem y hys (by rw [hyd]; linarith)
  -- The witness point on the inner circle.
  set x₀ : ↥D.compl := eN.symm (z₀ + ((R / 2 : ℝ) : ℂ)) with hx₀def
  have hwsph : z₀ + ((R / 2 : ℝ) : ℂ) ∈ sphere z₀ (R / 2) := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hx₀Γin : x₀ ∈ Γin := ⟨z₀ + ((R / 2 : ℝ) : ℂ), hwsph, rfl⟩
  have hx₀ne : x₀ ≠ p₀ := (hΓprop (R / 2) (by positivity) (by linarith) x₀ hx₀Γin).2.2
  -- The collar sits inside the region.
  have hChatW : Chat ⊆ Wset := by
    intro y hy
    rw [hWdef]
    intro hyD
    rw [hDpcar] at hyD
    obtain ⟨w', hw', hwy⟩ := hyD
    have h1 := (hRsub (closedBall_subset_closedBall (by linarith) hw')).2
    rw [Set.mem_preimage, hwy] at h1
    exact h1 hy
  -- ## The harmonic-measure family and its envelope
  set Fam : Set (↥D.compl → ℝ) := {u | MSubharmonicOn u Wset ∧ (∀ y ∈ Wset, u y ≤ 1)
      ∧
    ∃ K : Set ↥D.compl, IsCompact K ∧ ∀ y ∈ Wset, y ∉ K → u y = 0} with hFam
  have h0Fam : (fun _ : ↥D.compl ↦ (0 : ℝ)) ∈ Fam := by
    refine ⟨fun y _ ↦ ?_, fun y _ ↦ by norm_num, ∅, isCompact_empty, fun y _ _ ↦ rfl⟩
    exact (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt
  set omeg : ↥D.compl → ℝ := fun y ↦ sSup ((fun u ↦ u y) '' Fam) with homeg
  have hFamne : ∀ y : ↥D.compl, ((fun u ↦ u y) '' Fam).Nonempty :=
    fun y ↦ ⟨0, (fun _ : ↥D.compl ↦ (0 : ℝ)), h0Fam, rfl⟩
  have hFamBdd : ∀ y ∈ Wset, BddAbove ((fun u ↦ u y) '' Fam) := by
    intro y hy
    refine ⟨1, ?_⟩
    rintro b ⟨u, hu, rfl⟩
    exact hu.2.1 y hy
  have homegle1 : ∀ y ∈ Wset, omeg y ≤ 1 := by
    intro y hy
    refine csSup_le (hFamne y) ?_
    rintro b ⟨u, hu, rfl⟩
    exact hu.2.1 y hy
  have homegge : ∀ y ∈ Wset, ∀ u ∈ Fam, u y ≤ omeg y :=
    fun y hy u hu ↦ le_csSup (hFamBdd y hy) ⟨u, hu, rfl⟩
  have homegge0 : ∀ y ∈ Wset, 0 ≤ omeg y :=
    fun y hy ↦ homegge y hy _ h0Fam
  -- Max-closure of the family.
  have hFammax : ∀ u₁ ∈ Fam, ∀ u₂ ∈ Fam, (fun y ↦ max (u₁ y) (u₂ y)) ∈ Fam := by
    rintro u₁ ⟨hs₁, hb₁, K₁, hK₁, hz₁⟩ u₂ ⟨hs₂, hb₂, K₂, hK₂, hz₂⟩
    refine ⟨fun y hy ↦ (hs₁ y hy).max (hs₂ y hy), fun y hy ↦ max_le (hb₁ y hy) (hb₂ y
        hy),
      K₁ ∪ K₂, hK₁.union hK₂, ?_⟩
    intro y hy hyK
    change max (u₁ y) (u₂ y) = 0
    rw [hz₁ y hy (fun h ↦ hyK (Or.inl h)), hz₂ y hy (fun h ↦ hyK (Or.inr h))]
    exact max_self 0
  -- ## Perron: the envelope is harmonic on the region
  have homegHarm : MHarmonicOn omeg Wset := by
    intro x hx
    set ex : OpenPartialHomeomorph ↥D.compl ℂ := chartAt ℂ x with hex
    have hxsrc : x ∈ ex.source := by rw [hex]; exact mem_chart_source ℂ x
    have hexatlas : ex ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ↥D.compl := by
      rw [hex]; exact IsManifold.chart_mem_maximalAtlas x
    set cx : ℂ := ex x with hcx
    have hop : IsOpen (ex.target ∩ ex.symm ⁻¹' Wset) := ex.isOpen_inter_preimage_symm hWopen
    have hmem : cx ∈ ex.target ∩ ex.symm ⁻¹' Wset := by
      refine ⟨by rw [hcx]; exact ex.map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, hcx, ex.left_inv hxsrc]
      exact hx
    obtain ⟨ρb, hρb, hρbsub⟩ := nhds_basis_closedBall.mem_iff.1 (hop.mem_nhds hmem)
    set ρ : ℝ := ρb / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρlt : ρ < ρb := by rw [hρdef]; linarith
    have hballtgt : ball cx ρb ⊆ ex.target :=
      fun w hw ↦ (hρbsub (ball_subset_closedBall hw)).1
    have hballW : ∀ w ∈ ball cx ρb, ex.symm w ∈ Wset := by
      intro w hw
      have := (hρbsub (ball_subset_closedBall hw)).2
      rwa [Set.mem_preimage] at this
    have hcbρ : closedBall cx ρ ⊆ ball cx ρb := closedBall_subset_ball hρlt
    have hsphρ : sphere cx ρ ⊆ ball cx ρb := sphere_subset_closedBall.trans hcbρ
    -- (P1) chart reading of a family member is subharmonic on the chart ball.
    have hread : ∀ u : ↥D.compl → ℝ, MSubharmonicOn u Wset →
        SubharmonicOn (u ∘ ex.symm) (ball cx ρb) := by
      intro u hu
      have hkey : ∀ w ∈ ball cx ρb, ∃ r' > 0,
          SubharmonicOn (u ∘ ex.symm) (ball w r') := by
        intro w hw
        have hwt : w ∈ ex.target := hballtgt hw
        have hwsrc : ex.symm w ∈ ex.source := ex.map_target hwt
        have hws : ex.symm w ∈ Wset := hballW w hw
        obtain ⟨r', hr', -, hsh⟩ :=
          (msubharmonicAt_iff_of_mem_maximalAtlas hexatlas hwsrc).mp (hu _ hws)
        rw [ex.right_inv hwt] at hsh
        exact ⟨r', hr', hsh⟩
      apply subharmonicOn_of_locally isOpen_ball
      · intro w hw
        obtain ⟨r', hr', hsh⟩ := hkey w hw
        exact (hsh.1.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr'))).continuousWithinAt
      · intro w hw
        obtain ⟨r', hr', hsh⟩ := hkey w hw
        refine ⟨r', hr', ?_⟩
        intro r hr0 hrr' _
        exact hsh.2 w (mem_ball_self hr') r hr0 (closedBall_subset_ball hrr')
    -- (P2) Poisson modification is monotone in the boundary data.
    have hpmono : ∀ pf qf : ℂ → ℝ, ContinuousOn pf (sphere cx ρ) →
        ContinuousOn qf (sphere cx ρ) → (∀ s ∈ sphere cx ρ, pf s ≤ qf s) →
        ∀ w ∈ ball cx ρ,
          RiemannDynamics.poissonModify pf cx ρ w ≤ RiemannDynamics.poissonModify qf cx ρ w := by
      intro pf qf hpc hqc hpq w hw
      simp only [RiemannDynamics.poissonModify, ite_eq_left hw, poissonIntegral]
      have hwlt : ‖w - cx‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hw
      have hkcont : ContinuousOn (fun s ↦ poissonKernel cx w s) (sphere cx ρ) := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]
        apply Complex.continuous_re.comp_continuousOn
        rw [herglotzRieszKernel_fun_def]
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro s hs
        have hsn : ‖s - cx‖ = ρ := by
          rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hs)
        intro hcontra
        have : s - cx = w - cx := by linear_combination (norm := ring_nf) hcontra
        rw [this] at hsn; rw [hsn] at hwlt; linarith
      have hci_p : CircleIntegrable (fun s ↦ poissonKernel cx w s * pf s) cx ρ :=
        (hkcont.mul hpc).circleIntegrable hρ.le
      have hci_q : CircleIntegrable (fun s ↦ poissonKernel cx w s * qf s) cx ρ :=
        (hkcont.mul hqc).circleIntegrable hρ.le
      have hker_nn : ∀ s ∈ sphere cx |ρ|, 0 ≤ poissonKernel cx w s := by
        intro s hs
        rw [abs_of_pos hρ] at hs
        have hzc : ‖s - cx‖ = ρ := by
          rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hs)
        rw [poissonKernel_def]
        apply div_nonneg _ (by positivity)
        have : ‖w - cx‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwlt.le 2
        rw [hzc]; linarith
      apply Real.circleAverage_mono hci_p hci_q
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (hker_nn s hs)
      exact hpq s (by rwa [abs_of_pos hρ] at hs)
    -- Plane bound: the modification of data `≤ 1` stays `≤ 1` inside the disk.
    have hPMle1 : ∀ u : ↥D.compl → ℝ, MSubharmonicOn u Wset → (∀ y ∈ Wset, u y ≤ 1)
        →
        ∀ w ∈ ball cx ρ, RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ w ≤ 1 := by
      intro u husub hule w hw
      have hPMsub : SubharmonicOn
          (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ) (ball cx ρb) :=
        (hread u husub).poissonModify hρ hcbρ
      have hcont : ContinuousOn (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ)
          (closure (ball cx ρ)) := by
        rw [closure_ball cx hρ.ne']
        exact hPMsub.1.mono (closedBall_subset_ball hρlt)
      have hfr : ∀ ζ ∈ frontier (ball cx ρ),
          RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ ζ ≤ 1 := by
        intro ζ hζ
        rw [frontier_ball cx hρ.ne'] at hζ
        have hnb : ζ ∉ ball cx ρ := by
          rw [mem_ball, Metric.mem_sphere.1 hζ]; exact lt_irrefl _
        have h1 : RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ ζ = u (ex.symm ζ) := by
          simp only [RiemannDynamics.poissonModify, ite_eq_right hnb]; rfl
        rw [h1]
        exact hule _ (hballW ζ (hsphρ hζ))
      exact (subMono _ _ _ hPMsub (ball_subset_ball hρlt.le)).le_of_frontier_le
        isOpen_ball isBounded_ball hcont hfr w hw
    -- (P3) the surface transplant of the Poisson modification.
    set Breg : Set ↥D.compl := ex.symm '' ball cx ρ with hBreg
    set Bcl : Set ↥D.compl := ex.symm '' closedBall cx ρ with hBcl
    have hcbtgt : closedBall cx ρ ⊆ ex.target := hcbρ.trans hballtgt
    have hBclcomp : IsCompact Bcl :=
      (isCompact_closedBall cx ρ).image_of_continuousOn (ex.continuousOn_symm.mono hcbtgt)
    have hBclW : Bcl ⊆ Wset := by
      rintro y ⟨w, hw, rfl⟩
      exact hballW w (hcbρ hw)
    have hBregBcl : Breg ⊆ Bcl := Set.image_mono ball_subset_closedBall
    set mdf : (↥D.compl → ℝ) → ↥D.compl → ℝ := fun u y ↦
      if y ∈ ex.source ∧ ex y ∈ ball cx ρ then
        RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ (ex y) else u y with hmdf
    -- `mdf u = u` off the compact `Bcl`.
    have hmdfoff : ∀ u : ↥D.compl → ℝ, ∀ y : ↥D.compl, y ∉ Bcl → mdf u y = u y := by
      intro u y hy
      rw [hmdf]
      simp only
      rw [ite_eq_right]
      rintro ⟨hys, hyb⟩
      exact hy ⟨ex y, ball_subset_closedBall hyb, ex.left_inv hys⟩
    -- Value of the transplant inside the modified region.
    have hmdfval : ∀ u : ↥D.compl → ℝ, ∀ w ∈ ball cx ρ,
        mdf u (ex.symm w) = RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ w := by
      intro u w hw
      have hwt : w ∈ ex.target := hballtgt (ball_subset_ball hρlt.le hw)
      have h1 : ex.symm w ∈ ex.source := ex.map_target hwt
      rw [hmdf]
      simp only
      rw [ite_eq_left ⟨h1, by rwa [ex.right_inv hwt]⟩, ex.right_inv hwt]
    -- The transplant reading agrees with the plane modification.
    have hmdfread : ∀ u : ↥D.compl → ℝ, Set.EqOn (mdf u ∘ ex.symm)
        (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ) (ball cx ρb) := by
      intro u w hw
      have hwt : w ∈ ex.target := hballtgt hw
      have h1 : ex.symm w ∈ ex.source := ex.map_target hwt
      by_cases hwb : w ∈ ball cx ρ
      · exact hmdfval u w hwb
      · have h2 : mdf u (ex.symm w) = u (ex.symm w) := by
          rw [hmdf]
          simp only
          rw [ite_eq_right]
          rintro ⟨-, hyb⟩
          rw [ex.right_inv hwt] at hyb
          exact hwb hyb
        have h3 : RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ w = u (ex.symm w) := by
          simp only [RiemannDynamics.poissonModify, ite_eq_right hwb]; rfl
        rw [Function.comp_apply, h2, h3]
    -- Membership of the transplant in the family.
    have hmdfmem : ∀ u ∈ Fam, mdf u ∈ Fam := by
      rintro u ⟨husub, hule, Ku, hKu, hKuz⟩
      have hPMsub : SubharmonicOn
          (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ) (ball cx ρb) :=
        (hread u husub).poissonModify hρ hcbρ
      refine ⟨?_, ?_, Ku ∪ Bcl, hKu.union hBclcomp, ?_⟩
      · -- subharmonicity of the transplant
        intro y hy
        by_cases hyB : y ∈ Bcl
        · obtain ⟨wy, hwy, rfl⟩ := hyB
          have hwyt : wy ∈ ex.target := hcbtgt hwy
          have hysrc : ex.symm wy ∈ ex.source := ex.map_target hwyt
          rw [msubharmonicAt_iff_of_mem_maximalAtlas hexatlas hysrc]
          have hwyb : ex (ex.symm wy) ∈ ball cx ρb := by
            rw [ex.right_inv hwyt]
            exact hcbρ hwy
          set r' : ℝ := ρb - dist (ex (ex.symm wy)) cx with hr'
          have hr'pos : 0 < r' := by
            rw [hr']
            have := mem_ball.1 hwyb
            linarith
          have hr'sub : ball (ex (ex.symm wy)) r' ⊆ ball cx ρb := by
            apply ball_subset_ball'
            rw [hr']
            ring_nf
            exact le_rfl
          refine ⟨r', hr'pos, hr'sub.trans hballtgt, ?_⟩
          exact transfer _ _ _ _ hPMsub hr'sub (fun w hw ↦ (hmdfread u (hr'sub hw)).symm)
        · have hbase := husub y hy
          apply msubCongr u (mdf u) y hbase
          filter_upwards [hBclcomp.isClosed.isOpen_compl.mem_nhds hyB] with z hz
          exact (hmdfoff u z hz).symm
      · -- the transplant stays `≤ 1`
        intro y hy
        by_cases hyc : y ∈ ex.source ∧ ex y ∈ ball cx ρ
        · have h1 : mdf u y = RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ (ex y) := by
            rw [hmdf]; simp only; rw [ite_eq_left hyc]
          rw [h1]
          exact hPMle1 u husub hule (ex y) hyc.2
        · have h1 : mdf u y = u y := by
            rw [hmdf]; simp only; rw [ite_eq_right hyc]
          rw [h1]
          exact hule y hy
      · -- vanishing off a compact set
        intro y hy hyK
        rw [hmdfoff u y (fun h ↦ hyK (Or.inr h))]
        exact hKuz y hy (fun h ↦ hyK (Or.inl h))
    -- The transplant dominates the member.
    have hmdfge : ∀ u ∈ Fam, ∀ y ∈ Wset, u y ≤ mdf u y := by
      rintro u ⟨husub, -, -⟩ y hy
      by_cases hyc : y ∈ ex.source ∧ ex y ∈ ball cx ρ
      · have h1 : mdf u y = RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ (ex y) := by
          rw [hmdf]; simp only; rw [ite_eq_left hyc]
        rw [h1]
        have h2 := poissonModify_ge (hread u husub) hρ hcbρ (ex y)
          (ball_subset_ball hρlt.le hyc.2)
        rwa [Function.comp_apply, ex.left_inv hyc.1] at h2
      · have h1 : mdf u y = u y := by rw [hmdf]; simp only; rw [ite_eq_right hyc]
        rw [h1]
    -- (P4) running maxima.
    set rmax : (ℕ → ↥D.compl → ℝ) → ℕ → ↥D.compl → ℝ :=
      fun g ↦ fun k ↦ Nat.rec (g 0) (fun n acc ↦ fun y ↦ max (acc y) (g (n + 1) y)) k
      with hrmax
    have hrmax_mem : ∀ (g : ℕ → ↥D.compl → ℝ), (∀ n, g n ∈ Fam) →
        ∀ k, rmax g k ∈ Fam := by
      intro g hg k
      induction k with
      | zero => exact hg 0
      | succ n ih => exact hFammax _ ih _ (hg (n + 1))
    have hrmax_ge : ∀ (g : ℕ → ↥D.compl → ℝ) (k : ℕ) (y : ↥D.compl),
        g k y ≤ rmax g k y := by
      intro g k y
      cases k with
      | zero => simp [hrmax]
      | succ n => exact le_max_right _ _
    have hrmax_mono : ∀ (g : ℕ → ↥D.compl → ℝ) (y : ↥D.compl),
        Monotone (fun k ↦ rmax g k y) := by
      intro g y
      apply monotone_nat_of_le_succ
      intro n
      exact le_max_left _ _
    have hrmax_data_mono : ∀ (g₁ g₂ : ℕ → ↥D.compl → ℝ), (∀ n y, g₁ n y ≤ g₂
        n y) →
        ∀ k y, rmax g₁ k y ≤ rmax g₂ k y := by
      intro g₁ g₂ hle k y
      induction k with
      | zero => exact hle 0 y
      | succ n ih => exact max_le_max ih (hle (n + 1) y)
    -- (P5) maximizing sequences.
    have hmaxseq : ∀ q ∈ Wset, ∃ s : ℕ → ↥D.compl → ℝ, (∀ n, s n ∈ Fam) ∧
        Tendsto (fun n ↦ s n q) atTop (𝓝 (omeg q)) := by
      intro q hq
      obtain ⟨a, -, hatends, hamem⟩ :=
        exists_seq_tendsto_sSup (hFamne q) (hFamBdd q hq)
      have hchoose : ∀ n, ∃ v ∈ Fam, v q = a n := fun n ↦ hamem n
      choose s hs hsval using hchoose
      refine ⟨s, hs, ?_⟩
      have : (fun n ↦ s n q) = a := funext fun n ↦ hsval n
      rw [this]
      exact hatends
    -- (P6) the harmonic limit construction on the chart disk.
    have hbuild : ∀ (g : ℕ → ↥D.compl → ℝ), (∀ n, g n ∈ Fam) →
        ∃ V : ℂ → ℝ, HarmonicOnNhd V (ball cx ρ) ∧
          (∀ y : ↥D.compl, y ∈ ex.source → ex y ∈ ball cx ρ →
            V (ex y) ≤ omeg y ∧ ∀ k, g k y ≤ V (ex y)) ∧
          V = fun w ↦ ⨆ k, RiemannDynamics.poissonModify (rmax g k ∘ ex.symm) cx ρ w := by
      intro g hg
      set Vseq : ℕ → ℂ → ℝ :=
        fun k ↦ RiemannDynamics.poissonModify (rmax g k ∘ ex.symm) cx ρ with hVseq
      have hrm_mem : ∀ k, rmax g k ∈ Fam := hrmax_mem g hg
      have hrm_read : ∀ k, SubharmonicOn (rmax g k ∘ ex.symm) (ball cx ρb) :=
        fun k ↦ hread _ (hrm_mem k).1
      have hVharm : ∀ k, HarmonicOnNhd (Vseq k) (ball cx ρ) :=
        fun k ↦ poissonModify_harmonicOn (hrm_read k) hρ hcbρ
      -- the plane value equals the surface transplant inside the disk
      have hVsurf : ∀ k, ∀ w ∈ ball cx ρ, Vseq k w = mdf (rmax g k) (ex.symm w) :=
        fun k w hw ↦ (hmdfval (rmax g k) w hw).symm
      have hVle : ∀ k, ∀ w ∈ ball cx ρ, Vseq k w ≤ omeg (ex.symm w) := by
        intro k w hw
        rw [hVsurf k w hw]
        exact homegge _ (hballW w (ball_subset_ball hρlt.le hw)) _
          (hmdfmem _ (hrm_mem k))
      have hVmono : ∀ w ∈ ball cx ρ, Monotone (fun k ↦ Vseq k w) := by
        intro w hw
        apply monotone_nat_of_le_succ
        intro k
        exact hpmono _ _ ((hrm_read k).1.mono hsphρ) ((hrm_read (k + 1)).1.mono hsphρ)
          (fun s _ ↦ hrmax_mono g (ex.symm s) (Nat.le_succ k)) w hw
      have hVbdd : ∀ w ∈ ball cx ρ, BddAbove (Set.range fun k ↦ Vseq k w) := by
        intro w hw
        exact ⟨omeg (ex.symm w), by rintro b ⟨k, rfl⟩; exact hVle k w hw⟩
      set V : ℂ → ℝ := fun w ↦ ⨆ k, Vseq k w with hV
      have htends : ∀ w ∈ ball cx ρ, Tendsto (fun k ↦ Vseq k w) atTop (𝓝 (V w)) :=
        fun w hw ↦ tendsto_atTop_ciSup (hVmono w hw) (hVbdd w hw)
      have hbddV : ∀ w ∈ ball cx ρ, ∀ k, Vseq k w ≤ V w :=
        fun w hw k ↦ le_ciSup (hVbdd w hw) k
      have hVlim : HarmonicOnNhd V (ball cx ρ) :=
        harmonicOnNhd_of_monotone_tendsto hVharm hVmono hbddV htends
      refine ⟨V, hVlim, ?_, rfl⟩
      intro y hysrc hyball
      have hywt : y = ex.symm (ex y) := (ex.left_inv hysrc).symm
      have hyW : y ∈ Wset := by
        rw [hywt]
        exact hballW _ (ball_subset_ball hρlt.le hyball)
      constructor
      · refine ciSup_le fun k ↦ ?_
        have := hVle k (ex y) hyball
        rwa [← hywt] at this
      · intro k
        calc g k y ≤ rmax g k y := hrmax_ge g k y
          _ ≤ mdf (rmax g k) y := hmdfge _ (hrm_mem k) y hyW
          _ = Vseq k (ex y) := by rw [hVsurf k (ex y) hyball, ← hywt]
          _ ≤ V (ex y) := hbddV (ex y) hyball k
    -- assemble: the envelope agrees with a harmonic function near `x`.
    obtain ⟨g0, hg0mem, hg0t⟩ := hmaxseq x hx
    obtain ⟨V, hVharm, hVprop, hVeq⟩ := hbuild g0 hg0mem
    have hcxball : ex x ∈ ball cx ρ := by rw [← hcx]; exact mem_ball_self hρ
    have hVcx : V (ex x) = omeg x := by
      apply le_antisymm (hVprop x hxsrc hcxball).1
      refine le_of_tendsto_of_tendsto hg0t tendsto_const_nhds ?_
      filter_upwards with k using (hVprop x hxsrc hcxball).2 k
    have hVeqomeg : ∀ y : ↥D.compl, y ∈ ex.source → ex y ∈ ball cx ρ →
        V (ex y) = omeg y := by
      intro q hqsrc hqball
      rcases lt_or_eq_of_le (hVprop q hqsrc hqball).1 with hlt | heq
      · exfalso
        have hqW : q ∈ Wset := by
          have : q = ex.symm (ex q) := (ex.left_inv hqsrc).symm
          rw [this]
          exact hballW _ (ball_subset_ball hρlt.le hqball)
        obtain ⟨g1, hg1mem, hg1t⟩ := hmaxseq q hqW
        set gc : ℕ → ↥D.compl → ℝ := fun n y ↦ max (g0 n y) (g1 n y) with hgc
        have hgcmem : ∀ n, gc n ∈ Fam := fun n ↦ hFammax _ (hg0mem n) _ (hg1mem n)
        obtain ⟨Q, hQharm, hQprop, hQeq⟩ := hbuild gc hgcmem
        have hQcx : Q (ex x) = omeg x := by
          apply le_antisymm (hQprop x hxsrc hcxball).1
          refine le_of_tendsto_of_tendsto hg0t tendsto_const_nhds ?_
          filter_upwards with k using
            le_trans (le_max_left _ _) ((hQprop x hxsrc hcxball).2 k)
        have hQq : Q (ex q) = omeg q := by
          apply le_antisymm (hQprop q hqsrc hqball).1
          refine le_of_tendsto_of_tendsto hg1t tendsto_const_nhds ?_
          filter_upwards with k using
            le_trans (le_max_right _ _) ((hQprop q hqsrc hqball).2 k)
        have hQgeV : ∀ w ∈ ball cx ρ, V w ≤ Q w := by
          intro w hw
          rw [hVeq, hQeq]
          have hbdd2 : BddAbove (Set.range fun k ↦
              RiemannDynamics.poissonModify (rmax gc k ∘ ex.symm) cx ρ w) := by
            refine ⟨omeg (ex.symm w), ?_⟩
            rintro b ⟨k, rfl⟩
            change RiemannDynamics.poissonModify (rmax gc k ∘ ex.symm) cx ρ w
              ≤ omeg (ex.symm w)
            rw [← hmdfval (rmax gc k) w hw]
            exact homegge _ (hballW w (ball_subset_ball hρlt.le hw)) _
              (hmdfmem _ (hrmax_mem gc hgcmem k))
          refine ciSup_mono hbdd2 fun k ↦ ?_
          apply hpmono _ _ ((hread _ (hrmax_mem g0 hg0mem k).1).1.mono hsphρ)
            ((hread _ (hrmax_mem gc hgcmem k).1).1.mono hsphρ) _ w hw
          intro s _
          exact hrmax_data_mono g0 gc (fun n y ↦ le_max_left _ _) k (ex.symm s)
        have hDharm : HarmonicOnNhd (fun w ↦ Q w - V w) (ball cx ρ) := by
          exact hQharm.sub hVharm
        have hDnn : ∀ w ∈ ball cx ρ, 0 ≤ Q w - V w := fun w hw ↦ by
          linarith [hQgeV w hw]
        have hD0 : Q (ex x) - V (ex x) = 0 := by rw [hQcx, hVcx, sub_self]
        have hzero := harmonic_eq_zero_of_nonneg_eq_zero isOpen_ball
          (convex_ball cx ρ).isPreconnected hDharm hDnn hcxball hD0
        have := hzero (ex q) hqball
        have hQV : Q (ex q) = V (ex q) := by linarith
        rw [← hQq, hQV] at hlt
        exact lt_irrefl _ hlt
      · exact heq
    -- transfer harmonicity to the envelope through the chart.
    have hev : V =ᶠ[𝓝 cx] (omeg ∘ ex.symm) := by
      have hb1 : ball cx ρ ∈ 𝓝 cx := isOpen_ball.mem_nhds (mem_ball_self hρ)
      filter_upwards [hb1] with w hw
      have hwt : w ∈ ex.target := hballtgt (ball_subset_ball hρlt.le hw)
      have h1 : ex.symm w ∈ ex.source := ex.map_target hwt
      have h2 : ex (ex.symm w) ∈ ball cx ρ := by rwa [ex.right_inv hwt]
      have := hVeqomeg (ex.symm w) h1 h2
      rw [ex.right_inv hwt] at this
      exact this
    have hgoal : HarmonicAt (omeg ∘ ex.symm) cx :=
      (harmonicAt_congr_nhds hev).mp (hVharm cx (mem_ball_self hρ))
    rw [hex, hcx] at hgoal
    exact hgoal
  -- ## The dip at the removed circle
  set a1 : ℝ := (Real.log ρ₁ - Real.log D.radius)⁻¹ with ha1
  have hloggap : 0 < Real.log ρ₁ - Real.log D.radius :=
    sub_pos.2 (Real.log_lt_log hρ₀pos hρ₁gt)
  have ha1pos : 0 < a1 := inv_pos.2 hloggap
  set hbar : ↥D.compl → ℝ :=
    fun q ↦ a1 * (Real.log (dist (e₀ (q : M)) c₀) - Real.log D.radius) with hhbar
  -- The open annulus region between the removed circle and the enlarged circle.
  set Aann : Set ↥D.compl :=
    Subtype.val ⁻¹' (e₀.source ∩ e₀ ⁻¹' (ball c₀ ρ₁ \ closedBall c₀ D.radius))
        with hAann
  have hAannopen : IsOpen Aann :=
    (e₀.continuousOn.isOpen_inter_preimage e₀.open_source
      (isOpen_ball.sdiff isClosed_closedBall)).preimage continuous_subtype_val
  have hAannmem : ∀ y : ↥D.compl, y ∈ Aann ↔ (y : M) ∈ e₀.source ∧
      D.radius < dist (e₀ (y : M)) c₀ ∧ dist (e₀ (y : M)) c₀ < ρ₁ := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall] at h2
      exact ⟨h1, not_le.1 h2.2, h2.1⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_⟩
      rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall]
      exact ⟨h3, not_le.2 h2⟩
  have hAannChat : Aann ⊆ Chat := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := (hAannmem y).1 hy
    refine ⟨e₀ (y : M), ⟨mem_closedBall.2 h3.le, ?_⟩, e₀.left_inv h1⟩
    rw [mem_ball, not_lt]
    exact h2.le
  have hAannW : Aann ⊆ Wset := hAannChat.trans hChatW
  have hp₀Aann : p₀ ∉ Aann := fun h ↦ hp₀Chat (hAannChat h)
  have hAannne : Aann ≠ Set.univ := by
    intro hcon
    apply hp₀Aann
    rw [hcon]
    trivial
  -- The collar points of the piece are never on the removed circle itself.
  have hcollarpts : ∀ y : ↥D.compl, (y : M) ∈ Ccol → (y : M) ∈ e₀.source ∧
      D.radius < dist (e₀ (y : M)) c₀ ∧ dist (e₀ (y : M)) c₀ ≤ ρ₁ := by
    rintro y ⟨w, ⟨hw1, hw2⟩, hwy⟩
    have hwt : w ∈ e₀.target := hρ₁sub hw1
    have hsrc : (y : M) ∈ e₀.source := hwy ▸ e₀.map_target hwt
    have hval : e₀ (y : M) = w := by rw [← hwy, e₀.right_inv hwt]
    have hne : D.radius < dist w c₀ := by
      rcases lt_or_eq_of_le (not_lt.1 (fun h ↦ hw2 (mem_ball.2 h))) with h | h
      · exact h
      · exfalso
        have hyD : (y : M) ∈ D.closedCarrier :=
          ⟨w, mem_closedBall.2 h.symm.le, hwy⟩
        exact y.2 hyD
    exact ⟨hsrc, by rw [hval]; exact hne, by rw [hval]; exact mem_closedBall.1 hw1⟩
  -- Harmonicity of the annulus barrier on the piece.
  have hbarHarm : ∀ y ∈ Aann, MHarmonicAt hbar y := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := (hAannmem y).1 hy
    have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    -- the chart reading of the base coordinate is analytic
    have hTan : AnalyticAt ℂ
        (fun w ↦ e₀ (((chartAt ℂ y).symm w : ↥D.compl) : M)) (chartAt ℂ y y) := by
      have hs1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ y).symm (chartAt ℂ y y) :=
        contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas y) (mem_chart_target ℂ y)
      have hs2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun q : ↥D.compl ↦ (q : M))
          ((chartAt ℂ y).symm (chartAt ℂ y y)) := contMDiff_subtype_val.contMDiffAt
      have hs3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e₀)
          ((((chartAt ℂ y).symm (chartAt ℂ y y) : ↥D.compl)) : M) := by
        apply contMDiffAt_of_mem_maximalAtlas (n := ω)
        · rw [he₀]; exact IsManifold.chart_mem_maximalAtlas D.center
        · rw [hyy]; exact h1
      have hs4 := (hs3.comp _ hs2).comp (chartAt ℂ y y) hs1
      exact (contMDiffAt_iff_contDiffAt.mp hs4).analyticAt
    have hne : e₀ (((chartAt ℂ y).symm (chartAt ℂ y y) : ↥D.compl) : M) - c₀ ≠ 0 := by
      rw [hyy, sub_ne_zero]
      intro hcon
      rw [hcon, dist_self] at h2
      exact absurd h2 (not_lt.2 hρ₀pos.le)
    have hlog : HarmonicAt (fun w ↦
        Real.log ‖e₀ (((chartAt ℂ y).symm w : ↥D.compl) : M) - c₀‖) (chartAt ℂ y y) :=
      AnalyticAt.harmonicAt_log_norm (hTan.sub analyticAt_const) hne
    have haff := (hlog.sub (harmonicAt_const (Real.log D.radius))).const_smul (c := a1)
    have heq : (a1 • ((fun w ↦
        Real.log ‖e₀ (((chartAt ℂ y).symm w : ↥D.compl) : M) - c₀‖) -
        fun _ ↦ Real.log D.radius)) = hbar ∘ (chartAt ℂ y).symm := by
      funext w
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_apply, hhbar]
      rw [dist_eq_norm]
    rw [heq] at haff
    exact haff
  -- Continuity of the barrier at collar points.
  have hbarCont : ∀ y : ↥D.compl, (y : M) ∈ e₀.source → e₀ (y : M) ≠ c₀ →
      ContinuousAt hbar y := by
    intro y hys hyne
    have h0 : ContinuousAt (fun q : ↥D.compl ↦ e₀ (q : M)) y :=
      (e₀.continuousAt hys).comp continuous_subtype_val.continuousAt
    have h1 : ContinuousAt (fun q : ↥D.compl ↦ dist (e₀ (q : M)) c₀) y :=
      h0.dist continuousAt_const
    have h2 : dist (e₀ (y : M)) c₀ ≠ 0 := dist_ne_zero.2 hyne
    exact continuousAt_const.mul ((h1.log h2).sub continuousAt_const)
  -- Every family member dips below the barrier on the annulus.
  have hdipFam : ∀ u ∈ Fam, ∀ y ∈ Aann, u y ≤ hbar y := by
    rintro u ⟨husub, hule, Ku, hKu, hKuz⟩ y hy
    have hkey : ∀ z ∈ Aann, u z - hbar z ≤ 0 := by
      apply maxPrin Aann (fun z ↦ u z - hbar z) 0 Ku hAannopen hAannne ?_ hKu ?_ ?_
      · -- subharmonicity of the difference
        intro z hz
        exact (husub z (hAannW hz)).sub_mharmonicAt (hbarHarm z hz)
      · -- off the compact support the barrier dominates
        intro z hz hzK
        obtain ⟨-, h2, -⟩ := (hAannmem z).1 hz
        have h3 : u z = 0 := hKuz z (hAannW hz) hzK
        have h4 : 0 ≤ hbar z := by
          rw [hhbar]
          apply mul_nonneg ha1pos.le
          rw [sub_nonneg]
          exact Real.log_le_log hρ₀pos h2.le
        linarith
      · -- boundary points lie on the enlarged circle where the barrier is `1`
        rintro z ⟨hzcl, hzA⟩
        have hzChat : z ∈ Chat := (hChatcl.closure_subset_iff.2 hAannChat) hzcl
        obtain ⟨hzsrc, hzgt, hzle⟩ := hcollarpts z hzChat
        have hzeq : dist (e₀ (z : M)) c₀ = ρ₁ := by
          rcases lt_or_eq_of_le hzle with h | h
          · exact absurd ((hAannmem z).2 ⟨hzsrc, hzgt, h⟩) hzA
          · exact h
        have hzW : z ∈ Wset := hChatW hzChat
        have hzne : e₀ (z : M) ≠ c₀ := by
          intro hcon
          rw [hcon, dist_self] at hzgt
          exact absurd hzgt (not_lt.2 hρ₀pos.le)
        refine ⟨((husub z hzW).continuousAt).sub (hbarCont z hzsrc hzne), ?_⟩
        have hb1 : hbar z = 1 := by
          rw [hhbar]
          simp only
          rw [hzeq, ha1]
          exact inv_mul_cancel₀ hloggap.ne'
        have := hule z hzW
        linarith
    have := hkey y hy
    linarith
  -- The midpoint of the annulus.
  set ρm : ℝ := (D.radius + ρ₁) / 2 with hρm
  have hρmgt : D.radius < ρm := by rw [hρm]; linarith
  have hρmlt : ρm < ρ₁ := by rw [hρm]; linarith
  have hρmpos : 0 < ρm := hρ₀pos.trans hρmgt
  have hmiddist : dist (c₀ + ((ρm : ℝ) : ℂ)) c₀ = ρm := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hρmpos.le]
  have hwmid : c₀ + ((ρm : ℝ) : ℂ) ∈ closedBall c₀ ρ₁ := by
    rw [mem_closedBall, hmiddist]
    exact hρmlt.le
  have hwtmid : c₀ + ((ρm : ℝ) : ℂ) ∈ e₀.target := hρ₁sub hwmid
  have hmidM : e₀.symm (c₀ + ((ρm : ℝ) : ℂ)) ∈ D.compl := by
    intro hcon
    obtain ⟨w', hw', hww⟩ := hcon
    have hwt' : w' ∈ e₀.target := hρ₁sub ((closedBall_subset_closedBall hρ₁gt.le) hw')
    have heq : w' = c₀ + ((ρm : ℝ) : ℂ) := by
      have := congrArg (⇑e₀) hww
      rwa [e₀.right_inv hwt', e₀.right_inv hwtmid] at this
    rw [heq] at hw'
    have h1 := mem_closedBall.1 hw'
    rw [hmiddist] at h1
    linarith
  set ymid : ↥D.compl := ⟨e₀.symm (c₀ + ((ρm : ℝ) : ℂ)), hmidM⟩ with hymid
  have hymidval : dist (e₀ ((ymid : ↥D.compl) : M)) c₀ = ρm := by
    rw [hymid]
    simp only
    rw [e₀.right_inv hwtmid, hmiddist]
  have hymidA : ymid ∈ Aann := by
    rw [hAannmem]
    refine ⟨?_, ?_, ?_⟩
    · rw [hymid]
      exact e₀.map_target hwtmid
    · rw [hymidval]; exact hρmgt
    · rw [hymidval]; exact hρmlt
  have hymidW : ymid ∈ Wset := hAannW hymidA
  set tmid : ℝ := a1 * (Real.log ρm - Real.log D.radius) with htmid
  have htmidlt : tmid < 1 := by
    rw [htmid, ha1]
    have h1 : Real.log ρm - Real.log D.radius < Real.log ρ₁ - Real.log D.radius := by
      have := Real.log_lt_log hρmpos hρmlt
      linarith
    calc (Real.log ρ₁ - Real.log D.radius)⁻¹ * (Real.log ρm - Real.log D.radius)
        < (Real.log ρ₁ - Real.log D.radius)⁻¹ * (Real.log ρ₁ - Real.log D.radius) :=
          mul_lt_mul_of_pos_left h1 ha1pos
      _ = 1 := inv_mul_cancel₀ hloggap.ne'
  have hbarmid : hbar ymid = tmid := by
    rw [hhbar, htmid]
    simp only
    rw [hymidval]
  have hdip : omeg ymid ≤ tmid := by
    refine csSup_le (hFamne ymid) ?_
    rintro b ⟨u, hu, rfl⟩
    have := hdipFam u hu ymid hymidA
    rwa [hbarmid] at this
  -- ## Strict bound below `1` everywhere on the region
  have homeglt1 : ∀ y ∈ Wset, omeg y < 1 := by
    intro y hy
    rcases lt_or_eq_of_le (homegle1 y hy) with hlt | heq
    · exact hlt
    exfalso
    have hmax : ∀ z ∈ Wset, omeg z ≤ omeg y := by
      intro z hz
      rw [heq]
      exact homegle1 z hz
    have hconst := propagate Wset omeg y hWopen hWconn.isPreconnected hy
      (fun z hz ↦ (homegHarm z hz).msubharmonicAt) hmax
    have h1 : omeg ymid = omeg y := hconst ymid hymidW
    rw [heq] at h1
    have := hdip
    rw [h1] at this
    linarith
  -- The maximum of the envelope over the outer circle.
  have homegcont : ContinuousOn omeg Γout :=
    fun y hy ↦ ((homegHarm y (hΓoutW hy)).continuousAt).continuousWithinAt
  obtain ⟨ystar, hystar, hystarmax⟩ := hΓoutcomp.exists_isMaxOn hΓoutne homegcont
  set tstar : ℝ := omeg ystar with htstar
  have htstarlt : tstar < 1 := homeglt1 ystar (hΓoutW hystar)
  set dlt : ℝ := 1 - tstar with hdlt
  have hdltpos : 0 < dlt := by rw [hdlt]; linarith
  -- ## The uniform bound on the Green family
  refine ⟨x₀, hx₀ne, ⟨max (Real.log 2 / dlt) 0, ?_⟩⟩
  rintro b ⟨v, hv, rfl⟩
  obtain ⟨hvsub, hvcont, ⟨Kv, hKvcomp, -, hKvzero⟩, Cv, hCv⟩ := hv
  -- The maxima of the candidate over the two circles.
  obtain ⟨xin, hxin, hxinmax⟩ := hΓincomp.exists_isMaxOn hΓinne
    (hvcont.mono hΓinW)
  obtain ⟨xout, hxout, hxoutmax⟩ := hΓoutcomp.exists_isMaxOn hΓoutne
    (hvcont.mono (hΓoutW.trans hWsub))
  set m : ℝ := v xin with hm
  set Mo : ℝ := v xout with hMo
  -- Continuity of the candidate at points away from the pole.
  have hvCA : ∀ y : ↥D.compl, y ≠ p₀ → ContinuousAt v y := by
    intro y hy
    exact hvcont.continuousAt
      (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hy))
  -- ### Interior bound: `v ≤ max m 0` on the region
  have hIntB : ∀ y ∈ Wset, v y ≤ max m 0 := by
    apply maxPrin Wset v (max m 0) Kv hWopen hWne (fun y hy ↦ hvsub y (hWsub hy))
      hKvcomp
    · intro y hy hyK
      rw [hKvzero y hyK]
      exact le_max_right _ _
    · rintro y ⟨hycl, hyW⟩
      have hyD : y ∈ Dp.closedCarrier := not_not.1 (fun h ↦ hyW h)
      obtain ⟨hysrc, hyd⟩ := hcarmem y hyD
      have hydeq : dist (eN y) z₀ = R / 2 := by
        rcases lt_or_eq_of_le hyd with h | h
        · exfalso
          have hBopen : IsOpen (eN.source ∩ eN ⁻¹' ball z₀ (R / 2)) :=
            eN.continuousOn.isOpen_inter_preimage eN.open_source isOpen_ball
          have hBsubD : eN.source ∩ eN ⁻¹' ball z₀ (R / 2) ⊆ Dp.closedCarrier := by
            rw [hDpcar, himgN eN _ ((closedBall_subset_closedBall (by linarith)).trans
              hRtgt)]
            exact Set.inter_subset_inter (subset_refl _)
              (Set.preimage_mono ball_subset_closedBall)
          have hyint : y ∈ interior Dp.closedCarrier :=
            interior_maximal hBsubD hBopen ⟨hysrc, h⟩
          rw [hWdef, closure_compl] at hycl
          exact hycl hyint
        · exact h
      have hyΓ : y ∈ Γin := hΓmem (R / 2) (by linarith) y hysrc hydeq
      have hyne : y ≠ p₀ := (hΓprop (R / 2) (by positivity) (by linarith) y hyΓ).2.2
      exact ⟨hvCA y hyne, le_trans (hxinmax hyΓ) (le_max_left _ _)⟩
  -- ### Growth estimate: `v ≤ Mo + log 2` on the inner circle
  -- The pole bound holds on a small chart ball.
  obtain ⟨Nv, hNvnhds, hNv⟩ := (eventually_nhdsWithin_iff.mp hCv).exists_mem
  have hprev : eN.target ∩ eN.symm ⁻¹' Nv ∈ 𝓝 z₀ := by
    have h1 : ContinuousAt eN.symm z₀ := eN.continuousAt_symm hz₀tgt
    have h3 : eN.symm ⁻¹' Nv ∈ 𝓝 z₀ := h1.preimage_mem_nhds (hsymz₀ ▸ hNvnhds)
    exact Filter.inter_mem (eN.open_target.mem_nhds hz₀tgt) h3
  obtain ⟨σ₀, hσ₀pos, hσ₀sub⟩ := nhds_basis_closedBall.mem_iff.1 hprev
  have hCbound : ∀ y : ↥D.compl, y ∈ eN.source → eN y ∈ closedBall z₀ σ₀ → y ≠
      p₀ →
      v y + Real.log (dist (eN y) z₀) ≤ Cv := by
    intro y hys hyball hyne
    have h3 : eN y ∈ eN.symm ⁻¹' Nv := (hσ₀sub hyball).2
    have h4 : y ∈ Nv := by rwa [Set.mem_preimage, eN.left_inv hys] at h3
    have h5 := hNv y h4 (Set.mem_compl_singleton_iff.mpr hyne)
    have h6 : ‖poleCoord p₀ y‖ = dist (eN y) z₀ := by
      simp only [poleCoord, ← heN, ← hz₀, dist_eq_norm]
    rwa [h6] at h5
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hGrow : ∀ y ∈ Γin, v y ≤ Mo + Real.log 2 := by
    intro y hyΓ
    obtain ⟨hysrc, hydist, hyne⟩ := hΓprop (R / 2) (by positivity) (by linarith) y hyΓ
    refine le_of_forall_pos_le_add ?_
    intro ε' hε'
    set ε : ℝ := ε' / Real.log 2 with hε
    have hεpos : 0 < ε := div_pos hε' hlog2
    have hεlog : ε * Real.log 2 = ε' := by
      rw [hε]
      exact div_mul_cancel₀ ε' hlog2.ne'
    -- choice of the excision radius
    set Q : ℝ := (Mo - Cv + (1 + ε) * Real.log R) / ε with hQ
    set σ : ℝ := min (min σ₀ (R / 4)) (Real.exp Q) with hσ
    have hσpos : 0 < σ := lt_min (lt_min hσ₀pos (by positivity)) (Real.exp_pos Q)
    have hσσ₀ : σ ≤ σ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hσR4 : σ ≤ R / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) :=
            Real.log_le_log hσpos (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hεQ : ε * Q = Mo - Cv + (1 + ε) * Real.log R := by
      rw [hQ, mul_comm]
      exact div_mul_cancel₀ _ hεpos.ne'
    -- the annulus region and the competitor
    set Ωσ : Set ↥D.compl := eN.symm '' (ball z₀ R \ closedBall z₀ σ) with hΩσ
    have hΩσsub : ball z₀ R \ closedBall z₀ σ ⊆ eN.target :=
      (Set.sdiff_subset.trans ball_subset_closedBall).trans hRtgt
    have hΩσopen : IsOpen Ωσ := by
      rw [hΩσ, himgN eN _ hΩσsub]
      exact eN.continuousOn.isOpen_inter_preimage eN.open_source
        (isOpen_ball.sdiff isClosed_closedBall)
    have hΩσmem : ∀ z ∈ Ωσ, z ∈ eN.source ∧ σ < dist (eN z) z₀ ∧ dist (eN z) z₀ <
        R := by
      intro z hz
      rw [hΩσ, himgN eN _ hΩσsub] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall] at hz2
      exact ⟨hz1, not_le.1 hz2.2, hz2.1⟩
    have hΩσmem' : ∀ z : ↥D.compl, z ∈ eN.source → σ < dist (eN z) z₀ →
        dist (eN z) z₀ < R → z ∈ Ωσ := by
      intro z hz1 hz2 hz3
      rw [hΩσ, himgN eN _ hΩσsub]
      refine ⟨hz1, ?_⟩
      rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall]
      exact ⟨hz3, not_le.2 hz2⟩
    have hp₀Ωσ : p₀ ∉ Ωσ := by
      intro hcon
      obtain ⟨-, h2, -⟩ := hΩσmem p₀ hcon
      rw [← hz₀, dist_self] at h2
      exact absurd h2 (not_lt.2 hσpos.le)
    have hΩσne : Ωσ ≠ Set.univ := by
      intro hcon
      apply hp₀Ωσ
      rw [hcon]
      trivial
    set Kσ : Set ↥D.compl := eN.symm '' (closedBall z₀ R \ ball z₀ σ) with hKσ
    have hKσcomp : IsCompact Kσ :=
      ((isCompact_closedBall z₀ R).diff isOpen_ball).image_of_continuousOn
        (eN.continuousOn_symm.mono (Set.sdiff_subset.trans hRtgt))
    have hΩσKσ : Ωσ ⊆ Kσ :=
      Set.image_mono (fun w hw ↦ ⟨ball_subset_closedBall hw.1,
        fun h ↦ hw.2 (ball_subset_closedBall h)⟩)
    -- harmonicity of the logarithmic barrier at annulus points
    have hbharmN : ∀ z : ↥D.compl, z ∈ eN.source → eN z ≠ z₀ →
        MHarmonicAt (fun q ↦ Real.log (dist (eN q) z₀)) z := by
      intro z hzs hzne
      have h1 : MHarmonicAt (fun q ↦ Real.log (dist (eN q) z₀)) z ↔
          HarmonicAt ((fun q ↦ Real.log (dist (eN q) z₀)) ∘ eN.symm) (eN z) :=
        mharmonicAt_iff_of_mem_maximalAtlas heNatlas hzs
      rw [h1]
      have hharm : HarmonicAt (fun w : ℂ ↦ Real.log ‖w - z₀‖) (eN z) := by
        apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ ↦ w - z₀)
        · exact analyticAt_id.sub analyticAt_const
        · exact sub_ne_zero.2 hzne
      have heqv : (fun w : ℂ ↦ Real.log ‖w - z₀‖) =ᶠ[𝓝 (eN z)]
          ((fun q ↦ Real.log (dist (eN q) z₀)) ∘ eN.symm) := by
        filter_upwards [eN.open_target.mem_nhds (eN.map_source hzs)] with w hw
        simp only [Function.comp_apply, eN.right_inv hw, dist_eq_norm]
      exact (harmonicAt_congr_nhds heqv).1 hharm
    -- continuity of the logarithmic barrier
    have hbcont : ∀ z : ↥D.compl, z ∈ eN.source → eN z ≠ z₀ →
        ContinuousAt (fun q ↦ Real.log (dist (eN q) z₀)) z := by
      intro z hzs hzne
      have h2 : ContinuousAt eN z := eN.continuousAt hzs
      have h3 : dist (eN z) z₀ ≠ 0 := (dist_pos.2 hzne).ne'
      exact ((h2.dist continuousAt_const).log h3)
    -- the competitor and its subharmonicity
    set Wf : ↥D.compl → ℝ :=
      fun q ↦ v q + (1 + ε) * (Real.log (dist (eN q) z₀) - Real.log R) with hWf
    have hWfsub : MSubharmonicOn Wf Ωσ := by
      intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hΩσmem z hz
      have hzne : eN z ≠ z₀ := by
        intro hcon
        rw [hcon, dist_self] at hz2
        exact absurd hz2 (not_lt.2 hσpos.le)
      have hznep : z ≠ p₀ := hnep z hz1 hzne
      have hu : MHarmonicAt
          (fun q ↦ (-(1 + ε)) * Real.log (dist (eN q) z₀) + (1 + ε) * Real.log R) z :=
        mharmAffine _ z _ _ (hbharmN z hz1 hzne)
      have h7 := (hvsub z (Set.mem_compl_singleton_iff.mpr hznep)).sub_mharmonicAt hu
      convert h7 using 2
      rw [hWf]
      simp only
      ring
    -- boundary control
    have hWfbd : ∀ z ∈ closure Ωσ \ Ωσ, ContinuousAt Wf z ∧ Wf z ≤ Mo := by
      rintro z ⟨hzcl, hzΩ⟩
      have hzK : z ∈ Kσ := (hKσcomp.isClosed.closure_subset_iff.2 hΩσKσ) hzcl
      obtain ⟨w, ⟨hw1, hw2⟩, hwz⟩ := hzK
      have hwt : w ∈ eN.target := hRtgt hw1
      have hzsrc : z ∈ eN.source := hwz ▸ eN.map_target hwt
      have hzval : eN z = w := by rw [← hwz, eN.right_inv hwt]
      have hzd1 : σ ≤ dist (eN z) z₀ := by
        rw [hzval]
        exact not_lt.1 (fun h ↦ hw2 (mem_ball.2 h))
      have hzd2 : dist (eN z) z₀ ≤ R := by rw [hzval]; exact mem_closedBall.1 hw1
      have hzne : eN z ≠ z₀ := by
        intro hcon
        rw [hcon, dist_self] at hzd1
        exact absurd hzd1 (not_le.2 hσpos)
      have hznep : z ≠ p₀ := hnep z hzsrc hzne
      have hcont : ContinuousAt Wf z := by
        rw [hWf]
        exact (hvCA z hznep).add
          (continuousAt_const.mul ((hbcont z hzsrc hzne).sub continuousAt_const))
      refine ⟨hcont, ?_⟩
      have hdisj : dist (eN z) z₀ = σ ∨ dist (eN z) z₀ = R := by
        rcases lt_or_eq_of_le hzd1 with h1 | h1
        · rcases lt_or_eq_of_le hzd2 with h2 | h2
          · exact absurd (hΩσmem' z hzsrc h1 h2) hzΩ
          · exact Or.inr h2
        · exact Or.inl h1.symm
      rcases hdisj with hzd | hzd
      · -- inner circle: the pole bound beats the barrier
        have hσball : eN z ∈ closedBall z₀ σ₀ := by
          rw [mem_closedBall, hzd]
          exact hσσ₀
        have hvz : v z + Real.log σ ≤ Cv := by
          have := hCbound z hzsrc hσball hznep
          rwa [hzd] at this
        rw [hWf]
        simp only
        rw [hzd]
        have h8 : ε * Real.log σ ≤ ε * Q := mul_le_mul_of_nonneg_left hσQ hεpos.le
        rw [hεQ] at h8
        nlinarith only [hvz, h8]
      · -- outer circle: bounded by the outer maximum
        have hzΓ : z ∈ Γout := hΓmem R le_rfl z hzsrc hzd
        rw [hWf]
        simp only
        rw [hzd, sub_self, mul_zero, add_zero]
        exact hxoutmax hzΓ
    have hWfle : ∀ z ∈ Ωσ, Wf z ≤ Mo := by
      apply maxPrin Ωσ Wf Mo Kσ hΩσopen hΩσne hWfsub hKσcomp ?_ hWfbd
      intro z hz hzK
      exact absurd (hΩσKσ hz) hzK
    -- evaluate at the inner circle
    have hyΩσ : y ∈ Ωσ := by
      apply hΩσmem' y hysrc
      · rw [hydist]; linarith
      · rw [hydist]; linarith
    have h9 := hWfle y hyΩσ
    rw [hWf] at h9
    simp only at h9
    rw [hydist] at h9
    have h10 : Real.log (R / 2) = Real.log R - Real.log 2 :=
      Real.log_div hR.ne' two_ne_zero
    rw [h10] at h9
    have h11 : (1 + ε) * (Real.log R - Real.log 2 - Real.log R) = -(1 + ε) * Real.log 2 := by
      ring
    rw [h11] at h9
    have h12 : (1 + ε) * Real.log 2 = Real.log 2 + ε' := by
      rw [add_mul, one_mul, hεlog]
    linarith only [h9, h12]
  -- ### Assembly of the uniform bound
  have hvx₀ : v x₀ ≤ m := hxinmax hx₀Γin
  rcases le_or_gt m 0 with hm0 | hm0
  · exact le_trans hvx₀ (le_trans hm0 (le_max_right _ _))
  · -- the normalized candidate joins the harmonic-measure family
    have hmax0 : max m 0 = m := max_eq_left hm0.le
    set u : ↥D.compl → ℝ := fun y ↦ m⁻¹ * v y with hu
    have humem : u ∈ Fam := by
      refine ⟨?_, ?_, Kv, hKvcomp, ?_⟩
      · intro y hy
        exact msubSmul v m⁻¹ (by positivity) y (hvsub y (hWsub hy))
      · intro y hy
        rw [hu]
        simp only
        calc m⁻¹ * v y ≤ m⁻¹ * m := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have := hIntB y hy
              rwa [hmax0] at this
          _ = 1 := inv_mul_cancel₀ hm0.ne'
      · intro y hy hyK
        rw [hu]
        simp only
        rw [hKvzero y hyK, mul_zero]
    have hvle : ∀ y ∈ Wset, v y ≤ m * omeg y := by
      intro y hy
      have h1 : u y ≤ omeg y := homegge y hy u humem
      have h2 : v y = m * u y := by
        rw [hu]
        simp only
        rw [← mul_assoc, mul_inv_cancel₀ hm0.ne', one_mul]
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hm0.le
    -- close the bootstrap
    have hMole : Mo ≤ m * tstar := by
      have h1 := hvle xout (hΓoutW hxout)
      have h2 : omeg xout ≤ tstar := hystarmax hxout
      calc Mo = v xout := rfl
        _ ≤ m * omeg xout := h1
        _ ≤ m * tstar := mul_le_mul_of_nonneg_left h2 hm0.le
    have hmle : m ≤ Mo + Real.log 2 := hGrow xin hxin
    have hkey : m * dlt ≤ Real.log 2 := by
      rw [hdlt]
      nlinarith only [hMole, hmle]
    have hmfin : m ≤ Real.log 2 / dlt := by
      rw [le_div_iff₀ hdltpos]
      exact hkey
    exact le_trans hvx₀ (le_trans hmfin (le_max_left _ _))

end RiemannDynamics
