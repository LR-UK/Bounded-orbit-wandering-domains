import FunctionTheory.Conformal.BoundaryCapTransfer
import FunctionTheory.Conformal.AnalyticHalfDiscBoundary

open Set Metric Complex Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Local Carathéodory cap control in an arbitrary analytic coordinate.
Only the chosen side and its diameter are specified; the domain may also
occupy the other side and its remaining boundary is unrestricted. -/
theorem exists_boundary_cap_at_analytic_side
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (hei : DifferentiableOn ℂ e.symm e.target)
    {R δ : ℝ} (hR : 0<R) (hT : closedBall (0:ℂ) R⊆e.target)
    (hhalf : ∀ z∈ball (0:ℂ) R, 0<z.re → e.symm z∈U)
    (hline : ∀ z∈ball (0:ℂ) R, z.re=0 → e.symm z∉U)
    (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ<R ∧ ∃ a∈sphere (0:ℂ) 1,
      ∀ z∈ball (0:ℂ) ρ, 0<z.re → f (e.symm z)∈closedBall a δ := by
  let W := ball (0:ℂ) R∩{z : ℂ | 0<z.re}
  let H : ℂ → ℂ := fun z => f (e.symm z)
  let g := invFunOn f U
  have hgd : DifferentiableOn ℂ g (ball (0:ℂ) 1) := by
    have Hg := DifferentiableOn.invFunOn hf hU hbij.injOn
    rwa [hbij.image_eq] at Hg
  have hgU : MapsTo g (ball (0:ℂ) 1) U := hbij.surjOn.mapsTo_invFunOn
  have hWT : W⊆e.target := fun z hz => hT (ball_subset_closedBall hz.1)
  have hWU : MapsTo e.symm W U := fun z hz => hhalf z hz.1 hz.2
  have hW : IsOpen W := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hH : DifferentiableOn ℂ H W := hf.comp (hei.mono hWT) hWU
  have hHD : MapsTo H W (ball (0:ℂ) 1) := hbij.mapsTo.comp hWU
  have hHi : InjOn H W := by
    intro z hz w hw Heq
    exact e.symm.injOn (hWT hz) (hWT hw) (hbij.injOn (hWU hz) (hWU hw) Heq)
  have h0T : (0:ℂ)∈e.target := hT (mem_closedBall_self hR.le)
  have hbase : e.symm 0≠g 0 := by
    intro Heq
    apply hline 0 (mem_ball_self hR) rfl
    rw [Heq]
    exact hgU (mem_ball_self one_pos)
  have havoid : ∀ᶠ z in 𝓝 (0:ℂ), e.symm z≠g 0 :=
    (e.symm.continuousAt h0T).eventually_ne hbase
  obtain ⟨s,hs,hsavoid⟩ := Metric.mem_nhds_iff.mp havoid
  let R' := min (R/2) (s/2)
  have hR' : 0<R' := lt_min (half_pos hR) (half_pos hs)
  have hR'R : R'<R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hR's : R'<s := (min_le_right _ _).trans_lt (half_lt_self hs)
  obtain ⟨r,hr,hchoice⟩ := exists_uniform_annulus_of_bounded_image
    (B := ball (0:ℂ) 1) isBounded_ball (half_pos hδ) hR'
  obtain ⟨ρ,hρ,hlen⟩ := hchoice W H 0 hW hH hHi hHD
  have hρpos : 0<ρ := hr.1.trans hρ.1
  have hρR : ρ<R := hρ.2.trans hR'R
  have hρs : ρ<s := hρ.2.trans hR's
  have hcircleR : ∀ θ : ℝ, circleMap (0:ℂ) ρ θ∈ball (0:ℂ) R := by
    intro θ
    simpa only [mem_ball,dist_zero_right,norm_circleMap_zero,abs_of_pos hρpos] using hρR
  have harc : ∀ θ∈Ioo (-(Real.pi/2)) (Real.pi/2), circleMap 0 ρ θ∈W := by
    intro θ hθ
    refine ⟨hcircleR θ,?_⟩
    change 0<(circleMap (0:ℂ) ρ θ).re
    rw [circleMap_zero_re]
    exact mul_pos hρpos (Real.cos_pos_of_mem_Ioo hθ)
  let v := circleMap (0:ℂ) ρ (Real.pi/2)
  have hvT : v∈e.target := hT (ball_subset_closedBall (hcircleR _))
  have hvre : v.re=0 := by simp [v,circleMap_pi_div_two]
  have hvnot : e.symm v∉U := hline v (hcircleR _) hvre
  have hvcl : v∈closure W := by
    have hc : Continuous (circleMap (0:ℂ) ρ) := by unfold circleMap; fun_prop
    have Hend : v∈closure (circleMap (0:ℂ) ρ '' Ioo (-(Real.pi/2)) (Real.pi/2)) := by
      apply hc.continuousAt.continuousWithinAt.mem_closure_image
      rw [closure_Ioo (by linarith [Real.pi_pos] : -(Real.pi/2)≠Real.pi/2)]
      exact ⟨by linarith [Real.pi_pos],le_rfl⟩
    exact closure_mono (by rintro z ⟨θ,hθ,rfl⟩; exact harc θ hθ) Hend
  have hvfront : e.symm v∈frontier U := by
    refine ⟨?_,fun hi => hvnot (interior_subset hi)⟩
    exact closure_mono (image_subset_iff.mpr hWU)
      ((e.symm.continuousAt hvT).continuousWithinAt.mem_closure_image hvcl)
  have ht : Tendsto e.symm (𝓝[W] v) (𝓝[U] (e.symm v)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (e.symm.continuousAt hvT).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using hWU hz
  have hcluster : TauCeti.clusterSetOn H W v⊆sphere (0:ℂ) 1 := by
    intro a ha
    have hglobal : a∈TauCeti.clusterSetOn f U (e.symm v) := MapClusterPt.of_comp ht ha
    have Hfront := TauCeti.clusterSetOn_subset_frontier_image hU hf hbij.injOn hvfront hglobal
    simpa only [hbij.image_eq,frontier_ball _ one_ne_zero] using Hfront
  obtain ⟨a,ha,hcap⟩ := exists_boundary_cap_of_short_arc_and_circle_clusters hW hH hHD
    hρpos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) harc hcluster hlen
  let K := closedBall (0:ℂ) ρ∩{w : ℂ | 0≤w.re}
  let P := e.symm '' K
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) ρ).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hKT : K⊆e.target := fun w hw => hT (closedBall_subset_closedBall hρR.le hw.1)
  have hP : IsCompact P := hK.image_of_continuousOn (e.symm.continuousOn.mono hKT)
  have hPne : P.Nonempty := ⟨e.symm 0,0,⟨mem_closedBall_self hρpos.le,by simp⟩,rfl⟩
  have hg0 : g 0∉P := by
    rintro ⟨w,hw,heq⟩
    exact hsavoid (closedBall_subset_ball hρs hw.1) heq
  have hfront : ∀ z∈frontier P∩U, f z∈closedBall a δ := by
    intro z hz
    obtain ⟨θ,hθ,heq⟩ := exists_arc_parameter_of_frontier_half_disc_image e hρpos hKT
      (fun w hw hwr => hline w (closedBall_subset_ball hρR hw) hwr) hz
    rw [heq]
    exact hcap θ hθ
  have Hcap := image_closed_piece_subset_boundary_cap hP.isClosed hPne hgd.continuousOn hgU
    hbij.invOn_invFunOn.1 hbij.invOn_invFunOn.2 hbij.mapsTo hg0 ha hδ hδ1 hfront
  refine ⟨ρ,hρpos,hρR,a,ha,?_⟩
  intro z hz hzr
  exact Hcap (e.symm z) ⟨⟨z,⟨ball_subset_closedBall hz,hzr.le⟩,rfl⟩,
    hhalf z (ball_subset_ball hρR.le hz) hzr⟩

end FunctionTheory
