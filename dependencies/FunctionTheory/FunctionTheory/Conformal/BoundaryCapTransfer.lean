import FunctionTheory.Conformal.SeparatingCrosscut
import FunctionTheory.Conformal.CircularArcCap
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Metric Complex Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A closed source piece whose relative boundary maps into a small disc
cap also maps into that cap, provided a reference point lies outside the
piece. The signed-distance barrier works for curved coordinate boundaries. -/
theorem image_closed_piece_subset_boundary_cap
    {U P : Set ℂ} {f g : ℂ → ℂ} {a : ℂ} {δ : ℝ}
    (hP : IsClosed P) (hPne : P.Nonempty)
    (hg : ContinuousOn g (ball (0:ℂ) 1)) (hgU : MapsTo g (ball (0:ℂ) 1) U)
    (hgf : LeftInvOn g f U) (hfg : RightInvOn g f (ball (0:ℂ) 1))
    (hfD : MapsTo f U (ball (0:ℂ) 1))
    (hbase : g 0∉P) (ha : a∈sphere (0:ℂ) 1) (hδ : 0<δ) (hδ1 : δ<1)
    (hfront : ∀ z∈frontier P∩U, f z∈closedBall a δ) :
    ∀ z∈P∩U, f z∈closedBall a δ := by
  let q : ℂ → ℝ := fun z => infDist z P-infDist z Pᶜ
  have hqc : Continuous q := (continuous_infDist_pt P).sub (continuous_infDist_pt Pᶜ)
  have hPc : Pᶜ.Nonempty := ⟨g 0,hbase⟩
  have hqbase : 0<q (g 0) := by
    dsimp only [q]
    rw [infDist_zero_of_mem (s := Pᶜ) hbase,sub_zero]
    exact (hP.notMem_iff_infDist_pos hPne).mp hbase
  have hzero : ∀ z∈U, q z=0 → f z∈closedBall a δ := by
    intro z hz H
    have Hdist : infDist z P=infDist z Pᶜ := sub_eq_zero.mp H
    have hdist0 : infDist z P=0 ∧ infDist z Pᶜ=0 := by
      by_cases hmem : z∈P
      · have HP := infDist_zero_of_mem hmem
        exact ⟨HP,Hdist.symm.trans HP⟩
      · have HP : infDist z Pᶜ=0 := infDist_zero_of_mem hmem
        exact ⟨Hdist.trans HP,HP⟩
    apply hfront z ⟨?_,hz⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨(mem_closure_iff_infDist_zero hPne).mpr hdist0.1,
      (mem_closure_iff_infDist_zero hPc).mpr hdist0.2⟩
  have h0cap : (0:ℂ)∈ball (0:ℂ) 1 \ closedBall a δ := by
    refine ⟨mem_ball_self one_pos,?_⟩
    have H : dist (0:ℂ) a=1 := by simpa only [dist_comm] using mem_sphere.mp ha
    simpa only [mem_closedBall,H] using not_le.mpr hδ1
  have Hcap := nonpositive_side_subset_boundary_cap (hqc.continuousOn.comp hg hgU)
    ha hδ (by linarith) h0cap hqbase (by
      intro w hw H
      simpa only [hfg hw] using hzero (g w) (hgU hw) H)
  intro z hz
  apply Hcap
  refine ⟨hfD hz.2,?_⟩
  change q (g (f z))≤0
  rw [hgf hz.2]
  dsimp only [q]
  rw [infDist_zero_of_mem hz.1,zero_sub]
  exact neg_nonpos.mpr infDist_nonneg

/-- The short-arc cap estimate only needs boundary cluster values on the
unit circle. This local version allows a nonlinear analytic source chart;
the map need not be onto the whole disc. -/
theorem exists_boundary_cap_of_short_arc_and_circle_clusters
    {W : Set ℂ} {H : ℂ → ℂ} {ρ ε α β : ℝ}
    (hW : IsOpen W) (hH : DifferentiableOn ℂ H W)
    (hmap : MapsTo H W (ball (0:ℂ) 1))
    (hρ : 0<ρ) (hα : α<0) (hβ : 0<β) (hwidth : β≤α+2*Real.pi)
    (harc : ∀ θ∈Ioo α β, circleMap 0 ρ θ∈W)
    (hcluster : TauCeti.clusterSetOn H W (circleMap 0 ρ β)⊆sphere (0:ℂ) 1)
    (hlen : TauCeti.circleImageLength H W 0 ρ < ENNReal.ofReal (ε/2)) :
    ∃ a∈sphere (0:ℂ) 1, ∀ θ∈Ioo α β, H (circleMap 0 ρ θ)∈closedBall a ε := by
  let C := circleMap (0:ℂ) ρ '' Ioo α β
  have hCW : C⊆W := by rintro z ⟨θ,hθ,rfl⟩; exact harc θ hθ
  have hecl : circleMap (0:ℂ) ρ β∈closure C := by
    have hc : Continuous (circleMap (0:ℂ) ρ) := by unfold circleMap; fun_prop
    apply hc.continuousAt.continuousWithinAt.mem_closure_image
    rw [closure_Ioo (hα.trans hβ).ne]
    exact ⟨(hα.trans hβ).le,le_rfl⟩
  obtain ⟨a,ha⟩ := TauCeti.clusterSetOn_nonempty (isCompact_closedBall (0:ℂ) 1)
    (fun z hz => ball_subset_closedBall (hmap (hCW hz))) hecl
  have hacircle : a∈sphere (0:ℂ) 1 := hcluster (TauCeti.clusterSetOn_mono hCW ha)
  have hCsmall : H '' C⊆closedBall (H ((ρ:ℂ))) (ε/2) := by
    rintro z ⟨w,⟨θ,hθ,rfl⟩,rfl⟩
    apply mem_closedBall.mpr
    simpa only [zero_add] using (dist_image_circle_arc_lt_of_length_lt hW hH hρ hα hβ hwidth harc hlen hθ).le
  have hasmall : a∈closedBall (H ((ρ:ℂ))) (ε/2) :=
    (isClosed_closedBall.closure_subset_iff.mpr hCsmall) (TauCeti.clusterSetOn_subset_closure_image ha)
  refine ⟨a,hacircle,?_⟩
  intro θ hθ
  have hθsmall := hCsmall (mem_image_of_mem H (mem_image_of_mem _ hθ))
  apply mem_closedBall.mpr
  calc
    dist (H (circleMap 0 ρ θ)) a ≤ dist (H (circleMap 0 ρ θ)) (H (ρ:ℂ)) + dist (H (ρ:ℂ)) a := dist_triangle _ _ _
    _ ≤ ε/2+ε/2 := add_le_add (mem_closedBall.mp hθsmall) (by simpa only [dist_comm] using mem_closedBall.mp hasmall)
    _ = ε := by ring

end FunctionTheory
