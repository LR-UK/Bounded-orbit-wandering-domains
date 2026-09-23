import FunctionTheory.Conformal.AnalyticSideCap
import FunctionTheory.Conformal.StraightBoundaryContinuous

open Set Metric Complex Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- The conformal disc map has a unique unit-circle limit on the selected
side of a regular analytic boundary chart, with no condition on the rest
of the domain's boundary. -/
theorem exists_boundary_limit_at_analytic_side
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (hei : DifferentiableOn ℂ e.symm e.target)
    {R : ℝ} (hR : 0<R) (hT : closedBall (0:ℂ) R⊆e.target)
    (hhalf : ∀ z∈ball (0:ℂ) R, 0<z.re → e.symm z∈U)
    (hline : ∀ z∈ball (0:ℂ) R, z.re=0 → e.symm z∉U) :
    ∃ a∈sphere (0:ℂ) 1,
      Tendsto (fun z => f (e.symm z))
        (𝓝[ball (0:ℂ) R∩{z : ℂ | 0<z.re}] 0) (𝓝 a) := by
  let W := ball (0:ℂ) R∩{z : ℂ | 0<z.re}
  let H : ℂ → ℂ := fun z => f (e.symm z)
  have hWU : MapsTo e.symm W U := fun z hz => hhalf z hz.1 hz.2
  have h0cl : (0:ℂ)∈closure W := mem_closure_right_half_ball (by simpa using hR) (by simp)
  have h0T : (0:ℂ)∈e.target := hT (mem_closedBall_self hR.le)
  have h0front : e.symm 0∈frontier U := by
    refine ⟨?_,fun hi => hline 0 (mem_ball_self hR) rfl (interior_subset hi)⟩
    exact closure_mono (image_subset_iff.mpr hWU)
      ((e.symm.continuousAt h0T).continuousWithinAt.mem_closure_image h0cl)
  have hsub : (TauCeti.clusterSetOn H W 0).Subsingleton := by
    apply TauCeti.subsingleton_clusterSetOn_of_forall_exists
    intro ε hε
    let δ := min (ε/2) (1/2:ℝ)
    have hδ : 0<δ := lt_min (half_pos hε) (by norm_num)
    have hδ1 : δ<1 := (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨ρ,hρ,hρR,a,ha,hcap⟩ := exists_boundary_cap_at_analytic_side
      hU hf hbij e hei hR hT hhalf hline hδ hδ1
    refine ⟨ρ,hρ,?_⟩
    intro x hx y hy
    have hxcap := mem_closedBall.mp (hcap x hx.2 hx.1.2)
    have hycap := mem_closedBall.mp (hcap y hy.2 hy.1.2)
    have Htri := dist_triangle (H x) a (H y)
    rw [dist_comm a] at Htri
    have hδε : δ≤ε/2 := min_le_left _ _
    linarith
  have : (𝓝[W] (0:ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp h0cl
  obtain ⟨a,ha⟩ := TauCeti.exists_tendsto_of_clusterSetOn_subsingleton
    (isCompact_closedBall (0:ℂ) 1)
    (fun z hz => ball_subset_closedBall (hbij.mapsTo (hWU hz))) h0cl hsub
  have ht : Tendsto e.symm (𝓝[W] (0:ℂ)) (𝓝[U] (e.symm 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (e.symm.continuousAt h0T).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using hWU hz
  have hglobal : a∈TauCeti.clusterSetOn f U (e.symm 0) := MapClusterPt.of_comp ht ha.mapClusterPt
  have hcircle := TauCeti.clusterSetOn_subset_frontier_image hU hf hbij.injOn h0front hglobal
  exact ⟨a,by simpa only [hbij.image_eq,frontier_ball _ one_ne_zero] using hcircle,ha⟩

end FunctionTheory
