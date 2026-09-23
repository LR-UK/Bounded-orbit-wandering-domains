import FunctionTheory.Conformal.CircularArcCap
import FunctionTheory.Conformal.SeparatingCrosscut

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

/-- The local crosscut estimate underlying Carathéodory continuity. The
approach region is cut by circular arcs; the rest of the boundary is arbitrary. -/
theorem exists_boundary_cap_for_circular_approach
    {U : Set ℂ} {f g : ℂ → ℂ} {R α β δ : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (h0 : (0 : ℂ) ∉ U)
    (hg : ContinuousOn g (ball 0 1)) (hgU : MapsTo g (ball 0 1) U)
    (hfg : RightInvOn g f (ball 0 1)) (hgf : LeftInvOn g f U)
    (hR : 0 < R) (hα : α < 0) (hβ : 0 < β) (hwidth : β ≤ α + 2 * Real.pi)
    (harcs : ∀ ρ ∈ Ioo 0 R,
      (∀ θ ∈ Ioo α β, circleMap 0 ρ θ ∈ U) ∧
      circleMap 0 ρ β ∈ frontier U ∧
      ∀ z ∈ U ∩ sphere (0 : ℂ) ρ, ∃ θ ∈ Ioo α β, z = circleMap 0 ρ θ)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ ρ > 0, ∃ a ∈ sphere (0 : ℂ) 1,
      ∀ z ∈ U ∩ ball (0 : ℂ) ρ, f z ∈ closedBall a δ := by
  have hg0U : g 0 ∈ U := hgU (by simp)
  have hg0ne : g 0 ≠ 0 := fun heq => h0 (heq ▸ hg0U)
  have hnorm : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0ne
  let R' := min (R / 2) (‖g 0‖ / 2)
  have hR' : 0 < R' := lt_min (half_pos hR) (half_pos hnorm)
  have hR'R : R' < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hR'g : R' < ‖g 0‖ := (min_le_right _ _).trans_lt (half_lt_self hnorm)
  obtain ⟨r, hr, hchoice⟩ := exists_uniform_annulus_of_bounded_image
    (B := ball (0 : ℂ) 1) isBounded_ball (half_pos hδ) hR'
  obtain ⟨ρ, hρ, hlen⟩ := hchoice U f 0 hU hf hbij.injOn hbij.mapsTo
  have hρpos : 0 < ρ := hr.1.trans hρ.1
  have hρR : ρ < R := hρ.2.trans hR'R
  obtain ⟨harc, hend, hcover⟩ := harcs ρ ⟨hρpos, hρR⟩
  obtain ⟨a, ha, hcap⟩ := exists_boundary_cap_containing_short_circular_arc
    hU hf hbij hρpos hα hβ hwidth harc hend hlen
  have hb : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ closedBall a δ := by
    refine ⟨by simp, ?_⟩
    have ha' : dist (0 : ℂ) a = 1 := by simpa only [dist_comm] using mem_sphere.mp ha
    simpa only [mem_closedBall, ha'] using (not_le.mpr hδ1)
  have hqb : 0 < dist (g 0) 0 - ρ := by
    rw [dist_zero_right]
    linarith [hρ.2, hR'g]
  have hzero : ∀ w ∈ ball (0 : ℂ) 1, dist (g w) 0 - ρ = 0 →
      w ∈ closedBall a δ := by
    intro w hw hq
    have hgsphere : g w ∈ sphere (0 : ℂ) ρ := sub_eq_zero.mp hq
    obtain ⟨θ, hθ, heq⟩ := hcover (g w) ⟨hgU hw, hgsphere⟩
    have h := hcap θ hθ
    rw [← heq, hfg hw] at h
    exact h
  have hqcont : ContinuousOn (fun w => dist (g w) 0 - ρ) (ball (0 : ℂ) 1) := by
    simp only [dist_zero_right]
    fun_prop
  have hside := nonpositive_side_subset_boundary_cap hqcont
    ha hδ (by linarith) hb hqb hzero
  refine ⟨ρ, hρpos, a, ha, ?_⟩
  intro z hz
  apply hside
  refine ⟨hbij.mapsTo hz.1, ?_⟩
  rw [hgf hz.1]
  exact (sub_neg.mpr (mem_ball.mp hz.2)).le

/-- Local Carathéodory continuity from circular crosscuts. No Jordan or local
connectedness condition is imposed on the boundary away from the chosen point. -/
theorem exists_boundary_limit_of_circular_approach
    {U : Set ℂ} {f : ℂ → ℂ} {R α β : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (h0 : (0 : ℂ) ∈ frontier U)
    (hR : 0 < R) (hα : α < 0) (hβ : 0 < β) (hwidth : β ≤ α + 2 * Real.pi)
    (harcs : ∀ ρ ∈ Ioo 0 R,
      (∀ θ ∈ Ioo α β, circleMap 0 ρ θ ∈ U) ∧
      circleMap 0 ρ β ∈ frontier U ∧
      ∀ z ∈ U ∩ sphere (0 : ℂ) ρ, ∃ θ ∈ Ioo α β, z = circleMap 0 ρ θ) :
    ∃ a ∈ sphere (0 : ℂ) 1, Tendsto f (𝓝[U] 0) (𝓝 a) := by
  let g := invFunOn f U
  have hg : DifferentiableOn ℂ g (ball 0 1) := by
    have h := DifferentiableOn.invFunOn hf hU hbij.injOn
    rwa [hbij.image_eq] at h
  have hsub : (TauCeti.clusterSetOn f U 0).Subsingleton := by
    apply TauCeti.subsingleton_clusterSetOn_of_forall_exists
    intro ε hε
    let δ := min (ε / 2) (1 / 2 : ℝ)
    have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨ρ, hρ, a, _, hcap⟩ := exists_boundary_cap_for_circular_approach
      hU hf hbij (hU.frontier_eq ▸ h0).2 hg.continuousOn hbij.surjOn.mapsTo_invFunOn
      hbij.invOn_invFunOn.2 hbij.invOn_invFunOn.1 hR hα hβ hwidth harcs hδ hδ1
    refine ⟨ρ, hρ, ?_⟩
    intro x hx y hy
    have hxcap := mem_closedBall.mp (hcap x hx)
    have hycap := mem_closedBall.mp (hcap y hy)
    have htri := dist_triangle (f x) a (f y)
    rw [dist_comm a] at htri
    have hδε : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have : (𝓝[U] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp h0.1
  obtain ⟨a, ha⟩ := TauCeti.exists_tendsto_of_clusterSetOn_subsingleton
    (isCompact_closedBall (0 : ℂ) 1) (fun z hz => ball_subset_closedBall (hbij.mapsTo hz)) h0.1 hsub
  have hacircle := TauCeti.clusterSetOn_subset_frontier_image hU hf hbij.injOn h0 ha.mapClusterPt
  refine ⟨a, ?_, ha⟩
  simpa only [hbij.image_eq, frontier_ball _ one_ne_zero] using hacircle

end FunctionTheory
