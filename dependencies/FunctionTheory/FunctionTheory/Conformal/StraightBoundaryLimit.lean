import FunctionTheory.Conformal.LocalCircularBoundary

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

/-- Short semicircles control the approach from one side of a straight boundary
arc. The domain is allowed to have a second component locally on its other side. -/
theorem exists_boundary_cap_at_straight_side
    {U : Set ℂ} {f : ℂ → ℂ} {R δ : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R)
    (hhalf : ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → z ∈ U)
    (hline : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → z ∉ U)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ ρ > 0, ∃ a ∈ sphere (0 : ℂ) 1,
      ∀ z ∈ U ∩ ball (0 : ℂ) ρ, 0 < z.re → f z ∈ closedBall a δ := by
  let g := invFunOn f U
  have hgd : DifferentiableOn ℂ g (ball 0 1) := by
    have h := DifferentiableOn.invFunOn hf hU hbij.injOn
    rwa [hbij.image_eq] at h
  have hg := hgd.continuousOn
  have hgU : MapsTo g (ball 0 1) U := hbij.surjOn.mapsTo_invFunOn
  have hgf : LeftInvOn g f U := hbij.invOn_invFunOn.1
  have hfg : RightInvOn g f (ball 0 1) := hbij.invOn_invFunOn.2
  have h0not : (0 : ℂ) ∉ U := hline 0 (by simpa using hR) rfl
  have hg0ne : g 0 ≠ 0 := fun heq => h0not (heq ▸ hgU (by simp))
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
  have harc : ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), circleMap 0 ρ θ ∈ U := by
    intro θ hθ
    apply hhalf
    · simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hρpos] using hρR
    · rw [circleMap_zero_re]
      exact mul_pos hρpos (Real.cos_pos_of_mem_Ioo hθ)
  have hend : circleMap 0 ρ (Real.pi / 2) ∈ frontier U := by
    have hc : Continuous (circleMap (0 : ℂ) ρ) := by unfold circleMap; fun_prop
    have hcl : circleMap 0 ρ (Real.pi / 2) ∈ closure
        (circleMap (0 : ℂ) ρ '' Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
      apply hc.continuousAt.continuousWithinAt.mem_closure_image
      rw [closure_Ioo (by linarith [Real.pi_pos] : -(Real.pi / 2) ≠ Real.pi / 2)]
      exact ⟨by linarith [Real.pi_pos], le_rfl⟩
    refine ⟨closure_mono (by rintro _ ⟨θ, hθ, rfl⟩; exact harc θ hθ) hcl, ?_⟩
    intro hi
    apply hline _ _ _ (interior_subset hi)
    · simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hρpos] using hρR
    · simp [circleMap_pi_div_two]
  obtain ⟨a, ha, hcap⟩ := exists_boundary_cap_containing_short_circular_arc hU hf hbij
    hρpos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) harc hend hlen
  let q : ℂ → ℝ := fun z => max (dist z 0 - ρ) (-z.re)
  have hqcont : Continuous q := by dsimp [q]; fun_prop
  have hzero : ∀ z ∈ U, q z = 0 →
      ∃ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), z = circleMap 0 ρ θ := by
    intro z hz hq
    have hdle : dist z 0 ≤ ρ := by
      have h := (le_max_left (dist z 0 - ρ) (-z.re)).trans (le_of_eq hq)
      linarith
    have hrege : 0 ≤ z.re := by
      have h := (le_max_right (dist z 0 - ρ) (-z.re)).trans (le_of_eq hq)
      linarith
    have hre : 0 < z.re := by
      by_contra h
      have heq := le_antisymm (le_of_not_gt h) hrege
      exact hline z (mem_ball.mpr (hdle.trans_lt hρR)) heq hz
    have hdist : dist z 0 = ρ := by
      dsimp [q] at hq
      rcases le_total (dist z 0 - ρ) (-z.re) with h | h
      · rw [max_eq_right h] at hq
        linarith
      · rw [max_eq_left h] at hq
        linarith
    have harg : |z.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    refine ⟨z.arg, abs_lt.mp harg, ?_⟩
    have hnormz : ‖z‖ = ρ := by simpa only [dist_zero_right] using hdist
    simpa only [circleMap_zero, ← hnormz] using (norm_mul_exp_arg_mul_I z).symm
  have hb0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ closedBall a δ := by
    refine ⟨by simp, ?_⟩
    have ha' : dist (0 : ℂ) a = 1 := by simpa only [dist_comm] using mem_sphere.mp ha
    simpa only [mem_closedBall, ha'] using not_le.mpr hδ1
  have hqg0 : 0 < q (g 0) := by
    apply lt_of_lt_of_le _ (le_max_left _ _)
    change 0 < dist (g 0) 0 - ρ
    rw [dist_zero_right]
    linarith [hρ.2, hR'g]
  have hzeros : ∀ w ∈ ball (0 : ℂ) 1, (q ∘ g) w = 0 → w ∈ closedBall a δ := by
    intro w hw hq
    obtain ⟨θ, hθ, heq⟩ := hzero (g w) (hgU hw) hq
    have h := hcap θ hθ
    rwa [← heq, hfg hw] at h
  have hside := nonpositive_side_subset_boundary_cap
    (hqcont.comp_continuousOn hg) ha hδ (by linarith) hb0 hqg0 hzeros
  refine ⟨ρ, hρpos, a, ha, ?_⟩
  intro z hz hre
  apply hside
  refine ⟨hbij.mapsTo hz.1, ?_⟩
  change q (g (f z)) ≤ 0
  rw [hgf hz.1]
  exact max_le (sub_nonpos.mpr (mem_ball.mp hz.2).le) (neg_nonpos.mpr hre.le)

/-- A disk map has a boundary limit from a chosen side of a locally straight
boundary, even when the domain also lies on its other side. -/
theorem exists_boundary_limit_at_straight_side
    {U : Set ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R)
    (hhalf : ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → z ∈ U)
    (hline : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → z ∉ U) :
    ∃ a ∈ sphere (0 : ℂ) 1,
      Tendsto f (𝓝[U ∩ {z : ℂ | 0 < z.re}] 0) (𝓝 a) := by
  let S := U ∩ {z : ℂ | 0 < z.re}
  have h0cl : (0 : ℂ) ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let t := min R ε / 2
    have ht : 0 < t := half_pos (lt_min hR hε)
    have htR : t < R := (half_lt_self (lt_min hR hε)).trans_le (min_le_left _ _)
    have htε : t < ε := (half_lt_self (lt_min hR hε)).trans_le (min_le_right _ _)
    have hball : (t : ℂ) ∈ ball (0 : ℂ) R := by simpa [abs_of_pos ht] using htR
    refine ⟨(t : ℂ), ⟨hhalf _ hball (by simpa using ht), by simpa using ht⟩, ?_⟩
    simpa [dist_comm, abs_of_pos ht] using htε
  have h0front : (0 : ℂ) ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨closure_mono inter_subset_left h0cl, hline 0 (by simpa using hR) rfl⟩
  have hsub : (TauCeti.clusterSetOn f S 0).Subsingleton := by
    apply TauCeti.subsingleton_clusterSetOn_of_forall_exists
    intro ε hε
    let δ := min (ε / 2) (1 / 2 : ℝ)
    have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨ρ, hρ, a, _, hcap⟩ := exists_boundary_cap_at_straight_side
      hU hf hbij hR hhalf hline hδ hδ1
    refine ⟨ρ, hρ, ?_⟩
    intro x hx y hy
    have hxcap := mem_closedBall.mp (hcap x ⟨hx.1.1, hx.2⟩ hx.1.2)
    have hycap := mem_closedBall.mp (hcap y ⟨hy.1.1, hy.2⟩ hy.1.2)
    have htri := dist_triangle (f x) a (f y)
    rw [dist_comm a] at htri
    have hδε : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have : (𝓝[S] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp h0cl
  obtain ⟨a, ha⟩ := TauCeti.exists_tendsto_of_clusterSetOn_subsingleton
    (isCompact_closedBall (0 : ℂ) 1)
    (fun z hz => ball_subset_closedBall (hbij.mapsTo hz.1)) h0cl hsub
  have hcircle := TauCeti.clusterSetOn_subset_frontier_image hU hf hbij.injOn h0front
    (TauCeti.clusterSetOn_mono inter_subset_left ha.mapClusterPt)
  exact ⟨a, by simpa only [hbij.image_eq, frontier_ball _ one_ne_zero] using hcircle, ha⟩

end FunctionTheory
