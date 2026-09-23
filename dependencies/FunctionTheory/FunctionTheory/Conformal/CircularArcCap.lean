import FunctionTheory.Conformal.UniformLengthArea
import TauCeti.Analysis.Complex.Conformal.ClusterSet

open Set Metric Complex

namespace FunctionTheory

theorem dist_image_circle_arc_lt_of_length_lt
    {U : Set ℂ} {f : ℂ → ℂ} {ζ : ℂ} {ρ ε α β : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hρ : 0 < ρ)
    (hα : α < 0) (hβ : 0 < β) (hwidth : β ≤ α + 2 * Real.pi)
    (harc : ∀ θ ∈ Ioo α β, circleMap ζ ρ θ ∈ U)
    (hlen : TauCeti.circleImageLength f U ζ ρ < ENNReal.ofReal ε)
    {θ : ℝ} (hθ : θ ∈ Ioo α β) :
    dist (f (circleMap ζ ρ θ)) (f (ζ + ρ)) < ε := by
  have hzero : circleMap ζ ρ 0 = ζ + ρ := by simp [circleMap]
  have hchord : ENNReal.ofReal (dist (f (circleMap ζ ρ θ)) (f (circleMap ζ ρ 0))) ≤
      TauCeti.circleImageLength f U ζ ρ := by
    rcases le_total θ 0 with hθ0 | h0θ
    · apply TauCeti.ofReal_dist_le_circleImageLength hU hf ζ hρ hθ0
        (by linarith [hθ.1])
      all_goals intro t ht; apply harc; constructor <;> linarith [ht.1, ht.2, hθ.1, hθ.2]
    · rw [dist_comm]
      apply TauCeti.ofReal_dist_le_circleImageLength hU hf ζ hρ h0θ
        (by linarith [hθ.2])
      all_goals intro t ht; apply harc; constructor <;> linarith [ht.1, ht.2, hθ.1, hθ.2]
  rw [hzero] at hchord
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp (hchord.trans_lt hlen)

/-- The short-arc image lies near the unit circle, without assuming a boundary
extension at its endpoint. This applies both to flat boundaries and slit tips. -/
theorem exists_boundary_cap_containing_short_circular_arc
    {U : Set ℂ} {f : ℂ → ℂ} {ζ : ℂ} {ρ ε α β : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hρ : 0 < ρ) (hα : α < 0) (hβ : 0 < β) (hwidth : β ≤ α + 2 * Real.pi)
    (harc : ∀ θ ∈ Ioo α β, circleMap ζ ρ θ ∈ U)
    (hend : circleMap ζ ρ β ∈ frontier U)
    (hlen : TauCeti.circleImageLength f U ζ ρ < ENNReal.ofReal (ε / 2)) :
    ∃ a ∈ sphere (0 : ℂ) 1, ∀ θ ∈ Ioo α β,
      f (circleMap ζ ρ θ) ∈ closedBall a ε := by
  let C := circleMap ζ ρ '' Ioo α β
  have hCU : C ⊆ U := by rintro _ ⟨θ, hθ, rfl⟩; exact harc θ hθ
  have hecl : circleMap ζ ρ β ∈ closure C := by
    have hc : Continuous (circleMap ζ ρ) := by unfold circleMap; fun_prop
    apply hc.continuousAt.continuousWithinAt.mem_closure_image
    rw [closure_Ioo (hα.trans hβ).ne]
    exact ⟨(hα.trans hβ).le, le_rfl⟩
  obtain ⟨a, ha⟩ := TauCeti.clusterSetOn_nonempty (isCompact_closedBall (0 : ℂ) 1)
    (fun z hz => ball_subset_closedBall (hbij.mapsTo (hCU hz))) hecl
  have hacircle : a ∈ sphere (0 : ℂ) 1 := by
    have h := TauCeti.clusterSetOn_subset_frontier_image hU hf hbij.injOn hend
      (TauCeti.clusterSetOn_mono hCU ha)
    simpa only [hbij.image_eq, frontier_ball _ one_ne_zero] using h
  have hCsmall : f '' C ⊆ closedBall (f (ζ + ρ)) (ε / 2) := by
    rintro _ ⟨z, ⟨θ, hθ, rfl⟩, rfl⟩
    exact mem_closedBall.mpr (dist_image_circle_arc_lt_of_length_lt
      hU hf hρ hα hβ hwidth harc hlen hθ).le
  have hasmall : a ∈ closedBall (f (ζ + ρ)) (ε / 2) :=
    closure_minimal hCsmall isClosed_closedBall (TauCeti.clusterSetOn_subset_closure_image ha)
  refine ⟨a, hacircle, ?_⟩
  intro θ hθ
  have hp := mem_closedBall.mp (hCsmall (mem_image_of_mem f (mem_image_of_mem _ hθ)))
  have ha' : dist (f (ζ + ρ)) a ≤ ε / 2 := by
    simpa only [mem_closedBall, dist_comm] using hasmall
  change dist _ a ≤ ε
  exact (dist_triangle _ _ _).trans (by linarith)

end FunctionTheory
