import EremenkosConjecture.ReferenceDynamics

/-! # Tolerances preserving a finite stage on its control disk -/

open Set Metric Function

namespace EremenkosConjecture
namespace UniformEscapeData

theorem stageProperty_stability_closed (D : UniformEscapeData) (n : ℕ)
    (p : Polynomial ℂ) (hp : D.StageProperty n p.eval) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z ∈ controlDisc n, dist (f z) (p.eval z) < δ) → D.StageProperty n f := by
  by_cases hn : n = 0
  · subst n
    have hcompact : IsCompact (p.eval '' controlDisc 0) :=
      (isCompact_closedBall _ _).image p.continuous
    obtain ⟨r, hr, htube⟩ := hcompact.exists_thickening_subset_open
      (show IsOpen trappingDisc from isOpen_ball) hp.1.image_subset
    refine ⟨r, hr, fun f hf hc => ⟨?_, ?_, ?_, by simp⟩⟩
    · intro z hz
      exact htube (mem_thickening_iff.mpr ⟨p.eval z, mem_image_of_mem _ hz, hc z hz⟩)
    · intro j hj
      have : j = 0 := by omega
      subst j
      exact D.normalized
    · intro j hj
      have : j = 0 := by omega
      subst j
      exact hasAmbientConformalChart_id _
  · have hn' : 1 ≤ n := by omega
    have ht : controlDisc 0 ⊆ interior (controlDisc n) :=
      (controlDisc_subset_interior_succ 0).trans (interior_mono (controlDisc_mono hn'))
    have hKo : ∀ j ≤ n, ∀ k < j,
        MapsTo (p.eval^[k]) (D.K j) (interior (controlDisc n)) := by
      intro j hj k hk z hz
      exact targetDisc_subset_controlDisc_interior (by omega)
        (hp.2.1 k (by omega) (D.antitone (by omega) hz))
    have hPo : ∀ j < n, ∀ k < j + 1,
        MapsTo (p.eval^[k]) (D.P j) (interior (controlDisc n)) := by
      intro j hj k hk z hz
      exact targetDisc_subset_controlDisc_interior (by omega)
        (hp.2.1 k (by omega) (D.antitone (by omega) (D.points_subset j hz)))
    obtain ⟨δ, hδ, Hδ⟩ := D.stageProperty_approximationStable p.eval
      (interior (controlDisc n)) isOpen_interior p.differentiable.differentiableOn n hp ht hKo hPo
    exact ⟨δ, hδ, fun f hf hc => Hδ f hf.differentiableOn
      (fun z hz => hc z (interior_subset hz))⟩

structure ApproximationStage (D : UniformEscapeData) (n : ℕ) where
  p : Polynomial ℂ
  property : D.StageProperty n p.eval
  tolerance : ℝ
  positive : 0 < tolerance
  stable : ∀ f : ℂ → ℂ, Differentiable ℂ f →
    (∀ z ∈ controlDisc n, ‖f z - p.eval z‖ ≤ 2 * tolerance) → D.StageProperty n f

theorem exists_approximationStage (D : UniformEscapeData) (n : ℕ)
    (p : Polynomial ℂ) (hp : D.StageProperty n p.eval) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : D.ApproximationStage n, S.p = p ∧ S.tolerance ≤ ε := by
  obtain ⟨δ, hδ, Hδ⟩ := D.stageProperty_stability_closed n p hp
  let r := min (δ / 4) ε
  have hr : 0 < r := lt_min (by positivity) hε
  have hstable : ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z ∈ controlDisc n, ‖f z - p.eval z‖ ≤ 2 * r) → D.StageProperty n f := by
    intro f hf hc
    apply Hδ f hf
    intro z hz
    rw [dist_eq_norm]
    have hbound := hc z hz
    have hsmall : r ≤ δ / 4 := min_le_left _ _
    linarith
  exact ⟨⟨p, hp, r, hr, hstable⟩, rfl, min_le_right _ _⟩

theorem exists_next_approximationStage (D : UniformEscapeData) (n : ℕ)
    (S : D.ApproximationStage n) :
    ∃ T : D.ApproximationStage (n + 1), T.tolerance ≤ S.tolerance / 2 ∧
      ∀ z ∈ controlDisc n, ‖T.p.eval z - S.p.eval z‖ ≤ S.tolerance := by
  obtain ⟨q, hq, hclose⟩ := D.exists_polynomial_extension n S.p S.property S.tolerance S.positive
  obtain ⟨T, hT, htol⟩ := D.exists_approximationStage (n + 1) q hq
    (S.tolerance / 2) (half_pos S.positive)
  exact ⟨T, htol, fun z hz => hT ▸ (hclose z hz).le⟩

end UniformEscapeData
end EremenkosConjecture
