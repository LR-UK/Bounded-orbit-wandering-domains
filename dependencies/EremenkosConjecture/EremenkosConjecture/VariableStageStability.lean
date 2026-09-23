import EremenkosConjecture.VariableReferenceDynamics
import ComplexDynamics.FastEscape

/-! # Tolerances preserving a finite stage on its control disk -/

open Set Metric Function

namespace EremenkosConjecture
namespace VariableConstruction

theorem stageProperty_stability_closed (D : UniformEscapeData) {n : ℕ} (S : DiscSchedule n)
    (p : Polynomial ℂ) (hp : StageProperty D S p.eval) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z ∈ variableControlDisc (S.radius n), dist (f z) (p.eval z) < δ) → StageProperty D S f := by
  by_cases hn : n = 0
  · subst n
    have hcompact : IsCompact (p.eval '' controlDisc 0) :=
      (isCompact_closedBall _ _).image p.continuous
    obtain ⟨r, hr, htube⟩ := hcompact.exists_thickening_subset_open
      (show IsOpen trappingDisc from isOpen_ball) hp.1.image_subset
    refine ⟨r, hr, fun f hf hc => ⟨?_, ?_, ?_, by simp⟩⟩
    · intro z hz
      exact htube (mem_thickening_iff.mpr ⟨p.eval z, mem_image_of_mem _ hz, hc z (by simpa [variableControlDisc, S.initial, controlDisc] using hz)⟩)
    · intro j hj
      have : j = 0 := by omega
      subst j
      change D.K 0 ⊆ _
      simpa [DiscSchedule.center, variableTargetDisc, targetDisc] using D.normalized
    · intro j hj
      have : j = 0 := by omega
      subst j
      exact hasAmbientConformalChart_id _
  · have ht := S.initial_control_subset_interior (by omega : 0 < n)
    have hKo : ∀ j ≤ n, ∀ k < j,
        MapsTo (p.eval^[k]) (D.K j) (interior (variableControlDisc (S.radius n))) := by
      intro j hj k hk z hz
      exact S.target_subset_control_interior (by omega) le_rfl
        (hp.2.1 k (by omega) (D.antitone (by omega) hz))
    have hPo : ∀ j < n, ∀ k < j + 1,
        MapsTo (p.eval^[k]) (D.P j) (interior (variableControlDisc (S.radius n))) := by
      intro j hj k hk z hz
      exact S.target_subset_control_interior (by omega) le_rfl
        (hp.2.1 k (by omega) (D.antitone (by omega) (D.points_subset j hz)))
    obtain ⟨δ, hδ, Hδ⟩ := stageProperty_approximationStable D p.eval
      (interior (variableControlDisc (S.radius n))) isOpen_interior p.differentiable.differentiableOn S hp ht hKo hPo
    exact ⟨δ, hδ, fun f hf hc => Hδ f hf.differentiableOn
      (fun z hz => hc z (interior_subset hz))⟩

structure ApproximationStage (D : UniformEscapeData) (n : ℕ) where
  schedule : DiscSchedule n
  p : Polynomial ℂ
  property : StageProperty D schedule p.eval
  tolerance : ℝ
  positive : 0 < tolerance
  small : tolerance ≤ 1 / 4
  stable : ∀ f : ℂ → ℂ, Differentiable ℂ f →
    (∀ z ∈ variableControlDisc (schedule.radius n), ‖f z - p.eval z‖ ≤ 2 * tolerance) →
      StageProperty D schedule f

theorem exists_approximationStage (D : UniformEscapeData) {n : ℕ} (S : DiscSchedule n)
    (p : Polynomial ℂ) (hp : StageProperty D S p.eval) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ApproximationStage D n, T.schedule = S ∧ T.p = p ∧ T.tolerance ≤ ε := by
  obtain ⟨δ, hδ, Hδ⟩ := stageProperty_stability_closed D S p hp
  let r := min (δ / 4) (min ε (1 / 4))
  have hr : 0 < r := lt_min (by positivity) (lt_min hε (by norm_num))
  have hsmall : r ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hstable : ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z ∈ variableControlDisc (S.radius n), ‖f z - p.eval z‖ ≤ 2 * r) →
      StageProperty D S f := by
    intro f hf hc
    apply Hδ f hf
    intro z hz
    rw [dist_eq_norm]
    have hbound := hc z hz
    have hsmall' : r ≤ δ / 4 := min_le_left _ _
    linarith
  exact ⟨⟨S, p, hp, r, hr, hsmall, hstable⟩, rfl, rfl,
    (min_le_right _ _).trans (min_le_left _ _)⟩

def IsNext {D : UniformEscapeData} {n : ℕ}
    (S : ApproximationStage D n) (T : ApproximationStage D (n + 1)) : Prop :=
  (∀ j ≤ n, T.schedule.radius j = S.schedule.radius j) ∧
  T.tolerance ≤ S.tolerance / 2 ∧
  (∀ z ∈ variableControlDisc (S.schedule.radius n),
    ‖T.p.eval z - S.p.eval z‖ ≤ S.tolerance) ∧
  (∀ z ∈ (S.p.eval^[n]) '' D.P n, ‖T.p.eval z - (-3)‖ ≤ S.tolerance) ∧
  ComplexDynamics.maximumModulus S.p.eval (S.schedule.radius n - 3) + 2 <
    T.schedule.radius (n + 1) - 3

theorem exists_next_approximationStage (D : UniformEscapeData) {n : ℕ}
    (S : ApproximationStage D n) :
    ∃ T : ApproximationStage D (n + 1), IsNext S T := by
  let r := max (S.schedule.radius n + 6)
    (ComplexDynamics.maximumModulus S.p.eval (S.schedule.radius n - 3) + 6)
  have hr : S.schedule.radius n + 5 < r := by
    have H : S.schedule.radius n + 6 ≤ r := le_max_left _ _
    linarith
  obtain ⟨q, hq, hclose, hpoints⟩ := exists_polynomial_extension D S.schedule r hr
    S.p S.property S.tolerance S.positive
  obtain ⟨T, hT, hp, htol⟩ := exists_approximationStage D (S.schedule.extend r hr)
    q hq (S.tolerance / 2) (half_pos S.positive)
  refine ⟨T, ?_, htol, ?_, ?_, ?_⟩
  · intro j hj
    rw [hT, S.schedule.extend_radius_old r hr hj]
  · intro z hz
    rw [hp]
    exact (hclose z hz).le
  · intro z hz
    rw [hp]
    exact (hpoints z hz).le
  · rw [hT, S.schedule.extend_radius_new r hr]
    have H : ComplexDynamics.maximumModulus S.p.eval (S.schedule.radius n - 3) + 6 ≤ r :=
      le_max_right _ _
    linarith

end VariableConstruction
end EremenkosConjecture

