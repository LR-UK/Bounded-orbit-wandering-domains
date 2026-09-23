import EremenkosConjecture.ConstructionData
import EremenkosConjecture.VariableDiscs

open Set Metric Function

namespace EremenkosConjecture
namespace VariableConstruction

def StageProperty (D : UniformEscapeData) {n : ℕ} (S : DiscSchedule n) (f : ℂ → ℂ) : Prop :=
  MapsTo f (controlDisc 0) trappingDisc ∧
  (∀ j ≤ n, MapsTo (f^[j]) (D.K j) (variableTargetDisc (S.center j))) ∧
  (∀ j ≤ n, HasAmbientConformalChart (f^[j]) (D.K j)) ∧
  (∀ j < n, MapsTo (f^[j + 1]) (D.P j) trappingDisc)

theorem stageProperty_initial (D : UniformEscapeData) :
    StageProperty D DiscSchedule.initialSchedule (fun _ => -3) := by
  refine ⟨fun _ _ => mem_ball_self (by norm_num), ?_, ?_, by simp⟩
  · intro j hj
    have : j = 0 := by omega
    subst j
    change D.K 0 ⊆ _
    simpa [DiscSchedule.center, variableTargetDisc, targetDisc] using D.normalized
  · intro j hj
    have : j = 0 := by omega
    subst j
    exact hasAmbientConformalChart_id _

theorem stageProperty_approximationStable (D : UniformEscapeData)
    (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    {n : ℕ} (S : DiscSchedule n) (hs : StageProperty D S g) (htrap : controlDisc 0 ⊆ U)
    (hKorbit : ∀ j ≤ n, ∀ k < j, MapsTo (g^[k]) (D.K j) U)
    (hPorbit : ∀ j < n, ∀ k < j + 1, MapsTo (g^[k]) (D.P j) U) :
    ApproximationStable g U (StageProperty D S) := by
  have ht : ApproximationStable g U (fun f => MapsTo f (controlDisc 0) trappingDisc) := by
    simpa only [iterate_one] using approximationStable_iterate_target g U (controlDisc 0)
      trappingDisc (isCompact_closedBall _ _) hU hg.continuousOn 1
      (fun k hk => by
        have : k = 0 := by omega
        subst k
        exact htrap)
      isOpen_ball hs.1
  have hi : ApproximationStable g U
      (fun f => ∀ j : Fin (n + 1), MapsTo (f^[j.val]) (D.K j.val) (variableTargetDisc (S.center j.val))) :=
    ApproximationStable.forall_finite (fun j => approximationStable_iterate_target
      g U (D.K j.val) (variableTargetDisc (S.center j.val)) (D.compact _) hU hg.continuousOn j.val
      (hKorbit j.val (by omega)) isOpen_ball (hs.2.1 j.val (by omega)))
  have hc : ApproximationStable g U
      (fun f => ∀ j : Fin (n + 1), HasAmbientConformalChart (f^[j.val]) (D.K j.val)) :=
    ApproximationStable.forall_finite (fun j => approximationStable_ambient_conformal_iterate
      g U hU hg j.val (D.K j.val) (D.compact _) (hs.2.2.1 j.val (by omega))
      (hKorbit j.val (by omega)))
  have hp : ApproximationStable g U
      (fun f => ∀ j : Fin n, MapsTo (f^[j.val + 1]) (D.P j.val) trappingDisc) :=
    ApproximationStable.forall_finite (fun j => approximationStable_iterate_target
      g U (D.P j.val) trappingDisc (D.compactP _) hU hg.continuousOn (j.val + 1)
      (hPorbit j.val j.isLt) isOpen_ball (hs.2.2.2 j.val j.isLt))
  apply (ht.and (hi.and (hc.and hp))).mono
  intro f ⟨htf, hif, hcf, hpf⟩
  exact ⟨htf, fun j hj => hif ⟨j, by omega⟩,
    fun j hj => hcf ⟨j, by omega⟩, fun j hj => hpf ⟨j, hj⟩⟩

end VariableConstruction
end EremenkosConjecture

