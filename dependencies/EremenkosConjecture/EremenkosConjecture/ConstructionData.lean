import EremenkosConjecture.AmbientCharts
import EremenkosConjecture.DiscGeometry

/-!
# Data and finite-stage properties for Proposition 3.2

The construction needs nested full compact sets and compact nonseparating
subsets of their boundaries. Density is used later for the Julia-set
conclusion, and is not needed for the polynomial induction itself.
-/

open Set Metric Function

namespace EremenkosConjecture

structure UniformEscapeData where
  K : ℕ → Set ℂ
  compact : ∀ n, IsCompact (K n)
  full : ∀ n, IsConnected (K n)ᶜ
  nested : ∀ n, K (n + 1) ⊆ interior (K n)
  normalized : K 0 ⊆ targetDisc 0
  P : ℕ → Set ℂ
  compactP : ∀ n, IsCompact (P n)
  fullP : ∀ n, IsConnected (P n)ᶜ
  boundary : ∀ n, P n ⊆ frontier (K n)

namespace UniformEscapeData

theorem antitone (D : UniformEscapeData) : Antitone D.K :=
  antitone_nat_of_succ_le (fun n => (D.nested n).trans interior_subset)

theorem points_subset (D : UniformEscapeData) (n : ℕ) : D.P n ⊆ D.K n :=
  (D.boundary n).trans (frontier_subset_iff_isClosed.mpr (D.compact n).isClosed)

def StageProperty (D : UniformEscapeData) (n : ℕ) (f : ℂ → ℂ) : Prop :=
  MapsTo f (controlDisc 0) trappingDisc ∧
  (∀ j ≤ n, MapsTo (f^[j]) (D.K j) (targetDisc j)) ∧
  (∀ j ≤ n, HasAmbientConformalChart (f^[j]) (D.K j)) ∧
  (∀ j < n, MapsTo (f^[j + 1]) (D.P j) trappingDisc)

theorem stageProperty_initial (D : UniformEscapeData) :
    D.StageProperty 0 (fun _ => -3) := by
  refine ⟨fun _ _ => mem_ball_self (by norm_num), ?_, ?_, by simp⟩
  · intro j hj
    have : j = 0 := by omega
    subst j
    exact D.normalized
  · intro j hj
    have : j = 0 := by omega
    subst j
    exact hasAmbientConformalChart_id _

theorem stageProperty_approximationStable (D : UniformEscapeData)
    (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (n : ℕ) (hs : D.StageProperty n g) (htrap : controlDisc 0 ⊆ U)
    (hKorbit : ∀ j ≤ n, ∀ k < j, MapsTo (g^[k]) (D.K j) U)
    (hPorbit : ∀ j < n, ∀ k < j + 1, MapsTo (g^[k]) (D.P j) U) :
    ApproximationStable g U (D.StageProperty n) := by
  have ht : ApproximationStable g U (fun f => MapsTo f (controlDisc 0) trappingDisc) := by
    simpa only [iterate_one] using approximationStable_iterate_target g U (controlDisc 0)
      trappingDisc (isCompact_closedBall _ _) hU hg.continuousOn 1
      (fun k hk => by
        have : k = 0 := by omega
        subst k
        exact htrap)
      isOpen_ball hs.1
  have hi : ApproximationStable g U
      (fun f => ∀ j : Fin (n + 1), MapsTo (f^[j.val]) (D.K j.val) (targetDisc j.val)) :=
    ApproximationStable.forall_finite (fun j => approximationStable_iterate_target
      g U (D.K j.val) (targetDisc j.val) (D.compact _) hU hg.continuousOn j.val
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

end UniformEscapeData
end EremenkosConjecture
