/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.PositiveAreaExceptionalReduction

/-! # Finite anchors for the compact global surface case -/

open Set Function MeasureTheory
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

/-- In the sole compact-global case left by the local-subsurface reduction,
three points of the positive-area set can be made into backward-invariant
countable anchors.  Deleting their backward tree preserves positive area and
all of the wandering cancellation identities, while the remaining saturation
avoids the anchors. -/
theorem exists_three_anchor_positive_wandering_configuration
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hsource : f.source = ⊤)
    {A : Set X} (hAmeas : MeasurableSet A)
    (hAtrap : A ⊆ f.trapped)
    (hdis : Pairwise
      (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A)
    (hApos : HasPositiveChartArea A) :
    ∃ E : Finset X, E.card = 3 ∧ (E : Set X) ⊆ A ∧
      ∃ S : Set X, S.Countable ∧ (E : Set X) ⊆ S ∧
        let Astar := A \ S
        let Wstar := f.saturation Astar
        MeasurableSet Astar ∧ HasPositiveChartArea Astar ∧
          MeasurableSet Wstar ∧ Astar ⊆ Wstar ∧
          InjOn f.totalize Wstar ∧
          f.totalize '' Wstar = Wstar \ Astar ∧
          Disjoint Wstar S := by
  classical
  obtain ⟨a, ha, b, hb, hba, c, hc, hca, hcb⟩ := hApos.exists_three
  let E : Finset X := {a, b, c}
  have haE : a ∉ ({b, c} : Finset X) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hba, Ne.symm hca⟩
  have hbE : b ∉ ({c} : Finset X) := by
    simpa only [Finset.mem_singleton] using Ne.symm hcb
  have hEcard : E.card = 3 := by
    rw [show E = insert a (insert b {c}) from rfl,
      Finset.card_insert_of_notMem haE,
      Finset.card_insert_of_notMem hbE]
    simp
  have hEA : (E : Set X) ⊆ A := by
    intro x hx
    change x ∈ E at hx
    rw [show E = insert a (insert b {c}) from rfl] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  let V : TopologicalSpace.Opens X := ⊤
  have hVcompact : IsCompact (closure (V : Set X)) := by
    simpa [V] using (isCompact_univ : IsCompact (Set.univ : Set X))
  have hVsource : closure (V : Set X) ⊆ f.source := by
    simpa [V, hsource]
  let P : ℕ → Finset X := fun _ => ∅
  have hPmono : Monotone P := fun _ _ _ => by simp [P]
  obtain ⟨Sseq, hSmono, hcontain, hback⟩ :=
    f.exists_backwardExceptionalFinsets hf V hVcompact hVsource P hPmono E
  let S : Set X := ⋃ n, ((Sseq n : Finset X) : Set X)
  have hScount : S.Countable :=
    Set.countable_iUnion fun n => (Sseq n).finite_toSet.countable
  have hES : (E : Set X) ⊆ S := by
    intro x hx
    exact mem_iUnion.mpr ⟨0, (hcontain 0).2 hx⟩
  have hback' : ∀ (x : f.source), (x : X) ∈ V →
      f.map x ∈ S → (x : X) ∈ S := by
    intro x hx hfx
    exact hback (x : X) hx hfx
  obtain ⟨hAstarmeas, hAstarpos, hWmeas, hAstarW, -, hWinj,
      himage, hWdis⟩ :=
    f.diff_backwardExceptional_wandering_configuration hf hAmeas hApos
      hAtrap hdis hinj (subset_univ _) (subset_univ _) hScount hback'
  exact ⟨E, hEcard, hEA, S, hScount, hES, hAstarmeas, hAstarpos,
    hWmeas, hAstarW, hWinj, himage, hWdis⟩

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.exists_three_anchor_positive_wandering_configuration
