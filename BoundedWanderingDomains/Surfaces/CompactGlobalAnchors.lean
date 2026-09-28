/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.PositiveAreaExceptionalReduction
import BoundedWanderingDomains.Surfaces.CompactFiniteHyperbolization

/-! # Finite anchors for the compact global surface case -/

open Set Function MeasureTheory
open scoped Manifold Topology ContDiff

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] in
/-- The three anchors can be propagated backwards through finite stages, and
every such stage has a disc-covered complement.  This combines the dynamical
backward-tree construction with compact-surface hyperbolisation. -/
theorem exists_three_anchor_backward_hyperbolic_models
    [ConnectedSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hsource : f.source = ⊤)
    {A : Set X} (hApos : HasPositiveChartArea A) :
    ∃ E : Finset X, E.card = 3 ∧ (E : Set X) ⊆ A ∧
      ∃ P : ℕ → Finset X, Monotone P ∧
        (∀ n, E ⊆ P n) ∧
        (∀ n x, x ∈ P n →
          f.totalize x ∈ (P n : Set X) ∪ f.totalize '' (E : Set X)) ∧
        (∀ (x : f.source), f.map x ∈
            (⋃ n, ((P n : Finset X) : Set X)) →
          (x : X) ∈ (⋃ n, ((P n : Finset X) : Set X))) ∧
        ∀ n,
          let U : TopologicalSpace.Opens X :=
            ⟨((↑(P n) : Set X)ᶜ),
              (P n).finite_toSet.isClosed.isOpen_compl⟩
          Nonempty (AreaDeficit.Surfaces.DiscCover U) := by
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
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  let V : TopologicalSpace.Opens X := ⊤
  have hVcompact : IsCompact (closure (V : Set X)) := by
    simpa [V] using (isCompact_univ : IsCompact (Set.univ : Set X))
  have hVsource : closure (V : Set X) ⊆ f.source := by
    simp [V, hsource]
  let Q : ℕ → Finset X := fun _ => ∅
  have hQmono : Monotone Q := fun _ _ _ => by simp [Q]
  obtain ⟨P, hPmono, hcontain, hforward, hback⟩ :=
    f.exists_backwardExceptionalFinsets hf V hVcompact hVsource Q hQmono E
  let : Nontrivial X := ⟨⟨a, b, Ne.symm hba⟩⟩
  let : Infinite X := Set.infinite_univ_iff.mp
    ((infinite_of_mem_nhds a
      ((chartAt ℂ a).open_source.mem_nhds (mem_chart_source ℂ a))).mono
        (subset_univ _))
  let : IsManifold 𝓘(ℂ) ω X :=
    AreaDeficit.Surfaces.isManifold_analytic_of_complex
  refine ⟨E, hEcard, hEA, P, hPmono, fun n => hcontain n |>.2,
    ?_, ?_, ?_⟩
  · intro n x hxP
    have hxsource : x ∈ f.source := by rw [hsource]; trivial
    rw [f.totalize_eq hxsource]
    have h := hforward n x (by trivial) hxP
    simpa only [Q, Finset.coe_empty, empty_union] using h
  · intro x hx
    exact hback (x : X) (by trivial) hx
  · intro n
    exact AreaDeficit.Surfaces.DiscCover.nonempty_compl_finset_of_card_three_subset
      E (P n) hEcard
        (hcontain n).2

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
    simp [V, hsource]
  let P : ℕ → Finset X := fun _ => ∅
  have hPmono : Monotone P := fun _ _ _ => by simp [P]
  obtain ⟨Sseq, hSmono, hcontain, _hforward, hback⟩ :=
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

/-- Compact global positive-area dynamics admit one increasing finite
backward tree whose every complement is disc-covered, while deleting its
countable union preserves the complete wandering cancellation package. -/
theorem exists_three_anchor_positive_wandering_hyperbolic_models
    [ConnectedSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hsource : f.source = ⊤)
    {A : Set X} (hAmeas : MeasurableSet A)
    (hAtrap : A ⊆ f.trapped)
    (hdis : Pairwise
      (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A)
    (hApos : HasPositiveChartArea A) :
    ∃ E : Finset X, E.card = 3 ∧ (E : Set X) ⊆ A ∧
      ∃ P : ℕ → Finset X, Monotone P ∧
        (∀ n, E ⊆ P n) ∧
        (∀ n x, x ∈ P n →
          f.totalize x ∈ (P n : Set X) ∪ f.totalize '' (E : Set X)) ∧
        (∀ (x : f.source), f.map x ∈
            (⋃ n, ((P n : Finset X) : Set X)) →
          (x : X) ∈ (⋃ n, ((P n : Finset X) : Set X))) ∧
        (∀ n,
          let U : TopologicalSpace.Opens X :=
            ⟨((↑(P n) : Set X)ᶜ),
              (P n).finite_toSet.isClosed.isOpen_compl⟩
          Nonempty (AreaDeficit.Surfaces.DiscCover U)) ∧
        let S := ⋃ n, ((P n : Finset X) : Set X)
        let Astar := A \ S
        let Wstar := f.saturation Astar
        MeasurableSet Astar ∧ HasPositiveChartArea Astar ∧
          MeasurableSet Wstar ∧ Astar ⊆ Wstar ∧
          InjOn f.totalize Wstar ∧
          f.totalize '' Wstar = Wstar \ Astar ∧
          Disjoint Wstar S := by
  classical
  obtain ⟨E, hEcard, hEA, P, hPmono, hEP, hforward, hback, hcover⟩ :=
    f.exists_three_anchor_backward_hyperbolic_models hf hsource hApos
  let S : Set X := ⋃ n, ((P n : Finset X) : Set X)
  have hScount : S.Countable :=
    Set.countable_iUnion fun n => (P n).finite_toSet.countable
  have hES : (E : Set X) ⊆ S := by
    intro x hx
    exact mem_iUnion.mpr ⟨0, hEP 0 hx⟩
  obtain ⟨hAstarmeas, hAstarpos, hWmeas, hAstarW, -, hWinj,
      himage, hWdis⟩ :=
    f.diff_backwardExceptional_wandering_configuration hf hAmeas hApos
      hAtrap hdis hinj (subset_univ _) (subset_univ _) hScount
      (fun x _ hx => hback x hx)
  exact ⟨E, hEcard, hEA, P, hPmono, hEP, hforward, hback, hcover,
    hAstarmeas, hAstarpos, hWmeas, hAstarW, hWinj, himage, hWdis⟩

end SurfaceDynamics.LocalMap
