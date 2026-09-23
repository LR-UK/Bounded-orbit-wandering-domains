import ComplexApproximation.Topology.HorizontalEscape
import ComplexApproximation.Topology.Nonseparation

/-! # Restricting escape to a horizontal strip

An unbounded complementary component can be kept inside a strip when its
boundary collars are free of the closed obstacle. Compact obstacles are
handled by enlarging the disk before restricting the component.
-/

open Set Metric Bornology Complex
open scoped Topology

namespace ComplexApproximation

def openHorizontalStrip (l u : ℝ) : Set ℂ := {z | l < z.im ∧ z.im < u}

theorem isOpen_openHorizontalStrip (l u : ℝ) : IsOpen (openHorizontalStrip l u) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem unbounded_connected_meets_frontier {C B : Set ℂ} (hC : IsPreconnected C)
    (hCu : ¬ IsBounded C) (hB : IsOpen B) (hBb : IsBounded B)
    (hmeet : (C ∩ B).Nonempty) : (C ∩ frontier B).Nonempty := by
  by_contra h
  have hsub : C ⊆ B ∪ (closure B)ᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact Or.inl hzB
    · apply Or.inr
      intro hzc
      exact h ⟨z, hz, ⟨hzc, by simpa only [hB.interior_eq] using hzB⟩⟩
  have hCB : C ⊆ B := hC.subset_left_of_subset_union hB isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure) hsub hmeet
  exact hCu (hBb.subset hCB)

/-- A component stays unbounded on restricting to an open region, provided
that all its accessible boundary points have neighbourhoods whose interior
points already have unbounded restricted complementary components. -/
theorem unbounded_component_restrict_of_boundary_collars {F U : Set ℂ}
    (hF : IsClosed F) (hU : IsOpen U) {R S : ℝ} (hRS : R ≤ S)
    (hcollar : ∀ w ∈ frontier U, w ∉ closedBall 0 S →
      ∃ O : Set ℂ, IsOpen O ∧ w ∈ O ∧ ∀ v ∈ O ∩ U,
        ¬ IsBounded (connectedComponentIn (U \ (F ∪ closedBall 0 R)) v))
    {z : ℂ} (hzU : z ∈ U) (hzF : z ∉ F ∪ closedBall 0 S)
    (hunb : ¬ IsBounded (connectedComponentIn (F ∪ closedBall 0 S)ᶜ z)) :
    ¬ IsBounded (connectedComponentIn (U \ (F ∪ closedBall 0 R)) z) := by
  intro hb
  let A := U \ (F ∪ closedBall 0 R)
  let B := connectedComponentIn A z
  let C := connectedComponentIn (F ∪ closedBall 0 S)ᶜ z
  have hA : IsOpen A := hU.sdiff (hF.union isClosed_closedBall)
  have hzA : z ∈ A := ⟨hzU, fun hz => hzF (hz.imp id (fun h => closedBall_subset_closedBall hRS h))⟩
  obtain ⟨w, hwC, hwB⟩ := unbounded_connected_meets_frontier
    (C := C) (B := B) isPreconnected_connectedComponentIn hunb hA.connectedComponentIn hb
    ⟨z, mem_connectedComponentIn hzF, mem_connectedComponentIn hzA⟩
  have hwF : w ∉ F ∪ closedBall 0 S := connectedComponentIn_subset _ _ hwC
  have hwA : w ∉ A := frontier_component_subset_compl hA hzA hwB
  have hwU : w ∉ U := by
    intro hw
    apply hwA
    exact ⟨hw, fun h => hwF (h.imp id (fun h => closedBall_subset_closedBall hRS h))⟩
  have hwcl : w ∈ closure U := closure_mono
    ((connectedComponentIn_subset A z).trans sdiff_subset) hwB.1
  have hwfront : w ∈ frontier U := ⟨hwcl, by simpa only [hU.interior_eq] using hwU⟩
  obtain ⟨O, hO, hwO, hescape⟩ := hcollar w hwfront (fun h => hwF (Or.inr h))
  obtain ⟨v, hvO, hvB⟩ := mem_closure_iff.mp hwB.1 O hO hwO
  have hvU : v ∈ U := (connectedComponentIn_subset A z hvB).1
  apply hescape v ⟨hvO, hvU⟩
  have heq : connectedComponentIn A z = connectedComponentIn A v := connectedComponentIn_eq hvB
  rwa [← heq]

theorem frontier_openHorizontalStrip {l u : ℝ} {w : ℂ}
    (hw : w ∈ frontier (openHorizontalStrip l u)) : w.im = l ∨ w.im = u := by
  have hclosed : IsClosed {z : ℂ | l ≤ z.im ∧ z.im ≤ u} :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const)
  have hbound : l ≤ w.im ∧ w.im ≤ u := closure_minimal
    (fun _ hz => ⟨hz.1.le, hz.2.le⟩ : openHorizontalStrip l u ⊆ {z : ℂ | l ≤ z.im ∧ z.im ≤ u})
    hclosed hw.1
  have hn : ¬ (l < w.im ∧ w.im < u) := by
    have hnot : w ∉ interior (openHorizontalStrip l u) := hw.2
    rw [(isOpen_openHorizontalStrip l u).interior_eq] at hnot
    exact hnot
  rcases le_iff_lt_or_eq.mp hbound.1 with h | h
  · exact Or.inr (le_antisymm hbound.2 (le_of_not_gt (fun h' => hn ⟨h, h'⟩)))
  · exact Or.inl h.symm

end ComplexApproximation
