import ComplexDynamics.Trapping

open Set

namespace ComplexDynamics

/-- If a closed set has Fatou interior and Julia boundary, its interior
components are exactly the Fatou components through its interior points. -/
theorem connectedComponentIn_interior_eq_fatou {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsClosed K) (hinter : interior K ⊆ fatouSet f)
    (hfront : frontier K ⊆ juliaSet f) {z : ℂ} (hz : z ∈ interior K) :
    connectedComponentIn (interior K) z = connectedComponentIn (fatouSet f) z := by
  apply Set.Subset.antisymm (connectedComponentIn_mono z hinter)
  have hsub : connectedComponentIn (fatouSet f) z ⊆ interior K ∪ Kᶜ := by
    intro w hw
    have hwF := connectedComponentIn_subset (fatouSet f) z hw
    by_cases hwK : w ∈ K
    · apply Or.inl
      by_contra hwi
      exact hfront ⟨hK.closure_eq.symm ▸ hwK, hwi⟩ hwF
    · exact Or.inr hwK
  have hdisj : Disjoint (interior K) Kᶜ :=
    disjoint_compl_right.mono_left interior_subset
  have hinside : connectedComponentIn (fatouSet f) z ⊆ interior K :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_interior
      hK.isOpen_compl hdisj hsub ⟨z, mem_connectedComponentIn (hinter hz), hz⟩
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn (hinter hz)) hinside

theorem isFatouComponent_connectedComponentIn_interior {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsClosed K) (hinter : interior K ⊆ fatouSet f)
    (hfront : frontier K ⊆ juliaSet f) {z : ℂ} (hz : z ∈ interior K) :
    IsFatouComponent f (connectedComponentIn (interior K) z) :=
  ⟨z, hinter hz, connectedComponentIn_interior_eq_fatou hK hinter hfront hz⟩

/-- The Julia part of such a closed set is precisely its boundary. -/
theorem inter_juliaSet_eq_frontier {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsClosed K) (hinter : interior K ⊆ fatouSet f)
    (hfront : frontier K ⊆ juliaSet f) : K ∩ juliaSet f = frontier K := by
  ext z
  constructor
  · rintro ⟨hzK, hzJ⟩
    exact ⟨hK.closure_eq.symm ▸ hzK, fun hzi => hzJ (hinter hzi)⟩
  · intro hz
    exact ⟨hK.closure_eq ▸ hz.1, hfront hz⟩

end ComplexDynamics
