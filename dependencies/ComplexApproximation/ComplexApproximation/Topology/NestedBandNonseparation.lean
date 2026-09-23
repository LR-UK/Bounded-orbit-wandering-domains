import ComplexApproximation.Topology.Filling
import ComplexApproximation.Topology.Nonseparation

open Set Bornology

namespace ComplexApproximation

/-- A connected subset that misses only a bounded part of an open set joins
all its unbounded components. -/
theorem isConnected_of_unbounded_components_of_connected_subset
    {S Q : Set ℂ} (hQ : IsConnected Q) (hQS : Q ⊆ S)
    (hbounded : IsBounded (S \ Q))
    (hunbounded : ∀ z ∈ S, ¬ IsBounded (connectedComponentIn S z)) :
    IsConnected S := by
  obtain ⟨a, ha⟩ := hQ.nonempty
  have hQC := hQ.isPreconnected.subset_connectedComponentIn ha hQS
  have heq : connectedComponentIn S a = S := by
    apply Subset.antisymm (connectedComponentIn_subset _ _)
    intro z hz
    have hmeet : (connectedComponentIn S z ∩ Q).Nonempty := by
      by_contra hn
      apply hunbounded z hz
      apply hbounded.subset
      intro w hw
      exact ⟨connectedComponentIn_subset _ _ hw, fun hwQ => hn ⟨w, hw, hwQ⟩⟩
    obtain ⟨w, hw, hwQ⟩ := hmeet
    have hsame := (connectedComponentIn_eq hw).trans (connectedComponentIn_eq (hQC hwQ)).symm
    rw [← hsame]
    exact mem_connectedComponentIn hz
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr (hQS ha)

/-- The band outside an open neighbourhood, together with a smaller closed
set inside it, has no bounded complementary components. Nonseparation of the
inner set makes the intervening gap connected; its tail keeps it unbounded. -/
theorem noBoundedComplementComponents_band_union_inner
    {P B U : Set ℂ}
    (hP : NoBoundedComplementComponents P)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hB : IsClosed B) (hBc : IsPreconnected Bᶜ)
    (hBU : B ⊆ U) (hUP : U ⊆ P)
    (hgap : ¬ IsBounded (U \ B)) :
    NoBoundedComplementComponents ((P \ U) ∪ B) := by
  have hpre : IsPreconnected (U \ B) := by
    have h := isPreconnected_compl_union_disjoint B Uᶜ hB hU.isClosed_compl
      (disjoint_left.mpr (fun z hz hzU => hzU (hBU hz))) hBc
      (by simpa only [compl_compl] using hUc)
    have heq : (B ∪ Uᶜ)ᶜ = U \ B := by ext z; simp [and_comm]
    rwa [heq] at h
  have hsub : U \ B ⊆ ((P \ U) ∪ B)ᶜ := by
    rintro z ⟨hzU, hzB⟩ (hz | hz)
    · exact hz.2 hzU
    · exact hzB hz
  have hEP : (P \ U) ∪ B ⊆ P := union_subset sdiff_subset (hBU.trans hUP)
  intro z hz hb
  by_cases hzP : z ∈ P
  · have hzU : z ∈ U := by
      by_contra hn
      exact hz (Or.inl ⟨hzP, hn⟩)
    have hzB : z ∉ B := fun h => hz (Or.inr h)
    exact hgap (hb.subset (hpre.subset_connectedComponentIn ⟨hzU, hzB⟩ hsub))
  · exact hP z hzP (hb.subset (connectedComponentIn_mono z (compl_subset_compl.mpr hEP)))

end ComplexApproximation
