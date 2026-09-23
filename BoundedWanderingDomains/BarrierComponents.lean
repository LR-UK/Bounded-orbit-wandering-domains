import BoundedWanderingDomains.LocalTrappedTopology

open Set Function

namespace AreaDeficit

/-- The puncture barrier has the same complementary components as the
interior trapped set at every interior trapped point. -/
theorem barrier_component_eq_trapped_component
    {f : ℂ → ℂ} {V A : Set ℂ} (hV : IsOpen V) (hA : IsClosed A)
    (hf : ContinuousOn f V) (hfront : frontier V ⊆ A)
    (hback : V ∩ f ⁻¹' A ⊆ A)
    (havoid : interior (trappedSet f V) ⊆ Aᶜ)
    {x : ℂ} (hx : x ∈ interior (trappedSet f V)) :
    connectedComponentIn Aᶜ x = connectedComponentIn (interior (trappedSet f V)) x := by
  let C := connectedComponentIn Aᶜ x
  have hxC : x ∈ C := mem_connectedComponentIn (havoid hx)
  have hCopen : IsOpen C := hA.isOpen_compl.connectedComponentIn
  have hCconn : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCA : C ⊆ Aᶜ := connectedComponentIn_subset _ _
  have htrap : x ∈ trappedSet f V := interior_subset hx
  have hCV : C ⊆ V := preconnected_subset_of_avoids_frontier
    hCconn hV hfront hCA ⟨x, hxC, htrap 0⟩
  have hit : ∀ n : ℕ, ContinuousOn (f^[n]) C ∧ MapsTo (f^[n]) C (V \ A) := by
    intro n
    induction n with
    | zero => exact ⟨continuousOn_id, fun y hy => ⟨hCV hy, hCA hy⟩⟩
    | succ n ih =>
        have hc : ContinuousOn (f^[n + 1]) C := by
          simpa only [iterate_succ'] using hf.comp ih.1 (fun y hy => (ih.2 hy).1)
        have ha : f^[n + 1] '' C ⊆ Aᶜ := by
          rintro y ⟨z, hz, rfl⟩ hyA
          apply (ih.2 hz).2
          apply hback
          exact ⟨(ih.2 hz).1, by simpa only [mem_preimage, iterate_succ_apply'] using hyA⟩
        have hv : f^[n + 1] '' C ⊆ V :=
          preconnected_subset_of_avoids_frontier (hCconn.image _ hc) hV hfront ha
            ⟨f^[n + 1] x, ⟨x, hxC, rfl⟩, htrap (n + 1)⟩
        exact ⟨hc, fun y hy => ⟨hv ⟨y, hy, rfl⟩, ha ⟨y, hy, rfl⟩⟩⟩
  have hCT : C ⊆ interior (trappedSet f V) :=
    hCopen.subset_interior_iff.mpr (fun y hy n => ((hit n).2 hy).1)
  apply Subset.antisymm
  · exact hCconn.subset_connectedComponentIn hxC hCT
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) ((connectedComponentIn_subset _ _).trans havoid)

end AreaDeficit
