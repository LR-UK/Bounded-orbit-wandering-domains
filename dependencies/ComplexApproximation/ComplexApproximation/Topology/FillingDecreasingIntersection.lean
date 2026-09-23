import ComplexApproximation.Topology.FilledContinua
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Normed.Module.Connected

open Set Metric Bornology

namespace ComplexApproximation

/-- Filling commutes with a decreasing closed intersection if the limiting
set has no bounded complementary components and all added holes stay in one
bounded set. A compact path to the outside eventually avoids one entire
closed neighbourhood. -/
theorem iInter_fill_eq_of_uniformly_bounded_holes
    {E : ℕ → Set ℂ} {B : Set ℂ}
    (hE : ∀ n, IsClosed (E n)) (hanti : Antitone E)
    (hfull : NoBoundedComplementComponents (⋂ n, E n))
    (hB : IsBounded B) (hholes : ∀ n, fill (E n) \ E n ⊆ B) :
    (⋂ n, fill (E n)) = ⋂ n, E n := by
  apply Subset.antisymm
  · intro z hz
    by_contra hzE
    let C := connectedComponentIn (⋂ n, E n)ᶜ z
    have hCu : ¬ IsBounded C := hfull z hzE
    have hCB : ¬ C ⊆ B := fun h => hCu (hB.subset h)
    obtain ⟨w, hwC, hwB⟩ := not_subset.mp hCB
    have hCo : IsOpen C := (isClosed_iInter hE).isOpen_compl.connectedComponentIn
    have hCc : IsConnected C := isConnected_connectedComponentIn_iff.mpr hzE
    obtain ⟨γ, hγ⟩ := (hCo.isConnected_iff_isPathConnected.mp hCc).joinedIn
      z (mem_connectedComponentIn hzE) w hwC
    have hγE : range γ ⊆ (⋂ n, E n)ᶜ := by
      rintro _ ⟨t, rfl⟩
      exact connectedComponentIn_subset _ _ (hγ t)
    have hdis : Disjoint (range γ) (⋂ n, E n) := disjoint_left.mpr
      (fun x hx hxE => hγE hx hxE)
    obtain ⟨n, hn⟩ := (isCompact_range γ.continuous).elim_directed_family_closed E hE hdis
      (fun i j => ⟨max i j, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩)
    have hpEn : range γ ⊆ (E n)ᶜ := fun x hx hxE => disjoint_left.mp hn hx hxE
    have hwcomp : w ∈ connectedComponentIn (E n)ᶜ z :=
      (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
        γ.source_mem_range hpEn γ.target_mem_range
    have hzfill : IsBounded (connectedComponentIn (E n)ᶜ z) := mem_iInter.mp hz n
    have hwfill : w ∈ fill (E n) := by
      change IsBounded (connectedComponentIn (E n)ᶜ w)
      rw [← connectedComponentIn_eq hwcomp]
      exact hzfill
    exact hwB (hholes n ⟨hwfill, hpEn γ.target_mem_range⟩)
  · intro z hz
    exact mem_iInter.mpr fun n => subset_fill (E n) (mem_iInter.mp hz n)

end ComplexApproximation
