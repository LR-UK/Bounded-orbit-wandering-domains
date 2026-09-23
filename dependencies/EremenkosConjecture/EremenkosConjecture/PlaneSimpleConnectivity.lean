import EremenkosConjecture.JordanSimplyConnected
import ComplexApproximation.Topology.FilledContinua
import FunctionTheory.Topology.SimpleConnectivity

/-! # Simple connectivity from unbounded complementary components

Every compact continuum in the domain has a compact full filling that remains
in the domain, and therefore a relatively compact simply connected Jordan
neighbourhood. The compact-subset loop criterion then contracts every loop.
The complement may have several components, as it does for a horizontal strip.
-/

open Set Bornology

namespace EremenkosConjecture

theorem exists_simplyConnected_neighbourhood_of_noBoundedComplementComponents
    {K U : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hUo : IsOpen U) (hKU : K ⊆ U)
    (hcomp : ComplexApproximation.NoBoundedComplementComponents U) :
    ∃ V : Set ℂ, IsOpen V ∧ IsSimplyConnected V ∧ K ⊆ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U := by
  let F := ComplexApproximation.fill K
  have hFc : IsCompact F := ComplexApproximation.isCompact_fill hK
  have hFn : IsConnected F := ComplexApproximation.isConnected_fill hK.isClosed hKc
  have hFf : IsConnected Fᶜ := ComplexApproximation.isConnected_compl_fill hK
  have hFU : F ⊆ U :=
    ComplexApproximation.fill_subset_of_noBoundedComplementComponents hKU hcomp
  obtain ⟨L, _, _, hL⟩ :=
    exists_nested_jordan_neighbourhoods_within F U hFc hFn hFf hUo hFU
  refine ⟨interior (L 0).carrier, isOpen_interior,
    (L 0).simplyConnectedInterior,
    (ComplexApproximation.subset_fill K).trans (L 0).contains, ?_, ?_⟩
  · rw [← (L 0).regular]
    exact (L 0).compact
  · rw [← (L 0).regular]
    exact hL

theorem isSimplyConnected_of_noBoundedComplementComponents {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hcomp : ComplexApproximation.NoBoundedComplementComponents U) :
    IsSimplyConnected U := by
  apply FunctionTheory.isSimplyConnected_of_compact_connected_subsets hUo hUc
  intro K hK hKc hKU
  obtain ⟨V, _, hV, hKV, _, hVU⟩ :=
    exists_simplyConnected_neighbourhood_of_noBoundedComplementComponents hK hKc hUo hKU hcomp
  exact ⟨V, hV, hKV, subset_closure.trans hVU⟩

theorem isSimplyConnected_of_unbounded_preconnected_complement {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hcomp : IsPreconnected Uᶜ) (hunb : ¬ IsBounded Uᶜ) :
    IsSimplyConnected U := by
  apply isSimplyConnected_of_noBoundedComplementComponents hUo hUc
  intro z hz hb
  exact hunb (hb.subset (hcomp.subset_connectedComponentIn hz (Subset.refl _)))

end EremenkosConjecture
