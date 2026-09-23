import ComplexApproximation.Topology.TwoPointNonseparation
import ComplexApproximation.Topology.FullCompactSets

open Set Metric Bornology
open scoped Topology

namespace ComplexApproximation

set_option autoImplicit false

/-- Filling does nothing to a compact set with connected complement. -/
theorem fill_eq_self_of_full_compact {A : Set ℂ}
    (hA : IsCompact A) (hfull : IsConnected Aᶜ) : fill A = A := by
  apply fill_eq_self
  intro z hz hb
  have hsub := hfull.isPreconnected.subset_connectedComponentIn hz Subset.rfl
  obtain ⟨R, hR, hAR⟩ := hA.isBounded.exists_pos_norm_le
  have hE : {w : ℂ | R < ‖w‖} ⊆ Aᶜ :=
    fun w hw hwa => (not_lt_of_ge (hAR w hwa)) hw
  exact not_isBounded_exterior R (hb.subset (hE.trans hsub))

/-- Splitting off full compact pieces disjoint from a core does not add
holes beyond those already filled in the core. -/
theorem fill_union_finite_disjoint_full_family
    {I : Type*} [DecidableEq I] (K : I → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hfull : ∀ i, IsConnected (K i)ᶜ)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (B : Set ℂ) (hB : IsCompact B) (S T : Finset I) (hST : S ⊆ T)
    (hfar : ∀ i ∈ T \ S, Disjoint B (K i)) :
    fill (B ∪ ⋃ i ∈ T, K i) =
      fill (B ∪ ⋃ i ∈ S, K i) ∪ ⋃ i ∈ T \ S, K i := by
  classical
  let A := B ∪ ⋃ i ∈ S, K i
  let D : Set ℂ := ⋃ i ∈ T \ S, K i
  have hAc : IsCompact A := hB.union (S.isCompact_biUnion (fun i _ => hK i))
  have hDc : IsCompact D := (T \ S).isCompact_biUnion (fun i _ => hK i)
  have hDf : IsConnected Dᶜ :=
    isConnected_compl_finite_disjoint_union (T \ S) K
      (fun i _ => hK i) (fun i _ => hfull i) (fun i _ j _ hij => hdis hij)
  have hAD : Disjoint A D := by
    apply disjoint_left.mpr
    intro z hzA hzD
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzD
    rcases hzA with hzB | hzS
    · exact disjoint_left.mp (hfar i hi) hzB hzi
    · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzS
      have hji : j ≠ i := by
        intro h
        exact (Finset.mem_sdiff.mp hi).2 (h ▸ hj)
      exact disjoint_left.mp (hdis hji) hzj hzi
  have heq : B ∪ ⋃ i ∈ T, K i = A ∪ D := by
    ext z
    constructor
    · rintro (hzB | hzT)
      · exact Or.inl (Or.inl hzB)
      · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzT
        by_cases hiS : i ∈ S
        · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨i, hiS, hzi⟩))
        · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiS⟩, hzi⟩)
    · rintro ((hzB | hzS) | hzD)
      · exact Or.inl hzB
      · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzS
        exact Or.inr (mem_iUnion₂.mpr ⟨i, hST hi, hzi⟩)
      · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzD
        exact Or.inr (mem_iUnion₂.mpr ⟨i, (Finset.mem_sdiff.mp hi).1, hzi⟩)
  rw [heq, fill_union_disjoint_compacts A D hAc hDc hAD,
    fill_eq_self_of_full_compact hDc hDf]

end ComplexApproximation
