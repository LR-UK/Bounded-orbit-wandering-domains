import FunctionTheory.Topology.LocallyFiniteSeparation
import FunctionTheory.Topology.EscapingDiscs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

open Set Filter Metric Bornology
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A locally finite disjoint compact family in the plane leaves points
arbitrarily far from the origin. A real half-ray outside a putative bounded
complement would have to lie in a single compact member. -/
theorem not_isBounded_compl_iUnion_locallyFinite_disjoint_compacts
    {I : Type*} (K : I → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hloc : LocallyFinite K)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ¬ IsBounded (⋃ i, K i)ᶜ := by
  intro hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  let S : Set ℂ := Complex.ofReal '' Ioi R
  have hS : IsPreconnected S :=
    isPreconnected_Ioi.image _ Complex.continuous_ofReal.continuousOn
  have hSK : S ⊆ ⋃ i, K i := by
    rintro z ⟨t, ht, rfl⟩
    by_contra hz
    have H := hR _ hz
    have hnorm : ‖(t : ℂ)‖ = |t| := by simp
    rw [hnorm] at H
    exact (ht.trans_le ((le_abs_self t).trans H)).false
  have hxS : ((R+1 : ℝ) : ℂ) ∈ S := ⟨R+1, by simp, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hSK hxS)
  have hSi := preconnected_subset_member_of_locallyFinite_disjoint_closed
    K (fun i => (hK i).isClosed) hloc hdis hS hSK hxS hi
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp ((hK i).isBounded.subset hSi)
  have hy : ((max R M+1 : ℝ) : ℂ) ∈ S :=
    ⟨max R M+1, by simp only [mem_Ioi]; linarith [le_max_left R M], rfl⟩
  have H := hM _ hy
  have hnorm : ‖((max R M+1 : ℝ) : ℂ)‖ = |max R M+1| := by simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at H
  linarith [le_abs_self (max R M+1), le_max_right R M]

/-- The return discs can avoid an arbitrary additional compact set as well
as all members of a locally finite disjoint compact family. -/
theorem exists_escaping_discs_avoiding_compact_family
    {I : Type*} (K : I → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hloc : LocallyFinite K)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    {C : Set ℂ} (hC : IsCompact C) :
    ∃ (c : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ n, 0 < r n ∧ r n ≤ 1 / ((n : ℝ)+1)) ∧
      (∀ n, Disjoint (closedBall (c n) (r n)) (C ∪ ⋃ i, K i)) ∧
      Pairwise (fun i j => Disjoint (closedBall (c i) (r i)) (closedBall (c j) (r j))) ∧
      Tendsto r atTop (𝓝 0) ∧
      ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ closedBall (c n) (r n), R < ‖z‖ := by
  apply exists_disjoint_escaping_discs
    (hC.isClosed.union (hloc.isClosed_iUnion (fun i => (hK i).isClosed)))
  intro hb
  apply not_isBounded_compl_iUnion_locallyFinite_disjoint_compacts K hK hloc hdis
  apply (hC.isBounded.union hb).subset
  intro z hz
  by_cases hc : z ∈ C
  · exact Or.inl hc
  · exact Or.inr (by simp only [mem_compl_iff, mem_union]; exact not_or.mpr ⟨hc,hz⟩)

end FunctionTheory
