import Runge.MarkedMeromorphicApproximation
import FunctionTheory.Meromorphic.CompactGluing

open Set Filter Polynomial FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

/-- Simultaneous meromorphic approximation on finitely many disjoint compact
pieces, with analytic errors and preservation of marked local degrees.
The input functions need only be meromorphic near their own pieces. -/
theorem meromorphic_approximation_on_disjoint_compacts
    {ι : Type*} [Fintype ι] (K : ι → Set ℂ) (f : ι → ℂ → ℂ)
    (hK : ∀ i, IsCompact (K i))
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hf : ∀ i, MeromorphicOn (f i) (K i))
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents (⋃ i, K i) P)
    (C : ι → Finset ℂ) (hC : ∀ i a, a ∈ C i → a ∈ K i)
    (hreg : ∀ i a, a ∈ C i → AnalyticAt ℂ (f i) a)
    (hnc : ∀ i a, a ∈ C i → ¬ ∀ᶠ z in 𝓝 a, f i z = f i a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (p q : ℂ[X]) (g : ℂ → ℂ), q ≠ 0 ∧
      (∀ a, q.eval a = 0 →
        (∃ i, a ∈ K i ∧ ¬ AnalyticAt ℂ (f i) a) ∨ a ∈ P) ∧
      MeromorphicOn g univ ∧
      (∀ a, g =ᶠ[𝓝[≠] a] (fun z => p.eval z / q.eval z)) ∧
      ∀ i,
        AnalyticOnNhd ℂ (fun z => f i z - g z) (K i) ∧
        (∀ a ∈ K i, ‖f i a - g a‖ < ε) ∧
        (∀ a ∈ K i, AnalyticAt ℂ (f i) a → AnalyticAt ℂ g a) ∧
        ∀ a ∈ C i, g a = f i a ∧
          analyticOrderAt (fun z => g z - g a) a =
            analyticOrderAt (fun z => f i z - f i a) a := by
  classical
  obtain ⟨F, hF, H⟩ := exists_meromorphic_gluing_on_disjoint_compacts K f hK hdis hf
  let s : Finset ℂ := Finset.univ.biUnion C
  have hs : ∀ a, a ∈ s ↔ ∃ i, a ∈ C i := by
    intro a
    simp only [s, Finset.mem_biUnion, Finset.mem_univ, true_and]
  have hsK : ∀ a ∈ s, a ∈ ⋃ i, K i := by
    intro a ha
    obtain ⟨i, hi⟩ := (hs a).mp ha
    exact mem_iUnion.mpr ⟨i, hC i a hi⟩
  have hsreg : ∀ a ∈ s, AnalyticAt ℂ F a := by
    intro a ha
    obtain ⟨i, hi⟩ := (hs a).mp ha
    exact (hreg i a hi).congr (H i a (hC i a hi)).symm
  have hsnc : ∀ a ∈ s, ¬ ∀ᶠ z in 𝓝 a, F z = F a := by
    intro a ha hc
    obtain ⟨i, hi⟩ := (hs a).mp ha
    have he := H i a (hC i a hi)
    apply hnc i a hi
    filter_upwards [he, hc] with z hz hcz
    rw [← hz, hcz, he.eq_of_nhds]
  obtain ⟨p, q, g, hq, hpole, hg, hgr, hdiff, hbound, hgreg, hmarks⟩ :=
    meromorphic_approximation_preserving_marked_local_degrees
      (⋃ i, K i) (isCompact_iUnion hK) P hP F hF s hsK hsreg hsnc ε hε
  refine ⟨p, q, g, hq, ?_, hg, hgr, ?_⟩
  · intro a ha
    rcases hpole a ha with ⟨haK, hna⟩ | haP
    · obtain ⟨i, hi⟩ := mem_iUnion.mp haK
      exact Or.inl ⟨i, hi, fun h => hna (h.congr (H i a hi).symm)⟩
    · exact Or.inr haP
  · intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      exact (hdiff a (mem_iUnion.mpr ⟨i, ha⟩)).congr
        ((H i a ha).sub (Filter.EventuallyEq.refl _ _))
    · intro a ha
      simpa only [(H i a ha).eq_of_nhds] using hbound a (mem_iUnion.mpr ⟨i, ha⟩)
    · intro a ha hfa
      exact hgreg a (mem_iUnion.mpr ⟨i, ha⟩) (hfa.congr (H i a ha).symm)
    · intro a ha
      obtain ⟨hval, hdeg⟩ := hmarks a ((hs a).mpr ⟨i, ha⟩)
      have he := H i a (hC i a ha)
      refine ⟨hval.trans he.eq_of_nhds, hdeg.trans ?_⟩
      apply analyticOrderAt_congr
      filter_upwards [he] with z hz
      rw [hz, he.eq_of_nhds]

end Runge
