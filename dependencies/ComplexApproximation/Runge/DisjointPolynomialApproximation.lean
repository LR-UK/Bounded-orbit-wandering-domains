import Runge.MarkedPolynomialApproximation
import FunctionTheory.Meromorphic.CompactGluing

open Set Filter Polynomial FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

/-- Polynomial approximation on finitely many disjoint compact pieces with
full union, retaining the marked values and local degrees on every piece. -/
theorem polynomial_approximation_on_disjoint_compacts
    {ι : Type*} [Fintype ι] (K : ι → Set ℂ) (f : ι → ℂ → ℂ)
    (hK : ∀ i, IsCompact (K i))
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hfull : IsConnected (⋃ i, K i)ᶜ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (K i))
    (C : ι → Finset ℂ) (hC : ∀ i a, a ∈ C i → a ∈ K i)
    (hnc : ∀ i a, a ∈ C i → ¬ ∀ᶠ z in 𝓝 a, f i z = f i a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ i,
      (∀ a ∈ K i, ‖f i a - p.eval a‖ < ε) ∧
      ∀ a ∈ C i, p.eval a = f i a ∧
        analyticOrderAt (fun z => p.eval z - p.eval a) a =
          analyticOrderAt (fun z => f i z - f i a) a := by
  classical
  obtain ⟨F, hF, H⟩ := exists_meromorphic_gluing_on_disjoint_compacts K f hK hdis (fun i z hz => (hf i z hz).meromorphicAt)
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
    exact (hf i a (hC i a hi)).congr (H i a (hC i a hi)).symm
  have hsnc : ∀ a ∈ s, ¬ ∀ᶠ z in 𝓝 a, F z = F a := by
    intro a ha hc
    obtain ⟨i, hi⟩ := (hs a).mp ha
    have he := H i a (hC i a hi)
    apply hnc i a hi
    filter_upwards [he, hc] with z hz hcz
    rw [← hz, hcz, he.eq_of_nhds]
  have hFA : AnalyticOnNhd ℂ F (⋃ i, K i) := by
    intro a ha
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    exact (hf i a hi).congr (H i a hi).symm
  obtain ⟨p, hbound, hmarks⟩ :=
    polynomial_approximation_preserving_marked_local_degrees
      (⋃ i, K i) (isCompact_iUnion hK) hfull F hFA s hsK hsnc ε hε
  refine ⟨p, ?_⟩
  intro i
  refine ⟨?_, ?_⟩
  · intro a ha
    simpa only [(H i a ha).eq_of_nhds] using hbound a (mem_iUnion.mpr ⟨i, ha⟩)
  · intro a ha
    obtain ⟨hval, hdeg⟩ := hmarks a ((hs a).mpr ⟨i, ha⟩)
    have he := H i a (hC i a ha)
    refine ⟨hval.trans he.eq_of_nhds, hdeg.trans ?_⟩
    apply analyticOrderAt_congr
    filter_upwards [he] with z hz
    rw [hz, he.eq_of_nhds]

end Runge
