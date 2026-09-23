import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Holomorphic functions agreeing on every overlap glue over an arbitrary
open cover. The values of the ambient representative outside the union are
irrelevant to the conclusion. -/
theorem exists_analyticOnNhd_gluing
    {ι : Type*} (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (f : ι → ℂ → ℂ) (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (hagree : ∀ i j, ∀ z ∈ U i ∩ U j, f i z = f j z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (⋃ i, U i) ∧ ∀ i, EqOn F (f i) (U i) := by
  classical
  let F : ℂ → ℂ := fun z => if hz : z ∈ ⋃ i, U i then
    f (mem_iUnion.mp hz).choose z else 0
  have heq : ∀ i, EqOn F (f i) (U i) := by
    intro i z hz
    have hzU : z ∈ ⋃ i, U i := mem_iUnion.mpr ⟨i, hz⟩
    simp only [F, dite_eq_left hzU]
    exact hagree _ i z ⟨(mem_iUnion.mp hzU).choose_spec, hz⟩
  refine ⟨F, ?_, heq⟩
  intro a ha
  obtain ⟨i, hi⟩ := mem_iUnion.mp ha
  apply (hf i a hi).congr
  filter_upwards [(hU i).mem_nhds hi] with z hz
  exact (heq i hz).symm

/-- Nearby holomorphic lifts agree on distinct-chart overlaps whenever the
target map is injective on the comparison ball there. They therefore glue to
one holomorphic lift with the same displacement and target constraints. -/
theorem exists_glued_analytic_lift_of_injOn_overlaps
    {ι : Type*} (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (θ : ι → ℂ → ℂ) (hθ : ∀ i, AnalyticOnNhd ℂ (θ i) (U i))
    {g φ : ℂ → ℂ} {T : Set ℂ} {r : ℝ}
    (hnear : ∀ i, ∀ z ∈ U i, dist (θ i z) z < r)
    (hlift : ∀ i, ∀ z ∈ U i, g (θ i z) = φ z)
    (htarget : ∀ i, MapsTo (θ i) (U i) T)
    (hinj : ∀ i j, i ≠ j → ∀ z ∈ U i ∩ U j, InjOn g (ball z r)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (⋃ i, U i) ∧ MapsTo F (⋃ i, U i) T ∧
      (∀ i, EqOn F (θ i) (U i)) ∧
      ∀ z ∈ ⋃ i, U i, dist (F z) z < r ∧ g (F z) = φ z := by
  classical
  have hagree : ∀ i j, ∀ z ∈ U i ∩ U j, θ i z = θ j z := by
    intro i j z hz
    by_cases hij : i = j
    · simp only [hij]
    · exact hinj i j hij z hz (hnear i z hz.1) (hnear j z hz.2)
        ((hlift i z hz.1).trans (hlift j z hz.2).symm)
  obtain ⟨F, hF, heq⟩ := exists_analyticOnNhd_gluing U hU θ hθ hagree
  refine ⟨F, hF, ?_, heq, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    rw [heq i hi]
    exact htarget i hi
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    rw [heq i hi]
    exact ⟨hnear i z hi, hlift i z hi⟩

end FunctionTheory
