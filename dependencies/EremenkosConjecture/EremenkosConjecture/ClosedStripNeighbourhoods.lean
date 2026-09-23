import EremenkosConjecture.NestedContinua
import FunctionTheory.Conformal.StripBounds
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

/-- A decreasing closed family with shrinking straight tails eventually fits
inside every open neighbourhood of its intersection that has a straight
tail of positive width. Compact left truncations handle the decoration. -/
theorem exists_stage_subset_open_of_shrinking_straight_tails
    {E : ℕ → Set ℂ} {U : Set ℂ} {η : ℕ → ℝ} {L M A R c H : ℝ}
    (hE : ∀ n, IsClosed (E n)) (hanti : Antitone E)
    (hleft : ∀ n, ∀ z ∈ E n, L ≤ z.re)
    (him : ∀ n, ∀ z ∈ E n, |z.im| ≤ M)
    (htails : ∀ n, ∀ z ∈ E n, A < z.re → |z.im - c| ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (hU : IsOpen U) (hEU : (⋂ n, E n) ⊆ U) (hH : 0 < H)
    (htailU : ∀ z : ℂ, R < z.re → |z.im - c| < H → z ∈ U) :
    ∃ n, E n ⊆ U := by
  let T := max A R + 1
  let K := fun n => E n ∩ {z : ℂ | z.re ≤ T}
  have hK : ∀ n, IsCompact (K n) := fun n =>
    FunctionTheory.isCompact_left_truncation_of_strip_bounds (hE n) (hleft n) (him n)
  have hKanti : Antitone K := fun i j hij => inter_subset_inter_left _ (hanti hij)
  have hKU : (⋂ n, K n) ⊆ U := fun z hz =>
    hEU (mem_iInter.mpr fun n => (mem_iInter.mp hz n).1)
  obtain ⟨n₀, hn₀⟩ := exists_stage_subset_open hK hKanti hU hKU
  obtain ⟨n, hn, hηn⟩ := ((eventually_ge_atTop n₀).and (hη.eventually (Iio_mem_nhds hH))).exists
  refine ⟨n, ?_⟩
  intro z hz
  by_cases hzT : z.re ≤ T
  · exact hn₀ ⟨hanti hn hz, hzT⟩
  · have hzT' : T < z.re := lt_of_not_ge hzT
    exact htailU z (by dsimp [T] at hzT'; linarith [le_max_right A R])
      ((htails n z hz (by dsimp [T] at hzT'; linarith [le_max_left A R])).trans_lt hηn)

end EremenkosConjecture
