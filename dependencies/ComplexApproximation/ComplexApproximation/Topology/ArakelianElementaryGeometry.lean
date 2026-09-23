import ComplexApproximation.Topology.HorizontalEscape
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

open Set Metric Bornology Complex

namespace ComplexApproximation

/-- Every point outside a star-convex set escapes along the outward radial ray. -/
theorem noBoundedComplementComponents_of_starConvex {E : Set ℂ} {c : ℂ}
    (hc : c ∈ E) (hstar : StarConvex ℝ c E) : NoBoundedComplementComponents E := by
  intro z hz
  have hzc : z - c ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ hc))
  apply not_isBounded_component_of_affine_ray hzc
  intro t ht hw
  have hden : 0 < t + 1 := by linarith
  have hp : 0 ≤ (t + 1)⁻¹ := inv_nonneg.mpr hden.le
  have hp1 : (t + 1)⁻¹ ≤ 1 := (inv_le_one₀ hden).mpr (by linarith)
  have hm := hstar.add_smul_sub_mem hw hp hp1
  have heq : c + (t + 1)⁻¹ • (z + (t : ℂ) * (z - c) - c) = z := by
    rw [Complex.real_smul]
    push_cast
    have hdenc : (t : ℂ) + 1 ≠ 0 := by exact_mod_cast hden.ne'
    field_simp
    ring
  exact hz (heq ▸ hm)

/-- A closed star-convex plane set satisfies Arakelian's geometric condition.
Adjoining a disk centred at its star centre creates no holes. -/
theorem isArakelian_of_closed_starConvex {E : Set ℂ} {c : ℂ}
    (hE : IsClosed E) (hc : c ∈ E) (hstar : StarConvex ℝ c E) : IsArakelian E := by
  refine ⟨hE, noBoundedComplementComponents_of_starConvex hc hstar, ?_⟩
  intro R
  let S := max R 0 + ‖c‖
  have hS : 0 ≤ S := add_nonneg (le_max_right _ _) (norm_nonneg _)
  have hball : closedBall (0 : ℂ) R ⊆ closedBall c S := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le z c).trans
      (by dsimp [S]; linarith [mem_closedBall_zero_iff.mp hz, le_max_left R 0])
  have hstar' : StarConvex ℝ c (E ∪ closedBall c S) :=
    hstar.union ((convex_closedBall c S).starConvex (mem_closedBall_self hS))
  have hfill := fill_mono (union_subset_union_right E hball)
  rw [fill_eq_self (noBoundedComplementComponents_of_starConvex (Or.inl hc) hstar')] at hfill
  apply isBounded_closedBall.subset
  intro z hz
  exact (hfill hz.1).resolve_left hz.2

/-- Bounded changes preserve Arakelian's condition whenever the new closed set
still has no bounded complementary components. -/
theorem IsArakelian.of_bounded_modification {E F : Set ℂ} (hF : IsArakelian F)
    (hE : IsClosed E) (hfull : NoBoundedComplementComponents E)
    (hEF : IsBounded (E \ F)) (hFE : IsBounded (F \ E)) : IsArakelian E := by
  refine ⟨hE, hfull, ?_⟩
  obtain ⟨T, hT⟩ := hEF.subset_closedBall (0 : ℂ)
  intro R
  have hsub : E ∪ closedBall 0 R ⊆ F ∪ closedBall 0 (max R T) := by
    rintro z (hz | hz)
    · by_cases hzF : z ∈ F
      · exact Or.inl hzF
      · exact Or.inr ((closedBall_subset_closedBall (le_max_right R T)) (hT ⟨hz, hzF⟩))
    · exact Or.inr ((closedBall_subset_closedBall (le_max_left R T)) hz)
  apply ((hF.boundedHoles (max R T)).union hFE).subset
  intro z hz
  by_cases hzF : z ∈ F
  · exact Or.inr ⟨hzF, hz.2⟩
  · exact Or.inl ⟨fill_mono hsub hz.1, hzF⟩

/-- Adding a compact decoration to a closed star-convex set and filling its
bounded holes produces an Arakelian set. -/
theorem isArakelian_fill_compact_union_starConvex {C S : Set ℂ} {c : ℂ}
    (hC : IsCompact C) (hS : IsClosed S) (hc : c ∈ S)
    (hstar : StarConvex ℝ c S) : IsArakelian (fill (C ∪ S)) := by
  refine ⟨isClosed_fill (hC.isClosed.union hS), noBoundedComplementComponents_fill _, ?_⟩
  intro R
  obtain ⟨B, hB, hbound⟩ := hC.isBounded.exists_pos_norm_le
  let r := B + |R| + ‖c‖ + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hCball : C ⊆ closedBall c r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le z c).trans (by dsimp [r]; linarith [hbound z hz, abs_nonneg R])
  have hRball : closedBall (0 : ℂ) R ⊆ closedBall c r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le z c).trans (by dsimp [r]; linarith [mem_closedBall_zero_iff.mp hz, le_abs_self R])
  have hfull : NoBoundedComplementComponents (S ∪ closedBall c r) :=
    noBoundedComplementComponents_of_starConvex (Or.inl hc)
      (hstar.union ((convex_closedBall c r).starConvex (mem_closedBall_self hr)))
  have hEF : fill (C ∪ S) ⊆ S ∪ closedBall c r := by
    have h := fill_mono (show C ∪ S ⊆ S ∪ closedBall c r from
      union_subset (fun z hz => Or.inr (hCball hz)) subset_union_left)
    rwa [fill_eq_self hfull] at h
  have hsub : fill (C ∪ S) ∪ closedBall 0 R ⊆ S ∪ closedBall c r :=
    union_subset hEF (fun z hz => Or.inr (hRball hz))
  have hfilled := fill_mono hsub
  rw [fill_eq_self hfull] at hfilled
  apply isBounded_closedBall.subset
  intro z hz
  rcases hfilled hz.1 with hzS | hzB
  · exact False.elim (hz.2 (subset_fill _ (Or.inr hzS)))
  · exact hzB

end ComplexApproximation
