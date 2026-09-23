import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

open Set Filter Function
open scoped Topology

namespace AreaDeficit

/-- A nonnegative smooth compactly supported cutoff at least one on a
given compact set. Its existence is proved, not an input to dynamics. -/
theorem exists_compact_cutoff {K V : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ chi : ℂ → ℝ, ContDiff ℝ 2 chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ V ∧ (∀ z, 0 ≤ chi z) ∧ (∀ z ∈ K, 1 ≤ chi z) := by
  classical
  have hlocal : ∀ x : K, ∃ g : ℂ → ℝ,
      tsupport g ⊆ V ∧ HasCompactSupport g ∧ ContDiff ℝ (2 : ℕ∞) g ∧
      range g ⊆ Icc 0 1 ∧ g x = 1 :=
    fun x => exists_contDiff_tsupport_subset (hV.mem_nhds (hKV x.2))
  choose g hs hc hd hp h1 using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : K => {z | (1 / 2 : ℝ) < g x z})
    (fun x => isOpen_lt continuous_const (hd x).continuous)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, by simp [h1]; norm_num⟩)
  let chi : ℂ → ℝ := fun z => 2 * ∑ x ∈ t, g x z
  have hts : tsupport chi ⊆ ⋃ x ∈ t, tsupport (g x) := by
    apply closure_minimal ?_ (isClosed_biUnion_finset (fun x _ => isClosed_tsupport (g x)))
    intro z hz
    by_contra hn
    have hz0 : ∀ x ∈ t, g x z = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (fun he => hn (mem_iUnion₂.mpr ⟨x, hx, he⟩))
    exact hz (by simp [chi, Finset.sum_eq_zero hz0])
  refine ⟨chi, contDiff_const.mul (ContDiff.sum (fun x _ => hd x)), ?_, ?_, ?_, ?_⟩
  · exact (t.finite_toSet.isCompact_biUnion (fun x _ => hc x)).of_isClosed_subset
      (isClosed_tsupport chi) hts
  · exact hts.trans (iUnion₂_subset (fun x _ => hs x))
  · intro z
    dsimp [chi]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun x _ => (hp x (mem_range_self z)).1))
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (ht hz)
    have hle := Finset.single_le_sum (s := t) (f := fun x => g x z)
      (fun x _ => (hp x (mem_range_self z)).1) hx
    dsimp [chi]
    change (1 / 2 : ℝ) < g x z at hzx
    linarith

end AreaDeficit
