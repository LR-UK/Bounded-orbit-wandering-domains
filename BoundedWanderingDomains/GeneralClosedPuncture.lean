/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralPunctureCost
import Mathlib.Topology.Metrizable.Basic

/-!
# Uniform area cost of deleting a point of a plane domain

A closed planar deleted set with at least two points admits a monotone
finite exhaustion. The area gained by removing one more point is bounded
by one in units of `2π`.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace AreaDeficit

/-- Exhaust a closed subset of the complex plane by increasing finite
sets, preserving two specified omitted values at the initial stage. -/
theorem exists_finite_exhaustion_closed (A : Set ℂ) (hA : IsClosed A)
    {a b : ℂ} (ha : a ∈ A) (hb : b ∈ A) :
    ∃ P : ℕ → Finset ℂ, Monotone P ∧ a ∈ P 0 ∧ b ∈ P 0 ∧
      A = closure (⋃ n, (↑(P n) : Set ℂ)) := by
  classical
  obtain ⟨T, hTA, hTc, hAT⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace A).exists_countable_dense_subset
  let D : Set ℂ := T ∪ {a, b}
  have hDc : D.Countable := hTc.union (Set.toFinite {a, b}).countable
  have hDn : D.Nonempty := ⟨a, Or.inr (by simp)⟩
  obtain ⟨f, hf⟩ := hDc.exists_eq_range hDn
  let P : ℕ → Finset ℂ := fun n => (Finset.range n).image f ∪ {a, b}
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    change (Finset.range i).image f ∪ ({a, b} : Finset ℂ) ⊆
      (Finset.range j).image f ∪ ({a, b} : Finset ℂ)
    exact Finset.union_subset_union_left (Finset.image_subset_image (Finset.range_mono hij))
  · simp [P]
  · simp [P]
  · have hPD : (⋃ n, (↑(P n) : Set ℂ)) = D := by
      ext z
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := mem_iUnion.mp hz
        rcases Finset.mem_union.mp hn with hzn | hzn
        · rcases Finset.mem_image.mp hzn with ⟨i, _, rfl⟩
          exact hf.symm ▸ mem_range_self i
        · exact Or.inr (by simpa using hzn)
      · intro hz
        rcases hz with hzt | hze
        · have hzD : z ∈ D := Or.inl hzt
          rw [hf] at hzD
          rcases hzD with ⟨i, rfl⟩
          exact mem_iUnion.mpr ⟨i + 1, Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_self i), rfl⟩)⟩
        · exact mem_iUnion.mpr ⟨0, Finset.mem_union_right _ (by simpa using hze)⟩
    rw [hPD]
    apply Set.Subset.antisymm
    · exact hAT.trans (closure_mono (subset_union_left))
    · apply closure_minimal
      exact union_subset hTA (by simpa [Set.insert_subset_iff] using And.intro ha hb)
      exact hA

/-- Removing a point increases the normalised hyperbolic area by at most
one, integrated over the smaller domain. Thus the curvature −1 area gain
is at most `2π`. This formulation applies to arbitrary closed planar
obstacle sets whose complement is hyperbolic. -/
theorem FinitePunctureMetricInput.point_removal_gain_le_one
    (G : FinitePunctureMetricInput) (A : Set ℂ) (hA : IsClosed A)
    {a b w : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    (∫⁻ z in (A ∪ {w})ᶜ,
      closedComplementAreaWeight (A ∪ {w}) (hA.union isClosed_singleton) hab
        (Or.inl ha) (Or.inl hb) z -
      closedComplementAreaWeight A hA hab ha hb z) ≤ (1 : ℝ≥0∞) := by
  obtain ⟨P, hP, hPa, hPb, hrep⟩ := exists_finite_exhaustion_closed A hA ha hb
  have hrep' : A ∪ {w} = closure (⋃ n, (↑(P n ∪ {w}) : Set ℂ)) := by
    have hsets : (⋃ n, (↑(P n ∪ {w}) : Set ℂ)) =
        (⋃ n, (↑(P n) : Set ℂ)) ∪ {w} := by
      ext z
      simp only [mem_iUnion, Finset.mem_coe, Finset.mem_union,
        Finset.mem_singleton, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨n, hn | hn⟩
        · exact Or.inl ⟨n, hn⟩
        · exact Or.inr hn
      · rintro (⟨n, hn⟩ | hn)
        · exact ⟨n, Or.inl hn⟩
        · exact ⟨0, Or.inr hn⟩
    rw [hsets, closure_union, ← hrep, isClosed_singleton.closure_eq]
  convert G.puncture_gain_bound_closed_exhaustion hP hab hPa hPb
    {w} A (A ∪ {w}) hA (hA.union isClosed_singleton)
    (subset_union_left) hrep hrep' ha hb (Or.inl ha) (Or.inl hb) using 1
  simp

end AreaDeficit

#print axioms AreaDeficit.exists_finite_exhaustion_closed
#print axioms AreaDeficit.FinitePunctureMetricInput.point_removal_gain_le_one
