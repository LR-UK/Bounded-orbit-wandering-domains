/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Bases
import Mathlib.Dynamics.FixedPoints.Basic

/-! # Finite models of a backward orbit

Finite forward chains from a dense sequence in the backward orbit give an
increasing exhaustion. Only the images of the two roots are forward exceptions.
No density theorem for periodic points is needed for this construction.
-/

open Set Function

namespace BoundedWanderingDomains

def twoPointBackwardOrbit (f : ℂ → ℂ) (a b : ℂ) : Set ℂ :=
  {z | ∃ n : ℕ, (f^[n]) z = a ∨ (f^[n]) z = b}

theorem exists_finite_backward_orbit_models (f : ℂ → ℂ) (a b : ℂ) :
    ∃ P : ℕ → Finset ℂ, Monotone P ∧ a ∈ P 0 ∧ b ∈ P 0 ∧
      (∀ j, MapsTo f (↑(P j) : Set ℂ)
        ((↑(P j) : Set ℂ) ∪ {f a, f b})) ∧
      closure (⋃ j, (↑(P j) : Set ℂ)) = closure (twoPointBackwardOrbit f a b) := by
  classical
  let T := twoPointBackwardOrbit f a b
  have haT : a ∈ T := ⟨0, Or.inl rfl⟩
  have hbT : b ∈ T := ⟨0, Or.inr rfl⟩
  let : Nonempty T := ⟨⟨a, haT⟩⟩
  let x := TopologicalSpace.denseSeq T
  have hx : ∀ i, ∃ n : ℕ, (f^[n]) (x i : ℂ) = a ∨ (f^[n]) (x i : ℂ) = b :=
    fun i => (x i).property
  choose N hN using hx
  let chain := fun i => (Finset.range (N i + 1)).image (fun k => (f^[k]) (x i : ℂ))
  let P := fun j => ({a, b} : Finset ℂ) ∪ (Finset.range (j + 1)).biUnion chain
  have hchain : ∀ i k, k ≤ N i → (f^[k]) (x i : ℂ) ∈ chain i := by
    intro i k hk
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hchainP : ∀ j i, i ≤ j → chain i ⊆ P j := by
    intro j i hij w hw
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_range.mpr (by omega), hw⟩)
  have hPT : ∀ j, (↑(P j) : Set ℂ) ⊆ T := by
    intro j w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact haT
      · exact hbT
    · obtain ⟨i, _, hw⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
      have hkN : k ≤ N i := by simp only [Finset.mem_range] at hk; omega
      refine ⟨N i - k, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hkN]
      exact hN i
  refine ⟨P, ?_, by simp [P], by simp [P], ?_, ?_⟩
  · intro i j hij w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ hw
    · obtain ⟨k, hk, hw⟩ := Finset.mem_biUnion.mp hw
      exact hchainP j k (by simp only [Finset.mem_range] at hk; omega) hw
  · intro j w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨i, hi, hw⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
      have hkN : k ≤ N i := by simp only [Finset.mem_range] at hk; omega
      by_cases he : k = N i
      · subst k
        rcases hN i with h | h
        · exact Or.inr (Or.inl (congrArg f h))
        · exact Or.inr (Or.inr (congrArg f h))
      · apply Or.inl
        rw [← Function.iterate_succ_apply' f k]
        exact hchainP j i (by simp only [Finset.mem_range] at hi; omega)
          (hchain i (k + 1) (by omega))
  · apply Subset.antisymm
    · exact closure_mono (iUnion_subset hPT)
    · apply closure_minimal _ isClosed_closure
      intro w hw
      have hd := TopologicalSpace.denseRange_denseSeq T ⟨w, hw⟩
      have hc := closure_subtype.mp hd
      apply closure_mono _ hc
      rintro y ⟨_, ⟨i, rfl⟩, rfl⟩
      exact mem_iUnion.mpr ⟨i, hchainP i i le_rfl (hchain i 0 (Nat.zero_le _))⟩

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.exists_finite_backward_orbit_models
