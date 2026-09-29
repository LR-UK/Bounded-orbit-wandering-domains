module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

/-! # Compact escape in the one-point compactification

These statements justify the escape alternative without choosing an end or
conformal boundary point. They apply to every locally compact Hausdorff surface.
-/

open Set Filter OnePoint Topology
open scoped Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Convergence to the added point means eventual avoidance of every compact set. -/
theorem tendsto_infty_iff_leaves_compacts (u : ℕ → X) :
    Tendsto (fun n => (u n : OnePoint X)) atTop (𝓝 (∞ : OnePoint X)) ↔
      ∀ K : Set X, IsCompact K → ∀ᶠ n in atTop, u n ∉ K := by
  change Tendsto (((↑) : X → OnePoint X) ∘ u) atTop (𝓝 (∞ : OnePoint X)) ↔ _
  rw [← tendsto_comap_iff, OnePoint.comap_coe_nhds_infty,
    coclosedCompact_eq_cocompact, hasBasis_cocompact.tendsto_right_iff]
  rfl

/-- The escape alternative is impossible in a compact ambient surface. -/
theorem not_tendsto_infty_of_compactSpace [CompactSpace X] (u : ℕ → X) :
    ¬ Tendsto (fun n => (u n : OnePoint X)) atTop (𝓝 (∞ : OnePoint X)) := by
  intro h
  have hh := (tendsto_infty_iff_leaves_compacts u).mp h univ isCompact_univ
  obtain ⟨n, hn⟩ := hh.exists
  exact hn (mem_univ _)

/-- Compactly contained sequences cannot escape the ambient surface. -/
theorem not_tendsto_infty_of_range_subset_compact (u : ℕ → X)
    {K : Set X} (hK : IsCompact K) (hu : ∀ n, u n ∈ K) :
    ¬ Tendsto (fun n => (u n : OnePoint X)) atTop (𝓝 (∞ : OnePoint X)) := by
  intro h
  obtain ⟨n, hn⟩ := ((tendsto_infty_iff_leaves_compacts u).mp h K hK).exists
  exact hn (hu n)

/-- A sequence either escapes every compact set, or has a subsequence converging
in the original space. No choice of a conformal boundary is involved. -/
theorem escape_or_convergent_subsequence [FirstCountableTopology X] (u : ℕ → X) :
    Tendsto (fun n => (u n : OnePoint X)) atTop (𝓝 (∞ : OnePoint X)) ∨
      ∃ a : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) := by
  by_cases h : ∀ K : Set X, IsCompact K → ∀ᶠ n in atTop, u n ∉ K
  · exact Or.inl ((tendsto_infty_iff_leaves_compacts u).mpr h)
  · push Not at h
    obtain ⟨K,hK,hfreq⟩ := h
    obtain ⟨a,_,φ,hφ,hlim⟩ := hK.tendsto_subseq' hfreq
    exact Or.inr ⟨a,φ,hφ,hlim⟩

end SurfaceDynamics
