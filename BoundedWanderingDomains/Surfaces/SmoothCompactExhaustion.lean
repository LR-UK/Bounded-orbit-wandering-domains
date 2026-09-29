module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SmoothSurface
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

/-! # Smooth compact exhaustions of Riemann surfaces -/

open Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

/-- Every second-countable Riemann surface admits smooth `[0,1]` cutoffs
with compact support which are eventually one at each point. -/
theorem exists_smooth_compact_exhaustion :
    ∃ chi : ℕ → M → ℝ,
      (∀ n, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (chi n)) ∧
      (∀ n, HasCompactSupport (chi n)) ∧
      (∀ n x, chi n x ∈ Icc (0 : ℝ) 1) ∧
      ∀ x, ∀ᶠ n : ℕ in atTop, chi n x = 1 := by
  letI : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  let K : ℕ → Set M := compactCovering M
  have hKcompact : ∀ n, IsCompact (K n) := isCompact_compactCovering M
  have hlarge : ∀ n, ∃ L : Set M, IsCompact L ∧ K n ⊆ interior L :=
    fun n => exists_compact_superset (hKcompact n)
  choose L hLcompact hKL using hlarge
  have hcut : ∀ n, ∃ f : C^∞⟮𝓘(ℝ, ℂ), M; 𝓘(ℝ), ℝ⟯,
      (∀ᶠ x in 𝓝ˢ (K n), f x = 1) ∧
      (∀ x ∉ L n, f x = 0) ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    intro n
    exact exists_contMDiffMap_one_nhds_of_subset_interior
      𝓘(ℝ, ℂ) (hKcompact n).isClosed (hKL n)
  choose f hfOne hfZero hfBounds using hcut
  refine ⟨fun n => f n, fun n => (f n).contMDiff, ?_, hfBounds, ?_⟩
  · intro n
    apply (hLcompact n).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (hLcompact n).isClosed
    intro x hx
    by_contra hxL
    exact hx (hfZero n x hxL)
  · intro x
    obtain ⟨N, hxN⟩ := exists_mem_compactCovering x
    apply eventually_atTop.mpr
    refine ⟨N, fun n hn => ?_⟩
    exact (hfOne n).self_of_nhdsSet x
      (compactCovering_subset M hn hxN)

end AreaDeficit.Surfaces
