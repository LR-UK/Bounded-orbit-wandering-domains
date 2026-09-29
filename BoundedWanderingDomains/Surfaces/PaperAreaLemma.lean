module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.UniformFiniteRemoval

@[expose] public section

/-! # Uniform area budget used in the revised paper -/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Paper form of the uniform area-gain lemma on a hyperbolic ambient
surface.  The constant is independent of the old open domain, of at most
`q` moving punctures, of the finite-area measurable subset of `L`, and of
the chosen universal disc cover. -/
theorem uniform_remote_finite_area_budget_all_covers
    (p₀ : DiscCover M) (q : ℕ) {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (p : DiscCover M) (E : Finset M), E.card ≤ q →
        ∀ (U : TopologicalSpace.Opens M) (A : Set M), MeasurableSet A →
          A ⊆ L →
          p.domainArea
              (finiteRemovalDomain U E ⊓ ⟨Kᶜ, hK.isClosed.isOpen_compl⟩) A ≤
            p.domainArea U A + C := by
  obtain ⟨C, hC, hgain⟩ :=
    p₀.uniform_compact_finite_remote_removal_gain_le_all_covers
      q hK hL hKL.symm
  refine ⟨C, hC, ?_⟩
  intro p E hEq U A hA hAL
  exact (p.domainArea_le_add_gain U _ hA).trans
    (add_le_add_right ((measure_mono hAL).trans (hgain p E hEq U)) _)

end AreaDeficit.Surfaces.DiscCover
