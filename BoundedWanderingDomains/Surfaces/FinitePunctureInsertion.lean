module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.UniformFiniteRemoval

@[expose] public section

/-! # Uniform area cost for adding finitely many punctures -/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M] [DecidableEq M]

/-- On a fixed compact measured region, adjoining at most `q` punctures to
an arbitrary finite-puncture model increases area by one uniform finite
amount. -/
theorem uniform_finitePuncture_insertion_area_le (p : DiscCover M)
    (q : ℕ) {L : Set M} (hL : IsCompact L) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ (P E : Finset M), E.card ≤ q →
      ∀ (A : Set M), MeasurableSet A → A ⊆ L →
        p.domainArea (finitePunctureDomain (P ∪ E)) A ≤
          p.domainArea (finitePunctureDomain P) A + D := by
  classical
  obtain ⟨D, hD, hgain⟩ := p.uniform_compact_finite_removal_gain_le q hL
  refine ⟨D, hD, ?_⟩
  intro P E hEq A hA hAL
  have hdom : finiteRemovalDomain (finitePunctureDomain P) E =
      finitePunctureDomain (P ∪ E) := by
    ext x
    simp [finiteRemovalDomain, finitePunctureDomain]
  rw [← hdom]
  exact (p.domainArea_le_add_gain (finitePunctureDomain P)
    (finiteRemovalDomain (finitePunctureDomain P) E) hA).trans
      (add_le_add_right ((measure_mono hAL).trans
        (hgain E hEq (finitePunctureDomain P))) _)

end AreaDeficit.Surfaces.DiscCover
