/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FinitePunctureInsertion
import BoundedWanderingDomains.Surfaces.FiniteModelArea
import BoundedWanderingDomains.AreaCancellation

/-! # Surface finite-model cancellation -/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M] [DecidableEq M]

/-- A uniform one-step area-advance estimate, together with the already
proved uniform puncture cost, bounds the first wandering piece in every
finite model. -/
theorem finite_model_cancellation_of_area_advance
    (p : DiscCover M) (q : ℕ) {L : Set M} (hL : IsCompact L)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    ∃ H : ℝ≥0∞, H ≠ ⊤ ∧ ∀ (P E : Finset M), E.card ≤ q →
      ∀ (f : M → M) (B W : Set M), MeasurableSet B → B ⊆ W → W ⊆ L →
        MeasurableSet (f '' W) → f '' W ⊆ W \ B →
        p.domainArea (finitePunctureDomain P) W ≤
          p.domainArea (finitePunctureDomain (P ∪ E)) (f '' W) + C →
        p.domainArea (finitePunctureDomain P) B ≤ H := by
  obtain ⟨D, hD, hinsert⟩ := p.uniform_finitePuncture_insertion_area_le q hL
  refine ⟨D + C, ENNReal.add_ne_top.mpr ⟨hD, hC⟩, ?_⟩
  intro P E hEq f B W hB hBW hWL hfW himage hadvance
  let μ := p.domainArea (finitePunctureDomain P)
  let ν := p.domainArea (finitePunctureDomain (P ∪ E))
  have hfinite : μ W ≠ ⊤ :=
    p.finitePunctureDomain_area_subset_compact_finite P hL hWL
  have himageL : f '' W ⊆ L := himage.trans sdiff_subset |>.trans hWL
  have hcost : ν (f '' W) ≤ μ (f '' W) + D :=
    hinsert P E hEq (f '' W) hfW himageL
  exact AreaDeficit.finite_area_cancellation_le hB hBW hfinite himage
    hadvance hcost

end AreaDeficit.Surfaces.DiscCover
