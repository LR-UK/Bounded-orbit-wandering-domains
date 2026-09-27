/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FiniteBoundaryMassAssembly
import BoundedWanderingDomains.Surfaces.GlobalPointInsertion

/-! # Global point insertion from a Riesz exhaustion

This module isolates the exact global Green identity needed on a finite-type
surface.  Once the area-gain measure has cutoffs whose masses equal uniformly
bounded boundary pairings, the whole-surface point-removal estimate follows
formally from Fatou. -/

open Set Filter MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [DecidableEq M]

/-- A uniform Riesz-exhaustion package for inserting one point into every
finite-puncture model.  `boundary` is the finite sum of end pairings produced
by Green's identity. -/
def GlobalPointInsertionRieszBound (p : DiscCover M) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ (P : Finset M) (a : M),
    let μ := p.domainAreaGain (finitePunctureDomain P)
      (finitePunctureDomain (insert a P))
    ∃ (χ : ℕ → M → ℝ≥0∞) (boundary : ℕ → ℝ),
      (∀ n, AEMeasurable (χ n) μ) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1)) ∧
      (∀ n, (∫⁻ x, χ n x ∂μ) = ENNReal.ofReal (boundary n)) ∧
      ∀ᶠ n : ℕ in atTop, |boundary n| ≤ B

/-- The Riesz package implies the intrinsic uniform global insertion bound.
No finiteness of either total hyperbolic area is used. -/
theorem uniformGlobalPointInsertionBound_of_riesz
    (p : DiscCover M) {B : ℝ}
    (h : p.GlobalPointInsertionRieszBound B) :
    p.UniformGlobalPointInsertionBound (ENNReal.ofReal B) := by
  intro P a
  let μ := p.domainAreaGain (finitePunctureDomain P)
    (finitePunctureDomain (insert a P))
  obtain ⟨χ, boundary, hχ, hlim, hgreen, hbound⟩ := h.2 P a
  exact AreaDeficit.Surfaces.measure_univ_le_of_eventually_bounded_riesz_cutoffs
    μ χ hχ hlim boundary hgreen h.1 hbound

end AreaDeficit.Surfaces.DiscCover
