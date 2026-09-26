/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SurfaceLocalBranching

/-! # Coverings obtained from compact surface restrictions -/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics

/-- A compact restriction of a continuous map is a covering over every
target set whose relevant fibres lie in the compact interior and where the
ambient map is locally a homeomorphism. -/
theorem compact_surface_covering
    {M N : Type*} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace N] [T2Space N]
    {f : M → N} {K : Set M} {S : Set N}
    (hK : IsCompact K) (hf : Continuous f)
    (hint : ∀ z ∈ K, f z ∈ S → z ∈ interior K)
    (hloc : IsLocalHomeomorphOn f (K ∩ f ⁻¹' S)) :
    IsCoveringMapOn (fun z : K => f z) S := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hf.continuousOn.domRestrict
  exact hloc.comp
    ((AreaDeficit.subtype_localHomeomorph_interior K).mono
      (fun z hz => hint z z.2 hz))
    (fun z hz => ⟨z.2, hz⟩)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [LocallyCompactSpace M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [LocallyCompactSpace N] [T2Space N]
  [DecidableEq N]

/-- One finite branch-value set works for every target set whose compact
restriction has no boundary fibres. -/
theorem exists_finite_branch_values_compact_covering
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {K : Set M} (hK : IsCompact K) :
    ∃ E : Finset N, ∀ S : Set N, S ⊆ (E : Set N)ᶜ →
      (∀ z ∈ K, f z ∈ S → z ∈ interior K) →
      IsCoveringMapOn (fun z : K => f z) S := by
  obtain ⟨E, hloc⟩ :=
    exists_finite_branch_values_isLocalHomeomorphOn hf hopen hK
  refine ⟨E, ?_⟩
  intro S hSE hint
  apply compact_surface_covering hK hf.continuous hint
  apply hloc.mono
  rintro z ⟨hzK, hfzS⟩
  exact ⟨hzK, hSE hfzS⟩

end SurfaceDynamics

#print axioms SurfaceDynamics.compact_surface_covering
#print axioms SurfaceDynamics.exists_finite_branch_values_compact_covering
