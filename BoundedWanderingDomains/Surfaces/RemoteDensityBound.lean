/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DiscAvoidanceRatio
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The bound is uniform over all covered open subdomains of the ambient surface.
The removed closed set need not be compact; the set of centres is compact. -/
theorem remote_densityRatio_bound (p : DiscCover M) {K C : Set M}
    (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (V : TopologicalSpace.Opens M) (q : DiscCover V)
      (W : TopologicalSpace.Opens V) (s : DiscCover W),
      (∀ x : V, x ∈ W ↔ (x : M) ∉ K) →
      ∀ x : W, ((x : V) : M) ∈ C → q.densityRatio s x ≤ B := by
  obtain ⟨r,hr,hr1,havoid⟩ := p.compact_uniform_disc_avoidance hK hC hCK
  refine ⟨1 / r,(le_div_iff₀ hr).mpr (by simpa using hr1),?_⟩
  intro V q W s hW x hx
  apply q.densityRatio_le_of_disc_avoidance s hr hr1
  intro g hg hg0 z hz
  apply (hW (g z)).mpr
  apply havoid (Subtype.val ∘ g) ((mdifferentiable_subtype_val V).comp hg) _ z hz
  change (g discZero : M) ∈ C
  rw [hg0]
  exact hx
end AreaDeficit.Surfaces.DiscCover
