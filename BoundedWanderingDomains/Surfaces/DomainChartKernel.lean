module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainChartDensity
public import BoundedWanderingDomains.Surfaces.ComponentKernel

@[expose] public section

/-! # Finite-puncture convergence in ambient coordinates -/
open Set Function Filter
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem domainChartDensity_tendsto_finite_punctures (p : DiscCover M)
    {A : Set M} (hA : IsClosed A) (P : ℕ → Finset M) (hP : Monotone P)
    (hPA : ∀ n, (↑(P n) : Set M) ⊆ A)
    (hclosure : closure (⋃ n, (↑(P n) : Set M)) = A)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet ⟨Aᶜ,hA.isOpen_compl⟩ c) :
    Tendsto (fun n => p.domainChartDensity (finitePunctureDomain (P n)) c z) atTop
      (𝓝 (p.domainChartDensity ⟨Aᶜ,hA.isOpen_compl⟩ c z)) := by
  have hzP : ∀ n, z ∈ domainChartSet (finitePunctureDomain (P n)) c :=
    fun n => ⟨hz.1, fun h => hz.2 (hPA n h)⟩
  simp_rw [p.domainChartDensity_of_mem _ c (hzP _), p.domainChartDensity_of_mem _ c hz]
  exact p.domainDensity_tendsto_finite_punctures hA P hP hPA hclosure hz.2 hc
    (c.map_target hz.1)

end AreaDeficit.Surfaces.DiscCover
