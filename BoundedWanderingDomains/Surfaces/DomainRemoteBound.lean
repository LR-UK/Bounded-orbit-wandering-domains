module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainSchwarz
public import BoundedWanderingDomains.Surfaces.DomainChartDensity

@[expose] public section

/-! # Uniform remote density bounds without connectedness restrictions -/
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem remote_domainDensity_ratio_bound (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (U V : TopologicalSpace.Opens M) (hVU : V ≤ U),
      (∀ y ∈ U, y ∉ K → y ∈ V) →
      ∀ (c : OpenPartialHomeomorph M ℂ),
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source →
      ∀ x : V, (x : M) ∈ C → (x : M) ∈ c.source →
      p.domainDensity V c x / p.domainDensity U c ⟨(x : M),hVU x.property⟩ ≤ B := by
  obtain ⟨r,hr,hr1,havoid⟩ := p.compact_uniform_disc_avoidance hK hC hCK
  refine ⟨1 / r, (le_div_iff₀ hr).mpr (by simpa using hr1), ?_⟩
  intro U V hVU hUVK c hc x hxC hxc
  apply p.domainDensity_ratio_le_of_disc_avoidance hVU hc hxc hr hr1
  intro g hg hgm hg0 z hz
  apply hUVK (g z) (hgm z)
  apply havoid g hg _ z hz
  rwa [hg0]

theorem domainChartDensity_mono (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ domainChartSet V c) :
    p.domainChartDensity U c z ≤ p.domainChartDensity V c z := by
  rw [p.domainChartDensity_of_mem V c hz,
    p.domainChartDensity_of_mem U c ⟨hz.1,hVU hz.2⟩]
  exact p.domainDensity_mono hVU hc (x := ⟨c.symm z,hz.2⟩) (c.map_target hz.1)

theorem remote_domainChart_log_bound (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (U V : TopologicalSpace.Opens M) (_hVU : V ≤ U),
      (∀ y ∈ U, y ∉ K → y ∈ V) →
      ∀ (c : OpenPartialHomeomorph M ℂ),
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source →
      ∀ z ∈ domainChartSet V c, c.symm z ∈ C →
      Real.log (p.domainChartDensity V c z) -
        Real.log (p.domainChartDensity U c z) ≤ B := by
  obtain ⟨B,hB,hbound⟩ := p.remote_domainDensity_ratio_bound hK hC hCK
  refine ⟨Real.log B, Real.log_nonneg hB, ?_⟩
  intro U V hVU hUVK c hc z hz hzC
  have hratio := hbound U V hVU hUVK c hc ⟨c.symm z,hz.2⟩ hzC (c.map_target hz.1)
  rw [← p.domainChartDensity_of_mem V c hz,
    ← p.domainChartDensity_of_mem U c ⟨hz.1,hVU hz.2⟩] at hratio
  have ha := p.domainChartDensity_pos V hc hz
  have hb := p.domainChartDensity_pos U hc ⟨hz.1,hVU hz.2⟩
  have hl := Real.log_le_log (div_pos ha hb) hratio
  rwa [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at hl

end AreaDeficit.Surfaces.DiscCover
