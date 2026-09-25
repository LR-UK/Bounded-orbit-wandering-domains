/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.ComponentDensity
import BoundedWanderingDomains.Surfaces.KernelConvergence

/-! # Finite-puncture convergence with all component covers constructed -/
open Set Function Filter
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

/-- The componentwise Poincaré densities of finite-puncture complements
converge to the density of the closed-set complement. Only the ambient
disc cover is supplied; every subdomain cover is constructed. -/
theorem domainDensity_tendsto_finite_punctures (p : DiscCover M)
    {A : Set M} (hA : IsClosed A)
    (P : ℕ → Finset M) (hP : Monotone P)
    (hPA : ∀ n, (↑(P n) : Set M) ⊆ A)
    (hclosure : closure (⋃ n, (↑(P n) : Set M)) = A)
    {x : M} (hx : x ∉ A)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hxc : x ∈ c.source) :
    Tendsto (fun n => p.domainDensity (finitePunctureDomain (P n)) c
      ⟨x, fun h => hx (hPA n h)⟩) atTop
      (𝓝 (p.domainDensity ⟨Aᶜ,hA.isOpen_compl⟩ c ⟨x,hx⟩)) := by
  let O : TopologicalSpace.Opens M := ⟨Aᶜ,hA.isOpen_compl⟩
  let ox : O := ⟨x,hx⟩
  let U := componentDomain O x
  let ux : U := componentPoint O ox
  let V : ℕ → TopologicalSpace.Opens M :=
    fun n => componentDomain (finitePunctureDomain (P n)) x
  let px : ∀ n, finitePunctureDomain (P n) := fun n => ⟨x, fun h => hx (hPA n h)⟩
  let q : ∀ n, DiscCover (V n) := fun n => p.componentCover _ (px n)
  let r : DiscCover U := p.componentCover O ox
  have hUV : ∀ n, U ≤ V n := fun n =>
    component_complement_le_finite_punctures hA (P n) (hPA n) x
  have homit : ∀ n y, y ∈ V n → y ∉ (↑(P n) : Set M) := by
    intro n y hy
    exact componentDomain_le (finitePunctureDomain (P n)) x hy
  exact p.density_tendsto_of_dense_punctures V
    (component_finite_punctures_antitone P hP x) q r ux hUV
    P hP hclosure homit rfl hc hxc

end AreaDeficit.Surfaces.DiscCover
