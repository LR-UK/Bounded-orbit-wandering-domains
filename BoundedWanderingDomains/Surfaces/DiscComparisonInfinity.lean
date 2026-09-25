/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactDiscImages
import BoundedWanderingDomains.Surfaces.DomainSchwarz

/-! # Uniform metric comparison tending to one outside compact sets

This is the qualitative upper comparison used in Mihaljević–Rempe/Minda:
removing a fixed compact set has arbitrarily small multiplicative effect
far out in a fixed hyperbolic ambient surface, uniformly in the old domain.
The proof is in covering-disc coordinates, so no new distance construction
or boundary regularity is required.
-/
open Set Function Filter Metric RiemannDynamics
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem compact_uniform_avoidance_outside (p : DiscCover M)
    {K : Set M} (hK : IsCompact K) {r : ℝ} (hr : r < 1) :
    ∃ C : Set M, IsCompact C ∧
      ∀ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
        g discZero ∉ C → ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → g z ∉ K := by
  obtain ⟨C,hC,hcontrol⟩ := p.compact_disc_images hK hr
  refine ⟨C,hC,?_⟩
  intro g hg hgC z hz hzK
  let m := discMobiusFromZero z
  let w : unitDisc := ⟨-(z : ℂ), by
    simpa only [unitDisc,TopologicalSpace.Opens.mem_mk,mem_ball_zero_iff,norm_neg] using z.property⟩
  have hm0 : m discZero = z := discMobiusFromZero_zero z
  have hmw : m w = discZero := Subtype.ext (mobiusDisk_self (-(z : ℂ)))
  have hG0 : (g ∘ m) discZero ∈ K := by simpa only [comp_apply,hm0] using hzK
  have hw : ‖(w : ℂ)‖ ≤ r := by simpa only [w,norm_neg] using hz
  have hmem := hcontrol (g ∘ m) (hg.comp (discMobiusFromZero_holomorphic z)) hG0 w hw
  exact hgC (by simpa only [comp_apply,hmw] using hmem)

variable [T2Space M] [SecondCountableTopology M]

theorem domainDensity_ratio_le_outside_compact (p : DiscCover M)
    {K : Set M} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : Set M, IsCompact C ∧
      ∀ (U V : TopologicalSpace.Opens M) (hVU : V ≤ U),
        (∀ y ∈ U, y ∉ K → y ∈ V) →
        ∀ (c : OpenPartialHomeomorph M ℂ),
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source →
        ∀ x : V, (x : M) ∉ C → (x : M) ∈ c.source →
        p.domainDensity V c x / p.domainDensity U c ⟨(x : M),hVU x.property⟩ ≤ 1 / r := by
  obtain ⟨C,hC,havoid⟩ := p.compact_uniform_avoidance_outside hK hr1
  refine ⟨C,hC,?_⟩
  intro U V hVU hVK c hc x hxC hxc
  apply p.domainDensity_ratio_le_of_disc_avoidance hVU hc hxc hr hr1.le
  intro g hg hgm hg0 z hz
  apply hVK _ (hgm z)
  exact havoid g hg (hg0.symm ▸ hxC) z hz.le

/-- The compact exceptional set depends only on the ambient surface, the
removed compact set and epsilon. It is uniform over all old domains. -/
theorem domainDensity_ratio_near_one_outside_compact (p : DiscCover M)
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set M, IsCompact C ∧
      ∀ (U V : TopologicalSpace.Opens M) (hVU : V ≤ U),
        (∀ y ∈ U, y ∉ K → y ∈ V) →
        ∀ (c : OpenPartialHomeomorph M ℂ),
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source →
        ∀ x : V, (x : M) ∉ C → (x : M) ∈ c.source →
        1 ≤ p.domainDensity V c x / p.domainDensity U c ⟨(x : M),hVU x.property⟩ ∧
        p.domainDensity V c x / p.domainDensity U c ⟨(x : M),hVU x.property⟩ ≤ 1 + ε := by
  have hpos : 0 < 1 + ε := by linarith
  have hr : 0 < 1 / (1 + ε) := one_div_pos.mpr hpos
  have hr1 : 1 / (1 + ε) < 1 := (div_lt_one hpos).mpr (by linarith)
  obtain ⟨C,hC,hbound⟩ := p.domainDensity_ratio_le_outside_compact hK hr hr1
  refine ⟨C,hC,?_⟩
  intro U V hVU hVK c hc x hxC hxc
  constructor
  · apply (le_div_iff₀ (p.domainDensity_pos U hc (x := ⟨(x : M),hVU x.property⟩) hxc)).mpr
    simpa only [one_mul] using p.domainDensity_mono hVU hc (x := x) hxc
  · simpa only [one_div_one_div] using hbound U V hVU hVK c hc x hxC hxc

end AreaDeficit.Surfaces.DiscCover
