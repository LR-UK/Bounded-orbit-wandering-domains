/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactDiscImages
import BoundedWanderingDomains.Surfaces.DomainSchwarz
import BoundedWanderingDomains.Surfaces.DiscAvoidanceRatio

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

/-- Along any specified old end, removing a fixed compact set changes the
hyperbolic density by a factor tending to one.  The hypothesis is deliberately
phrased as escape in the old ambient surface: it excludes convergence to one
of the newly removed points, where the quotient instead has logarithmic
growth. -/
theorem densityRatio_tendsto_one_of_tendsto_cocompact
    (p : DiscCover M) {K : Set M} (hK : IsCompact K)
    {U : TopologicalSpace.Opens M} (hU : ∀ y : M, y ∈ U ↔ y ∉ K)
    (q : DiscCover U) {ι : Type*} {l : Filter ι} (x : ι → U)
    (hx : Tendsto (fun i => (x i : M)) l (cocompact M)) :
    Tendsto (fun i => p.densityRatio q (x i)) l (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let r : ℝ := 1 / (1 + δ)
  have hr : 0 < r := one_div_pos.mpr (by dsimp [δ]; linarith)
  have hr1 : r < 1 := (div_lt_one (by dsimp [δ]; linarith)).mpr (by linarith)
  obtain ⟨C, hC, havoid⟩ := p.compact_uniform_avoidance_outside hK hr1
  filter_upwards [hx.eventually hC.compl_mem_cocompact] with i hi
  have hupper : p.densityRatio q (x i) ≤ 1 + δ := by
    have h := p.densityRatio_le_of_disc_avoidance q hr hr1.le
      (fun g hg hg0 z hz => by
        apply (hU _).mpr
        exact havoid g hg (hg0.symm ▸ hi) z hz.le)
    simpa only [r, one_div_one_div] using h
  have hlower : 1 ≤ p.densityRatio q (x i) := p.one_le_densityRatio q _
  rw [Real.dist_eq]
  have habs : |p.densityRatio q (x i) - 1| = p.densityRatio q (x i) - 1 :=
    abs_of_nonneg (sub_nonneg.mpr hlower)
  rw [habs]
  dsimp only [δ] at hupper
  linarith

/-- Logarithmic form of the old-end comparison. -/
theorem log_densityRatio_tendsto_zero_of_tendsto_cocompact
    (p : DiscCover M) {K : Set M} (hK : IsCompact K)
    {U : TopologicalSpace.Opens M} (hU : ∀ y : M, y ∈ U ↔ y ∉ K)
    (q : DiscCover U) {ι : Type*} {l : Filter ι} (x : ι → U)
    (hx : Tendsto (fun i => (x i : M)) l (cocompact M)) :
    Tendsto (fun i => Real.log (p.densityRatio q (x i))) l (𝓝 0) := by
  change Tendsto (Real.log ∘ fun i => p.densityRatio q (x i)) l (𝓝 0)
  simpa only [Real.log_one] using
    (Real.continuousAt_log one_ne_zero).tendsto.comp
    (p.densityRatio_tendsto_one_of_tendsto_cocompact hK hU q x hx)

end AreaDeficit.Surfaces.DiscCover
