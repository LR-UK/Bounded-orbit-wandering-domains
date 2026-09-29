module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainPlanarDensity
public import BoundedWanderingDomains.Surfaces.DomainAreaGain
public import BoundedWanderingDomains.UnnormalisedPointRemoval

@[expose] public section

/-! # Sharp point-removal cost for a surface domain in one chart -/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [T2Space M]

def punctureDomain (U : TopologicalSpace.Opens M) (a : M) : TopologicalSpace.Opens M :=
  ⟨(U : Set M) \ {a},U.isOpen.sdiff isClosed_singleton⟩

theorem punctureDomain_le (U : TopologicalSpace.Opens M) (a : M) : punctureDomain U a ≤ U :=
  fun _ hx => hx.1

theorem domainChartSet_puncture (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ} {a : M} (ha : a ∈ c.source) :
    domainChartSet (punctureDomain U a) c = domainChartSet U c \ {c a} := by
  ext z
  change (z ∈ c.target ∧ c.symm z ∈ (U : Set M) \ {a}) ↔
    (z ∈ c.target ∧ c.symm z ∈ U) ∧ z ∉ ({c a} : Set ℂ)
  simp only [Set.mem_sdiff,mem_singleton_iff]
  constructor
  · rintro ⟨hzt,hzU,hzne⟩
    refine ⟨⟨hzt,hzU⟩,?_⟩
    intro he
    apply hzne
    rw [he,c.left_inv ha]
  · rintro ⟨⟨hzt,hzU⟩,hzne⟩
    refine ⟨hzt,hzU,?_⟩
    intro he
    exact hzne ((c.right_inv hzt).symm.trans (congrArg c he))

omit [T2Space M] in
theorem image_domain_eq_domainChartSet (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ} (hUc : (U : Set M) ⊆ c.source) :
    c '' (U : Set M) = domainChartSet U c := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨c.map_source (hUc hx),by simpa only [mem_preimage,c.left_inv (hUc hx)] using hx⟩
  · rintro ⟨hz,hzU⟩
    exact ⟨c.symm z,hzU,c.right_inv hz⟩

namespace DiscCover
variable [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The existing sharp planar theorem applies intrinsically to every open
domain contained in a single chart. Neither connectedness nor finite area
is required. The two omitted coordinate values ensure planar hyperbolicity. -/
theorem chart_point_removal_gain (p : DiscCover M)
    (U : TopologicalSpace.Opens M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hci : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c.symm c.target)
    (hUc : (U : Set M) ⊆ c.source)
    {a : M} (ha : a ∈ c.source)
    {b d : ℂ} (hbd : b ≠ d) (hb : b ∉ domainChartSet U c)
    (hd : d ∉ domainChartSet U c) :
    p.domainAreaGain U (punctureDomain U a) univ ≤ ENNReal.ofReal (2 * Real.pi) := by
  let V := punctureDomain U a
  let A := (domainChartSet U c)ᶜ
  have hA : IsClosed A := (isOpen_domainChartSet U c).isClosed_compl
  have hVc : (V : Set M) ⊆ c.source := fun _ hx => hUc hx.1
  have hAV : (domainChartSet V c)ᶜ = A ∪ {c a} := by
    rw [domainChartSet_puncture U ha,compl_sdiff,union_comm]
  have hbV : b ∉ domainChartSet V c := by
    rw [domainChartSet_puncture U ha]
    exact fun h => hb h.1
  have hdV : d ∉ domainChartSet V c := by
    rw [domainChartSet_puncture U ha]
    exact fun h => hd h.1
  have hρU := p.domainChartDensity_eq_planar U hc hci hUc hbd hb hd
  have hρV := p.domainChartDensity_eq_planar V hc hci hVc hbd hbV hdV
  have hρV' (z : ℂ) : p.domainChartDensity V c z =
      closedComplementDensity (A ∪ {c a}) (hA.union isClosed_singleton) hbd
        (Or.inl hb) (Or.inl hd) z := by
    simpa only [hAV] using hρV z
  rw [← p.domainAreaGain_inter U V univ,univ_inter,
    p.domainAreaGain_coordinate_formula U V hc V.isOpen.measurableSet hVc,
    image_domain_eq_domainChartSet V hVc]
  have hset : domainChartSet V c = (A ∪ {c a})ᶜ := by
    rw [← hAV,compl_compl]
  rw [hset]
  calc
    (∫⁻ z in (A ∪ {c a})ᶜ, ENNReal.ofReal
        ((p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2)) =
        ∫⁻ z in (A ∪ {c a})ᶜ,
          hyperbolicAreaWeight (A ∪ {c a}) (hA.union isClosed_singleton) hbd
            (Or.inl hb) (Or.inl hd) z - hyperbolicAreaWeight A hA hbd hb hd z := by
      apply setLIntegral_congr_fun (hA.union isClosed_singleton).measurableSet.compl
      intro z _
      dsimp only
      rw [hρU z,hρV' z]
      exact ENNReal.ofReal_sub _ (sq_nonneg _)
    _ ≤ _ := point_removal_gain_le_two_pi A hA hbd hb hd

end DiscCover
end AreaDeficit.Surfaces
