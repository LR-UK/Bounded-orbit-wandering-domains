module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainGainLimit
public import BoundedWanderingDomains.CompactCutoff

@[expose] public section

/-! # A fixed compact chart set has uniformly bounded remote area gain -/
open Set Function Filter MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

/-- Uniformity is over every closed old complement, not merely finite
punctures. The measured set need not stay away from that old complement. -/
theorem remote_domain_chart_compact_gain (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {L D : Set ℂ} (hL : IsCompact L) (hD : IsOpen D) (hLD : L ⊆ D)
    (hDc : D ⊆ c.target) (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (A : Set M) (hA : IsClosed A),
      (∫⁻ z in L ∩ domainChartSet ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩ c,
        ENNReal.ofReal
          ((p.domainChartDensity ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩ c z)^2 -
            (p.domainChartDensity ⟨Aᶜ,hA.isOpen_compl⟩ c z)^2)) ≤ B := by
  obtain ⟨B,hB,hbound⟩ := p.remote_domain_chart_cutoff hK hC hCK hc hD hDc hDC
  obtain ⟨chi,hchi,hcomp,hsupp,hchi0,hchiL⟩ := exists_compact_cutoff hL hD hLD
  refine ⟨ENNReal.ofReal (B * ∫ z, |Δ chi z|), ENNReal.ofReal_ne_top, ?_⟩
  intro A hA
  let U : TopologicalSpace.Opens M := ⟨Aᶜ,hA.isOpen_compl⟩
  let V : TopologicalSpace.Opens M := ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩
  have hVU : V ≤ U := fun _ h ha => h (Or.inl ha)
  have hm : MeasurableSet (L ∩ domainChartSet V c) :=
    hL.measurableSet.inter (isOpen_domainChartSet V c).measurableSet
  calc
    (∫⁻ z in L ∩ domainChartSet V c,
        ENNReal.ofReal ((p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2)) ≤
      ∫⁻ z in L ∩ domainChartSet V c, ENNReal.ofReal (chi z *
        ((p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2)) := by
          apply setLIntegral_mono' hm
          intro z hz
          have hpos := p.domainChartDensity_pos U hc ⟨hz.2.1,hVU hz.2.2⟩
          have hmono := p.domainChartDensity_mono hVU hc hz.2
          have hn : 0 ≤ (p.domainChartDensity V c z)^2 -
              (p.domainChartDensity U c z)^2 := by nlinarith
          exact ENNReal.ofReal_le_ofReal (by nlinarith [hchiL z hz.1])
    _ ≤ ∫⁻ z in domainChartSet V c, ENNReal.ofReal (chi z *
        ((p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2)) :=
      lintegral_mono_set inter_subset_right
    _ ≤ ENNReal.ofReal (B * ∫ z, |Δ chi z|) :=
      hbound A hA chi hchi hcomp hchi0 hsupp

end AreaDeficit.Surfaces.DiscCover
