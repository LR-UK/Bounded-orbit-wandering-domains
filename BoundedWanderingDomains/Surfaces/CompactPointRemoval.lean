module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.ChartPointRemoval
public import BoundedWanderingDomains.Surfaces.DomainRemoteArea
public import BoundedWanderingDomains.Surfaces.DomainGainOrder
public import BoundedWanderingDomains.Surfaces.SmallChartDomain

@[expose] public section

/-! # Uniform finite puncture cost on compact subsets of a surface

Localise around the new puncture and apply the sharp planar bound there.
The localisation error and the gain away from the puncture have the
already proved uniform remote-removal bounds. This result is enough for
compact area budgets; it does not assert the sharp global surface bound.
-/
open Set Function Filter MeasureTheory Metric
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M]


namespace DiscCover
variable [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  [T2Space M] [SecondCountableTopology M] [LocallyCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- One finite bound for deleting a fixed point, uniform in every old open
domain, on a fixed compact set. The compact set may contain the puncture
and may intersect the old complement. -/
theorem compact_point_removal_gain (p : DiscCover M) (a : M)
    {L : Set M} (hL : IsCompact L) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ U : TopologicalSpace.Opens M,
      p.domainAreaGain U (punctureDomain U a) L ≤ B := by
  let c := chartAt ℂ a
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) a).1
  have hci := (mdifferentiable_chart (I := 𝓘(ℂ)) a).2
  have hac : a ∈ c.source := mem_chart_source ℂ a
  obtain ⟨D,haD,hDc,b,d,hbd,hb,hd⟩ := exists_small_chart_domain hac
  obtain ⟨C,hC,haC,hCD⟩ := exists_compact_subset D.isOpen haD
  obtain ⟨B₀,hB₀,hlocal⟩ := p.compact_localization_domainAreaGain D hC hCD
  let R := L \ interior C
  have hR : IsCompact R := hL.diff isOpen_interior
  have hRa : R ⊆ ({a} : Set M)ᶜ := by
    rintro x ⟨_,hx⟩ hxa
    exact hx (mem_singleton_iff.mp hxa ▸ haC)
  let E : TopologicalSpace.Opens M := ⟨{a}ᶜ,isClosed_singleton.isOpen_compl⟩
  obtain ⟨B₁,hB₁,hremote⟩ := p.compact_localization_domainAreaGain E hR hRa
  refine ⟨(B₀ + ENNReal.ofReal (2 * Real.pi)) + B₁,
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hB₀,ENNReal.ofReal_ne_top⟩,hB₁⟩,?_⟩
  intro U
  let V := punctureDomain U a
  let W := U ⊓ D
  let Z := punctureDomain W a
  have hZV : Z ≤ V := fun _ hx => ⟨hx.1.1,hx.2⟩
  have hCZ : C ∩ V ⊆ Z := by
    rintro x ⟨hxC,hxV⟩
    exact ⟨⟨hxV.1,hCD hxC⟩,hxV.2⟩
  have hWc : (W : Set M) ⊆ c.source := fun _ hx => hDc hx.2
  have hbW : b ∉ domainChartSet W c := fun h => hb ⟨h.1,h.2.2⟩
  have hdW : d ∉ domainChartSet W c := fun h => hd ⟨h.1,h.2.2⟩
  have hsharp := p.chart_point_removal_gain W hc hci hWc hac hbd hbW hdW
  have hnear : p.domainAreaGain U V C ≤ B₀ + ENNReal.ofReal (2 * Real.pi) := by
    calc
      p.domainAreaGain U V C ≤ p.domainAreaGain U W C + p.domainAreaGain W Z C :=
        p.domainAreaGain_localize U V W Z hZV hC.measurableSet hCZ
      _ ≤ B₀ + ENNReal.ofReal (2 * Real.pi) :=
        add_le_add (hlocal U) ((measure_mono (subset_univ C)).trans hsharp)
  have hfar : p.domainAreaGain U V R ≤ B₁ := hremote U
  calc
    p.domainAreaGain U V L ≤ p.domainAreaGain U V (C ∪ R) := by
      apply measure_mono
      intro x hx
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · exact Or.inr ⟨hx,fun hi => hxC (interior_subset hi)⟩
    _ ≤ p.domainAreaGain U V C + p.domainAreaGain U V R := measure_union_le _ _
    _ ≤ _ := add_le_add hnear hfar

end DiscCover
end AreaDeficit.Surfaces
