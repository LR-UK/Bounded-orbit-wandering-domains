module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.RemoteChartGain
public import BoundedWanderingDomains.Surfaces.AreaGain
public import BoundedWanderingDomains.CompactCutoff

@[expose] public section

/-! # Compact chart sets have uniformly bounded remote area gain -/
open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The constant depends on the chart and the compact measured set, but not on
the smaller covering metric. -/
theorem remote_chart_compact_gain_bound (p : DiscCover M) {K C : Set M}
    (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K)
    (V : TopologicalSpace.Opens M) (q : DiscCover V)
    (W : TopologicalSpace.Opens V)
    (hW : ∀ x : V, x ∈ W ↔ (x : M) ∉ K)
    (hNE : Nonempty W) (c : OpenPartialHomeomorph V ℂ)
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A D : Set ℂ} (hA : IsCompact A) (hD : IsOpen D) (hAD : A ⊆ D)
    (hDc : D ⊆ (c.subtypeRestr hNE).target)
    (hDC : ∀ z ∈ D, (((c.subtypeRestr hNE).symm z : V) : M) ∈ C) :
    ∃ R : ℝ, ∀ s : DiscCover W,
      (∫⁻ z in A, ENNReal.ofReal
        ((s.chartDensity (c.subtypeRestr hNE) z)^2 - (q.chartDensity c z)^2)) ≤
        ENNReal.ofReal R := by
  obtain ⟨B, hB, hbound⟩ := p.remote_chart_gain_bound hK hC hCK
  obtain ⟨chi, hchi, hcomp, hsupp, hchi0, hchiA⟩ :=
    AreaDeficit.exists_compact_cutoff hA hD hAD
  refine ⟨B * ∫ z, |Δ chi z|, ?_⟩
  intro s
  calc
    (∫⁻ z in A, ENNReal.ofReal
      ((s.chartDensity (c.subtypeRestr hNE) z)^2 - (q.chartDensity c z)^2)) ≤
        ∫⁻ z in A, ENNReal.ofReal (chi z *
          ((s.chartDensity (c.subtypeRestr hNE) z)^2 - (q.chartDensity c z)^2)) := by
            apply setLIntegral_mono' hA.measurableSet
            intro z hz
            have hpos : 0 ≤ (s.chartDensity (c.subtypeRestr hNE) z)^2 -
                (q.chartDensity c z)^2 := by
              rw [← q.chartLogRatio_laplacian s hNE hc (hDc (hAD hz))]
              exact q.chartLogRatio_laplacian_nonneg s hNE hc (hDc (hAD hz))
            exact ENNReal.ofReal_le_ofReal (by nlinarith [hchiA z hz])
    _ ≤ ∫⁻ z, ENNReal.ofReal (chi z *
      ((s.chartDensity (c.subtypeRestr hNE) z)^2 - (q.chartDensity c z)^2)) := by
        exact setLIntegral_le_lintegral A _
    _ ≤ ENNReal.ofReal (B * ∫ z, |Δ chi z|) :=
      hbound V q W s hW hNE c hc D hD hDc hDC chi hchi hcomp hchi0 hsupp

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Intrinsic gain over the part of a compact chart set is uniformly finite
for every disc cover of the smaller domain. -/
theorem remote_intrinsic_compact_chart_bound (p : DiscCover M) {K C : Set M}
    (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K)
    (V : TopologicalSpace.Opens M) (q : DiscCover V)
    (W : TopologicalSpace.Opens V)
    (hW : ∀ x : V, x ∈ W ↔ (x : M) ∉ K)
    (hNE : Nonempty W) (c : OpenPartialHomeomorph V ℂ)
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A D : Set ℂ} (hA : IsCompact A) (hD : IsOpen D) (hAD : A ⊆ D)
    (hDc : D ⊆ (c.subtypeRestr hNE).target)
    (hDC : ∀ z ∈ D, (((c.subtypeRestr hNE).symm z : V) : M) ∈ C) :
    ∃ R : ℝ, ∀ s : DiscCover W,
      q.areaGain s ((c.subtypeRestr hNE).symm '' A) ≤ ENNReal.ofReal R := by
  obtain ⟨R, hR⟩ := p.remote_chart_compact_gain_bound
    hK hC hCK V q W hW hNE c hc hA hD hAD hDc hDC
  refine ⟨R, ?_⟩
  intro s
  let d := c.subtypeRestr hNE
  have hAtarget : A ⊆ d.target := hAD.trans hDc
  have hcompact : IsCompact (d.symm '' A) :=
    hA.image_of_continuousOn (d.symm.continuousOn.mono hAtarget)
  have hmeas : MeasurableSet (d.symm '' A) := hcompact.isClosed.measurableSet
  have hsource : d.symm '' A ⊆ d.source := by
    rintro w ⟨z, hz, rfl⟩
    exact d.symm.map_source (hAtarget hz)
  have himage : d '' (d.symm '' A) = A := by
    ext z
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [d.right_inv (hAtarget hy)] using hy
    · intro hz
      exact ⟨d.symm z, ⟨z, hz, rfl⟩, d.right_inv (hAtarget hz)⟩
  rw [q.areaGain_coordinate_formula s hNE hc hmeas hsource, himage]
  exact hR s

end AreaDeficit.Surfaces.DiscCover
