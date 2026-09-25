/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FinitePunctureChartTarget
import BoundedWanderingDomains.Surfaces.AreaGain

/-! # Erasing finite exceptional chart points from area integrals -/

open Set Function MeasureTheory
open scoped ENNReal
namespace AreaDeficit.Surfaces

/-- The finite exceptional set in the fixed chart estimate does not change
the integral; no regularity of the integrand at the punctures is needed. -/
theorem finite_exception_chart_integral (F : Finset ℂ) {A : Set ℂ}
    (hA : MeasurableSet A) (g : ℂ → ℝ) :
    (∫⁻ z in A, ENNReal.ofReal (if z ∈ F then 0 else g z)) =
      ∫⁻ z in A, ENNReal.ofReal (g z) := by
  have hF : (volume : Measure ℂ) (↑F : Set ℂ) = 0 := F.measure_zero _
  have hnot : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ (↑F : Set ℂ) := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hF
  apply setLIntegral_congr_fun_ae hA
  filter_upwards [hnot] with z hz _
  simp [show z ∉ F from hz]

end AreaDeficit.Surfaces

namespace AreaDeficit.Surfaces

/-- An inverse chart sends measurable subsets of its target to measurable
subsets of the surface. -/
theorem chart_inverse_image_measurable {N : Type*} [TopologicalSpace N]
    [MeasurableSpace N] [BorelSpace N]
    (e : OpenPartialHomeomorph N ℂ) {A : Set ℂ}
    (hA : MeasurableSet A) (hAt : A ⊆ e.target) :
    MeasurableSet (e.symm '' A) := by
  let V : Set e.target := Subtype.val ⁻¹' A
  have hV : MeasurableSet V := measurable_subtype_coe hA
  have he := e.symm.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image.mpr hV
  convert he using 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z,hAt hz⟩,hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z, hz, rfl⟩

end AreaDeficit.Surfaces

open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- A uniform chart-area gain estimate stated without the finite exceptional
set in the integrand. Integrals ignore its values at the punctures. -/
theorem ambient_chart_compact_gain_all_punctures (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C)
    (hCK : Disjoint C K) (c : OpenPartialHomeomorph M ℂ)
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A D : Set ℂ} (hA : IsCompact A) (hD : IsOpen D)
    (hAD : A ⊆ D) (hDc : D ⊆ c.target)
    (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ R : ℝ, ∀ (P : Finset M) (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (hWN : Nonempty W)
      (s : DiscCover W),
      (∫⁻ z in A, ENNReal.ofReal
        ((s.chartDensity ((c.subtypeRestr hUN).subtypeRestr hWN) z)^2 -
          (r.chartDensity (c.subtypeRestr hUN) z)^2)) ≤ ENNReal.ofReal R := by
  obtain ⟨R, hR⟩ := p.ambient_chart_compact_gain_finite_punctures
    hK hC hCK c hc hA hD hAD hDc hDC
  refine ⟨R, ?_⟩
  intro P U hU hUN r W hW hWN s
  rw [← AreaDeficit.Surfaces.finite_exception_chart_integral
    (AreaDeficit.Surfaces.chartPunctures c P) hA.measurableSet]
  exact hR P U hU hUN r W hW hWN s

end AreaDeficit.Surfaces.DiscCover

namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Intrinsic area gain on the portion of a fixed chart compact set that
survives finite punctures has a uniform bound. -/
theorem ambient_intrinsic_chart_gain_finite_punctures (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C)
    (hCK : Disjoint C K) (c : OpenPartialHomeomorph M ℂ)
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A D : Set ℂ} (hA : IsCompact A) (hD : IsOpen D)
    (hAD : A ⊆ D) (hDc : D ⊆ c.target)
    (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ R : ℝ, ∀ (P : Finset M) (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (hWN : Nonempty W)
      (s : DiscCover W),
      r.areaGain s (((c.subtypeRestr hUN).subtypeRestr hWN).symm ''
        (A \ (↑(AreaDeficit.Surfaces.chartPunctures c P) : Set ℂ))) ≤
          ENNReal.ofReal R := by
  obtain ⟨R, hR⟩ := p.ambient_chart_compact_gain_all_punctures
    hK hC hCK c hc hA hD hAD hDc hDC
  refine ⟨R, ?_⟩
  intro P U hU hUN r W hW hWN s
  let d := c.subtypeRestr hUN
  let e := d.subtypeRestr hWN
  let F := AreaDeficit.Surfaces.chartPunctures c P
  let A' : Set ℂ := A \ (↑F : Set ℂ)
  have hA' : MeasurableSet A' := hA.measurableSet.diff F.finite_toSet.measurableSet
  have hAt : A' ⊆ e.target := by
    intro z hz
    exact AreaDeficit.Surfaces.finite_puncture_restricted_chart_target
      P U hU hUN hCK W hW hWN c (hDc (hAD hz.1)) hz.2 (hDC z (hAD hz.1))
  have hmeas : MeasurableSet (e.symm '' A') :=
    AreaDeficit.Surfaces.chart_inverse_image_measurable e hA' hAt
  have hsource : e.symm '' A' ⊆ e.source := by
    rintro w ⟨z, hz, rfl⟩
    exact e.symm.map_source (hAt hz)
  have himage : e '' (e.symm '' A') = A' := by
    ext z
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [e.right_inv (hAt hy)] using hy
    · intro hz
      exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.right_inv (hAt hz)⟩
  rw [r.areaGain_coordinate_formula s hWN
    (mdifferentiableOn_subtypeRestr hUN hc) hmeas hsource, himage]
  have hF : (volume : Measure ℂ) (↑F : Set ℂ) = 0 := F.measure_zero _
  have hnot : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ (↑F : Set ℂ) := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hF
  have hset : A' =ᵐ[volume] A := by
    filter_upwards [hnot] with z hz
    simp [A', hz]
  rw [setLIntegral_congr hset]
  exact hR P U hU hUN r W hW hWN s

end AreaDeficit.Surfaces.DiscCover
