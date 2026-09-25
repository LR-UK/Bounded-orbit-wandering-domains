/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DensityCoordinateChange
import BoundedWanderingDomains.HolomorphicTransport
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]
noncomputable def coordinateArea (p : DiscCover M) (c : OpenPartialHomeomorph M ℂ)
    (A : Set M) : ℝ≥0∞ :=
  ∫⁻ z in c '' A, ENNReal.ofReal ((p.chartDensity c z)^2)

theorem chartArea_coordinate_change (p : DiscCover M)
    {c d : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {W : Set ℂ} (hW : MeasurableSet W)
    (hWc : W ⊆ c.target) (hWd : MapsTo c.symm W d.source) :
    (∫⁻ z in (d ∘ c.symm) '' W, ENNReal.ofReal ((p.chartDensity d z)^2)) =
      ∫⁻ z in W, ENNReal.ofReal ((p.chartDensity c z)^2) := by
  have hf : ∀ z ∈ W, HasDerivAt (d ∘ c.symm) (deriv (d ∘ c.symm) z) z := by
    intro z hz
    have hci := (mdifferentiableOn_symm hc _ (hWc hz)).mdifferentiableAt
      (c.open_target.mem_nhds (hWc hz))
    have hdi := (hd _ (hWd hz)).mdifferentiableAt (d.open_source.mem_nhds (hWd hz))
    exact (hdi.comp z hci).differentiableAt.hasDerivAt
  have hi : InjOn (d ∘ c.symm) W := by
    intro z hz z' hz' he
    exact c.symm.injOn (hWc hz) (hWc hz') (d.injOn (hWd hz) (hWd hz') he)
  rw [holomorphic_change_of_variables hW hf hi]
  apply setLIntegral_congr_fun hW
  intro z hz
  have hchange := p.density_sq_coordinate_change hc hd (c.map_target (hWc hz)) (hWd hz)
  rw [c.right_inv (hWc hz)] at hchange
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  change ‖deriv (d ∘ c.symm) z‖^2 * (p.density d (d.symm (d (c.symm z))))^2 =
    (p.density c (c.symm z))^2
  rw [d.left_inv (hWd hz), mul_comm]
  exact hchange

theorem coordinateArea_eq (p : DiscCover M)
    {c d : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {A : Set M} (hAc : A ⊆ c.source) (hAd : A ⊆ d.source)
    (hA : MeasurableSet (c '' A)) :
    p.coordinateArea d A = p.coordinateArea c A := by
  have hWc : c '' A ⊆ c.target := c.mapsTo.mono_left hAc |>.image_subset
  have hWd : MapsTo c.symm (c '' A) d.source := by
    rintro z ⟨x,hx,rfl⟩
    rw [c.left_inv (hAc hx)]
    exact hAd hx
  have he : (d ∘ c.symm) '' (c '' A) = d '' A := by
    rw [← image_comp]
    apply image_congr
    intro x hx
    simp only [comp_apply, c.left_inv (hAc hx)]
  simpa only [coordinateArea, he] using p.chartArea_coordinate_change hc hd hA hWc hWd
end AreaDeficit.Surfaces.DiscCover
