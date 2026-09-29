module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.HyperbolicArea
public import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
public import BoundedWanderingDomains.DiscArea

@[expose] public section

/-! # Exact area of an embedded covering disc in one surface chart -/

open Set Function Metric MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] in
theorem hyperbolicArea_image_radius (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {r : ℝ} (hr1 : r < 1)
    (hchart : ∀ z : unitDisc, ‖(z : ℂ)‖ < r → p.projection z ∈ c.source)
    (hinj : InjOn p.projection {z : unitDisc | ‖(z : ℂ)‖ < r}) :
    p.hyperbolicArea (p.projection '' {z : unitDisc | ‖(z : ℂ)‖ < r}) =
      ∫⁻ z in ball (0 : ℂ) r, ENNReal.ofReal ((discDensity z)^2) := by
  let D := {z : unitDisc | ‖(z : ℂ)‖ < r}
  let g := planeExtension (c ∘ p.projection)
  have hD : IsOpen D := isOpen_lt continuous_subtype_val.norm continuous_const
  have hA : MeasurableSet (p.projection '' D) := (p.isOpenMap _ hD).measurableSet
  have hAc : p.projection '' D ⊆ c.source := by
    rintro x ⟨z, hz, rfl⟩
    exact hchart z hz
  have hsub : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball hr1.le
  have hval : ∀ z (hz : z ∈ ball (0 : ℂ) r),
      g z = c (p.projection ⟨z, hsub hz⟩) := fun z hz =>
    planeExtension_coe _ ⟨z, hsub hz⟩
  have hgd : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv g z) z := by
    intro z hz
    have hcz := hchart ⟨z, hsub hz⟩ (mem_ball_zero_iff.mp hz)
    exact (planeExtension_mdifferentiableAt
      (((hc _ hcz).mdifferentiableAt (c.open_source.mem_nhds hcz)).comp
        ⟨z, hsub hz⟩ (p.holomorphic ⟨z, hsub hz⟩))).hasDerivAt
  have hgi : InjOn g (ball (0 : ℂ) r) := by
    intro z hz w hw he
    rw [hval z hz, hval w hw] at he
    have hpp := c.injOn (hchart ⟨z, hsub hz⟩ (mem_ball_zero_iff.mp hz))
      (hchart ⟨w, hsub hw⟩ (mem_ball_zero_iff.mp hw)) he
    exact congrArg Subtype.val (hinj (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw) hpp)
  have himage : g '' ball (0 : ℂ) r = c '' (p.projection '' D) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨p.projection ⟨z, hsub hz⟩,
        ⟨⟨z, hsub hz⟩, mem_ball_zero_iff.mp hz, rfl⟩, (hval z hz).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, mem_ball_zero_iff.mpr hz, planeExtension_coe _ z⟩
  rw [p.hyperbolicArea_apply_chart hc hA hAc]
  unfold coordinateArea
  rw [← himage, holomorphic_change_of_variables isOpen_ball.measurableSet hgd hgi]
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro z hz
  let w : unitDisc := ⟨z, hsub hz⟩
  have hw : p.projection w ∈ c.source := hchart w (mem_ball_zero_iff.mp hz)
  have hd : ‖deriv g z‖ ≠ 0 := norm_ne_zero_iff.mpr (p.coordinate_deriv_ne_zero hc hw)
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  change ‖deriv g z‖^2 * (p.density c (c.symm (g z)))^2 = _
  rw [hval z hz, c.left_inv hw, p.density_eq_fibre hc hw]
  unfold fibreDensity
  change ‖deriv g z‖^2 * (discDensity z / ‖deriv g z‖)^2 = (discDensity z)^2
  field_simp

end AreaDeficit.Surfaces.DiscCover
