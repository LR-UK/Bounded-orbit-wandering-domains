/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.CoordinateDerivative
import BoundedWanderingDomains.Surfaces.DiscSchwarz

/-! # Intrinsic hyperbolic density in surface coordinates

The density obtained from a supplied disc cover is independent of both the
chosen point of a fibre and the chosen cover. These are consequences of
holomorphic lifting and Schwarz–Pick, not additional fields of the cover.
-/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

namespace DiscCover

/-- The density in a target coordinate, evaluated using a specified lift. -/
noncomputable def fibreDensity (p : DiscCover M) (c : OpenPartialHomeomorph M ℂ)
    (w : unitDisc) : ℝ :=
  discDensity w / ‖deriv (planeExtension (c ∘ p.projection)) w‖

/-- Comparison between the densities computed using two disc covers. -/
theorem fibreDensity_le (p q : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {w v : unitDisc} (hwv : p.projection w = q.projection v)
    (hv : q.projection v ∈ c.source) :
    p.fibreDensity c w ≤ q.fibreDensity c v := by
  let : LocallyPathConnectedSpace unitDisc := ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  obtain ⟨h,hv0,hfac,hh⟩ := exists_holomorphic_lift p.holomorphic p.covering
    q.holomorphic v w hwv
  have hw : p.projection w ∈ c.source := hwv ▸ hv
  have hp := ((hc _ hw).mdifferentiableAt (c.open_source.mem_nhds hw)).comp w
    (p.holomorphic w)
  have hd := planeExtension_deriv_comp (g := c ∘ p.projection) (h := h)
    (w := v) (hv0.symm ▸ hp) (hh v)
  have hfun : (c ∘ p.projection) ∘ h = c ∘ q.projection := by
    rw [Function.comp_assoc, hfac]
  rw [hfun, hv0] at hd
  have hs := unitDisc_schwarz hh v
  rw [hv0] at hs
  have hp0 : ‖deriv (planeExtension (c ∘ p.projection)) w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (p.coordinate_deriv_ne_zero hc hw)
  have hqpos : 0 < ‖deriv (planeExtension (c ∘ q.projection)) v‖ :=
    norm_pos_iff.mpr (q.coordinate_deriv_ne_zero hc hv)
  unfold fibreDensity
  apply (le_div_iff₀ hqpos).mpr
  calc
    _ = discDensity w * ‖deriv (planeExtension (fun z => (h z : ℂ))) v‖ := by
      rw [hd, norm_mul]
      field_simp
    _ ≤ discDensity v := hs

/-- Independence of the selected covering point and of the supplied cover. -/
theorem fibreDensity_eq (p q : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {w v : unitDisc} (hwv : p.projection w = q.projection v)
    (hv : q.projection v ∈ c.source) :
    p.fibreDensity c w = q.fibreDensity c v :=
  le_antisymm (p.fibreDensity_le q hc hwv hv)
    (q.fibreDensity_le p hc hwv.symm (hwv ▸ hv))

/-- Hyperbolic density in a target chart. Only values on the chart source
are used; the arbitrary selected lift does not affect those values. -/
noncomputable def density (p : DiscCover M) (c : OpenPartialHomeomorph M ℂ) (x : M) : ℝ :=
  p.fibreDensity c (Classical.choose (p.surjective x))

theorem density_eq_fibre (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {w : unitDisc} (hw : p.projection w ∈ c.source) :
    p.density c (p.projection w) = p.fibreDensity c w :=
  p.fibreDensity_eq p hc (Classical.choose_spec (p.surjective (p.projection w))) hw

theorem density_independent (p q : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) {x : M} (hx : x ∈ c.source) :
    p.density c x = q.density c x := by
  obtain ⟨w,rfl⟩ := p.surjective x
  obtain ⟨v,hv⟩ := q.surjective (p.projection w)
  rw [p.density_eq_fibre hc hx, ← hv, q.density_eq_fibre hc (hv ▸ hx)]
  exact p.fibreDensity_eq q hc hv.symm (hv ▸ hx)

theorem density_pos (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) {x : M} (hx : x ∈ c.source) :
    0 < p.density c x := by
  obtain ⟨w,rfl⟩ := p.surjective x
  rw [p.density_eq_fibre hc hx]
  exact div_pos (discDensity_pos (mem_ball_zero_iff.mp w.2))
    (norm_pos_iff.mpr (p.coordinate_deriv_ne_zero hc hx))

end DiscCover
end AreaDeficit.Surfaces
