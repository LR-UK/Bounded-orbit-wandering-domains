module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseDiscImages

@[expose] public section

/-! # Compact avoidance on disconnected hyperbolic manifolds -/

open Set Function Filter Metric RiemannDynamics
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]

theorem compact_uniform_avoidance_outside (p : ComponentwiseDiscCover M)
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

end AreaDeficit.Surfaces.ComponentwiseDiscCover
