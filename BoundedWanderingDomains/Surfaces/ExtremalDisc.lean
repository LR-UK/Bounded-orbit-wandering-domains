/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.SurfaceSchwarz
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic
import BoundedWanderingDomains.Surfaces.UniformDiscAvoidance

/-! # Extremal holomorphic discs for the intrinsic hyperbolic density -/
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem density_extremal_disc (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source) {x : M} (hx : x ∈ c.source) :
    ∃ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ g discZero = x ∧
      p.density c x * ‖deriv (planeExtension (c ∘ g)) (0 : ℂ)‖ = 2 := by
  obtain ⟨w,rfl⟩ := p.surjective x
  obtain ⟨m,hm,hmm,hm0,hscale⟩ := exists_disc_recentring w.2
  let mD : unitDisc → unitDisc := fun z => ⟨m z,hmm z.2⟩
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) mD := by
    apply (mdifferentiable_subtypeVal_comp_iff unitDisc mD).mp
    intro z
    change MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : unitDisc => m z) z
    apply mdifferentiableAt_subtype_iff.mpr
    exact (hm.differentiableAt (isOpen_ball.mem_nhds z.2)).mdifferentiableAt
  have hmD0 : mD discZero = w := Subtype.ext hm0
  let g := p.projection ∘ mD
  refine ⟨g,p.holomorphic.comp hmd,?_,?_⟩
  · change p.projection (mD discZero) = p.projection w
    rw [hmD0]
  · have hp := ((hc _ hx).mdifferentiableAt (c.open_source.mem_nhds hx)).comp w
      (p.holomorphic w)
    have hd := planeExtension_deriv_comp (g := c ∘ p.projection) (h := mD)
      (w := discZero) (hmD0.symm ▸ hp) (hmd discZero)
    rw [hmD0] at hd
    have hmeq : planeExtension (fun z => (mD z : ℂ)) =ᶠ[𝓝 (0 : ℂ)] m := by
      filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
      exact planeExtension_coe (fun z => (mD z : ℂ)) ⟨z,hz⟩
    have hp0 : ‖deriv (planeExtension (c ∘ p.projection)) w‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (p.coordinate_deriv_ne_zero hc hx)
    change p.density c (p.projection w) *
      ‖deriv (planeExtension ((c ∘ p.projection) ∘ mD)) (discZero : ℂ)‖ = 2
    rw [p.density_eq_fibre hc hx,fibreDensity,hd]
    change (discDensity w / ‖deriv (planeExtension (c ∘ p.projection)) w‖) *
      ‖deriv (planeExtension (c ∘ p.projection)) w *
        deriv (planeExtension (fun z => (mD z : ℂ))) 0‖ = 2
    rw [hmeq.deriv_eq,norm_mul]
    calc
      _ = discDensity w * ‖deriv m 0‖ := by field_simp
      _ = 2 := hscale

end AreaDeficit.Surfaces.DiscCover
