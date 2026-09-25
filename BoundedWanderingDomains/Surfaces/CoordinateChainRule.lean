/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CoordinateDerivative
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]
omit [IsManifold 𝓘(ℂ) 1 N] in
theorem coordinate_deriv_comp {U : TopologicalSpace.Opens ℂ} {g : U → M} {f : M → N}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {w : U} (hwc : g w ∈ c.source) (hwd : f (g w) ∈ d.source) :
    deriv (planeExtension (d ∘ f ∘ g)) w =
      deriv (d ∘ f ∘ c.symm) (c (g w)) * deriv (planeExtension (c ∘ g)) w := by
  have hcw : c (g w) ∈ c.target := c.map_source hwc
  have hci := (mdifferentiableOn_symm hc _ hcw).mdifferentiableAt
    (c.open_target.mem_nhds hcw)
  have hdg := (hd _ hwd).mdifferentiableAt (d.open_source.mem_nhds hwd)
  have houter : DifferentiableAt ℂ (d ∘ f ∘ c.symm) (c (g w)) := by
    have hdf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (d ∘ f) (c.symm (c (g w))) := by
      rw [c.left_inv hwc]
      exact hdg.comp (g w) (hf (g w))
    exact (hdf.comp (c (g w)) hci).differentiableAt
  have hinner : DifferentiableAt ℂ (planeExtension (c ∘ g)) w :=
    planeExtension_mdifferentiableAt
      (((hc _ hwc).mdifferentiableAt (c.open_source.mem_nhds hwc)).comp w (hg w))
  have he : planeExtension (d ∘ f ∘ g) =ᶠ[𝓝 (w : ℂ)]
      (d ∘ f ∘ c.symm) ∘ planeExtension (c ∘ g) := by
    have hV : IsOpen (Subtype.val '' (g ⁻¹' c.source)) :=
      U.isOpen.isOpenMap_subtype_val _ (c.open_source.preimage hg.continuous)
    filter_upwards [hV.mem_nhds ⟨w,hwc,rfl⟩] with z hz
    obtain ⟨v,hv,rfl⟩ := hz
    change planeExtension (d ∘ f ∘ g) v =
      (d ∘ f ∘ c.symm) (planeExtension (c ∘ g) v)
    rw [planeExtension_coe, planeExtension_coe]
    simp only [comp_apply, c.left_inv hv]
  rw [he.deriv_eq]
  have hval : planeExtension (c ∘ g) w = c (g w) := planeExtension_coe _ w
  rw [deriv_comp (w : ℂ) (hval.symm ▸ houter) hinner, hval]
end AreaDeficit.Surfaces
