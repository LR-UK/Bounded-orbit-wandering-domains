/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactOrbitNormal
import BoundedWanderingDomains.Surfaces.LocalMapRestriction

/-! # Compact interior orbits survive a relatively compact restriction -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

omit [T2Space X] [LocallyCompactSpace X] in
/-- Uniform small-disc avoidance keeps a whole neighbourhood of a compact
marked interior orbit inside any prescribed open neighbourhood of that orbit. -/
theorem mem_interior_trapped_restrict_of_compact_orbit
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : DiscCover X)
    (V : TopologicalSpace.Opens X) (hVsource : (V : Set X) ⊆ f.source)
    {x : X} (hx : x ∈ interior f.trapped)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (horbitK : ∀ n, f.orbit n ⟨x, interior_subset hx⟩ ∈ K) :
    x ∈ interior (f.restrictSource V hVsource).trapped := by
  let W : TopologicalSpace.Opens X := ⟨interior f.trapped, isOpen_interior⟩
  let hW : (W : Set X) ⊆ f.trapped := interior_subset
  obtain ⟨D, hDcenter, hDsub⟩ :=
    SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset W.isOpen hx
  let d : unitDisc → W := fun z => ⟨D.param z, hDsub (D.param_mem_closedCarrier z)⟩
  have hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) d := by
    apply (mdifferentiable_subtypeVal_comp_iff W d).mp
    exact D.mdifferentiable_param
  let F : ℕ → unitDisc → X := fun n => f.orbitOn W hW n ∘ d
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := fun n =>
    (f.mdifferentiable_orbitOn hf W hW n).comp hd
  have hF0 : ∀ n, F n discZero ∈ K := by
    intro n
    simpa only [F, comp_apply, d, orbitOn, D.param_zero, hDcenter] using horbitK n
  obtain ⟨r, hr, -, havoid⟩ := p.compact_uniform_disc_avoidance V.isOpen.isClosed_compl
    hK (disjoint_left.mpr (fun _ hx hxnot => hxnot (hKV hx)))
  let R := {z : unitDisc | ‖(z : ℂ)‖ < r}
  have hR : IsOpen R := isOpen_lt continuous_subtype_val.norm continuous_const
  have hximage : x ∈ D.param '' R :=
    ⟨discZero, by change ‖(0 : ℂ)‖ < r; simpa using hr,
      D.param_zero.trans hDcenter⟩
  have himage : D.param '' R ⊆ (f.restrictSource V hVsource).trapped := by
    rintro y ⟨z, hz, rfl⟩
    apply f.restrictSource_mem_trapped_of_orbit_mem V hVsource
      (hW (d z).property)
    intro n
    have hh := havoid (F n) (hF n) (hF0 n) z hz
    exact not_not.mp hh
  exact ((D.isOpenEmbedding_param.isOpenMap _ hR).subset_interior_iff.mpr himage) hximage

end SurfaceDynamics.LocalMap
