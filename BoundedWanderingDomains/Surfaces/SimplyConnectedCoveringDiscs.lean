module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
public import BoundedWanderingDomains.Surfaces.LocalCoveringDiscs
public import BoundedWanderingDomains.Surfaces.SurfaceSingularCovering

@[expose] public section

open Set Function Topology
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem injective_of_simplyConnected (p : DiscCover X) [SimplyConnectedSpace X] :
    Injective p.projection := by
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  let : LocallyPathConnectedSpace unitDisc := ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have hA : IsSimplyConnected (univ : Set unitDisc) :=
    (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace
  have hB : IsSimplyConnected (univ : Set X) :=
    (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace
  have hh := covering_injOn_simplyConnected isOpen_univ hA isOpen_univ hB
    (a := discZero) (mem_univ _) p.continuous.continuousOn (fun _ _ => mem_univ _)
    p.covering.isCoveringMapOn
  exact fun x y he => hh (mem_univ _) (mem_univ _) he

end AreaDeficit.Surfaces.DiscCover

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem injOn_of_simplyConnected_regular_image
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {D T : Set X} (hDo : IsOpen D) (hDsc : IsSimplyConnected D)
    (hTo : IsOpen T) (hTsc : IsSimplyConnected T)
    (hDs : D ⊆ f.source) (hmap : MapsTo f.totalize D T)
    (hreg : T ⊆ f.singularValuesᶜ) : InjOn f.totalize D := by
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let : LocallyPathConnectedSpace f.source := ChartedSpace.locallyPathConnectedSpace ℂ f.source
  let D0 : Set f.source := Subtype.val ⁻¹' D
  have hD0o : IsOpen D0 := hDo.preimage continuous_subtype_val
  have hD0image : (Subtype.val : f.source → X) '' D0 = D := by
    rw [image_preimage_eq_inter_range]
    exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hDs hx⟩, rfl⟩)
  have hD0sc : IsSimplyConnected D0 := by
    apply IsEmbedding.subtypeVal.isSimplyConnected_image.mp
    rwa [hD0image]
  obtain ⟨a, ha⟩ := hD0sc.nonempty
  have hi := AreaDeficit.Surfaces.covering_injOn_simplyConnected hD0o hD0sc hTo hTsc
    ha hf.2.continuous.continuousOn (p := f.map)
    (fun x hx => by
      have hh := hmap hx
      rwa [f.totalize_eq x.property] at hh)
    (f.isCoveringMapOn_compl_singularValues.mono hreg)
  intro x hx y hy he
  have he' : f.map ⟨x, hDs hx⟩ = f.map ⟨y, hDs hy⟩ := by
    simpa only [f.totalize_eq (hDs hx), f.totalize_eq (hDs hy)] using he
  exact congrArg Subtype.val (hi (x₁ := ⟨x, hDs hx⟩) (x₂ := ⟨y, hDs hy⟩) hx hy he')

end SurfaceDynamics.LocalMap
