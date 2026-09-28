/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
import BoundedWanderingDomains.Surfaces.LocalMapTotalization

open Set Function Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

/-- The disc automorphism sending zero to a specified point. -/
noncomputable def discMobiusHomeomorph (w : unitDisc) : unitDisc ≃ₜ unitDisc := by
  let v : unitDisc := ⟨-(w : ℂ), by simpa only [unitDisc, TopologicalSpace.Opens.mem_mk,
    mem_ball_zero_iff, norm_neg] using w.property⟩
  exact
  { toFun := discMobiusFromZero w
    invFun := discMobiusFromZero v
    left_inv := fun z => Subtype.ext (by
      simpa only [discMobiusFromZero, v, neg_neg] using
        RiemannDynamics.mobiusDisk_neg_mobiusDisk z.property v.property)
    right_inv := fun z => Subtype.ext (by
      simpa only [discMobiusFromZero, v, neg_neg] using
        RiemannDynamics.mobiusDisk_neg_mobiusDisk z.property w.property)
    continuous_toFun := (discMobiusFromZero_holomorphic w).continuous
    continuous_invFun := (discMobiusFromZero_holomorphic v).continuous }

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

theorem DiscCover.exists_centred (p : DiscCover X) (x : X) :
    ∃ q : DiscCover X, q.projection discZero = x := by
  obtain ⟨w, hw⟩ := p.surjective x
  let q : DiscCover X :=
    { projection := p.projection ∘ discMobiusHomeomorph w
      holomorphic := p.holomorphic.comp (discMobiusFromZero_holomorphic w)
      covering := p.covering.comp_homeomorph (discMobiusHomeomorph w)
      surjective := p.surjective.comp (discMobiusHomeomorph w).surjective }
  refine ⟨q, ?_⟩
  change p.projection (discMobiusFromZero w discZero) = x
  rw [discMobiusFromZero_zero, hw]

end AreaDeficit.Surfaces

namespace SurfaceDynamics.LocalMap

open AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
theorem mdifferentiableOn_totalize (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f.totalize f.source := by
  intro x hx
  apply MDifferentiableAt.mdifferentiableWithinAt
  apply (mdifferentiableAt_subtype_iff (x := ⟨x, hx⟩)).mp
  have he : (fun z : f.source => f.totalize z) = f.map :=
    funext fun z => f.totalize_eq z.property
  rw [he]
  exact hf ⟨x, hx⟩

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] in
theorem isOpen_image_totalize (f : LocalMap X) (hf : IsOpenMap f.map)
    {D : Set X} (hD : IsOpen D) (hDs : D ⊆ f.source) :
    IsOpen (f.totalize '' D) := by
  have he : f.totalize '' D = f.map '' ((Subtype.val : f.source → X) ⁻¹' D) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hDs hx⟩, hx, (f.totalize_eq (hDs hx)).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, f.totalize_eq x.property⟩
  rw [he]
  exact hf _ (hD.preimage continuous_subtype_val)

/-- Equal-radius covering discs map forward for an open-source map. -/
theorem mapsTo_covering_open_radius (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (U W : TopologicalSpace.Opens X) (hUs : (U : Set X) ⊆ f.source)
    (p : DiscCover U) (q : DiscCover W)
    (hm : MapsTo f.totalize U W)
    (h0 : (q.projection discZero : X) = f.totalize (p.projection discZero)) (r : ℝ) :
    MapsTo f.totalize ((fun z => (p.projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r})
      ((fun z => (q.projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ < r}) := by
  let g : U → W := fun x => ⟨f.totalize x, hm x.property⟩
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    apply (mdifferentiable_subtypeVal_comp_iff W g).mp
    intro x
    exact ((f.mdifferentiableOn_totalize hf x (hUs x.property)).mdifferentiableAt
      (f.source.isOpen.mem_nhds (hUs x.property))).comp x (mdifferentiable_subtype_val U x)
  have hq0 : q.projection discZero = g (p.projection discZero) := Subtype.ext h0
  have hh := p.mapsTo_open_radius q hg hq0 r
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwe⟩ := hh (mem_image_of_mem _ hz)
  exact ⟨w, hw, congrArg Subtype.val hwe⟩

end SurfaceDynamics.LocalMap
