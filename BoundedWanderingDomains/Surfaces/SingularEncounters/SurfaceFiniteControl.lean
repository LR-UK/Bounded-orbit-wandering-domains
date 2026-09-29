module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompactSurfaceFiniteControl
public import BoundedWanderingDomains.Surfaces.SingularEncounters.NoncompactSurfaceFiniteControl

@[expose] public section

/-! # Finite component control on an arbitrary target surface -/

open Set Function MeasureTheory
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

theorem no_compact_positive_area_saturation_of_finite_component_control
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A K : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) (hpos : HasPositiveChartArea A)
    (hK : IsCompact K) (hsatK : f.saturation A ⊆ K)
    {ι : Type*} [Fintype ι] (D : ι → EmbeddedDisc X) (E : Finset X)
    (L : ι → Set X) (hL : ∀ i, IsCompact (L i)) (hLD : ∀ i, L i ⊆ (D i).carrier)
    (hcontrol : ∀ x ∈ f.saturation A, ∃ i, f.totalize x ∈ L i ∧
      x ∈ f.finiteObstructionSource hf.2.continuous (D i).carrier (E : Set X)) : False := by
  by_cases hc : IsCompact (univ : Set X)
  · let compactSurface : CompactSpace X := ⟨hc⟩
    exact no_compact_surface_positive_area_saturation_of_finite_component_control
      f hf hA hAbad hdis hinj hpos D E L hL hLD hcontrol
  · exact no_noncompact_surface_positive_area_saturation_of_finite_component_control hc
      f hf hA hAbad hdis hinj hpos hK hsatK D E L hL hLD hcontrol

end SurfaceDynamics
