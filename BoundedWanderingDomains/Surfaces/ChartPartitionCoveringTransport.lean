module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.GeneralCoveringAreaTransport

@[expose] public section

/-! # Covering transport from canonical countable chart partitions -/

open Set Function MeasureTheory
open scoped Manifold

namespace AreaDeficit.Surfaces.DiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [T2Space X] [LocallyCompactSpace X]

/-- A covering between open surface domains preserves intrinsic area on any
measurable set on which its ambient representative is injective. Countable
source/target chart partitions are constructed internally. -/
theorem domainArea_eq_image_of_openDomain_covering
    (p : DiscCover X) (U V : TopologicalSpace.Opens X)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {f : X → X} (hf : (fun x : U => f x) = (fun x => (F x : X)))
    (hfm : Measurable f) {W : Set X} (hW : MeasurableSet W)
    (hWU : W ⊆ U) (hinj : InjOn f W) :
    p.domainArea U W = p.domainArea V (f '' W) :=
  p.domainArea_eq_image_of_openDomain_covering_between p U V F hF hcov hf hfm hW hWU hinj

end AreaDeficit.Surfaces.DiscCover
