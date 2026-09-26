/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OpenDomainAreaTransport
import BoundedWanderingDomains.Surfaces.FinitePatchTransport

/-! # Finite-patch area transport through an open-domain covering -/

open Set Function MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [T2Space X]

/-- Exact covering pullback on finitely many chart patches gives the global
one-step area advance used by the cancellation argument. -/
theorem domainArea_le_image_of_openDomain_covering_finite_patches
    (p : DiscCover X) (U V : TopologicalSpace.Opens X)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {f : X → X} (hf : (fun x : U => f x) = (fun x => (F x : X)))
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (c d : ι → OpenPartialHomeomorph X ℂ)
    (hc : ∀ i ∈ I, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c i) (c i).source)
    (hd : ∀ i ∈ I, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (d i) (d i).source)
    (A : ι → Set X) {W : Set X}
    (hA : ∀ i ∈ I, MeasurableSet (A i))
    (hfiA : ∀ i ∈ I, MeasurableSet (f '' A i))
    (hAU : ∀ i ∈ I, A i ⊆ U)
    (hAc : ∀ i ∈ I, A i ⊆ (c i).source)
    (hfAd : ∀ i ∈ I, f '' A i ⊆ (d i).source)
    (hsub : ∀ i ∈ I, A i ⊆ W)
    (hdis : Set.PairwiseDisjoint (I : Set ι) A)
    (hcover : (⋃ i ∈ I, A i) = W)
    (hinj : InjOn f W) :
    p.domainArea U W ≤ p.domainArea V (f '' W) := by
  have hlocal : ∀ i ∈ I,
      p.domainArea U (A i) ≤ p.domainArea V (f '' A i) + 0 := by
    intro i hi
    rw [add_zero]
    exact (p.chart_domainArea_eq_image_of_openDomain_covering p U V F hF hcov hf
      (hc i hi) (hd i hi) (hA i hi) (hAU i hi) (hAc i hi)
      (hfAd i hi) (hfiA i hi) (hinj.mono (hsub i hi))).le
  simpa using AreaDeficit.Surfaces.finite_patch_area_advance
    (p.domainArea U) (p.domainArea V) I A (fun _ => 0)
    hA hfiA hsub hdis hcover hinj hlocal

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.domainArea_le_image_of_openDomain_covering_finite_patches
