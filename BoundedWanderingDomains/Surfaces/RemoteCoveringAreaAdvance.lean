/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OpenDomainFinitePatchTransport
import BoundedWanderingDomains.Surfaces.UniformFiniteRemoval

/-! # Uniform one-step area advance from a remote covering model -/

open Set Function MeasureTheory
open scoped Manifold ENNReal Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [T2Space X] [LocallyCompactSpace X]

/-- If a one-step map is a covering after removing a fixed remote compact
set and at most `q` exceptional values, its exact pullback identity gives a
uniform area-advance estimate in every old open-domain model. -/
theorem exists_uniform_area_advance_of_remote_coverings
    (p : DiscCover X) (q : ℕ) {H L : Set X}
    (hH : IsCompact H) (hL : IsCompact L) (hLH : Disjoint L H) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (E : Finset X), E.card ≤ q → ∀ (U T : TopologicalSpace.Opens X),
      T ≤ U →
      ∀ (F : T → ↥(finiteRemovalDomain U E ⊓
          (⟨Hᶜ, hH.isClosed.isOpen_compl⟩ : TopologicalSpace.Opens X))),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → IsCoveringMap F →
      ∀ (f : X → X),
      (fun x : T => f x) = (fun x => (F x : X)) →
      ∀ {ι : Type*} [DecidableEq ι] (I : Finset ι)
        (c d : ι → OpenPartialHomeomorph X ℂ)
        (A : ι → Set X) (W : Set X),
      (∀ i ∈ I, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c i) (c i).source) →
      (∀ i ∈ I, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (d i) (d i).source) →
      (∀ i ∈ I, MeasurableSet (A i)) →
      (∀ i ∈ I, MeasurableSet (f '' A i)) →
      (∀ i ∈ I, A i ⊆ T) →
      (∀ i ∈ I, A i ⊆ (c i).source) →
      (∀ i ∈ I, f '' A i ⊆ (d i).source) →
      (∀ i ∈ I, A i ⊆ W) →
      Set.PairwiseDisjoint (I : Set ι) A →
      (⋃ i ∈ I, A i) = W → InjOn f W →
      MeasurableSet (f '' W) → f '' W ⊆ L →
      p.domainArea U W ≤ p.domainArea U (f '' W) + C := by
  obtain ⟨C, hC, hremote⟩ :=
    p.uniform_compact_finite_remote_area_le q hH hL hLH
  refine ⟨C, hC, ?_⟩
  intro E hEq U T hTU F hF hcov f hf ι _ I c d A W
    hc hd hA hfA hAT hAc hfAd hsub hdis hcover hinj hfW hfWL
  have hsource : p.domainArea U W ≤ p.domainArea T W := by
    apply p.domainArea_mono_on hTU
    · rw [← hcover]
      exact MeasurableSet.biUnion I.countable_toSet hA
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover.symm ▸ hx)
      exact hAT i hi hxi
  have htransport : p.domainArea T W ≤
      p.domainArea (finiteRemovalDomain U E ⊓
        ⟨Hᶜ, hH.isClosed.isOpen_compl⟩) (f '' W) :=
    p.domainArea_le_image_of_openDomain_covering_finite_patches
      T _ F hF hcov hf I c d hc hd A hA hfA hAT hAc hfAd
      hsub hdis hcover hinj
  exact hsource.trans (htransport.trans (hremote E hEq U (f '' W) hfW hfWL))

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.exists_uniform_area_advance_of_remote_coverings
