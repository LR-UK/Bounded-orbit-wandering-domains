/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.OpenDomainAreaTransport

/-! # Countable-patch exact area transport -/

open Set Function MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [T2Space X]

/-- Exact local covering transport sums over a countable measurable chart
partition. There is no accumulated error term. -/
theorem domainArea_eq_image_of_openDomain_covering_countable_patches
    (p : DiscCover X) (U V : TopologicalSpace.Opens X)
    (F : U → V) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hcov : IsCoveringMap F)
    {f : X → X} (hf : (fun x : U => f x) = (fun x => (F x : X)))
    (c d : ℕ → OpenPartialHomeomorph X ℂ)
    (hc : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c i) (c i).source)
    (hd : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (d i) (d i).source)
    (A : ℕ → Set X) {W : Set X}
    (hA : ∀ i, MeasurableSet (A i))
    (hfiA : ∀ i, MeasurableSet (f '' A i))
    (hAU : ∀ i, A i ⊆ U)
    (hAc : ∀ i, A i ⊆ (c i).source)
    (hfAd : ∀ i, f '' A i ⊆ (d i).source)
    (hsub : ∀ i, A i ⊆ W)
    (hdis : Pairwise (Disjoint on A))
    (hcover : (⋃ i, A i) = W) (hinj : InjOn f W) :
    p.domainArea U W = p.domainArea V (f '' W) := by
  have hlocal : ∀ i,
      p.domainArea U (A i) = p.domainArea V (f '' A i) := by
    intro i
    exact p.chart_domainArea_eq_image_of_openDomain_covering p U V F hF hcov hf
      (hc i) (hd i) (hA i) (hAU i) (hAc i) (hfAd i) (hfiA i)
      (hinj.mono (hsub i))
  have hdisImage : Pairwise (Disjoint on fun i => f '' A i) := by
    intro i j hij
    apply Set.disjoint_left.2
    rintro y ⟨x, hxi, rfl⟩ ⟨x', hxj, heq⟩
    have hxx : x = x' := hinj (hsub i hxi) (hsub j hxj) heq.symm
    subst x'
    exact Set.disjoint_left.mp (hdis hij) hxi hxj
  have hcoverImage : (⋃ i, f '' A i) = f '' W := by
    rw [← image_iUnion, hcover]
  calc
    p.domainArea U W = ∑' i, p.domainArea U (A i) := by
      rw [← hcover, measure_iUnion hdis hA]
    _ = ∑' i, p.domainArea V (f '' A i) := by
      congr 1
      funext i
      exact hlocal i
    _ = p.domainArea V (f '' W) := by
      rw [← measure_iUnion hdisImage hfiA, hcoverImage]

end AreaDeficit.Surfaces.DiscCover
