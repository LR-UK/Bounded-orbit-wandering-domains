module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.GeneralCoveringAreaTransport

@[expose] public section

/-! # Intrinsic area transport for an entire covering -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold

namespace AreaDeficit.Surfaces.DiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M] [LocallyCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [T2Space N] [LocallyCompactSpace N]

theorem hyperbolicArea_eq_image_of_covering (p : DiscCover M) (q : DiscCover N)
    (f : M → N) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hc : IsCoveringMap f)
    {A : Set M} (hA : MeasurableSet A) (hinj : InjOn f A) :
    p.hyperbolicArea A = q.hyperbolicArea (f '' A) := by
  let F : (⊤ : Opens M) → (⊤ : Opens N) := fun x => ⟨f x, mem_univ _⟩
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    apply (mdifferentiable_subtypeVal_comp_iff (⊤ : Opens N) F).mp
    exact hf.comp (mdifferentiable_subtype_val ⊤)
  have hFc : IsCoveringMap F :=
    (hc.comp_homeomorph (Homeomorph.Set.univ M)).homeomorph_comp (Homeomorph.Set.univ N).symm
  simpa only [domainArea_top] using p.domainArea_eq_image_of_openDomain_covering_between
    q ⊤ ⊤ F hF hFc rfl hf.continuous.measurable hA (subset_univ _) hinj

end AreaDeficit.Surfaces.DiscCover
