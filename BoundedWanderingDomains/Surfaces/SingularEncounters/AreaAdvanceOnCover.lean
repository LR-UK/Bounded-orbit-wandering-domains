module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableCrossAmbientArea

@[expose] public section

/-! # Area advance for measurable sets covered by countably many restrictions -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ENNReal

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem exists_uniform_area_advance_on_countable_cover
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : DiscCover X)
    {ι : Type*} [Fintype ι] (D : ι → TopologicalSpace.Opens X) (E : Finset X)
    (L : ι → Set X) (hL : ∀ i, IsCompact (L i)) (hLD : ∀ i, L i ⊆ D i) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (V : ℕ → TopologicalSpace.Opens X) (hV : ∀ n, (V n : Set X) ⊆ f.source)
        (label : ℕ → ι),
      (∀ n, (D (label n) : Set X) \ (E : Set X) ⊆
        (f.restrictSource (V n) (hV n)).regularValues) →
      ∀ P : Finset X,
      (∀ x : f.source, (x : X) ∈ P → f.map x ∈ P) →
      ∀ W : Set X, MeasurableSet W → InjOn f.totalize W →
      W ⊆ ⋃ n, (V n : Set X) ∩ f.totalize ⁻¹' L (label n) →
      (∀ x ∈ W, f.totalize x ∉ P ∧ f.totalize x ∉ E) →
      p.domainArea (finitePunctureDomain P) W ≤
        p.domainArea (finitePunctureDomain P) (f.totalize '' W) + C := by
  classical
  obtain ⟨C, hC, hstep⟩ := f.exists_uniform_cross_ambient_area_advance_on_cover
    hf p (fun _ : ι => p) (fun _ => id) (fun _ => IsOpenEmbedding.id)
    (fun _ => mdifferentiable_id) D E L hL hLD
  refine ⟨C, hC, ?_⟩
  intro V hV label hreg P hforward W hW hinj hcover havoid
  exact hstep V hV label hreg P
    (fun x hx => Finset.mem_union_left _ (hforward x hx))
    W hW hinj hcover havoid

end SurfaceDynamics.LocalMap

