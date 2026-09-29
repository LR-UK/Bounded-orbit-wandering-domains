module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CountableCrossAmbientArea

@[expose] public section

/-! # A uniform area budget across countably many visited restrictions -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ENNReal

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem exists_uniform_countable_restricted_area_advance
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
      ∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) →
      Pairwise (Disjoint on A) → (∀ n, A n ⊆ V n) →
      InjOn f.totalize (⋃ n, A n) →
      (∀ n, f.totalize '' A n ⊆ L (label n)) →
      (∀ n x, x ∈ A n → f.totalize x ∉ P ∧ f.totalize x ∉ E) →
      p.domainArea (finitePunctureDomain P) (⋃ n, A n) ≤
        p.domainArea (finitePunctureDomain P) (f.totalize '' (⋃ n, A n)) + C := by
  classical
  obtain ⟨C, hC, hstep⟩ := f.exists_uniform_countable_cross_ambient_area_advance
    hf p (fun _ : ι => p) (fun _ => id) (fun _ => IsOpenEmbedding.id)
    (fun _ => mdifferentiable_id) D E L hL hLD
  refine ⟨C, hC, ?_⟩
  intro V hV label hreg P hforward A hA hdis hAV hinj himage havoid
  exact hstep V hV label hreg P
    (fun x hx => Finset.mem_union_left _ (hforward x hx))
    A hA hdis hAV hinj (by simpa only [image_id] using himage) havoid

end SurfaceDynamics.LocalMap

