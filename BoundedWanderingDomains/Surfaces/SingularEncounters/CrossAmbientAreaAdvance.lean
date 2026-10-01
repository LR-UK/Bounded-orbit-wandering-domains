module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseOpenEmbeddingArea
public import BoundedWanderingDomains.Surfaces.RegularCoveringArea
public import BoundedWanderingDomains.Surfaces.LocalMapRestriction

@[expose] public section

/-! # Local area advance with a target budget in a larger ambient surface -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold ENNReal

namespace SurfaceDynamics.LocalMap

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M] [LocallyCompactSpace M] [DecidableEq M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [T2Space N] [LocallyCompactSpace N]

theorem restricted_area_le_add_cross_ambient_gain
    (f : LocalMap M) (hf : IsOpenHolomorphic f) (p : ComponentwiseDiscCover M) (q : ComponentwiseDiscCover N)
    (j : M → N) (hj : IsOpenEmbedding j) (hjh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j)
    (D : TopologicalSpace.Opens N) (E : Finset M)
    (V : TopologicalSpace.Opens M) (hV : (V : Set M) ⊆ f.source)
    (hreg : (j ⁻¹' (D : Set N)) \ (E : Set M) ⊆ (f.restrictSource V hV).regularValues)
    (P : Finset M)
    (hforward : ∀ x : f.source, (x : M) ∈ P → f.map x ∈ (P ∪ E : Finset M))
    {W : Set M} (hW : MeasurableSet W) (hWV : W ⊆ V) (hinj : InjOn f.totalize W)
    (himage : j '' (f.totalize '' W) ⊆ D)
    (havoid : ∀ x ∈ W, f.totalize x ∉ P ∧ f.totalize x ∉ E) :
    let U := finitePunctureDomain P
    let Y := finiteRemovalDomain U E ⊓
      (⟨j ⁻¹' (D : Set N), D.isOpen.preimage hj.continuous⟩ : TopologicalSpace.Opens M)
    p.domainArea U W ≤ p.domainArea U (f.totalize '' W) +
      (q.domainAreaGain
        ⟨j '' (U : Set M), hj.isOpenMap _ U.isOpen⟩
        ⟨j '' (Y : Set M), hj.isOpenMap _ Y.isOpen⟩).comap j (f.totalize '' W) := by
  let g := f.restrictSource V hV
  have hg := f.isOpenHolomorphic_restrictSource hf V hV
  let U := finitePunctureDomain P
  let Y := finiteRemovalDomain U E ⊓
    (⟨j ⁻¹' (D : Set N), D.isOpen.preimage hj.continuous⟩ : TopologicalSpace.Opens M)
  let T := g.regularCoverDomain Y hg.2.continuous
  have hY : (Y : Set M) ⊆ g.singularValuesᶜ := by
    intro x hx
    exact not_not.mpr (hreg ⟨hx.2, hx.1.2⟩)
  obtain ⟨F, hF, hcov, hFeq⟩ := g.exists_regular_domain_cover hg Y hY
  have hTU : T ≤ U := by
    rintro x ⟨w, hw, rfl⟩ hxP
    rcases Finset.mem_union.mp (hforward ⟨w, hV w.2⟩ hxP) with hh | hh
    · exact hw.1.1 hh
    · exact hw.1.2 hh
  have hWT : W ⊆ T := by
    intro x hx
    refine ⟨⟨x, hWV hx⟩, ?_, rfl⟩
    change f.map ⟨x, hV (hWV hx)⟩ ∈ Y
    rw [← f.totalize_eq (hV (hWV hx))]
    exact ⟨havoid x hx, himage ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩
  have hagrees : (fun x : T => f.totalize x) = fun x => (F x : M) := by
    funext x
    have hxV : (x : M) ∈ V := by
      obtain ⟨w, _, hw⟩ := x.2
      exact hw ▸ w.2
    exact (f.totalize_eq (hV hxV)).trans
      ((g.totalize_eq hxV).symm.trans (congrFun hFeq x))
  have him : MeasurableSet (f.totalize '' W) := by
    let : PolishSpace M := surfacePolishSpace
    exact hW.image_of_continuousOn_injOn
      ((f.continuousOn_totalize hf.2.continuous).mono (hWV.trans hV)) hinj
  have himY : f.totalize '' W ⊆ Y := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨havoid x hx, himage ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩
  calc
    p.domainArea U W ≤ p.domainArea T W := p.domainArea_mono_on hTU hW hWT
    _ = p.domainArea Y (f.totalize '' W) :=
      p.domainArea_eq_image_of_openDomain_covering_between p T Y F hF hcov hagrees hW hWT hinj
    _ ≤ _ := p.domainArea_le_add_comap_gain q j hj hjh U Y him
      (himY.trans (fun _ hx => hx.1.1)) himY

end SurfaceDynamics.LocalMap
