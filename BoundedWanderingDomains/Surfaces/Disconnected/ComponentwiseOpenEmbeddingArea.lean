module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseCoveringArea
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseAreaGain
public import Mathlib.MeasureTheory.Measure.Comap

@[expose] public section

/-! # Intrinsic area is preserved by changing a disconnected ambient manifold -/

open Set Function MeasureTheory Topology
open scoped Manifold

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [T2Space M] [LocallyCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [T2Space N] [LocallyCompactSpace N]

theorem domainArea_image_openEmbedding
    (p : ComponentwiseDiscCover M) (q : ComponentwiseDiscCover N) (j : M → N)
    (hj : IsOpenEmbedding j) (hjh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j)
    (U : TopologicalSpace.Opens M) {W : Set M}
    (hW : MeasurableSet W) (hWU : W ⊆ U) :
    p.domainArea U W =
      q.domainArea ⟨j '' (U : Set M), hj.isOpenMap _ U.isOpen⟩ (j '' W) := by
  let V : TopologicalSpace.Opens N := ⟨j '' (U : Set M), hj.isOpenMap _ U.isOpen⟩
  let e : U ≃ₜ V := hj.isEmbedding.homeomorphImage (U : Set M)
  have heh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e := by
    apply (mdifferentiable_subtypeVal_comp_iff V e).mp
    exact hjh.comp (mdifferentiable_subtype_val U)
  have hec : IsCoveringMap e := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    apply e.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    · intro y _
      exact Set.Subsingleton.finite (fun a ha b hb => e.injective (ha.trans hb.symm))
    · exact e.isLocalHomeomorph.isLocalHomeomorphOn
  exact p.domainArea_eq_image_of_openDomain_covering_between q U V e heh hec rfl
    hW hWU hj.injective.injOn

theorem domainArea_le_add_comap_gain
    (p : ComponentwiseDiscCover M) (q : ComponentwiseDiscCover N) (j : M → N)
    (hj : IsOpenEmbedding j) (hjh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j)
    (U V : TopologicalSpace.Opens M) {W : Set M}
    (hW : MeasurableSet W) (hWU : W ⊆ U) (hWV : W ⊆ V) :
    p.domainArea V W ≤ p.domainArea U W +
      (q.domainAreaGain
        ⟨j '' (U : Set M), hj.isOpenMap _ U.isOpen⟩
        ⟨j '' (V : Set M), hj.isOpenMap _ V.isOpen⟩).comap j W := by
  have him : ∀ S : Set M, MeasurableSet S → MeasurableSet (j '' S) :=
    fun _ hS => hj.measurableEmbedding.measurableSet_image.mpr hS
  rw [p.domainArea_image_openEmbedding q j hj hjh U hW hWU,
    p.domainArea_image_openEmbedding q j hj hjh V hW hWV,
    Measure.comap_apply j hj.injective him _ hW]
  exact q.domainArea_le_add_gain _ _ (him W hW)

end AreaDeficit.Surfaces.ComponentwiseDiscCover
