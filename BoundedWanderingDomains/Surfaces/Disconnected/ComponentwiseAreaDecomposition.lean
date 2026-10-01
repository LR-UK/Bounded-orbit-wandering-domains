module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseAreaSubtype
public import BoundedWanderingDomains.Surfaces.Disconnected.OpenComponents

@[expose] public section

/-! # Summing intrinsic areas of the connected components of an open domain -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X]

omit [LocallyCompactSpace X] in
theorem domainArea_domainComponent (p : ComponentwiseDiscCover X) (U : Opens X)
    (c : ConnectedComponents U) {A : Set X} (hA : MeasurableSet A)
    (hAC : A ⊆ domainComponent U c) :
    p.domainArea U A = p.domainArea (domainComponent U c) A := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [domainComponent_mk] at hAC ⊢
  exact p.domainArea_component U x hA hAC

theorem domainArea_eq_tsum_intrinsic_components (p : ComponentwiseDiscCover X) (U : Opens X)
    (q : ∀ c : ConnectedComponents U, DiscCover (domainComponent U c))
    {A : Set X} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    p.domainArea U A = ∑' c : ConnectedComponents U,
      (q c).hyperbolicArea (Subtype.val ⁻¹' A) := by
  let : Countable (ConnectedComponents U) := countable_ambient_components
  let B : ConnectedComponents U → Set X := fun c => A ∩ domainComponent U c
  have hB : ∀ c, MeasurableSet (B c) := fun c =>
    hA.inter (domainComponent U c).isOpen.measurableSet
  have hdis : Pairwise (Disjoint on B) :=
    pairwise_disjoint_mono (domainComponent_pairwise_disjoint U) (fun _ => inter_subset_right)
  have hcover : (⋃ c, B c) = A := by
    dsimp only [B]
    rw [← inter_iUnion, iUnion_domainComponent, inter_eq_left.mpr hAU]
  rw [← hcover, measure_iUnion hdis hB, hcover]
  apply tsum_congr
  intro c
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  have hC : domainComponent U c = componentDomain U (x : X) := by
    rw [← hx, domainComponent_mk]
  have he := p.domainArea_component U x (hB c)
    (show B c ⊆ componentDomain U (x : X) from hC ▸ inter_subset_right)
  rw [← hC] at he
  rw [he, p.domainArea_eq_hyperbolicArea_preimage_connected (domainComponent U c) (q c)
    (hB c) inter_subset_right]
  congr 1
  ext y
  exact and_iff_left y.property

end AreaDeficit.Surfaces.ComponentwiseDiscCover
