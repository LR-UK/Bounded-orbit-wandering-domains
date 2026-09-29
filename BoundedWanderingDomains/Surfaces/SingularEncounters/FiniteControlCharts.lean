module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.LocalFiniteEncounters
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ComponentControl

@[expose] public section

/-! # Coordinate discs adapted to finite component obstructions -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

/-- A compact inner neighborhood and a coordinate disc, chosen so that the
finite exceptional values meet the closed disc only at its center. -/
theorem exists_component_control_chart
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (c : ℕ → f.source) {x : X}
    (hx : f.LocallyFiniteComponentEncounters hf.2.continuous c x) :
    ∃ (D : TopologicalSpace.Opens X) (Q : RiemannDynamics.CoordDisk X)
      (L : Set X) (E : Finset X) (N : ℕ),
      IsConnected (D : Set X) ∧ Q.center = x ∧ IsCompact L ∧ x ∈ interior L ∧
      L ⊆ range Q.param ∧ Q.closedCarrier ⊆ D ∧
      (∀ y ∈ Q.closedCarrier, y ∈ E → y = Q.center) ∧
      ∀ n, N ≤ n → f.map (c n) ∈ L →
        f.componentSingularValues hf.2.continuous D (c n) ⊆ (E : Set X) := by
  classical
  obtain ⟨D, B, hD, hxB, hBD, E, N, hcontrol⟩ := hx
  have hclosed : IsClosed ((E : Set X) \ {x}) := E.finite_toSet.sdiff.isClosed
  obtain ⟨Q, hQ, hQsub⟩ := exists_coordDisk_center_closedCarrier_subset
    (B.isOpen.sdiff hclosed) (show x ∈ (B : Set X) \ ((E : Set X) \ {x}) by simp [hxB])
  have hxQ : x ∈ range Q.param := ⟨discZero, Q.param_zero.trans hQ⟩
  obtain ⟨L, hL, hxL, hLQ⟩ := exists_compact_between isCompact_singleton
    Q.isOpenEmbedding_param.isOpen_range (singleton_subset_iff.mpr hxQ)
  refine ⟨D, Q, L, E, N, hD, hQ, hL, hxL (mem_singleton x), hLQ, ?_, ?_, ?_⟩
  · exact fun y hy => hBD (hQsub hy).1
  · intro y hy hyE
    have hyx : y = x := by
      by_contra hn
      exact (hQsub hy).2 ⟨hyE, hn⟩
    exact hyx.trans hQ.symm
  · intro n hn hnL
    obtain ⟨w, hw⟩ := hLQ hnL
    apply hcontrol n hn
    exact (hQsub (hw ▸ Q.param_mem_closedCarrier w)).1

theorem hasComponentPuncturedDisc_of_inverse_component_control
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (D : TopologicalSpace.Opens X) (hD : IsConnected (D : Set X))
    (Q : RiemannDynamics.CoordDisk X) (hQD : Q.closedCarrier ⊆ D)
    (E H : Finset X) (hEH : E ⊆ H) (hcenter : Q.center ∈ H)
    (hQE : ∀ y ∈ Q.closedCarrier, y ∈ E → y = Q.center)
    (a : f.source) (haD : f.map a ∈ D) (haE : f.map a ∉ E)
    (hobs : f.componentSingularValues hf.2.continuous D a ⊆ (E : Set X))
    {A : Set X} (hA : IsPreconnected A) (hAs : A ⊆ f.source) (haA : (a : X) ∈ A)
    (himage : MapsTo f.totalize A (range Q.param \ (H : Set X))) :
    f.HasComponentPuncturedDisc (H : Set X) A ∧
      A ⊆ f.inverseComponentSource hf.2.continuous D a ∧
      range Q.param \ (H : Set X) ⊆ (f.inverseComponentMap hf.2.continuous D a).regularValues := by
  classical
  let V := f.inverseComponentSource hf.2.continuous D a
  have hreg := f.inverseComponent_regularValues_of_finite_obstructions hf D hD
    E.finite_toSet a haD haE hobs
  have hAV : A ⊆ V := by
    apply f.subset_inverseComponentSource_of_preconnected hf.2.continuous D a hA hAs haA
    intro y hy
    obtain ⟨w, hw⟩ := (himage hy).1
    have heq : f.totalize y = f.map y := f.totalize_eq y.2
    exact heq ▸ hw ▸ hQD (Q.param_mem_closedCarrier w)
  have hpunct : ∀ w : BKL.puncturedUnitDisc,
      Q.param ⟨w, w.2.1⟩ ∈ (f.inverseComponentMap hf.2.continuous D a).regularValues := by
    intro w
    apply hreg
    refine ⟨hQD (Q.param_mem_closedCarrier _), ?_⟩
    intro hwE
    have heq := hQE _ (Q.param_mem_closedCarrier _) hwE
    have hw0 := Q.injective_param (heq.trans Q.param_zero.symm)
    exact w.2.2 (congrArg (Subtype.val : unitDisc → ℂ) hw0)
  refine ⟨⟨V, f.inverseComponentSource_subset _ D a, Q, hAV, ?_, hpunct, ?_⟩, hAV, ?_⟩
  · intro y hy
    obtain ⟨w, hw⟩ := (himage hy).1
    have hw0 : (w : ℂ) ≠ 0 := by
      intro hwzero
      have hwdisc : w = discZero := Subtype.ext hwzero
      exact (himage hy).2 (hw ▸ hwdisc ▸ Q.param_zero.symm ▸ hcenter)
    exact ⟨⟨w, w.2, hw0⟩, hw⟩
  · intro y hy
    have hyE : y ∈ E := by
      by_contra hn
      exact hy.1 (hreg ⟨hQD hy.2, hn⟩)
    exact hEH hyE
  · intro y hy
    obtain ⟨w, hw⟩ := hy.1
    exact hreg ⟨hw ▸ hQD (Q.param_mem_closedCarrier w), fun he => hy.2 (hEH he)⟩

end SurfaceDynamics.LocalMap
