module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseArea
public import BoundedWanderingDomains.Surfaces.DomainAreaBlowup

@[expose] public section

/-! # The finite-model area contradiction on disconnected surfaces -/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem measure_zero_of_finite_model_area_bounds (p : ComponentwiseDiscCover X)
    (P : ℕ → Finset X) (hP : Monotone P) {A : Set X}
    (hA : MeasurableSet A) (hAP : A ⊆ closure (⋃ n, (P n : Set X)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, p.domainArea (finitePunctureDomain (P n)) A ≤ C) :
    p.hyperbolicArea A = 0 := by
  rw [hyperbolicArea, p.domainArea_apply _ hA]
  apply ENNReal.tsum_eq_zero.mpr
  intro c
  rw [componentPart_top, DiscCover.domainArea_top]
  have hAPc : (Subtype.val ⁻¹' A : Set (ambientComponent c)) ⊆
      closure (⋃ n, (componentPunctures c (P n) : Set (ambientComponent c))) := by
    have he : (⋃ n, (componentPunctures c (P n) : Set (ambientComponent c))) =
        Subtype.val ⁻¹' (⋃ n, (P n : Set X)) := by
      ext x
      simp
    have hop : IsOpenMap (Subtype.val : ambientComponent c → X) :=
      (ambientComponent c).isOpen.isOpenMap_subtype_val
    rw [he, ← hop.preimage_closure_eq_closure_preimage
      continuous_subtype_val (⋃ n, (P n : Set X))]
    exact fun _ hx => hAP hx
  apply (p.cover c).measure_zero_of_finite_model_area_bounds
    (fun n => componentPunctures c (P n)) ((componentPunctures_mono c).comp hP)
    (hA.preimage continuous_subtype_val.measurable) hAPc hC
  intro n
  apply le_trans _ (hbound n)
  rw [p.domainArea_apply _ hA]
  simpa only [componentPart_finitePunctureDomain] using
    (ENNReal.le_tsum (f := fun d : ConnectedComponents X =>
      (p.cover d).domainArea (componentPart d (finitePunctureDomain (P n)))
        (Subtype.val ⁻¹' A)) c :
      (p.cover c).domainArea (componentPart c (finitePunctureDomain (P n)))
        (Subtype.val ⁻¹' A) ≤
      ∑' d : ConnectedComponents X,
        (p.cover d).domainArea (componentPart d (finitePunctureDomain (P n)))
          (Subtype.val ⁻¹' A))

end AreaDeficit.Surfaces.ComponentwiseDiscCover
