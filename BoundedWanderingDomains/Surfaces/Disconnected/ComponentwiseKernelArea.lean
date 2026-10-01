module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseAreaSubtype

@[expose] public section

/-! # Finite-model limits on one component of a disconnected manifold -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem domainArea_le_of_finite_model_bounds_in_component (p : ComponentwiseDiscCover X)
    {A : Set X} (hA : IsClosed A) (P : ℕ → Finset X) (hP : Monotone P)
    (hPA : ∀ n, (P n : Set X) ⊆ A)
    (hclosure : closure (⋃ n, (P n : Set X)) = A)
    {B : Set X} (hB : MeasurableSet B) (hBA : B ⊆ Aᶜ)
    (c : ConnectedComponents X) (hBc : B ⊆ ambientComponent c)
    {H : ℝ≥0∞} (hbound : ∀ n, p.domainArea (finitePunctureDomain (P n)) B ≤ H) :
    p.domainArea ⟨Aᶜ, hA.isOpen_compl⟩ B ≤ H := by
  have hcl : closure (⋃ n, (componentPunctures c (P n) : Set (ambientComponent c))) =
      (Subtype.val : ambientComponent c → X) ⁻¹' A := by
    have he : (⋃ n, (componentPunctures c (P n) : Set (ambientComponent c))) =
        Subtype.val ⁻¹' (⋃ n, (P n : Set X)) := by ext x; simp
    have hop : IsOpenMap (Subtype.val : ambientComponent c → X) :=
      (ambientComponent c).isOpen.isOpenMap_subtype_val
    rw [he, ← hop.preimage_closure_eq_closure_preimage continuous_subtype_val, hclosure]
  rw [p.domainArea_apply_of_subset_component _ c hB hBc]
  apply (p.cover c).domainArea_le_of_finite_model_bounds
    (hA.preimage continuous_subtype_val) (fun n => componentPunctures c (P n))
    ((componentPunctures_mono c).comp hP) (fun n x hx => hPA n (by simpa using hx)) hcl
    (hB.preimage continuous_subtype_val.measurable) (fun x hx => hBA hx)
  intro n
  have hn := hbound n
  rwa [p.domainArea_apply_of_subset_component _ c hB hBc, componentPart_finitePunctureDomain] at hn

end AreaDeficit.Surfaces.ComponentwiseDiscCover
