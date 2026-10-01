module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.FiniteAreaPunctures
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseArea

@[expose] public section

/-! # Finite punctures preserve finite area componentwise -/

open Set Function MeasureTheory TopologicalSpace Topology
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem finitePunctureDomain_area_finite_of_hyperbolicArea_finite
    (p : ComponentwiseDiscCover X) (P : Finset X) {A : Set X}
    (hA : MeasurableSet A) (hp : p.hyperbolicArea A < ⊤) :
    p.domainArea (finitePunctureDomain P) A < ⊤ := by
  classical
  let localCompactComponents : ∀ c : ConnectedComponents X, LocallyCompactSpace (ambientComponent c) :=
    fun c => (ambientComponent c).isOpen.locallyCompactSpace
  let I := P.image ConnectedComponents.mk
  let μ := fun c : ConnectedComponents X =>
    (p.cover c).domainArea (finitePunctureDomain (componentPunctures c P)) (Subtype.val ⁻¹' A)
  let ν := fun c : ConnectedComponents X =>
    (p.cover c).hyperbolicArea (Subtype.val ⁻¹' A)
  have hsumν : ∑' c, ν c = p.hyperbolicArea A := by
    rw [hyperbolicArea, p.domainArea_apply _ hA]
    simp only [componentPart_top, DiscCover.domainArea_top, ν]
  have hν : ∀ c, ν c < ⊤ := fun c =>
    (ENNReal.le_tsum (f := ν) c).trans_lt (hsumν.symm ▸ hp)
  have hμ : ∀ c, μ c < ⊤ := fun c =>
    (p.cover c).finitePunctureDomain_area_finite_of_hyperbolicArea_finite (componentPunctures c P)
      (hA.preimage continuous_subtype_val.measurable) (hν c)
  have he : ∀ c ∉ I, μ c = ν c := by
    intro c hc
    have hPc : componentPunctures c P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hc (Finset.mem_image.mpr ⟨x, (mem_componentPunctures c P x).mp hx, x.property⟩)
    have ht : finitePunctureDomain (∅ : Finset (ambientComponent c)) = ⊤ := by
      ext x; simp [finitePunctureDomain]
    simp only [μ, hPc, ht, DiscCover.domainArea_top, ν]
  have hb : ∀ c, μ c ≤ (if c ∈ I then μ c else 0) + ν c := by
    intro c
    by_cases hc : c ∈ I
    · simp only [ite_eq_left hc]; exact le_add_right le_rfl
    · simp only [ite_eq_right hc, zero_add, he c hc, le_refl]
  have hsum : (∑' c, if c ∈ I then μ c else 0) = ∑ c ∈ I, μ c := by
    rw [tsum_eq_sum (s := I) (fun c hc => ite_eq_right hc)]
    exact Finset.sum_congr rfl (fun c hc => ite_eq_left hc)
  rw [p.domainArea_apply _ hA]
  simp only [componentPart_finitePunctureDomain]
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hb)
  rw [ENNReal.tsum_add, hsum, hsumν]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr (fun c _ => hμ c), hp⟩

end AreaDeficit.Surfaces.ComponentwiseDiscCover
