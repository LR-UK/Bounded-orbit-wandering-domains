/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DenseFinitePunctures
import BoundedWanderingDomains.Surfaces.LocalPunctures

/-! # Backward-invariant finite-puncture barriers on analytic surfaces -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- A closed set outside a compact working domain can be exhausted by finite
roots and pulled backwards to an increasing finite barrier.  The resulting
closed barrier is locally backward invariant.  It also avoids every open
forward-invariant set trapped in the working domain. -/
theorem exists_finitePuncture_barrier {f : X → X} {V K A O : Set X}
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hA : IsClosed A)
    (hAV : Disjoint A V) (hopen : IsOpenMap f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hO : IsOpen O) (hOV : O ⊆ V) (hfO : MapsTo f O O) :
    ∃ P : ℕ → Set X,
      Monotone P ∧
      (∀ n, (P n).Finite) ∧
      A ⊆ closure (⋃ n, P n) ∧
      V ∩ f ⁻¹' closure (⋃ n, P n) ⊆ closure (⋃ n, P n) ∧
      Disjoint (closure (⋃ n, P n)) O := by
  classical
  obtain ⟨Q, hQmono, hQA, hQclosure⟩ :=
    AreaDeficit.Surfaces.closed_set_dense_finite_exhaustion hA
  let R : ℕ → Set X := fun n => (Q n : Set X)
  let P : ℕ → Set X := fun n => AreaDeficit.localPunctures f V R n
  have hRmono : Monotone R := fun _ _ hnm => by
    exact_mod_cast hQmono hnm
  have hRfinite : ∀ n, (R n).Finite := fun n => (Q n).finite_toSet
  have hRV : ∀ n, Disjoint (R n) V := by
    intro n
    exact Set.disjoint_left.mpr fun x hxR hxV =>
      Set.disjoint_left.mp hAV (hQA n hxR) hxV
  have hPmono : Monotone P := AreaDeficit.localPunctures_mono hRmono
  have hPfinite : ∀ n, (P n).Finite :=
    localPunctures_finite hVK hK hopen hf hRfinite
  have hAP : A ⊆ closure (⋃ n, P n) := by
    rw [← hQclosure]
    apply closure_mono
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n,
      AreaDeficit.roots_subset_backwardTree f V (R n) n hxn⟩
  have hback : V ∩ f ⁻¹' closure (⋃ n, P n) ⊆ closure (⋃ n, P n) := by
    apply AreaDeficit.closure_locally_backward_invariant
      (hV := hV)
    · intro U hUV hU
      exact hopen U hU
    · exact AreaDeficit.localPunctures_union_backward_invariant hRmono
  have hPO : (⋃ n, P n) ⊆ Oᶜ := by
    intro x hxP hxO
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxP
    exact AreaDeficit.trapped_not_mem_backwardTree (hRV n)
      (fun k => hOV (hfO.iterate k hxO)) n hxn
  have hdisj : Disjoint (closure (⋃ n, P n)) O := by
    exact Set.disjoint_left.mpr fun x hx hxO =>
      (closure_minimal hPO hO.isClosed_compl hx) hxO
  exact ⟨P, hPmono, hPfinite, hAP, hback, hdisj⟩

end SurfaceDynamics

#print axioms SurfaceDynamics.exists_finitePuncture_barrier
