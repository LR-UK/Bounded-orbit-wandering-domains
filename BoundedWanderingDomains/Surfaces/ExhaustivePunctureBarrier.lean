/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DenseFinitePunctures
import BoundedWanderingDomains.Surfaces.LocalPunctures
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Globally exhaustive finite backward-puncture barriers -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics

/-- At stage `n + 1`, pull the previous finite barrier back only inside the
`n + 1`-st compact exhaustion set.  Every point is eventually inspected, so
the union is globally backward invariant while every stage remains finite. -/
def exhaustiveBackwardTree {X : Type*} (f : X → X) (K Q : ℕ → Set X) :
    ℕ → Set X
  | 0 => Q 0
  | n + 1 => exhaustiveBackwardTree f K Q n ∪ Q (n + 1) ∪
      (K (n + 1) ∩ f ⁻¹' exhaustiveBackwardTree f K Q n)

theorem exhaustiveBackwardTree_mono {X : Type*} (f : X → X)
    (K Q : ℕ → Set X) : Monotone (exhaustiveBackwardTree f K Q) :=
  monotone_nat_of_le_succ fun _ => subset_union_left.trans subset_union_left

theorem roots_subset_exhaustiveBackwardTree {X : Type*} {f : X → X}
    {K Q : ℕ → Set X} (n : ℕ) :
    Q n ⊆ exhaustiveBackwardTree f K Q n := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
      intro x hx
      exact Or.inl (Or.inr hx)

theorem exhaustiveBackwardTree_finite {X : Type*} [TopologicalSpace X]
    [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {f : X → X} (hopen : IsOpenMap f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {K Q : ℕ → Set X} (hK : ∀ n, IsCompact (K n))
    (hQ : ∀ n, (Q n).Finite) (n : ℕ) :
    (exhaustiveBackwardTree f K Q n).Finite := by
  induction n with
  | zero => exact hQ 0
  | succ n ih =>
      exact (ih.union (hQ (n + 1))).union
        (finite_compact_inter_preimage_of_finite hopen hf (hK (n + 1)) ih)

theorem exhaustiveBackwardTree_union_backward {X : Type*} {f : X → X}
    {K Q : ℕ → Set X} (hKmono : Monotone K)
    (hKcover : (⋃ n, K n) = (univ : Set X)) :
    f ⁻¹' (⋃ n, exhaustiveBackwardTree f K Q n) ⊆
      ⋃ n, exhaustiveBackwardTree f K Q n := by
  intro x hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  obtain ⟨r, hr⟩ : ∃ r, x ∈ K r := by
    apply mem_iUnion.mp
    rw [hKcover]
    exact mem_univ x
  let n := max m r
  have hmn : exhaustiveBackwardTree f K Q m ⊆
      exhaustiveBackwardTree f K Q n :=
    exhaustiveBackwardTree_mono f K Q (le_max_left _ _)
  have hrn : x ∈ K (n + 1) :=
    hKmono ((le_max_right m r).trans (Nat.le_succ n)) hr
  exact mem_iUnion.mpr ⟨n + 1, Or.inr ⟨hrn, hmn hm⟩⟩

theorem exhaustiveBackwardTree_disjoint_forwardInvariant {X : Type*}
    [TopologicalSpace X] {f : X → X} {K Q : ℕ → Set X} {O : Set X}
    (hQO : ∀ n, Disjoint (Q n) O) (hO : IsOpen O)
    (hfO : MapsTo f O O) :
    Disjoint (closure (⋃ n, exhaustiveBackwardTree f K Q n)) O := by
  have hstage : ∀ n, Disjoint (exhaustiveBackwardTree f K Q n) O := by
    intro n
    induction n with
    | zero => exact hQO 0
    | succ n ih =>
        apply Set.disjoint_left.mpr
        rintro x ((hx | hx) | hx) hxO
        · exact Set.disjoint_left.mp ih hx hxO
        · exact Set.disjoint_left.mp (hQO (n + 1)) hx hxO
        · exact Set.disjoint_left.mp ih hx.2 (hfO hxO)
  have hunion : (⋃ n, exhaustiveBackwardTree f K Q n) ⊆ Oᶜ := by
    intro x hx hxO
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hstage n) hxn hxO
  exact Set.disjoint_left.mpr fun x hx hxO =>
    (closure_minimal hunion hO.isClosed_compl hx) hxO

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Every closed set disjoint from an open forward-invariant set admits an
increasing finite, globally backward-invariant puncture barrier whose closure
contains the closed set and still avoids the invariant open set. -/
theorem exists_exhaustive_finitePuncture_barrier {f : X → X} {A O : Set X}
    (hA : IsClosed A) (hAO : Disjoint A O) (hO : IsOpen O)
    (hfO : MapsTo f O O) (hopen : IsOpenMap f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ P : ℕ → Set X, Monotone P ∧ (∀ n, (P n).Finite) ∧
      A ⊆ closure (⋃ n, P n) ∧
      f ⁻¹' closure (⋃ n, P n) ⊆ closure (⋃ n, P n) ∧
      Disjoint (closure (⋃ n, P n)) O := by
  classical
  obtain ⟨Q, _, hQA, hQclosure⟩ :=
    AreaDeficit.Surfaces.closed_set_dense_finite_exhaustion hA
  let R : ℕ → Set X := fun n => (Q n : Set X)
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let P : ℕ → Set X := exhaustiveBackwardTree f K R
  have hRfinite : ∀ n, (R n).Finite := fun n => (Q n).finite_toSet
  have hRO : ∀ n, Disjoint (R n) O := fun n =>
    Set.disjoint_left.mpr fun x hxR hxO =>
      Set.disjoint_left.mp hAO (hQA n hxR) hxO
  have hAP : A ⊆ closure (⋃ n, P n) := by
    rw [← hQclosure]
    apply closure_mono
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n,
      roots_subset_exhaustiveBackwardTree n hxn⟩
  have hunionback : f ⁻¹' (⋃ n, P n) ⊆ ⋃ n, P n :=
    exhaustiveBackwardTree_union_backward (OrderHomClass.mono K) K.iUnion_eq
  have hclosedback : f ⁻¹' closure (⋃ n, P n) ⊆
      closure (⋃ n, P n) := by
    have hh := AreaDeficit.closure_locally_backward_invariant
      (f := f) (V := univ) (P := ⋃ n, P n) isOpen_univ
      (fun U _ hU => hopen U hU)
      (by simpa only [univ_inter] using hunionback)
    simpa only [univ_inter] using hh
  exact ⟨P, exhaustiveBackwardTree_mono f K R,
    exhaustiveBackwardTree_finite hopen hf K.isCompact hRfinite,
    hAP, hclosedback,
    exhaustiveBackwardTree_disjoint_forwardInvariant hRO hO hfO⟩

end SurfaceDynamics
