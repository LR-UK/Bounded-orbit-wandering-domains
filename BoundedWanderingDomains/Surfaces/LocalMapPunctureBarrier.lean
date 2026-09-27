/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.ExhaustivePunctureBarrier
import BoundedWanderingDomains.Surfaces.LocalDynamics

/-! # Finite puncture barriers for a map with open source -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics
namespace LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Exhaustive backward tree for a map whose source is an open subtype. -/
def sourceExhaustiveBackwardTree (f : LocalMap X)
    (K : ℕ → Set f.source) (Q : ℕ → Set X) : ℕ → Set X
  | 0 => Q 0
  | n + 1 => sourceExhaustiveBackwardTree f K Q n ∪ Q (n + 1) ∪
      Subtype.val '' (K (n + 1) ∩ f.map ⁻¹' sourceExhaustiveBackwardTree f K Q n)

theorem sourceExhaustiveBackwardTree_mono (f : LocalMap X)
    (K : ℕ → Set f.source) (Q : ℕ → Set X) :
    Monotone (sourceExhaustiveBackwardTree f K Q) :=
  monotone_nat_of_le_succ fun _ => subset_union_left.trans subset_union_left

theorem roots_subset_sourceExhaustiveBackwardTree (f : LocalMap X)
    {K : ℕ → Set f.source} {Q : ℕ → Set X} (n : ℕ) :
    Q n ⊆ sourceExhaustiveBackwardTree f K Q n := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact fun _ hx => Or.inl (Or.inr hx)

theorem sourceExhaustiveBackwardTree_finite (f : LocalMap X)
    (hf : IsOpenHolomorphic f) {K : ℕ → Set f.source}
    {Q : ℕ → Set X} (hK : ∀ n, IsCompact (K n))
    (hQ : ∀ n, (Q n).Finite) (n : ℕ) :
    (sourceExhaustiveBackwardTree f K Q n).Finite := by
  induction n with
  | zero => exact hQ 0
  | succ n ih =>
      have hpre : (K (n + 1) ∩
          f.map ⁻¹' sourceExhaustiveBackwardTree f K Q n).Finite :=
        finite_compact_inter_preimage_of_finite hf.1 hf.2 (hK (n + 1)) ih
      exact (ih.union (hQ (n + 1))).union
        (hpre.image (fun x : f.source => (x : X)))

theorem sourceExhaustiveBackwardTree_union_backward (f : LocalMap X)
    {K : ℕ → Set f.source} {Q : ℕ → Set X}
    (hKmono : Monotone K) (hKcover : (⋃ n, K n) = univ) :
    ∀ x : f.source, f.map x ∈
        (⋃ n, sourceExhaustiveBackwardTree f K Q n) →
      (x : X) ∈ (⋃ n, sourceExhaustiveBackwardTree f K Q n) := by
  intro x hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  obtain ⟨r, hr⟩ : ∃ r, x ∈ K r := by
    apply mem_iUnion.mp
    rw [hKcover]
    exact mem_univ x
  let n := max m r
  have hmn : sourceExhaustiveBackwardTree f K Q m ⊆
      sourceExhaustiveBackwardTree f K Q n :=
    sourceExhaustiveBackwardTree_mono f K Q (le_max_left _ _)
  have hrn : x ∈ K (n + 1) :=
    hKmono ((le_max_right m r).trans (Nat.le_succ n)) hr
  exact mem_iUnion.mpr ⟨n + 1, Or.inr
    ⟨x, ⟨hrn, hmn hm⟩, rfl⟩⟩

/-- Openness promotes backward invariance of a set to backward invariance of
its closure, for a map with open source. -/
theorem closure_source_backward_invariant (f : LocalMap X)
    (hopen : IsOpenMap f.map) {P : Set X}
    (hback : ∀ x : f.source, f.map x ∈ P → (x : X) ∈ P) :
    ∀ x : f.source, f.map x ∈ closure P → (x : X) ∈ closure P := by
  intro x hx
  apply mem_closure_iff.mpr
  intro U hU hxU
  let W : Set f.source := Subtype.val ⁻¹' (U ∩ (f.source : Set X))
  have hWopen : IsOpen W :=
    (hU.inter f.source.isOpen).preimage continuous_subtype_val
  have himage : IsOpen (f.map '' W) := hopen W hWopen
  have hfx : f.map x ∈ f.map '' W :=
    ⟨x, ⟨hxU, x.property⟩, rfl⟩
  obtain ⟨y, ⟨z, hzW, rfl⟩, hyP⟩ :=
    mem_closure_iff.mp hx _ himage hfx
  exact ⟨(z : X), hzW.1, hback z hyP⟩

theorem sourceExhaustiveBackwardTree_disjoint_forwardInvariant
    (f : LocalMap X) {K : ℕ → Set f.source} {Q : ℕ → Set X}
    {O : Set X} (hQO : ∀ n, Disjoint (Q n) O) (hO : IsOpen O)
    (hOsource : O ⊆ f.source)
    (hfO : ∀ x (hx : x ∈ O), f.map ⟨x, hOsource hx⟩ ∈ O) :
    Disjoint (closure (⋃ n, sourceExhaustiveBackwardTree f K Q n)) O := by
  have hstage : ∀ n, Disjoint (sourceExhaustiveBackwardTree f K Q n) O := by
    intro n
    induction n with
    | zero => exact hQO 0
    | succ n ih =>
        apply Set.disjoint_left.mpr
        rintro x ((hx | hx) | ⟨z, hz, rfl⟩) hxO
        · exact Set.disjoint_left.mp ih hx hxO
        · exact Set.disjoint_left.mp (hQO (n + 1)) hx hxO
        · exact Set.disjoint_left.mp ih hz.2 (hfO z hxO)
  have hunion : (⋃ n, sourceExhaustiveBackwardTree f K Q n) ⊆ Oᶜ := by
    intro x hx hxO
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hstage n) hxn hxO
  exact Set.disjoint_left.mpr fun x hx hxO =>
    (closure_minimal hunion hO.isClosed_compl hx) hxO

/-- Global finite barrier for the actual open-source local map. -/
theorem exists_source_finitePuncture_barrier (f : LocalMap X)
    (hf : IsOpenHolomorphic f) {A O : Set X} (hA : IsClosed A)
    (hAO : Disjoint A O) (hO : IsOpen O) (hOsource : O ⊆ f.source)
    (hfO : ∀ x (hx : x ∈ O), f.map ⟨x, hOsource hx⟩ ∈ O) :
    ∃ P : ℕ → Set X, Monotone P ∧ (∀ n, (P n).Finite) ∧
      A ⊆ closure (⋃ n, P n) ∧
      (∀ x : f.source, f.map x ∈ closure (⋃ n, P n) →
        (x : X) ∈ closure (⋃ n, P n)) ∧
      Disjoint (closure (⋃ n, P n)) O := by
  classical
  letI : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  obtain ⟨Q, _, hQA, hQclosure⟩ :=
    AreaDeficit.Surfaces.closed_set_dense_finite_exhaustion hA
  let R : ℕ → Set X := fun n => (Q n : Set X)
  let K : CompactExhaustion f.source := CompactExhaustion.choice f.source
  let P : ℕ → Set X := f.sourceExhaustiveBackwardTree K R
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
      f.roots_subset_sourceExhaustiveBackwardTree n hxn⟩
  have hunionback := f.sourceExhaustiveBackwardTree_union_backward
    (K := K) (Q := R) (OrderHomClass.mono K) K.iUnion_eq
  exact ⟨P, f.sourceExhaustiveBackwardTree_mono K R,
    f.sourceExhaustiveBackwardTree_finite hf K.isCompact hRfinite,
    hAP, f.closure_source_backward_invariant hf.1 hunionback,
    f.sourceExhaustiveBackwardTree_disjoint_forwardInvariant
      hRO hO hOsource hfO⟩

end LocalMap
end SurfaceDynamics
