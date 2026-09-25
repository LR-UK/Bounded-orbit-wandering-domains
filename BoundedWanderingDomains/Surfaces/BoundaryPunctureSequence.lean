/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DenseFinitePunctures
import BoundedWanderingDomains.Surfaces.LocalPunctures
import BoundedWanderingDomains.Surfaces.LocalDynamics
import Mathlib.Topology.Separation.Regular

/-! # Finite backward punctures from the boundary of a working domain -/

open Set Function
open scoped Manifold Topology

namespace SurfaceDynamics
namespace LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Pull finite boundary roots backwards only while the preimage remains in
the chosen relatively compact working domain. -/
def boundaryBackwardTree (f : LocalMap X) (V : Set X)
    (hVsource : closure V ⊆ f.source) (Q : Set X) : ℕ → Set X
  | 0 => Q
  | n + 1 => boundaryBackwardTree f V hVsource Q n ∪
      {x | ∃ hx : x ∈ V,
        f.map ⟨x, hVsource (subset_closure hx)⟩ ∈
          boundaryBackwardTree f V hVsource Q n}

theorem boundaryBackwardTree_mono (f : LocalMap X) (V : Set X)
    (hVsource : closure V ⊆ f.source) (Q : Set X) :
    Monotone (f.boundaryBackwardTree V hVsource Q) :=
  monotone_nat_of_le_succ fun _ => subset_union_left

theorem roots_subset_boundaryBackwardTree (f : LocalMap X) (V : Set X)
    (hVsource : closure V ⊆ f.source) (Q : Set X) (n : ℕ) :
    Q ⊆ f.boundaryBackwardTree V hVsource Q n :=
  f.boundaryBackwardTree_mono V hVsource Q (Nat.zero_le n)

theorem boundaryBackwardTree_mono_roots (f : LocalMap X) {V Q R : Set X}
    (hVsource : closure V ⊆ f.source) (hQR : Q ⊆ R) (n : ℕ) :
    f.boundaryBackwardTree V hVsource Q n ⊆
      f.boundaryBackwardTree V hVsource R n := by
  induction n with
  | zero => exact hQR
  | succ n ih =>
      rintro x (hx | ⟨hxV, hfx⟩)
      · exact Or.inl (ih hx)
      · exact Or.inr ⟨hxV, ih hfx⟩

theorem finite_working_preimage (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {V S : Set X} (hVcompact : IsCompact (closure V))
    (hVsource : closure V ⊆ f.source) (hS : S.Finite) :
    {x | ∃ hx : x ∈ V,
      f.map ⟨x, hVsource (subset_closure hx)⟩ ∈ S}.Finite := by
  let C : Set f.source := Subtype.val ⁻¹' closure V
  have hC : IsCompact C := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    rw [image_preimage_eq_inter_range]
    convert hVcompact using 1
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨⟨x, hVsource hx⟩, rfl⟩
  have hpre : (C ∩ f.map ⁻¹' S).Finite :=
    finite_compact_inter_preimage_of_finite hf.1 hf.2 hC hS
  apply (hpre.image (fun x : f.source => (x : X))).subset
  rintro x ⟨hxV, hfx⟩
  exact ⟨⟨x, hVsource (subset_closure hxV)⟩,
    ⟨subset_closure hxV, hfx⟩, rfl⟩

theorem boundaryBackwardTree_finite (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {V Q : Set X} (hVcompact : IsCompact (closure V))
    (hVsource : closure V ⊆ f.source) (hQ : Q.Finite) (n : ℕ) :
    (f.boundaryBackwardTree V hVsource Q n).Finite := by
  induction n with
  | zero => exact hQ
  | succ n ih =>
      exact ih.union (f.finite_working_preimage hf hVcompact hVsource ih)

theorem boundaryBackwardTree_union_backward (f : LocalMap X)
    {V Q : Set X} (hVsource : closure V ⊆ f.source) :
    ∀ x (hx : x ∈ V),
      f.map ⟨x, hVsource (subset_closure hx)⟩ ∈
          (⋃ n, f.boundaryBackwardTree V hVsource Q n) →
        x ∈ (⋃ n, f.boundaryBackwardTree V hVsource Q n) := by
  intro x hx hfx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hfx
  exact mem_iUnion.mpr ⟨n + 1, Or.inr ⟨hx, hn⟩⟩

theorem boundaryBackwardTree_closure_backward (f : LocalMap X)
    (hopen : IsOpenMap f.map) {V Q : Set X} (hV : IsOpen V)
    (hVsource : closure V ⊆ f.source) :
    ∀ x (hx : x ∈ V),
      f.map ⟨x, hVsource (subset_closure hx)⟩ ∈
          closure (⋃ n, f.boundaryBackwardTree V hVsource Q n) →
        x ∈ closure (⋃ n, f.boundaryBackwardTree V hVsource Q n) := by
  have hback := f.boundaryBackwardTree_union_backward (Q := Q) hVsource
  intro x hxV hfx
  apply mem_closure_iff.mpr
  intro U hU hxU
  let W : Set f.source := Subtype.val ⁻¹' (U ∩ V)
  have hWopen : IsOpen W := (hU.inter hV).preimage continuous_subtype_val
  have himage : IsOpen (f.map '' W) := hopen W hWopen
  have hfxmem : f.map ⟨x, hVsource (subset_closure hxV)⟩ ∈ f.map '' W :=
    ⟨⟨x, hVsource (subset_closure hxV)⟩, ⟨hxU, hxV⟩, rfl⟩
  obtain ⟨y, ⟨z, hzW, rfl⟩, hyP⟩ :=
    mem_closure_iff.mp hfx _ himage hfxmem
  exact ⟨(z : X), hzW.1, hback z hzW.2 hyP⟩

/-- A compact subset of the source admits exactly the boundary-preimage
construction used in the paper. -/
theorem exists_boundaryPunctureSequence (f : LocalMap X)
    (hf : IsOpenHolomorphic f) {K : Set X} (hK : IsCompact K)
    (hKsource : K ⊆ f.source) :
    ∃ V : Set X, ∃ hVsource : closure V ⊆ f.source, ∃ P : ℕ → Set X,
      IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) ∧
      Monotone P ∧ (∀ n, (P n).Finite) ∧
      frontier V ⊆ closure (⋃ n, P n) ∧
      (∀ x (hx : x ∈ V),
        f.map ⟨x, hVsource (subset_closure hx)⟩ ∈
            closure (⋃ n, P n) → x ∈ closure (⋃ n, P n)) := by
  obtain ⟨V, hVopen, hKV, hVsource, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hK f.source.isOpen hKsource
  obtain ⟨Q, hQmono, _, hQclosure⟩ :=
    AreaDeficit.Surfaces.closed_set_dense_finite_exhaustion
      (A := frontier V) isClosed_frontier
  let R : ℕ → Set X := fun n => f.boundaryBackwardTree V hVsource (Q n) n
  have hRmono : Monotone R := by
    intro n m hnm
    have hroots : (Q n : Set X) ⊆ (Q m : Set X) := by
      exact_mod_cast hQmono hnm
    exact (f.boundaryBackwardTree_mono_roots hVsource hroots n).trans
      (f.boundaryBackwardTree_mono V hVsource (Q m) hnm)
  have hRfinite : ∀ n, (R n).Finite := fun n =>
    f.boundaryBackwardTree_finite hf hVcompact hVsource (Q n).finite_toSet n
  have hfront : frontier V ⊆ closure (⋃ n, R n) := by
    rw [← hQclosure]
    apply closure_mono
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n,
      f.roots_subset_boundaryBackwardTree V hVsource (Q n) n hxn⟩
  refine ⟨V, hVsource, R, hVopen, hKV, hVcompact,
    hRmono, hRfinite, hfront, ?_⟩
  intro x hxV hfx
  have hstageBack : ∀ n, ∀ y (hy : y ∈ V),
      f.map ⟨y, hVsource (subset_closure hy)⟩ ∈ R n → y ∈ R (n + 1) := by
    intro n y hy hfy
    have hroots : (Q n : Set X) ⊆ (Q (n + 1) : Set X) := by
      exact_mod_cast hQmono (Nat.le_succ n)
    exact Or.inr ⟨hy,
      f.boundaryBackwardTree_mono_roots hVsource hroots n hfy⟩
  apply mem_closure_iff.mpr
  intro U hU hxU
  let W : Set f.source := Subtype.val ⁻¹' (U ∩ V)
  have hWopen : IsOpen W := (hU.inter hVopen).preimage continuous_subtype_val
  have himage : IsOpen (f.map '' W) := hf.1 W hWopen
  have hfxmem : f.map ⟨x, hVsource (subset_closure hxV)⟩ ∈ f.map '' W :=
    ⟨⟨x, hVsource (subset_closure hxV)⟩, ⟨hxU, hxV⟩, rfl⟩
  obtain ⟨y, ⟨z, hzW, rfl⟩, hy⟩ :=
    mem_closure_iff.mp hfx _ himage hfxmem
  obtain ⟨n, hyn⟩ := mem_iUnion.mp hy
  exact ⟨(z : X), hzW.1, mem_iUnion.mpr ⟨n + 1, hstageBack n z hzW.2 hyn⟩⟩

end LocalMap
end SurfaceDynamics

#print axioms SurfaceDynamics.LocalMap.exists_boundaryPunctureSequence
