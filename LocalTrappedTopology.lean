import LocalPunctures
import Mathlib.Topology.Connected.LocallyConnected

open Set Function Filter
open scoped Topology

namespace AreaDeficit

def trappedSet {α : Type*} (f : α → α) (V : Set α) : Set α :=
  {x | ∀ n : ℕ, f^[n] x ∈ V}

theorem trappedSet_subset {α : Type*} (f : α → α) (V : Set α) :
    trappedSet f V ⊆ V := fun _ hx => hx 0

theorem trappedSet_forward {α : Type*} (f : α → α) (V : Set α) :
    MapsTo f (trappedSet f V) (trappedSet f V) := by
  intro x hx n
  simpa only [iterate_succ_apply] using hx (n + 1)

theorem preconnected_subset_of_avoids_frontier {α : Type*} [TopologicalSpace α]
    {S V A : Set α} (hS : IsPreconnected S) (hV : IsOpen V)
    (hfront : frontier V ⊆ A) (havoid : S ⊆ Aᶜ)
    (hmeet : (S ∩ V).Nonempty) : S ⊆ V := by
  apply hS.subset_of_closure_inter_subset hV hmeet
  rintro x ⟨hxcl, hxS⟩
  by_contra hxV
  apply havoid hxS
  apply hfront
  exact ⟨hxcl, by simpa only [hV.interior_eq] using hxV⟩

/-- A closed locally backward-invariant barrier containing the boundary
captures every trapped point which is not interior to the trapped set.
This theorem is purely local and topological. -/
theorem trapped_outside_barrier_is_interior {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] {f : α → α} {V A : Set α}
    (hV : IsOpen V) (hA : IsClosed A) (hf : ContinuousOn f V)
    (hfront : frontier V ⊆ A) (hback : V ∩ f ⁻¹' A ⊆ A)
    {x : α} (hx : x ∈ trappedSet f V) (hxA : x ∉ A) :
    x ∈ interior (trappedSet f V) := by
  let C := connectedComponentIn Aᶜ x
  have hxC : x ∈ C := mem_connectedComponentIn hxA
  have hCopen : IsOpen C := hA.isOpen_compl.connectedComponentIn
  have hCconn : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCA : C ⊆ Aᶜ := connectedComponentIn_subset _ _
  have hCV : C ⊆ V := preconnected_subset_of_avoids_frontier
    hCconn hV hfront hCA ⟨x, hxC, hx 0⟩
  have hit : ∀ n : ℕ, ContinuousOn (f^[n]) C ∧ MapsTo (f^[n]) C (V \ A) := by
    intro n
    induction n with
    | zero => exact ⟨continuousOn_id, fun y hy => ⟨hCV hy, hCA hy⟩⟩
    | succ n ih =>
        have hc : ContinuousOn (f^[n + 1]) C := by
          simpa only [iterate_succ'] using hf.comp ih.1 (fun y hy => (ih.2 hy).1)
        have ha : f^[n + 1] '' C ⊆ Aᶜ := by
          rintro y ⟨z, hz, rfl⟩ hyA
          apply (ih.2 hz).2
          apply hback
          exact ⟨(ih.2 hz).1, by simpa only [mem_preimage, iterate_succ_apply'] using hyA⟩
        have hv : f^[n + 1] '' C ⊆ V :=
          preconnected_subset_of_avoids_frontier (hCconn.image _ hc) hV hfront ha
            ⟨f^[n + 1] x, ⟨x, hxC, rfl⟩, hx (n + 1)⟩
        exact ⟨hc, fun y hy => ⟨hv ⟨y, hy, rfl⟩, ha ⟨y, hy, rfl⟩⟩⟩
  have hCT : C ⊆ trappedSet f V := fun y hy n => ((hit n).2 hy).1
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hCopen.mem_nhds hxC) hCT)

theorem trapped_boundary_subset_barrier {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] {f : α → α} {V A : Set α}
    (hV : IsOpen V) (hA : IsClosed A) (hf : ContinuousOn f V)
    (hfront : frontier V ⊆ A) (hback : V ∩ f ⁻¹' A ⊆ A) :
    trappedSet f V \ interior (trappedSet f V) ⊆ A := by
  rintro x ⟨hx, hxi⟩
  by_contra hxA
  exact hxi (trapped_outside_barrier_is_interior hV hA hf hfront hback hx hxA)

theorem trapped_interior_forward {α : Type*} [TopologicalSpace α]
    {f : α → α} {V : Set α}
    (hop : ∀ U ⊆ V, IsOpen U → IsOpen (f '' U)) :
    MapsTo f (interior (trappedSet f V)) (interior (trappedSet f V)) := by
  have ho := hop _ (interior_subset.trans (trappedSet_subset f V)) isOpen_interior
  apply mapsTo_iff_image_subset.mpr
  apply ho.subset_interior_iff.mpr
  rintro y ⟨x, hx, rfl⟩
  exact trappedSet_forward f V (interior_subset hx)

theorem localPunctures_closure_avoids_trapped_interior
    {α : Type*} [TopologicalSpace α] {f : α → α} {V : Set α} {Q : ℕ → Set α}
    (hQV : ∀ n, Disjoint (Q n) V) :
    Disjoint (closure (⋃ n : ℕ, localPunctures f V Q n))
      (interior (trappedSet f V)) := by
  have hp : (⋃ n : ℕ, localPunctures f V Q n) ⊆ (interior (trappedSet f V))ᶜ := by
    intro x hx hxi
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact trapped_not_mem_backwardTree (hQV n) (interior_subset hxi) n hn
  exact disjoint_left.mpr (fun _ hx hxi =>
    (closure_minimal hp isOpen_interior.isClosed_compl hx) hxi)

/-- Dense outer roots and their local preimages detect precisely the
non-interior trapped points. This is the topological part of the local
metric-exhaustion argument, proved without any Poincaré-metric axioms. -/
theorem analytic_trapped_inter_puncture_closure
    {f : ℂ → ℂ} {V : Set ℂ} {Q : ℕ → Set ℂ}
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x))
    (hQ : Monotone Q) (hQV : ∀ n, Disjoint (Q n) V)
    (hdense : frontier V ⊆ closure (⋃ n : ℕ, Q n)) :
    trappedSet f V ∩ closure (⋃ n : ℕ, localPunctures f V Q n) =
      trappedSet f V \ interior (trappedSet f V) := by
  have hr : (⋃ n : ℕ, Q n) ⊆ ⋃ n : ℕ, localPunctures f V Q n := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, roots_subset_backwardTree f V (Q n) n hn⟩
  have hb := trapped_boundary_subset_barrier hV isClosed_closure hf.continuousOn
    (hdense.trans (closure_mono hr)) (analytic_puncture_closure_backward_invariant hV hf hn hQ)
  have ha := localPunctures_closure_avoids_trapped_interior (f := f) hQV
  apply Subset.antisymm
  · rintro x ⟨hx, hxA⟩
    exact ⟨hx, fun hxi => disjoint_left.mp ha hxA hxi⟩
  · intro x hx
    exact ⟨hx.1, hb hx⟩

end AreaDeficit
