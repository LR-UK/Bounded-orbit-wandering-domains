import BoundedWanderingDomains.WanderingSets
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.OpenMapping

open Set Function Filter
open scoped Topology

namespace AreaDeficit

/-- Local backward trees stop when they reach the prescribed outer roots. -/
def backwardTree {α : Type*} (f : α → α) (V Q : Set α) : ℕ → Set α
  | 0 => Q
  | n + 1 => backwardTree f V Q n ∪ (V ∩ f ⁻¹' backwardTree f V Q n)

theorem backwardTree_mono {α : Type*} (f : α → α) (V Q : Set α) :
    Monotone (backwardTree f V Q) :=
  monotone_nat_of_le_succ (fun _ => subset_union_left)

theorem roots_subset_backwardTree {α : Type*} (f : α → α) (V Q : Set α) (n : ℕ) :
    Q ⊆ backwardTree f V Q n :=
  backwardTree_mono f V Q (Nat.zero_le n)

theorem backwardTree_mono_roots {α : Type*} {f : α → α} {V Q R : Set α}
    (h : Q ⊆ R) (n : ℕ) : backwardTree f V Q n ⊆ backwardTree f V R n := by
  induction n with
  | zero => exact h
  | succ n ih => exact union_subset_union ih (inter_subset_inter_right _ (preimage_mono ih))

/-- Local forward invariance holds because roots lie outside the working set. -/
theorem backwardTree_forward {α : Type*} {f : α → α} {V Q : Set α}
    (hQV : Disjoint Q V) (n : ℕ) :
    f '' (backwardTree f V Q n ∩ V) ⊆ backwardTree f V Q n := by
  induction n with
  | zero =>
      rintro y ⟨x, ⟨hx, hxV⟩, rfl⟩
      exact False.elim (disjoint_left.mp hQV hx hxV)
  | succ n ih =>
      rintro y ⟨x, ⟨hx, hxV⟩, rfl⟩
      rcases hx with hx | hx
      · exact Or.inl (ih ⟨x, ⟨hx, hxV⟩, rfl⟩)
      · exact Or.inl hx.2

theorem backwardTree_finite {α : Type*} {f : α → α} {V Q : Set α}
    (hQ : Q.Finite) (hf : ∀ S : Set α, S.Finite → (V ∩ f ⁻¹' S).Finite)
    (n : ℕ) : (backwardTree f V Q n).Finite := by
  induction n with
  | zero => exact hQ
  | succ n ih => exact ih.union (hf _ ih)

theorem backwardTree_eventually_hits_root {α : Type*} {f : α → α} {V Q : Set α}
    {n : ℕ} {x : α} (hx : x ∈ backwardTree f V Q n) :
    ∃ k ≤ n, f^[k] x ∈ Q := by
  induction n generalizing x with
  | zero => exact ⟨0, le_rfl, hx⟩
  | succ n ih =>
      rcases hx with hx | hx
      · obtain ⟨k, hk, hroot⟩ := ih hx
        exact ⟨k, hk.trans (Nat.le_succ n), hroot⟩
      · obtain ⟨k, hk, hroot⟩ := ih hx.2
        exact ⟨k + 1, Nat.succ_le_succ hk, by simpa only [iterate_succ_apply] using hroot⟩

/-- No point of a fully trapped orbit is removed by a local puncture tree. -/
theorem trapped_not_mem_backwardTree {α : Type*} {f : α → α} {V Q : Set α}
    (hQV : Disjoint Q V) {x : α} (hx : ∀ k : ℕ, f^[k] x ∈ V) (n : ℕ) :
    x ∉ backwardTree f V Q n := by
  intro hp
  obtain ⟨k, _, hk⟩ := backwardTree_eventually_hits_root hp
  exact disjoint_left.mp hQV hk (hx k)

/-- The finite-fibre input is proved from analyticity on a neighbourhood of
a compact set and local nonconstancy, using isolated zeros. -/
theorem finite_local_preimage {f : ℂ → ℂ} {K S : Set ℂ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ x ∈ K, ¬EventuallyConst f (𝓝 x)) (hS : S.Finite) :
    (K ∩ f ⁻¹' S).Finite := by
  have hd := hf.preimage_mem_codiscreteWithin hn
    (compl_finite_mem_codiscreteWithin hS)
  have hh := hK.finite_sdiff_of_mem_codiscreteWithin hd
  simpa only [preimage_compl, sdiff_compl] using hh

/-- Openness transfers local backward invariance to the closure. No periodic
points or global dynamics enter this topological assertion. -/
theorem closure_locally_backward_invariant {α : Type*} [TopologicalSpace α]
    {f : α → α} {V P : Set α} (hV : IsOpen V)
    (hop : ∀ U ⊆ V, IsOpen U → IsOpen (f '' U))
    (hback : V ∩ f ⁻¹' P ⊆ P) : V ∩ f ⁻¹' closure P ⊆ closure P := by
  rintro x ⟨hxV, hx⟩
  apply mem_closure_iff.mpr
  intro U hU hxU
  have himage := hop (U ∩ V) inter_subset_right (hU.inter hV)
  obtain ⟨y, ⟨z, ⟨hzU, hzV⟩, hzy⟩, hyP⟩ :=
    mem_closure_iff.mp hx _ himage ⟨x, ⟨hxU, hxV⟩, rfl⟩
  exact ⟨z, hzU, hback ⟨hzV, by simpa only [mem_preimage, hzy] using hyP⟩⟩

theorem backwardTree_union_backward_invariant {α : Type*}
    (f : α → α) (V Q : Set α) :
    V ∩ f ⁻¹' (⋃ n : ℕ, backwardTree f V Q n) ⊆
      ⋃ n : ℕ, backwardTree f V Q n := by
  rintro x ⟨hxV, hx⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨n + 1, Or.inr ⟨hxV, hn⟩⟩

/-- On an open invariant set, even the closure of the puncture union is absent. -/
theorem puncture_closure_disjoint_trapped_open {α : Type*} [TopologicalSpace α]
    {f : α → α} {V Q O : Set α} (hQV : Disjoint Q V)
    (hO : IsOpen O) (hOV : O ⊆ V) (hfO : MapsTo f O O) :
    Disjoint (closure (⋃ n : ℕ, backwardTree f V Q n)) O := by
  have hp : (⋃ n : ℕ, backwardTree f V Q n) ⊆ Oᶜ := by
    intro x hx hxO
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    apply trapped_not_mem_backwardTree hQV (fun k => hOV (hfO.iterate k hxO)) n hn
  exact disjoint_left.mpr (fun x hx hxO =>
    (closure_minimal hp hO.isClosed_compl hx) hxO)

/-- Increasing finite root sets allow a dense collection of boundary roots. -/
def localPunctures {α : Type*} (f : α → α) (V : Set α) (Q : ℕ → Set α)
    (n : ℕ) : Set α := backwardTree f V (Q n) n

theorem localPunctures_mono {α : Type*} {f : α → α} {V : Set α}
    {Q : ℕ → Set α} (hQ : Monotone Q) : Monotone (localPunctures f V Q) := by
  intro n m hnm
  exact (backwardTree_mono_roots (hQ hnm) n).trans (backwardTree_mono f V (Q m) hnm)

theorem localPunctures_union_backward_invariant {α : Type*} {f : α → α}
    {V : Set α} {Q : ℕ → Set α} (hQ : Monotone Q) :
    V ∩ f ⁻¹' (⋃ n : ℕ, localPunctures f V Q n) ⊆
      ⋃ n : ℕ, localPunctures f V Q n := by
  rintro x ⟨hxV, hx⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  refine mem_iUnion.mpr ⟨n + 1, Or.inr ⟨hxV, ?_⟩⟩
  exact backwardTree_mono_roots (hQ (Nat.le_succ n)) n hn

theorem analytic_localPunctures_finite {f : ℂ → ℂ} {V K : Set ℂ}
    {Q : ℕ → Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K)
    (hf : AnalyticOnNhd ℂ f K) (hn : ∀ x ∈ K, ¬EventuallyConst f (𝓝 x))
    (hQ : ∀ n, (Q n).Finite) (n : ℕ) : (localPunctures f V Q n).Finite := by
  apply backwardTree_finite (hQ n)
  intro S hS
  exact (finite_local_preimage hK hf hn hS).subset (inter_subset_inter_left _ hVK)

theorem analytic_localPunctures_countable {f : ℂ → ℂ} {V K : Set ℂ}
    {Q : ℕ → Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K)
    (hf : AnalyticOnNhd ℂ f K) (hn : ∀ x ∈ K, ¬EventuallyConst f (𝓝 x))
    (hQ : ∀ n, (Q n).Finite) : (⋃ n : ℕ, localPunctures f V Q n).Countable :=
  countable_iUnion (fun n => (analytic_localPunctures_finite hVK hK hf hn hQ n).countable)

theorem analytic_locally_open {f : ℂ → ℂ} {V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f V) (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x)) :
    ∀ U ⊆ V, IsOpen U → IsOpen (f '' U) := by
  intro U hUV hU
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  have hh := (hf x (hUV hx)).eventually_constant_or_nhds_le_map_nhds
  have he : ¬ ∀ᶠ z in 𝓝 x, f z = f x := by
    intro he
    exact hn x (hUV hx) (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨f x, he⟩)
  exact hh.resolve_left he (image_mem_map (hU.mem_nhds hx))

theorem analytic_puncture_closure_backward_invariant {f : ℂ → ℂ}
    {V : Set ℂ} {Q : ℕ → Set ℂ} (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x))
    (hQ : Monotone Q) :
    V ∩ f ⁻¹' closure (⋃ n : ℕ, localPunctures f V Q n) ⊆
      closure (⋃ n : ℕ, localPunctures f V Q n) :=
  closure_locally_backward_invariant hV (analytic_locally_open hf hn)
    (localPunctures_union_backward_invariant hQ)

end AreaDeficit
