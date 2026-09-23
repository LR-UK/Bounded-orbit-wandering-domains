import FunctionTheory.Analytic.FiniteComposition
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Points whose first n evaluation steps remain in the specified domains.
No values outside those domains are used in the corresponding composition. -/
def finiteOrbitDomain {α : Type*} (g : ℕ → α → α) (U : ℕ → Set α) (n : ℕ) : Set α :=
  {z | ∀ k < n, finiteComposition g k z ∈ U k}

theorem finiteOrbitDomain_zero {α : Type*} (g : ℕ → α → α) (U : ℕ → Set α) :
    finiteOrbitDomain g U 0 = univ := by
  ext z
  simp [finiteOrbitDomain]

theorem finiteOrbitDomain_succ {α : Type*} (g : ℕ → α → α) (U : ℕ → Set α) (n : ℕ) :
    finiteOrbitDomain g U (n + 1) =
      finiteOrbitDomain g U n ∩ (finiteComposition g n) ⁻¹' U n := by
  ext z
  constructor
  · intro h
    exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩
  · rintro ⟨h, hn⟩ k hk
    by_cases hkn : k < n
    · exact h k hkn
    · have he : k = n := by omega
      subst k
      exact hn

/-- The valid evaluation domain of a finite composition is open when every
map is continuous on its specified open domain. -/
theorem isOpen_finiteOrbitDomain {α : Type*} [TopologicalSpace α]
    (g : ℕ → α → α) (U : ℕ → Set α) (n : ℕ)
    (hU : ∀ k < n, IsOpen (U k)) (hg : ∀ k < n, ContinuousOn (g k) (U k)) :
    IsOpen (finiteOrbitDomain g U n) := by
  induction n with
  | zero => rw [finiteOrbitDomain_zero]; exact isOpen_univ
  | succ n ih =>
    have Hopen := ih (fun k hk => hU k (Nat.lt_succ_of_lt hk))
      (fun k hk => hg k (Nat.lt_succ_of_lt hk))
    have Hcont := continuousOn_finiteComposition g U (finiteOrbitDomain g U n) n
      (fun k hk => hg k (Nat.lt_succ_of_lt hk)) (fun k hk z hz => hz k hk)
    rw [finiteOrbitDomain_succ]
    apply isOpen_iff_mem_nhds.mpr
    rintro z ⟨hz, hz'⟩
    exact inter_mem (Hopen.mem_nhds hz)
      (((Hcont z hz).continuousAt (Hopen.mem_nhds hz)).eventually
        ((hU n (Nat.lt_succ_self n)).mem_nhds hz'))

/-- A chain of set inclusions is preserved by finite composition. -/
theorem mapsTo_finiteComposition {α : Type*} (g : ℕ → α → α)
    (A : ℕ → Set α) (n : ℕ)
    (hg : ∀ k < n, MapsTo (g k) (A k) (A (k + 1))) :
    MapsTo (finiteComposition g n) (A 0) (A n) := by
  induction n with
  | zero => intro z hz; exact hz
  | succ n ih =>
    change MapsTo (g n ∘ finiteComposition g n) (A 0) (A (n + 1))
    exact (hg n (Nat.lt_succ_self n)).comp
      (ih (fun k hk => hg k (Nat.lt_succ_of_lt hk)))

/-- The finite composition is holomorphic on its full valid evaluation domain. -/
theorem analyticOnNhd_finiteOrbitDomain (g : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (n : ℕ)
    (hg : ∀ k < n, AnalyticOnNhd ℂ (g k) (U k)) :
    AnalyticOnNhd ℂ (finiteComposition g n) (finiteOrbitDomain g U n) := by
  intro a ha
  exact analyticAt_finiteComposition g n (fun k hk => hg k hk _ (ha k hk))

end FunctionTheory
