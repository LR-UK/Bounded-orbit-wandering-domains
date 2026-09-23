import FunctionTheory.Topology.FiniteOrbitDomain

open Set

namespace FunctionTheory

set_option autoImplicit false

/-- Finite compositions depend only on map values in the domains actually
visited by the orbit, including when the maps are ambient representatives
of functions on open subtypes. -/
theorem finiteComposition_eq_of_eqOn_along_orbit
    {α : Type*} (g f : ℕ → α → α) (U : ℕ → Set α) (N : ℕ) (z : α)
    (hz : z ∈ finiteOrbitDomain g U N)
    (hgf : ∀ k < N, EqOn (g k) (f k) (U k)) :
    ∀ k ≤ N, finiteComposition g k z = finiteComposition f k z := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    simp only [finiteComposition, Function.comp_apply]
    rw [← ih (by omega)]
    exact hgf k hkN (hz k hkN)

end FunctionTheory
