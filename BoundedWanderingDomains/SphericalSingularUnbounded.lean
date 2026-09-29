module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.SphericalEscape
public import RiemannDynamics.BoundedWanderingSolution

@[expose] public section

/-!
# The unbounded-singular-set case of spherical accumulation

The previously formalised absence of bounded point orbits gives an unbounded
wandering orbit. When the finite singular set is unbounded, infinity lies in
its spherical derived set, and a subsequence of the orbit tends to infinity.
This reusable statement accepts any unbounded set; the completed singular-value
theorem instantiates it with the actual finite singular-value set.
-/

open Set Filter OnePoint
open scoped Topology

namespace BoundedWanderingDomains

/-- The unbounded-set branch of the derived-set theorem. The parameter `S`
can be instantiated with the finite singular-value set. -/
theorem wandering_orbit_subsequence_of_unbounded_set
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m : ℕ => Disjoint (U n) (U m)))
    (S : Set ℂ) (hS : ¬Bornology.IsBounded S) :
    ∃ a ∈ sphericalDerivedSet S, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => ((f^[φ k]) z : OnePoint ℂ))
        atTop (𝓝 a) := by
  have hescape : ¬Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z)) := by
    intro hb
    exact (Unconditional.no_bounded_wandering_domains_transcendental_entire
      hf htrans hU hz hforward hb) hdis
  obtain ⟨φ, hφ, hlim⟩ :=
    exists_subsequence_tendsto_infty_of_unbounded
      (fun n : ℕ => (f^[n]) z) hescape
  exact ⟨∞, (infty_mem_sphericalDerivedSet_iff S).mpr hS, φ, hφ, hlim⟩

end BoundedWanderingDomains
