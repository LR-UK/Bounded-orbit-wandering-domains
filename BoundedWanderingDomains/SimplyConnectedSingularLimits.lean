/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.DerivedSetAreaContradiction
import BoundedWanderingDomains.BackwardOrbitMontel

/-! # Derived singular limits for simply connected wandering orbits

The finite models are constructed from backward images of two initial points.
Simple connectivity remains explicit here; it is the remaining classical
input for the bounded-singular-set branch of the unrestricted theorem.
-/

open Set Function Filter Metric OnePoint
open scoped Topology

namespace BoundedWanderingDomains

theorem wandering_orbit_subsequence_singularDerivedSet_of_simplyConnected
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hsc : ∀ n, IsSimplyConnected (U n)) :
    ∃ a ∈ sphericalDerivedSet (ComplexDynamics.singularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) := by
  classical
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    obtain ⟨p, _, hp⟩ := hU n
    rw [hp]
    exact (ComplexDynamics.isOpen_fatouSet f).connectedComponentIn
  have hzn : ∀ n, (f^[n]) z ∈ U n := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih => simpa only [iterate_succ_apply'] using hforward n ih
  have hUne : ∀ n, U n ≠ univ := by
    intro n heq
    exact disjoint_left.mp (hdis (Nat.ne_of_lt (Nat.lt_succ_self n)))
      (heq ▸ mem_univ ((f^[n+1]) z)) (hzn (n+1))
  choose u hu hub hu0 using fun n =>
    Complex.exists_bijOn_unitBall_map_eq_zero (hUo n) (hsc n) (hUne n) (hzn n)
  obtain ⟨a, ha, b, hb, hab⟩ := (infinite_of_mem_nhds z ((hUo 0).mem_nhds hz)).nontrivial
  obtain ⟨P, hP, haP, hbP, hfP, hcl⟩ := exists_finite_backward_orbit_models f a b
  have hcomp : ∀ n, connectedComponentIn (closure (⋃ j, (↑(P j) : Set ℂ)))ᶜ
      ((f^[n+1]) z) = U (n+1) := by
    intro n
    rw [hcl]
    exact backwardOrbit_complement_component hf hab hU hforward hdis ha hb
      (Nat.zero_lt_succ n) (hzn (n+1))
  have hnot := AreaDeficit.not_disjoint_cluster_singularDerivedSet_of_finite_models_with_exceptions
    hf (fun n => hUo (n+1)) (fun n => hu (n+1)) (fun n => hub (n+1))
    (fun n => hzn (n+1)) (fun n => hu0 (n+1))
    (fun n => (iterate_succ_apply' f (n+1) z).symm)
    (fun n => hforward (n+1))
    (fun n m hnm => hdis (by omega : n+1 ≠ m+1))
    hP hab haP hbP {f a, f b} (by simpa using hfP) hcomp
  obtain ⟨c, hcS, hc⟩ := not_disjoint_iff.mp hnot
  let : MetricSpace (OnePoint ℂ) := MetricSpace.ofDistTopology
    RiemannDynamics.sphericalDist
    (fun x => (RiemannDynamics.sphericalDist_eq_zero_iff x x).mpr rfl)
    RiemannDynamics.sphericalDist_comm RiemannDynamics.sphericalDist_triangle
    RiemannDynamics.sphericalDist_induces_topology
    (fun x y hxy => (RiemannDynamics.sphericalDist_eq_zero_iff x y).mp hxy)
  obtain ⟨φ, hφ, hlim⟩ := hc.tendsto_subseq
  exact ⟨c, hcS, fun k => φ k + 1, fun i j hij => Nat.add_lt_add_right (hφ hij) 1, hlim⟩

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.wandering_orbit_subsequence_singularDerivedSet_of_simplyConnected
