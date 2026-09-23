import ConditionalWanderingDomains
import ComplexDynamics.BoundedNormality

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- For an entire non-polynomial function, no germ is constant. -/
theorem entire_nonpolynomial_no_constant_germ {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    ∀ x, ¬EventuallyConst f (𝓝 x) := by
  intro x hx
  obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.mp hx
  have he : EqOn f (fun _ => c) univ :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      isPreconnected_univ (mem_univ x) hc
  exact hp ⟨Polynomial.C c, fun z => by simpa using he (mem_univ z)⟩

/-- Bounded trapped interiors consist of Fatou points, using spherical
normality of locally bounded holomorphic iterates. -/
theorem trapped_interior_subset_fatou {f : ℂ → ℂ} {V : Set ℂ}
    (hf : Differentiable ℂ f) (hn : ∀ x, ¬EventuallyConst f (𝓝 x))
    (hV : Bornology.IsBounded V) :
    interior (trappedSet f V) ⊆ ComplexDynamics.fatouSet f := by
  have hi := trapped_interior_forward (analytic_locally_open
    ((hf.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ V)) (fun x _ => hn x))
  intro z hz
  exact ComplexDynamics.mem_fatouSet_of_iterate_mem_bounded_invariant hf isOpen_interior
    (hV.subset (interior_subset.trans (trappedSet_subset f V))) hi (N := 0) hz

/-- A uniformly bounded forward orbit of actual Fatou components is
represented by components of the local trapped interior in any larger
disc. This bridge is proved, not a hypothesis of the entire theorem. -/
theorem fatou_orbit_eq_trapped_components {f : ℂ → ℂ} {U : ℕ → Set ℂ} {V : Set ℂ}
    (hf : Differentiable ℂ f) (hn : ∀ x, ¬EventuallyConst f (𝓝 x))
    (hV : Bornology.IsBounded V)
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1))) (hUV : ∀ n, U n ⊆ V)
    {z : ℂ} (hz : z ∈ U 0) :
    (∀ n, f^[n] z ∈ interior (trappedSet f V)) ∧
    (∀ n, U n = connectedComponentIn (interior (trappedSet f V)) (f^[n] z)) := by
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    obtain ⟨a, _, ha⟩ := hU n
    rw [ha]
    exact (ComplexDynamics.isOpen_fatouSet f).connectedComponentIn
  have hit : ∀ k n, MapsTo (f^[k]) (U n) (U (n + k)) := by
    intro k
    induction k with
    | zero => intro n; simpa using mapsTo_id (U n)
    | succ k ih =>
        intro n
        simpa only [Nat.add_assoc, iterate_succ'] using (hforward (n + k)).comp (ih n)
  have hUT : ∀ n, U n ⊆ interior (trappedSet f V) := by
    intro n
    apply (hUo n).subset_interior_iff.mpr
    intro w hw k
    exact hUV (n + k) (hit k n hw)
  have hzn : ∀ n, f^[n] z ∈ U n := fun n => by simpa using hit n 0 hz
  refine ⟨fun n => hUT n (hzn n), ?_⟩
  intro n
  obtain ⟨a, ha, hcomp⟩ := hU n
  have hUa : U n = connectedComponentIn (ComplexDynamics.fatouSet f) (f^[n] z) :=
    hcomp.trans (connectedComponentIn_eq (hcomp ▸ hzn n))
  apply Subset.antisymm
  · have hconn : IsPreconnected (U n) := hcomp ▸ isPreconnected_connectedComponentIn
    exact hconn.subset_connectedComponentIn (hzn n) (hUT n)
  · rw [hUa]
    exact connectedComponentIn_mono _ (trapped_interior_subset_fatou hf hn hV)

end AreaDeficit

#print axioms AreaDeficit.fatou_orbit_eq_trapped_components
