/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LocalDerivedSetAreaContradiction
import BoundedWanderingDomains.LocalPunctureSequence
import BoundedWanderingDomains.BarrierComponents
import BoundedWanderingDomains.SubmissionDefinitions

/-! # Derived singular accumulation for bounded local analytic dynamics

The singular set belongs to the restriction f|V. Values of f outside V do
not enter its definition. The working domain has compact closure, and the
map is analytic and has no constant germ near that closure.
-/

open Set Function Filter Metric OnePoint
open scoped Topology

namespace BoundedWanderingDomains
open AreaDeficit

theorem local_wandering_orbit_subsequence_spherical_singular_derivedSet
    {f : ℂ → ℂ} {V : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValuesOn f V), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) := by
  classical
  have hfV := hf.mono (subset_closure : V ⊆ closure V)
  have hi := trapped_interior_forward
    (analytic_locally_open hfV (fun x hx => hn x (subset_closure hx)))
  have hzi : ∀ n, f^[n] z ∈ interior (trappedSet f V) := fun n => hi.iterate n hz
  have hUo : ∀ n, IsOpen (U n) := fun n => by rw [hU n]; exact isOpen_interior.connectedComponentIn
  have hzU : ∀ n, f^[n] z ∈ U n := fun n => by rw [hU n]; exact mem_connectedComponentIn (hzi n)
  have hUT : ∀ n, U n ⊆ interior (trappedSet f V) :=
    fun n => by rw [hU n]; exact connectedComponentIn_subset _ _
  have hUV : ∀ n, U n ⊆ V :=
    fun n => (hUT n).trans (interior_subset.trans (trappedSet_subset f V))
  have hfm : ∀ n, MapsTo f (U n) (U (n+1)) := by
    intro n
    rw [hU n, hU (n+1), iterate_succ_apply']
    exact ((hfV.continuousOn.mono
      (interior_subset.trans (trappedSet_subset f V))).mapsTo_connectedComponentIn
      (hzi n)).mono_right (connectedComponentIn_mono _ hi.image_subset)
  have hUne : ∀ n, U n ≠ univ := by
    intro n heq
    exact disjoint_left.mp (hdis (Nat.ne_of_lt (Nat.lt_succ_self n)))
      (heq ▸ mem_univ (f^[n+1] z)) (hzU (n+1))
  choose u hu hub hu0 using fun n =>
    Complex.exists_bijOn_unitBall_map_eq_zero (hUo n) (hsc n) (hUne n) (hzU n)
  obtain ⟨R, hR, hVR⟩ := hVc.isBounded.exists_pos_norm_le
  let a : ℂ := ((R+1 : ℝ) : ℂ)
  let b : ℂ := ((R+2 : ℝ) : ℂ)
  have ha : a ∉ V := by
    intro hx
    have h := hVR _ (subset_closure hx)
    dsimp [a] at h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h
    linarith
  have hb : b ∉ V := by
    intro hx
    have h := hVR _ (subset_closure hx)
    dsimp [b] at h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h
    linarith
  have hab : a ≠ b := by
    intro he
    have h := Complex.ofReal_injective he
    linarith
  obtain ⟨P, hP, hanchors, hforward, _havoid, hbarrier, hfront, hback⟩ :=
    exists_local_puncture_sequence hV subset_closure hVc hf hn ha hb
  let A := closure (⋃ n, (↑(P n) : Set ℂ))
  have hTA : interior (trappedSet f V) ⊆ Aᶜ := by
    intro x hx hxA
    have hh : x ∈ trappedSet f V ∩ A := ⟨interior_subset hx, hxA⟩
    rw [hbarrier] at hh
    exact hh.2 hx
  have hcomp : ∀ n, connectedComponentIn Aᶜ (f^[n] z) = U n := fun n =>
    (barrier_component_eq_trapped_component hV isClosed_closure hfV.continuousOn
      hfront hback hTA (hzi n)).trans (hU n).symm
  have hnot := not_disjoint_cluster_localSingularDerivedSet_of_finite_models
    hV hfV hUo hUV hu hub hzU hu0
    (fun n => (iterate_succ_apply' f n z).symm) hfm hdis hP hab
    (hanchors 0).1 (hanchors 0).2 ∅
    (fun j x hx hxP => Or.inl (hforward j x hx hxP)) hcomp
  obtain ⟨c, hcS, hc⟩ := not_disjoint_iff.mp hnot
  let : MetricSpace (OnePoint ℂ) := MetricSpace.ofDistTopology
    RiemannDynamics.sphericalDist
    (fun x => (RiemannDynamics.sphericalDist_eq_zero_iff x x).mpr rfl)
    RiemannDynamics.sphericalDist_comm RiemannDynamics.sphericalDist_triangle
    RiemannDynamics.sphericalDist_induces_topology
    (fun x y hxy => (RiemannDynamics.sphericalDist_eq_zero_iff x y).mp hxy)
  obtain ⟨φ, hφ, hlim⟩ := hc.tendsto_subseq
  refine ⟨c, ?_, φ, hφ, hlim⟩
  rwa [ComplexDynamics.derivedSet_sphericalSingularValuesOn]

end BoundedWanderingDomains

#print axioms BoundedWanderingDomains.local_wandering_orbit_subsequence_spherical_singular_derivedSet
