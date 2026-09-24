/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphereCompactSeparation
import BoundedWanderingDomains.DerivedSetExceptionalAvoidance
import BoundedWanderingDomains.SphericalShrinking
import BoundedWanderingDomains.SingularDiscInjectivity

/-!
# Intrinsic discs away from a spherical derived set

If the spherical cluster set of a wandering orbit is disjoint from the
spherical derived set of a planar set, then every fixed intrinsic disc in
the late components avoids that planar set.  Applied to the singular values,
the global covering theorem consequently gives eventual injectivity on the
preceding intrinsic discs.
-/

open Set Filter Metric Function OnePoint
open scoped Topology

namespace AreaDeficit

/-- Separation from the spherical derived set forces every fixed late
intrinsic disc to avoid the original planar set.  The finitely many points
outside a neighbourhood of the derived set are avoided by pairwise
disjointness of the ambient domains. -/
theorem eventually_chartDisc_avoid_of_cluster_disjoint_sphericalDerivedSet
    (S : Set ℂ) {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hsep : Disjoint (BoundedWanderingDomains.sphericalDerivedSet S)
      (BoundedWanderingDomains.sphericalClusterSet
        (fun n => ((z n : ℂ) : OnePoint ℂ))))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop,
      Disjoint (chartDisc (u (n + 1)) (U (n + 1)) r) S := by
  let D := BoundedWanderingDomains.sphericalDerivedSet S
  let C := BoundedWanderingDomains.sphericalClusterSet
    (fun n => ((z n : ℂ) : OnePoint ℂ))
  have hDc : IsCompact D :=
    isCompact_univ.of_isClosed_subset
      (BoundedWanderingDomains.isClosed_sphericalDerivedSet S) (subset_univ D)
  have hCc : IsCompact C :=
    BoundedWanderingDomains.isCompact_sphericalClusterSet _
  obtain ⟨K, L, hKc, hLc, hKL, hDK, hCL⟩ :=
    BoundedWanderingDomains.exists_disjoint_compact_sphere_neighborhoods
      hDc hCc hsep
  have havoid0 : ∀ᶠ n in atTop,
      Disjoint (U n) {w : ℂ | w ∈ S ∧ (w : OnePoint ℂ) ∉ interior K} :=
    BoundedWanderingDomains.eventually_components_avoid_outside_spherical_derived_neighbourhood
      S (interior K) isOpen_interior hDK U hdis
  have havoid : ∀ᶠ n in atTop,
      Disjoint (U (n + 1)) {w : ℂ | w ∈ S ∧ (w : OnePoint ℂ) ∉ interior K} := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp havoid0
    exact eventually_atTop.mpr ⟨N, fun n hn =>
      hN (n + 1) (hn.trans (Nat.le_succ n))⟩
  have hshrink : ∀ᶠ n in atTop,
      ((fun w : ℂ => ((w : ℂ) : OnePoint ℂ)) ''
        chartDisc (u (n + 1)) (U (n + 1)) r) ⊆ interior L :=
    eventually_chartDisc_subset_cluster_neighbourhood hU hu hub hz hu0 hdis
      isOpen_interior hCL hr hr1
  filter_upwards [havoid, hshrink] with n hn hLn
  apply disjoint_left.mpr
  intro w hwD hwS
  have hwL : (w : OnePoint ℂ) ∈ interior L :=
    hLn (mem_image_of_mem (fun q : ℂ => ((q : ℂ) : OnePoint ℂ)) hwD)
  by_cases hwK : (w : OnePoint ℂ) ∈ interior K
  · exact Set.disjoint_left.mp hKL (interior_subset hwK) (interior_subset hwL)
  · exact Set.disjoint_left.mp hn hwD.1 ⟨hwS, hwK⟩

/-- If the orbit cluster set misses the spherical derived set of the singular
values, the map is eventually injective on every fixed intrinsic disc. -/
theorem eventually_injOn_chartDisc_of_cluster_disjoint_singularDerivedSet
    {f : ℂ → ℂ} {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hznext : ∀ n, f (z n) = z (n + 1))
    (hf : Differentiable ℂ f)
    (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hsep : Disjoint
      (BoundedWanderingDomains.sphericalDerivedSet
        (ComplexDynamics.singularValues f))
      (BoundedWanderingDomains.sphericalClusterSet
        (fun n => ((z n : ℂ) : OnePoint ℂ))))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, InjOn f (chartDisc (u n) (U n) r) := by
  apply eventually_injOn_chartDisc_of_chartDisc_avoid_singularValues
    hU hu hub hz hu0 hznext hf hfm hr hr1
  exact eventually_chartDisc_avoid_of_cluster_disjoint_sphericalDerivedSet
    (ComplexDynamics.singularValues f) hU hu hub hz hu0 hdis hsep hr hr1

end AreaDeficit

#print axioms AreaDeficit.eventually_chartDisc_avoid_of_cluster_disjoint_sphericalDerivedSet
#print axioms AreaDeficit.eventually_injOn_chartDisc_of_cluster_disjoint_singularDerivedSet
