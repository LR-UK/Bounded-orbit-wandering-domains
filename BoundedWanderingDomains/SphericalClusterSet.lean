/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphericalDerivedSet
import Mathlib.Dynamics.OmegaLimit

/-!
# Spherical cluster sets of sequences

The cluster set of a sequence in the Riemann sphere is a nonempty compact
set.  The sequence is eventually contained in every open neighbourhood of
that set.  We also record the elementary separation property used for an
orbit through pairwise disjoint Fatou components.
-/

open Set Filter OnePoint Topology
open scoped Topology omegaLimit

namespace BoundedWanderingDomains

/-- The set of spherical cluster points of a sequence. -/
def sphericalClusterSet (u : ℕ → OnePoint ℂ) : Set (OnePoint ℂ) :=
  {a | MapClusterPt a atTop u}

theorem isClosed_sphericalClusterSet (u : ℕ → OnePoint ℂ) :
    IsClosed (sphericalClusterSet u) := by
  change IsClosed {a | ClusterPt a (Filter.map u atTop)}
  exact isClosed_setOfPred_clusterPt

theorem isCompact_sphericalClusterSet (u : ℕ → OnePoint ℂ) :
    IsCompact (sphericalClusterSet u) :=
  isCompact_univ.of_isClosed_subset (isClosed_sphericalClusterSet u) (subset_univ _)

theorem sphericalClusterSet_nonempty (u : ℕ → OnePoint ℂ) :
    (sphericalClusterSet u).Nonempty := by
  obtain ⟨a, ha⟩ := exists_clusterPt_of_compactSpace (Filter.map u atTop)
  exact ⟨a, ha⟩

/-- A sequence in the compact sphere eventually lies in every open
neighbourhood of its full cluster set. -/
theorem eventually_mem_of_sphericalClusterSet_subset
    (u : ℕ → OnePoint ℂ) {O : Set (OnePoint ℂ)} (hO : IsOpen O)
    (hsub : sphericalClusterSet u ⊆ O) :
    ∀ᶠ n in atTop, u n ∈ O := by
  let phi : ℕ → Unit → OnePoint ℂ := fun n _ => u n
  have heq : omegaLimit atTop phi ({Unit.unit} : Set Unit) = sphericalClusterSet u := by
    ext a
    rw [mem_omegaLimit_singleton_iff_mapClusterPt]
    rfl
  have hmaps := eventually_mapsTo_of_isOpen_of_omegaLimit_subset
    (f := atTop) (ϕ := phi) (s := ({Unit.unit} : Set Unit)) hO (heq ▸ hsub)
  filter_upwards [hmaps] with n hn
  exact hn (mem_singleton Unit.unit)

/-- An eventual closed constraint contains every spherical cluster point. -/
theorem sphericalClusterSet_subset_of_eventually_mem
    (u : ℕ → OnePoint ℂ) {C : Set (OnePoint ℂ)} (hC : IsClosed C)
    (hu : ∀ᶠ n in atTop, u n ∈ C) :
    sphericalClusterSet u ⊆ C := by
  intro a ha
  exact hC.mem_of_mapClusterPt ha hu

/-- Marked points in pairwise disjoint domains have no cluster point in the
initial domain. -/
theorem sphericalClusterSet_disjoint_initial
    (U : ℕ → Set ℂ) (z : ℕ → ℂ)
    (hz : ∀ n, z n ∈ U n)
    (hU : IsOpen (U 0))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    Disjoint (sphericalClusterSet (fun n => (z n : OnePoint ℂ)))
      (((↑) : ℂ → OnePoint ℂ) '' U 0) := by
  have hclosed : IsClosed ((((↑) : ℂ → OnePoint ℂ) '' U 0)ᶜ) :=
    (OnePoint.isOpen_image_coe.mpr hU).isClosed_compl
  have hev : ∀ᶠ n in atTop,
      (z n : OnePoint ℂ) ∈ ((((↑) : ℂ → OnePoint ℂ) '' U 0)ᶜ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro hmem
    obtain ⟨w, hw, heq⟩ := hmem
    have hne : 0 ≠ n := by omega
    exact Set.disjoint_left.mp (hdis hne) hw
      (OnePoint.coe_injective heq ▸ hz n)
  apply Set.disjoint_left.mpr
  intro a ha hUa
  exact (sphericalClusterSet_subset_of_eventually_mem _ hclosed hev ha) hUa

end BoundedWanderingDomains
