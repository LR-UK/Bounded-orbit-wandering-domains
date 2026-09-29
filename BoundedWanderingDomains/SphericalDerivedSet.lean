module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sequences
public import RiemannDynamics.Sphere.SphericalMetric

@[expose] public section

/-!
# Spherical accumulation of finite singular values

The set of finite singular values is a subset of `ℂ`, but its derived set
belongs to the sphere `OnePoint ℂ`. This file establishes the topological
infinity case independently of the definition of singular values.
-/

open Set Filter OnePoint Topology RiemannDynamics

namespace BoundedWanderingDomains

/-- Accumulation points in the sphere of a planar set. -/
def sphericalDerivedSet (S : Set ℂ) : Set (OnePoint ℂ) :=
  {a | AccPt a (𝓟 (((↑) : ℂ → OnePoint ℂ) '' S))}

/-- The spherical derived set is closed. -/
theorem isClosed_sphericalDerivedSet (S : Set ℂ) :
    IsClosed (sphericalDerivedSet S) := by
  exact isClosed_derivedSet (((↑) : ℂ → OnePoint ℂ) '' S)

/-- If the orbit eventually enters every spherical neighbourhood of the
derived set, all its cluster points lie in that derived set. -/
theorem cluster_points_in_sphericalDerivedSet_of_eventually_near
    (S : Set ℂ) (u : ℕ → OnePoint ℂ)
    (h : ∀ O : Set (OnePoint ℂ), IsOpen O →
      sphericalDerivedSet S ⊆ O → ∀ᶠ n in atTop, u n ∈ O) :
    ∀ a, MapClusterPt a atTop u → a ∈ sphericalDerivedSet S := by
  intro a ha
  by_contra hnot
  let D := sphericalDerivedSet S
  have hD : IsClosed D := isClosed_sphericalDerivedSet S
  have hDc : IsCompact D := isCompact_univ.of_isClosed_subset hD (subset_univ D)
  have hsub : D ⊆ ({a} : Set (OnePoint ℂ))ᶜ := by
    intro z hz heq
    exact hnot (heq ▸ hz)
  obtain ⟨O, hO, hDO, hOa⟩ := hDc.exists_isOpen_closure_subset
    (isOpen_compl_singleton.mem_nhdsSet.mpr hsub)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h O hO hDO)
  have htail : u '' Set.Ici N ⊆ O := by
    rintro z ⟨n, hn, rfl⟩
    exact hN n hn
  have hcl := (mapClusterPt_atTop_iff_forall_mem_closure.mp ha) N
  exact (hOa (closure_mono htail hcl)) rfl

/-- At infinity, being an accumulation point is just being in the closure:
the original planar set contains no point at infinity. -/
theorem infty_mem_sphericalDerivedSet_iff_mem_closure (S : Set ℂ) :
    (∞ : OnePoint ℂ) ∈ sphericalDerivedSet S ↔
      (∞ : OnePoint ℂ) ∈ closure (((↑) : ℂ → OnePoint ℂ) '' S) := by
  change AccPt (∞ : OnePoint ℂ) (𝓟 (((↑) : ℂ → OnePoint ℂ) '' S)) ↔ _
  rw [accPt_iff_frequently, mem_closure_iff_frequently]
  constructor
  · exact fun h => h.mono (fun _ hx => hx.2)
  · exact fun h => h.mono (fun x hx =>
      ⟨fun he => OnePoint.infty_notMem_image_coe (he ▸ hx), hx⟩)

/-- Infinity belongs to the spherical derived set precisely for an unbounded
planar set. -/
theorem infty_mem_sphericalDerivedSet_iff (S : Set ℂ) :
    (∞ : OnePoint ℂ) ∈ sphericalDerivedSet S ↔ ¬Bornology.IsBounded S := by
  rw [infty_mem_sphericalDerivedSet_iff_mem_closure]
  constructor
  · intro hin hb
    have hcompact : IsCompact (closure S) := hb.isCompact_closure
    have hclosed : IsClosed (((↑) : ℂ → OnePoint ℂ) '' closure S) :=
      OnePoint.isClosed_image_coe.mpr ⟨isClosed_closure, hcompact⟩
    have hsub : (((↑) : ℂ → OnePoint ℂ) '' S) ⊆
        (((↑) : ℂ → OnePoint ℂ) '' closure S) :=
      image_mono subset_closure
    exact OnePoint.infty_notMem_image_coe
      (closure_minimal hsub hclosed hin)
  · intro hunbounded
    by_contra h
    apply hunbounded
    have hnot : (∞ : OnePoint ℂ) ∉
        closure (((↑) : ℂ → OnePoint ℂ) '' S) := h
    have hcompact : IsCompact
        (((↑) : ℂ → OnePoint ℂ) ⁻¹'
          closure (((↑) : ℂ → OnePoint ℂ) '' S)) :=
      ((OnePoint.isClosed_iff_of_notMem hnot).mp isClosed_closure).2
    apply hcompact.isBounded.subset
    intro x hx
    exact subset_closure (mem_image_of_mem _ hx)

/-- Outside any open neighbourhood of its spherical derived set, a subset of
the sphere has only finitely many points. -/
theorem finite_outside_open_of_derived_subset
    (S O : Set (OnePoint ℂ)) (hO : IsOpen O)
    (hder : ∀ a, AccPt a (𝓟 S) → a ∈ O) : (S \ O).Finite := by
  by_contra hfinite
  have hinfinite : (S \ O).Infinite := Set.infinite_coe_iff.mp (not_finite_iff_infinite.mp hfinite)
  obtain ⟨a, ha⟩ := hinfinite.exists_accPt_principal
  have haS : AccPt a (𝓟 S) := ha.mono (principal_mono.mpr sdiff_subset)
  obtain ⟨b, ⟨hbO, hbSO⟩, _⟩ := (accPt_iff_nhds.mp ha) O (hO.mem_nhds (hder a haS))
  exact hbSO.2 hbO

/-- A planar set has finitely many points outside a spherical open
neighbourhood of all its spherical accumulation points. -/
theorem finite_planar_outside_spherical_derived_neighbourhood
    (S : Set ℂ) (O : Set (OnePoint ℂ)) (hO : IsOpen O)
    (hder : sphericalDerivedSet S ⊆ O) :
    {z : ℂ | z ∈ S ∧ (z : OnePoint ℂ) ∉ O}.Finite := by
  have hfinite := finite_outside_open_of_derived_subset
    (((↑) : ℂ → OnePoint ℂ) '' S) O hO (fun a ha => hder ha)
  have hpre := hfinite.preimage (fun x _ y _ hxy => OnePoint.coe_injective hxy)
  convert hpre using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff]
  constructor
  · rintro ⟨hz, hnot⟩
    exact ⟨⟨z, hz, rfl⟩, hnot⟩
  · rintro ⟨⟨w, hw, hwz⟩, hnot⟩
    exact ⟨OnePoint.coe_injective hwz ▸ hw, hnot⟩

/-- A derived singular value occurs as a cluster point provided every
cluster point belongs to the derived set. -/
theorem exists_clusterPt_sphericalDerivedSet
    (S : Set ℂ) (u : ℕ → OnePoint ℂ)
    (h : ∀ a, MapClusterPt a atTop u → a ∈ sphericalDerivedSet S) :
    ∃ a ∈ sphericalDerivedSet S, MapClusterPt a atTop u := by
  obtain ⟨a, ha⟩ := exists_clusterPt_of_compactSpace (Filter.map u atTop)
  exact ⟨a, h a ha, ha⟩

/-- The spherical metric converts a cluster point into a strictly increasing
subsequence converging to it. -/
theorem exists_subsequence_tendsto_sphericalDerivedSet
    (S : Set ℂ) (u : ℕ → OnePoint ℂ)
    (h : ∀ a, MapClusterPt a atTop u → a ∈ sphericalDerivedSet S) :
    ∃ a ∈ sphericalDerivedSet S, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) := by
  let : MetricSpace (OnePoint ℂ) := MetricSpace.ofDistTopology
    sphericalDist (fun x => (sphericalDist_eq_zero_iff x x).mpr rfl)
    sphericalDist_comm sphericalDist_triangle sphericalDist_induces_topology
    (fun x y hxy => (sphericalDist_eq_zero_iff x y).mp hxy)
  obtain ⟨a, ha, hcluster⟩ := exists_clusterPt_sphericalDerivedSet S u h
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  exact ⟨a, ha, φ, hφ, hlim⟩

/-- An eventual-neighbourhood conclusion from the dynamical argument gives
the requested strictly increasing subsequence on the sphere. -/
theorem exists_subsequence_of_eventually_near_sphericalDerivedSet
    (S : Set ℂ) (u : ℕ → OnePoint ℂ)
    (h : ∀ O : Set (OnePoint ℂ), IsOpen O →
      sphericalDerivedSet S ⊆ O → ∀ᶠ n in atTop, u n ∈ O) :
    ∃ a ∈ sphericalDerivedSet S, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  exists_subsequence_tendsto_sphericalDerivedSet S u
    (cluster_points_in_sphericalDerivedSet_of_eventually_near S u h)

end BoundedWanderingDomains
