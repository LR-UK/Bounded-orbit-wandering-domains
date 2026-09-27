/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SurfaceGreenIdentity
import Mathlib.Topology.Compactness.LocallyFinite

/-! # Smooth partitions subordinate to restricted ambient charts -/

open Set Function
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

/-- A smooth partition on an open subsurface, subordinate to restrictions of
the ambient preferred charts centred at its own points. -/
structure RestrictedChartPartition (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) where
  rho : SmoothPartitionOfUnity U 𝓘(ℝ, ℂ) U Set.univ
  subordinate : rho.IsSubordinate
    (fun x : U => ((chartAt ℂ (x : M)).subtypeRestr hU).source)

/-- Every open subsurface of a second-countable Riemann surface has such a
partition. -/
theorem exists_restrictedChartPartition
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    Nonempty (RestrictedChartPartition U hU) := by
  letI : IsManifold 𝓘(ℝ, ℂ) ∞ U := isManifold_real_of_complex
  letI : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace ℂ U
  letI : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  let V : U → Set U := fun x =>
    ((chartAt ℂ (x : M)).subtypeRestr hU).source
  have hVopen : ∀ x, IsOpen (V x) := fun x =>
    ((chartAt ℂ (x : M)).subtypeRestr hU).open_source
  have hcover : (Set.univ : Set U) ⊆ ⋃ x, V x := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨x, ?_⟩
    simpa only [V, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using
      (mem_chart_source ℂ (x : M))
  obtain ⟨rho, hrho⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ)
      isClosed_univ V hVopen hcover
  exact ⟨⟨rho, hrho⟩⟩

theorem restrictedAmbientChart_mem_real_maximalAtlas
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) (x : U) :
    (chartAt ℂ (x : M)).subtypeRestr hU ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 U := by
  letI : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
  letI : IsManifold 𝓘(ℝ, ℂ) ∞ U := isManifold_real_of_complex
  exact StructureGroupoid.subtypeRestr_mem_maximalAtlas
    (G := contDiffGroupoid 2 𝓘(ℝ, ℂ))
      (chart_mem_atlas ℂ (x : M)) hU

namespace RestrictedChartPartition

variable {U : TopologicalSpace.Opens M} {hU : Nonempty U}

/-- Only finitely many members of a locally finite partition meet a compact
cutoff support. -/
noncomputable def active (P : RestrictedChartPartition U hU)
    (chi : U → ℝ) (hchi : HasCompactSupport chi) : Finset U :=
  (P.rho.locallyFinite.finite_nonempty_inter_compact hchi).toFinset

theorem mem_active_iff (P : RestrictedChartPartition U hU)
    {chi : U → ℝ} (hchi : HasCompactSupport chi) (i : U) :
    i ∈ P.active chi hchi ↔
      (support (P.rho i) ∩ tsupport chi).Nonempty := by
  simp [active]

/-- On the support of a compact cutoff, the active finite part of the
partition still sums to one. -/
theorem sum_active_mul (P : RestrictedChartPartition U hU)
    {chi : U → ℝ} (hchi : HasCompactSupport chi) (x : U) :
    (∑ i ∈ P.active chi hchi, P.rho i x * chi x) = chi x := by
  by_cases hx : chi x = 0
  · simp [hx]
  have hsub : P.rho.finsupport x ⊆ P.active chi hchi := by
    intro i hi
    rw [P.mem_active_iff hchi]
    refine ⟨x, ?_, subset_closure hx⟩
    simpa only [SmoothPartitionOfUnity.mem_finsupport, mem_support] using hi
  rw [← Finset.sum_mul]
  rw [P.rho.sum_finsupport' x (mem_univ x) hsub, one_mul]

end RestrictedChartPartition
end AreaDeficit.Surfaces
