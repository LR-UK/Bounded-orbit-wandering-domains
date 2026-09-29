module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainSurfaceGreenIdentity
public import Mathlib.Topology.Compactness.LocallyFinite

@[expose] public section

/-! # Smooth partitions subordinate to ambient surface charts -/

open Set Function
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

/-- A smooth partition of unity subordinate to the preferred holomorphic
chart centred at each index point. -/
structure AmbientChartPartition (M : Type*) [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] where
  rho : SmoothPartitionOfUnity M 𝓘(ℝ, ℂ) M Set.univ
  subordinate : rho.IsSubordinate (fun x : M => (chartAt ℂ x).source)

theorem exists_ambientChartPartition : Nonempty (AmbientChartPartition M) := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  let V : M → Set M := fun x => (chartAt ℂ x).source
  have hVopen : ∀ x, IsOpen (V x) := fun x => (chartAt ℂ x).open_source
  have hcover : (Set.univ : Set M) ⊆ ⋃ x, V x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩
  obtain ⟨rho, hrho⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ)
      isClosed_univ V hVopen hcover
  exact ⟨⟨rho, hrho⟩⟩

omit [T2Space M] [SecondCountableTopology M] in
theorem ambientChart_mem_real_maximalAtlas (x : M) :
    chartAt ℂ x ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 2 M := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_of_complex
  exact (contDiffGroupoid 2 𝓘(ℝ, ℂ)).chart_mem_maximalAtlas x

namespace AmbientChartPartition

/-- The finite set of partition members meeting a compact cutoff. -/
noncomputable def active (P : AmbientChartPartition M)
    (chi : M → ℝ) (hchi : HasCompactSupport chi) : Finset M :=
  (P.rho.locallyFinite.finite_nonempty_inter_compact hchi).toFinset

omit [T2Space M] [SecondCountableTopology M] in
theorem mem_active_iff (P : AmbientChartPartition M)
    {chi : M → ℝ} (hchi : HasCompactSupport chi) (i : M) :
    i ∈ P.active chi hchi ↔
      (support (P.rho i) ∩ tsupport chi).Nonempty := by
  simp [active]

omit [T2Space M] [SecondCountableTopology M] in
theorem sum_active_mul (P : AmbientChartPartition M)
    {chi : M → ℝ} (hchi : HasCompactSupport chi) (x : M) :
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

end AmbientChartPartition
end AreaDeficit.Surfaces
