module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CompactPointRemoval

@[expose] public section

/-! # Uniform compact area budget for a fixed finite removed set -/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [T2Space M]

def finiteRemovalDomain (U : TopologicalSpace.Opens M) (E : Finset M) :
    TopologicalSpace.Opens M :=
  ⟨(U : Set M) \ (E : Set M),U.isOpen.sdiff E.finite_toSet.isClosed⟩

@[simp] theorem finiteRemovalDomain_empty (U : TopologicalSpace.Opens M) :
    finiteRemovalDomain U ∅ = U := by ext x; simp [finiteRemovalDomain]

theorem finiteRemovalDomain_insert [DecidableEq M] (U : TopologicalSpace.Opens M)
    (E : Finset M) (a : M) :
    finiteRemovalDomain U (insert a E) = punctureDomain (finiteRemovalDomain U E) a := by
  ext x
  change (x ∈ U ∧ x ∉ insert a E) ↔ (x ∈ U ∧ x ∉ E) ∧ x ≠ a
  simp only [Finset.mem_insert]
  tauto

namespace DiscCover
variable [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  [SecondCountableTopology M] [LocallyCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- Finite exceptional points have one finite compact area budget,
independent of the variable old domain and its number of components. -/
theorem compact_finite_removal_gain (p : DiscCover M) (E : Finset M)
    {L : Set M} (hL : IsCompact L) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ U : TopologicalSpace.Opens M,
      p.domainAreaGain U (finiteRemovalDomain U E) L ≤ B := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨0,ENNReal.zero_ne_top,?_⟩
    intro U
    simp
  | @insert a E _ ih =>
    obtain ⟨B,hB,hbound⟩ := ih
    obtain ⟨C,hC,hpoint⟩ := p.compact_point_removal_gain a hL
    refine ⟨B + C,ENNReal.add_ne_top.mpr ⟨hB,hC⟩,?_⟩
    intro U
    rw [finiteRemovalDomain_insert]
    exact (p.domainAreaGain_triangle U (punctureDomain (finiteRemovalDomain U E) a)
      (finiteRemovalDomain U E) hL.measurableSet).trans
      (add_le_add (hbound U) (hpoint (finiteRemovalDomain U E)))

/-- A remote closed obstacle and finitely many exceptional points have a
single finite compact removal budget, uniformly in the old domain. -/
theorem compact_finite_remote_removal_gain (p : DiscCover M) (E : Finset M)
    {K L : Set M} (hK : IsClosed K) (hL : IsCompact L) (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ U : TopologicalSpace.Opens M,
      p.domainAreaGain U
        (finiteRemovalDomain U E ⊓ ⟨Kᶜ,hK.isOpen_compl⟩) L ≤ B := by
  obtain ⟨B,hB,hfinite⟩ := p.compact_finite_removal_gain E hL
  obtain ⟨C,hC,hremote⟩ := p.compact_localization_domainAreaGain
    ⟨Kᶜ,hK.isOpen_compl⟩ hL (fun _ hx hxK => disjoint_left.mp hLK hx hxK)
  refine ⟨B + C,ENNReal.add_ne_top.mpr ⟨hB,hC⟩,?_⟩
  intro U
  exact (p.domainAreaGain_triangle U _ (finiteRemovalDomain U E) hL.measurableSet).trans
    (add_le_add (hfinite U) (hremote (finiteRemovalDomain U E)))

end DiscCover
end AreaDeficit.Surfaces
