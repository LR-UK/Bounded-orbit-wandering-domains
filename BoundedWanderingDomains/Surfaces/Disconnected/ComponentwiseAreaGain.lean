module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseArea
public import BoundedWanderingDomains.Surfaces.CompactFiniteRemoval

@[expose] public section

/-! # Area-gain budgets summed over ambient components -/

open Set Function MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

noncomputable def domainAreaGain (p : ComponentwiseDiscCover X) (U V : Opens X) : Measure X :=
  Measure.sum (fun c : ConnectedComponents X =>
    Measure.map (Subtype.val : ambientComponent c → X)
      ((p.cover c).domainAreaGain (componentPart c U) (componentPart c V)))

theorem domainAreaGain_apply (p : ComponentwiseDiscCover X) (U V : Opens X)
    {A : Set X} (hA : MeasurableSet A) :
    p.domainAreaGain U V A = ∑' c : ConnectedComponents X,
      (p.cover c).domainAreaGain (componentPart c U) (componentPart c V) (Subtype.val ⁻¹' A) := by
  rw [domainAreaGain, Measure.sum_apply _ hA]
  apply tsum_congr
  intro c
  exact Measure.map_apply continuous_subtype_val.measurable hA

theorem domainArea_le_add_gain (p : ComponentwiseDiscCover X) (U V : Opens X)
    {A : Set X} (hA : MeasurableSet A) :
    p.domainArea V A ≤ p.domainArea U A + p.domainAreaGain U V A := by
  rw [p.domainArea_apply V hA, p.domainArea_apply U hA, p.domainAreaGain_apply U V hA,
    ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro c
  exact (p.cover c).domainArea_le_add_gain _ _
    (hA.preimage continuous_subtype_val.measurable)

theorem domainAreaGain_apply_finite_component_cover (p : ComponentwiseDiscCover X)
    (U V : Opens X) (I : Finset (ConnectedComponents X)) {A : Set X}
    (hA : MeasurableSet A) (hAI : A ⊆ ⋃ c ∈ I, (ambientComponent c : Set X)) :
    p.domainAreaGain U V A = ∑ c ∈ I,
      (p.cover c).domainAreaGain (componentPart c U) (componentPart c V) (Subtype.val ⁻¹' A) := by
  classical
  rw [p.domainAreaGain_apply U V hA]
  apply tsum_eq_sum
  intro c hc
  have hempty : (Subtype.val ⁻¹' A : Set (ambientComponent c)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp (hAI hx)
    have hcd : c = d := x.property.symm.trans hxd
    exact hc (hcd.symm ▸ hd)
  rw [hempty, measure_empty]

variable [LocallyCompactSpace X]

theorem compact_finite_remote_removal_gain (p : ComponentwiseDiscCover X) (E : Finset X)
    {K L : Set X} (hK : IsClosed K) (hL : IsCompact L) (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ U : Opens X,
      p.domainAreaGain U (finiteRemovalDomain U E ⊓ ⟨Kᶜ, hK.isOpen_compl⟩) L ≤ B := by
  classical
  obtain ⟨I, hI⟩ := exists_finite_component_cover hL
  let localCompactComponents : ∀ c : ConnectedComponents X, LocallyCompactSpace (ambientComponent c) :=
    fun c => (ambientComponent c).isOpen.locallyCompactSpace
  choose B hB hb using fun c : ConnectedComponents X =>
    (p.cover c).compact_finite_remote_removal_gain (componentPunctures c E)
      (hK.preimage (continuous_subtype_val : Continuous (Subtype.val : ambientComponent c → X)))
      ((isClosed_ambientComponent c).isClosedEmbedding_subtypeVal.isCompact_preimage hL)
      (hLK.preimage (Subtype.val : ambientComponent c → X))
  refine ⟨∑ c ∈ I, B c, ENNReal.sum_ne_top.mpr (fun c _ => hB c), ?_⟩
  intro U
  rw [p.domainAreaGain_apply_finite_component_cover _ _ I hL.measurableSet hI]
  apply Finset.sum_le_sum
  intro c hc
  have he : componentPart c (finiteRemovalDomain U E ⊓ ⟨Kᶜ, hK.isOpen_compl⟩) =
      finiteRemovalDomain (componentPart c U) (componentPunctures c E) ⊓
        ⟨(Subtype.val ⁻¹' K)ᶜ, (hK.preimage continuous_subtype_val).isOpen_compl⟩ := by
    ext x
    simp [componentPart, finiteRemovalDomain]
  rw [he]
  exact hb c (componentPart c U)

end AreaDeficit.Surfaces.ComponentwiseDiscCover
