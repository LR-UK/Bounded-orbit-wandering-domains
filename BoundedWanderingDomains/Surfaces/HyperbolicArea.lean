/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CountableChartPartition
import BoundedWanderingDomains.Surfaces.LocalAreaMeasure
open Set Function Filter Metric MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
noncomputable def areaUsing (p : DiscCover M) (P : ChartPartition M) : Measure M :=
  Measure.sum (fun n => (p.localArea (P.chart n)).restrict (P.piece n))
theorem areaUsing_apply_chart (p : DiscCover M) (P : ChartPartition M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    p.areaUsing P A = p.localArea c A := by
  change (Measure.sum _) A = _
  rw [Measure.sum_apply _ hA]
  have he : ∀ n, (p.localArea (P.chart n)).restrict (P.piece n) A =
      p.localArea c (A ∩ P.piece n) := by
    intro n
    rw [Measure.restrict_apply hA]
    exact p.localArea_overlap (P.holomorphic n) hc (hA.inter (P.measurable n))
      (inter_subset_right.trans (P.subordinate n)) (inter_subset_left.trans hAc)
  simp_rw [he]
  have hdis : Pairwise (Disjoint on (fun n => A ∩ P.piece n)) :=
    pairwise_disjoint_mono P.disjoint (fun _ => inter_subset_right)
  rw [← measure_iUnion hdis (fun n => hA.inter (P.measurable n)),
    ← inter_iUnion,P.covers,inter_univ]
theorem areaUsing_independent (p : DiscCover M) (P Q : ChartPartition M) :
    p.areaUsing P = p.areaUsing Q := by
  apply Measure.ext
  intro A hA
  have hdis : Pairwise (Disjoint on (fun n => A ∩ P.piece n)) :=
    pairwise_disjoint_mono P.disjoint (fun _ => inter_subset_right)
  have hcover : (⋃ n, A ∩ P.piece n) = A := by rw [← inter_iUnion,P.covers,inter_univ]
  have he : ∀ n, p.areaUsing P (A ∩ P.piece n) = p.areaUsing Q (A ∩ P.piece n) := by
    intro n
    rw [p.areaUsing_apply_chart P (P.holomorphic n) (hA.inter (P.measurable n))
        (inter_subset_right.trans (P.subordinate n)),
      p.areaUsing_apply_chart Q (P.holomorphic n) (hA.inter (P.measurable n))
        (inter_subset_right.trans (P.subordinate n))]
  rw [← hcover,measure_iUnion hdis (fun n => hA.inter (P.measurable n)),
    measure_iUnion hdis (fun n => hA.inter (P.measurable n))]
  exact tsum_congr he
theorem areaUsing_cover_independent (p q : DiscCover M) (P : ChartPartition M) :
    p.areaUsing P = q.areaUsing P := by
  unfold areaUsing
  congr 1
  funext n
  rw [p.localArea_cover_independent q (P.holomorphic n)]
variable [SecondCountableTopology M]
noncomputable def hyperbolicArea (p : DiscCover M) : Measure M := by
  let : Nonempty M := ⟨p.projection ⟨0,by simp [unitDisc]⟩⟩
  exact p.areaUsing (Classical.choice (exists_chartPartition (M := M)))
theorem hyperbolicArea_apply_chart (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    p.hyperbolicArea A = p.coordinateArea c A := by
  unfold hyperbolicArea
  rw [p.areaUsing_apply_chart _ hc hA hAc,p.localArea_apply_of_subset c hA hAc]
theorem hyperbolicArea_independent (p q : DiscCover M) :
    p.hyperbolicArea = q.hyperbolicArea := by
  unfold hyperbolicArea
  exact p.areaUsing_cover_independent q _
end AreaDeficit.Surfaces.DiscCover
