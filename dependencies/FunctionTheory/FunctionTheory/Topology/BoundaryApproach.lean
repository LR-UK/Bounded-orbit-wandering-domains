import TauCeti.Topology.ClusterSet
import Mathlib.Analysis.Normed.Module.Convex

/-! # Connected approach regions and relative boundary charts

Convex sets have preconnected approach regions. This property transfers through
a chart continuous on a larger set containing the domain, with a continuous
inverse there. In particular it is invariant under ambient homeomorphisms.
The application uses a topological chart of a closed Jordan interior.
-/

open Set Metric
open scoped Topology

namespace FunctionTheory

theorem isPreconnectedApproachAt_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (a : E) : TauCeti.IsPreconnectedApproachAt U a := by
  apply TauCeti.isPreconnectedApproachAt_of_forall_exists_isPreconnected_superset
  intro ε hε
  exact ⟨ε, hε, U ∩ ball a ε, Subset.refl _,
    (hU.inter (convex_ball a ε)).isPreconnected, Subset.refl _⟩

theorem isPreconnectedApproachAt_of_relative_chart
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {U S : Set X} {V T : Set Y} {F : X → Y} {G : Y → X} {a : X}
    (hUS : U ⊆ S) (hVT : V ⊆ T)
    (hF : ContinuousWithinAt F S a) (hG : ContinuousOn G T)
    (haT : F a ∈ T) (haG : G (F a) = a)
    (hFU : MapsTo F U V) (hGV : MapsTo G V U) (hGF : LeftInvOn G F U)
    (hV : TauCeti.IsPreconnectedApproachAt V (F a)) :
    TauCeti.IsPreconnectedApproachAt U a := by
  apply TauCeti.isPreconnectedApproachAt_of_forall_exists_isPreconnected_superset
  intro ε hε
  obtain ⟨η, hη, hηG⟩ := Metric.continuousWithinAt_iff.mp (hG (F a) haT) ε hε
  obtain ⟨t, ht, htη, htV⟩ := hV (ball (F a) η) (ball_mem_nhds _ hη)
  obtain ⟨β, hβ, hβt⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousWithinAt_iff.mp hF β hβ
  refine ⟨δ, hδ, G '' (V ∩ t), ?_, ?_, ?_⟩
  · rintro x ⟨y, ⟨hyV, hyt⟩, rfl⟩
    refine ⟨hGV hyV, ?_⟩
    have h := hηG (hVT hyV) (htη hyt)
    simpa only [haG, mem_ball] using h
  · exact htV.image G (hG.mono (inter_subset_left.trans hVT))
  · rintro x ⟨hxU, hxδ⟩
    exact ⟨F x, ⟨hFU hxU, hβt (hδF (hUS hxU) hxδ)⟩, hGF hxU⟩

theorem isPreconnectedApproachAt_preimage_homeomorph
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ₜ Y) {V : Set Y} {a : X}
    (hV : TauCeti.IsPreconnectedApproachAt V (e a)) :
    TauCeti.IsPreconnectedApproachAt (e ⁻¹' V) a := by
  apply isPreconnectedApproachAt_of_relative_chart (S := univ) (T := univ)
    (F := e) (G := e.symm) (subset_univ _) (subset_univ _)
    e.continuous.continuousWithinAt e.symm.continuous.continuousOn (mem_univ _)
    (e.symm_apply_apply a) (fun _ hz => hz) ?_ ?_ hV
  · intro y hy
    change e (e.symm y) ∈ V
    simpa only [e.apply_symm_apply] using hy
  · intro x _
    exact e.symm_apply_apply x

end FunctionTheory
