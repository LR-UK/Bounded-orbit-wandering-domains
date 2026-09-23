import EremenkosConjecture.ContinuumReferenceOrbits
import EremenkosConjecture.LocalChartMargins
import EremenkosConjecture.UniformIterateControl

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

variable {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ}
  {S : ContinuumStage D j} {R : ContinuumReturnChannel D S.f j (S.depth + 3)}

theorem ContinuumReference.barrier_iterate_zero (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {z : ℂ} (hz : z ∈ frontier (D.region (S.depth + 1))) :
    (P.reference.g^[returnTime j + 1]) z = 0 := by
  have hband : z ∈ D.band S.depth :=
    (D.frontier_tube_band hζ (i := S.depth) (m := S.depth + 1) (n := S.depth + 2)
      (by omega) (by omega)).subset hz
  rw [iterate_succ_apply', P.iterate_eq_old le_rfl hband.1, ← P.oldChart.agrees z]
  exact P.reference.barrier_eq (mem_image_of_mem _ hband)

theorem ContinuumReference.barrier_uniformControl (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {k : ℕ} (hk : k < returnTime j + 1) :
    UniformControlOn P.reference.g P.controlSet
      ((P.reference.g^[k]) '' frontier (D.region (S.depth + 1))) := by
  have hbar : HasUniformTube (frontier (D.region (S.depth + 1))) (D.band S.depth) :=
    D.frontier_tube_band hζ (by omega) (by omega)
  have hbarold : HasUniformTube (frontier (D.region (S.depth + 1))) (D.region S.depth) :=
    hbar.mono Subset.rfl sdiff_subset
  by_cases hkn : k < returnTime j
  · obtain ⟨e₀⟩ := S.charts k hkn.le
    obtain ⟨e₁⟩ := S.charts (k + 1) (by omega)
    have hg₀ : EqOn (P.reference.g^[k]) e₀.chart (D.region S.depth) :=
      fun z hz => (P.iterate_eq_old hkn.le hz).trans (e₀.agrees z).symm
    have hnext : UniformContinuousOn (P.reference.g^[k + 1]) (D.region S.depth) :=
      e₁.forward_uniform.congr (fun z hz => (e₁.agrees z).trans
        (P.iterate_eq_old (by omega) hz).symm)
    have hclosed := e₀.tail.isClosed_image (D.geometry S.depth).1.isClosed
      (e₀.chart.continuousOn.mono e₀.contains)
    obtain ⟨r, hr, htube⟩ := hbarold
    apply uniformControlOn_iterate_image_of_local_chart e₀.chart e₀.contains hg₀ hclosed
      e₀.inverse_uniform hnext hr htube
    rintro _ ⟨z, hz, rfl⟩
    rw [e₀.agrees]
    exact Or.inl (Or.inl ((S.orbitTubes k hkn).subset (mem_image_of_mem _ hz)))
  · have hkn : k = returnTime j := by omega
    subst k
    have hBclosed : IsClosed (D.band S.depth) :=
      (D.geometry S.depth).1.isClosed.sdiff (D.openRegion_properties (S.depth + 2)).1
    have hBS : D.band S.depth ⊆ P.oldChart.chart.source := sdiff_subset.trans P.oldChart.contains
    have hclosed := (P.oldChart.tail.mono sdiff_subset).isClosed_image hBclosed
      (P.oldChart.chart.continuousOn.mono hBS)
    obtain ⟨r, hr, htube⟩ := hbar
    obtain ⟨d, hd, hdtube⟩ := exists_uniform_image_tube_of_uniform_inverse
      P.oldChart.chart hBS hclosed (P.oldChart.inverse_uniform.mono (image_mono sdiff_subset))
      hr htube
    have hc := uniformControlOn_of_eqOn_lipschitz (LipschitzWith.const (0 : ℂ))
      P.reference.barrier_eq hd (fun z hz => (hdtube z hz).trans interior_subset)
    have himage : (P.reference.g^[returnTime j]) '' frontier (D.region (S.depth + 1)) =
        P.oldChart.chart '' frontier (D.region (S.depth + 1)) :=
      image_congr (fun z hz => (P.iterate_eq_old le_rfl (hbarold.subset hz)).trans
        (P.oldChart.agrees z).symm)
    rw [himage]
    exact hc.mono_domain (fun _ hz => Or.inl (Or.inr hz))

/-- Lemma 2.5 preserves the reference map's strict trapping of the complete
boundary barrier. -/
theorem ContinuumReference.exists_barrier_tolerance (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
      (∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < δ) →
      MapsTo (F^[returnTime j + 1]) (frontier (D.region (S.depth + 1))) trappingDisk := by
  obtain ⟨δ, hδ, happrox⟩ := iterate_approximation_of_uniform_control P.reference.g
    P.controlSet (frontier (D.region (S.depth + 1))) (returnTime j + 1)
    (fun _ hk => P.barrier_uniformControl hζ hk) (1 / 4) (by norm_num)
  refine ⟨δ, hδ, fun F hclose z hz => ?_⟩
  have he := (happrox F hclose).1 (returnTime j + 1) le_rfl z hz
  rw [P.barrier_iterate_zero hζ hz, dist_zero_right] at he
  exact mem_closedBall_zero_iff.mpr (by linarith)

end EremenkosConjecture
