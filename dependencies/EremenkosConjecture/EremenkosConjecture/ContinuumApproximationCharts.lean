import EremenkosConjecture.ContinuumReferenceCharts
import EremenkosConjecture.LocalIterateStability

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

variable {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ}
  {S : ContinuumStage D j} {R : ContinuumReturnChannel D S.f j (S.depth + 3)}

/-- A sufficiently small entire approximation preserves every field of one
iterate chart on the next fixed inset. -/
theorem ContinuumReference.exists_chart_tolerance (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {k : ℕ} (hk : k ≤ returnTime (j + 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < δ) →
      Nonempty (LocalIterateChart F k (D.region (R.depth + 5))) := by
  obtain ⟨d, _⟩ := P.iterate_charts hζ hk
  let U := D.openRegion (R.depth + 2)
  have hU : IsOpen U := (D.openRegion_properties _).1
  have hUsub : U ⊆ D.region (R.depth + 1) :=
    ((D.openRegion_subset _).trans interior_subset).trans (D.region_antitone (by omega))
  let e := d.chart.restrOpen U hU
  have heS : e.source = U := inter_eq_right.mpr (hUsub.trans d.contains)
  have hei : DifferentiableOn ℂ e.symm e.target := d.inverse_holomorphic.mono inter_subset_left
  have htubeU : HasUniformTube U (D.region (R.depth + 1)) :=
    (D.region_tube_openRegion hζ (i := R.depth + 1) (n := R.depth + 2) (by omega)).mono
      ((D.openRegion_subset _).trans interior_subset)
      ((D.openRegion_subset _).trans interior_subset)
  have hcontrol : ∀ i < k, UniformControlOn P.reference.g P.controlSet
      ((P.reference.g^[i]) '' e.source) := by
    intro i hi
    rw [heS]
    exact P.uniformControl_iterate hζ htubeU (hi.trans_le hk)
  have hsmall : D.region (R.depth + 3) ⊆ D.region (R.depth + 1) :=
    D.region_antitone (by omega)
  have hSe : D.region (R.depth + 3) ⊆ e.source := by
    rw [heS]
    exact D.region_subset_openRegion hζ (by omega)
  have hAe : D.region (R.depth + 4) ⊆ e.source :=
    (D.region_antitone (by omega)).trans hSe
  have hclosed : IsClosed (e '' D.region (R.depth + 3)) :=
    (d.tail.mono hsmall).isClosed_image (D.geometry _).1.isClosed
      (d.chart.continuousOn.mono (hsmall.trans d.contains))
  have hinv : UniformContinuousOn e.symm (e '' D.region (R.depth + 3)) :=
    d.inverse_uniform.mono (image_mono hsmall)
  obtain ⟨r, hr, hsourceTube⟩ :=
    (D.region_tube_openRegion hζ (i := R.depth + 3) (n := R.depth + 4) (by omega)).mono
      Subset.rfl ((D.openRegion_subset _).trans interior_subset)
  obtain ⟨s, hs, himageTube⟩ := exists_uniform_image_tube_of_uniform_inverse
    e hSe hclosed hinv hr hsourceTube
  have himage : e '' D.region (R.depth + 3) ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hSe hz)
  obtain ⟨δ, hδ, happrox⟩ := approximate_local_iterate P.reference.g P.controlSet k e
    (fun z _ => (d.agrees z).symm) hei hcontrol hAe hs
    (fun z hz => (himageTube z hz).trans (interior_subset.trans himage))
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨δ, hδ, fun F hF hclose => ?_⟩
  obtain ⟨H, hH, L, L', hL, hL'⟩ := (happrox F hF hclose).1
  have hU₄ : D.openRegion (R.depth + 4) ⊆ D.region (R.depth + 4) :=
    (D.openRegion_subset _).trans interior_subset
  have h₄₁ : D.region (R.depth + 4) ⊆ D.region (R.depth + 1) := D.region_antitone (by omega)
  obtain ⟨d', _⟩ := exists_localIterateChart_on_source_of_image_change
    (P := D.region (R.depth + 5)) (U := D.openRegion (R.depth + 4)) d
    (hF.iterate k).differentiableOn (D.openRegion_properties (R.depth + 4)).1
    (D.openRegion_properties (R.depth + 4)).2.1 (hU₄.trans (h₄₁.trans d.contains))
    (D.region_subset_openRegion hζ (by omega)) (D.region_antitone (by omega))
    H hL hL' (by
      intro z hz
      change (F^[k]) z = H (d.chart z)
      exact (hH (hU₄ hz)).trans (congrArg H (d.agrees z).symm))
  exact ⟨d'⟩

end EremenkosConjecture
