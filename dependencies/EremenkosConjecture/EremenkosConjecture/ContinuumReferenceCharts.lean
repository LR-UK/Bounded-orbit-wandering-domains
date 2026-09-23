import EremenkosConjecture.ContinuumReferenceOrbits
import EremenkosConjecture.LocalChartImageChange
import EremenkosConjecture.LocalChartMargins
import EremenkosConjecture.IterateApproximation

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

variable {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ}
  {S : ContinuumStage D j} {R : ContinuumReturnChannel D S.f j (S.depth + 3)}

/-- All reference iterates have local charts on one common closed buffer. -/
theorem ContinuumReference.iterate_charts (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {k : ℕ} (hk : k ≤ returnTime (j + 1)) :
    ∃ E : LocalIterateChart P.reference.g k (D.region (R.depth + 1)),
      E.chart.source = D.openRegion R.depth := by
  have hU : D.openRegion R.depth ⊆ D.region R.depth :=
    (D.openRegion_subset R.depth).trans interior_subset
  have hP : D.region (R.depth + 1) ⊆ D.openRegion R.depth :=
    D.region_subset_openRegion hζ (by omega)
  have hhol := (P.iterate_holomorphic hk).mono hU
  by_cases hkn : k ≤ returnTime j
  · obtain ⟨e⟩ := S.charts k hkn
    apply exists_localIterateChart_on_source_of_image_change e hhol
      (D.openRegion_properties R.depth).1 (D.openRegion_properties R.depth).2.1
      (hU.trans (P.inner_subset_old.trans e.contains)) hP
      (hP.trans (hU.trans P.inner_subset_old)) (Homeomorph.refl ℂ)
      isometry_id.lipschitzWith isometry_id.lipschitzWith
    intro z hz
    change (P.reference.g^[k]) z = e.chart z
    exact (P.iterate_eq_old hkn (P.inner_subset_old (hU hz))).trans (e.agrees z).symm
  · let i := k - (returnTime j + 1)
    have hi : i ≤ j + 1 := by dsimp [i]; rw [returnTime_succ] at hk; omega
    have hki : k = returnTime j + 1 + i := by dsimp [i]; omega
    obtain ⟨e, _⟩ := R.charts i hi
    apply exists_localIterateChart_on_source_of_image_change e hhol
      (D.openRegion_properties R.depth).1 (D.openRegion_properties R.depth).2.1
      (hU.trans e.contains) hP (hP.trans hU) (Homeomorph.refl ℂ)
      isometry_id.lipschitzWith isometry_id.lipschitzWith
    intro z hz
    change (P.reference.g^[k]) z = e.chart z
    have heq : (P.reference.g^[k]) z = (S.f^[i]) (R.ψ z) :=
      hki ▸ P.iterate_eq_return hi (hU hz)
    exact heq.trans (e.agrees z).symm

/-- The space between nested neighbourhoods supplies the hypotheses of
the Section 2 finite-iterate approximation lemma. -/
theorem ContinuumReference.uniformControl_iterate (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {A : Set ℂ}
    (htube : HasUniformTube A (D.region (R.depth + 1)))
    {k : ℕ} (hk : k < returnTime (j + 1)) :
    UniformControlOn P.reference.g P.controlSet ((P.reference.g^[k]) '' A) := by
  obtain ⟨e₀, _⟩ := P.iterate_charts hζ hk.le
  obtain ⟨e₁, _⟩ := P.iterate_charts hζ (Nat.succ_le_of_lt hk)
  obtain ⟨r, hr, htube⟩ := htube
  have hclosed := e₀.tail.isClosed_image (D.geometry (R.depth + 1)).1.isClosed
    (e₀.chart.continuousOn.mono e₀.contains)
  have hnext : UniformContinuousOn (P.reference.g^[k + 1]) (D.region (R.depth + 1)) :=
    e₁.forward_uniform.congr (fun z _ => e₁.agrees z)
  apply uniformControlOn_iterate_image_of_local_chart e₀.chart e₀.contains
    (fun z _ => (e₀.agrees z).symm) hclosed e₀.inverse_uniform hnext hr htube
  rintro _ ⟨z, hz, rfl⟩
  rw [e₀.agrees]
  exact P.mapsTo_controlSet hk (D.region_antitone (by omega) hz)

theorem ContinuumReference.exists_iterate_tolerance (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
      (∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < δ) →
      ∀ k ≤ returnTime (j + 1), ∀ z ∈ D.openRegion (R.depth + 2),
        dist ((F^[k]) z) ((P.reference.g^[k]) z) < ε := by
  have htube : HasUniformTube (D.openRegion (R.depth + 2)) (D.region (R.depth + 1)) :=
    (D.region_tube_openRegion hζ (i := R.depth + 1) (n := R.depth + 2) (by omega)).mono
      ((D.openRegion_subset _).trans interior_subset)
      ((D.openRegion_subset _).trans interior_subset)
  obtain ⟨δ, hδ, happrox⟩ := iterate_approximation_of_uniform_control P.reference.g
    P.controlSet (D.openRegion (R.depth + 2)) (returnTime (j + 1))
    (fun _ hk => P.uniformControl_iterate hζ htube hk) ε hε
  exact ⟨δ, hδ, fun F hclose => (happrox F hclose).1⟩

end EremenkosConjecture
