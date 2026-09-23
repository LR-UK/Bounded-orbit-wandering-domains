import EremenkosConjecture.ContinuumReference

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding

variable {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ}
  {S : ContinuumStage D j} {R : ContinuumReturnChannel D S.f j (S.depth + 3)}

theorem ContinuumReference.inner_subset_old (P : ContinuumReference S R) :
    D.region R.depth ⊆ D.region S.depth := D.region_antitone (by have := R.later; omega)

theorem ContinuumReference.iterate_eq_old (P : ContinuumReference S R)
    {k : ℕ} (hk : k ≤ returnTime j) :
    EqOn (P.reference.g^[k]) (S.f^[k]) (D.region S.depth) :=
  P.reference.iterate_eq_old hk
    (fun i hi z hz => (S.orbitTubes i hi).subset (mem_image_of_mem _ hz))

theorem ContinuumReference.iterate_eq_return (P : ContinuumReference S R)
    {k : ℕ} (hk : k ≤ j + 1) :
    EqOn (P.reference.g^[returnTime j + 1 + k]) (fun z => (S.f^[k]) (R.ψ z))
      (D.region R.depth) :=
  P.reference.iterate_eq_return hk
    (fun i hi z hz => (S.orbitTubes i hi).subset (mem_image_of_mem _ (P.inner_subset_old hz)))
    (fun z _ => (P.oldChart.agrees z).symm)
    (fun i hi z hz => sourceStrips_subset_background j (mem_iUnion.mpr
      ⟨i, insetSourceStrip_subset i (R.orbit i hi (R.region_subset hz))⟩))

theorem ContinuumReference.mapsTo_controlSet (P : ContinuumReference S R)
    {k : ℕ} (hk : k < returnTime (j + 1)) :
    MapsTo (P.reference.g^[k]) (D.region R.depth) P.controlSet := by
  apply P.reference.mapsTo_controlSet (N := returnTime j) (m := j + 1)
    (by rw [returnTime_succ] at hk; omega)
    (fun i hi z hz => (S.orbitTubes i hi).subset (mem_image_of_mem _ (P.inner_subset_old hz)))
    (fun z _ => (P.oldChart.agrees z).symm)
    (fun i hi z hz => sourceStrips_subset_background j (mem_iUnion.mpr
      ⟨i, insetSourceStrip_subset i (R.orbit i hi (R.region_subset hz))⟩))

theorem ContinuumReference.iterate_holomorphic (P : ContinuumReference S R)
    {k : ℕ} (hk : k ≤ returnTime (j + 1)) :
    DifferentiableOn ℂ (P.reference.g^[k]) (D.region R.depth) :=
  ComplexDynamics.differentiableOn_iterate_of_mapsTo P.reference.g P.reference.domain
    (D.region R.depth) P.reference.holomorphic k
    (fun i hi z hz => P.reference.contains (P.mapsTo_controlSet (hi.trans_le hk) hz))

theorem ContinuumReference.orbit_tubes (P : ContinuumReference S R)
    {k : ℕ} (hk : k < returnTime (j + 1)) :
    HasUniformTube ((P.reference.g^[k]) '' D.region R.depth) (background (j + 1)) := by
  by_cases hkn : k < returnTime j
  · apply (S.orbitTubes k hkn).mono _ (background_monotone (Nat.le_succ j))
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, P.inner_subset_old hz, (P.iterate_eq_old hkn.le (P.inner_subset_old hz)).symm⟩
  · by_cases he : k = returnTime j
    · refine ⟨1 / 4, by norm_num, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply ball_target_subset_next_background
      have heq : (P.reference.g^[k]) z = (S.f^[returnTime j]) z :=
        he ▸ P.iterate_eq_old le_rfl (P.inner_subset_old hz)
      rw [heq]
      exact S.mapsTo_region_target (P.inner_subset_old hz)
    · let i := k - (returnTime j + 1)
      have hi : i < j + 1 := by dsimp [i]; rw [returnTime_succ] at hk; omega
      have hki : k = returnTime j + 1 + i := by dsimp [i]; omega
      refine ⟨1 / 10, by norm_num, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have heq : (P.reference.g^[k]) z = (S.f^[i]) (R.ψ z) :=
        hki ▸ P.iterate_eq_return hi.le hz
      rw [heq]
      exact ball_inset_subset_background (j + 1) i (R.orbit i hi (R.region_subset hz))

theorem ContinuumReference.target_margin (P : ContinuumReference S R) :
    ∀ z ∈ D.region R.depth,
      (height (j + 1) + 7) / 4 + 1 / 4 ≤ ((P.reference.g^[returnTime (j + 1)]) z).im ∧
      ((P.reference.g^[returnTime (j + 1)]) z).im ≤ (height (j + 1) + 11) / 4 - 1 / 4 := by
  intro z hz
  have heq : (P.reference.g^[returnTime (j + 1)]) z = (S.f^[j + 1]) (R.ψ z) := by
    convert P.iterate_eq_return (k := j + 1) le_rfl hz using 1 <;>
      congr 1 <;> simp only [returnTime_succ] <;> omega
  rw [heq]
  exact R.target z (R.region_subset hz)

end EremenkosConjecture
