import EremenkosConjecture.RayReference

/-! # Exact orbit identities for the glued reference map -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

namespace RayReference

variable {j : ℕ} {S : RayStage j} {R : RayReturnChannel S.f j S.a S.b}
    (P : RayReference S R)

theorem iterate_eq_old {k : ℕ} (hk : k ≤ returnTime j) :
    EqOn (P.g^[k]) (S.f^[k]) S.region := by
  intro z hz
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iterate_succ_apply', iterate_succ_apply', ih (by omega)]
      apply P.background_eq
      exact (S.orbitTubes k (by omega)).subset (mem_image_of_mem _ hz)

theorem iterate_eq_return {k : ℕ} (hk : k ≤ j + 1) :
    EqOn (P.g^[returnTime j + 1 + k]) (fun z => (S.f^[k]) (R.ψ z)) R.inner := by
  intro z hz
  change (P.g^[returnTime j + 1 + k]) z = (S.f^[k]) (R.ψ z)
  induction k with
  | zero =>
      simp only [add_zero, iterate_zero, id_eq]
      rw [iterate_succ_apply', P.iterate_eq_old le_rfl (S.inner_subset_region R.η_small hz),
        P.extension (S.inner_subset_region R.η_small hz)]
      exact P.return_eq z hz
  | succ k ih =>
      rw [show returnTime j + 1 + (k + 1) = (returnTime j + 1 + k) + 1 by omega,
        iterate_succ_apply', ih (by omega), iterate_succ_apply']
      apply P.background_eq
      exact sourceStrips_subset_background j (mem_iUnion.mpr
        ⟨k, insetSourceStrip_subset k (R.orbit k (by omega) (R.inner_subset_domain S.b_small hz))⟩)

theorem iterate_extensions {k : ℕ} (hk : k ≤ returnTime (j + 1)) :
    HasQuantitativeExtensionOn (P.g^[k]) R.inner := by
  by_cases hkn : k ≤ returnTime j
  · obtain ⟨H, he, L, L', hL, hL'⟩ := S.extensions k hkn
    exact ⟨H, fun z hz => (P.iterate_eq_old hkn (S.inner_subset_region R.η_small hz)).trans
      (he (S.inner_subset_region R.η_small hz)), L, L', hL, hL'⟩
  · let i := k - (returnTime j + 1)
    have hi : i ≤ j + 1 := by dsimp [i]; rw [returnTime_succ] at hk; omega
    have hki : k = returnTime j + 1 + i := by dsimp [i]; omega
    obtain ⟨H, he, L, L', hL, hL'⟩ := R.extensions i hi
    exact ⟨H, fun z hz => (hki ▸ P.iterate_eq_return hi hz).trans (he hz), L, L', hL, hL'⟩

theorem mapsTo_controlSet {k : ℕ} (hk : k < returnTime (j + 1)) :
    MapsTo (P.g^[k]) R.inner P.controlSet := by
  intro z hz
  by_cases hkn : k < returnTime j
  · rw [P.iterate_eq_old hkn.le (S.inner_subset_region R.η_small hz)]
    exact Or.inl (Or.inl ((S.orbitTubes k hkn).subset
      (mem_image_of_mem _ (S.inner_subset_region R.η_small hz))))
  · by_cases he : k = returnTime j
    · rw [he, P.iterate_eq_old le_rfl (S.inner_subset_region R.η_small hz),
        P.extension (S.inner_subset_region R.η_small hz)]
      exact Or.inr (mem_image_of_mem _ hz)
    · let i := k - (returnTime j + 1)
      have hi : i < j + 1 := by dsimp [i]; rw [returnTime_succ] at hk; omega
      have hki : k = returnTime j + 1 + i := by dsimp [i]; omega
      have hi' : (P.g^[k]) z = (S.f^[i]) (R.ψ z) := hki ▸ P.iterate_eq_return hi.le hz
      rw [hi']
      exact Or.inl (Or.inl (sourceStrips_subset_background j (mem_iUnion.mpr
        ⟨i, insetSourceStrip_subset i (R.orbit i hi (R.inner_subset_domain S.b_small hz))⟩)))

theorem iterate_holomorphic {k : ℕ} (hk : k ≤ returnTime (j + 1)) :
    DifferentiableOn ℂ (P.g^[k]) R.inner :=
  ComplexDynamics.differentiableOn_iterate_of_mapsTo P.g P.D R.inner P.holomorphic k
    (fun i hi z hz => P.subset_domain (P.mapsTo_controlSet (hi.trans_le hk) hz))

theorem uniformControl_iterate {U : Set ℂ} (htube : HasUniformTube U R.inner)
    {k : ℕ} (hk : k < returnTime (j + 1)) :
    UniformControlOn P.g P.controlSet ((P.g^[k]) '' U) := by
  obtain ⟨H₀, he₀, L₀, L₀', hL₀, hL₀'⟩ := P.iterate_extensions hk.le
  obtain ⟨H₁, he₁, L₁, L₁', hL₁, hL₁'⟩ := P.iterate_extensions (Nat.succ_le_of_lt hk)
  obtain ⟨r, hr, htube⟩ := htube
  apply uniformControlOn_iterate_image H₀ H₁ he₀ he₁ hL₀' hL₁ hr htube
  rintro _ ⟨z, hz, rfl⟩
  rw [← he₀ hz]
  exact P.mapsTo_controlSet hk hz

theorem orbit_tubes {k : ℕ} (hk : k < returnTime (j + 1)) :
    HasUniformTube ((P.g^[k]) '' R.inner) (background (j + 1)) := by
  by_cases hkn : k < returnTime j
  · apply (S.orbitTubes k hkn).mono _ (background_monotone (Nat.le_succ j))
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, S.inner_subset_region R.η_small hz,
      (P.iterate_eq_old hkn.le (S.inner_subset_region R.η_small hz)).symm⟩
  · by_cases he : k = returnTime j
    · refine ⟨1 / 4, by norm_num, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply ball_target_subset_next_background
      rw [he, P.iterate_eq_old le_rfl (S.inner_subset_region R.η_small hz)]
      exact S.mapsTo_region_target (S.inner_subset_region R.η_small hz)
    · let i := k - (returnTime j + 1)
      have hi : i < j + 1 := by dsimp [i]; rw [returnTime_succ] at hk; omega
      have hki : k = returnTime j + 1 + i := by dsimp [i]; omega
      refine ⟨1 / 10, by norm_num, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have hi' : (P.g^[k]) z = (S.f^[i]) (R.ψ z) := hki ▸ P.iterate_eq_return hi.le hz
      rw [hi']
      exact ball_inset_subset_background (j + 1) i
        (R.orbit i hi (R.inner_subset_domain S.b_small hz))

end RayReference

end EremenkosConjecture
