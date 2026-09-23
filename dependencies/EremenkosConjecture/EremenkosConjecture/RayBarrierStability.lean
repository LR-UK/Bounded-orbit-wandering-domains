import EremenkosConjecture.RayReferenceOrbits

/-! # Uniform trapping of the boundary barrier -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

namespace RayReference

variable {j : ℕ} {S : RayStage j} {R : RayReturnChannel S.f j S.a S.b}
    (P : RayReference S R)

theorem frontier_core_subset_region : frontier S.core ⊆ S.region := by
  apply ((isClosed_closedHalfStrip rayBase S.a S.b).frontier_subset).trans
  intro z hz
  exact ⟨by linarith [hz.1, S.a_pos], hz.2.trans (by linarith [S.b_pos])⟩

theorem frontier_core_tube_region : HasUniformTube (frontier S.core) S.region :=
  (hasUniformTube_halfStrip (ζ := rayBase) (show S.a < 2 * S.a by linarith [S.a_pos])
    (show S.b < 2 * S.b by linarith [S.b_pos])).mono
      (isClosed_closedHalfStrip rayBase S.a S.b).frontier_subset Subset.rfl

theorem barrier_iterate_zero {z : ℂ} (hz : z ∈ frontier S.core) :
    (P.g^[returnTime j + 1]) z = 0 := by
  rw [iterate_succ_apply', P.iterate_eq_old le_rfl ((frontier_core_subset_region (S := S)) hz),
    P.extension ((frontier_core_subset_region (S := S)) hz)]
  exact P.barrier_eq _ (mem_image_of_mem _
    ((hasUniformTube_frontier_rayBand S.a_pos S.b_pos).subset hz))

theorem barrier_uniformControl {k : ℕ} (hk : k < returnTime j + 1) :
    UniformControlOn P.g P.controlSet ((P.g^[k]) '' frontier S.core) := by
  by_cases hkn : k < returnTime j
  · obtain ⟨H₀, he₀, L₀, L₀', hL₀, hL₀'⟩ := S.extensions k hkn.le
    obtain ⟨H₁, he₁, L₁, L₁', hL₁, hL₁'⟩ := S.extensions (k + 1) (by omega)
    have hg₀ : EqOn (P.g^[k]) H₀ S.region := fun z hz => (P.iterate_eq_old hkn.le hz).trans (he₀ hz)
    have hg₁ : EqOn (P.g^[k + 1]) H₁ S.region := fun z hz =>
      (P.iterate_eq_old (by omega) hz).trans (he₁ hz)
    obtain ⟨r, hr, htube⟩ := (frontier_core_tube_region (S := S))
    apply uniformControlOn_iterate_image H₀ H₁ hg₀ hg₁ hL₀' hL₁ hr htube
    rintro _ ⟨z, hz, rfl⟩
    rw [← he₀ hz]
    exact Or.inl (Or.inl ((S.orbitTubes k hkn).subset (mem_image_of_mem _ hz)))
  · have hkn : k = returnTime j := by omega
    subst k
    obtain ⟨L, L', hL, hL'⟩ := P.quantitative
    obtain ⟨r, hr, htube⟩ := (hasUniformTube_frontier_rayBand S.a_pos S.b_pos).image P.H hL'
    have hc := uniformControlOn_of_eqOn_lipschitz (LipschitzWith.const (0 : ℂ))
      P.barrier_eq hr htube
    have himage : (P.g^[returnTime j]) '' frontier S.core = P.H '' frontier S.core :=
      image_congr (fun z hz => (P.iterate_eq_old le_rfl ((frontier_core_subset_region (S := S)) hz)).trans
        (P.extension ((frontier_core_subset_region (S := S)) hz)))
    rw [himage]
    exact hc.mono_domain (fun _ hz => Or.inl (Or.inr hz))

theorem exists_barrier_tolerance : ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℂ → ℂ,
    (∀ z ∈ P.controlSet, dist (F z) (P.g z) < δ) →
    MapsTo (F^[returnTime j + 1]) (frontier S.core) trappingDisk := by
  obtain ⟨δ, hδ, Hδ⟩ := iterate_approximation_of_uniform_control P.g P.controlSet
    (frontier S.core) (returnTime j + 1) (fun _ hk => P.barrier_uniformControl hk) (1 / 4) (by norm_num)
  refine ⟨δ, hδ, fun F hclose z hz => ?_⟩
  have he := (Hδ F hclose).1 (returnTime j + 1) le_rfl z hz
  rw [P.barrier_iterate_zero hz, dist_zero_right] at he
  exact mem_closedBall_zero_iff.mpr (by linarith)

end RayReference

end EremenkosConjecture
