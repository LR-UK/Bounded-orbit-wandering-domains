import EremenkosConjecture.ReferenceMap

/-! # Finite orbits of the piecewise reference map -/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture
namespace UniformEscapeData

theorem old_orbit_mem_control (D : UniformEscapeData) {n : ℕ} {f : ℂ → ℂ}
    (hs : D.StageProperty n f) {j k : ℕ} (hkj : k ≤ j) (hkn : k < n)
    {z : ℂ} (hz : z ∈ D.K j) : (f^[k]) z ∈ controlDisc n :=
  interior_subset (targetDisc_subset_controlDisc_interior hkn
    (hs.2.1 k hkn.le (D.antitone hkj hz)))

namespace ReferenceMapData

variable {D : UniformEscapeData} {n : ℕ} {f : ℂ → ℂ}

theorem old_iterates_eq_nhds (R : D.ReferenceMapData n f)
    (hf : Continuous f) (hs : D.StageProperty n f)
    (j k : ℕ) (hkj : k ≤ j + 1) (hkn : k ≤ n) {z : ℂ} (hz : z ∈ D.K j) :
    (R.g^[k]) =ᶠ[𝓝 z] (f^[k]) := by
  apply ComplexDynamics.eventuallyEq_iterate_of_orbit f R.g hf k z
  intro i hi
  exact R.old_eq _ (D.old_orbit_mem_control hs (by omega) (by omega) hz)

theorem next_iterate_eq_nhds (R : D.ReferenceMapData n f)
    (hf : Continuous f) (hs : D.StageProperty n f) {z : ℂ} (hz : z ∈ D.K (n + 1)) :
    (R.g^[n + 1]) =ᶠ[𝓝 z] (fun w => (f^[n]) w + 3) := by
  have hi := R.old_iterates_eq_nhds hf hs (n + 1) n (by omega) le_rfl hz
  have hc := (R.translate_eq _ (mem_image_of_mem _ hz)).comp_tendsto
    (hf.iterate n).continuousAt
  simpa only [iterate_succ', Function.comp_def] using (hi.fun_comp R.g).trans hc

theorem stageProperty (R : D.ReferenceMapData n f)
    (hf : Continuous f) (hs : D.StageProperty n f) : D.StageProperty (n + 1) R.g := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [(R.old_eq z (controlDisc_mono (Nat.zero_le n) hz)).eq_of_nhds]
    exact hs.1 hz
  · intro j hj z hz
    by_cases hjn : j ≤ n
    · rw [(R.old_iterates_eq_nhds hf hs j j (by omega) hjn hz).eq_of_nhds]
      exact hs.2.1 j hjn hz
    · have hjeq : j = n + 1 := by omega
      subst j
      rw [(R.next_iterate_eq_nhds hf hs hz).eq_of_nhds]
      exact add_three_mem_targetDisc (hs.2.1 n le_rfl (D.antitone (by omega) hz))
  · intro j hj
    by_cases hjn : j ≤ n
    · exact (hs.2.2.1 j hjn).congr_nhds (fun z hz =>
        (R.old_iterates_eq_nhds hf hs j j (by omega) hjn hz).symm)
    · have hjeq : j = n + 1 := by omega
      subst j
      exact ((hs.2.2.1 n le_rfl).mono (D.antitone (by omega))).add_const 3 |>.congr_nhds
        (fun z hz => (R.next_iterate_eq_nhds hf hs hz).symm)
  · intro j hj z hz
    by_cases hjn : j < n
    · rw [(R.old_iterates_eq_nhds hf hs j (j + 1) le_rfl (by omega)
        (D.points_subset j hz)).eq_of_nhds]
      exact hs.2.2.2 j hjn hz
    · have hjeq : j = n := by omega
      subst j
      rw [iterate_succ_apply', (R.old_iterates_eq_nhds hf hs n n (by omega) le_rfl
        (D.points_subset n hz)).eq_of_nhds]
      rw [(R.trap_eq _ (mem_image_of_mem _ hz)).eq_of_nhds]
      exact mem_ball_self (by norm_num)

theorem orbit_compact (R : D.ReferenceMapData n f)
    (hf : Continuous f) (hs : D.StageProperty n f)
    (j : ℕ) (hj : j ≤ n + 1) (k : ℕ) (hk : k < j) :
    MapsTo (R.g^[k]) (D.K j) (interior R.A) := by
  intro z hz
  have hkn : k ≤ n := by omega
  rw [(R.old_iterates_eq_nhds hf hs j k (by omega) hkn hz).eq_of_nhds]
  by_cases hlt : k < n
  · exact R.control (D.old_orbit_mem_control hs (by omega) hlt hz)
  · have hkeq : k = n := by omega
    have hjeq : j = n + 1 := by omega
    subst k
    subst j
    exact R.next (mem_image_of_mem _ hz)

theorem orbit_points (R : D.ReferenceMapData n f)
    (hf : Continuous f) (hs : D.StageProperty n f)
    (j : ℕ) (hj : j < n + 1) (k : ℕ) (hk : k < j + 1) :
    MapsTo (R.g^[k]) (D.P j) (interior R.A) := by
  intro z hz
  have hkn : k ≤ n := by omega
  rw [(R.old_iterates_eq_nhds hf hs j k (by omega) hkn (D.points_subset j hz)).eq_of_nhds]
  by_cases hlt : k < n
  · exact R.control (D.old_orbit_mem_control hs (by omega) hlt (D.points_subset j hz))
  · have hkeq : k = n := by omega
    have hjeq : j = n := by omega
    subst k
    subst j
    exact R.points (mem_image_of_mem _ hz)

theorem approximationStable (R : D.ReferenceMapData n f)
    (hf : Continuous f) (hs : D.StageProperty n f) :
    ApproximationStable R.g (interior R.A) (D.StageProperty (n + 1)) :=
  D.stageProperty_approximationStable R.g (interior R.A) isOpen_interior
    (R.holomorphic.mono (interior_subset.trans R.subset)) (n + 1) (R.stageProperty hf hs)
    (fun _ hz => R.control (controlDisc_mono (Nat.zero_le n) hz))
    (R.orbit_compact hf hs) (R.orbit_points hf hs)

end ReferenceMapData

/-- The polynomial-extension step: all existing finite-stage properties persist,
one more stage is realised, and the change on the old control disk can be made
arbitrarily small. -/
theorem exists_polynomial_extension (D : UniformEscapeData) (n : ℕ)
    (p : Polynomial ℂ) (hp : D.StageProperty n p.eval) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Polynomial ℂ, D.StageProperty (n + 1) q.eval ∧
      ∀ z ∈ controlDisc n, ‖q.eval z - p.eval z‖ < ε := by
  obtain ⟨R⟩ := D.exists_reference_map n p.eval p.differentiable hp
  obtain ⟨δ, hδ, Hδ⟩ := R.approximationStable p.continuous hp
  obtain ⟨q, hq⟩ := Runge.polynomial_approximation_of_holomorphic R.A R.compact R.full
    R.U R.isOpen R.subset R.g R.holomorphic (min δ ε) (lt_min hδ hε)
  refine ⟨q, Hδ q.eval q.differentiable.differentiableOn ?_, ?_⟩
  · intro z hz
    have H := (hq z (interior_subset hz)).trans_le (min_le_left _ _)
    simpa only [dist_eq_norm, norm_sub_rev] using H
  · intro z hz
    have H := (hq z (interior_subset (R.control hz))).trans_le (min_le_right _ _)
    rw [(R.old_eq z hz).eq_of_nhds] at H
    simpa only [norm_sub_rev] using H

end UniformEscapeData
end EremenkosConjecture
