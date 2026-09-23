import EremenkosConjecture.VariableReferenceMap

/-! # Finite orbits of the piecewise reference map -/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture
namespace VariableConstruction

theorem old_orbit_mem_control (D : UniformEscapeData) {n : ℕ} {S : DiscSchedule n} {f : ℂ → ℂ}
    (hs : StageProperty D S f) {j k : ℕ} (hkj : k ≤ j) (hkn : k < n)
    {z : ℂ} (hz : z ∈ D.K j) : (f^[k]) z ∈ variableControlDisc (S.radius n) :=
  interior_subset (S.target_subset_control_interior hkn le_rfl
    (hs.2.1 k hkn.le (D.antitone hkj hz)))

namespace ReferenceMapData

variable {D : UniformEscapeData} {n : ℕ} {S : DiscSchedule n} {b : ℝ} {f : ℂ → ℂ}

theorem old_iterates_eq_nhds (R : ReferenceMapData D S b f)
    (hf : Continuous f) (hs : StageProperty D S f)
    (j k : ℕ) (hkj : k ≤ j + 1) (hkn : k ≤ n) {z : ℂ} (hz : z ∈ D.K j) :
    (R.g^[k]) =ᶠ[𝓝 z] (f^[k]) := by
  apply ComplexDynamics.eventuallyEq_iterate_of_orbit f R.g hf k z
  intro i hi
  exact R.old_eq _ (old_orbit_mem_control D hs (by omega) (by omega) hz)

theorem next_iterate_eq_nhds (R : ReferenceMapData D S b f)
    (hf : Continuous f) (hs : StageProperty D S f) {z : ℂ} (hz : z ∈ D.K (n + 1)) :
    (R.g^[n + 1]) =ᶠ[𝓝 z] (fun w => (f^[n]) w + ((b - S.center n : ℝ) : ℂ)) := by
  have hi := R.old_iterates_eq_nhds hf hs (n + 1) n (by omega) le_rfl hz
  have hc := (R.translate_eq _ (mem_image_of_mem _ hz)).comp_tendsto
    (hf.iterate n).continuousAt
  simpa only [iterate_succ', Function.comp_def] using (hi.fun_comp R.g).trans hc

theorem stageProperty (R : ReferenceMapData D S b f)
    (hf : Continuous f) (hs : StageProperty D S f)
    (T : DiscSchedule (n + 1)) (hT : ∀ j ≤ n, T.center j = S.center j)
    (hb : T.center (n + 1) = b) : StageProperty D T R.g := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [(R.old_eq z (S.initial_control_subset hz)).eq_of_nhds]
    exact hs.1 hz
  · intro j hj z hz
    by_cases hjn : j ≤ n
    · rw [(R.old_iterates_eq_nhds hf hs j j (by omega) hjn hz).eq_of_nhds]
      rw [hT j hjn]
      exact hs.2.1 j hjn hz
    · have hjeq : j = n + 1 := by omega
      subst j
      rw [(R.next_iterate_eq_nhds hf hs hz).eq_of_nhds]
      rw [hb]
      exact translate_mem_variableTargetDisc (hs.2.1 n le_rfl (D.antitone (by omega) hz))
  · intro j hj
    by_cases hjn : j ≤ n
    · exact (hs.2.2.1 j hjn).congr_nhds (fun z hz =>
        (R.old_iterates_eq_nhds hf hs j j (by omega) hjn hz).symm)
    · have hjeq : j = n + 1 := by omega
      subst j
      exact ((hs.2.2.1 n le_rfl).mono (D.antitone (by omega))).add_const ((b - S.center n : ℝ) : ℂ) |>.congr_nhds
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

theorem orbit_compact (R : ReferenceMapData D S b f)
    (hf : Continuous f) (hs : StageProperty D S f)
    (j : ℕ) (hj : j ≤ n + 1) (k : ℕ) (hk : k < j) :
    MapsTo (R.g^[k]) (D.K j) (interior R.A) := by
  intro z hz
  have hkn : k ≤ n := by omega
  rw [(R.old_iterates_eq_nhds hf hs j k (by omega) hkn hz).eq_of_nhds]
  by_cases hlt : k < n
  · exact R.control (old_orbit_mem_control D hs (by omega) hlt hz)
  · have hkeq : k = n := by omega
    have hjeq : j = n + 1 := by omega
    subst k
    subst j
    exact R.next (mem_image_of_mem _ hz)

theorem orbit_points (R : ReferenceMapData D S b f)
    (hf : Continuous f) (hs : StageProperty D S f)
    (j : ℕ) (hj : j < n + 1) (k : ℕ) (hk : k < j + 1) :
    MapsTo (R.g^[k]) (D.P j) (interior R.A) := by
  intro z hz
  have hkn : k ≤ n := by omega
  rw [(R.old_iterates_eq_nhds hf hs j k (by omega) hkn (D.points_subset j hz)).eq_of_nhds]
  by_cases hlt : k < n
  · exact R.control (old_orbit_mem_control D hs (by omega) hlt (D.points_subset j hz))
  · have hkeq : k = n := by omega
    have hjeq : j = n := by omega
    subst k
    subst j
    exact R.points (mem_image_of_mem _ hz)

theorem approximationStable (R : ReferenceMapData D S b f)
    (hf : Continuous f) (hs : StageProperty D S f)
    (T : DiscSchedule (n + 1)) (hT : ∀ j ≤ n, T.center j = S.center j)
    (hb : T.center (n + 1) = b) :
    ApproximationStable R.g (interior R.A) (StageProperty D T) :=
  stageProperty_approximationStable D R.g (interior R.A) isOpen_interior
    (R.holomorphic.mono (interior_subset.trans R.subset)) T (R.stageProperty hf hs T hT hb)
    (fun _ hz => R.control (S.initial_control_subset hz))
    (R.orbit_compact hf hs) (R.orbit_points hf hs)

end ReferenceMapData

/-- Extend an orbit itinerary to any sufficiently distant next target. The
additional bound on the old boundary images will certify transcendence. -/
theorem exists_polynomial_extension (D : UniformEscapeData) {n : ℕ}
    (S : DiscSchedule n) (r : ℝ) (hr : S.radius n + 5 < r)
    (p : Polynomial ℂ) (hp : StageProperty D S p.eval) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Polynomial ℂ, StageProperty D (S.extend r hr) q.eval ∧
      (∀ z ∈ variableControlDisc (S.radius n), ‖q.eval z - p.eval z‖ < ε) ∧
      ∀ z ∈ (p.eval^[n]) '' D.P n, ‖q.eval z - (-3)‖ < ε := by
  obtain ⟨R⟩ := exists_reference_map D S r p.eval p.differentiable hp
  obtain ⟨δ, hδ, Hδ⟩ := R.approximationStable p.continuous hp (S.extend r hr)
    (fun j hj => S.extend_center_old r hr hj) (S.extend_center_new r hr)
  obtain ⟨q, hq⟩ := Runge.polynomial_approximation_of_holomorphic R.A R.compact R.full
    R.U R.isOpen R.subset R.g R.holomorphic (min δ ε) (lt_min hδ hε)
  refine ⟨q, Hδ q.eval q.differentiable.differentiableOn ?_, ?_, ?_⟩
  · intro z hz
    have H := (hq z (interior_subset hz)).trans_le (min_le_left _ _)
    simpa only [dist_eq_norm, norm_sub_rev] using H
  · intro z hz
    have H := (hq z (interior_subset (R.control hz))).trans_le (min_le_right _ _)
    rw [(R.old_eq z hz).eq_of_nhds] at H
    simpa only [norm_sub_rev] using H
  · intro z hz
    have H := (hq z (interior_subset (R.points hz))).trans_le (min_le_right _ _)
    rw [(R.trap_eq z hz).eq_of_nhds] at H
    simpa only [norm_sub_rev] using H

end VariableConstruction
end EremenkosConjecture

