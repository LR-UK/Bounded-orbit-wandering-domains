import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Full compact sets and complementary components

Elementary plane topology and the maximum principle relate connected
complements to polynomial separation. These facts support the neighbourhood
constructions used in Section 2.
-/

open Set Metric Function Bornology
open scoped Topology

namespace EremenkosConjecture

theorem isConnected_exterior (R : ℝ) (hR : 0 < R) :
    IsConnected {z : ℂ | R < ‖z‖} := by
  have hh : IsConnected {z : ℂ | Real.log R < z.re} :=
    (convex_halfSpace_re_gt (Real.log R)).isConnected
      ⟨((Real.log R + 1 : ℝ) : ℂ), by simp⟩
  have heq : Complex.exp '' {z : ℂ | Real.log R < z.re} = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change R < ‖Complex.exp w‖
      rw [Complex.norm_exp, ← Real.exp_log hR]
      exact Real.exp_lt_exp.mpr hw
    · intro hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans hz)
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      change Real.log R < (Complex.log z).re
      rw [Complex.log_re]
      exact Real.log_lt_log hR hz
  rw [← heq]
  exact hh.image Complex.exp Complex.continuous_exp.continuousOn

/-- For a bounded plane set, if every complementary component is unbounded,
the complement is connected. -/
theorem isConnected_compl_of_unbounded_components (K : Set ℂ) (hK : IsBounded K)
    (hcomp : ∀ z ∉ K, ¬ IsBounded (connectedComponentIn Kᶜ z)) : IsConnected Kᶜ := by
  obtain ⟨R, hR, hKR⟩ := hK.exists_pos_norm_le
  have hE := isConnected_exterior R hR
  have hEK : {z : ℂ | R < ‖z‖} ⊆ Kᶜ := fun z hz hzK => (not_lt_of_ge (hKR z hzK)) hz
  obtain ⟨a, ha⟩ := hE.nonempty
  have hEC := hE.isPreconnected.subset_connectedComponentIn ha hEK
  have hC : connectedComponentIn Kᶜ a = Kᶜ := by
    apply Subset.antisymm (connectedComponentIn_subset _ _)
    intro z hz
    have hfar : ∃ b ∈ connectedComponentIn Kᶜ z, R < ‖b‖ := by
      by_contra! H
      exact hcomp z hz (isBounded_iff_forall_norm_le.mpr ⟨R, H⟩)
    obtain ⟨b, hb, hbR⟩ := hfar
    have heq : connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ a :=
      (connectedComponentIn_eq hb).trans (connectedComponentIn_eq (hEC hbR)).symm
    rw [← heq]
    exact mem_connectedComponentIn hz
  rw [← hC]
  exact isConnected_connectedComponentIn_iff.mpr (hEK ha)

theorem frontier_component_subset_compl {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) : frontier (connectedComponentIn U z) ⊆ Uᶜ := by
  intro w hw hwU
  have hw' : (⟨w, hwU⟩ : U) ∈ closure (connectedComponent (⟨z, hz⟩ : U)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    simpa only [Set.mem_preimage, connectedComponentIn_eq_image hz] using hw.1
  rw [isClosed_connectedComponent.closure_eq] at hw'
  have hwc : w ∈ connectedComponentIn U z := by
    rw [connectedComponentIn_eq_image hz]
    exact ⟨⟨w, hwU⟩, hw', rfl⟩
  exact hw.2 ((hU.connectedComponentIn).interior_eq.symm ▸ hwc)

/-- Polynomial separation rules out all bounded complementary components,
by the maximum-modulus principle. -/
theorem isConnected_compl_of_polynomial_separation (K : Set ℂ) (hK : IsCompact K)
    (hsep : ∀ z ∉ K, ∃ p : Polynomial ℂ, ∃ C : ℝ,
      (∀ w ∈ K, ‖p.eval w‖ ≤ C) ∧ C < ‖p.eval z‖) : IsConnected Kᶜ := by
  apply isConnected_compl_of_unbounded_components K hK.isBounded
  intro z hz hbounded
  obtain ⟨p, C, hp, hpz⟩ := hsep z hz
  have hfront : frontier (connectedComponentIn Kᶜ z) ⊆ K := by
    simpa only [compl_compl] using frontier_component_subset_compl hK.isClosed.isOpen_compl hz
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le hbounded
    (p.differentiable.diffContOnCl) (fun w hw => hp w (hfront hw))
    (subset_closure (mem_connectedComponentIn hz))
  exact (not_lt_of_ge hbound) hpz

end EremenkosConjecture
