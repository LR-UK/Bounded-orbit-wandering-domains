/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import EremenkoLyubichConstant.TractSimplyConnected

open Set Function Metric
open scoped Topology

namespace FunctionTheory

open EremenkoLyubichConstant

/-- A transcendental entire function has values of arbitrarily large modulus. -/
theorem IsTranscendentalEntire.exists_norm_gt {f : ℂ → ℂ}
    (hf : IsTranscendentalEntire f) (R : ℝ) : ∃ z : ℂ, R < ‖f z‖ := by
  by_contra hn
  push Not at hn
  apply hf.2
  apply isPolynomialFunction_of_polynomial_growth hf.1 (C := R) (R := 0) (m := 0)
  intro z _
  simpa using hn z

/-- Class B admits an exterior covering whose full preimage avoids the closed unit disk.
The half-plane boundary can be chosen nonnegative. -/
theorem MemClassB.exists_normalized_exterior_covering {f : ℂ → ℂ} (hf : MemClassB f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ IsCoveringMapOn f (exponentialExterior ρ) ∧
      ∀ z, f z ∈ exponentialExterior ρ → 1 < ‖z‖ := by
  obtain ⟨_, R₀, _, hc⟩ := (memClassB_iff_exists_isCoveringMapOn_exterior f).mp hf
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) 1).image hf.1.1.continuous).isBounded.subset_closedBall 0
  let R := max 1 (max R₀ (C + 1))
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hRR : R₀ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hCR : C < R := lt_of_lt_of_le (by linarith : C < C + 1)
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Real.log R, Real.log_nonneg hR1, ?_, ?_⟩
  · apply hc.mono
    intro z hz
    change R₀ < ‖z‖
    change Real.exp (Real.log R) < ‖z‖ at hz
    rw [Real.exp_log hR] at hz
    exact hRR.trans_lt hz
  · intro z hz
    by_contra hn
    have hzB : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (le_of_not_gt hn)
    have hbound : ‖f z‖ ≤ C := mem_closedBall_zero_iff.mp (hC ⟨z, hzB, rfl⟩)
    change Real.exp (Real.log R) < ‖f z‖ at hz
    rw [Real.exp_log hR] at hz
    exact (not_lt_of_ge (hbound.trans hCR.le)) hz

/-- Each exterior preimage component of a transcendental entire covering has an exponential
half-plane chart. No source normalization or prescribed value at zero is required. -/
theorem IsTranscendentalEntire.exists_exterior_tract_chart
    {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) {ρ : ℝ}
    (hc : IsCoveringMapOn f (exponentialExterior ρ))
    {z₀ : ℂ} (hz₀ : f z₀ ∈ exponentialExterior ρ) :
    ∃ e : TractEquiv (connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀) ρ,
      ∀ z ∈ connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀,
        Complex.exp (e.toFun z) = f z := by
  let T := connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀
  have hW : IsOpen (exponentialExterior ρ) := isOpen_lt continuous_const continuous_norm
  have hT : IsOpen T := (hW.preimage hf.1.continuous).connectedComponentIn
  have hTc : IsConnected T := isConnected_connectedComponentIn_iff.mpr hz₀
  let : ConnectedSpace T := isConnected_iff_connectedSpace.mp hTc
  let : LocallyPathConnectedSpace T := hT.locallyPathConnectedSpace
  let : PathConnectedSpace T := PathConnectedSpace.of_locallyPathConnectedSpace
  exact exists_tractEquiv_of_transcendental_covering hf hc hT
    (connectedComponentIn_subset (f ⁻¹' exponentialExterior ρ) z₀)
    (isCoveringMap_connectedComponentIn hf.1.continuous hW hc z₀)

/-- Every exterior tract of a transcendental entire covering is simply connected. -/
theorem IsTranscendentalEntire.isSimplyConnected_exterior_tract
    {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) {ρ : ℝ}
    (hc : IsCoveringMapOn f (exponentialExterior ρ))
    {z₀ : ℂ} (hz₀ : f z₀ ∈ exponentialExterior ρ) :
    IsSimplyConnected (connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀) := by
  obtain ⟨e, _⟩ := hf.exists_exterior_tract_chart hc hz₀
  exact e.isSimplyConnected

/-- The tract simple-connectivity theorem stated using an arbitrary positive radius. -/
theorem IsTranscendentalEntire.isSimplyConnected_exterior_component
    {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) {R : ℝ} (hR : 0 < R)
    (hc : IsCoveringMapOn f {w : ℂ | R < ‖w‖}) {z₀ : ℂ} (hz₀ : R < ‖f z₀‖) :
    IsSimplyConnected (connectedComponentIn (f ⁻¹' {w : ℂ | R < ‖w‖}) z₀) := by
  have hce : IsCoveringMapOn f (exponentialExterior (Real.log R)) := by
    simpa only [exponentialExterior, Real.exp_log hR] using hc
  have hze : f z₀ ∈ exponentialExterior (Real.log R) := by
    simpa only [exponentialExterior, mem_ofPred_eq, Real.exp_log hR] using hz₀
  simpa only [exponentialExterior, Real.exp_log hR] using hf.isSimplyConnected_exterior_tract hce hze

/-- Class B has a common exterior radius beyond which every tract is simply connected and
has a conformal exponential covering chart. -/
theorem MemClassB.exists_simplyConnected_tracts {f : ℂ → ℂ} (hf : MemClassB f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ z₀, f z₀ ∈ exponentialExterior ρ →
      IsSimplyConnected (connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀) ∧
      ∃ e : TractEquiv (connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀) ρ,
        ∀ z ∈ connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀,
          Complex.exp (e.toFun z) = f z := by
  obtain ⟨ρ, hρ, hc, ha⟩ := hf.exists_normalized_exterior_covering
  refine ⟨ρ, hρ, fun z₀ hz₀ ↦ ?_⟩
  obtain ⟨e, he⟩ := hf.1.exists_exterior_tract_chart hc hz₀
  exact ⟨e.isSimplyConnected, e, he⟩

end FunctionTheory
