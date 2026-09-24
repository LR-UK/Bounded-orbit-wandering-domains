/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SimplyConnectedFilling
import BoundedWanderingDomains.SingularValues
import EremenkoLyubichConstant.ClassBTracts

/-! # The tract obstruction to surrounding curves

A compact continuum in an exterior preimage lies in one simply connected
tract, so its filling remains in the exterior preimage. This is the part of
Baker's surrounding-curve argument supplied by the Eremenko--Lyubich project.
-/

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

theorem exterior_fill_subset {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) {R : ℝ} (hR : 0 < R)
    (hc : IsCoveringMapOn f {w : ℂ | R < ‖w‖})
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKR : ∀ z ∈ K, R < ‖f z‖) :
    ∀ z ∈ ComplexApproximation.fill K, R < ‖f z‖ := by
  obtain ⟨a, ha⟩ := hKc.nonempty
  let T := connectedComponentIn (f ⁻¹' {w : ℂ | R < ‖w‖}) a
  have hT : IsOpen T :=
    ((isOpen_lt continuous_const continuous_norm).preimage hf.1.continuous).connectedComponentIn
  have hsc : IsSimplyConnected T := hf.isSimplyConnected_exterior_component hR hc (hKR a ha)
  have hKT : K ⊆ T := hKc.isPreconnected.subset_connectedComponentIn ha hKR
  exact (fill_subset_of_isSimplyConnected hK hT hsc hKT).trans
    (connectedComponentIn_subset _ _)

/-- A compact continuum surrounding a low-value point cannot lie in the
high-value preimage. This applies in particular to images of essential loops. -/
theorem exists_low_value_on_surrounding_continuum {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) {R : ℝ} (hR : 0 < R)
    (hc : IsCoveringMapOn f {w : ℂ | R < ‖w‖})
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    {a : ℂ} (ha : a ∈ ComplexApproximation.fill K) (hfa : ‖f a‖ ≤ R) :
    ∃ z ∈ K, ‖f z‖ ≤ R := by
  by_contra! hn
  exact (not_lt_of_ge hfa) (exterior_fill_subset hf hR hc hK hKc hn a ha)

/-- Bounded finite singular values provide a single radius for the preceding
obstruction, using the singular-value definition of the wandering project. -/
theorem classB_surrounding_continuum_bound {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) (hB : ComplexDynamics.MemClassB f)
    (a : ℂ) : ∃ R > 0, ∀ K : Set ℂ, IsCompact K → IsConnected K →
      a ∈ ComplexApproximation.fill K → ∃ z ∈ K, ‖f z‖ ≤ R := by
  obtain ⟨M, hM, hb⟩ := ((ComplexDynamics.memClassB_iff f).mp hB).exists_pos_norm_le
  let R := max M ‖f a‖
  have hR : 0 < R := hM.trans_le (le_max_left _ _)
  have hc : IsCoveringMapOn f {w : ℂ | R < ‖w‖} :=
    (ComplexDynamics.isCoveringMapOn_compl_singularValues f).mono (by
      intro w hw hws
      exact (not_lt_of_ge ((hb w hws).trans (le_max_left M ‖f a‖))) hw)
  exact ⟨R, hR, fun K hK hKc ha =>
    exists_low_value_on_surrounding_continuum hf hR hc hK hKc ha (le_max_right _ _)⟩

/-- Baker's surrounding and escape conclusions contradict membership in class B.
The hypotheses here concern compact continua; there is no parametrisation or
smoothness requirement on the surrounding curves. -/
theorem not_classB_of_surrounding_escaping_continua {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) {K : ℕ → Set ℂ}
    (hK : ∀ n, IsCompact (K n)) (hKc : ∀ n, IsConnected (K n))
    {a : ℂ} (ha : ∀ᶠ n in atTop, a ∈ ComplexApproximation.fill (K n))
    (he : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K n, R < ‖f z‖) :
    ¬ ComplexDynamics.MemClassB f := by
  intro hB
  obtain ⟨R, _, hb⟩ := classB_surrounding_continuum_bound hf hB a
  obtain ⟨n, hn, hnR⟩ := (ha.and (he R)).exists
  obtain ⟨z, hz, hzR⟩ := hb (K n) (hK n) (hKc n) hn
  exact (not_lt_of_ge hzR) (hnR z hz)

end AreaDeficit

#print axioms AreaDeficit.not_classB_of_surrounding_escaping_continua
