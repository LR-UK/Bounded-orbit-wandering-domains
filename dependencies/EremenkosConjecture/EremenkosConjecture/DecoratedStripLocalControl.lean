import EremenkosConjecture.StripInsetControl
import FunctionTheory.Conformal.StripEndMapLocal

/-! # Controlled strip maps using only local end geometry

This removes the global Jordan-frontier hypothesis from the approximation interface. The
source domain and its closed insets must still be constructed. Given the
displayed geometric conditions, the map, its end estimates, its derivative
bounds and its uniform iterate-control modulus are all proved to exist.
-/

open Set Metric Filter Asymptotics
open scoped Topology

namespace EremenkosConjecture

theorem exists_strip_map_with_uniform_control_of_straight_tail
    {U S A : Set ℂ} {z₀ : ℂ} {L R T δ : ℝ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUS : U ⊆ FunctionTheory.standardHorizontalStrip) (hleft : ∀ z ∈ U, L ≤ z.re)
    (htail : ∀ z ∈ FunctionTheory.standardHorizontalStrip, R < z.re → z ∈ U)
    (hz₀ : z₀ ∈ U) (hS : IsClosed S) (hSU : S ⊆ U)
    (hA : IsClosed A) (hAS : A ⊆ interior S) (hδ : 0 < δ)
    (hAtail : ∀ z ∈ A, T ≤ z.re → closedBall z δ ⊆ interior S) :
    ∃ (φ : ℂ → ℂ) (ρ m B : ℝ), DifferentiableOn ℂ φ U ∧
      BijOn φ U FunctionTheory.standardHorizontalStrip ∧ φ z₀ = 0 ∧
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      UniformControlOn φ S A ∧ 0 < m ∧ 0 < B ∧
      ∀ z ∈ S, m ≤ ‖deriv φ z‖ ∧ ‖deriv φ z‖ ≤ B := by
  obtain ⟨φ, ρ, hφd, hφbij, hφ0, hOd, hOv, -⟩ :=
    FunctionTheory.exists_normalized_strip_map_of_straight_tail
      hUo hUc hUS htail hz₀
  have hleftS : ∀ z ∈ S, L ≤ z.re := fun z hz => hleft z (hSU hz)
  have himS : ∀ z ∈ S, |z.im| ≤ Real.pi / 2 :=
    fun z hz => (show |z.im| < Real.pi / 2 from hUS (hSU hz)).le
  have hOS : (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 S]
      (fun z => Real.exp (-z.re)) :=
    hOd.mono (inf_le_inf_left _ (Filter.principal_mono.mpr hSU))
  obtain ⟨m, B, hm, hB, hbounds⟩ :=
    FunctionTheory.exists_derivative_bounds_of_strip_asymptotic hUo hφd hφbij.injOn
      hS hSU hleftS himS hOS
  exact ⟨φ, ρ, m, B, hφd, hφbij, hφ0, hOd, hOv,
    uniformControlOn_of_strip_asymptotic hUo hφd hφbij.injOn hS hSU hleftS himS
      hA hAS hδ hAtail hOS, hm, hB, hbounds⟩

end EremenkosConjecture
