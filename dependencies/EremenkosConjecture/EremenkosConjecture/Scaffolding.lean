import EremenkosConjecture.ScaffoldingDomains

/-! # Section 4: the scaffolding lemma -/

open Set Metric Function Complex

namespace EremenkosConjecture.Scaffolding

/-- Lemma 4.1, with an explicit admissible approximation tolerance. The
open partial homeomorphism is the conformal isomorphism `f^j : V_j → T_j`.
Its source is a domain and is unbounded in both real directions. -/
theorem lemma4_1 : ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℂ → ℂ,
    DifferentiableOn ℂ f sourceStrips →
    (∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ ε) →
    (∀ z ∈ sourceStrips, 1 ≤ |z.re| → 4 * |z.re| < |(f z).re|) ∧
    ∀ j : ℕ, 0 < j → ∃ e : OpenPartialHomeomorph ℂ ℂ,
      e.target = targetStrip j ∧ e.source ⊆ sourceStrip 0 ∧ IsConnected e.source ∧
      ¬ BddAbove (Complex.re '' e.source) ∧ ¬ BddBelow (Complex.re '' e.source) ∧
      (∀ z, e z = (f^[j]) z) ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (∀ k < j, MapsTo (f^[k]) e.source (sourceStrip k)) ∧
      ∀ k < j, ∀ z ∈ e.source, 2 ≤ ‖deriv f ((f^[k]) z)‖ ∧
        ‖deriv f ((f^[k]) z)‖ ≤ 8 := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro f hf hclose
  refine ⟨fun z hz hzr => real_part_expansion (by norm_num) (hclose z hz) hzr, ?_⟩
  intro j hj
  obtain ⟨e, heT, heS, he, hehol, hei, horbit, hderiv⟩ :=
    exists_iterated_strip_chart hf hclose j hj
  obtain ⟨hconn, hupper, hlower⟩ := strip_chart_domain_properties hclose j e heT he horbit
  exact ⟨e, heT, heS, hconn, hupper, hlower, he, hehol, hei, horbit, hderiv⟩

/-- A fixed entire starting function with room for subsequent perturbations.
The tolerance `1/200` is half the tolerance used in Lemma 4.1. -/
theorem exists_scaffolding_function : ∃ f₀ : ℂ → ℂ, Differentiable ℂ f₀ ∧
    (∀ z ∈ closedSourceStrips, ‖f₀ z - 5 * z‖ < 1 / 200) ∧
    (∀ z ∈ trappingDisk, ‖f₀ z‖ < 1 / 200) ∧
    ∀ f : ℂ → ℂ, (∀ z ∈ initialApproximationSet, ‖f z - f₀ z‖ ≤ 1 / 200) →
      (∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100) ∧
      MapsTo f trappingDisk (ball 0 (1 / 2)) := by
  obtain ⟨f₀, hf₀, hS, hD⟩ := exists_initial_entire (1 / 200) (by norm_num)
  refine ⟨f₀, hf₀, hS, hD, ?_⟩
  intro f hclose
  refine ⟨?_, mapsTo_trappingDisk_of_close (by norm_num) hD (fun z hz => hclose z (Or.inr hz))⟩
  intro z hz
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  have hzS : z ∈ closedSourceStrips := mem_iUnion.mpr ⟨j, sourceStrip_subset_closed j hj⟩
  have h₁ := hclose z (Or.inl hzS)
  have h₂ := hS z hzS
  have ht := norm_sub_le_norm_sub_add_norm_sub (f z) (f₀ z) (5 * z)
  linarith

end EremenkosConjecture.Scaffolding
