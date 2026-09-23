import EremenkosConjecture.RayEntireLimit
import EremenkosConjecture.RayCounterexampleCriterion

/-! # The singleton counterexample to Eremenko's conjecture

The analytic construction is now supplied by the infinite chain of entire
approximations. The distinguished endpoint in these coordinates is `7i/2`.
-/

open Set Metric Function Filter ComplexDynamics
open scoped Topology

namespace EremenkosConjecture

open Scaffolding

theorem RayEntireConstruction.constructionData (C : RayEntireConstruction) :
    RayConstructionData C.f rayBase := by
  refine ⟨C.entire, ?_, C.trapping, ?_, fun j => (C.property j).returnMap, ?_,
    fun j => (C.property j).endpoint⟩
  · exact ⟨fun j => (C.chain.stage j).a, fun j => (C.chain.stage j).b,
      fun j => (C.chain.stage j).a_pos, fun j => (C.chain.stage j).b_pos,
      C.widths_tendsto.1, C.widths_tendsto.2, fun j => (C.property j).barrier⟩
  · intro j
    cases j with
    | zero =>
        intro z hz
        change height 0 + 7 < 4 * z.im ∧ 4 * z.im < height 0 + 11
        rw [hz.2]
        norm_num [height, rayBase]
    | succ j => exact (C.property j).excursion
  · intro z hz hne
    let x := z.re - rayBase.re
    have hx : 0 < x := by
      by_contra hn
      have hn' : x ≤ 0 := le_of_not_gt hn
      apply hne
      apply Complex.ext
      · dsimp [x] at hn'
        linarith [hz.1]
      · exact hz.2
    have hzrepr : z = rayBase + (x : ℂ) := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re]
        dsimp [x]
        ring
      · simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz.2
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / x) x)
    have hN₁ : 1 / x < (N : ℝ) := (le_max_left _ _).trans_lt hN
    have hN₂ : x < (N : ℝ) := (le_max_right _ _).trans_lt hN
    have hprod : 1 < (N : ℝ) * x := (div_lt_iff₀ hx).mp hN₁
    filter_upwards [eventually_ge_atTop N] with j hj
    have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
    rw [hzrepr]
    apply (C.property j).bounded x
    · apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
      nlinarith
    · linarith

theorem exists_rayConstructionData : ∃ f : ℂ → ℂ, RayConstructionData f rayBase := by
  obtain ⟨C⟩ := exists_rayEntireConstruction
  exact ⟨C.f, C.constructionData⟩

/-- Theorem 7.1 with the endpoint at `7i/2` instead of the origin. -/
theorem theorem7_1_translated : ∃ f : ℂ → ℂ,
    IsTranscendentalEntire f ∧ horizontalRay rayBase ⊆ juliaSet f ∧ rayBase ∈ escapingSet f ∧
    horizontalRay rayBase \ {rayBase} ⊆ bungeeSet f ∧
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) rayBase = horizontalRay rayBase ∧
    connectedComponentIn (escapingSet f) rayBase = {rayBase} := by
  obtain ⟨f, D⟩ := exists_rayConstructionData
  exact ⟨f, D.conclusions⟩

/-- A transcendental entire function with a singleton connected component of
its escaping set, disproving the assertion that every such component is unbounded. -/
theorem eremenko_counterexample : ∃ (f : ℂ → ℂ) (z : ℂ),
    IsTranscendentalEntire f ∧ z ∈ escapingSet f ∧ connectedComponentIn (escapingSet f) z = {z} := by
  obtain ⟨f, hf, _, he, _, _, hc⟩ := theorem7_1_translated
  exact ⟨f, rayBase, hf, he, hc⟩

end EremenkosConjecture
