import Runge.Rational
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Algebra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Uniform closure of rational functions

The norm on `C(K, ℂ)` is the uniform norm. Working with integrals in this space
keeps one polynomial quotient valid at every point of the compact set.
-/

open Polynomial MeasureTheory

namespace Runge

/-- Continuous rational functions with a denominator nonzero on `K`. -/
def rationalAlgebra (K : Set ℂ) : Subalgebra ℂ C(K, ℂ) where
  carrier := {f | ∃ p q : ℂ[X], (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
    ∀ z : K, f z = p.eval (z : ℂ) / q.eval (z : ℂ)}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp⟩
  add_mem' := by
    rintro f g ⟨p, q, hq, hf⟩ ⟨r, s, hs, hg⟩
    refine ⟨p * s + q * r, q * s, ?_, ?_⟩
    · intro z
      simpa using mul_ne_zero (hq z) (hs z)
    · intro z
      simp only [ContinuousMap.add_apply, Polynomial.eval_add, Polynomial.eval_mul]
      rw [hf, hg]
      exact div_add_div _ _ (hq z) (hs z)
  mul_mem' := by
    rintro f g ⟨p, q, hq, hf⟩ ⟨r, s, hs, hg⟩
    refine ⟨p * r, q * s, ?_, ?_⟩
    · intro z
      simpa using mul_ne_zero (hq z) (hs z)
    · intro z
      simp only [ContinuousMap.mul_apply, Polynomial.eval_mul]
      rw [hf, hg]
      exact div_mul_div_comm _ _ _ _
  algebraMap_mem' c := ⟨C c, 1, by simp, by simp⟩

/-- The continuous map associated with a polynomial quotient on `K`. -/
noncomputable def rationalMap (K : Set ℂ) (p q : ℂ[X])
    (hq : ∀ z : K, q.eval (z : ℂ) ≠ 0) : C(K, ℂ) :=
  ⟨fun z => p.eval (z : ℂ) / q.eval (z : ℂ),
    (p.continuous.comp continuous_subtype_val).div
      (q.continuous.comp continuous_subtype_val) hq⟩

theorem rationalMap_mem (K : Set ℂ) (p q : ℂ[X]) (hq : ∀ z : K, q.eval (z : ℂ) ≠ 0) :
    rationalMap K p q hq ∈ rationalAlgebra K :=
  ⟨p, q, hq, fun _ => rfl⟩

/-- Uniform limits of rational functions without poles on the compact domain. -/
noncomputable def rationalClosure (K : Set ℂ) [CompactSpace K] : Subalgebra ℂ C(K, ℂ) :=
  (rationalAlgebra K).topologicalClosure

theorem mem_rationalClosure_iff (K : Set ℂ) [CompactSpace K] (f : C(K, ℂ)) :
    f ∈ rationalClosure K ↔ ∀ ε : ℝ, 0 < ε →
      ∃ p q : ℂ[X], (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
        ∀ z : K, ‖f z - p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε := by
  change f ∈ closure (rationalAlgebra K : Set C(K, ℂ)) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro hf ε hε
    obtain ⟨g, ⟨p, q, hq, hg⟩, hfg⟩ := hf ε hε
    refine ⟨p, q, hq, fun z => ?_⟩
    rw [← hg z]
    exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (f - g) z)
      (by simpa only [dist_eq_norm] using hfg)
  · intro hf ε hε
    obtain ⟨p, q, hq, hpq⟩ := hf ε hε
    refine ⟨rationalMap K p q hq, rationalMap_mem K p q hq, ?_⟩
    rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
    exact hpq

/-- A closed real vector subspace contains the integral of any family in it.
The integral is zero by definition when the family is not integrable. -/
theorem integral_mem_closedSubmodule {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (μ : Measure α) (F : α → E) (hF : ∀ a, F a ∈ S) :
    (∫ a, F a ∂μ) ∈ S := by
  let : CompleteSpace S := hS.completeSpace_coe
  let G : α → S := fun a => ⟨F a, hF a⟩
  have h := S.subtypeₗᵢ.integral_comp_comm (μ := μ) G
  change (∫ a, F a ∂μ) = ((∫ a, G a ∂μ : S) : E) at h
  rw [h]
  exact (∫ a, G a ∂μ : S).property

theorem integral_mem_rationalClosure {α : Type*} [MeasurableSpace α]
    (K : Set ℂ) [CompactSpace K] (μ : Measure α) (F : α → C(K, ℂ))
    (hF : ∀ a, F a ∈ rationalClosure K) :
    (∫ a, F a ∂μ) ∈ rationalClosure K := by
  exact integral_mem_closedSubmodule
    ((rationalClosure K).toSubmodule.restrictScalars ℝ)
    (rationalAlgebra K).isClosed_topologicalClosure μ F hF

/-- Integration preserves uniform rational approximability. The approximating
polynomials are chosen once and work simultaneously at every point of `K`. -/
theorem integral_uniform_rational_approximation {α : Type*} [MeasurableSpace α]
    (K : Set ℂ) [CompactSpace K] (μ : Measure α) (F : α → C(K, ℂ))
    (hF : ∀ a, F a ∈ rationalClosure K) (hi : Integrable F μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
      ∀ z : K, ‖(∫ a, F a z ∂μ) - p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε := by
  obtain ⟨p, q, hq, hpq⟩ :=
    (mem_rationalClosure_iff K _).mp (integral_mem_rationalClosure K μ F hF) ε hε
  refine ⟨p, q, hq, fun z => ?_⟩
  simpa only [ContinuousMap.integral_apply hi] using hpq z

end Runge
