import Runge.UniformClosure
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Polynomial MeasureTheory Set

namespace Runge

theorem ringInverse_apply (K : Set ℂ) (f : C(K, ℂ)) (hf : IsUnit f) (z : K) :
    (Ring.inverse f) z = (f z)⁻¹ := by
  have hn := (f.isUnit_iff_forall_ne_zero.mp hf) z
  apply mul_left_cancel₀ hn
  have h := congrArg (fun g : C(K, ℂ) => g z) (Ring.mul_inverse_cancel f hf)
  exact h.trans (mul_inv_cancel₀ hn).symm

theorem ringInverse_mem_rationalAlgebra (K : Set ℂ) (f : C(K, ℂ))
    (hf : f ∈ rationalAlgebra K) : Ring.inverse f ∈ rationalAlgebra K := by
  by_cases hu : IsUnit f
  · obtain ⟨p, q, hq, hpq⟩ := hf
    refine ⟨q, p, ?_, ?_⟩
    · intro z hp
      have hn := (f.isUnit_iff_forall_ne_zero.mp hu) z
      rw [hpq z, hp, zero_div] at hn
      exact hn rfl
    · intro z
      rw [ringInverse_apply K f hu z, hpq z, inv_div]
  · rw [Ring.inverse_non_unit f hu]
    exact (rationalAlgebra K).zero_mem

/-- Uniform rational approximability is preserved by taking the reciprocal of
a continuous function that never vanishes on the compact set. -/
theorem ringInverse_mem_rationalClosure (K : Set ℂ) [CompactSpace K] (f : C(K, ℂ))
    (hf : f ∈ rationalClosure K) (hu : IsUnit f) :
    Ring.inverse f ∈ rationalClosure K := by
  have hc : ContinuousAt Ring.inverse f := by
    simpa only [IsUnit.unit_spec] using NormedRing.inverse_continuousAt hu.unit
  have hm : Ring.inverse '' (rationalAlgebra K : Set C(K, ℂ)) ⊆ rationalAlgebra K := by
    rintro _ ⟨g, hg, rfl⟩
    exact ringInverse_mem_rationalAlgebra K g hg
  exact closure_mono hm (mem_closure_image hc hf)

theorem intervalIntegral_mem_rationalClosure (K : Set ℂ) [CompactSpace K]
    (F : ℝ → C(K, ℂ)) (hF : ∀ t, F t ∈ rationalClosure K) (a b : ℝ) :
    (∫ t in a..b, F t) ∈ rationalClosure K := by
  exact (rationalClosure K).sub_mem
    (integral_mem_rationalClosure K (volume.restrict (Ioc a b)) F hF)
    (integral_mem_rationalClosure K (volume.restrict (Ioc b a)) F hF)

theorem continuousMap_intervalIntegral_apply (K : Set ℂ) [CompactSpace K]
    (F : ℝ → C(K, ℂ)) (a b : ℝ) (hF : IntervalIntegrable F volume a b) (z : K) :
    (∫ t in a..b, F t) z = ∫ t in a..b, F t z := by
  exact ((ContinuousMap.evalCLM ℝ z).intervalIntegral_comp_comm hF).symm

end Runge
