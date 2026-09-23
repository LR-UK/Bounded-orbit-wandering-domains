import Runge.UniformClosure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Uniform rational approximation of a Cauchy area integral

A continuous, compactly supported coefficient vanishing near `K` produces a
continuous family of rational functions on `K`. Its integral therefore belongs
to the uniform rational closure.
-/

open Polynomial MeasureTheory Function Filter Set
open scoped Topology

namespace Runge

theorem continuous_cauchyKernel (K : Set ℂ) (c : ℂ → ℂ)
    (hc : Continuous c) (hsep : Disjoint (tsupport c) K) :
    Continuous (fun p : ℂ × K => c p.1 / (p.1 - (p.2 : ℂ))) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 = (p.2 : ℂ)
  · have hn : p.1 ∉ tsupport c := fun h =>
      Set.disjoint_left.mp hsep h (hp.symm ▸ p.2.property)
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
      (continuous_fst.tendsto p)
    have hzero : ContinuousAt (fun _ : ℂ × K => (0 : ℂ)) p := continuousAt_const
    apply hzero.congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [Function.comp_apply, Pi.zero_apply] at hq
    simp [hq]
  · exact (hc.continuousAt.comp continuousAt_fst).div
      (continuousAt_fst.sub (continuous_subtype_val.continuousAt.comp continuousAt_snd))
      (sub_ne_zero.mpr hp)

noncomputable def cauchyKernelFamily (K : Set ℂ) (c : ℂ → ℂ)
    (hc : Continuous c) (hsep : Disjoint (tsupport c) K) (w : ℂ) : C(K, ℂ) :=
  ⟨fun z => c w / (w - (z : ℂ)),
    (continuous_cauchyKernel K c hc hsep).comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_cauchyKernelFamily (K : Set ℂ) (c : ℂ → ℂ)
    (hc : Continuous c) (hsep : Disjoint (tsupport c) K) :
    Continuous (cauchyKernelFamily K c hc hsep) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_cauchyKernel K c hc hsep)

theorem cauchyKernelFamily_mem (K : Set ℂ) (c : ℂ → ℂ)
    (hc : Continuous c) (hsep : Disjoint (tsupport c) K) (w : ℂ) :
    cauchyKernelFamily K c hc hsep w ∈ rationalAlgebra K := by
  by_cases hw : w ∈ K
  · have hz : c w = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => Set.disjoint_left.mp hsep h hw)
    refine ⟨0, 1, by simp, ?_⟩
    intro z
    simp [cauchyKernelFamily, hz]
  · refine ⟨C (c w), C w - X, ?_, ?_⟩
    · intro z
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      exact sub_ne_zero.mpr (fun h => hw (h.symm ▸ z.property))
    · intro z
      simp [cauchyKernelFamily]

theorem hasCompactSupport_cauchyKernelFamily (K : Set ℂ) (c : ℂ → ℂ)
    (hc : Continuous c) (hsep : Disjoint (tsupport c) K) (hs : HasCompactSupport c) :
    HasCompactSupport (cauchyKernelFamily K c hc hsep) := by
  apply hs.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro w hw
  contrapose! hw
  apply notMem_support.mpr
  apply ContinuousMap.ext
  intro z
  simp [cauchyKernelFamily, notMem_support.mp hw]

/-- The same quotient approximates the Cauchy area integral throughout `K`. -/
theorem cauchyIntegral_uniform_rational_approximation
    (K : Set ℂ) [CompactSpace K] (c : ℂ → ℂ) (hc : Continuous c)
    (hsep : Disjoint (tsupport c) K) (hs : HasCompactSupport c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
      ∀ z : K, ‖(∫ w : ℂ, c w / (w - (z : ℂ))) -
        p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε := by
  apply integral_uniform_rational_approximation K volume (cauchyKernelFamily K c hc hsep)
    (fun w => (rationalAlgebra K).le_topologicalClosure (cauchyKernelFamily_mem K c hc hsep w))
    ((continuous_cauchyKernelFamily K c hc hsep).integrable_of_hasCompactSupport
      (hasCompactSupport_cauchyKernelFamily K c hc hsep hs)) ε hε

end Runge
