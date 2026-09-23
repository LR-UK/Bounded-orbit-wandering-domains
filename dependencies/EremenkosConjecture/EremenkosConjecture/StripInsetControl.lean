import FunctionTheory.Conformal.StripUniformity
import EremenkosConjecture.UniformConformalStability

/-! # Uniform iterate control from strip-end estimates

This applies the classical strip estimates to the continuity hypothesis used
in finite-iterate approximation. The closed inset geometry and asymptotic
remain explicit; no ambient extension of the conformal map is assumed.
-/

open Set Metric Filter Asymptotics
open scoped Topology

namespace EremenkosConjecture

theorem uniformControlOn_of_strip_asymptotic {V S A : Set ℂ} {f : ℂ → ℂ}
    {L M R δ : ℝ}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hinj : InjOn f V)
    (hS : IsClosed S) (hSV : S ⊆ V) (hleft : ∀ z ∈ S, L ≤ z.re)
    (him : ∀ z ∈ S, |z.im| ≤ M)
    (hA : IsClosed A) (hAS : A ⊆ interior S) (hδ : 0 < δ)
    (htail : ∀ z ∈ A, R ≤ z.re → closedBall z δ ⊆ interior S)
    (hO : (fun z => deriv f z - 1) =O[comap Complex.re atTop ⊓ 𝓟 S]
      (fun z => Real.exp (-z.re))) :
    UniformControlOn f S A := by
  obtain ⟨r, hr, htube⟩ := FunctionTheory.exists_uniform_neighbourhood_of_strip_tail hA
    (fun z hz => hleft z (interior_subset (hAS hz)))
    (fun z hz => him z (interior_subset (hAS hz))) isOpen_interior hAS hδ htail
  obtain ⟨m, C, _, hC, hbounds⟩ :=
    FunctionTheory.exists_derivative_bounds_of_strip_asymptotic hV hf hinj hS hSV hleft him hO
  exact uniformControlOn_of_derivative_bound hr hC.le
    (fun z hz => ball_subset_closedBall.trans ((htube z hz).trans interior_subset))
    (hf.mono hSV) (fun z hz => (hbounds z hz).2)

end EremenkosConjecture
