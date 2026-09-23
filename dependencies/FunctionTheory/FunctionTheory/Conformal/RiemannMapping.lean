import FunctionTheory.Holomorphic
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Conformal
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle

/-! # Riemann maps on their actual domains

The underlying Riemann mapping, normalization and Schwarz reflection proofs
are the attributed Tau Ceti modules recorded in `third_party/TauCeti/`.
This interface represents the conformal isomorphism as a homeomorphism of
subtypes, so neither direction has values outside its mathematical domain.
-/

open Set Metric

namespace FunctionTheory

/-- Riemann mapping as a homeomorphism, holomorphic in both directions, whose
functions are defined only on the open domains they map between. -/
theorem exists_riemannMap_on_domain {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ e : U ≃ₜ ball (0 : ℂ) 1,
      FunctionTheory.IsHolomorphicFunctionOn U (fun z => (e z : ℂ)) ∧
      FunctionTheory.IsHolomorphicFunctionOn (ball (0 : ℂ) 1) (fun z => (e.symm z : ℂ)) := by
  obtain ⟨f, hbij, hf, hg, -, -⟩ :=
    TauCeti.exists_bijOn_ball_differentiableOn_invFunOn hUo hUc hU
  refine ⟨hf.toHomeomorphOfBijOn hUo hbij, ?_, ?_⟩
  · simpa only [DifferentiableOn.toHomeomorphOfBijOn_apply] using
      FunctionTheory.isHolomorphicFunctionOn_restrict hUo hf
  · simpa only [DifferentiableOn.toHomeomorphOfBijOn_symm_apply] using
      FunctionTheory.isHolomorphicFunctionOn_restrict isOpen_ball hg

end FunctionTheory
