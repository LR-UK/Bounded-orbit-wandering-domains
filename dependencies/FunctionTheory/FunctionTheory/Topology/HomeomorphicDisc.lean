import TauCeti.Topology.JordanCurve.Basic
import TauCeti.Analysis.Complex.Conformal.Biholomorph
import FunctionTheory.Holomorphic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- A plane homeomorphism sends a disc to a bounded simply connected Jordan
domain, with the expected closure and boundary. -/
theorem homeomorph_image_ball_geometry (H : ℂ ≃ₜ ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsOpen (H '' ball c r) ∧
      IsConnected (H '' ball c r) ∧
      IsSimplyConnected (H '' ball c r) ∧
      Bornology.IsBounded (H '' ball c r) ∧
      closure (H '' ball c r) = H '' closedBall c r ∧
      frontier (H '' ball c r) = H '' sphere c r ∧
      TauCeti.IsJordanCurve (frontier (H '' ball c r)) := by
  have hc : IsConnected (ball c r) :=
    (convex_ball c r).isConnected (nonempty_ball.mpr hr)
  have hsc : IsSimplyConnected (ball c r) := by
    haveI : ContractibleSpace (ball c r) :=
      (convex_ball c r).contractibleSpace (nonempty_ball.mpr hr)
    change SimplyConnectedSpace (ball c r)
    infer_instance
  have hclosure : closure (H '' ball c r) = H '' closedBall c r := by
    rw [← H.image_closure, closure_ball c hr.ne']
  have hfront : frontier (H '' ball c r) = H '' sphere c r := by
    rw [← H.image_frontier, frontier_ball c hr.ne']
  refine ⟨H.isOpenMap _ isOpen_ball, H.isConnected_image.mpr hc,
    H.isSimplyConnected_image.mpr hsc, ?_, hclosure, hfront, ?_⟩
  · exact ((isCompact_closedBall c r).image H.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  · rw [hfront]
    exact (TauCeti.isJordanCurve_sphere c hr).image_homeomorph H

/-- Restricting a holomorphic plane homeomorphism to an open domain gives
a conformal chart, including holomorphy of the inverse on its actual domain. -/
theorem exists_holomorphic_image_chart (H : ℂ ≃ₜ ℂ) {D : Set ℂ}
    (hD : IsOpen D) (hH : DifferentiableOn ℂ (H : ℂ → ℂ) D) :
    ∃ ψ : D ≃ₜ (H '' D),
      (∀ z : D, (ψ z : ℂ) = H z) ∧
      IsHolomorphicFunctionOn D (fun z => (ψ z : ℂ)) ∧
      IsHolomorphicFunctionOn (H '' D) (fun z => (ψ.symm z : ℂ)) := by
  have hb : BijOn (H : ℂ → ℂ) D (H '' D) :=
    ⟨mapsTo_image H D, H.injective.injOn, surjOn_image H D⟩
  let ψ := hH.toHomeomorphOfBijOn hD hb
  refine ⟨ψ, fun z => rfl, ?_, ?_⟩
  · exact isHolomorphicFunctionOn_restrict hD hH
  · have hi := hH.invFunOn hD H.injective.injOn
    have hh := isHolomorphicFunctionOn_restrict (H.isOpenMap D hD) hi
    simpa only [ψ, DifferentiableOn.toHomeomorphOfBijOn_symm_apply] using hh

end FunctionTheory

