import FunctionTheory.Conformal.AnalyticSideInverse
import FunctionTheory.Conformal.AnalyticBoundarySide
import FunctionTheory.Conformal.RegularBoundaryContinuation

open Set Metric Complex Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A conformal disc chart extends analytically through any regular analytic
boundary arc, with an injective extension near a preimage of the prescribed
boundary point. Neither a Jordan boundary nor continuity on the whole closed
disc is required. Local injectivity is the correct assertion even for slits. -/
theorem exists_disc_continuation_at_regular_analytic_boundary
    {U : Set ℂ} {φ : ℂ → ℂ} {p : ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ (ball (0:ℂ) 1))
    (hbij : BijOn φ (ball (0:ℂ) 1) U) (hp : p∈frontier U)
    (harc : HasRegularAnalyticArcAt (frontier U) p) :
    ∃ (ξ : ℂ) (ε : ℝ) (G : ℂ → ℂ), ‖ξ‖=1 ∧ 0<ε ∧
      AnalyticOnNhd ℂ G (ball 0 1 ∪ ball ξ ε) ∧ InjOn G (ball ξ ε) ∧
      EqOn G φ (ball 0 1) ∧ G ξ=p := by
  let f := invFunOn φ (ball (0:ℂ) 1)
  have hfb : BijOn f U (ball (0:ℂ) 1) :=
    Set.BijOn.symm hbij.invOn_invFunOn.symm hbij
  have hfd : DifferentiableOn ℂ f U := by
    simpa only [hbij.image_eq] using DifferentiableOn.invFunOn hφ isOpen_ball hbij.injOn
  obtain ⟨e,hps,hea,hei,hep,haxis⟩ := harc
  obtain ⟨R,hR,hT,hline,hside⟩ := exists_occupied_side_of_boundary_coordinate hU hp e hps hep haxis
  have he0 : e.symm 0=p := by rw [← hep]; exact e.left_inv hps
  have Hext : ∃ (ξ : ℂ) (ε : ℝ) (Ψ : ℂ → ℂ), ‖ξ‖=1 ∧ 0<ε ∧
      AnalyticOnNhd ℂ Ψ (ball ξ ε) ∧ InjOn Ψ (ball ξ ε) ∧ Ψ ξ=p ∧
      EqOn Ψ (invFunOn f U) (ball ξ ε∩ball 0 1) := by
    rcases hside with hpos|hneg
    · simpa only [he0] using exists_local_inverse_extension_at_analytic_side
        hU hfd hfb e hei.differentiableOn hR hT hpos hline
    · let E := e.transHomeomorph (Homeomorph.neg ℂ)
      have hET : closedBall (0:ℂ) R⊆E.target := by
        intro z hz
        change -z∈e.target
        exact hT (by simpa only [mem_closedBall,dist_zero_right,norm_neg] using hz)
      have hEd : DifferentiableOn ℂ E.symm E.target := by
        intro z hz
        change DifferentiableWithinAt ℂ (fun w => e.symm (-w)) E.target z
        exact (hei.differentiableOn (-z) hz).comp z differentiableWithinAt_id.neg (fun w hw => hw)
      have hEside : ∀ z∈ball (0:ℂ) R, 0<z.re → E.symm z∈U := by
        intro z hz hre
        change e.symm (-z)∈U
        apply hneg _ (by simpa only [mem_ball,dist_zero_right,norm_neg] using hz)
        simpa only [neg_re] using neg_neg_of_pos hre
      have hEline : ∀ z∈ball (0:ℂ) R, z.re=0 → E.symm z∉U := by
        intro z hz hre
        change e.symm (-z)∉U
        exact hline _ (by simpa only [mem_ball,dist_zero_right,norm_neg] using hz) (by simp [hre])
      have hE0 : E.symm 0=p := by change e.symm (-0)=p; simpa only [neg_zero] using he0
      simpa only [hE0] using exists_local_inverse_extension_at_analytic_side
        hU hfd hfb E hEd hR hET hEside hEline
  obtain ⟨ξ,ε,Ψ,hξ,hε,hΨa,hΨi,hΨ0,hΨf⟩ := Hext
  have hfinv : EqOn (invFunOn f U) φ (ball (0:ℂ) 1) := by
    intro z hz
    have Hf : f (φ z)=z := hbij.injOn.leftInvOn_invFunOn hz
    simpa only [Hf] using hfb.injOn.leftInvOn_invFunOn (hbij.mapsTo hz)
  have hΨφ : EqOn φ Ψ (ball (0:ℂ) 1∩ball ξ ε) :=
    fun z hz => ((hΨf ⟨hz.2,hz.1⟩).trans (hfinv hz.1)).symm
  obtain ⟨G,hGa,hGφ,hGΨ⟩ := exists_analytic_gluing isOpen_ball isOpen_ball
    (hφ.analyticOnNhd isOpen_ball) hΨa hΨφ
  refine ⟨ξ,ε,G,hξ,hε,hGa,?_,hGφ,(hGΨ (mem_ball_self hε)).trans hΨ0⟩
  intro z hz w hw H
  exact hΨi hz hw (by rwa [hGΨ hz,hGΨ hw] at H)

end FunctionTheory
