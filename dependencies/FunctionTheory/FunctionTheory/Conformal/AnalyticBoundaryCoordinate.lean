import FunctionTheory.Conformal.AnalyticBoundaryContinuation
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Metric Complex Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A local coordinate identifying a domain with the right halfplane
carries its boundary points in the coordinate neighbourhood to the axis. -/
theorem re_eq_zero_of_boundary_coordinate
    {U : Set ℂ} (hU : IsOpen U) (e : OpenPartialHomeomorph ℂ ℂ)
    (hside : ∀ z∈e.source, z∈U ↔ 0<(e z).re)
    {x : ℂ} (hx : x∈frontier U) (hxs : x∈e.source) : (e x).re=0 := by
  have hn : ¬0<(e x).re := fun H => (hU.frontier_eq ▸ hx).2 ((hside x hxs).mpr H)
  have hnn : 0≤(e x).re := by
    by_contra H
    have H' : (e x).re<0 := lt_of_not_ge H
    have hec : ContinuousAt (fun z => (e z).re) x :=
      Complex.continuous_re.continuousAt.comp (e.continuousOn.continuousAt (e.open_source.mem_nhds hxs))
    have hev : ∀ᶠ z in 𝓝 x, z∈e.source ∧ (e z).re<0 := by
      filter_upwards [e.open_source.mem_nhds hxs,hec (gt_mem_nhds H')] with z hz hneg
      exact ⟨hz,hneg⟩
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hev
    obtain ⟨z,hz,hzx⟩ := Metric.mem_closure_iff.mp hx.1 r hr
    have hzB : z∈ball x r := by simpa only [mem_ball,dist_comm] using hzx
    have hp := (hside z (hrsub hzB).1).mp hz
    exact (not_lt_of_ge hp.le) (hrsub hzB).2
  exact le_antisymm (le_of_not_gt hn) hnn

/-- A closed-disc-continuous conformal parametrisation extends through a
boundary point admitting a local analytic coordinate to a halfplane. All
maps are only assumed holomorphic on their displayed actual domains. -/
theorem exists_disc_continuation_of_boundary_coordinate
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfc : ContinuousOn f (closedBall 0 1))
    (hfi : InjOn f (ball 0 1)) (hfU : MapsTo f (ball 0 1) U)
    (hfbd : MapsTo f (sphere 0 1) (frontier U))
    {a : ℂ} (ha : ‖a‖=1) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (hfa : f a∈e.source) (h0 : e (f a)=0)
    (hside : ∀ z∈e.source, z∈U ↔ 0<(e z).re) :
    ∃ ε : ℝ, ∃ g : ℂ → ℂ, 0<ε ∧
      AnalyticOnNhd ℂ g (ball 0 1 ∪ ball a ε) ∧
      InjOn g (ball a ε) ∧ EqOn g f (ball 0 1) ∧ g a=f a := by
  exact exists_disc_continuation_across_analytic_target_arc hf hfc hfi ha e he hei hfa h0
    (fun w hw hws => re_eq_zero_of_boundary_coordinate hU e hside (hfbd hw) hws)
    (fun w hw hws => (hside (f w) hws).mp (hfU hw))

end FunctionTheory
