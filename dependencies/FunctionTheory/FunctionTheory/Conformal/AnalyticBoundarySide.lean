import FunctionTheory.Conformal.RegularAnalyticArc

open Set Metric Complex Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- At a boundary locally straightened by a homeomorphism, at least one
of the two half-neighbourhoods belongs to the domain. Both may belong to
it, as at a slit. No global Jordan condition is needed. -/
theorem exists_occupied_side_of_boundary_coordinate
    {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p∈frontier U)
    (e : OpenPartialHomeomorph ℂ ℂ) (hps : p∈e.source) (hep : e p=0)
    (haxis : ∀ z∈e.source, z∈frontier U ↔ (e z).re=0) :
    ∃ R : ℝ, 0<R ∧ closedBall (0:ℂ) R⊆e.target ∧
      (∀ z∈ball (0:ℂ) R, z.re=0 → e.symm z∉U) ∧
      ((∀ z∈ball (0:ℂ) R, 0<z.re → e.symm z∈U) ∨
       (∀ z∈ball (0:ℂ) R, z.re<0 → e.symm z∈U)) := by
  have h0T : (0:ℂ)∈e.target := hep ▸ e.map_source hps
  obtain ⟨r,hr,hrT⟩ := Metric.isOpen_iff.mp e.open_target 0 h0T
  let R := r/2
  have hR : 0<R := half_pos hr
  have hRT : closedBall (0:ℂ) R⊆e.target := (closedBall_subset_ball (half_lt_self hr)).trans hrT
  have hballT : ball (0:ℂ) R⊆e.target := ball_subset_closedBall.trans hRT
  have hline : ∀ z∈ball (0:ℂ) R, z.re=0 → e.symm z∉U := by
    intro z hz hre hmem
    have Hfront : e.symm z∈frontier U := (haxis _ (e.symm.map_source (hballT hz))).mpr
      (by rwa [e.right_inv (hballT hz)])
    exact ((hU.frontier_eq ▸ Hfront).2) hmem
  have hN : e.source∩e ⁻¹' ball (0:ℂ) R∈𝓝 p := by
    apply Filter.inter_mem (e.open_source.mem_nhds hps)
    apply (e.continuousAt hps).preimage_mem_nhds
    simpa only [hep] using isOpen_ball.mem_nhds (mem_ball_self hR)
  obtain ⟨x,hxN,hxU⟩ := mem_closure_iff_nhds.mp hp.1 _ hN
  have hxT : e x∈ball (0:ℂ) R := hxN.2
  have hxSource : x∈e.source := hxN.1
  have hxinv : e.symm (e x)=x := e.left_inv hxSource
  have hxre : (e x).re≠0 := by
    intro H
    exact hline (e x) hxT H (hxinv.symm ▸ hxU)
  have Hside (S : Set ℂ) (hSc : IsPreconnected S) (hSR : S⊆ball (0:ℂ) R)
      (hSn : ∀ z∈S, z.re≠0) (hxS : e x∈S) : MapsTo e.symm S U := by
    have hST : S⊆e.target := hSR.trans hballT
    have hIc : IsPreconnected (e.symm '' S) := hSc.image e.symm (e.symm.continuousOn.mono hST)
    have hne : (e.symm '' S∩U).Nonempty := ⟨x,⟨e x,hxS,hxinv⟩,hxU⟩
    apply image_subset_iff.mp
    apply hIc.subset_of_closure_inter_subset hU hne
    rintro y ⟨hyc,w,hw,rfl⟩
    by_contra hnot
    have hyfront : e.symm w∈frontier U := by rw [hU.frontier_eq]; exact ⟨hyc,hnot⟩
    have Hre := (haxis _ (e.symm.map_source (hST hw))).mp hyfront
    rw [e.right_inv (hST hw)] at Hre
    exact hSn w hw Hre
  refine ⟨R,hR,hRT,hline,?_⟩
  rcases lt_or_gt_of_ne hxre with hneg|hpos
  · right
    have H := Hside (ball (0:ℂ) R∩{z : ℂ | z.re<0})
      ((convex_ball (0:ℂ) R).inter (convex_halfSpace_re_lt 0)).isPreconnected inter_subset_left
      (fun z hz => (show z.re<0 from hz.2).ne) ⟨hxT,hneg⟩
    exact fun z hz hzre => H ⟨hz,hzre⟩
  · left
    have H := Hside (ball (0:ℂ) R∩{z : ℂ | 0<z.re})
      ((convex_ball (0:ℂ) R).inter (convex_halfSpace_re_gt 0)).isPreconnected inter_subset_left
      (fun z hz => (show 0<z.re from hz.2).ne') ⟨hxT,hpos⟩
    exact fun z hz hzre => H ⟨hz,hzre⟩

end FunctionTheory
