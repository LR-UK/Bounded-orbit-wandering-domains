import FunctionTheory.Conformal.AnalyticSideContinuous
import FunctionTheory.Conformal.HalfDiskCircleReflection

open Set Metric Complex Filter Function
open scoped Topology ComplexConjugate
namespace FunctionTheory
set_option autoImplicit false

/-- Reflecting the disc map on a chosen analytic boundary side yields a
conformal extension of its inverse at the corresponding unit-circle point.
No global Jordan-boundary or closed-disc continuity hypothesis is used. -/
theorem exists_local_inverse_extension_at_analytic_side
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (hei : DifferentiableOn ℂ e.symm e.target)
    {R : ℝ} (hR : 0<R) (hT : closedBall (0:ℂ) R⊆e.target)
    (hhalf : ∀ z∈ball (0:ℂ) R, 0<z.re → e.symm z∈U)
    (hline : ∀ z∈ball (0:ℂ) R, z.re=0 → e.symm z∉U) :
    ∃ (ξ : ℂ) (ε : ℝ) (Ψ : ℂ → ℂ), ‖ξ‖=1 ∧ 0<ε ∧
      AnalyticOnNhd ℂ Ψ (ball ξ ε) ∧ InjOn Ψ (ball ξ ε) ∧ Ψ ξ=e.symm 0 ∧
      EqOn Ψ (invFunOn f U) (ball ξ ε∩ball 0 1) := by
  obtain ⟨H,hHc,hHf,hHa⟩ := exists_continuous_extension_at_analytic_side
    hU hf hbij e hei hR hT hhalf hline
  have hTU : MapsTo e.symm (ball (0:ℂ) (R/2)∩{z : ℂ | 0<z.re}) U :=
    fun z hz => hhalf z (ball_subset_ball (half_le_self hR.le) hz.1) hz.2
  have hTT : ball (0:ℂ) (R/2)∩{z : ℂ | 0<z.re}⊆e.target :=
    fun z hz => hT (ball_subset_closedBall (ball_subset_ball (half_le_self hR.le) hz.1))
  have hHd : DifferentiableOn ℂ H (ball (0:ℂ) (R/2)∩{z : ℂ | 0<z.re}) :=
    (hf.comp (hei.mono hTT) hTU).congr hHf
  have hHi : InjOn H (ball (0:ℂ) (R/2)∩{z : ℂ | 0<z.re}) := by
    intro z hz w hw Hzw
    rw [hHf hz,hHf hw] at Hzw
    exact e.symm.injOn (hTT hz) (hTT hw) (hbij.injOn (hTU hz) (hTU hw) Hzw)
  have hHD : MapsTo H (ball (0:ℂ) (R/2)∩{z : ℂ | 0<z.re}) (ball (0:ℂ) 1) := by
    intro z hz
    rw [hHf hz]
    exact hbij.mapsTo (hTU hz)
  obtain ⟨δ,F,hδ,hδR,hFd,hFi,hF0,hFH,hFs,hFpos⟩ :=
    exists_reflection_of_half_disk_map_to_circle (half_pos hR) hHc hHd hHi hHD hHa
  let ξ := H 0
  have hξ : ‖ξ‖=1 := by
    simpa only [mem_sphere,dist_zero_right] using hHa 0 (mem_ball_self (half_pos hR)) rfl
  have hξ0 : ξ≠0 := norm_ne_zero_iff.mp (by rw [hξ]; norm_num)
  let ψ := invFunOn F (ball (0:ℂ) δ)
  have hI : IsOpen (F '' ball (0:ℂ) δ) :=
    TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hFd hFi
  have h0I : (0:ℂ)∈F '' ball (0:ℂ) δ := ⟨0,mem_ball_self hδ,hF0⟩
  have hψa : AnalyticAt ℂ ψ 0 :=
    (DifferentiableOn.invFunOn hFd isOpen_ball hFi).analyticAt (hI.mem_nhds h0I)
  have hψ0 : ψ 0=0 := by simpa only [hF0] using hFi.leftInvOn_invFunOn (mem_ball_self hδ)
  let q : ℂ → ℂ := fun w => cayleyCoordinate (w/ξ)
  have hq0 : q ξ=0 := by simp [q,div_self hξ0]
  have hqa : AnalyticAt ℂ q ξ := by
    exact (analyticAt_const.sub analyticAt_id.div_const).div
      (analyticAt_const.add analyticAt_id.div_const) (by simp [div_self hξ0])
  let Ψ : ℂ → ℂ := fun w => e.symm (ψ (q w))
  have he0 : AnalyticAt ℂ e.symm 0 :=
    hei.analyticAt (e.open_target.mem_nhds (hT (mem_closedBall_self hR.le)))
  have hΨa : AnalyticAt ℂ Ψ ξ := by
    have Hψ : AnalyticAt ℂ ψ (q ξ) := by rwa [hq0]
    have He : AnalyticAt ℂ e.symm (ψ (q ξ)) := by simpa only [hq0,hψ0] using he0
    exact (He.comp Hψ).comp hqa
  have hΨ0 : Ψ ξ=e.symm 0 := by simp only [Ψ,hq0,hψ0]
  have hqnear : ∀ᶠ w in 𝓝 ξ, q w∈F '' ball (0:ℂ) δ :=
    hqa.continuousAt.preimage_mem_nhds (by simpa only [hq0] using hI.mem_nhds h0I)
  have hdennear : ∀ᶠ w : ℂ in 𝓝 ξ, 1+w/ξ≠0 :=
    (continuous_const.add (continuous_id.div_const ξ)).continuousAt.eventually_ne (by simp [div_self hξ0])
  have hnear : ∀ᶠ w : ℂ in 𝓝 ξ,
      q w∈F '' ball (0:ℂ) δ ∧ AnalyticAt ℂ Ψ w ∧ 1+w/ξ≠0 := by
    filter_upwards [hqnear,hΨa.eventually_analyticAt,hdennear] with w hw ha hd
    exact ⟨hw,ha,hd⟩
  obtain ⟨ε,hε,hεnear⟩ := Metric.mem_nhds_iff.mp hnear
  have hψprop : ∀ w∈ball ξ ε, ψ (q w)∈ball (0:ℂ) δ ∧ F (ψ (q w))=q w := by
    intro w hw
    obtain ⟨u,hu,huq⟩ := (hεnear hw).1
    have Hψ : ψ (q w)=u := by rw [← huq]; exact hFi.leftInvOn_invFunOn hu
    exact ⟨Hψ.symm ▸ hu,by rw [Hψ]; exact huq⟩
  have hsmallT : ball (0:ℂ) δ⊆e.target :=
    fun z hz => hT (ball_subset_closedBall (ball_subset_ball (hδR.trans (half_le_self hR.le)) hz))
  refine ⟨ξ,ε,Ψ,hξ,hε,fun w hw => (hεnear hw).2.1,?_,hΨ0,?_⟩
  · intro w hw v hv Hwv
    have Hψ : ψ (q w)=ψ (q v) := e.symm.injOn
      (hsmallT (hψprop w hw).1) (hsmallT (hψprop v hv).1) Hwv
    have Hq : q w=q v := (hψprop w hw).2.symm.trans ((congrArg F Hψ).trans (hψprop v hv).2)
    exact (div_left_inj' hξ0).mp (cayleyCoordinate_injOn (hεnear hw).2.2 (hεnear hv).2.2 Hq)
  · intro w hw
    let u := ψ (q w)
    have hu : u∈ball (0:ℂ) δ := (hψprop w hw.1).1
    have huq : F u=q w := (hψprop w hw.1).2
    have hwξ : w/ξ∈ball (0:ℂ) 1 := by
      simpa only [mem_ball,dist_zero_right,norm_div,hξ,div_one] using hw.2
    have hqpos : 0<(q w).re := re_cayleyCoordinate_pos_of_mem_ball hwξ
    have hupos : 0<u.re := by
      by_contra Hpos
      rcases lt_or_eq_of_le (le_of_not_gt Hpos) with hneg|hzero
      · have hu' : -conj u∈ball (0:ℂ) δ := by
          simpa only [mem_ball,dist_zero_right,norm_neg,norm_conj] using hu
        have Hp := hFpos _ hu' (by simpa using neg_pos.mpr hneg)
        rw [hFs u hu,huq] at Hp
        simp only [neg_re,conj_re] at Hp
        linarith
      · have Heq : -conj u=u := by apply Complex.ext <;> simp [hzero]
        have HH := congrArg Complex.re (hFs u hu)
        rw [Heq,huq] at HH
        simp only [neg_re,conj_re] at HH
        linarith
    have hur : u∈ball (0:ℂ) (R/2) := ball_subset_ball hδR hu
    have hHξ : H u/ξ∈ball (0:ℂ) 1 := by
      simpa only [mem_ball,dist_zero_right,norm_div,hξ,div_one] using hHD ⟨hur,hupos⟩
    have hHuw : H u=w := by
      have Hq : cayleyCoordinate (H u/ξ)=cayleyCoordinate (w/ξ) :=
        (hFH ⟨hu,hupos.le⟩).symm.trans huq
      exact (div_left_inj' hξ0).mp (cayleyCoordinate_injOn
        (cayley_denominator_ne_zero_of_mem_ball hHξ) (cayley_denominator_ne_zero_of_mem_ball hwξ) Hq)
    have huU : e.symm u∈U := hTU ⟨hur,hupos⟩
    have hfu : f (e.symm u)=w := (hHf ⟨hur,hupos⟩).symm.trans hHuw
    have hgi : invFunOn f U w=e.symm u := by
      rw [← hfu]
      exact hbij.injOn.leftInvOn_invFunOn huU
    exact hgi.symm

end FunctionTheory
