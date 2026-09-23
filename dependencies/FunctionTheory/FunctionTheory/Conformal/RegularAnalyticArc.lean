import FunctionTheory.Conformal.AnalyticBoundaryContinuation
import Mathlib.Analysis.Complex.Convex

open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace FunctionTheory
set_option autoImplicit false

/-- The side of a reflected conformal map need not be prescribed: on the
connected open half-disc, a nonzero real part has a constant sign. -/
theorem exists_conformal_reflection_of_axis_avoidance
    {H : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (hc : ContinuousOn H (ball 0 r ∩ {z : ℂ | 0≤z.re}))
    (hd : DifferentiableOn ℂ H (ball 0 r ∩ {z : ℂ | 0<z.re}))
    (ha : ∀ z∈ball (0:ℂ) r, z.re=0 → (H z).re=0) (h0 : H 0=0)
    (hne : ∀ z∈ball (0:ℂ) r, 0<z.re → (H z).re≠0)
    (hi : InjOn H (ball 0 r ∩ {z : ℂ | 0<z.re})) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 r) ∧ InjOn G (ball 0 r) ∧
      EqOn G H (ball 0 r ∩ {z : ℂ | 0≤z.re}) ∧ G 0=0 := by
  have hs : IsPreconnected (ball (0:ℂ) r ∩ {z : ℂ | 0<z.re}) :=
    ((convex_ball (0:ℂ) r).inter (convex_halfSpace_re_gt 0)).isPreconnected
  have hrc : ContinuousOn (fun z => (H z).re) (ball 0 r ∩ {z : ℂ | 0<z.re}) :=
    Complex.continuous_re.comp_continuousOn hd.continuousOn
  have hsym : MapsTo (fun z : ℂ => -conj z) (ball 0 r) (ball 0 r) :=
    fun z hz => by simpa only [mem_ball,dist_zero_right,norm_neg,norm_conj] using hz
  rcases hs.mapsTo_Ioi_or_Iio hrc (fun z hz => hne z hz.1 hz.2) with hp | hn
  · obtain ⟨G,hG,hGi,hGH,hG0,-⟩ := exists_conformal_reflection_at_zero
      isOpen_ball (convex_ball (0:ℂ) r).isPreconnected (mem_ball_self hr)
      hsym hc hd ha h0 (fun z hz hzre => hp ⟨hz,hzre⟩) hi
    exact ⟨G,hG,hGi,hGH,hG0⟩
  · have hnegaxis : ∀ z∈ball (0:ℂ) r, z.re=0 → (-H z).re=0 := by
      intro z hz hz0
      simp only [neg_re,ha z hz hz0,neg_zero]
    obtain ⟨G,hG,hGi,hGH,hG0,-⟩ := exists_conformal_reflection_at_zero
      isOpen_ball (convex_ball (0:ℂ) r).isPreconnected (mem_ball_self hr)
      hsym hc.neg hd.neg hnegaxis (by simp [h0])
      (fun z hz hzre => by simpa only [Pi.neg_apply,neg_re] using neg_pos.mpr (hn ⟨hz,hzre⟩))
      (fun z hz w hw Hzw => hi hz hw (neg_injective Hzw))
    refine ⟨fun z => -G z,hG.neg,?_,?_,by simp [hG0]⟩
    · intro z hz w hw Hzw
      exact hGi hz hw (neg_injective Hzw)
    · intro z hz
      simpa only [Pi.neg_apply,neg_neg] using congrArg Neg.neg (hGH hz)

/-- Schwarz reflection across a regular analytic target arc, expressed by
an actual local conformal coordinate straightening that arc. The input map
is only required on a half-disc; injectivity of the continuation is local. -/
theorem exists_conformal_reflection_in_analytic_coordinate_of_axis_avoidance
    {H : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (hHc : ContinuousOn H (ball 0 r ∩ {z : ℂ | 0 ≤ z.re}))
    (hHd : DifferentiableOn ℂ H (ball 0 r ∩ {z : ℂ | 0 < z.re}))
    (hHi : InjOn H (ball 0 r ∩ {z : ℂ | 0 < z.re}))
    (hHS : MapsTo H (ball 0 r ∩ {z : ℂ | 0 ≤ z.re}) e.source)
    (haxis : ∀ z ∈ ball (0 : ℂ) r, z.re = 0 → (e (H z)).re = 0)
    (hnot : ∀ z ∈ ball (0 : ℂ) r, 0 < z.re → (e (H z)).re ≠ 0)
    (h0 : e (H 0)=0) :
    ∃ δ : ℝ, ∃ F : ℂ → ℂ, 0 < δ ∧ δ ≤ r ∧
      DifferentiableOn ℂ F (ball 0 δ) ∧ InjOn F (ball 0 δ) ∧
      EqOn F H (ball 0 δ ∩ {z : ℂ | 0 ≤ z.re}) := by
  let Q := fun z => e (H z)
  have hsub : ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.re} ⊆
      ball 0 r ∩ {z : ℂ | 0 ≤ z.re} := fun z hz => ⟨hz.1,(show 0<z.re from hz.2).le⟩
  have hQc : ContinuousOn Q (ball 0 r ∩ {z : ℂ | 0 ≤ z.re}) :=
    e.continuousOn.comp hHc hHS
  have hQd : DifferentiableOn ℂ Q (ball 0 r ∩ {z : ℂ | 0 < z.re}) :=
    he.comp hHd (hHS.mono hsub (subset_refl _))
  have hQi : InjOn Q (ball 0 r ∩ {z : ℂ | 0 < z.re}) := by
    intro z hz w hw hzw
    exact hHi hz hw (e.injOn (hHS (hsub hz)) (hHS (hsub hw)) hzw)
  have hsym : MapsTo (fun z : ℂ => -conj z) (ball 0 r) (ball 0 r) :=
    fun z hz => by simpa only [mem_ball,dist_zero_right,norm_neg,norm_conj] using hz
  obtain ⟨G,hGd,hGi,hGQ,hG0⟩ := exists_conformal_reflection_of_axis_avoidance
    hr hQc hQd haxis h0 hnot hQi
  have h0T : (0 : ℂ) ∈ e.target := h0 ▸ e.map_source (hHS ⟨mem_ball_self hr,by simp⟩)
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), G z ∈ e.target :=
    (hGd.continuousOn.continuousAt (ball_mem_nhds 0 hr))
      (by simpa only [hG0] using e.open_target.mem_nhds h0T)
  obtain ⟨s,hs,hsG⟩ := Metric.mem_nhds_iff.mp hev
  let δ := min s r
  have hδ : 0 < δ := lt_min hs hr
  have hδr : δ ≤ r := min_le_right _ _
  have hGT : MapsTo G (ball 0 δ) e.target :=
    fun z hz => hsG (ball_subset_ball (min_le_left _ _) hz)
  refine ⟨δ,fun z => e.symm (G z),hδ,hδr,?_,?_,?_⟩
  · exact hei.comp (hGd.mono (ball_subset_ball hδr)) hGT
  · intro z hz w hw H
    exact hGi (ball_subset_ball hδr hz) (ball_subset_ball hδr hw)
      (e.symm.injOn (hGT hz) (hGT hw) H)
  · intro z hz
    change e.symm (G z)=H z
    rw [hGQ ⟨ball_subset_ball hδr hz.1,hz.2⟩]
    exact e.left_inv (hHS ⟨ball_subset_ball hδr hz.1,hz.2⟩)

/-- A disc map continuous on the closed disc continues conformally through
a regular analytic target arc. The local target coordinate sends the relevant boundary arc to the imaginary
axis. Connectedness determines the side occupied by the local disc cap. -/
theorem exists_disc_continuation_across_analytic_arc_of_axis_avoidance
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hfc : ContinuousOn f (closedBall 0 1)) (hfi : InjOn f (ball 0 1))
    {a : ℂ} (ha : ‖a‖=1) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (hfa : f a∈e.source) (h0 : e (f a)=0)
    (haxis : ∀ w∈sphere (0:ℂ) 1, f w∈e.source → (e (f w)).re=0)
    (hnot : ∀ w∈ball (0:ℂ) 1, f w∈e.source → (e (f w)).re≠0) :
    ∃ ε : ℝ, ∃ g : ℂ → ℂ, 0<ε ∧
      AnalyticOnNhd ℂ g (ball 0 1 ∪ ball a ε) ∧
      InjOn g (ball a ε) ∧ EqOn g f (ball 0 1) ∧ g a=f a := by
  have ha0 : a≠0 := by intro H; simp [H] at ha
  let A := fun z => a*cayleyCoordinate z
  let H := fun z => f (A z)
  have hAc : ContinuousOn A {z : ℂ | 0≤z.re} := by
    intro z hz
    exact (continuousAt_const.mul (differentiableAt_cayleyCoordinate
      (cayley_denominator_ne_zero hz)).continuousAt).continuousWithinAt
  have hAclosed : MapsTo A {z : ℂ | 0≤z.re} (closedBall 0 1) := by
    intro z hz
    have hc := cayleyCoordinate_mem_closedBall hz
    simpa only [A,mem_closedBall,dist_zero_right,norm_mul,ha,one_mul] using hc
  have hAopen : MapsTo A {z : ℂ | 0<z.re} (ball 0 1) := by
    intro z hz
    have hc := cayleyCoordinate_mem_ball hz
    simpa only [A,mem_ball,dist_zero_right,norm_mul,ha,one_mul] using hc
  have hHC : ContinuousOn H {z : ℂ | 0≤z.re} := hfc.comp hAc hAclosed
  have hH0 : H 0=f a := by simp [H,A]
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | 0≤z.re}] (0:ℂ), H z∈e.source :=
    hHC 0 (by simp) (by simpa only [hH0] using e.open_source.mem_nhds hfa)
  obtain ⟨r,hr,hrH⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  have hHS : MapsTo H (ball 0 r ∩ {z : ℂ | 0≤z.re}) e.source :=
    fun z hz => hrH hz.1 hz.2
  have hHd : DifferentiableOn ℂ H (ball 0 r ∩ {z : ℂ | 0<z.re}) := by
    apply hf.comp ?_ (fun z hz => hAopen hz.2)
    intro z hz
    exact ((differentiableAt_cayleyCoordinate
      (cayley_denominator_ne_zero (show 0<z.re from hz.2).le)).const_mul a).differentiableWithinAt
  have hHi : InjOn H (ball 0 r ∩ {z : ℂ | 0<z.re}) := by
    intro z hz w hw Hzw
    have heq := hfi (hAopen hz.2) (hAopen hw.2) Hzw
    have hc : cayleyCoordinate z=cayleyCoordinate w := mul_left_cancel₀ ha0 heq
    exact cayleyCoordinate_injOn
      (cayley_denominator_ne_zero (show 0<z.re from hz.2).le)
      (cayley_denominator_ne_zero (show 0<w.re from hw.2).le) hc
  have hHa : ∀ z∈ball (0:ℂ) r, z.re=0 → (e (H z)).re=0 := by
    intro z hz hz0
    apply haxis (A z) ?_ (hHS ⟨hz,by simpa [hz0]⟩)
    have hc := cayleyCoordinate_mem_sphere hz0
    simpa only [A,mem_sphere,dist_zero_right,norm_mul,ha,one_mul] using hc
  have hHp : ∀ z∈ball (0:ℂ) r, 0<z.re → (e (H z)).re≠0 :=
    fun z hz hp => hnot (A z) (hAopen hp) (hHS ⟨hz,hp.le⟩)
  obtain ⟨δ,G,hδ,-,hG,hGi,hGH⟩ := exists_conformal_reflection_in_analytic_coordinate_of_axis_avoidance
    hr e he hei (hHC.mono inter_subset_right) hHd hHi hHS hHa hHp (by rw [hH0,h0])
  exact exists_disc_continuation_of_half_disc_extension ha hδ hf hG hGi hGH

/-- A set is a regular analytic arc near a point when a local conformal
coordinate identifies it with the imaginary axis. This is the usual local
coordinate characterisation of a regularly parametrised real-analytic curve;
no side of a neighbouring domain is prescribed. -/
def HasRegularAnalyticArcAt (S : Set ℂ) (p : ℂ) : Prop :=
  ∃ e : OpenPartialHomeomorph ℂ ℂ, p∈e.source ∧
    AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
    e p=0 ∧ ∀ z∈e.source, z∈S ↔ (e z).re=0

/-- Reflection of a closed-disc-continuous conformal parametrisation
through a regular analytic arc of the target boundary. No global orientation
or one-sided-domain assumption is added to the analytic-arc hypothesis. -/
theorem exists_disc_continuation_of_regular_analytic_boundary_arc
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfc : ContinuousOn f (closedBall 0 1))
    (hfi : InjOn f (ball 0 1)) (hfU : MapsTo f (ball 0 1) U)
    (hfbd : MapsTo f (sphere 0 1) (frontier U))
    {a : ℂ} (ha : ‖a‖=1) (harc : HasRegularAnalyticArcAt (frontier U) (f a)) :
    ∃ ε : ℝ, ∃ g : ℂ → ℂ, 0<ε ∧
      AnalyticOnNhd ℂ g (ball 0 1 ∪ ball a ε) ∧
      InjOn g (ball a ε) ∧ EqOn g f (ball 0 1) ∧ g a=f a := by
  obtain ⟨e,hfa,he,hei,h0,haxis⟩ := harc
  exact exists_disc_continuation_across_analytic_arc_of_axis_avoidance hf hfc hfi ha
    e he.differentiableOn hei.differentiableOn hfa h0
    (fun w hw hws => (haxis (f w) hws).mp (hfbd hw))
    (fun w hw hws H => (hU.frontier_eq ▸ (haxis (f w) hws).mpr H).2 (hfU hw))

end FunctionTheory
