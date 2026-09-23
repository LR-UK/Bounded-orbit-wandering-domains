import FunctionTheory.Conformal.ReflectionInjectivity
import FunctionTheory.Conformal.CayleyCoordinates
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace FunctionTheory
set_option autoImplicit false

/-- Schwarz reflection across a regular analytic target arc, expressed by
an actual local conformal coordinate straightening that arc. The input map
is only required on a half-disc; injectivity of the continuation is local. -/
theorem exists_conformal_reflection_in_analytic_coordinate
    {H : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (hHc : ContinuousOn H (ball 0 r ∩ {z : ℂ | 0 ≤ z.re}))
    (hHd : DifferentiableOn ℂ H (ball 0 r ∩ {z : ℂ | 0 < z.re}))
    (hHi : InjOn H (ball 0 r ∩ {z : ℂ | 0 < z.re}))
    (hHS : MapsTo H (ball 0 r ∩ {z : ℂ | 0 ≤ z.re}) e.source)
    (haxis : ∀ z ∈ ball (0 : ℂ) r, z.re = 0 → (e (H z)).re = 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) r, 0 < z.re → 0 < (e (H z)).re)
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
  obtain ⟨G,hGd,hGi,hGQ,hG0,-⟩ := exists_conformal_reflection_at_zero
    isOpen_ball (convex_ball (0:ℂ) r).isPreconnected (mem_ball_self hr)
    hsym hQc hQd haxis h0 hpos hQi
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

/-- Transport a conformal half-disc reflection to a continuation of a disc
map across a specified unit-circle point. The extension is analytic on the
union, and injective on the new boundary neighbourhood. -/
theorem exists_disc_continuation_of_half_disc_extension
    {f G : ℂ → ℂ} {a : ℂ} (ha : ‖a‖=1) {δ : ℝ} (hδ : 0<δ)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hG : DifferentiableOn ℂ G (ball 0 δ)) (hGi : InjOn G (ball 0 δ))
    (hGf : EqOn G (fun z => f (a*cayleyCoordinate z))
      (ball 0 δ ∩ {z : ℂ | 0 ≤ z.re})) :
    ∃ ε : ℝ, ∃ e : ℂ → ℂ, 0<ε ∧
      AnalyticOnNhd ℂ e (ball 0 1 ∪ ball a ε) ∧
      InjOn e (ball a ε) ∧ EqOn e f (ball 0 1) ∧ e a=f a := by
  classical
  have ha0 : a≠0 := by intro H; simp [H] at ha
  let B := fun w => cayleyCoordinate (w/a)
  have hBa : B a=0 := by simp [B,cayleyCoordinate,div_self ha0]
  have hBda : DifferentiableAt ℂ B a :=
    (differentiableAt_cayleyCoordinate (by simp [div_self ha0])).comp a
      (differentiableAt_id.div_const a)
  have hdena : (1:ℂ)+a/a≠0 := by simp [div_self ha0]
  have hdenev : ∀ᶠ w in 𝓝 a, (1:ℂ)+w/a≠0 :=
    (continuous_const.add (continuous_id.div_const a)).continuousAt.eventually_ne hdena
  have hsmall : ∀ᶠ w in 𝓝 a, B w∈ball (0:ℂ) δ :=
    hBda.continuousAt (by simpa only [hBa] using ball_mem_nhds (0:ℂ) hδ)
  obtain ⟨ε,hε,hεsmall⟩ := Metric.mem_nhds_iff.mp (hsmall.and hdenev)
  let e := fun w => if w∈ball a ε then G (B w) else f w
  have hBwD : ∀ w∈ball (0:ℂ) 1, w/a∈ball (0:ℂ) 1 := by
    intro w hw
    simpa only [mem_ball,dist_zero_right,norm_div,ha,div_one] using hw
  have hAB : ∀ w∈ball (0:ℂ) 1, a*cayleyCoordinate (B w)=w := by
    intro w hw
    dsimp only [B]
    rw [cayleyCoordinate_involution (cayley_denominator_ne_zero_of_mem_ball (hBwD w hw))]
    field_simp
  have heq : EqOn e f (ball 0 1) := by
    intro w hw
    by_cases hwb : w∈ball a ε
    · have hp : 0<(B w).re := re_cayleyCoordinate_pos_of_mem_ball (hBwD w hw)
      simp only [e,if_pos hwb]
      rw [hGf ⟨(hεsmall hwb).1,hp.le⟩]
      exact congrArg f (hAB w hw)
    · simp only [e,if_neg hwb]
  have heb : ∀ w∈ball a ε, e w=G (B w) := fun w hw => if_pos hw
  have haB : a∈ball a ε := mem_ball_self hε
  refine ⟨ε,e,hε,?_,?_,heq,?_⟩
  · intro w hw
    rcases hw with hw | hw
    · apply ((hf.analyticOnNhd isOpen_ball) w hw).congr
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact (heq hz).symm
    · have hB : AnalyticAt ℂ B w := by
        change AnalyticAt ℂ (fun z : ℂ => (1-z/a)/(1+z/a)) w
        exact (analyticAt_const.sub (analyticAt_id.div analyticAt_const ha0)).div
          (analyticAt_const.add (analyticAt_id.div analyticAt_const ha0)) (hεsmall hw).2
      have hg : AnalyticAt ℂ (fun w => G (B w)) w :=
        ((hG.analyticOnNhd isOpen_ball) _ (hεsmall hw).1).comp hB
      apply hg.congr
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact (heb z hz).symm
  · intro w hw z hz H
    rw [heb w hw,heb z hz] at H
    have H' := hGi (hεsmall hw).1 (hεsmall hz).1 H
    have H'' := cayleyCoordinate_injOn (hεsmall hw).2 (hεsmall hz).2 H'
    exact (div_left_inj' ha0).mp H''
  · rw [heb a haB,hBa,hGf ⟨mem_ball_self hδ,by simp⟩]
    simp [cayleyCoordinate]

/-- A disc map continuous on the closed disc continues conformally through
a regular analytic target arc. The local target coordinate sends the relevant
boundary arc to the imaginary axis and the domain side to the right halfplane. -/
theorem exists_disc_continuation_across_analytic_target_arc
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hfc : ContinuousOn f (closedBall 0 1)) (hfi : InjOn f (ball 0 1))
    {a : ℂ} (ha : ‖a‖=1) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (hfa : f a∈e.source) (h0 : e (f a)=0)
    (haxis : ∀ w∈sphere (0:ℂ) 1, f w∈e.source → (e (f w)).re=0)
    (hpos : ∀ w∈ball (0:ℂ) 1, f w∈e.source → 0<(e (f w)).re) :
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
  have hHp : ∀ z∈ball (0:ℂ) r, 0<z.re → 0<(e (H z)).re :=
    fun z hz hp => hpos (A z) (hAopen hp) (hHS ⟨hz,hp.le⟩)
  obtain ⟨δ,G,hδ,-,hG,hGi,hGH⟩ := exists_conformal_reflection_in_analytic_coordinate
    hr e he hei (hHC.mono inter_subset_right) hHd hHi hHS hHa hHp (by rw [hH0,h0])
  exact exists_disc_continuation_of_half_disc_extension ha hδ hf hG hGi hGH

end FunctionTheory
