import FunctionTheory.NormalFamilies.FiniteChartConvergence
import TauCeti.Analysis.Complex.Conformal.Hurwitz

/-! # Omitted values in spherical limits
Holomorphy and omission are only required eventually on each bounded disc.
The proof uses finite-chart convergence, Tau Ceti Hurwitz and connectedness. -/

open Set Filter Metric OnePoint
open scoped Topology
namespace FunctionTheory
open NoWanderingDomains
set_option autoImplicit false

/-- Restriction of a sphere-valued holomorphic map to an open subset. -/
theorem sphereHolomorphicOn_mono {F : ℂ → ℂ̂} {U V : Set ℂ}
    (hF : SphereHolomorphicOn F U) (hV : IsOpen V) (hVU : V ⊆ U) :
    SphereHolomorphicOn F V := by
  intro z hz
  obtain ⟨W,hW,hzW,hWU,hcases⟩ := hF z (hVU hz)
  refine ⟨W ∩ V,hW.inter hV,⟨hzW,hz⟩,inter_subset_right,?_⟩
  rcases hcases with ⟨hne,hd⟩ | ⟨hne,hd⟩
  · exact Or.inl ⟨fun w hw => hne w hw.1,hd.mono inter_subset_left⟩
  · exact Or.inr ⟨fun w hw => hne w hw.1,hd.mono inter_subset_left⟩

/-- Spherical Hurwitz for a finite omitted value. Holomorphy and omission are
only required eventually on every bounded disc, as in Zalcman rescalings. -/
theorem spherical_hurwitz_finite {F : ℕ → ℂ → ℂ̂} {G : ℂ → ℂ̂} {v : ℂ}
    (hGc : Continuous G) (hFG : TendstoLocallyUniformlyOn F G atTop univ)
    (hF : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      SphereHolomorphicOn (F n) (ball 0 R) ∧
      ∀ z ∈ ball 0 R, F n z ≠ (v : ℂ̂)) :
    (∀ z, G z ≠ (v : ℂ̂)) ∨ (∀ z, G z = (v : ℂ̂)) := by
  classical
  by_cases hn : ∀ z, G z ≠ (v : ℂ̂)
  · exact Or.inl hn
  push Not at hn
  obtain ⟨z₁,hz₁⟩ := hn
  have hcl : IsClosed {z | G z = (v : ℂ̂)} := isClosed_eq hGc continuous_const
  have hop : IsOpen {z | G z = (v : ℂ̂)} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    change G x = (v : ℂ̂) at hx
    obtain ⟨r,hr,-,hGne,hFne,hconv⟩ := exists_finite_chart_convergence
      isOpen_univ hGc.continuousOn hFG (mem_univ x)
      (by rw [hx]; exact OnePoint.coe_ne_infty v)
    have hR : 0 < ‖x‖ + r + 1 := by positivity
    have hsub : ball x r ⊆ ball (0 : ℂ) (‖x‖ + r + 1) := by
      intro w hw
      rw [mem_ball,dist_zero_right]
      have hw' : ‖w - x‖ < r := by simpa [dist_eq_norm] using hw
      have ht : ‖w‖ ≤ ‖w - x‖ + ‖x‖ := by
        simpa using norm_add_le (w - x) x
      linarith
    have hev : ∀ᶠ n in atTop,
        DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball x r) ∧
        ∀ w ∈ ball x r, chartFiniteMap (F n w) ≠ v := by
      filter_upwards [hF _ hR,hFne] with n hn hne
      refine ⟨(sphereHolomorphicOn_mono hn.1 isOpen_ball hsub).differentiableOn_chartFiniteMap (fun w hw => hne w (ball_subset_closedBall hw)),?_⟩
      intro w hw heq
      apply hn.2 w (hsub hw)
      cases hp : F n w with
      | infty => exact False.elim (hne w (ball_subset_closedBall hw) hp)
      | coe a =>
        rw [hp] at heq
        exact congrArg (fun a : ℂ => (a : ℂ̂)) heq
    have hgconst : ∀ w ∈ ball x r, chartFiniteMap (G w) = v := by
      rcases TauCeti.hurwitz_forall_ne_or_forall_eq isOpen_ball (convex_ball x r).isPreconnected
        (hev.mono fun _ hn => hn.1)
        (hconv.tendstoLocallyUniformlyOn.mono ball_subset_closedBall)
        (hev.mono fun _ hn => hn.2) with h | h
      · exact False.elim (h x (mem_ball_self hr) (by rw [hx]; rfl))
      · exact h
    refine mem_of_superset (ball_mem_nhds x hr) ?_
    intro w hw
    change G w = (v : ℂ̂)
    have heq := hgconst w hw
    cases hp : G w with
    | infty => exact False.elim (hGne w (ball_subset_closedBall hw) hp)
    | coe a =>
      rw [hp] at heq
      exact congrArg (fun a : ℂ => (a : ℂ̂)) heq
  have hall := (show IsClopen {z | G z = (v : ℂ̂)} from ⟨hcl,hop⟩).eq_univ ⟨z₁,hz₁⟩
  refine Or.inr (fun z => ?_)
  have hz : z ∈ {z | G z = (v : ℂ̂)} := by rw [hall]; trivial
  exact hz

/-- Spherical locally uniform convergence is preserved by inversion. -/
theorem tendstoLocallyUniformlyOn_sphere_inversion {F : ℕ → ℂ → ℂ̂}
    {G : ℂ → ℂ̂} {U : Set ℂ}
    (hFG : TendstoLocallyUniformlyOn F G atTop U) :
    TendstoLocallyUniformlyOn (fun n w => inversionGL • F n w)
      (fun w => inversionGL • G w) atTop U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hFG ⊢
  intro ε hε x hx
  obtain ⟨t,ht,hev⟩ := hFG ε hε x hx
  refine ⟨t,ht,hev.mono fun n hn y hy => ?_⟩
  exact lt_of_eq_of_lt (sphericalDist_inversionGL_smul (G y) (F n y)) (hn y hy)

/-- Spherical Hurwitz for the omitted value infinity. -/
theorem spherical_hurwitz_infty {F : ℕ → ℂ → ℂ̂} {G : ℂ → ℂ̂}
    (hGc : Continuous G) (hFG : TendstoLocallyUniformlyOn F G atTop univ)
    (hF : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      SphereHolomorphicOn (F n) (ball 0 R) ∧ ∀ z ∈ ball 0 R, F n z ≠ ∞) :
    (∀ z, G z ≠ ∞) ∨ (∀ z, G z = ∞) := by
  have hi : Function.Injective (fun p : ℂ̂ => inversionGL • p) :=
    MulAction.injective inversionGL
  have hv := spherical_hurwitz_finite
    ((continuous_gl_smul inversionGL).comp hGc)
    (tendstoLocallyUniformlyOn_sphere_inversion hFG) (v := 0)
    (fun R hR => (hF R hR).mono fun n hn => ⟨hn.1.gl_smul inversionGL,
      fun z hz heq => hn.2 z hz (hi (heq.trans inversionGL_smul_infty.symm))⟩)
  rcases hv with h | h
  · exact Or.inl (fun z heq => h z (by change inversionGL • G z = _; rw [heq,inversionGL_smul_infty]))
  · exact Or.inr (fun z => hi ((h z).trans inversionGL_smul_infty.symm))


end FunctionTheory
