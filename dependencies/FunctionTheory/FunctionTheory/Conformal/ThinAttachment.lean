import FunctionTheory.Conformal.UniformLengthArea
import FunctionTheory.Conformal.SeparatingCrosscut
import FunctionTheory.Conformal.RightCircularCut

open Set Metric Complex
open scoped ENNReal

namespace FunctionTheory

/-- A short semicircle across a narrow attachment sends the entire left side
far to the left. The estimate is independent of the shape of that side. -/
theorem leftward_bound_of_short_semicircle
    {U : Set ℂ} {f g : ℂ → ℂ} {ζ b : ℂ} {r ρ δ : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hfU : MapsTo f U (ball 0 1))
    (hg : ContinuousOn g (ball 0 1)) (hgU : MapsTo g (ball 0 1) U)
    (hfg : RightInvOn g f (ball 0 1)) (hgf : LeftInvOn g f U)
    (hρ : 0 < ρ) (hrρ : r < ρ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgate : ∀ w ∈ U, w.re = ζ.re → dist w ζ ≤ r)
    (harc : ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), circleMap ζ ρ θ ∈ U)
    (hlen : TauCeti.circleImageLength f U ζ ρ < ENNReal.ofReal (δ / 2))
    (hanchor : dist (f (ζ + ρ)) (-1) < δ / 2)
    (hb : b ∈ ball (0 : ℂ) 1 \ closedBall (-1 : ℂ) δ)
    (hbside : ζ.re < (g b).re ∧ ρ < dist (g b) ζ) :
    ∀ x ∈ U, x.re < ζ.re →
      (discToHorizontalStrip (f x)).re ≤ Real.log δ := by
  have hzero : ∀ z ∈ U, rightCircularCut ζ ρ z = 0 →
      f z ∈ closedBall (-1 : ℂ) δ := by
    intro z hz hcut
    obtain ⟨θ, hθ, rfl⟩ := exists_right_semicircle_of_rightCircularCut_eq_zero hrρ hgate hz hcut
    have hdist := dist_image_right_semicircle_lt_of_length_lt hU hf hρ harc hlen hθ
    change dist _ (-1) ≤ δ
    have ht := dist_triangle (f (circleMap ζ ρ θ)) (f (ζ + ρ)) (-1)
    linarith
  have hbound := leftward_strip_bound_of_separating_barrier
    (X := {x ∈ U | x.re < ζ.re}) hg hgU (continuous_rightCircularCut ζ ρ).continuousOn
    hfg (hfU.mono_left (fun _ hx => hx.1)) (hgf.mono (fun _ hx => hx.1))
    (fun x hx => (rightCircularCut_neg_of_re_lt hx.2).le) hδ hδ1 hb
    (rightCircularCut_pos_iff.mpr hbside) hzero
  exact fun x hx hleft => hbound x ⟨hx, hleft⟩

/-- Uniform narrow-attachment estimate. The allowable gate size is chosen
before the domain and map; the only convergence input required later is on
the compact interior segment `ζ + [r,R]`. -/
theorem exists_gate_size_for_uniform_leftward_bound
    {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < R) :
    ∃ r ∈ Ioo 0 R, ∀ (U : Set ℂ) (f g : ℂ → ℂ) (ζ b : ℂ),
      IsOpen U → DifferentiableOn ℂ f U → InjOn f U → MapsTo f U (ball 0 1) →
      ContinuousOn g (ball 0 1) → MapsTo g (ball 0 1) U →
      RightInvOn g f (ball 0 1) → LeftInvOn g f U →
      (∀ w ∈ U, w.re = ζ.re → dist w ζ ≤ r) →
      (∀ ρ ∈ Ioo r R, ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2),
        circleMap ζ ρ θ ∈ U) →
      (∀ ρ ∈ Ioo r R, dist (f (ζ + ρ)) (-1) < δ / 2) →
      b ∈ ball (0 : ℂ) 1 \ closedBall (-1 : ℂ) δ →
      ζ.re < (g b).re → R ≤ dist (g b) ζ →
      ∀ x ∈ U, x.re < ζ.re → (discToHorizontalStrip (f x)).re ≤ Real.log δ := by
  obtain ⟨r, hr, hchoice⟩ := exists_uniform_annulus_of_bounded_image
    (B := ball (0 : ℂ) 1) isBounded_ball (half_pos hδ) hR
  refine ⟨r, hr, ?_⟩
  intro U f g ζ b hU hf hinj hfU hg hgU hfg hgf hgate harc hanchor hb hbre hbdist
  obtain ⟨ρ, hρ, hlen⟩ := hchoice U f ζ hU hf hinj hfU
  exact leftward_bound_of_short_semicircle hU hf hfU hg hgU hfg hgf
    (hr.1.trans hρ.1) hρ.1 hδ hδ1 hgate (harc ρ hρ) hlen (hanchor ρ hρ) hb
    ⟨hbre, hρ.2.trans_le hbdist⟩

end FunctionTheory
