import BoundedWanderingDomains.GreenIdentity
import BoundedWanderingDomains.Regularisation

open MeasureTheory Filter Set InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

theorem pd_comp {u : ℂ → ℝ} {B : ℝ → ℝ} {x v : ℂ} {b : ℝ}
    (hu : DifferentiableAt ℝ u x) (hB : HasDerivAt B b (u x)) :
    pd (fun y => B (u y)) v x = b * pd u v x := by
  have hh := (hB.comp_hasFDerivAt x hu.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hh
  change fderiv ℝ (fun y => B (u y)) x v = _
  rw [hh]
  rfl

theorem pd2_comp {u : ℂ → ℝ} {B B₁ B₂ : ℝ → ℝ} {x : ℂ}
    (hu : ContDiffAt ℝ 2 u x)
    (hB : ∀ t, HasDerivAt B (B₁ t) t)
    (hB₁ : ∀ t, HasDerivAt B₁ (B₂ t) t) (v : ℂ) :
    pd (pd (fun y => B (u y)) v) v x =
      B₁ (u x) * pd (pd u v) v x + B₂ (u x) * (pd u v x) ^ 2 := by
  have heq : pd (fun y => B (u y)) v =ᶠ[𝓝 x]
      (fun y => B₁ (u y) * pd u v y) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact pd_comp (hy.differentiableAt (by norm_num)) (hB (u y))
  have hdu := hu.differentiableAt (by norm_num)
  have hdpu := (pd_contDiffAt (n := 1) hu v).differentiableAt (by norm_num)
  have hprod := ((hB₁ (u x)).comp_hasFDerivAt x hdu.hasFDerivAt).mul hdpu.hasFDerivAt
  simp only [Function.comp_def, Pi.mul_def, pd] at hprod
  unfold pd at heq ⊢
  rw [heq.fderiv_eq, hprod.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change B₁ (u x) * pd (pd u v) v x + pd u v x * (B₂ (u x) * pd u v x) =
    B₁ (u x) * pd (pd u v) v x + B₂ (u x) * (pd u v x)^2
  ring

noncomputable def gradientSq (u : ℂ → ℝ) (x : ℂ) : ℝ :=
  (pd u 1 x)^2 + (pd u Complex.I x)^2

theorem gradientSq_nonneg (u : ℂ → ℝ) (x : ℂ) : 0 ≤ gradientSq u x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem laplacian_comp {u : ℂ → ℝ} {B B₁ B₂ : ℝ → ℝ} {x : ℂ}
    (hu : ContDiffAt ℝ 2 u x) (hBc : ContDiff ℝ 2 B)
    (hB : ∀ t, HasDerivAt B (B₁ t) t)
    (hB₁ : ∀ t, HasDerivAt B₁ (B₂ t) t) :
    Δ (fun y => B (u y)) x = B₁ (u x) * Δ u x + B₂ (u x) * gradientSq u x := by
  have hcu : ContDiffAt ℝ 2 (fun y => B (u y)) x := hBc.contDiffAt.comp x hu
  rw [laplacian_eq_pd2 hcu,
    pd2_comp hu hB hB₁, pd2_comp hu hB hB₁, laplacian_eq_pd2 hu]
  unfold gradientSq
  ring

theorem scaled_transition_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => Real.smoothTransition (((n : ℝ) + 1) * s))
      (((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * t)) t := by
  convert (transition_hasDerivAt (((n : ℝ) + 1) * t)).comp t
    ((hasDerivAt_id t).const_mul ((n : ℝ) + 1)) using 1 <;> simp [Function.comp_def, mul_comm]

theorem laplacian_betaScaled {u : ℂ → ℝ} {x : ℂ}
    (hu : ContDiffAt ℝ 2 u x) (n : ℕ) :
    Δ (fun y => betaScaled n (u y)) x =
      Real.smoothTransition (((n : ℝ) + 1) * u x) * Δ u x +
      (((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * u x)) *
        gradientSq u x := by
  exact laplacian_comp hu ((betaScaled_contDiff n).of_le (by simp))
    (betaScaled_hasDerivAt n) (scaled_transition_hasDerivAt n)

end AreaDeficit
