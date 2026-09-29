module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.SphereChartCompact
public import BoundedWanderingDomains.ConformalDensityInvariance

@[expose] public section

/-!
# Transition maps between pole charts of the Riemann sphere

The transition maps are conformal wherever they are defined.  We record
their inverse and obstacle-pullback properties without expanding them into
fractional-linear formulae.
-/

open Set Function OnePoint MeasureTheory
open scoped Topology RiemannSphere ContDiff

namespace AreaDeficit

/-- Coordinate change from the chart omitting `q` to the chart omitting
`p`. Its value at the one excluded coordinate is immaterial. -/
noncomputable def sphereChartTransition (p q : OnePoint ℂ) : ℂ → ℂ :=
  fun z => (spherePoleChart p).symm (spherePoleChart q z)

theorem spherePoleChart_contMDiff (p : OnePoint ℂ) :
    ContMDiff OneDimension.I OneDimension.I ⊤ (spherePoleChart p) := by
  induction p using OnePoint.rec with
  | infty => exact RiemannSphere.mAnalytic_coe
  | coe a => exact RiemannSphere.mAnalytic_omittedPointParam a

theorem spherePoleChart_symm_contMDiffAt {p z : OnePoint ℂ} (hz : z ≠ p) :
    ContMDiffAt OneDimension.I OneDimension.I ⊤ (spherePoleChart p).symm z := by
  induction p using OnePoint.rec with
  | infty =>
      exact RiemannSphere.mAnalyticAt_toComplex' hz
  | coe a =>
      exact RiemannSphere.mAnalyticAt_omittedPointParam_symm a hz

theorem sphereChartTransition_differentiableAt {p q : OnePoint ℂ} {z : ℂ}
    (hz : spherePoleChart q z ≠ p) :
    DifferentiableAt ℂ (sphereChartTransition p q) z := by
  have h := (spherePoleChart_symm_contMDiffAt hz).comp z
    (spherePoleChart_contMDiff q).contMDiffAt
  convert h.contDiffAt.differentiableAt (by simp) using 1
  ext w
  rfl

theorem spherePoleChart_transition {p q : OnePoint ℂ} {z : ℂ}
    (hz : spherePoleChart q z ≠ p) :
    spherePoleChart p (sphereChartTransition p q z) = spherePoleChart q z := by
  exact (spherePoleChart p).right_inv (by
    rw [spherePoleChart_target]
    exact hz)

theorem sphereChartTransition_inverse {p q : OnePoint ℂ} {z : ℂ}
    (hz : spherePoleChart q z ≠ p) :
    sphereChartTransition q p (sphereChartTransition p q z) = z := by
  change (spherePoleChart q).symm
    (spherePoleChart p (sphereChartTransition p q z)) = z
  calc
    _ = (spherePoleChart q).symm (spherePoleChart q z) :=
      congrArg (spherePoleChart q).symm (spherePoleChart_transition hz)
    _ = z := (spherePoleChart q).left_inv (by simp)

/-- The transition map sends the complement of a pulled-back sphere obstacle
to the complement of the same obstacle in the other chart. -/
theorem sphereChartTransition_mapsTo_compl
    {A : Set (OnePoint ℂ)} {p q : OnePoint ℂ} (hp : p ∈ A) :
    MapsTo (sphereChartTransition p q)
      (((spherePoleChart q) ⁻¹' A)ᶜ) (((spherePoleChart p) ⁻¹' A)ᶜ) := by
  intro z hz
  have hzp : spherePoleChart q z ≠ p := by
    intro he
    exact hz (by simpa only [mem_preimage, he] using hp)
  intro hw
  apply hz
  change spherePoleChart q z ∈ A
  rw [← spherePoleChart_transition hzp]
  exact hw

theorem sphereChartTransition_differentiableOn_compl
    {A : Set (OnePoint ℂ)} {p q : OnePoint ℂ} (hp : p ∈ A) :
    DifferentiableOn ℂ (sphereChartTransition p q)
      (((spherePoleChart q) ⁻¹' A)ᶜ) := by
  intro z hz
  exact (sphereChartTransition_differentiableAt (by
    intro he
    exact hz (by simpa only [mem_preimage, he] using hp))).differentiableWithinAt

theorem sphereChartTransition_leftInverse_on_compl
    {A : Set (OnePoint ℂ)} {p q : OnePoint ℂ} (hp : p ∈ A) :
    ∀ z ∈ ((spherePoleChart q) ⁻¹' A)ᶜ,
      sphereChartTransition q p (sphereChartTransition p q z) = z := by
  intro z hz
  apply sphereChartTransition_inverse
  intro he
  exact hz (by simpa only [mem_preimage, he] using hp)

/-- The planar representatives of the same spherical hyperbolic metric in
two pole charts satisfy the conformal density transformation law. -/
theorem sphere_chart_density_transform
    {A : Set (OnePoint ℂ)} (hA : IsClosed A)
    {p q : OnePoint ℂ} (hp : p ∈ A) (hq : q ∈ A)
    {a₁ a₂ b₁ b₂ : ℂ}
    (ha : a₁ ≠ a₂)
    (ha₁ : a₁ ∈ (spherePoleChart q) ⁻¹' A)
    (ha₂ : a₂ ∈ (spherePoleChart q) ⁻¹' A)
    (hb : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ (spherePoleChart p) ⁻¹' A)
    (hb₂ : b₂ ∈ (spherePoleChart p) ⁻¹' A)
    {z : ℂ} (hz : z ∉ (spherePoleChart q) ⁻¹' A) :
    closedComplementDensity ((spherePoleChart p) ⁻¹' A)
        (closed_sphere_set_in_pole_chart hA p) hb hb₁ hb₂
        (sphereChartTransition p q z) * ‖deriv (sphereChartTransition p q) z‖ =
      closedComplementDensity ((spherePoleChart q) ⁻¹' A)
        (closed_sphere_set_in_pole_chart hA q) ha ha₁ ha₂ z := by
  exact closedComplementDensity_conformal_equiv
    (closed_sphere_set_in_pole_chart hA q)
    (closed_sphere_set_in_pole_chart hA p)
    ha ha₁ ha₂ hb hb₁ hb₂
    (sphereChartTransition_differentiableOn_compl hp)
    (sphereChartTransition_differentiableOn_compl hq)
    (sphereChartTransition_mapsTo_compl hp)
    (sphereChartTransition_mapsTo_compl hq)
    (sphereChartTransition_leftInverse_on_compl hp) hz

/-- Hyperbolic area in curvature −1 normalisation is unchanged under a
transition between two pole charts. -/
theorem sphere_chart_hyperbolic_area_image
    {A : Set (OnePoint ℂ)} (hA : IsClosed A)
    {p q : OnePoint ℂ} (hp : p ∈ A) (hq : q ∈ A)
    {a₁ a₂ b₁ b₂ : ℂ}
    (ha : a₁ ≠ a₂)
    (ha₁ : a₁ ∈ (spherePoleChart q) ⁻¹' A)
    (ha₂ : a₂ ∈ (spherePoleChart q) ⁻¹' A)
    (hb : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ (spherePoleChart p) ⁻¹' A)
    (hb₂ : b₂ ∈ (spherePoleChart p) ⁻¹' A)
    {W : Set ℂ} (hW : MeasurableSet W)
    (hWA : W ⊆ ((spherePoleChart q) ⁻¹' A)ᶜ) :
    (∫⁻ w in sphereChartTransition p q '' W,
      hyperbolicAreaWeight ((spherePoleChart p) ⁻¹' A)
        (closed_sphere_set_in_pole_chart hA p) hb hb₁ hb₂ w) =
    ∫⁻ z in W,
      hyperbolicAreaWeight ((spherePoleChart q) ⁻¹' A)
        (closed_sphere_set_in_pole_chart hA q) ha ha₁ ha₂ z := by
  have hdiff : ∀ z ∈ W, HasDerivAt (sphereChartTransition p q)
      (deriv (sphereChartTransition p q) z) z := by
    intro z hz
    exact (sphereChartTransition_differentiableAt (by
      intro he
      exact (hWA hz) (by simpa only [mem_preimage, he] using hp))).hasDerivAt
  have hinj : InjOn (sphereChartTransition p q) W := by
    intro x hx y hy he
    have hleft := sphereChartTransition_leftInverse_on_compl (q := q) hp
    rw [← hleft x (hWA hx), ← hleft y (hWA hy), he]
  rw [holomorphic_change_of_variables hW hdiff hinj]
  apply setLIntegral_congr_fun hW
  intro z hz
  have hρ := sphere_chart_density_transform hA hp hq ha ha₁ ha₂ hb hb₁ hb₂
    (show z ∉ (spherePoleChart q) ⁻¹' A from hWA hz)
  simp only [hyperbolicAreaWeight]
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow,
    mul_comm ‖deriv (sphereChartTransition p q) z‖, hρ]

/-- The gain of curvature −1 area between two nested sphere domains is also
invariant under a change of pole chart. -/
theorem sphere_chart_hyperbolic_gain_image
    {A B : Set (OnePoint ℂ)} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ⊆ B) {p q : OnePoint ℂ} (hp : p ∈ A) (hq : q ∈ A)
    {a₁ a₂ b₁ b₂ : ℂ}
    (ha : a₁ ≠ a₂)
    (ha₁ : a₁ ∈ (spherePoleChart q) ⁻¹' A)
    (ha₂ : a₂ ∈ (spherePoleChart q) ⁻¹' A)
    (hb : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ (spherePoleChart p) ⁻¹' A)
    (hb₂ : b₂ ∈ (spherePoleChart p) ⁻¹' A)
    {W : Set ℂ} (hW : MeasurableSet W)
    (hWB : W ⊆ ((spherePoleChart q) ⁻¹' B)ᶜ) :
    (∫⁻ w in sphereChartTransition p q '' W,
      hyperbolicAreaWeight ((spherePoleChart p) ⁻¹' B)
          (closed_sphere_set_in_pole_chart hB p) hb
          (show b₁ ∈ (spherePoleChart p) ⁻¹' B from hAB hb₁)
          (show b₂ ∈ (spherePoleChart p) ⁻¹' B from hAB hb₂) w -
        hyperbolicAreaWeight ((spherePoleChart p) ⁻¹' A)
          (closed_sphere_set_in_pole_chart hA p) hb hb₁ hb₂ w) =
    ∫⁻ z in W,
      hyperbolicAreaWeight ((spherePoleChart q) ⁻¹' B)
          (closed_sphere_set_in_pole_chart hB q) ha
          (show a₁ ∈ (spherePoleChart q) ⁻¹' B from hAB ha₁)
          (show a₂ ∈ (spherePoleChart q) ⁻¹' B from hAB ha₂) z -
        hyperbolicAreaWeight ((spherePoleChart q) ⁻¹' A)
          (closed_sphere_set_in_pole_chart hA q) ha ha₁ ha₂ z := by
  have hdiff : ∀ z ∈ W, HasDerivAt (sphereChartTransition p q)
      (deriv (sphereChartTransition p q) z) z := by
    intro z hz
    exact (sphereChartTransition_differentiableAt (by
      intro he
      exact (hWB hz) (by simpa only [mem_preimage, he] using hAB hp))).hasDerivAt
  have hinj : InjOn (sphereChartTransition p q) W := by
    intro x hx y hy he
    have hleft := sphereChartTransition_leftInverse_on_compl (q := q) hp
    rw [← hleft x (fun hxA => hWB hx (preimage_mono hAB hxA)),
      ← hleft y (fun hyA => hWB hy (preimage_mono hAB hyA)), he]
  rw [holomorphic_change_of_variables hW hdiff hinj]
  apply setLIntegral_congr_fun hW
  intro z hz
  have hzA : z ∉ (spherePoleChart q) ⁻¹' A :=
    fun hzA => hWB hz (preimage_mono hAB hzA)
  have hzB : z ∉ (spherePoleChart q) ⁻¹' B := hWB hz
  have hρA := sphere_chart_density_transform hA hp hq
    ha ha₁ ha₂ hb hb₁ hb₂ hzA
  have hρB := sphere_chart_density_transform hB (hAB hp) (hAB hq)
    ha (hAB ha₁) (hAB ha₂) hb (hAB hb₁) (hAB hb₂) hzB
  dsimp only
  rw [ENNReal.mul_sub (fun _ _ => ENNReal.ofReal_ne_top)]
  congr 1
  · simp only [hyperbolicAreaWeight]
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow,
      mul_comm ‖deriv (sphereChartTransition p q) z‖, hρB]
  · simp only [hyperbolicAreaWeight]
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow,
      mul_comm ‖deriv (sphereChartTransition p q) z‖, hρA]

end AreaDeficit
