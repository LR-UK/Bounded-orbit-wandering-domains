import FunctionTheory.Conformal.StraightBoundaryExtension

/-! # The direct coordinate at a straight boundary

The reflected disk parametrization has a holomorphic inverse near zero.
That inverse agrees, on the right half, with the Cayley coordinate of the
inverse Riemann map. This supplies the direct analytic coordinate needed
when logarithms turn a boundary point into the end of a strip.
-/

open Set Metric Complex Function Filter
open scoped ComplexConjugate Topology

namespace FunctionTheory

theorem exists_analytic_cayley_inverse_at_zero
    {Ω : Set ℂ} {G : ℂ → ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hr : 0 < r)
    (hnear : ∀ w ∈ ball (0 : ℂ) r, w ∈ Ω ↔ 0 < w.re)
    (hGc : ContinuousOn G (closedBall 0 1))
    (hGd : DifferentiableOn ℂ G (ball 0 1)) (hGbij : BijOn G (ball 0 1) Ω)
    (hG1 : G 1 = 0) :
    ∃ (ψ : ℂ → ℂ) (η a : ℝ), 0 < η ∧ AnalyticAt ℂ ψ 0 ∧
      ψ 0 = 0 ∧ 0 < a ∧ deriv ψ 0 = (a : ℂ) ∧
      EqOn ψ (fun w => cayleyCoordinate (invFunOn G (ball 0 1) w))
        (ball 0 η ∩ {w : ℂ | 0 < w.re}) := by
  obtain ⟨δ, F, a, hδ, hFd, hFi, hFG, hF0, ha, hFa, hFs, hFpos⟩ :=
    exists_positive_reflection_of_disc_map_at_one hΩ hr hnear hGc hGd hGbij hG1
  let ψ := invFunOn F (ball 0 δ)
  have hIo : IsOpen (F '' ball 0 δ) :=
    TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hFd hFi
  have h0I : (0 : ℂ) ∈ F '' ball 0 δ := ⟨0, mem_ball_self hδ, hF0⟩
  have hψa : AnalyticAt ℂ ψ 0 :=
    (DifferentiableOn.invFunOn hFd isOpen_ball hFi).analyticAt (hIo.mem_nhds h0I)
  have hψ0 : ψ 0 = 0 := by
    simpa only [hF0] using hFi.leftInvOn_invFunOn (mem_ball_self hδ)
  have hψd : deriv ψ 0 = ((a⁻¹ : ℝ) : ℂ) := by
    have h := (TauCeti.hasDerivAt_invFunOn hFd isOpen_ball hFi (mem_ball_self hδ)).deriv
    simpa only [hF0, hFa, Complex.ofReal_inv] using h
  obtain ⟨η, hη, hηI⟩ := Metric.isOpen_iff.mp hIo 0 h0I
  refine ⟨ψ, η, a⁻¹, hη, hψa, hψ0, inv_pos.mpr ha, hψd, ?_⟩
  intro w hw
  obtain ⟨u, hu, huw⟩ := hηI hw.1
  have hψw : ψ w = u := by
    rw [← huw]
    exact hFi.leftInvOn_invFunOn hu
  have hupos : 0 < u.re := by
    by_contra h
    have hunonpos : u.re ≤ 0 := le_of_not_gt h
    rcases lt_or_eq_of_le hunonpos with hneg | hzero
    · have hu' : -conj u ∈ ball (0 : ℂ) δ := by
        simpa only [mem_ball, dist_zero_right, norm_neg, norm_conj] using hu
      have hp := hFpos ⟨hu', show 0 < (-conj u).re by simpa using neg_pos.mpr hneg⟩
      change 0 < (F (-conj u)).re at hp
      rw [hFs u hu, huw] at hp
      simp only [neg_re, conj_re] at hp
      have hwpos : 0 < w.re := hw.2
      linarith
    · have he : -conj u = u := by apply Complex.ext <;> simp [hzero]
      have hh := congrArg Complex.re (hFs u hu)
      rw [he, huw] at hh
      simp only [neg_re, conj_re] at hh
      have hwpos : 0 < w.re := hw.2
      linarith
  have hFu : F u = G (cayleyCoordinate u) := hFG ⟨hu, hupos.le⟩
  have hGi : invFunOn G (ball 0 1) w = cayleyCoordinate u := by
    have h := hGbij.injOn.leftInvOn_invFunOn (cayleyCoordinate_mem_ball hupos)
    rwa [← hFu, huw] at h
  change ψ w = cayleyCoordinate (invFunOn G (ball 0 1) w)
  rw [hGi, cayleyCoordinate_involution (cayley_denominator_ne_zero hupos.le), hψw]

/-- Extend the direct coordinate off its mathematical domain so it is analytic
at the boundary point, while retaining its values on the entire Jordan domain.
The extension is an internal representative for subsequent calculus. -/
theorem exists_analytic_extension_of_cayley_inverse
    {Ω : Set ℂ} {G : ℂ → ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hr : 0 < r)
    (hnear : ∀ w ∈ ball (0 : ℂ) r, w ∈ Ω ↔ 0 < w.re)
    (hGc : ContinuousOn G (closedBall 0 1))
    (hGd : DifferentiableOn ℂ G (ball 0 1)) (hGbij : BijOn G (ball 0 1) Ω)
    (hG1 : G 1 = 0) :
    ∃ (ψ : ℂ → ℂ) (a : ℝ), AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      0 < a ∧ deriv ψ 0 = (a : ℂ) ∧
      EqOn ψ (fun w => cayleyCoordinate (invFunOn G (ball 0 1) w)) Ω := by
  classical
  obtain ⟨ψ₀, η, a, hη, hψ₀, hψ₀0, ha, hψ₀d, heq⟩ :=
    exists_analytic_cayley_inverse_at_zero hΩ hr hnear hGc hGd hGbij hG1
  let V : Set ℂ := ball 0 (min η r)
  let q : ℂ → ℂ := fun w => cayleyCoordinate (invFunOn G (ball 0 1) w)
  let ψ : ℂ → ℂ := V.piecewise ψ₀ q
  have h0V : (0 : ℂ) ∈ V := mem_ball_self (lt_min hη hr)
  have hlocal : ψ =ᶠ[𝓝 (0 : ℂ)] ψ₀ := by
    filter_upwards [isOpen_ball.mem_nhds h0V] with w hw
    exact piecewise_eq_of_mem V ψ₀ q hw
  refine ⟨ψ, a, hψ₀.congr hlocal.symm, (hlocal.eq_of_nhds).trans hψ₀0, ha,
    hlocal.deriv_eq.trans hψ₀d, ?_⟩
  intro w hwΩ
  change V.piecewise ψ₀ q w = q w
  by_cases hw : w ∈ V
  · rw [piecewise_eq_of_mem V ψ₀ q hw]
    exact heq ⟨ball_subset_ball (min_le_left _ _) hw,
      (hnear w (ball_subset_ball (min_le_right _ _) hw)).mp hwΩ⟩
  · exact piecewise_eq_of_notMem V ψ₀ q hw

end FunctionTheory
