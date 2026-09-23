import FunctionTheory.Conformal.SlitTipUnwrapped
import FunctionTheory.Conformal.HalfDiskCircleReflection

open Set Metric Complex Filter Function
open scoped Topology ComplexConjugate

namespace FunctionTheory

/-- At a free straight-slit tip, the inverse disk map extends holomorphically
across its corresponding circle point. The extension has value the tip.
No global Jordan-boundary or prime-end hypothesis is required. -/
theorem exists_analytic_inverse_extension_at_slit_tip
    {U : Set ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R) (hlocal : U ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ (ξ : ℂ) (η : ℝ) (Ψ : ℂ → ℂ), ξ ∈ sphere (0 : ℂ) 1 ∧ 0 < η ∧
      AnalyticAt ℂ Ψ ξ ∧ Ψ ξ = 0 ∧
      EqOn Ψ (invFunOn f U) (ball ξ η ∩ ball 0 1) := by
  let ρ := Real.sqrt R / 2
  have hρ : 0 < ρ := half_pos (Real.sqrt_pos.mpr hR)
  have hρR : ρ ^ 2 < R := by
    dsimp [ρ]
    nlinarith [Real.sq_sqrt hR.le]
  obtain ⟨H, hHc, hHd, hHi, hHf, hHD, hHa⟩ :=
    exists_continuous_extension_on_unwrapped_slit hU hf hbij hR hρ hρR hlocal
  obtain ⟨δ, F, hδ, hδρ, hFd, hFi, hF0, hFH, hFs, hFpos⟩ :=
    exists_reflection_of_half_disk_map_to_circle hρ hHc hHd hHi hHD hHa
  let ξ := H 0
  have hξs : ξ ∈ sphere (0 : ℂ) 1 := hHa 0 (mem_ball_self hρ) rfl
  have hξ : ‖ξ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hξs
  have hξ0 : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ]; norm_num)
  let ψ := invFunOn F (ball 0 δ)
  have hIo : IsOpen (F '' ball 0 δ) :=
    TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hFd hFi
  have h0I : (0 : ℂ) ∈ F '' ball 0 δ := ⟨0, mem_ball_self hδ, hF0⟩
  have hψa : AnalyticAt ℂ ψ 0 :=
    (DifferentiableOn.invFunOn hFd isOpen_ball hFi).analyticAt (hIo.mem_nhds h0I)
  have hψ0 : ψ 0 = 0 := by
    simpa only [hF0] using hFi.leftInvOn_invFunOn (mem_ball_self hδ)
  let q : ℂ → ℂ := fun w => cayleyCoordinate (w / ξ)
  have hq0 : q ξ = 0 := by simp [q, div_self hξ0]
  have hqa : AnalyticAt ℂ q ξ := by
    have hd : 1 + ξ / ξ ≠ 0 := by simp [div_self hξ0]
    exact (analyticAt_const.sub analyticAt_id.div_const).div
      (analyticAt_const.add analyticAt_id.div_const) hd
  have hqψa : AnalyticAt ℂ ψ (q ξ) := by rwa [hq0]
  let Ψ : ℂ → ℂ := fun w => (ψ (q w)) ^ 2
  have hΨa : AnalyticAt ℂ Ψ ξ := (hqψa.comp hqa).pow 2
  have hΨ0 : Ψ ξ = 0 := by simp [Ψ, hq0, hψ0]
  have hqnear : q ⁻¹' (F '' ball 0 δ) ∈ 𝓝 ξ :=
    hqa.continuousAt.preimage_mem_nhds (by simpa only [hq0] using hIo.mem_nhds h0I)
  obtain ⟨η, hη, hηI⟩ := Metric.mem_nhds_iff.mp hqnear
  refine ⟨ξ, η, Ψ, hξs, hη, hΨa, hΨ0, ?_⟩
  intro w hw
  obtain ⟨u, hu, huq⟩ := hηI hw.1
  have hψqu : ψ (q w) = u := by
    rw [← huq]
    exact hFi.leftInvOn_invFunOn hu
  have hwξ : w / ξ ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_div, hξ, div_one] using hw.2
  have hqpos : 0 < (q w).re := re_cayleyCoordinate_pos_of_mem_ball hwξ
  have hupos : 0 < u.re := by
    by_contra h
    rcases lt_or_eq_of_le (le_of_not_gt h) with hneg | hzero
    · have hu' : -conj u ∈ ball (0 : ℂ) δ := by
        simpa only [mem_ball, dist_zero_right, norm_neg, norm_conj] using hu
      have hp := hFpos _ hu' (show 0 < (-conj u).re by simpa using neg_pos.mpr hneg)
      rw [hFs u hu, huq] at hp
      simp only [neg_re, conj_re] at hp
      linarith
    · have he : -conj u = u := by apply Complex.ext <;> simp [hzero]
      have hh := congrArg Complex.re (hFs u hu)
      rw [he, huq] at hh
      simp only [neg_re, conj_re] at hh
      linarith
  have hur : u ∈ ball (0 : ℂ) ρ := ball_subset_ball hδρ hu
  have hHξ : H u / ξ ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_div, hξ, div_one] using hHD ⟨hur, hupos⟩
  have hHuw : H u = w := by
    have heq : cayleyCoordinate (H u / ξ) = cayleyCoordinate (w / ξ) :=
      (hFH ⟨hu, hupos.le⟩).symm.trans huq
    exact (div_left_inj' hξ0).mp (cayleyCoordinate_injOn
      (cayley_denominator_ne_zero_of_mem_ball hHξ)
      (cayley_denominator_ne_zero_of_mem_ball hwξ) heq)
  have hu2ball : u ^ 2 ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, norm_pow]
    have hu' := mem_ball_zero_iff.mp hur
    nlinarith [norm_nonneg u]
  have hu2U : u ^ 2 ∈ U := by
    have he := congrArg (fun S : Set ℂ => u ^ 2 ∈ S) hlocal
    have hm : u ^ 2 ∈ U ↔ u ^ 2 ∈ slitPlane := by
      simpa only [mem_inter_iff, hu2ball, and_true] using iff_of_eq he
    exact hm.mpr (sq_mem_slitPlane_of_re_pos hupos)
  have hfu : f (u ^ 2) = w := (hHf ⟨hur, hupos⟩).symm.trans hHuw
  have hgi : invFunOn f U w = u ^ 2 := by
    rw [← hfu]
    exact hbij.injOn.leftInvOn_invFunOn hu2U
  change (ψ (q w)) ^ 2 = invFunOn f U w
  rw [hψqu, hgi]

/-- The inverse disk map has a unique limit at the circle point corresponding
to a free slit tip, along the entire disk rather than only a radial approach. -/
theorem exists_inverse_boundary_limit_at_slit_tip
    {U : Set ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R) (hlocal : U ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ ξ ∈ sphere (0 : ℂ) 1,
      Tendsto (invFunOn f U) (𝓝[ball 0 1] ξ) (𝓝 0) := by
  obtain ⟨ξ, η, Ψ, hξ, hη, hΨ, hΨ0, heq⟩ :=
    exists_analytic_inverse_extension_at_slit_tip hU hf hbij hR hlocal
  refine ⟨ξ, hξ, ?_⟩
  have he : invFunOn f U =ᶠ[𝓝[ball 0 1] ξ] Ψ := by
    have hball : ∀ᶠ w in 𝓝[ball (0 : ℂ) 1] ξ, w ∈ ball ξ η :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hη))
    filter_upwards [self_mem_nhdsWithin, hball] with w hw hwη
    exact (heq ⟨hwη, hw⟩).symm
  rw [tendsto_congr' he]
  simpa only [hΨ0] using hΨ.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) 1] ξ ≤ 𝓝 ξ)

end FunctionTheory
