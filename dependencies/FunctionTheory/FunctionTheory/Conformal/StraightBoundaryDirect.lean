import FunctionTheory.Conformal.StraightBoundaryContinuous
import FunctionTheory.Conformal.HalfDiskCircleReflection
import FunctionTheory.Conformal.RiemannMapping

open Set Metric Complex Function Filter
open scoped Topology ComplexConjugate

namespace FunctionTheory

/-- A given disk map at a locally straight boundary has a unit-circle
limit. After rotation by that limit, its Cayley coordinate extends
holomorphically with positive real derivative. -/
theorem exists_positive_cayley_coordinate_of_disk_map_at_straight_boundary
    {U : Set ℂ} {f : ℂ → ℂ} {r : ℝ}
    (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hr : 0 < r) (hnear : ∀ z ∈ ball (0 : ℂ) r, z ∈ U ↔ 0 < z.re) :
    ∃ (ξ : ℂ) (ψ : ℂ → ℂ) (a : ℝ), ‖ξ‖ = 1 ∧
      Tendsto f (𝓝[U] 0) (𝓝 ξ) ∧ AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      0 < a ∧ deriv ψ 0 = (a : ℂ) ∧
      EqOn ψ (fun z => cayleyCoordinate (f z / ξ)) U := by
  classical
  obtain ⟨H, hHc, hHf, hHa⟩ := exists_continuous_extension_at_straight_side
    hUo hf hbij hr
    (fun z hz hp => (hnear z hz).mpr hp)
    (fun z hz he hu => by have hp := (hnear z hz).mp hu; rw [he] at hp; exact lt_irrefl _ hp)
  have hhalf : ball (0 : ℂ) (r / 2) ∩ {z : ℂ | 0 < z.re} ⊆ U := by
    intro z hz
    exact (hnear z (ball_subset_ball (half_le_self hr.le) hz.1)).mpr hz.2
  have hHd : DifferentiableOn ℂ H (ball 0 (r / 2) ∩ {z : ℂ | 0 < z.re}) :=
    (hf.mono hhalf).congr hHf
  have hHi : InjOn H (ball 0 (r / 2) ∩ {z : ℂ | 0 < z.re}) := by
    intro z hz w hw he
    apply hbij.injOn (hhalf hz) (hhalf hw)
    rwa [hHf hz, hHf hw] at he
  have hHD : MapsTo H (ball 0 (r / 2) ∩ {z : ℂ | 0 < z.re}) (ball 0 1) := by
    intro z hz
    rw [hHf hz]
    exact hbij.mapsTo (hhalf hz)
  obtain ⟨δ, F, hδ, hδr, hFd, hFi, hF0, hFH, hFs, hFpos⟩ :=
    exists_reflection_of_half_disk_map_to_circle (half_pos hr) hHc hHd hHi hHD hHa
  have hFaxis : ∀ z ∈ ball (0 : ℂ) δ, z.re = 0 → (F z).re = 0 := by
    intro z hz hre
    have he : -conj z = z := by apply Complex.ext <;> simp [hre]
    have h := congrArg Complex.re (hFs z hz)
    rw [he] at h
    simp only [neg_re, conj_re] at h
    linarith
  obtain ⟨a, ha, hFa⟩ := deriv_positive_real_of_halfplane_map
    (isOpen_ball.mem_nhds (mem_ball_self hδ))
    (hFd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))) hF0
    (TauCeti.deriv_ne_zero_of_injOn hFd isOpen_ball hFi (mem_ball_self hδ)) hFaxis hFpos
  let ξ := H 0
  have hξ : ‖ξ‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using hHa 0 (mem_ball_self (half_pos hr)) rfl
  have hξ0 : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ]; norm_num)
  have hsmall : ∀ᶠ z in 𝓝[U] (0 : ℂ), z ∈ ball (0 : ℂ) (r / 2) :=
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))
  have hpos : ∀ᶠ z in 𝓝[U] (0 : ℂ), 0 < z.re := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hzb
    exact (hnear z (ball_subset_ball (half_le_self hr.le) hzb)).mp hz
  have hle : 𝓝[U] (0 : ℂ) ≤ 𝓝[ball 0 (r / 2) ∩ {z : ℂ | 0 ≤ z.re}] 0 := by
    apply le_inf nhdsWithin_le_nhds
    apply le_principal_iff.mpr
    filter_upwards [hsmall, hpos] with z hz hp
    exact ⟨hz, hp.le⟩
  have hlimH : Tendsto H (𝓝[U] (0 : ℂ)) (𝓝 ξ) :=
    (hHc 0 ⟨mem_ball_self (half_pos hr), by simp⟩).mono_left hle
  have hevent : H =ᶠ[𝓝[U] (0 : ℂ)] f := by
    filter_upwards [hsmall, hpos] with z hz hp
    exact hHf ⟨hz, hp⟩
  have hlim : Tendsto f (𝓝[U] (0 : ℂ)) (𝓝 ξ) := hlimH.congr' hevent
  let g : ℂ → ℂ := fun z => f z / ξ
  let V : Set ℂ := ball 0 δ
  let q : ℂ → ℂ := fun z => cayleyCoordinate (g z)
  let ψ : ℂ → ℂ := V.piecewise F q
  have hlocal : ψ =ᶠ[𝓝 (0 : ℂ)] F := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with z hz
    exact piecewise_eq_of_mem V F q hz
  have hFa0 : AnalyticAt ℂ F 0 := hFd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hδ))
  refine ⟨ξ, ψ, a, hξ, hlim, hFa0.congr hlocal.symm,
    hlocal.eq_of_nhds.trans hF0, ha, hlocal.deriv_eq.trans hFa, ?_⟩
  intro z hzU
  change V.piecewise F q z = q z
  by_cases hzV : z ∈ V
  · rw [piecewise_eq_of_mem V F q hzV]
    have hzr : z ∈ ball (0 : ℂ) (r / 2) := ball_subset_ball hδr hzV
    have hzpos : 0 < z.re := (hnear z (ball_subset_ball (half_le_self hr.le) hzr)).mp hzU
    rw [hFH ⟨hzV, hzpos.le⟩]
    change cayleyCoordinate (H z / ξ) = cayleyCoordinate (f z / ξ)
    rw [hHf ⟨hzr, hzpos⟩]
  · exact piecewise_eq_of_notMem V F q hzV

/-- A Riemann map can be normalized at an interior point and a locally
straight boundary point without any regularity of the remaining boundary.
Its Cayley coordinate has a holomorphic extension with positive real
derivative at that boundary point. -/
theorem exists_disk_map_with_positive_cayley_coordinate_at_straight_boundary
    {U : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hz₀ : z₀ ∈ U) (hr : 0 < r)
    (hnear : ∀ z ∈ ball (0 : ℂ) r, z ∈ U ↔ 0 < z.re) :
    ∃ (g ψ : ℂ → ℂ) (a : ℝ), DifferentiableOn ℂ g U ∧
      BijOn g U (ball 0 1) ∧ g z₀ = 0 ∧ AnalyticAt ℂ ψ 0 ∧
      ψ 0 = 0 ∧ 0 < a ∧ deriv ψ 0 = (a : ℂ) ∧
      EqOn ψ (fun z => cayleyCoordinate (g z)) U := by
  have h0U : (0 : ℂ) ∉ U := fun h => by
    simpa using (hnear 0 (mem_ball_self hr)).mp h
  have hUproper : U ≠ univ := fun he => h0U (he ▸ mem_univ 0)
  obtain ⟨f, hf, _⟩ := TauCeti.riemannMapping_normalized hUo hUc hUproper hz₀
  obtain ⟨ξ, ψ, a, hξ, _, hψ, hψ0, ha, hψd, heq⟩ :=
    exists_positive_cayley_coordinate_of_disk_map_at_straight_boundary
      hUo hf.differentiableOn hf.bijOn hr hnear
  have hξ0 : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ]; norm_num)
  have hdiv : BijOn (fun w : ℂ => w / ξ) (ball 0 1) (ball 0 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa only [mem_ball, dist_zero_right, norm_div, hξ, div_one] using hw
    · intro z hz w hw he
      exact (div_left_inj' hξ0).mp he
    · intro w hw
      refine ⟨w * ξ, ?_, mul_div_cancel_right₀ w hξ0⟩
      simpa only [mem_ball, dist_zero_right, norm_mul, hξ, mul_one] using hw
  exact ⟨fun z => f z / ξ, ψ, a, hf.differentiableOn.div_const ξ,
    hdiv.comp hf.bijOn, by simp [hf.map_base], hψ, hψ0, ha, hψd, heq⟩

end FunctionTheory
