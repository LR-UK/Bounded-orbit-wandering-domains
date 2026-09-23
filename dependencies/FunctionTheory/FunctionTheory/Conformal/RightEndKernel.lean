import FunctionTheory.Conformal.RightEndNormalization

open Set Metric Complex Function Filter
open scoped Topology

namespace FunctionTheory

/-- Kernel convergence with the interior point and the right end fixed.
The common straight tail supplies the boundary control needed to remove the
rotation present in derivative-normalized Carathéodory convergence. -/
theorem rightEndRiemannMaps_tendsto_on_kernel
    {U : ℕ → Set ℂ} {V : Set ℂ} {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hUo : ∀ n, IsOpen (U n)) (hUc : ∀ n, IsSimplyConnected (U n))
    (hUS : ∀ n, U n ⊆ standardHorizontalStrip) (hdec : Antitone U)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V) (hVS : V ⊆ standardHorizontalStrip)
    (hVU : ∀ n, V ⊆ U n)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ V)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V)
    (hG : ∀ n, IsRightEndRiemannMapOn (G n) (U n) z₀)
    (hg : IsRightEndRiemannMapOn g V z₀) :
    TendstoLocallyUniformlyOn G g atTop V := by
  have hproper {S : Set ℂ} (hS : S ⊆ standardHorizontalStrip) : S ≠ univ := by
    intro he
    have h := hS (he ▸ mem_univ ((Real.pi : ℂ) * I))
    change |((Real.pi : ℂ) * I).im| < Real.pi / 2 at h
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_pos]
  choose F hF using fun n => TauCeti.exists_isNormalizedRiemannMapOn
    (hUo n) (hUc n) (hproper (hUS n)) (hG n).base_mem
  obtain ⟨f, hf⟩ := TauCeti.exists_isNormalizedRiemannMapOn
    hVo hVc (hproper hVS) hg.base_mem
  have hbound : ∀ z ∈ U 0, -(Real.pi / 2) ≤ z.im :=
    fun z hz => (abs_lt.mp (hUS 0 hz)).1.le
  have hconv := (normalized_riemannMaps_tendsto_on_halfPlane_kernel hUo hdec hbound hF
    hVo hVc.isPathConnected.isConnected.isPreconnected hf hVU hkernel).1
  have hUtail n : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U n :=
    fun z hz hr => hVU n (htail z hz hr)
  choose ξ ρ hξ hlim hest using fun n => exists_strip_end_normalization_of_disk_map
    (hUo n) (hUS n) (hUtail n) (hF n).differentiableOn (hF n).bijOn (hF n).map_base
  obtain ⟨ξ₀, ρ₀, hξ₀, hlim₀, _⟩ := exists_strip_end_normalization_of_disk_map
    hVo hVS htail hf.differentiableOn hf.bijOn hf.map_base
  have hξne n : ξ n ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ n]; norm_num)
  have hξ₀ne : ξ₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [hξ₀]; norm_num)
  have hξconv : Tendsto ξ atTop (𝓝 ξ₀) :=
    boundary_values_tendsto_at_common_strip_end hUo hUS hVo hVS
      (fun n => (hF n).differentiableOn) (fun n => (hF n).bijOn)
      hf.differentiableOn hf.bijOn (fun n => (hF n).base_mem) hf.base_mem
      (fun n => (hF n).map_base) hf.map_base hUtail htail
      (fun n => (hlim n).mono_left (nhdsWithin_mono _ inter_subset_left))
      (hlim₀.mono_left (nhdsWithin_mono _ inter_subset_left)) hconv
  have hrot n : IsRightEndRiemannMapOn (fun z => F n z / ξ n) (U n) z₀ := by
    refine ⟨(hF n).base_mem, (hF n).differentiableOn.div_const _,
      (bijOn_div_unit_disk (hξ n)).comp (hF n).bijOn, by simp [(hF n).map_base], ?_⟩
    simpa only [div_self (hξne n)] using (hlim n).div_const (ξ n)
  have hrot₀ : IsRightEndRiemannMapOn (fun z => f z / ξ₀) V z₀ := by
    refine ⟨hf.base_mem, hf.differentiableOn.div_const _,
      (bijOn_div_unit_disk hξ₀).comp hf.bijOn, by simp [hf.map_base], ?_⟩
    simpa only [div_self hξ₀ne] using hlim₀.div_const ξ₀
  exact ((locallyUniform_div_boundary_values hconv hf.differentiableOn.continuousOn
    hξconv hξ₀ne).congr (fun n =>
      ((hrot n).eqOn (hG n) (hUo n) (hUS n) (hUtail n)).mono (hVU n))).congr_right
        (hrot₀.eqOn hg hVo hVS htail)

end FunctionTheory
