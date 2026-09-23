import FunctionTheory.Conformal.RightEndSymmetry
import Mathlib.Topology.Order.IntermediateValue

open Set Metric Complex Function Filter
open scoped Topology ComplexConjugate

namespace FunctionTheory

/-- The finite endpoint of a symmetric halfstrip corresponds to `-1` when
the interior point maps to zero and the right end corresponds to `1`. -/
theorem rightEndRiemannMap_halfstrip_left_limit
    {f : ℂ → ℂ} {a : ℝ}
    (hf : IsRightEndRiemannMapOn f {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2}
      ((a + 1 : ℝ) : ℂ)) :
    Tendsto (fun t : ℝ => f ((a + t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (-1)) := by
  let V := {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2}
  let W := {z : ℂ | 0 < z.re ∧ |z.im| < Real.pi / 2}
  have hH : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hVo : IsOpen V := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im.abs continuous_const)
  have hWo : IsOpen W := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im.abs continuous_const)
  have hVS : V ⊆ standardHorizontalStrip := fun _ hz => hz.2
  have htail : ∀ z ∈ standardHorizontalStrip, a < z.re → z ∈ V := fun _ hz hr => ⟨hr, hz⟩
  have hconj : MapsTo conj V V := by
    intro z hz
    simpa only [V, mem_setOf_eq, conj_re, conj_im, abs_neg] using hz
  have hsym := hf.conj_eq hVo hVS htail hconj
  have hreal {x : ℝ} (hx : a < x) : (f (x : ℂ)).im = 0 := by
    apply conj_eq_iff_im.mp
    have h := hsym (x : ℂ) ⟨hx, by simpa using hH⟩
    rw [conj_ofReal] at h
    exact h.symm
  let p : ℝ → ℝ := fun t => (f ((a + Real.exp t : ℝ) : ℂ)).re
  have hpV t : ((a + Real.exp t : ℝ) : ℂ) ∈ V := by
    constructor
    · change a < a + Real.exp t
      linarith [Real.exp_pos t]
    · change |(0 : ℝ)| < Real.pi / 2
      simpa using hH
  have hpc : Continuous p := continuous_re.comp
    (hf.differentiableOn.continuousOn.comp_continuous
      (continuous_ofReal.comp (continuous_const.add Real.continuous_exp)) hpV)
  have hpi : Injective p := by
    intro t u he
    have hfe : f ((a + Real.exp t : ℝ) : ℂ) = f ((a + Real.exp u : ℝ) : ℂ) := by
      apply Complex.ext he
      rw [hreal (lt_add_of_pos_right a (Real.exp_pos t)),
        hreal (lt_add_of_pos_right a (Real.exp_pos u))]
    have h := congrArg Complex.re (hf.bijOn.injOn (hpV t) (hpV u) hfe)
    simp only [ofReal_re, add_left_cancel_iff] at h
    exact Real.exp_injective h
  have hp0 : p 0 = 0 := by simp only [p, Real.exp_zero, hf.map_base, zero_re]
  have hptop : Tendsto p atTop (𝓝 1) := by
    have h := (continuous_re.tendsto (1 : ℂ)).comp
      ((hf.tendsto_real_atTop htail).comp
        (tendsto_atTop_add_const_left atTop a Real.tendsto_exp_atTop))
    simpa only [Function.comp_def, one_re] using h
  have hpm : StrictMono p := by
    rcases hpc.strictMono_of_inj hpi with hm | ha
    · exact hm
    · have he : ∀ᶠ t : ℝ in atTop, p t ≤ 0 := by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        simpa only [hp0] using ha.antitone ht
      have h := le_of_tendsto hptop he
      norm_num at h
  have hshift : BijOn (fun z : ℂ => (a : ℂ) + z) W V := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact ⟨by simp only [add_re, ofReal_re]; linarith [hz.1],
        by simpa only [add_im, ofReal_im, zero_add] using hz.2⟩
    · intro z hz w hw he; exact add_left_cancel he
    · intro z hz
      refine ⟨z - (a : ℂ), ⟨?_, ?_⟩, by ring⟩
      · simpa only [sub_re, ofReal_re] using sub_pos.mpr hz.1
      · simpa only [sub_im, ofReal_im, sub_zero] using hz.2
  have hJd := hf.differentiableOn.comp
    ((differentiable_const (a : ℂ)).add differentiable_id).differentiableOn hshift.mapsTo
  have hnear : ∀ z ∈ ball (0 : ℂ) (Real.pi / 2), z ∈ W ↔ 0 < z.re := by
    intro z hz
    exact ⟨fun h => h.1, fun h => ⟨h,
      (abs_im_le_norm z).trans_lt (by simpa only [mem_ball, dist_zero_right] using hz)⟩⟩
  obtain ⟨ξ, ψ, c, hξ, hlim, _⟩ :=
    exists_positive_cayley_coordinate_of_disk_map_at_straight_boundary
      hWo hJd (hf.bijOn.comp hshift) hH hnear
  have hrealW : MapsTo (fun t : ℝ => (t : ℂ)) (Ioi 0) W :=
    fun t ht => ⟨ht, by simpa using hH⟩
  have htW : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝[W] 0) := by
    simpa using (continuous_ofReal.continuousWithinAt (x := (0 : ℝ))).tendsto_nhdsWithin hrealW
  have hlim' : Tendsto (fun t : ℝ => f ((a + t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ξ) := by
    simpa only [Function.comp_def, ofReal_add, Pi.add_apply, id_eq] using hlim.comp htW
  have hξim : ξ.im = 0 := by
    have he : (fun t : ℝ => (f ((a + t : ℝ) : ℂ)).im) =ᶠ[𝓝[>] 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hreal (lt_add_of_pos_right a ht)
    exact tendsto_nhds_unique ((continuous_im.tendsto ξ).comp hlim')
      (tendsto_const_nhds.congr' he.symm)
  have hξre : ξ.re ≤ 0 := by
    apply le_of_tendsto ((continuous_re.tendsto ξ).comp hlim')
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht ht1
    have h := hpm (Real.log_neg ht ht1)
    simpa only [p, Real.exp_log ht, hp0, Function.comp_apply] using h.le
  have hξeq : ξ = -1 := by
    have hre : (ξ.re : ℂ) = ξ := conj_eq_iff_re.mp (conj_eq_iff_im.mpr hξim)
    have hn : |ξ.re| = 1 := by
      have hh := hξ
      rw [← hre, norm_real, Real.norm_eq_abs] at hh
      exact hh
    rw [abs_of_nonpos hξre] at hn
    apply Complex.ext
    · simp only [neg_re, one_re]; linarith
    · simp only [neg_im, one_im, neg_zero, hξim]
  simpa only [hξeq] using hlim'

end FunctionTheory
