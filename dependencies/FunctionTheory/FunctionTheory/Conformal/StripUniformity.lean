import FunctionTheory.Conformal.StripBounds
import Mathlib.Topology.MetricSpace.Thickening

/-! # Uniform neighbourhoods and continuity on closed strip insets

Compact left truncations let us combine compact control with uniform control
on the straight end. No extension of a conformal map to the plane is used.
-/

open Set Metric Filter
open scoped Topology

namespace FunctionTheory

theorem exists_uniform_neighbourhood_of_strip_tail {S U : Set ℂ} {L M R δ : ℝ}
    (hS : IsClosed S) (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hU : IsOpen U) (hSU : S ⊆ U) (hδ : 0 < δ)
    (htail : ∀ z ∈ S, R ≤ z.re → closedBall z δ ⊆ U) :
    ∃ ε > 0, ∀ z ∈ S, closedBall z ε ⊆ U := by
  let K := S ∩ {z : ℂ | z.re ≤ R}
  have hK : IsCompact K := isCompact_left_truncation_of_strip_bounds hS hleft him
  obtain ⟨ε, hε, hthick⟩ := hK.exists_cthickening_subset_open hU
    (inter_subset_left.trans hSU)
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro z hz
  by_cases hr : z.re ≤ R
  · exact (closedBall_subset_closedBall (min_le_left _ _)).trans
      ((closedBall_subset_cthickening (show z ∈ K from ⟨hz, hr⟩) ε).trans hthick)
  · exact (closedBall_subset_closedBall (min_le_right _ _)).trans
      (htail z hz (le_of_not_ge hr))

theorem uniformContinuousOn_of_strip_limit {S : Set ℂ} {q : ℂ → ℂ} {c : ℂ} {L M : ℝ}
    (hS : IsClosed S) (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hq : ContinuousOn q S)
    (hlim : Tendsto q (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 c)) :
    UniformContinuousOn q S := by
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  have hevent : ∀ᶠ z in comap Complex.re atTop ⊓ 𝓟 S, dist (q z) c < ε / 2 :=
    hlim.eventually (Metric.ball_mem_nhds c (half_pos hε))
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp
    (eventually_inf_principal.mp hevent))
  let K := S ∩ {z : ℂ | z.re ≤ R + 1}
  have hK : IsCompact K := isCompact_left_truncation_of_strip_bounds hS hleft him
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (hq.mono inter_subset_left)) ε hε
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro z hz w hw hzw
  have hdδ : dist z w < δ := hzw.trans_le (min_le_left _ _)
  have hd1 : dist z w < 1 := hzw.trans_le (min_le_right _ _)
  have hrew : |z.re - w.re| < 1 := by
    have H := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re, ← dist_eq_norm] at H
    exact H.trans_lt hd1
  by_cases hzR : z.re ≤ R
  · exact hclose z ⟨hz, show z.re ≤ R + 1 by linarith⟩ w
      ⟨hw, show w.re ≤ R + 1 by linarith [(abs_lt.mp hrew).1]⟩ hdδ
  by_cases hwR : w.re ≤ R
  · exact hclose z ⟨hz, show z.re ≤ R + 1 by linarith [(abs_lt.mp hrew).2]⟩ w
      ⟨hw, show w.re ≤ R + 1 by linarith⟩ hdδ
  have hzsmall := hR z.re (le_of_not_ge hzR) z rfl hz
  have hwsmall := hR w.re (le_of_not_ge hwR) w rfl hw
  calc dist (q z) (q w) ≤ dist (q z) c + dist c (q w) := dist_triangle _ _ _
    _ < ε := by rw [dist_comm c]; linarith

theorem uniformContinuousOn_of_strip_translation_limit {S : Set ℂ} {f : ℂ → ℂ}
    {c : ℂ} {L M : ℝ}
    (hS : IsClosed S) (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hf : ContinuousOn f S)
    (hlim : Tendsto (fun z => f z - z) (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 c)) :
    UniformContinuousOn f S := by
  have hq := uniformContinuousOn_of_strip_limit hS hleft him
    (hf.sub continuous_id.continuousOn) hlim
  rw [uniformContinuousOn_iff_restrict] at hq ⊢
  change UniformContinuous (fun z : S => f z - (z : ℂ)) at hq
  change UniformContinuous (fun z : S => f z)
  simpa only [sub_add_cancel] using hq.add uniformContinuous_subtype_val

end FunctionTheory
