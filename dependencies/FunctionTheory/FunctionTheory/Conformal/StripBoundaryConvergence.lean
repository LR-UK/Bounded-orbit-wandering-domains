import FunctionTheory.Conformal.StraightBoundaryConvergence
import FunctionTheory.Conformal.StripEndMapLocal
import Mathlib.Analysis.Normed.Field.Lemmas

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

theorem bijOn_neg_log_exponentialImage {U : Set ℂ} (hU : U ⊆ standardHorizontalStrip) :
    BijOn (fun w => -log w) (exponentialImage U) U := by
  refine ⟨?_, ?_, ?_⟩
  · rintro w ⟨z, hz, rfl⟩
    simpa only [neg_log_exp_neg_of_mem_strip (hU hz)] using hz
  · intro w hw v hv he
    have hwe : 0 < w.re := by obtain ⟨z, hz, rfl⟩ := hw; exact re_exp_neg_pos_of_mem_strip (hU hz)
    have hve : 0 < v.re := by obtain ⟨z, hz, rfl⟩ := hv; exact re_exp_neg_pos_of_mem_strip (hU hz)
    have hh := congrArg (fun z => exp (-z)) he
    simpa only [exp_neg_neg_log_of_re_pos hwe, exp_neg_neg_log_of_re_pos hve] using hh
  · intro z hz
    exact ⟨exp (-z), ⟨z, hz, rfl⟩, neg_log_exp_neg_of_mem_strip (hU hz)⟩

/-- Ordinary kernel convergence of disk maps on straight-tail strip domains
also controls the circle point corresponding to the right end. -/
theorem boundary_values_tendsto_at_common_strip_end
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {ξ : ℕ → ℂ} {ξ₀ z₀ : ℂ} {R : ℝ}
    (hU : ∀ n, IsOpen (U n)) (hUS : ∀ n, U n ⊆ standardHorizontalStrip)
    (hV : IsOpen V) (hVS : V ⊆ standardHorizontalStrip)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (U n)) (hFb : ∀ n, BijOn (F n) (U n) (ball 0 1))
    (hf : DifferentiableOn ℂ f V) (hfb : BijOn f V (ball 0 1))
    (hz₀U : ∀ n, z₀ ∈ U n) (hz₀V : z₀ ∈ V)
    (hF0 : ∀ n, F n z₀ = 0) (hf0 : f z₀ = 0)
    (htail : ∀ n, ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U n)
    (hvtail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ V)
    (hξ : ∀ n, Tendsto (fun w => F n (-log w))
      (𝓝[exponentialImage (U n) ∩ {w : ℂ | 0 < w.re}] 0) (𝓝 (ξ n)))
    (hξ₀ : Tendsto (fun w => f (-log w))
      (𝓝[exponentialImage V ∩ {w : ℂ | 0 < w.re}] 0) (𝓝 ξ₀))
    (hconv : TendstoLocallyUniformlyOn F f atTop V) : Tendsto ξ atTop (𝓝 ξ₀) := by
  have hshape {S : Set ℂ} (hSo : IsOpen S) (hSS : S ⊆ standardHorizontalStrip) :
      IsOpen (exponentialImage S) ∧
      DifferentiableOn ℂ (fun w => -log w) (exponentialImage S) := by
    refine ⟨TauCeti.isOpen_image_of_differentiableOn_of_injOn hSo
      ((differentiable_exp.comp differentiable_id.neg).differentiableOn)
      (bijOn_exp_neg_strip.injOn.mono hSS),
      differentiableOn_neg_log_rightHalfPlane.mono ?_⟩
    rintro w ⟨z, hz, rfl⟩
    exact re_exp_neg_pos_of_mem_strip (hSS hz)
  have hnear n := exponentialImage_agrees_with_halfplane_at_zero (hUS n) (htail n)
  have hvnear := exponentialImage_agrees_with_halfplane_at_zero hVS hvtail
  apply boundary_limits_tendsto_of_common_straight_side
    (z₀ := exp (-z₀)) (R := Real.exp (-R)) (Real.exp_pos _) (exp_ne_zero _)
    (fun n => (hshape (hU n) (hUS n)).1)
    (fun n => (hF n).comp (hshape (hU n) (hUS n)).2
      (bijOn_neg_log_exponentialImage (hUS n)).mapsTo)
    (fun n => (hFb n).comp (bijOn_neg_log_exponentialImage (hUS n)))
    (fun n => ⟨z₀, hz₀U n, rfl⟩)
    (fun n => by simpa only [Function.comp_apply, neg_log_exp_neg_of_mem_strip (hUS n (hz₀U n))] using hF0 n)
    (fun n w hw hp => (hnear n w hw).mpr hp)
    (fun n w hw he hi => by have hp := (hnear n w hw).mp hi; rw [he] at hp; exact lt_irrefl _ hp)
    (hshape hV hVS).1 (hf.comp (hshape hV hVS).2 (bijOn_neg_log_exponentialImage hVS).mapsTo)
    (hfb.comp (bijOn_neg_log_exponentialImage hVS))
    ⟨z₀, hz₀V, rfl⟩
    (by simpa only [Function.comp_apply, neg_log_exp_neg_of_mem_strip (hVS hz₀V)] using hf0)
    (fun w hw hp => (hvnear w hw).mpr hp)
    (fun w hw he hi => by have hp := (hvnear w hw).mp hi; rw [he] at hp; exact lt_irrefl _ hp)
    hξ hξ₀
  intro w hw hp
  exact hconv.tendsto_at ((bijOn_neg_log_exponentialImage hVS).mapsTo ((hvnear w hw).mpr hp))

/-- Rotating disk maps by their convergent boundary values preserves local
uniform convergence. This changes derivative normalization into right-end
normalization. -/
theorem locallyUniform_div_boundary_values
    {V : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {ξ : ℕ → ℂ} {ξ₀ : ℂ}
    (hconv : TendstoLocallyUniformlyOn F f atTop V) (hf : ContinuousOn f V)
    (hξ : Tendsto ξ atTop (𝓝 ξ₀)) (hξ₀ : ξ₀ ≠ 0) :
    TendstoLocallyUniformlyOn (fun n z => F n z / ξ n) (fun z => f z / ξ₀) atTop V := by
  exact hconv.div₀ (hξ.tendstoUniformlyOn_const V).tendstoLocallyUniformlyOn
    hf continuousOn_const (fun _ _ => hξ₀)

end FunctionTheory
