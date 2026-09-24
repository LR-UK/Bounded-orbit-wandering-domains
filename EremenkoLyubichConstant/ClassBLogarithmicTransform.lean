/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import EremenkoLyubichConstant.ClassBTracts
import EremenkoLyubichConstant.Growth

open Set Function
open scoped Topology

namespace EremenkoLyubichConstant

open FunctionTheory

/-- Every logarithmic preimage component of a nonvanishing conformal exterior tract admits
a logarithmic transform. The statement does not impose periodicity on the transform. -/
theorem TractEquiv.exists_logarithmic_transform
    {T : Set ℂ} {ρ : ℝ} (e : TractEquiv T ρ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfun : ∀ z ∈ T, Complex.exp (e.toFun z) = f z)
    (hne : (0 : ℂ) ∉ T) {ζ₀ : ℂ} (hζ₀ : Complex.exp ζ₀ ∈ T) :
    ∃ F : TractEquiv (connectedComponentIn (Complex.exp ⁻¹' T) ζ₀) ρ,
      InjOn Complex.exp (connectedComponentIn (Complex.exp ⁻¹' T) ζ₀) ∧
      ∀ ζ ∈ connectedComponentIn (Complex.exp ⁻¹' T) ζ₀,
        Complex.exp (F.toFun ζ) = f (Complex.exp ζ) := by
  let S := connectedComponentIn (Complex.exp ⁻¹' T) ζ₀
  have hS : IsOpen S := (e.isOpen_source.preimage Complex.continuous_exp).connectedComponentIn
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp
    (isConnected_connectedComponentIn_iff.mpr hζ₀)
  let : SimplyConnectedSpace T := e.isSimplyConnected.simplyConnectedSpace
  let : LocallyPathConnectedSpace T := e.isOpen_source.locallyPathConnectedSpace
  have hce : IsCoveringMapOn Complex.exp T := Complex.isCoveringMapOn_exp.mono (by
    intro z hz hz0
    exact hne (hz0 ▸ hz))
  let p : S → T := fun z ↦ ⟨Complex.exp z,
    connectedComponentIn_subset (Complex.exp ⁻¹' T) ζ₀ z.2⟩
  have hp : IsCoveringMap p :=
    isCoveringMap_connectedComponentIn Complex.continuous_exp e.isOpen_source hce ζ₀
  obtain ⟨h, hh⟩ := exists_homeomorph_of_simplyConnected_base hp
    (⟨ζ₀, mem_connectedComponentIn hζ₀⟩ : S)
  have hinj : InjOn Complex.exp S := by
    intro z hz w hw he
    have he' : h ⟨z, hz⟩ = h ⟨w, hw⟩ := by
      rw [hh]
      exact Subtype.ext he
    exact congrArg Subtype.val (h.injective he')
  obtain ⟨F, hF⟩ := tractEquiv_of_homeomorph hS
    (hf.comp Complex.differentiable_exp).differentiableOn (h.trans e.toHomeomorph) (by
      intro z
      change Complex.exp (e.toFun (h z)) = f (Complex.exp z)
      rw [hh]
      exact hfun (Complex.exp z) (p z).2)
  exact ⟨F, hinj, hF⟩

/-- The logarithmic transform on an actual component of the full logarithmic preimage.
This uses the paper's condition that the exterior radius contains the value at zero. -/
theorem exists_logarithmic_transform_on_component
    {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) {ρ : ℝ}
    (hc : IsCoveringMapOn f (exponentialExterior ρ)) (h₀ : ‖f 0‖ ≤ Real.exp ρ)
    {ζ₀ : ℂ} (hζ₀ : f (Complex.exp ζ₀) ∈ exponentialExterior ρ) :
    ∃ F : TractEquiv (connectedComponentIn ((f ∘ Complex.exp) ⁻¹' exponentialExterior ρ) ζ₀) ρ,
      InjOn Complex.exp (connectedComponentIn ((f ∘ Complex.exp) ⁻¹' exponentialExterior ρ) ζ₀) ∧
      ∀ ζ ∈ connectedComponentIn ((f ∘ Complex.exp) ⁻¹' exponentialExterior ρ) ζ₀,
        Complex.exp (F.toFun ζ) = f (Complex.exp ζ) := by
  let T := connectedComponentIn (f ⁻¹' exponentialExterior ρ) (Complex.exp ζ₀)
  obtain ⟨e, he⟩ := hf.exists_exterior_tract_chart hc hζ₀
  have hT₀ : (0 : ℂ) ∉ T := by
    intro h
    exact (not_lt_of_ge h₀)
      (connectedComponentIn_subset (f ⁻¹' exponentialExterior ρ) (Complex.exp ζ₀) h)
  have he₀ : Complex.exp ζ₀ ∈ T :=
    mem_connectedComponentIn (show Complex.exp ζ₀ ∈ f ⁻¹' exponentialExterior ρ from hζ₀)
  have hr := e.exists_logarithmic_transform hf.1 he hT₀ he₀
  have hs := connectedComponentIn_preimage_connectedComponentIn Complex.continuous_exp
    (show Complex.exp ζ₀ ∈ f ⁻¹' exponentialExterior ρ from hζ₀)
  rw [hs] at hr
  exact hr

/-- A class-B function has logarithmic transforms on every component above one common radius.
The conformal chart is chosen separately on each component; periodicity is not part of the claim. -/
theorem _root_.FunctionTheory.MemClassB.exists_logarithmic_transforms
    {f : ℂ → ℂ} (hf : MemClassB f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ ζ₀, f (Complex.exp ζ₀) ∈ exponentialExterior ρ →
      ∃ F : TractEquiv (connectedComponentIn ((f ∘ Complex.exp) ⁻¹' exponentialExterior ρ) ζ₀) ρ,
        InjOn Complex.exp (connectedComponentIn ((f ∘ Complex.exp) ⁻¹' exponentialExterior ρ) ζ₀) ∧
        ∀ ζ ∈ connectedComponentIn ((f ∘ Complex.exp) ⁻¹' exponentialExterior ρ) ζ₀,
          Complex.exp (F.toFun ζ) = f (Complex.exp ζ) := by
  obtain ⟨ρ, hρ, hc, ha⟩ := hf.exists_normalized_exterior_covering
  have h₀ : ‖f 0‖ ≤ Real.exp ρ := by
    by_contra hh
    have h := ha 0 (lt_of_not_ge hh)
    norm_num at h
  exact ⟨ρ, hρ, fun _ hz ↦ exists_logarithmic_transform_on_component hf.1 hc h₀ hz⟩

/-- Every class-B function admits a logarithmic transform on a logarithmic tract. -/
theorem exists_logarithmic_transform_of_memClassB {f : ℂ → ℂ} (hf : MemClassB f) :
    ∃ (T : Set ℂ) (ρ : ℝ) (F : TractEquiv T ρ),
      0 ≤ ρ ∧ InjOn Complex.exp T ∧
      ∀ ζ ∈ T, Complex.exp (F.toFun ζ) = f (Complex.exp ζ) := by
  obtain ⟨ρ, hρ, hc, ha⟩ := hf.exists_normalized_exterior_covering
  obtain ⟨z₀, hz₀⟩ := hf.1.exists_norm_gt (Real.exp ρ)
  obtain ⟨e, he⟩ := hf.1.exists_exterior_tract_chart hc hz₀
  have hz₀ne : z₀ ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans (ha z₀ hz₀))
  have hn : (0 : ℂ) ∉ connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀ := by
    intro h
    have hh := ha 0 (connectedComponentIn_subset (f ⁻¹' exponentialExterior ρ) z₀ h)
    norm_num at hh
  have hlog : Complex.exp (Complex.log z₀) ∈
      connectedComponentIn (f ⁻¹' exponentialExterior ρ) z₀ := by
    rw [Complex.exp_log hz₀ne]
    exact mem_connectedComponentIn hz₀
  obtain ⟨F, hi, hF⟩ := e.exists_logarithmic_transform hf.1.1 he hn hlog
  exact ⟨_, ρ, F, hρ, hi, hF⟩

/-- Corollary 1.2: every Eremenko--Lyubich class-B function has lower order at least one half,
in the quantitative maximum-modulus formulation. -/
theorem lower_order_of_memClassB {f : ℂ → ℂ} (hf : MemClassB f) :
    ∃ c > 0, ∃ r₀ > 1, ∀ r ≥ r₀, c * Real.sqrt r ≤ Real.log (maximumModulus f r) := by
  obtain ⟨T, ρ, F, hρ, hi, hF⟩ := exists_logarithmic_transform_of_memClassB hf
  exact lower_order_of_logarithmic_tract F hρ hi hf.1.1 hF

/-- Theorem 1.1 in the original plane, for any exterior covering radius containing `f 0`. -/
theorem expansion_of_exterior_covering
    {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) {R : ℝ} (hR : 0 < R)
    (hc : IsCoveringMapOn f {w : ℂ | R < ‖w‖}) (h₀ : ‖f 0‖ ≤ R)
    {z : ℂ} (hz : R < ‖f z‖) :
    ((Real.log ‖f z‖ - Real.log R) * ‖f z‖) / (2 * ‖z‖) ≤ ‖deriv f z‖ := by
  have hce : IsCoveringMapOn f (exponentialExterior (Real.log R)) := by
    simpa only [exponentialExterior, Real.exp_log hR] using hc
  have hze : f z ∈ exponentialExterior (Real.log R) := by
    simpa only [exponentialExterior, mem_ofPred_eq, Real.exp_log hR] using hz
  have hn : z ≠ 0 := by rintro rfl; exact (not_lt_of_ge h₀) hz
  let T := connectedComponentIn (f ⁻¹' exponentialExterior (Real.log R)) z
  obtain ⟨e, he⟩ := hf.exists_exterior_tract_chart hce hze
  have hT₀ : (0 : ℂ) ∉ T := by
    intro h
    have hh := connectedComponentIn_subset (f ⁻¹' exponentialExterior (Real.log R)) z h
    change Real.exp (Real.log R) < ‖f 0‖ at hh
    rw [Real.exp_log hR] at hh
    exact (not_lt_of_ge h₀) hh
  have hlog : Complex.exp (Complex.log z) ∈ T := by
    rw [Complex.exp_log hn]
    exact mem_connectedComponentIn hze
  obtain ⟨F, hi, hF⟩ := e.exists_logarithmic_transform hf.1 he hT₀ hlog
  have hζ : Complex.log z ∈ connectedComponentIn (Complex.exp ⁻¹' T) (Complex.log z) :=
    mem_connectedComponentIn (show Complex.log z ∈ Complex.exp ⁻¹' T from hlog)
  have hvalue : Complex.exp (F.toFun (Complex.log z)) = f z := by
    simpa only [Complex.exp_log hn] using hF (Complex.log z) hζ
  have hre : (F.toFun (Complex.log z)).re = Real.log ‖f z‖ := by
    rw [← hvalue, Complex.norm_exp, Real.log_exp]
  have hm := expansion_for_logarithmic_transform F hζ hi hF
    (hf.1 (Complex.exp (Complex.log z)))
  rw [hre, hvalue, Complex.exp_log hn] at hm
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (norm_pos_iff.mpr hn))).mpr
  nlinarith

/-- The optimal derivative estimate with exactly the singular-set and radius assumptions
used in the paper. -/
theorem optimal_expansion_of_memClassB
    {f : ℂ → ℂ} (hf : MemClassB f) {R : ℝ} (hR : 0 < R)
    (hS : singularValueSet f ⊆ Metric.closedBall (0 : ℂ) R) (h₀ : ‖f 0‖ ≤ R)
    {z : ℂ} (hz : R < ‖f z‖) :
    ((Real.log ‖f z‖ - Real.log R) * ‖f z‖) / (2 * ‖z‖) ≤ ‖deriv f z‖ := by
  apply expansion_of_exterior_covering hf.1 hR _ h₀ hz
  intro w hw
  by_contra hn
  have hh := mem_closedBall_zero_iff.mp (hS (show w ∈ singularValueSet f from hn))
  exact (not_lt_of_ge hh) hw

end EremenkoLyubichConstant
