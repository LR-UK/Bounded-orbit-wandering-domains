import FunctionTheory.Conformal.SlitTipBoundary

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

/-- The local slit-tip theorem after an affine change of coordinates. -/
theorem exists_boundary_limit_at_reflected_slit_tip
    {U : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R)
    (hlocal : {z : ℂ | c - z ∈ U} ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ a ∈ sphere (0 : ℂ) 1, Tendsto f (𝓝[U] c) (𝓝 a) := by
  let φ : ℂ → ℂ := fun z => c - z
  let V := φ ⁻¹' U
  have hφc : Continuous φ := by dsimp [φ]; fun_prop
  have hφd : Differentiable ℂ φ := by dsimp [φ]; fun_prop
  have hφinv : ∀ z, φ (φ z) = z := by intro z; dsimp [φ]; ring
  have hφbij : BijOn φ V U := by
    refine ⟨fun _ hz => hz, ?_, ?_⟩
    · intro x _ y _ heq
      have h := congrArg φ heq
      simpa only [hφinv] using h
    · intro y hy
      refine ⟨φ y, ?_, hφinv y⟩
      change φ (φ y) ∈ U
      simpa only [hφinv] using hy
  have hV : IsOpen V := hU.preimage hφc
  obtain ⟨a, ha, hlim⟩ := exists_boundary_limit_at_slit_tip hV
    (hf.comp hφd.differentiableOn hφbij.mapsTo) (hbij.comp hφbij) hR hlocal
  have ht : Tendsto φ (𝓝[U] c) (𝓝[V] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := hφc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[U] c ≤ 𝓝 c)
      simpa only [φ, sub_self] using h
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change φ (φ z) ∈ U
      simpa only [hφinv] using hz
  refine ⟨a, ha, ?_⟩
  simpa only [Function.comp_def, hφinv] using hlim.comp ht

end FunctionTheory
