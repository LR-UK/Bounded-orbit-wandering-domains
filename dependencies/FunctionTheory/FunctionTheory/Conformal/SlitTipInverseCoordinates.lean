import FunctionTheory.Conformal.SlitTipInverse
import FunctionTheory.Conformal.SlitTipCoordinates

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

/-- Transfer the inverse boundary limit to the affine coordinate of the
free attached-segment endpoint. -/
theorem exists_inverse_boundary_limit_at_reflected_slit_tip
    {U : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R)
    (hlocal : {z : ℂ | c - z ∈ U} ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ ξ ∈ sphere (0 : ℂ) 1,
      Tendsto (invFunOn f U) (𝓝[ball 0 1] ξ) (𝓝 c) := by
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
  let g := invFunOn (f ∘ φ) V
  have hfb := hbij.comp hφbij
  obtain ⟨ξ, hξ, hg⟩ := exists_inverse_boundary_limit_at_slit_tip
    (hU.preimage hφc) (hf.comp hφd.differentiableOn hφbij.mapsTo) hfb hR hlocal
  refine ⟨ξ, hξ, ?_⟩
  have heq : invFunOn f U =ᶠ[𝓝[ball 0 1] ξ] fun w => φ (g w) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hgw : g w ∈ V := hfb.surjOn.mapsTo_invFunOn hw
    have he : f (φ (g w)) = w := hfb.surjOn.rightInvOn_invFunOn hw
    calc
      invFunOn f U w = invFunOn f U (f (φ (g w))) := congrArg (invFunOn f U) he.symm
      _ = φ (g w) := hbij.injOn.leftInvOn_invFunOn (hφbij.mapsTo hgw)
  rw [tendsto_congr' heq]
  simpa only [φ, g, V, Function.comp_def, sub_zero] using hφc.continuousAt.tendsto.comp hg

/-- The forward and inverse limits correspond at the same circle point.
Only inverse continuity is needed by the surrounding-curve application. -/
theorem exists_corresponding_boundary_limits_at_reflected_slit_tip
    {U : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R)
    (hlocal : {z : ℂ | c - z ∈ U} ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ ξ ∈ sphere (0 : ℂ) 1,
      Tendsto f (𝓝[U] c) (𝓝 ξ) ∧
      Tendsto (invFunOn f U) (𝓝[ball 0 1] ξ) (𝓝 c) := by
  obtain ⟨a, ha, hfa⟩ := exists_boundary_limit_at_reflected_slit_tip hU hf hbij hR hlocal
  obtain ⟨ξ, hξ, hg⟩ := exists_inverse_boundary_limit_at_reflected_slit_tip hU hf hbij hR hlocal
  have hξcl : ξ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    exact sphere_subset_closedBall hξ
  haveI := mem_closure_iff_nhdsWithin_neBot.mp hξcl
  have hgt : Tendsto (invFunOn f U) (𝓝[ball 0 1] ξ) (𝓝[U] c) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hg
    · filter_upwards [self_mem_nhdsWithin] with w hw using hbij.surjOn.mapsTo_invFunOn hw
  have heq : (fun w => f (invFunOn f U w)) =ᶠ[𝓝[ball 0 1] ξ] id := by
    filter_upwards [self_mem_nhdsWithin] with w hw using hbij.surjOn.rightInvOn_invFunOn hw
  have ht : Tendsto id (𝓝[ball 0 1] ξ) (𝓝 a) := (hfa.comp hgt).congr' heq
  have haξ : a = ξ := tendsto_nhds_unique ht (tendsto_id'.mpr nhdsWithin_le_nhds)
  exact ⟨ξ, hξ, haξ ▸ hfa, hg⟩

end FunctionTheory
